#use "tag-parser.ml";;

type var = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | Const' of constant
  | Var' of var
  | Box' of var
  | BoxGet' of var
  | BoxSet' of var * expr'
  | If' of expr' * expr' * expr'
  | Seq' of expr' list
  | Set' of expr' * expr'
  | Def' of expr' * expr'
  | Or' of expr' list
  | LambdaSimple' of string list * expr'
  | LambdaOpt' of string list * string * expr'
  | Applic' of expr' * (expr' list)
  | ApplicTP' of expr' * (expr' list);;

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | Const' Void, Const' Void -> true
  | Const'(Sexpr s1), Const'(Sexpr s2) -> sexpr_eq s1 s2
  | Var'(VarFree v1), Var'(VarFree v2) -> String.equal v1 v2
  | Var'(VarParam (v1,mn1)), Var'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Var'(VarBound (v1,mj1,mn1)), Var'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                            (expr'_eq th1 th2) &&
                                              (expr'_eq el1 el2)
  | (Seq'(l1), Seq'(l2)
  | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
  | (Set'(var1, val1), Set'(var2, val2)
  | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq var1 var2) &&
                                             (expr'_eq val1 val2)
  | LambdaSimple'(vars1, body1), LambdaSimple'(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr'_eq body1 body2)
  | LambdaOpt'(vars1, var1, body1), LambdaOpt'(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr'_eq body1 body2)
  | Applic'(e1, args1), Applic'(e2, args2)
  | ApplicTP'(e1, args1), ApplicTP'(e2, args2) ->
	 (expr'_eq e1 e2) &&
	   (List.for_all2 expr'_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;

module type SEMANTICS = sig
  val run_semantics : expr -> expr'
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
end;;

module Semantics : SEMANTICS = struct

let rec findminor x lst ans =
  match lst with
  | [] -> -1
  | hd::tl -> if x = hd then ans else findminor x tl (ans+1)

let rec findmajor x lst ans =
  match lst with
  | [] -> -1
  | hd::tl -> if List.mem x hd then ans else findmajor x tl (ans+1)

let rec lexical expr varlist =
    match expr with
    | Const(x) -> Const'(x)
    | If(test, dit, dif) -> If'(lexical test varlist, lexical dit varlist, lexical dif varlist)
    | Set(expr1, expr2) -> Set'(lexical expr1 varlist, lexical expr2 varlist)
    | Def(expr1, expr2) -> Def'(lexical expr1 varlist, lexical expr2 varlist)
    | Seq(exprlist) -> Seq'(List.map (fun expr -> lexical expr varlist) exprlist)
    | Or(exprlist) -> Or'(List.map (fun expr -> lexical expr varlist) exprlist)
    | LambdaSimple(params, expr) -> LambdaSimple'(params, lexical expr (params::varlist))
    | LambdaOpt(params, optparam, expr) -> LambdaOpt'(params, optparam, lexical expr ((params @ [optparam])::varlist))
    | Applic(proc, params) -> Applic'(lexical proc varlist, List.map (fun expr -> lexical expr varlist) params)
    | Var(x) -> match findmajor x varlist 0 with
                | -1 -> Var'(VarFree(x))
                | 0 -> Var'(VarParam(x, findminor x (List.hd varlist) 0))
                | major -> Var'(VarBound(x, major-1, findminor x (List.nth varlist major) 0));;

let rec lst_last lst ans =
  match lst with
  | [] -> raise X_syntax_error
  | hd :: [] -> (ans, hd)
  | hd :: tl -> lst_last tl (ans @ [hd]);;

let rec tailcall expr in_tp =
  match expr with 
  | Const'(x) -> expr
  | Var'(x) -> expr
  | If'(test, dit, dif) -> If'(tailcall test false, tailcall dit in_tp, tailcall dif in_tp)
  | Set'(expr1, expr2) -> Set'(tailcall expr1 false, tailcall expr2 false)
  | Def'(expr1, expr2) -> Def'(tailcall expr1 false, tailcall expr2 false)
  | Seq'(exprlist) -> let (lst, last) = lst_last exprlist [] in
                      Seq'((List.map (fun x -> tailcall x false) lst) @ [tailcall last in_tp])
  | Or'(exprlist) -> let (lst, last) = lst_last exprlist [] in
                      Or'((List.map (fun x -> tailcall x false) lst) @ [tailcall last in_tp])
  | LambdaSimple'(params, expr) -> LambdaSimple'(params, tailcall expr true)
  | LambdaOpt'(params, optparam, expr) -> LambdaOpt'(params, optparam, tailcall expr true)
  | Applic'(proc, params) -> (match in_tp with
                            | true -> ApplicTP'(tailcall proc false, List.map (fun x -> tailcall x false) params)
                            | false -> Applic'(tailcall proc false, List.map (fun x -> tailcall x false) params))
  | _ -> raise X_syntax_error;;

let check_var param var =
  match var with
  | VarFree(name) -> param = name
  | VarParam(name, minor) -> param = name
  | VarBound(name, major, minor) -> param = name;;

let rec check_rw param expr (read, write) =
  match expr with
  | If'(test, dit, dif) -> let (test_r, test_w) = check_rw param test (read, write) in
                           let (dit_r, dit_w) = check_rw param dit (read, write) in
                           let (dif_r, dif_w) = check_rw param dif (read, write) in
                           ((read || test_r || dit_r || dif_r), (write || test_w || dit_w || dif_w))
  | Seq'(exprlist) -> List.fold_right (fun expr (acc_r, acc_w) -> let (expr_r, expr_w) = check_rw param expr (read, write) in
                                                                  ((expr_r || acc_r), (expr_w || acc_w)))
                                      exprlist (read, write)
  | Or'(exprlist) -> List.fold_right (fun expr (acc_r, acc_w) -> let (expr_r, expr_w) = check_rw param expr (read, write) in
                                                                 ((acc_r || expr_r), (acc_w || expr_w)))
                                      exprlist (read, write)
  | Set'(Var'(var), expr) -> let (expr_r, expr_w) = check_rw param expr (read, write) in 
                      ((read || expr_r), (write || (check_var param var) || expr_w))
  | Def'(Var'(var), expr) -> check_rw param expr (read, write)
  | Applic'(proc, params) -> List.fold_right (fun expr (acc_r, acc_w) -> let (expr_r, expr_w) = check_rw param expr (read, write) in
                                                                          ((expr_r || acc_r), (expr_w || acc_w)))
                                              params (check_rw param proc (read, write))
  | ApplicTP'(proc, params) -> List.fold_right (fun expr (acc_r, acc_w) -> let (expr_r, expr_w) = check_rw param expr (read, write) in
                                                                           ((expr_r || acc_r), (expr_w || acc_w)))
                                              params (check_rw param proc (read, write))
  | Var'(var) -> ((read || (check_var param var)), write)
  | _ -> (false, false);;

  let rec check_rw_lambdas param expr (read, write) =
    match expr with
    | If'(test, dit, dif) -> let (test_r, test_w) = check_rw_lambdas param test (read, write) in
                             let (dit_r, dit_w) = check_rw_lambdas param dit (read, write) in
                             let (dif_r, dif_w) = check_rw_lambdas param dif (read, write) in
                             ((read || test_r || dit_r || dif_r), (write || test_w || dit_w || dif_w))
    | Seq'(exprlist) -> List.fold_right (fun expr (acc_r, acc_w) -> let (expr_r, expr_w) = check_rw_lambdas param expr (read, write) in
                                                                    ((expr_r || acc_r), (expr_w || acc_w)))
                                        exprlist (read, write)
    | Or'(exprlist) -> List.fold_right (fun expr (acc_r, acc_w) -> let (expr_r, expr_w) = check_rw_lambdas param expr (read, write) in
                                                                   ((acc_r || expr_r), (acc_w || expr_w)))
                                        exprlist (read, write)
    | Set'(Var'(var), expr) -> let (expr_r, expr_w) = check_rw_lambdas param expr (read, write) in 
                        ((read || expr_r), (write || (check_var param var) || expr_w))
    | Applic'(proc, params) -> List.fold_right (fun expr (acc_r, acc_w) -> let (expr_r, expr_w) = check_rw_lambdas param expr (read, write) in
                                                                            ((expr_r || acc_r), (expr_w || acc_w)))
                                                params (check_rw_lambdas param proc (read, write))
    | ApplicTP'(proc, params) -> List.fold_right (fun expr (acc_r, acc_w) -> let (expr_r, expr_w) = check_rw_lambdas param expr (read, write) in
                                                                             ((expr_r || acc_r), (expr_w || acc_w)))
                                                params (check_rw_lambdas param proc (read, write))
    | Var'(var) -> ((read || (check_var param var)), write)
    | LambdaSimple'(arglist, expr) when (not (List.mem param arglist)) -> check_rw_lambdas param expr (read, write)
    | LambdaOpt'(arglist, argopt, expr) when (not (List.mem param arglist)) && (not (param = argopt)) -> check_rw_lambdas param expr (read, write)
    | _ -> (false, false);;

let rec create_array param expr =
    match expr with
    | If'(test, dit, dif) -> (create_array param test) @ (create_array param dit) @ (create_array param dif)
    | Seq'(exprlist) -> List.fold_right (fun expr acc -> (create_array param expr) @ acc) exprlist []
    | Set'(var, expr) -> create_array param expr
    | Def'(var, expr) -> create_array param expr
    | Or'(exprlist) -> List.fold_right (fun expr acc -> (create_array param expr) @ acc) exprlist []
    | LambdaSimple'(arglist, expr) when (not (List.mem param arglist)) -> [check_rw_lambdas param expr (false, false)]
    | LambdaOpt'(arglist, argopt, expr) when (not (List.mem param arglist)) && (not (param = argopt)) -> [check_rw_lambdas param expr (false, false)]
    | Applic'(proc, params) -> (create_array param proc) @ (List.fold_right (fun expr acc -> (create_array param expr) @ acc) params [])
    | ApplicTP'(proc, params) -> (create_array param proc) @ (List.fold_right (fun expr acc -> (create_array param expr) @ acc) params [])
    | _ -> [];;

let rec check_box param expr =
  let main_rw = check_rw param expr (false, false) in
  let arr = create_array param expr in
  let rec check_element (e1_r, e1_w) arr =
    match arr with 
    | [] -> false
    | (e2_r, e2_w) :: tl -> (e1_r && e2_w) || (e1_w && e2_r) || check_element (e1_r, e1_w) tl in
  let rec check_arr arr =
    match arr with
    | [] -> false
    | e1 :: tl -> check_element e1 tl || check_arr tl in
  (check_element main_rw arr) || check_arr arr
  
let rec varlist arglist minor =
  match arglist with
  | [] -> [] 
  | hd :: tl -> VarParam(hd, minor) :: (varlist tl (minor + 1));;

let rec box_getset param expr =
  match expr with
  | Var'(var) -> if (check_var param var) then BoxGet'(var) else expr
  | BoxSet'(var, exp) -> BoxSet'(var, box_getset param exp)
  | If'(test, dit, dif) -> If'(box_getset param test, box_getset param dit, box_getset param dif)
  | Seq'(exprlist) -> Seq'(List.map (box_getset param) exprlist)
  | Set'(Var'(var), expr) -> if (check_var param var) then BoxSet'(var, box_getset param expr) else Set'(Var'(var), box_getset param expr)
  | Def'(var, expr) -> Def'(var, box_getset param expr)
  | Or'(exprlist) -> Or'(List.map (box_getset param) exprlist)
  | LambdaSimple'(arglist, expr) when (not (List.mem param arglist)) -> LambdaSimple'(arglist, box_getset param expr)
  | LambdaOpt'(arglist, opt, expr) when (not (List.mem param arglist)) && (not (param = opt)) -> LambdaOpt'(arglist, opt, box_getset param expr)
  | Applic'(proc, params) -> Applic'(box_getset param proc, List.map (box_getset param) params)
  | ApplicTP'(proc, params) -> ApplicTP'(box_getset param proc, List.map (box_getset param) params)
  | _ -> expr;;

let rec modify_body body need_box =
  match need_box with
  | [] -> body
  | VarParam(param, _)::tl -> modify_body (box_getset param body) tl
  | _ -> raise X_syntax_error;;

let name_of_var var =
  match var with
  | VarParam(param, _) -> param
  | _ -> raise X_syntax_error;;

let rec box e =
  match e with
  | If'(test, dit, dif) -> If'(box test, box dit, box dif)
  | Seq'(exprlist) -> Seq'(List.map box exprlist)
  | Set'(var, expr) -> Set'(box var, box expr)
  | Def'(var, expr) -> Def'(box var, box expr)
  | Or'(exprlist) -> Or'(List.map box exprlist)
  | LambdaSimple'(arglist, expr) -> let need_box = (List.filter (fun var -> check_box (name_of_var var) expr) (varlist arglist 0)) in
                                    let boxed_vars = List.map (fun var -> Set'(Var'(var), Box'(var))) need_box in
                                    let new_body = modify_body (box expr) need_box in
                                    (match new_body, boxed_vars with
                                    | new_body, [] -> LambdaSimple'(arglist, new_body)
                                    | new_body, boxed_vars ->  LambdaSimple'(arglist, Seq'(boxed_vars @ [new_body])))
  | LambdaOpt'(arglist, opt, expr) -> let need_box = (List.filter (fun var -> check_box (name_of_var var) expr) (varlist (arglist @ [opt]) 0)) in
                                      let boxed_vars = List.map (fun var -> Set'(Var'(var), Box'(var))) need_box in
                                      let new_body = modify_body (box expr) need_box in
                                      (match new_body, boxed_vars with
                                      | new_body, [] -> LambdaOpt'(arglist, opt, new_body)
                                      | new_body, boxed_vars ->  LambdaOpt'(arglist, opt, Seq'(boxed_vars @ [new_body])))
  | Applic'(proc, params) -> Applic'(box proc, List.map box params)
  | ApplicTP'(proc, params) -> ApplicTP'(box proc, List.map box params)
  | _ -> e;;
 
let annotate_lexical_addresses e = lexical e [];;

let annotate_tail_calls e = tailcall e false;;

let box_set e = box e;;

let run_semantics expr =
  box_set
    (annotate_tail_calls
       (annotate_lexical_addresses expr));;
  
end;; (* struct Semantics *)
