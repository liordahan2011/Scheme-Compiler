#use "reader.ml";;
open Reader;;

type constant =
  | Sexpr of sexpr
  | Void

type expr =
  | Const of constant
  | Var of string
  | If of expr * expr * expr
  | Seq of expr list
  | Set of expr * expr
  | Def of expr * expr
  | Or of expr list
  | LambdaSimple of string list * expr
  | LambdaOpt of string list * string * expr
  | Applic of expr * (expr list);;

let rec expr_eq e1 e2 =
  match e1, e2 with
  | Const Void, Const Void -> true
  | Const(Sexpr s1), Const(Sexpr s2) -> sexpr_eq s1 s2
  | Var(v1), Var(v2) -> String.equal v1 v2
  | If(t1, th1, el1), If(t2, th2, el2) -> (expr_eq t1 t2) &&
                                            (expr_eq th1 th2) &&
                                              (expr_eq el1 el2)
  | (Seq(l1), Seq(l2)
    | Or(l1), Or(l2)) -> List.for_all2 expr_eq l1 l2
  | (Set(var1, val1), Set(var2, val2)
    | Def(var1, val1), Def(var2, val2)) -> (expr_eq var1 var2) &&
                                             (expr_eq val1 val2)
  | LambdaSimple(vars1, body1), LambdaSimple(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr_eq body1 body2)
  | LambdaOpt(vars1, var1, body1), LambdaOpt(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr_eq body1 body2)
  | Applic(e1, args1), Applic(e2, args2) ->
     (expr_eq e1 e2) &&
       (List.for_all2 expr_eq args1 args2)
  | _ -> false;;


exception X_syntax_error;;

module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
  val tag_parse_expressions : sexpr list -> expr list
end;; (* signature TAG_PARSER *)

module Tag_Parser : TAG_PARSER = struct

(* work on the tag parser starts here *)

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;

let rec valid_arglist arglist =
  match arglist with
  | [] -> []
  | Symbol(hd) :: tl when (not (List.mem hd reserved_word_list)) -> hd :: (valid_arglist tl)
  | _ -> raise X_syntax_error;;

let unique_arglist arglist =
  match valid_check arglist with
  | true -> arglist
  | false -> raise X_syntax_error;;

let valid_body exprs =
  match exprs with
  | [] -> raise X_syntax_error
  | _ -> exprs;;

let valid_var expr =
  match expr with
  | Var(x) -> expr
  | _ -> raise X_syntax_error;;

let rec flat_pair sexp =
  match sexp with
  | Nil -> []
  | Pair(sexp1, sexp2) -> sexp1 :: flat_pair sexp2
  | _ -> [sexp];;

let rec lambda_type arglist =
  match arglist with
  | Nil -> 1
  | Symbol(x) -> 3
  | Pair(Symbol(x), Nil) -> 1
  | Pair(Symbol(x), Symbol(y)) -> 2
  | Pair(Symbol(x), rest) -> lambda_type rest
  | _ -> 0

let rec lst_without_last lst =
  match lst with
  | [] -> []
  | hd :: [] -> []
  | hd :: tl -> hd :: lst_without_last tl;;

let rec lst_last lst =
  match lst with
  | hd :: [] -> [hd]
  | hd :: tl -> lst_last tl
  | _ -> []

let rec quasi_expansion sexp =
  match sexp with
  | Pair(Symbol("unquote"), Pair(sexpr, Nil)) -> sexpr
  | Pair(Symbol("unquote-splicing"), Pair(sexpr, Nil)) -> raise X_syntax_error
  | Nil -> Pair(Symbol("quote"), Pair(sexp, Nil))
  | Symbol(x) -> Pair(Symbol("quote"), Pair(sexp, Nil))
  | Pair(sexp1, sexp2) -> (match sexp1, sexp2 with
                  | Pair(Symbol("unquote-splicing"), Pair(sexpr, Nil)), _ -> Pair(Symbol("append"), Pair(sexpr, Pair(quasi_expansion sexp2, Nil)))
                  | _, Pair(Symbol("unquote-splicing"), Pair(sexpr, Nil)) -> Pair(Symbol("cons"), Pair(quasi_expansion sexp1, Pair(sexpr, Nil)))
                  | _ -> Pair(Symbol("cons"), Pair(quasi_expansion sexp1, Pair(quasi_expansion sexp2, Nil))))
  | _ -> Pair(Symbol("quote"), Pair(sexp, Nil));;

let cond_vars cond body = Pair(Pair(Symbol("value"), Pair(cond, Nil)), Pair(Pair(Symbol("f"), Pair(Pair(Symbol("lambda"), Pair(Nil, body)), Nil)), Nil))

let if_2args = Pair(Symbol("if"), Pair(Symbol("value"), Pair(Pair(Pair(Symbol("f"), Nil), Pair(Symbol("value"), Nil)), Nil)))

let rec cond_expansion conds =
  match conds with
  | Pair(Pair(Symbol("else"), body), rest_ribs) -> Pair(Symbol("begin"), body)
  | Pair(Pair(cond, Pair(Symbol("=>"), body)), Nil) -> Pair(Symbol("let"), Pair((cond_vars cond body), Pair(if_2args, Nil)))
  | Pair(Pair(cond, Pair(Symbol("=>"), body)), rest_ribs) -> Pair(Symbol("let"), Pair(Pair(Pair(Symbol("value"), Pair(cond, Nil)),
                                                                                      Pair(Pair(Symbol("f"), Pair(Pair(Symbol("lambda"), Pair(Nil, body)), Nil)),
                                                                                      Pair(Pair(Symbol("rest"), Pair(Pair(Symbol("lambda"), Pair(Nil, Pair(cond_expansion rest_ribs, Nil))), Nil)), Nil))),
                                                                                      Pair(Pair(Symbol("if"), Pair(Symbol("value"), Pair(Pair(Pair(Symbol("f"), Nil), Pair(Symbol("value"), Nil)), Pair(Pair(Symbol("rest"), Nil), Nil)))), Nil)))
  | Pair(Pair(cond,body), Nil) -> Pair(Symbol("if"), Pair(cond, Pair(Pair(Symbol("begin"), body), Nil)))
  | Pair(Pair(cond, body), rest_ribs) -> Pair(Symbol("if"), Pair(cond, Pair(Pair(Symbol("begin"), body), Pair(cond_expansion rest_ribs, Nil))))
  | _ -> raise X_syntax_error;;

let rec and_expansion sexp =
  match sexp with
  | Nil -> Bool(true)
  | Pair(sexpr, Nil) -> sexpr
  | Pair(expr, rest) -> Pair(Symbol("if"), Pair(expr, Pair(and_expansion rest, Pair(Bool(false), Nil))))
  | _ -> raise X_syntax_error;;

  let rec extract_vars vars =
    match vars with
    | Nil -> Nil
    | Pair(Pair(var, Pair(expr, Nil)), rest) -> Pair(var, extract_vars rest)
    | _ -> raise X_syntax_error;;

  let rec extract_exprs vars =
    match vars with
    | Nil -> Nil
    | Pair(Pair(var, Pair(expr, Nil)), rest) -> Pair(expr, extract_exprs rest)
    | _ -> raise X_syntax_error;;
  
  let rec let_expansion sexp =
    match sexp with
    | Pair(Nil, body) -> Pair(Pair(Symbol("lambda"), Pair(Nil, body)), Nil)
    | Pair(vars, body) -> Pair(Pair(Symbol("lambda"), Pair(extract_vars vars, body)), extract_exprs vars)
    | _ -> raise X_syntax_error;;

  let rec letstar_expansion sexp =
    match sexp with
    | Pair(Nil, body) -> Pair(Symbol("let"), Pair(Nil, body))
    | Pair(Pair(v1, Nil), body) -> Pair(Symbol("let"), Pair(Pair(v1, Nil), body))
    | Pair(Pair(v1, rest_vars), body) -> Pair(Symbol("let"), Pair(Pair(v1, Nil), Pair(letstar_expansion (Pair(rest_vars, body)), Nil)))
    | _ -> raise X_syntax_error;;

  let rec letrec_vars vars =
    match vars with
    | Pair(Pair(f1, Pair(expr1, Nil)), Nil) -> Pair(Pair(f1, Pair(Pair(Symbol("quote"), Pair(Symbol("whatever"), Nil)), Nil)), Nil)
    | Pair(Pair(f1, Pair(expr1, Nil)), rest_vars) -> Pair(Pair(f1, Pair(Pair(Symbol("quote"), Pair(Symbol("whatever"), Nil)), Nil)), letrec_vars rest_vars)
    | _ -> raise X_syntax_error;;

  let rec letrec_body vars body =
    match vars with
    | Pair(var1, Nil) -> Pair(Pair(Symbol("set!"), var1), body)
    | Pair(var1, rest_vars) -> Pair(Pair(Symbol("set!"), var1), (letrec_body rest_vars body))
    | _ -> raise X_syntax_error;;

  let rec letrec_expansion sexp =
    match sexp with
    | Pair(Nil, body) -> Pair(Symbol("let"), Pair(Nil, body))
    | Pair(vars, body) -> Pair(Symbol("let"), Pair(letrec_vars vars, (letrec_body vars body)))
    | _ -> raise X_syntax_error;;

let rec tag_parse sexpr =
  match sexpr with
  | Nil -> Const(Void)
  | Bool(x) -> Const(Sexpr(sexpr))
  | Char(x) -> Const(Sexpr(sexpr))
  | Number(x) -> Const(Sexpr(sexpr))
  | String(x) -> Const(Sexpr(sexpr))
  | TagRef(x) -> Const(Sexpr(sexpr))
  | Pair(Symbol("quote"), Pair(sexpr, Nil)) -> Const(Sexpr(sexpr))
  | TaggedSexpr(tag, Pair(Symbol("quote"), Pair(x, Nil))) -> Const(Sexpr(TaggedSexpr(tag,x)))
  | TaggedSexpr(tag, x) -> Const(Sexpr(sexpr))
  | Symbol(x) when (not (List.mem x reserved_word_list)) -> Var(x)
  | Pair(Symbol("if"), Pair(cond, Pair(sexp1, sexp2))) -> (match sexp2 with
                                                          | Nil -> If(tag_parse cond, tag_parse sexp1, Const(Void))
                                                          | Pair(sexp3, Nil) -> If(tag_parse cond, tag_parse sexp1, tag_parse sexp3)
                                                          | _ -> raise X_syntax_error)
  | Pair(Symbol("lambda"), Pair(arglist, exprs)) -> let valid_list = unique_arglist (valid_arglist (flat_pair arglist)) in
                                                    let body = valid_body (flat_pair exprs) in
                                                    (match (lambda_type arglist), (List.length body) with
                                                    | 1, 1 -> LambdaSimple(valid_list, tag_parse (List.hd body))
                                                    | 1, _ -> LambdaSimple(valid_list, Seq(List.map tag_parse body))
                                                    | 2, 1 -> LambdaOpt(lst_without_last valid_list, List.hd (lst_last valid_list), tag_parse (List.hd body))
                                                    | 2, _ -> LambdaOpt(lst_without_last valid_list, List.hd (lst_last valid_list),
                                                                                                           Seq(List.map tag_parse body))
                                                    | 3, 1 -> LambdaOpt([], List.hd valid_list, tag_parse (List.hd body))
                                                    | 3, _ -> LambdaOpt([], List.hd valid_list, Seq(List.map tag_parse body))
                                                    | _ -> raise X_syntax_error)
  | Pair(Symbol("or"), sexp) -> (match sexp with
                                | Nil -> tag_parse (Bool(false))
                                | Pair(sexp, Nil) -> tag_parse sexp
                                | _ -> Or(List.map tag_parse (flat_pair sexp)))
  | Pair(Symbol("define"), Pair(Pair(var, arglist), body)) ->
                                tag_parse (Pair(Symbol("define"), Pair(var, Pair(Pair(Symbol("lambda"), Pair(arglist, body)), Nil))))
  | Pair(Symbol("define"), Pair(name, Pair(sexp, Nil))) -> Def(valid_var (tag_parse name), tag_parse sexp)
  | Pair(Symbol("set!"), Pair(name, Pair(sexp, Nil))) -> Set(valid_var (tag_parse name), tag_parse sexp)
  | Pair(Symbol("begin"), seq) -> (match seq with
                                  | Nil -> Const(Void)
                                  | Pair(sexp, Nil) -> tag_parse sexp
                                  | _ -> Seq(List.map tag_parse (flat_pair seq)))
  | Pair(Symbol("quasiquote"), Pair(sexp, Nil)) -> tag_parse (quasi_expansion sexp)
  | Pair(Symbol("cond"), conditions) -> tag_parse (cond_expansion conditions)
  | Pair(Symbol("and"), sexp) -> tag_parse (and_expansion sexp)
  | Pair(Symbol("let"), sexp) -> tag_parse (let_expansion sexp)
  | Pair(Symbol("let*"), sexp) -> tag_parse (letstar_expansion sexp)
  | Pair(Symbol("letrec"), sexp) -> tag_parse (letrec_expansion sexp)
  | Pair(op, sexprs) -> Applic(tag_parse op, List.map tag_parse (flat_pair sexprs))
  | _ -> raise X_syntax_error;;

let tag_parse_expression sexpr = tag_parse sexpr;;

let tag_parse_expressions sexpr = List.map tag_parse sexpr;;

end;; (* struct Tag_Parser *)
