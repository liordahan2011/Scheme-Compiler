#use "semantic-analyser.ml";;

(* This module is here for you convenience only!
   You are not required to use it.
   you are allowed to change it. *)
module type CODE_GEN = sig
  val renaming : expr' list -> int -> expr' list
  (* This signature assumes the structure of the constants table is
     a list of key-value pairs:
     - The keys are constant values (Sexpr(x) or Void)
     - The values are pairs of:
       * the offset from the base const_table address in bytes; and
       * a string containing the byte representation (or a sequence of nasm macros)
         of the constant value
     For example: [(Sexpr(Nil), (1, "SOB_NIL"))]
   *)
  val make_consts_tbl : expr' list -> (constant * (int * string)) list

  (* This signature assumes the structure of the fvars table is
     a list of key-value pairs:
     - The keys are the fvar names as strings
     - The values are the offsets from the base fvars_table address in bytes
     For example: [("boolean?", 0)]
   *)  
  val make_fvars_tbl : expr' list -> (string * int) list

  (* This signature represents the idea of outputing assembly code as a string
     for a single AST', given the full constants and fvars tables. 
   *)
  val generate : (constant * (int * string)) list -> (string * int) list -> expr' -> string
end;;

module Code_Gen : CODE_GEN = struct
  module Labels : sig
    val make_label : string -> string
    val make_labels : string list -> string list
  end = struct
    let label_counter = ref 0;;
      
    let count () =
      ( label_counter := 1 + !label_counter ;
        !label_counter );;
      
    let make_label base =
      Printf.sprintf "%s_%d" base (count());;
      
    let make_labels bases =
      let n = count() in
      List.map (fun base -> Printf.sprintf "%s_%d" base n)
         bases;;
  end;;

  
  let rec rename sexp id =
    match sexp with
    | TagRef(tag) -> TagRef(tag ^ (string_of_int id))
    | TaggedSexpr(tag, sexpr) -> TaggedSexpr(tag ^ (string_of_int id), rename sexpr id)
    | Pair(sexpr1, sexpr2) -> Pair(rename sexpr1 id, rename sexpr2 id)
    | _ -> sexp;;

  let rec rename_helper ast id =
    match ast with
    | Const'(Void) -> Const'(Void)
    | Const'(Sexpr(sexp)) -> Const'(Sexpr(rename sexp id))
    | BoxSet'(var, expr) -> BoxSet'(var, rename_helper expr id)
    | If'(test, dit, dif) -> If'((rename_helper test id), (rename_helper dit id), (rename_helper dif id))
    | Seq'(exprlst) -> Seq'(List.map (fun expr -> rename_helper expr id) exprlst)
    | Set'(expr1, expr2) -> Set'((rename_helper expr1 id), (rename_helper expr2 id))
    | Def'(expr1, expr2) -> Def'((rename_helper expr1 id), (rename_helper expr2 id))
    | Or'(exprlst) -> Or'((List.map (fun expr -> (rename_helper expr id)) exprlst))
    | LambdaSimple'(arglist, expr) -> LambdaSimple'(arglist, (rename_helper expr id))
    | LambdaOpt'(arglist, opt, expr) -> LambdaOpt'(arglist, opt, (rename_helper expr id))
    | Applic'(op, exprlst) -> Applic'((rename_helper op id), (List.map (fun expr -> (rename_helper expr id)) exprlst))
    | ApplicTP'(op, exprlst) -> ApplicTP'((rename_helper op id), (List.map (fun expr -> (rename_helper expr id)) exprlst))
    | _ -> ast;;

  let rec renaming asts id =
    match asts with
    | [] -> []
    | ast :: rest -> (rename_helper ast id) :: (renaming rest (id+1));;

  let rec ast_to_list ast = 
    match ast with 
    | Const'(Void) -> [Void]
    | Const'(Sexpr(sexp)) -> [Sexpr(sexp)]
    | BoxSet'(var, expr) -> ast_to_list expr
    | If'(test, dit, dif) -> (ast_to_list test) @ (ast_to_list dit) @ (ast_to_list dif)
    | Seq'(exprlst) -> List.fold_right (fun lst1 lst2 -> (ast_to_list lst1) @ lst2) exprlst []
    | Set'(expr1, expr2) -> (ast_to_list expr1) @ (ast_to_list expr2)
    | Def'(expr1, expr2) -> (ast_to_list expr1) @ (ast_to_list expr2)
    | Or'(exprlst) -> List.fold_right (fun lst1 lst2 -> (ast_to_list lst1) @ lst2) exprlst []
    | LambdaSimple'(arglist, expr) -> ast_to_list expr
    | LambdaOpt'(arglist, opt, expr) -> ast_to_list expr
    | Applic'(op, exprlst) -> List.fold_right (fun lst1 lst2 -> (ast_to_list lst1) @ lst2) exprlst (ast_to_list op)
    | ApplicTP'(op, exprlst) -> List.fold_right (fun lst1 lst2 -> (ast_to_list lst1) @ lst2) exprlst (ast_to_list op)
    | _ -> [];;

  let const_eq c1 c2 =
    match c1, c2 with
    | Void, Void -> true
    | Sexpr(x), Sexpr(y) -> sexpr_eq x y
    | _ -> false;;

  let rec remove_dups constants =
    match constants with
    | [] -> []
    | hd::tl -> hd :: (remove_dups (List.filter (fun const -> not (const_eq hd const)) tl));;

  let rec make_subs const =
    match const with
    | Sexpr(Symbol(str)) -> [Sexpr(String(str)); const]
    | Sexpr(Pair(sexp1, sexp2)) -> (make_subs (Sexpr(sexp1))) @ (make_subs (Sexpr(sexp2))) @ [const]
    | Sexpr(TaggedSexpr(tag, sexp)) -> make_subs (Sexpr(sexp)) @ [const]
    | _ -> [const];;

  let rec search const consts_tbl =
    match consts_tbl with
    | [] -> "-1"
    | (Void, (offset, str)) :: tl -> search const tl
    | (Sexpr(sexp), (offset, str)) :: tl -> if sexpr_eq sexp const then string_of_int offset else search const tl;;

  let rec build_consts_tbl all_consts offset consts_tbl =
    match all_consts with
    | [] -> consts_tbl
    | Void :: tl -> build_consts_tbl tl offset consts_tbl
    | Sexpr(sexp) :: tl -> (match sexp with
                            | Bool(x) -> build_consts_tbl tl offset consts_tbl
                            | Nil -> build_consts_tbl tl offset consts_tbl
                            | Number(Int(x)) -> let consts_tbl = consts_tbl @ [(Sexpr(sexp), (offset, "MAKE_LITERAL_INT(" ^ (string_of_int x) ^ ")"))] in
                                                build_consts_tbl tl (offset + 9) consts_tbl
                            | Number(Float(x)) -> let consts_tbl = consts_tbl @ [(Sexpr(sexp), (offset, "MAKE_LITERAL_FLOAT(" ^ (string_of_float x) ^ ")"))] in
                                                  build_consts_tbl tl (offset + 9) consts_tbl
                            | Char(x) -> let consts_tbl = consts_tbl @ [(Sexpr(sexp), (offset, "MAKE_LITERAL_CHAR(" ^ (string_of_int (int_of_char x )) ^ ")"))] in
                                         build_consts_tbl tl (offset + 2) consts_tbl
                            | String(x) -> let strlen = String.length x in
                                          let consts_tbl = consts_tbl @ [(Sexpr(sexp), (offset, "MAKE_LITERAL_STRING(" ^ (string_of_int strlen) ^ ", \"" ^ (String.escaped x) ^ "\")"))] in
                                           build_consts_tbl tl (offset + 9 + strlen) consts_tbl
                            | Symbol(x) -> let consts_tbl = consts_tbl @ [(Sexpr(sexp), (offset, "MAKE_LITERAL_SYMBOL(const_tbl+" ^ (search (String(x)) consts_tbl) ^ ")"))] in
                                            build_consts_tbl tl (offset + 9) consts_tbl
                            | Pair(sexpr1, sexpr2) -> let consts_tbl = consts_tbl @ [(Sexpr(sexp), (offset, ""))] in
                                                      build_consts_tbl tl (offset + 17) consts_tbl
                            | TagRef(x) -> build_consts_tbl tl offset consts_tbl
                            | TaggedSexpr(tag, sexp) -> build_consts_tbl tl offset consts_tbl
                            );;

  let rec search_name tag tag_defs all_consts =
    match tag_defs with
    | [] -> raise X_this_should_not_happen
    | (name, sexpr) :: tl -> if tag = name then search sexpr all_consts else search_name tag tl all_consts;;

  let rec search_all sexp all_consts tag_defs =
    match sexp with
    | TagRef(tag) -> search_name tag tag_defs all_consts
    | TaggedSexpr(tag, sexpr) -> search_name tag tag_defs all_consts
    | sexp -> search sexp all_consts;;

  let rec handle_tagged_sexprs iterate_tbl all_consts tag_defs =
    match iterate_tbl with
    | [] -> []
    | (Sexpr(Pair(sexpr1, sexpr2)), (p_offset, _)) :: tl -> let s1_off = search_all sexpr1 all_consts tag_defs in
                                                            let s2_off = search_all sexpr2 all_consts tag_defs in
                                                            (Sexpr(Pair(sexpr1, sexpr2)), (p_offset, "MAKE_LITERAL_PAIR(const_tbl+" ^s1_off^ ", const_tbl+" ^s2_off^ ")")) :: 
                                                            handle_tagged_sexprs tl all_consts tag_defs
    | (sexp, (p_offset, str)) :: tl -> (sexp, (p_offset, str)) :: handle_tagged_sexprs tl all_consts tag_defs;;

  let primitive_names_to_labels = 
    ["boolean?", "is_boolean"; "float?", "is_float"; "integer?", "is_integer"; "pair?", "is_pair";
      "null?", "is_null"; "char?", "is_char"; "string?", "is_string";
      "procedure?", "is_procedure"; "symbol?", "is_symbol"; "string-length", "string_length";
      "string-ref", "string_ref"; "string-set!", "string_set"; "make-string", "make_string";
      "symbol->string", "symbol_to_string"; 
      "char->integer", "char_to_integer"; "integer->char", "integer_to_char"; "eq?", "is_eq";
      "+", "bin_add"; "*", "bin_mul"; "-", "bin_sub"; "/", "bin_div"; "<", "bin_lt"; "=", "bin_equ"; 
      "car", "car"; "cdr", "cdr"; "cons", "cons"; "set-car!", "set_car"; "set-cdr!", "set_cdr"; "apply", "apply"];;

  let rec collect_fvars ast =
    match ast with 
    | Var'(VarFree(var)) -> [var]
    | Box'(VarFree(var)) -> [var]
    | BoxGet'(VarFree(var)) -> [var]
    | BoxSet'(var, expr) -> (match var with
                            | VarFree(x) -> x :: collect_fvars expr
                            | _ -> collect_fvars expr)
    | If'(test, dit, dif) -> (collect_fvars test) @ (collect_fvars dit) @ (collect_fvars dif)
    | Seq'(exprlst) -> List.fold_right (fun lst1 lst2 -> (collect_fvars lst1) @ lst2) exprlst []
    | Set'(expr1, expr2) -> (collect_fvars expr1) @ (collect_fvars expr2)
    | Def'(expr1, expr2) -> (collect_fvars expr1) @ (collect_fvars expr2)
    | Or'(exprlst) -> List.fold_right (fun lst1 lst2 -> (collect_fvars lst1) @ lst2) exprlst []
    | LambdaSimple'(arglist, expr) -> collect_fvars expr
    | LambdaOpt'(arglist, opt, expr) -> collect_fvars expr
    | Applic'(op, exprlst) -> List.fold_right (fun lst1 lst2 -> (collect_fvars lst1) @ lst2) exprlst (collect_fvars op)
    | ApplicTP'(op, exprlst) -> List.fold_right (fun lst1 lst2 -> (collect_fvars lst1) @ lst2) exprlst (collect_fvars op)
    | _ -> [];;

  let rec remove_dup_str vars =
    match vars with
    | [] -> []
    | hd::tl -> hd :: (remove_dup_str (List.filter (fun var -> not (hd = var)) tl));;

  let rec build_fvar_tbl fvars index =
    match fvars with
    | []->[]
    | hd::tl -> (hd, index) :: build_fvar_tbl tl (index+1);;

  let tag_definitions = ref [];;

  let rec gen consts fvars exp depth =
    match exp with
    (* | Const'(Sexpr(TagRef(tag))) -> "mov rax, const_tbl+" ^ (string_of_int (fst (List.assoc )))
    | Const'(Sexpr(TaggedSexpr(tag, sexpr))) -> "mov rax, const_tbl+" ^ (string_of_int (fst (List.assoc sexpr consts))) ^ "\n" *)
    | Const'(Void) -> "mov rax, const_tbl+" ^ (string_of_int (fst (List.assoc Void consts))) ^ "\n"
    | Const'(Sexpr(sexp)) -> "mov rax, const_tbl+" ^ (search_all sexp consts !tag_definitions) ^ "\n"
    | Var'(VarParam(_, minor)) -> "mov rax, PVAR(" ^ (string_of_int minor) ^ ")\n"
    | Set'(Var'(VarParam(_, minor)), expr) -> gen consts fvars expr depth ^
                                             "mov qword [rbp + (4 + " ^ (string_of_int minor) ^ ")*WORD_SIZE], rax\n" ^
                                             "mov rax, SOB_VOID_ADDRESS\n"
    | Var'(VarBound(_, major, minor)) -> "mov rax, qword [rbp + 2*WORD_SIZE]\n" ^
                                         "mov rax, qword [rax + " ^ (string_of_int major) ^ "*WORD_SIZE]\n" ^
                                         "mov rax, qword [rax + " ^ (string_of_int minor) ^ "*WORD_SIZE]\n"
    | Set'(Var'(VarBound(_, major, minor)), expr) -> gen consts fvars expr depth ^
                                                    "mov rbx, qword [rbp + 2*WORD_SIZE]\n" ^
                                                    "mov rbx, qword [rbx + " ^ (string_of_int major) ^ "*WORD_SIZE]\n" ^
                                                    "mov qword [rbx + " ^ (string_of_int minor) ^ "*WORD_SIZE], rax\n" ^
                                                    "mov rax, SOB_VOID_ADDRESS\n"
    | Var'(VarFree(var)) -> "mov rax, qword [fvar_tbl+" ^  (string_of_int (List.assoc var fvars)) ^ "*WORD_SIZE]\n"
    | Set'(Var'(VarFree(var)), expr) -> gen consts fvars expr depth ^
                                       "mov qword [fvar_tbl+" ^ string_of_int (List.assoc var fvars) ^ "*WORD_SIZE], rax\n" ^
                                       "mov rax, SOB_VOID_ADDRESS\n"
    | Def'(Var'(VarFree(var)), expr) -> gen consts fvars expr depth ^
                                       "mov qword [fvar_tbl+" ^ string_of_int (List.assoc var fvars) ^ "*WORD_SIZE], rax\n" ^
                                       "mov rax, SOB_VOID_ADDRESS\n"
    | Seq'(exprlst) -> List.fold_right (fun expr acc -> (gen consts fvars expr depth) ^ acc) exprlst ""
    | Or' (exprlst) -> let label = Labels.make_label "Lexit" in
                       List.fold_right (fun expr acc -> (gen consts fvars expr depth) ^ "cmp rax, SOB_FALSE_ADDRESS\n" ^
                                                                                        "jne " ^ label ^ "\n" ^ acc) 
                                                                                        exprlst (label ^ ":\n")
    | If'(test, dit, dif) -> let labels = Labels.make_labels ["Lelse"; "Lexit"] in
                             (gen consts fvars test depth) ^
                             "cmp rax, SOB_FALSE_ADDRESS\n" ^
                             "je " ^ (List.nth labels 0) ^ "\n" ^
                             (gen consts fvars dit depth) ^
                             "jmp " ^ (List.nth labels 1) ^ "\n" ^
                             (List.nth labels 0) ^ ":\n" ^
                             (gen consts fvars dif depth) ^
                             (List.nth labels 1) ^ ":\n"
    | Box'(var) -> (gen consts fvars (Var'(var)) depth) ^
                    "mov rbx, rax\n" ^
                    "MALLOC rax, WORD_SIZE\n" ^
                    "mov qword [rax], rbx \n "
    | BoxGet'(var) -> (gen consts fvars (Var'(var)) depth) ^
                      "mov rax, qword [rax]\n"
    | BoxSet'(var, expr) -> (gen consts fvars expr depth) ^
                            "push rax\n" ^
                            (gen consts fvars (Var'(var)) depth) ^
                            "pop qword [rax]\n" ^
                            "mov rax, SOB_VOID_ADDRESS\n"
    | LambdaSimple'(arglist, body) -> let labels = Labels.make_labels ["Lcode"; "Lcont"; "penvloop"; "tenvloop"; "LprevEnv"; "noArgs"] in
                                      let create_env = if depth = 0 then "mov rbx, SOB_NIL_ADDRESS\n" 
                                                                    else "MALLOC rax, WORD_SIZE*" ^ (string_of_int depth) ^ "\n" ^
                                                                         "mov rcx, " ^ (string_of_int (depth-1)) ^ "\n" ^
                                                                         "cmp rcx, 0\n" ^
                                                                         "jz " ^(List.nth labels 4) ^ "\n" ^
                                                                         "mov rbx, qword [rbp+2*WORD_SIZE]\n" ^
                                                                         (List.nth labels 2) ^ ":\n" ^
                                                                         "mov rdx, qword [rbx+(rcx-1)*WORD_SIZE]\n" ^
                                                                         "mov [rax+rcx*WORD_SIZE], qword rdx\n" ^
                                                                         "loop " ^ (List.nth labels 2) ^ "\n" ^
                                                                         (List.nth labels 4) ^ ":\n" ^
                                                                         "mov rcx, qword [rbp+3*WORD_SIZE]\n" ^
                                                                         (* "cmp rcx, 0\n" ^
                                                                         "jz " ^ (List.nth labels 5) ^ "\n" ^ *)
                                                                         "inc rcx\n" ^ (*changed*)
                                                                         "shl rcx, 3\n" ^
                                                                         "MALLOC rbx, rcx\n" ^
                                                                         "shr rcx, 3\n" ^
                                                                         "mov qword [rbx + (rcx-1)*WORD_SIZE], SOB_NIL_ADDRESS\n" ^ (*changed*)
                                                                         "dec rcx\n" ^ (*changed*)
                                                                         "jz " ^ (List.nth labels 5) ^ "\n" ^ (*changed*)
                                                                         (List.nth labels 3) ^ ":\n" ^
                                                                         "mov rdx, qword PVAR(rcx-1)\n" ^
                                                                         "mov [rbx+(rcx-1)*WORD_SIZE], qword rdx\n" ^
                                                                         "loop " ^ (List.nth labels 3) ^ "\n" ^
                                                                         "mov [rax], qword rbx\n" ^
                                                                         (List.nth labels 5) ^ ":\n" ^
                                                                         "mov rbx, rax\n" in
                                      create_env ^
                                      (* Allocate closure object *)
                                      "MAKE_CLOSURE (rax, rbx, " ^ (List.nth labels 0) ^ ")\n" ^
                                      "jmp " ^ (List.nth labels 1) ^ "\n" ^
                                      (* Code *)
                                      (List.nth labels 0) ^ ":\n" ^
                                      "push rbp\n" ^
                                      "mov rbp, rsp\n" ^
                                      (gen consts fvars body (depth+1)) ^
                                      "leave\n" ^
                                      "ret\n" ^
                                      (* End of Code *)
                                      (List.nth labels 1) ^ ":\n"
    | LambdaOpt'(arglist, opt, body) -> let arg_size = string_of_int (List.length arglist) in
                                        let labels = Labels.make_labels ["Lcode"; "Lcont"; "penvloop"; "tenvloop"; "LprevEnv"; "noArgs";"LendAdj"; "Lmakeopt";"LcopyArgs"] in
                                        let create_env = if depth = 0 then "mov rbx, SOB_NIL_ADDRESS\n" 
                                                                      else "MALLOC rax, WORD_SIZE*" ^ (string_of_int depth) ^ "\n" ^
                                                                          "mov rcx, " ^ (string_of_int (depth-1)) ^ "\n" ^
                                                                          "cmp rcx, 0\n" ^
                                                                          "jz " ^(List.nth labels 4) ^ "\n" ^
                                                                          "mov rbx, qword [rbp+2*WORD_SIZE]\n" ^
                                                                          (List.nth labels 2) ^ ":\n" ^
                                                                          "mov rdx, qword [rbx+(rcx-1)*WORD_SIZE]\n" ^
                                                                          "mov [rax+rcx*WORD_SIZE], qword rdx\n" ^
                                                                          "loop " ^ (List.nth labels 2) ^ "\n" ^
                                                                          (List.nth labels 4) ^ ":\n" ^
                                                                          "mov rcx, qword [rbp+3*WORD_SIZE]\n" ^
                                                                          (* "cmp rcx, 0\n" ^
                                                                          "jz " ^ (List.nth labels 5) ^ "\n" ^ *)
                                                                          "inc rcx\n" ^ (*changed*)
                                                                          "shl rcx, 3\n" ^
                                                                          "MALLOC rbx, rcx\n" ^
                                                                          "shr rcx, 3\n" ^
                                                                          "mov qword [rbx + (rcx-1)*WORD_SIZE], SOB_NIL_ADDRESS\n" ^ (*changed*)
                                                                          "dec rcx\n" ^ (*changed*)
                                                                          "jz " ^ (List.nth labels 5) ^ "\n" ^ (*changed*)
                                                                          (List.nth labels 3) ^ ":\n" ^
                                                                          "mov rdx, qword PVAR(rcx-1)\n" ^
                                                                          "mov [rbx+(rcx-1)*WORD_SIZE], qword rdx\n" ^
                                                                          "loop " ^ (List.nth labels 3) ^ "\n" ^
                                                                          "mov [rax], qword rbx\n" ^
                                                                          (List.nth labels 5) ^ ":\n" ^
                                                                          "mov rbx, rax\n" in
                                        create_env ^
                                        (* Allocate closure object *)
                                        "MAKE_CLOSURE (rax, rbx, " ^ (List.nth labels 0) ^ ")\n" ^
                                        "jmp " ^ (List.nth labels 1) ^ "\n" ^
                                        (* Code *)
                                        (List.nth labels 0) ^ ":\n" ^
                                        (* ADJUST STACK *)
                                        "mov rcx, qword [rsp+2*WORD_SIZE]\n" ^ (*rcx = argcount*)
                                        "sub rcx, qword " ^ arg_size ^ "\n" ^ (*rcx = argcount - arglist size*)
                                        (* "cmp rcx, qword 0\n" ^ *)
                                        "jz "^ (List.nth labels 6) ^ "\n" ^ (*if num of args in stk <= arglist*)
                                        "mov rsi, qword [rsp+2*WORD_SIZE]\n" ^ (*rsi = argcount*)
                                        "add rsi, 2\n" ^ (*rsi = pointer one block under magic*)
                                        "shl rsi, 3\n" ^
                                        "add rsi, rsp\n" ^
                                        (List.nth labels 7) ^ ":\n" ^
                                        "mov qword rbx, [rsi]\n" ^
                                        "mov qword rdx, [rsi+WORD_SIZE]\n" ^
                                        "MAKE_PAIR (rax, rbx, rdx)\n" ^
                                        "mov qword [rsi], rax\n" ^
                                        "sub rsi, WORD_SIZE \n" ^
                                        "loop " ^ (List.nth labels 7) ^ "\n" ^
                                        (* COPYING STACK *)
                                        "add rsi, WORD_SIZE\n" ^ (*rbx = points above magic*)
                                        "mov rdi, qword [rsp+2*WORD_SIZE]\n" ^ (*rdi = argcount*)
                                        "add rdi, 2\n" ^
                                        "shl rdi, 3\n" ^
                                        "add rdi, rsp\n" ^
                                        "mov rcx, qword " ^ arg_size ^ "\n" ^
                                        "add rcx, 4\n" ^
                                        (List.nth labels 8) ^ ":\n" ^
                                        "mov rax, qword [rsi]\n" ^
                                        "mov [rdi], qword rax\n" ^
                                        "sub rsi, WORD_SIZE\n" ^
                                        "sub rdi, WORD_SIZE\n" ^
                                        "loop " ^ (List.nth labels 8) ^ "\n" ^
                                        "add rdi, WORD_SIZE\n" ^
                                        "mov rsp, rdi\n" ^
                                        "mov rcx, " ^ arg_size ^ "\n" ^
                                        "inc rcx\n" ^
                                        "mov [rsp+2*WORD_SIZE], rcx\n" ^
                                        (List.nth labels 6) ^ ":\n" ^
                                        (* NO MORE ADJUST *)
                                        "push rbp\n" ^
                                        "mov rbp, rsp\n" ^
                                        (gen consts fvars body (depth+1)) ^
                                        "leave\n" ^
                                        "ret\n" ^
                                        (* End of Code *)
                                        (List.nth labels 1) ^ ":\n"
    | Applic'(proc, exprlst) -> let n = string_of_int (List.length exprlst) in
                                        "push SOB_NIL_ADDRESS\n" ^
                                        (List.fold_left (fun acc expr -> (gen consts fvars expr depth) ^ "push rax\n" ^ acc)
                                                ("push " ^ n ^ "\n" ^ (gen consts fvars proc depth) ^ 
                                                "CLOSURE_ENV rbx, rax\n" ^
                                                "push rbx\n" ^
                                                "CLOSURE_CODE rax, rax\n" ^
                                                "call rax\n" ^
                                                "add rsp, 8*1\n" ^
                                                "pop rbx\n" ^
                                                "shl rbx, 3\n" ^
                                                "add rsp, rbx\n" ^
                                                "add rsp, WORD_SIZE\n")
                                                exprlst)
    | ApplicTP'(proc, exprlst) -> let label = Labels.make_label "copy" in 
                                  let n = string_of_int (List.length exprlst) in
                                  "push SOB_NIL_ADDRESS\n" ^
                                  (List.fold_left (fun acc expr -> (gen consts fvars expr depth) ^ "push rax\n" ^ acc)
                                  ("push " ^ n ^ "\n" ^ (gen consts fvars proc depth) ^ 
                                  "CLOSURE_ENV rbx, rax\n" ^
                                  "push rbx\n" ^
                                  "push qword [rbp + WORD_SIZE]\n" ^

                                  (*FIXING STACK*)
                                  "mov rsi, rbp\n" ^
                                  "mov rbp, qword [rbp]\n" ^
                                  "mov rcx, [rsi + 3*WORD_SIZE]\n" ^ (* rcx = n *)
                                  "add rcx, 3\n" ^
                                  "shl rcx, 3\n" ^
                                  "add rsi, rcx\n" ^ (* rsi = pointer to A-n-1 *)
                                  "mov rcx, [rsp + 2*WORD_SIZE]\n" ^ (* rcx = m *)
                                  "add rcx, 3\n" ^ (* rcx = m + 3 *)
                                  label ^ ":\n" ^ 
                                  " mov rdx, qword [rsp + (rcx-1)*WORD_SIZE]\n" ^
                                  " mov [rsi], qword rdx\n" ^
                                  " sub rsi, WORD_SIZE\n" ^
                                  " loop " ^ label ^ "\n" ^
                                  "add rsi, WORD_SIZE\n" ^
                                  "mov rsp, rsi\n" ^
                                  (*DONE*)

                                  "CLOSURE_CODE rax, rax\n" ^
                                  "jmp rax\n" ^
                                  "add rsp, 8*1\n" ^
                                  "pop rbx\n" ^
                                  "shl rbx, 3\n" ^
                                  "add rsp, rbx\n" ^
                                  "add rsp, WORD_SIZE\n")
                                  exprlst)
    | _ -> "";;

  let make_consts_tbl asts =
    let consts_list = List.fold_right (fun lst1 acc -> (ast_to_list lst1) @ acc) asts [] in
    let consts_set = remove_dups consts_list in
    let all_consts_list = List.fold_right (fun lst1 lst2 -> (make_subs lst1) @ lst2) consts_set [] in
    let all_consts_set = remove_dups all_consts_list in
    tag_definitions := List.fold_right (fun sexp1 acc -> (match sexp1 with
                                                  | Sexpr(TaggedSexpr(tag, sexpr)) -> (tag, sexpr) :: acc
                                                  | _ -> acc)) all_consts_set [] ;
    let initial_const_tbl = [(Void, (0, "MAKE_VOID"));
                              (Sexpr(Nil), (1, "MAKE_NIL"));
                              (Sexpr(Bool false), (2, "MAKE_BOOL(0)"));
                              (Sexpr(Bool true), (4, "MAKE_BOOL(1)"))] in
    let all_consts = build_consts_tbl all_consts_set 6 initial_const_tbl in
    let consts_tbl = handle_tagged_sexprs all_consts all_consts !tag_definitions in
    consts_tbl;;

  let make_fvars_tbl asts = 
    let init_fvar = List.map fst primitive_names_to_labels in
    let fvar_list = init_fvar @ (List.fold_right (fun ast acc -> (collect_fvars ast) @ acc) asts []) in
    let fvar_set = remove_dup_str fvar_list in
    let fvar_tbl = build_fvar_tbl fvar_set 0 in
    fvar_tbl;;

  let generate consts fvars e = gen consts fvars e 0;;
end;;

