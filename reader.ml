
#use "pc.ml";;
open PC;;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;
  
type number =
  | Int of int
  | Float of float;;
  
type sexpr =
  | Bool of bool
  | Nil
  | Number of number
  | Char of char
  | String of string
  | Symbol of string
  | Pair of sexpr * sexpr
  | TaggedSexpr of string * sexpr
  | TagRef of string;;

let rec sexpr_eq s1 s2 =
  match s1, s2 with
  | Bool(b1), Bool(b2) -> b1 = b2
  | Nil, Nil -> true
  | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
  | Number(Int n1), Number(Int n2) -> n1 = n2
  | Char(c1), Char(c2) -> c1 = c2
  | String(s1), String(s2) -> s1 = s2
  | Symbol(s1), Symbol(s2) -> s1 = s2
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  | TaggedSexpr(name1, expr1), TaggedSexpr(name2, expr2) -> (name1 = name2) && (sexpr_eq expr1 expr2) 
  | TagRef(name1), TagRef(name2) -> name1 = name2
  | _ -> false;;

  let make_paired nt_left nt_right nt =
    let nt = caten nt_left nt in
    let nt = pack nt (function (_, e) -> e) in
    let nt = caten nt nt_right in
    let nt = pack nt (function (e, _) -> e) in
    nt;;

  let tok_true =
    let nt = caten (char '#') (char_ci 't') in
    let nt = pack nt (fun (t) -> Bool(true)) in
    nt;;

  let tok_false =
    let nt = caten (char '#') (char_ci 'f') in
    let nt = pack nt (fun (f) -> Bool(false)) in
    nt;;

  let tok_bool = disj tok_true tok_false;;

  let nt_vsc = const (fun ch -> ch > ' ');;

  let nt_nul = pack (word_ci "nul") (fun (nul) -> char_of_int 0);;
  let nt_newline = pack (word_ci "newline") (fun (newline) -> char_of_int 10);;
  let nt_return = pack (word_ci "return") (fun (return) -> char_of_int 13);;
  let nt_tab = pack (word_ci "tab") (fun (tab) -> char_of_int 9);;
  let nt_formfeed = pack (word_ci "page") (fun (page) -> char_of_int 12);;
  let nt_space = pack (word_ci "space") (fun (space) -> char_of_int 32);;

  let nt_nc = disj_list [nt_nul; nt_newline; nt_return; nt_tab; nt_formfeed; nt_space];;

  let tok_char =
    let nt_prefix = word "#\\" in
    let nt = disj nt_nc nt_vsc in
    let nt = caten nt_prefix nt in
    let nt = pack nt (fun (prefix, ch) -> Char(ch)) in
    nt;;

  let digit = range '0' '9';;
  let nt_natural = plus digit;;
  let nt_sign = disj (char '+') (char '-');;
  let nt_punctuation = one_of "!$^*-_=+<>/?:";;
  let nt_lowercase = range 'a' 'z';;
  let nt_uppercase = range 'A' 'Z';;

  let nt_signed =
    let nt = caten nt_sign nt_natural in
    let nt = pack nt (fun (sign, natural) -> sign::natural) in
    nt;;

  let nt_int = disj nt_natural nt_signed;;
  let tok_int = pack nt_int (fun (ds) -> Int (int_of_string (list_to_string ds)));;

  let nt_float =
    let nt = caten nt_int (char '.') in
    let nt = pack nt (fun (integer, dot) -> List.append integer [dot]) in
    let nt = caten nt nt_natural in
    let nt = pack nt (fun (integer, natural) -> List.append integer natural) in
    nt;;

  let tok_float = pack nt_float (fun (ds) -> Float (float_of_string (list_to_string ds)));;

  let tok_scientific =
    let nt = disj nt_float nt_int in
    let nt = caten nt (char_ci 'e') in
    let nt = pack nt (fun (num, e) -> List.append num [e]) in
    let nt = caten nt nt_int in
    let nt = pack nt (fun (num, sci) -> List.append num sci) in
    let nt = pack nt (fun ds -> Float(float_of_string (list_to_string ds))) in
    nt;;

  let nt_radix_prefix =
    let nt = caten (char '#') nt_natural in
    let nt = caten nt (char_ci 'r') in
    let nt = pack nt (fun ((hashtag, base), r) -> (int_of_string (list_to_string base))) in
    nt;;

  let nt_radix_natural =
    let make_nt_digit ch_from ch_to displacement =
      let nt = const (fun ch -> ch_from <= ch && ch <= ch_to) in
      let nt = pack nt (let delta = (Char.code ch_from) - displacement in
            fun ch -> (Char.code ch) - delta) in
      nt in
    let nt = disj (make_nt_digit '0' '9' 0) (make_nt_digit 'a' 'z' 10) in
    let nt = disj nt (make_nt_digit 'A' 'Z' 10) in
    plus nt;;

  let nt_radix_signed_int = caten nt_sign nt_radix_natural;;

  let nt_radix_unsigned_float =
    let nt = caten nt_radix_natural (char '.') in
    let nt = pack nt (fun (before, dot) -> before) in
    let nt = caten nt nt_radix_natural in
    let nt = pack nt (fun (before, after) -> (before, (List.map (fun x -> float_of_int x) after))) in
    nt;;

  let nt_radix_signed_float = caten nt_sign nt_radix_unsigned_float;;

  let tok_radix_natural =
    let nt = caten nt_radix_prefix nt_radix_natural in
    let nt = pack nt (fun (base, natural) -> List.fold_left (fun a b -> base * a + b) 0 natural) in
    nt;;

  let tok_radix_signed_int =
    let nt = caten nt_radix_prefix nt_radix_signed_int in
    let nt = pack nt (fun (base, (sign, natural)) -> match sign with
    | '-' -> (List.fold_left (fun a b -> base * a + b) 0 natural) * (-1)
    | '+' -> List.fold_left (fun a b -> base * a + b) 0 natural
    | _ -> 0) in
    nt;;

  let tok_radix_int =
    let nt = disj tok_radix_signed_int tok_radix_natural in
    let nt = pack nt (fun integer -> Int(integer)) in
    nt;;

  let tok_radix_unsigned_float =
    let nt = caten nt_radix_prefix nt_radix_unsigned_float in
    let nt = pack nt (fun (base, (before, after)) ->
                                    (float_of_int (List.fold_left (fun a b -> base * a + b) 0 before)) +.
                                    (List.fold_right (fun a b -> (a +. b) /. (float_of_int base)) after 0.0)) in
    nt;;

  let tok_radix_signed_float =
    let nt = caten nt_radix_prefix nt_radix_signed_float in
    let nt = pack nt (fun (base, (sign, (before, after))) -> match sign with
    | '-' -> (-1.0) *. ((float_of_int (List.fold_left (fun a b -> base * a + b) 0 before)) +.
              (List.fold_right (fun a b -> (a +. b) /. (float_of_int base)) after 0.0))
    | '+' -> (float_of_int (List.fold_left (fun a b -> base * a + b) 0 before)) +.
              (List.fold_right (fun a b -> (a +. b) /. (float_of_int base)) after 0.0)
    | _ -> 0.0) in
    nt;;

  let tok_radix_float =
    let nt = disj tok_radix_signed_float tok_radix_unsigned_float in
    let nt = pack nt (fun f -> Float(f)) in
    nt;;

  let tok_radix = disj tok_radix_float tok_radix_int;;

  let tok_num =
    let nt = disj_list [tok_radix; tok_scientific; tok_float; tok_int] in
    let nt = not_followed_by nt (disj_list [nt_punctuation; nt_lowercase; nt_uppercase]) in
    let nt = pack nt (fun (num) -> Number (num)) in
    nt;;

  let nt_sym_char = disj_list [digit; nt_lowercase; nt_uppercase; nt_punctuation];;
  let nt_symbol = pack (plus nt_sym_char) (List.map (fun ch -> lowercase_ascii ch));;
  let tok_symbol = pack nt_symbol (fun (sym) -> Symbol (list_to_string sym));;

  let nt_literal = diff nt_any (disj (char '\"') (char '\\'));;
  let nt_meta = disj_list [pack (word_ci "\\\\") (fun ch -> '\\');
                           pack (word_ci "\\\"") (fun ch -> '"');
                           pack (word_ci "\\t") (fun ch -> '\t');
                           pack (word_ci "\\n") (fun ch -> '\n');
                           pack (word_ci "\\r") (fun ch -> '\r');
                           pack (word_ci "\\f") (fun ch -> char_of_int 12)];;

  let nt_string_char = disj nt_literal nt_meta;;
  let tok_string =
    let nt = star nt_string_char in
    let nt = make_paired (char '\"') (char '\"') nt in
    let nt = pack nt (fun lst -> String(list_to_string lst)) in
    nt;;

  let nt_nested nt = make_paired (char '(') (char ')') nt;;

  let rec flat sexp =
    match sexp with
    | Pair(sexp1, sexp2) -> List.append (flat sexp1) (flat sexp2)
    | TaggedSexpr(tag, sexp3) -> tag :: (flat sexp3)
    | _ -> [] ;;

  let rec tag_check tag arr =
    match arr with
    | [] -> true
    | hd::tl -> (not (tag = hd)) && (tag_check tag tl);;

  let rec valid_check arr =
    match arr with
    | [] -> true
    | hd::tl -> (tag_check hd tl) && (valid_check tl);;

  let rec tok_sexpr s =
    let nt = disj_list [tok_bool; tok_char; tok_num; tok_string; tok_symbol; tok_list; tok_nil;
                        tok_dotted; tok_quote; tok_quasi; tok_unquote; tok_uas; tok_tagged_sexp] in
    let nt = pack nt (fun sexp -> match (valid_check (flat sexp)) with
                                          | false -> raise X_this_should_not_happen
                                          | true -> sexp) in
    (make_spaced nt) s

  and make_spaced nt s =
    (make_paired (star nt_garbage) (star nt_garbage) nt) s

  and tok_list s =
    let nt = plus tok_sexpr in
    let nt = nt_nested nt in
    let nt = pack nt
      (fun lst -> List.fold_right (fun car cdr -> Pair(car, cdr)) lst Nil) in
    nt s

  and tok_nil s =
    let nt = nt_nested (star nt_garbage) in
    let nt = pack nt (fun garbage -> Nil) in
    nt s

  and tok_dotted s =
    let nt = plus tok_sexpr in
    let nt = caten nt (char '.') in
    let nt = pack nt (fun (sexprs, dot) -> sexprs) in
    let nt = caten nt tok_sexpr in
    let nt = pack nt (fun (sexprs, sexpr) -> List.fold_right (fun car cdr -> Pair(car, cdr)) sexprs sexpr) in
    let nt = nt_nested nt in
    nt s

  and tok_quote s =
    let nt = caten (char '\'') tok_sexpr in
    let nt = pack nt (fun (quote, sexpr) -> Pair(Symbol("quote"), Pair(sexpr, Nil))) in
    nt s

  and tok_quasi s =
    let nt = caten (char '`') tok_sexpr in
    let nt = pack nt (fun (quasi, sexpr) -> Pair(Symbol("quasiquote"), Pair(sexpr, Nil))) in
    nt s

  and tok_unquote s =
    let nt = caten (char ',') tok_sexpr in
    let nt = pack nt (fun (unquote, sexpr) -> Pair(Symbol("unquote"), Pair(sexpr, Nil))) in
    nt s

  and tok_uas s =
    let nt = caten (word ",@") tok_sexpr in
    let nt = pack nt (fun (uas, sexpr) -> Pair(Symbol("unquote-splicing"), Pair(sexpr, Nil))) in
    nt s

  and nt_tag s =
    let nt = make_paired (char '{') (char '}') nt_symbol in
    let nt = caten (char '#') nt in
    let nt = pack nt (fun (hashtag, tag) -> tag) in
    nt s

  and tok_tag s =
    let nt = pack nt_tag (fun tag -> TagRef((list_to_string tag))) in
    nt s

  and tok_tagged s =
    let nt = caten nt_tag (char '=') in
    let nt = pack nt (fun (tag, equal) -> tag) in
    let nt = caten nt tok_sexpr in
    let nt = pack nt (fun (tag, sexpr) -> TaggedSexpr((list_to_string tag), sexpr)) in
    nt s

  and tok_tagged_sexp s = (disj tok_tagged tok_tag) s

  and nt_linecomment s =
    let nt_end = disj (pack (char '\n') (fun _ -> Nil)) (pack nt_end_of_input (fun _ -> Nil)) in
    let nt = diff nt_any nt_end in
    let nt = star nt in
    let nt = caten (char ';') nt in
    let nt = pack nt (fun (semicolon, comment) -> Nil) in
    let nt = caten nt nt_end in
    let nt = pack nt (fun _ -> Nil) in
    nt s

  and nt_sexpcomment s =
    let nt = word "#;" in
    let nt = caten nt tok_sexpr in
    let nt = pack nt (fun _ -> Nil) in
    nt s

  and nt_garbage s = disj_list [nt_linecomment;
                              nt_sexpcomment;
                              pack nt_whitespace (fun space -> Nil)] s;;

module Reader: sig
  val read_sexpr : string -> sexpr
  val read_sexprs : string -> sexpr list
end
= struct
let normalize_scheme_symbol str =
  let s = string_to_list str in
  if (andmap
	(fun ch -> (ch = (lowercase_ascii ch)))
	s) then str
  else Printf.sprintf "|%s|" str;;

let read_sexpr string =
  let (node, rest) = tok_sexpr (string_to_list string) in node;;

let read_sexprs string =
  let (ast, rest) = (star tok_sexpr) (string_to_list string) in ast;;

end;; (* struct Reader *)
