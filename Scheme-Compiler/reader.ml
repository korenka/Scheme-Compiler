(* reader.ml
 * A skeleton for the reader for the 2021-2022 course on compiler-construction
 *)

 #use "pc.ml";;
 let rec gcd a b =
   match (a, b) with
   | (0, b) -> b
   | (a, 0) -> a
   | (a, b) -> gcd b (a mod b);;
 

 type scm_number =
   | ScmRational of (int * int)
   | ScmReal of float;;
 
 type sexpr =
   | ScmVoid
   | ScmNil
   | ScmBoolean of bool
   | ScmChar of char
   | ScmString of string
   | ScmNumber of scm_number
   | ScmVector of (sexpr list)
   | ScmSymbol of string
   | ScmPair of (sexpr * sexpr);;
 
 module type READER = sig
     val nt_sexpr : sexpr PC.parser
 end;; (* end of READER signature *)
 
 module Reader : READER = struct
 open PC;;
 
 let unitify nt = pack nt (fun _ -> ());;
 
 let rec nt_whitespace str =
   const (fun ch -> ch <= ' ') str
   
 and nt_end_of_line_or_file str =
   let nt1 = unitify (char '\n') in
   let nt2 = unitify nt_end_of_input in
   let nt1 = disj nt1 nt2 in
   nt1 str

 and nt_line_comment str =
  let nt1 = char ';' in
  let nt2 = diff nt_any nt_end_of_line_or_file in
  let nt2 = star nt2 in
  let nt1 = caten nt1 (caten nt2 nt_end_of_line_or_file) in
  let nt1 = unitify nt1 in
  nt1 str


and nt_paired_comment str = 
  let nt1 = char '{' in 
  let nt2 = disj_list[unitify nt_char; unitify nt_string; unitify nt_comment] in
  let nt2' = disj nt2 (unitify (one_of"{}")) in
  let nt3 = diff nt_any nt2' in
  let nt3 = disj (unitify nt3) nt2 in
  let nt3 = star nt3 in
  let nt4 = char '}' in 
  let nt1 = unitify (caten nt1 (caten nt3 nt4)) in
  nt1 str

 and nt_sexpr_comment str = 
  let nt1 = caten (word "#;") nt_sexpr in
  let nt1 = unitify nt1 in
  nt1 str

 and nt_comment str =
   disj_list [nt_line_comment; nt_paired_comment; nt_sexpr_comment] str

 and nt_skip_star str =
   let nt1 = disj (unitify nt_whitespace) nt_comment in
   let nt1 = unitify (star nt1) in
   nt1 str

 and make_skipped_star (nt : 'a parser) =
   let nt1 = caten nt_skip_star (caten nt nt_skip_star) in
   let nt1 = pack nt1 (fun (_, (e, _)) -> e) in
   nt1

 and nt_int str = 
  let nt_minus = word "-" in 
  let nt_plus = word "+" in
  let nt_minus = caten nt_minus nt_integer_part in
  let nt_plus = caten nt_plus nt_integer_part in
  let nt_minus = pack nt_minus (fun (a,b) -> (-1)*b) in
  let nt_plus = pack nt_plus (fun (a,b) -> b) in
  let nt_out = disj_list [nt_integer_part; nt_minus; nt_plus] in
  nt_out str



 and nt_frac str =
  let nt_div = char '/' in
  let nt_numinator = caten nt_int nt_div in
  let nt_numinator = pack nt_numinator (fun (a,b) -> a) in
  let nt_denominator = caten nt_numinator nt_integer_part in 
  let nt_total = pack nt_denominator(fun (a,b) -> if b == 0 then raise X_no_match else ScmRational(a/(gcd a b), b/(gcd a b))) in
  nt_total str


 and nt_integer_part str = 
  let nt = range '0' '9' in
  let nt = plus nt in
  let nt = pack nt (fun (a) -> list_to_string a) in
  let nt = pack nt (fun (a) -> int_of_string a) in
  nt str

 and nt_mantissa str = 
  let nt1 = pack nt_integer_part (fun a ->
    let str_num = string_of_int a in
    let num_len = String.length str_num in
    let div = 10.0 ** (float_of_int num_len) in
    let numb = float a in
    let ans = numb /. div in ans) in 
    nt1 str

 and nt_exponent_token str =
  let nt_exp1 = char_ci 'e' in
  let nt_exp1 = pack nt_exp1 (fun _ -> 10) in
  let nt_exp2 = word "*10^" in
  let nt_exp2 = pack nt_exp2 (fun _ -> 10) in
  let nt_exp3 = word "*10**" in
  let nt_exp3 = pack nt_exp3 (fun _ -> 10) in
  let nt_out = disj_list [nt_exp1; nt_exp2; nt_exp3] in
  let nt_out = pack nt_out (fun _ -> 10) in
  nt_out str

 and nt_exponent str = 
  let nt1 = caten nt_exponent_token nt_int in
  let nt1 = pack nt1 (fun (token, integer) -> (float_of_int 10) ** (float_of_int integer)) in
  nt1 str

and nt_floatA str =
  let nt_dot = char '.' in
  let nt_int_part = caten nt_integer_part nt_dot in
  let nt_int_part = pack nt_int_part (fun (a,b) -> float_of_int a) in
  let nt_mantissa_part = caten nt_int_part nt_mantissa in
  let nt_mantissa_part = pack nt_mantissa_part (fun (a,b) -> a+.b) in
  let mantissa_exp = caten nt_mantissa_part nt_exponent in
  let mantissa_exp = pack mantissa_exp (fun (a,b) -> a*.b) in
  let nt_exp = caten nt_int_part nt_exponent in
  let nt_exp = pack nt_exp (fun (a,b) -> a*.b) in
  let nt_out = disj_list [mantissa_exp; nt_mantissa_part; nt_exp; nt_int_part] in
  nt_out str

and nt_floatB str = 
  let nt_dot = char '.' in
  let nt1 = caten nt_dot nt_mantissa in
  let nt1 = pack nt1 (fun (a,b) -> b) in
  let nt2 = caten nt1 nt_exponent in
  let nt2 = pack nt2 (fun (a,b) -> a*.b) in
  let nt_out = disj nt2 nt1 in
  nt_out str

and nt_floatC str = 
  let nt1 = caten nt_integer_part nt_exponent in
  let nt1 = pack nt1 (fun (a,b) -> (float_of_int a)*.b) in
  nt1 str
  
and nt_float str = 
let nt_floats = disj_list [nt_floatA; nt_floatB; nt_floatC] in
let nt_plus = char '+' in
let nt2 = caten nt_plus nt_floats in
let nt2 = pack nt2 (fun (a,b) -> b) in
let nt_minus = char '-' in
let nt3 = caten nt_minus nt_floats in
let nt3 = pack nt3 (fun (a,b) -> (-1.0)*.b) in
let nt_out = disj_list [nt_floats; nt2; nt3] in
let nt_out = pack nt_out (fun a -> ScmReal a) in
nt_out str

and nt_number str = 
  let nt3 = pack nt_int (fun n -> ScmRational(n, 1)) in
  let nt2 = nt_frac in
  let nt1 = nt_float in
  let nt1 = disj nt1 nt2 in
  let nt1 = disj nt1 nt3 in
  let nt1 = pack nt1 (fun r -> ScmNumber r) in
  let nt1 = not_followed_by nt1 nt_symbol_char in
  nt1 str

and nt_boolean str = 
  let nt_f = word_ci "#f" in
  let nt_f = pack nt_f (fun (a) -> false) in
  let nt_t = word_ci "#t" in
  let nt_t = pack nt_t (fun (a) -> true) in
  let nt_out = disj nt_f nt_t in
  let nt_out = pack nt_out (fun (b) -> ScmBoolean b) in
  nt_out str

and nt_char_simple str = 
  const (fun ch -> ch > ' ') str

and make_named_char char_name ch = 
  let nt1 = word_ci char_name in
  let nt1 = pack nt1 (fun (a) -> ch) in
  nt1

and nt_char_named str =
   let nt1 =
     disj_list [(make_named_char "newline" '\n');
                (make_named_char "page" '\012');
                (make_named_char "return" '\r');
                (make_named_char "space" ' ');
                (make_named_char "tab" '\t');
                (make_named_char "nul" '\000')] in
   nt1 str

and nt_char_hex str = 
  let nt0 = char_ci '0' in
  let nt0 = pack nt0 (fun (_) ->  0) in
  let nt1 = char_ci '1' in
  let nt1 = pack nt1 (fun (_) ->  1) in
  let nt2 = char_ci '2' in
  let nt2 = pack nt2 (fun (_) ->  2) in
  let nt3 = char_ci '3' in
  let nt3 = pack nt3 (fun (_) ->  3) in
  let nt4 = char_ci '4' in
  let nt4 = pack nt4 (fun (_) ->  4) in
  let nt5 = char_ci '5' in
  let nt5 = pack nt5 (fun (_) ->  5) in
  let nt6 = char_ci '6' in
  let nt6 = pack nt6 (fun (_) ->  6) in
  let nt7 = char_ci '7' in
  let nt7 = pack nt7 (fun (_) ->  7) in
  let nt8 = char_ci '8' in
  let nt8 = pack nt8 (fun (_) ->  8) in
  let nt9 = char_ci '9' in
  let nt9 = pack nt9 (fun (_) ->  9) in
  let nta = char_ci 'a' in
  let nta = pack nta (fun (_) ->  10) in
  let ntb = char_ci 'b' in
  let ntb = pack ntb (fun (_) ->  11) in
  let ntc = char_ci 'c' in
  let ntc = pack ntc (fun (_) ->  12) in
  let ntd = char_ci 'd' in
  let ntd = pack ntd (fun (_) ->  13) in
  let nte = char_ci 'e' in
  let nte = pack nte (fun (_) ->  14) in
  let ntf = char_ci 'f' in
  let ntf = pack ntf (fun (_) ->  15) in
  let nt_out = disj_list[nt0; nt1; nt2; nt3; nt4; nt5; nt6; nt7; nt8; nt9; nta; ntb; ntc; ntd; nte; ntf] in
  nt_out str

 and nt_char str = 
  let nt_char_prefix = word "#\\" in
  let nt1 = disj nt_hex_char nt_char_named in
  let nt1 = disj nt1 (not_followed_by nt_char_simple nt_any) in
  let nt_out = caten nt_char_prefix nt1 in
  let nt_out = pack nt_out (fun (prefix,ch) -> ScmChar ch) in
  nt_out str

 and nt_symbol_char str = 
  let nt4 = char '!' in 
  let nt5 = char '$' in 
  let nt6 = char '^' in 
  let nt7 = char '*' in 
  let nt8 = char '-' in 
  let nt9 = char '_' in 
  let nt10 = char '=' in 
  let nt11 = char '+' in 
  let nt12 = char '<' in 
  let nt13 = char '>' in 
  let nt14 = char '?' in 
  let nt15 = char '/' in 
  let nt16 = char ':' in 
  let nt1 = range '0' '9' in
  let nt2 = range_ci 'a' 'z' in 
  let nt_out = disj_list [nt1; nt2; nt4; nt5; nt6; nt7; nt8; nt9; nt10; nt11; nt12; nt13; nt14; nt15; nt16;] in 
  nt_out str

 and nt_symbol str =
   let nt1 = plus nt_symbol_char in
   let nt1 = pack nt1 list_to_string in
   let nt1 = pack nt1 (fun name -> ScmSymbol name) in
   let nt1 = diff nt1 nt_number in
   nt1 str

and nt_interpolated_string str = 
  let nt_poteach = word "~{" in
  let nt_space = star (char ' ') in
  let nt_poteach = caten nt_poteach nt_space in
  let nt_poteach = pack nt_poteach (fun (a,b) -> b) in
  let nt1 = caten nt_poteach nt_sexpr in
  let nt1 = pack nt1 (fun (a,b) -> b) in 
  let nt_soger = char '}' in
  let nt_soger = caten nt_space nt_soger in
  let nt_soger = pack nt_soger (fun (a,b) -> b) in
  let nt1 = caten nt1 nt_soger in 
  let nt1 = pack nt1 (fun (a,b) -> ScmPair(ScmSymbol ("format"), ScmPair(ScmString("~a"), ScmPair(a, ScmNil)))) in
  nt1 str


and nt_string_hex_char str =
  let nt1 = word_ci "\\x" in
  let nt2 = caten nt_char_hex nt_char_hex in
  let nt2 = pack nt2 (fun (a,b) -> (a*16 + b)) in
  let nt2 = pack nt2 (fun (a) -> char_of_int a) in
  let nt_out = caten nt1 nt2 in
  let nt_out = pack nt_out (fun (a,b) -> b) in
  nt_out str

and nt_hex_char str =
  let nt1 = char_ci 'x' in
  let nt2 = caten nt_char_hex nt_char_hex in
  let nt2 = pack nt2 (fun (a,b) -> (a*16 + b)) in
  let nt2 = pack nt2 (fun (a) -> char_of_int a) in
  let nt_out = caten nt1 nt2 in
  let nt_out = pack nt_out (fun (a,b) -> b) in
  nt_out str

and nt_string_char str =
  let nt_out = disj_list [nt_string_hex_char; nt_meta_char; nt_literal_char] in
  (pack (plus nt_out) (fun (ls) -> ScmString (list_to_string ls))) str


and nt_literal_char str =
  let nt1 = range ' ' '!' in 
  let nt2 = range '#' '[' in
  let nt3 = range ']' '}' in 
  let nt_out = disj_list [nt1 ; nt2 ; nt3] in
  nt_out str


and nt_meta_char str =
  let nt1 = word "\\\\" in
  let nt1 = pack nt1 (fun (_) -> char_of_int 92) in
  let nt2 = word "\\\"" in
  let nt2 = pack nt2 (fun (_) -> char_of_int 34) in
  let nt3 = word "\\t" in
  let nt3 = pack nt3 (fun (_) -> char_of_int 9) in
  let nt4 = word "\\f" in
  let nt4 = pack nt4 (fun (_) -> char_of_int 12) in
  let nt5 = word "\\n" in
  let nt5 = pack nt5 (fun (_) -> char_of_int 10) in
  let nt6 = word "\\r" in
  let nt6 = pack nt6 (fun (_) -> char_of_int 13) in
  let nt7 = word "~~" in
  let nt7 = pack nt7 (fun (_) -> char_of_int 126) in
  let nt_out = disj_list[nt1; nt2; nt3; nt4; nt5; nt6; nt7] in
  nt_out str


  and nt_string str =
   let f a b = ScmPair(a,b) in 
   let nt_1 = char '"' in
   let nt_out = (star (disj nt_string_char nt_interpolated_string)) in
   let nt_out = caten nt_out nt_1 in
   let nt_out = caten nt_1 nt_out in
   let nt_out = pack nt_out (fun (_, (list,_)) -> match list with [] -> ScmString("") | [a] -> a  |_-> let out = List.fold_right f list ScmNil in ScmPair(ScmSymbol "string-append", out)) in
   nt_out str

 and nt_vector str =
  let nt1 = word "#(" in
  let nt2 = caten nt_skip_star (char ')') in
  let nt2 = pack nt2 (fun _ -> ScmVector []) in
  let nt3 = plus nt_sexpr in
  let nt4 = char ')' in
  let nt3 = caten nt3 nt4 in
  let nt3 = pack nt3 (fun (sexprs, _) -> ScmVector sexprs) in
  let nt2 = disj nt2 nt3 in
  let nt1 = caten nt1 nt2 in
  let nt1 = pack nt1 (fun (_, sexpr) -> sexpr) in
  nt1 str


and nt_proper_list str =
   let nt_open = char '(' in
   let nt_close = char ')' in
   let nt_space = char ' ' in
   let nt1 = caten nt_open (star nt_space) in
   let nt1 = pack nt1 (fun (a,b) -> b) in
   let nt1 = caten nt1 (star nt_sexpr) in
   let nt1 = pack nt1 (fun (a,b) -> b) in
   let nt1 = caten nt1 (star nt_space) in
   let nt1 = pack nt1 (fun (a,b) -> a) in
   let nt1 = caten nt1 nt_close in
   let f a b = ScmPair (a,b) in
   let nt1 = pack nt1 (fun (a,b) -> List.fold_right f a ScmNil) in
   nt1 str



and nt_improper_list str =
  let f a b = ScmPair (a,b) in
  let nt_open = char '(' in
  let nt_close = char ')' in
  let nt_space = char ' ' in
  let nt1 = caten nt_open (star nt_space) in
  let nt1 = pack nt1 (fun (a,b) -> a) in (* returns parser for open and ignors spaces *)
  let nt1 = caten nt1 (plus nt_sexpr) in 
  let nt1 = pack nt1 (fun (a,b) -> b) in
  let nt_dot = char '.' in
  let nt1 = caten nt1 nt_dot in
  let nt1 = pack nt1 (fun (a,b) -> a) in
  let nt1 = caten nt1 nt_sexpr in
  let nt1 = pack nt1 (fun (a,b) -> List.fold_right f a b ) in
  let nt1 = caten nt1 (star nt_space) in
  let nt1 = pack nt1 (fun (a,b) -> a) in
  let nt1 = caten nt1 nt_close in
  let nt1 = pack nt1 (fun (a,b) -> a) in
  nt1 str


and nt_list str = 
  let nt_out = disj nt_proper_list nt_improper_list in
  nt_out str

and nt_quoted str = 
  let nt_out = char '\'' in
  let x = ScmSymbol("quote") in
  let nt_out = caten nt_out nt_sexpr in 
  let nt_out = pack nt_out(fun (a, b) ->ScmPair(x,ScmPair(b,ScmNil))) in 
  nt_out str

and nt_quasi_quoted str = 
  let nt_out = char '`' in
  let x = ScmSymbol("quasiquote") in
  let nt_out = caten nt_out nt_sexpr in 
  let nt_out = pack nt_out(fun (a, b) ->ScmPair(x,ScmPair(b,ScmNil))) in 
  nt_out str

and nt_unquoted str = 
  let nt_out = char ',' in
  let x = ScmSymbol("unquote") in
  let nt_out = caten nt_out nt_sexpr in 
  let nt_out = pack nt_out(fun (a, b) ->ScmPair(x,ScmPair(b,ScmNil))) in 
  nt_out str

and nt_unquote_and_splice str = 
  let nt_out = word ",@" in
  let x = ScmSymbol("unquote-splicing") in
  let nt_out = caten nt_out nt_sexpr in 
  let nt_out = pack nt_out(fun (a, b) ->ScmPair(x,ScmPair(b,ScmNil))) in 
  nt_out str

 and nt_quoted_forms str = 
  let nt_out = disj_list [nt_quoted; nt_quasi_quoted; nt_unquoted; nt_unquote_and_splice] in
  nt_out str

 and nt_sexpr str =
   let nt1 =
     disj_list [nt_number; nt_boolean; nt_char; nt_symbol;
                nt_string; nt_vector; nt_list; nt_quoted_forms] in
   let nt1 = make_skipped_star nt1 in
   nt1 str;;
 
 end;; (* end of struct Reader *)
 
 let rec string_of_sexpr = function
   | ScmVoid -> "#<void>"
   | ScmNil -> "()"
   | ScmBoolean(false) -> "#f"
   | ScmBoolean(true) -> "#t"
   | ScmChar('\n') -> "#\\newline"
   | ScmChar('\r') -> "#\\return"
   | ScmChar('\012') -> "#\\page"
   | ScmChar('\t') -> "#\\tab"
   | ScmChar(' ') -> "#\\space"
   | ScmChar('\000') -> "#\\nul" 
   | ScmChar(ch) ->
      if (ch < ' ')
      then let n = int_of_char ch in
           Printf.sprintf "#\\x%x" n
      else Printf.sprintf "#\\%c" ch
   | ScmString(str) ->
      Printf.sprintf "\"%s\""
        (String.concat ""
           (List.map
              (function
               | '\n' -> "\\n"
               | '\012' -> "\\f"
               | '\r' -> "\\r"
               | '\t' -> "\\t"
               | ch ->
                  if (ch < ' ')
                  then Printf.sprintf "\\x%x;" (int_of_char ch)
                  else Printf.sprintf "%c" ch)
              (string_to_list str)))
   | ScmSymbol(sym) -> sym
   | ScmNumber(ScmRational(0, _)) -> "0"
   | ScmNumber(ScmRational(num, 1)) -> Printf.sprintf "%d" num
   | ScmNumber(ScmRational(num, -1)) -> Printf.sprintf "%d" (- num)
   | ScmNumber(ScmRational(num, den)) -> Printf.sprintf "%d/%d" num den
   | ScmNumber(ScmReal(x)) -> Printf.sprintf "%f" x
   | ScmVector(sexprs) ->
      let strings = List.map string_of_sexpr sexprs in
      let inner_string = String.concat " " strings in
      Printf.sprintf "#(%s)" inner_string
   | ScmPair(ScmSymbol "quote",
             ScmPair(sexpr, ScmNil)) ->
      Printf.sprintf "'%s" (string_of_sexpr sexpr)
   | ScmPair(ScmSymbol "quasiquote",
             ScmPair(sexpr, ScmNil)) ->
      Printf.sprintf "`%s" (string_of_sexpr sexpr)
   | ScmPair(ScmSymbol "unquote",
             ScmPair(sexpr, ScmNil)) ->
      Printf.sprintf ",%s" (string_of_sexpr sexpr)
   | ScmPair(ScmSymbol "unquote-splicing",
             ScmPair(sexpr, ScmNil)) ->
      Printf.sprintf ",@%s" (string_of_sexpr sexpr)
   | ScmPair(car, cdr) ->
      string_of_sexpr' (string_of_sexpr car) cdr
 and string_of_sexpr' car_string = function
   | ScmNil -> Printf.sprintf "(%s)" car_string
   | ScmPair(cadr, cddr) ->
      let new_car_string =
        Printf.sprintf "%s %s" car_string (string_of_sexpr cadr) in
      string_of_sexpr' new_car_string cddr
   | cdr ->
      let cdr_string = (string_of_sexpr cdr) in
      Printf.sprintf "(%s . %s)" car_string cdr_string;;

