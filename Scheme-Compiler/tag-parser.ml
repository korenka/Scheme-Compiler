#use "reader.ml";;

type expr =
  | ScmConst of sexpr
  | ScmVar of string
  | ScmIf of expr * expr * expr
  | ScmSeq of expr list
  | ScmSet of expr * expr
  | ScmDef of expr * expr
  | ScmOr of expr list
  | ScmLambdaSimple of string list * expr
  | ScmLambdaOpt of string list * string * expr
  | ScmApplic of expr * (expr list);;

exception X_syntax_error of sexpr * string;;
exception X_reserved_word of string;;
exception X_proper_list_error;;
exception X_not_implemented;;

let rec list_to_proper_list = function
| [] -> ScmNil
| hd::[] -> ScmPair (hd, ScmNil)
| hd::tl -> ScmPair (hd, list_to_proper_list tl);;

let rec list_to_improper_list = function
| [] -> raise X_proper_list_error
| hd::[] -> hd
| hd::tl -> ScmPair (hd, list_to_improper_list tl);;

let rec scm_append scm_list sexpr =
match scm_list with
| ScmNil -> sexpr
| ScmPair (car, cdr) -> ScmPair (car, scm_append cdr sexpr)
| _ -> raise (X_syntax_error (scm_list, "Append expects a proper list"))

let rec scm_map f sexpr =
match sexpr with
| ScmNil -> ScmNil
| ScmPair (car, cdr) -> ScmPair (f car, scm_map f cdr)
| _ -> raise (X_syntax_error (sexpr, "Map expects a list"));;

let rec scm_zip f sexpr1 sexpr2 =
match sexpr1, sexpr2 with
| ScmNil, ScmNil -> ScmNil
| ScmPair (car1, cdr1), ScmPair (car2, cdr2) -> ScmPair (f car1 car2, scm_zip f cdr1 cdr2)
| _, _ ->
    let sepxrs = list_to_proper_list [ScmSymbol "sexpr1:"; sexpr1; ScmSymbol "sexpr2:"; sexpr2] in
    raise (X_syntax_error (sepxrs, "Zip expects 2 lists of equal length"));;

let rec scm_list_to_list = function
| ScmPair (hd, tl) -> hd::(scm_list_to_list tl)
| ScmNil -> []
| sexpr -> raise (X_syntax_error (sexpr, "Expected proper list"));;

let rec scm_is_list = function
| ScmPair (hd, tl) -> scm_is_list tl
| ScmNil -> true
| _ -> false

let rec scm_list_length = function
| ScmPair (hd, tl) -> 1 + (scm_list_length tl)
| ScmNil -> 0
| sexpr -> raise (X_syntax_error (sexpr, "Expected proper list"));;

let rec untag expr =
let untag_vars vars = List.map (fun s -> ScmSymbol s) vars in
let untag_tagged_list tag exprs = list_to_proper_list (ScmSymbol tag::(List.map untag exprs)) in

let untag_lambda_opt vars var body =
let vars = match vars with
| [] -> ScmSymbol var
| _ -> list_to_improper_list (untag_vars (vars@[var])) in
list_to_proper_list ([ScmSymbol "lambda"; vars]@body) in

match expr with
| (ScmConst (ScmSymbol(_) as sexpr)
    | ScmConst (ScmNil as sexpr)
    | ScmConst (ScmPair (_, _) as sexpr)) -> list_to_proper_list [ScmSymbol "quote"; sexpr]
| ScmConst s -> s
| ScmVar (name) -> ScmSymbol(name)
| ScmIf (test, dit, ScmConst (ScmVoid)) -> untag_tagged_list "if" [test; dit]
| ScmIf (test, dit, dif) -> untag_tagged_list "if" [test; dit; dif]
| ScmSeq(exprs) -> untag_tagged_list "begin" exprs
| ScmSet (var, value) -> untag_tagged_list "set!" [var; value]
| ScmDef (var, value) -> untag_tagged_list "define" [var; value]
| ScmOr (exprs) -> untag_tagged_list "or" exprs
| ScmLambdaSimple (vars, ScmSeq(body)) ->
    let vars = list_to_proper_list (untag_vars vars) in
    let body = List.map untag body in
    list_to_proper_list ([ScmSymbol "lambda"; vars]@body)
| ScmLambdaSimple (vars, body) ->
    let vars = list_to_proper_list (untag_vars vars) in
    list_to_proper_list ([ScmSymbol "lambda"; vars; untag body])
| ScmLambdaOpt (vars, var, ScmSeq(body)) ->
    let body = List.map untag body in
    untag_lambda_opt vars var body
| ScmLambdaOpt (vars, var, body) ->
    let body = [untag body] in
    untag_lambda_opt vars var body
| ScmApplic(procedure, args) -> list_to_proper_list (List.map untag (procedure::args));;


let rec string_of_expr expr =
string_of_sexpr (untag expr)

let scm_number_eq n1 n2 =
match n1, n2 with
| ScmRational(numerator1, denominator1), ScmRational(numerator2, denominator2) ->
        numerator1 = numerator2 && denominator1 = denominator2
| ScmReal(real1), ScmReal(real2) -> abs_float(real1 -. real2) < 0.001
| _, _ -> false

let rec sexpr_eq s1 s2 =
match s1, s2 with
| (ScmVoid, ScmVoid) | (ScmNil, ScmNil)  -> true
| ScmBoolean(bool1), ScmBoolean(bool2) -> bool1 = bool2
| ScmChar(char1), ScmChar(char2) -> char1 = char2
| ScmString(string1), ScmString(string2) -> String.equal string1 string2
| ScmSymbol(symbol1), ScmSymbol(symbol2) -> String.equal symbol1 symbol2
| ScmNumber(number1), ScmNumber(number2) -> scm_number_eq number1 number2
| ScmVector(sexprs1), ScmVector(sexprs2) -> List.for_all2 sexpr_eq sexprs1 sexprs2
| ScmPair(car1, cdr1), ScmPair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
| _, _ -> false

let rec expr_eq e1 e2 =
  match e1, e2 with
  | ScmConst (sexpr1), ScmConst (sexpr2) -> sexpr_eq sexpr1 sexpr2
  | ScmVar (var1), ScmVar (var2) -> String.equal var1 var2
  | ScmIf (test1, dit1, dif1), ScmIf (test2, dit2, dif2) -> (expr_eq test1 test2) &&
                                            (expr_eq dit1 dit2) &&
                                              (expr_eq dif1 dif2)
  | (ScmSeq(exprs1), ScmSeq(exprs2) | ScmOr (exprs1), ScmOr (exprs2)) ->
        List.for_all2 expr_eq exprs1 exprs2
  | (ScmSet (var1, val1), ScmSet (var2, val2) | ScmDef (var1, val1), ScmDef (var2, val2)) ->
        (expr_eq var1 var2) && (expr_eq val1 val2)
  | ScmLambdaSimple (vars1, body1), ScmLambdaSimple (vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) && (expr_eq body1 body2)
  | ScmLambdaOpt (vars1, var1, body1), ScmLambdaOpt (vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) && (expr_eq body1 body2)
  | ScmApplic (e1, args1), ScmApplic (e2, args2) ->
     (expr_eq e1 e2) && (List.for_all2 expr_eq args1 args2)
  | _ -> false;;

module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
end;; 

let list_contains ls word = 
    let predicat str = str = word in
    ormap predicat ls;;

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;


 
let rec bindings a fa ribs=
    match ribs with
    | ScmNil -> ScmPair(ScmPair (ScmSymbol("value"), ScmPair (a, ScmNil)), ScmPair (ScmPair (ScmSymbol("f"), ScmPair(ScmPair (ScmSymbol("lambda"), ScmPair (ScmNil,ScmPair(fa,ScmNil))), ScmNil)), ScmNil))
    | _ -> ScmPair(ScmPair(ScmSymbol "value", ScmPair(a, ScmNil)), ScmPair(ScmPair(ScmSymbol "f", ScmPair(ScmPair(ScmSymbol "lambda", ScmPair(ScmNil, ScmPair(fa, ScmNil))),ScmNil)), ScmPair(ScmPair(ScmSymbol "rest", ScmPair(ScmPair(ScmSymbol "lambda", ScmPair(ScmNil, ScmPair (ScmPair (ScmSymbol("cond"),ribs), ScmNil))),ScmNil)), ScmNil)));;


  let bodies ribs= 
    match ribs with
    | ScmNil -> ScmPair(ScmSymbol ("if"), ScmPair(ScmSymbol "value", ScmPair(ScmPair(ScmPair(ScmSymbol "f", ScmNil), ScmPair(ScmSymbol"value", ScmNil)), ScmNil)))
    | _ -> ScmPair(ScmSymbol "if", ScmPair(ScmSymbol "value", ScmPair(ScmPair(ScmPair(ScmSymbol "f", ScmNil), ScmPair(ScmSymbol"value", ScmNil)), ScmPair(ScmPair(ScmSymbol "rest", ScmNil),ScmNil))));;

   

  let rec parse_cond rib ribs = 
    match rib with 
    | ScmNil -> ScmPair(ScmSymbol "begin", ScmNil)
    | ScmPair(ScmSymbol "else", exps) -> ScmPair(ScmSymbol "begin", exps)
    | ScmPair (a, ScmPair (ScmSymbol "=>", ScmPair (fa, ScmNil))) -> ScmPair(ScmSymbol "let", ScmPair(bindings a fa ribs, ScmPair(bodies ribs,ScmNil)))
    | ScmPair(test, then_) ->  ScmPair(ScmSymbol ("if"), ScmPair(test, ScmPair(ScmPair(ScmSymbol "begin", then_), ScmPair(ScmPair(ScmSymbol "cond", ribs),ScmNil))))


let rec tag_parse_expression sexpr =
match sexpr with 
(*consts *)
| ScmBoolean b -> ScmConst (ScmBoolean b)
| ScmChar x -> ScmConst (ScmChar x)
| ScmString x -> ScmConst (ScmString x)
| ScmNumber x -> ScmConst (ScmNumber x)
| (ScmPair(ScmSymbol("quote"), ScmPair(x, ScmNil))) -> ScmConst(x)
(*quasi *)
| ScmPair (ScmSymbol "quasiquote", ScmPair(sexpr, ScmNil)) -> (tag_parse_expression (create_quasi_quote sexpr))
(*if *)
| (ScmPair(ScmSymbol "if", ScmPair(test, ScmPair(dit,ScmPair (dif,ScmNil)))))-> ScmIf(tag_parse_expression test, tag_parse_expression dit, tag_parse_expression dif)
| (ScmPair(ScmSymbol "if", ScmPair(test, ScmPair(dit, ScmNil)))) -> ScmIf(tag_parse_expression test, tag_parse_expression dit, tag_parse_expression ScmVoid)
(*or *)
| (ScmPair(ScmSymbol "or", ScmPair(ScmString x, ScmNil))) -> ScmConst(ScmString(x))
| (ScmPair(ScmSymbol "or", ScmNil)) -> ScmConst(ScmBoolean false)
| (ScmPair(ScmSymbol "or", ScmPair(first, second))) -> ScmOr((tag_parse_expression first) :: (List.map(tag_parse_expression)) (scm_list_to_list second))
(*seq *)
| (ScmPair(ScmSymbol "begin", exprs)) -> ScmSeq (list_exps exprs)
(*and *)
| ScmPair( ScmSymbol "and", exps) -> (match exps with
    | ScmNil -> ScmConst (ScmBoolean true)
    | ScmPair(exp, ScmNil) -> tag_parse_expression exp
    | ScmPair(car, cdr) -> ScmIf ((tag_parse_expression car),  (tag_parse_expression (ScmPair(ScmSymbol "and", cdr))), (ScmConst (ScmBoolean false)))
    | _ -> raise (X_syntax_error (sexpr, "create_and_exp: Sexpr structure not recognized")))
(*let *)
| ScmPair( ScmSymbol "let", ScmPair(args, body)) -> create_let_exp args body sexpr
| ScmPair( ScmSymbol "let*", ScmPair(bindings, bodies)) ->   (match bindings, bodies with
                                        | ScmNil, bodies -> tag_parse_expression (ScmPair( ScmSymbol "let", ScmPair(ScmNil, bodies)))
                                        | ScmPair(ScmPair(ScmSymbol var_name, ScmPair(value, ScmNil)), ScmNil), bodies -> 
                                                                      (tag_parse_expression (ScmPair( ScmSymbol "let", ScmPair(bindings, bodies))))
                                        | ScmPair(ScmPair(ScmSymbol var_name, ScmPair(value, ScmNil)), rest_args), bodies -> (
                                                    let let_star = ScmPair(ScmSymbol "let*", ScmPair(rest_args, bodies)) in
                                                                      (tag_parse_expression (ScmPair( ScmSymbol "let", ScmPair(ScmPair(ScmPair(ScmSymbol var_name, ScmPair(value, ScmNil)), ScmNil), ScmPair(let_star, ScmNil) ))) ) ) )
| ScmPair(ScmSymbol("let*"), ScmPair(ScmNil, exprs)) -> tag_parse_expression(ScmPair(ScmSymbol("let"), ScmPair(ScmNil, exprs)))
| ScmPair(ScmSymbol("let*"), ScmPair(ScmPair(pair, ScmNil), exprs)) -> tag_parse_expression(ScmPair(ScmSymbol("let"), ScmPair(ScmPair(pair,ScmNil), exprs)))
| ScmPair(ScmSymbol("let*"), ScmPair(ScmPair(first_pair, rest_pairs), exprs)) -> tag_parse_expression( ScmPair(ScmSymbol("let"), ScmPair(ScmPair(first_pair, ScmNil),ScmPair(ScmPair(ScmSymbol("let*"), ScmPair(rest_pairs, exprs)),ScmNil))))
| ScmPair(ScmSymbol("letrec"), ScmPair(bindings,bodies)) -> tag_parse_expression (parse_letrec bindings bodies)
(*lambda*)
| (ScmPair(ScmSymbol "lambda", ScmPair(ScmSymbol(a), body))) -> ScmLambdaOpt([], a ,sequence_parse body)
| ScmPair (ScmSymbol "lambda", ScmPair(args, exprs)) -> create_lambda_exp args exprs
(*def *)
| (ScmPair (ScmSymbol "define", ScmPair (var, ScmPair (vals, ScmNil)))) -> (match var with
          | ScmSymbol x -> if (List.mem x reserved_word_list) then raise (X_syntax_error (sexpr, "Expected variable on LHS of define")) else ScmDef (ScmVar x, (tag_parse_expression vals)) (*SimpleDefine*)
          | ScmPair (ScmSymbol y, args) -> ScmDef (ScmVar y, (tag_parse_expression (ScmPair (ScmSymbol "lambda", ScmPair(args, ScmPair (vals, ScmNil))))))) (*MIT style define*)
(*set!*)
| (ScmPair (ScmSymbol "set!", ScmPair (x, ScmPair (value, ScmNil)))) -> set_s x value sexpr
(*cond *)
 | ScmPair(ScmSymbol("cond"),ScmNil) -> ScmConst(ScmVoid)
| ScmPair(ScmSymbol("cond"),ScmPair(rib, ribs)) -> tag_parse_expression (parse_cond rib ribs)
(*applic *)
| (ScmPair (s, args)) -> ScmApplic ((tag_parse_expression s), (list_exps args))
| (ScmSymbol x) -> if list_contains reserved_word_list x then raise (X_reserved_word x) else  ScmVar (x) 
| (s) -> ScmConst(s)
| _ -> raise (X_syntax_error (sexpr, "Sexpr structure not recognized"))


and create_let_exp args body sexpr =
  let var_names = handle_args_in_let args in
  let var_values = handle_values_in_let args in
  let body = create_sequence body in
  let lambda = ScmLambdaSimple(var_names, body) in
  let applic_exp = ScmApplic(lambda, var_values) in
  applic_exp
  
and handle_args_in_let args = 
  match args with
    | ScmNil -> []
    | ScmPair( ScmPair(ScmSymbol var_name, ScmPair(sexp, ScmNil)), rest) -> ( let tail = (handle_args_in_let rest) in
                if (List.mem var_name tail) then raise (X_syntax_error(args, "var name duplicated")) else var_name::tail )
    | _ -> raise (X_syntax_error (args, "handle_args_in_let: Sexpr structure not recognized"))

and handle_values_in_let args = 
  match args with
    | ScmNil -> []
    | ScmPair( ScmPair(ScmSymbol var_name, ScmPair(sexp, ScmNil)), rest) -> (tag_parse_expression sexp)::(handle_values_in_let rest)
    | _ -> raise (X_syntax_error (args, "handle_values_in_let: Sexpr structure not recognized"))


and create_bindings_vals binding =
 match binding with
    | ScmNil -> []
    | ScmPair( ScmPair(ScmSymbol var_name, ScmPair(sexp, ScmNil)), rest) -> (tag_parse_expression sexp)::(create_bindings_vals rest)
    | _ -> raise (X_syntax_error (binding, "handle_values_in_let: Sexpr structure not recognized"))

and create_bindings_vars binding = 
match binding with
  | ScmNil -> []
  | ScmPair( ScmPair(ScmSymbol var_name, ScmPair(sexp, ScmNil)), rest) -> ( let tail = (create_bindings_vars rest) in
              if (List.mem var_name tail) then raise (X_syntax_error(binding, "var name duplicated")) else var_name::tail )
  | _ -> raise (X_syntax_error (binding, "create_bindings_vars: Sexpr structure not recognized"))

and parse_let args body sexpr =
  let var_names = create_bindings_vars args in
  let var_values = create_bindings_vals args in
  let body = create_sequence body in
  let lambda = ScmLambdaSimple(var_names, body) in
  let applic_exp = ScmApplic(lambda, var_values) in
  applic_exp

and set_s x value sexpr = 
match x with
| ScmSymbol v -> ScmSet(ScmVar v, (tag_parse_expression value))
| _ -> raise (X_syntax_error (sexpr, "Expected variable on LHS of set!"))

and sexps_to_exps_list sexps = 
match sexps with
  | ScmPair (hd, tl) -> (tag_parse_expression hd)::(sexps_to_exps_list tl)
  | ScmNil -> []
  | _ -> raise (X_syntax_error (sexps, "Syntax error"))

and get_last_arg_from_improper_args args =
  match args with
    | ScmSymbol sym -> sym
    | ScmPair(ScmSymbol car, ScmSymbol cdr) -> cdr
    | ScmPair(ScmSymbol car, cdr) -> get_last_arg_from_improper_args cdr
    | _ -> raise (X_syntax_error (args, "Syntax error"))

and improper_list_args args =
  match args with
    | ScmSymbol sym -> []
    | ScmPair(ScmSymbol car, ScmSymbol cdr) -> [car]
    | ScmPair(ScmSymbol car, cdr) -> car::improper_list_args cdr
    | _ -> raise (X_syntax_error (args, "Syntax error"))

and get_string_list list =
  match list with
   | ScmNil -> []
   | ScmPair(ScmSymbol car, cdr) -> car::get_string_list cdr
   | _ -> raise (X_syntax_error (list, "Syntax error"))

and get_lambda_type args = 
  match args with
    | ScmNil -> "lambda_simple"
    | ScmSymbol sym -> "lambda_opt"
    | ScmPair (car, cdr) -> get_lambda_type cdr
    | _ -> raise (X_syntax_error (args, "Syntax error"))
    
and create_lambda_exp args exprs =
  let lambda_type = get_lambda_type args in
  match lambda_type with
    | "lambda_simple" -> ScmLambdaSimple(get_string_list args, create_sequence exprs)
    | "lambda_opt" -> ScmLambdaOpt(improper_list_args args, get_last_arg_from_improper_args args, create_sequence exprs)
    | _ -> raise (X_syntax_error (args, "Syntax error"))

and create_quasi_quote sexpr =
match sexpr with
|ScmPair (ScmSymbol "unquote", ScmPair (sexpr, ScmNil)) -> sexpr
|ScmVector vector -> ScmPair (ScmSymbol "list->vector", ScmPair (create_quasi_quote (create_vector_quasiquote vector), ScmNil ))
|ScmPair (ScmPair (ScmSymbol "unquote-splicing", ScmPair (sexpr, ScmNil)), b) -> ScmPair (ScmSymbol "append", ScmPair (sexpr, ScmPair (create_quasi_quote b, ScmNil)))
|ScmPair (a,b) -> ScmPair (ScmSymbol "cons", ScmPair(create_quasi_quote a, ScmPair(create_quasi_quote b, ScmNil)))
|ScmPair (ScmSymbol "unquote-splicing", sexpr) -> ScmPair (ScmSymbol "quote", ScmPair (ScmPair (ScmSymbol "unquote-splicing", sexpr), ScmNil))
|ScmSymbol symbol -> ScmPair (ScmSymbol "quote", ScmPair (ScmSymbol symbol, ScmNil))
|ScmNil -> ScmPair (ScmSymbol "quote", ScmPair (ScmNil, ScmNil))
|_ -> sexpr

and create_sequence sexprs =
  match sexprs with
    | ScmNil -> ScmConst ScmVoid
    | ScmPair (car, ScmNil) -> tag_parse_expression car
    | _ -> ScmSeq (sexps_to_exps_list sexprs)

and create_vector_quasiquote vec =
match vec with
|[] -> ScmNil
|hd::tl -> ScmPair(hd, create_vector_quasiquote tl)

and sexpr_expr_ls pair =
match pair with
| ScmNil -> []
| ScmPair(x, y) -> tag_parse_expression x :: sexpr_expr_ls y
| _ -> [tag_parse_expression pair]

and sequence_parse sexpr =
match sexpr with
| ScmPair(x, ScmNil) -> tag_parse_expression x
| ScmPair(x, y) -> ScmSeq(sexpr_expr_ls sexpr)

and list_exps spair =
match spair with
| ScmNil -> []
| ScmPair (first, ScmNil) -> (tag_parse_expression first)::[]
| ScmPair (car, cdr) -> (tag_parse_expression car)::(list_exps cdr)


and parse_letrec_bindings bindings = 
  match bindings with 
  | ScmPair(ScmPair(func_name,val_), ScmNil) -> ScmPair(ScmPair(func_name,ScmPair(ScmPair(ScmSymbol "quote", ScmPair(ScmSymbol "whatever",ScmNil)),ScmNil)),ScmNil)
  | ScmPair(ScmPair(func_name,val_), next_var) -> ScmPair(ScmPair(func_name,ScmPair(ScmPair(ScmSymbol "quote", ScmPair(ScmSymbol "whatever",ScmNil)),ScmNil)),parse_letrec_bindings next_var)


and parse_letrec_body bindings bodies= 
  match bindings with
  | ScmNil -> ScmPair(ScmSymbol("let"),ScmPair(ScmNil,ScmPair(bodies,ScmNil)))
  | ScmPair(ScmPair(func_name,val_),ScmNil) -> ScmPair(ScmPair(ScmSymbol("set!"),ScmPair(func_name,val_)),ScmPair(ScmPair(ScmSymbol("let"),ScmPair(ScmNil,bodies)),ScmNil))
  | ScmPair(ScmPair(func_name,val_),other_funcs) -> ScmPair(ScmPair(ScmSymbol("set!"),ScmPair(func_name,val_)),parse_letrec_body other_funcs bodies)


and parse_letrec bindings bodies = 
  ScmPair(ScmSymbol "let", ScmPair(parse_letrec_bindings bindings,parse_letrec_body bindings bodies))

end;;