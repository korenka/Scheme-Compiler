(* semantic-analyser.ml
 * The semantic analysis phase of the compiler
 *
 * Programmer: Mayer Goldberg, 2021
 *)

#use "tag-parser.ml";;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;

type var' = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | ScmConst' of sexpr
  | ScmVar' of var'
  | ScmBox' of var'
  | ScmBoxGet' of var'
  | ScmBoxSet' of var' * expr'
  | ScmIf' of expr' * expr' * expr'
  | ScmSeq' of expr' list
  | ScmSet' of var' * expr'
  | ScmDef' of var' * expr'
  | ScmOr' of expr' list
  | ScmLambdaSimple' of string list * expr'
  | ScmLambdaOpt' of string list * string * expr'
  | ScmApplic' of expr' * (expr' list)
  | ScmApplicTP' of expr' * (expr' list);;


let var_eq v1 v2 =
match v1, v2 with
  | VarFree (name1), VarFree (name2) -> String.equal name1 name2
  | VarBound (name1, maj1, min1), VarBound (name2, maj2, min2) ->
    maj1 = maj2 && min1 = min2 && (String.equal name1 name2)
  | VarParam (name1, index1), VarParam (name2, index2) ->
       index1 = index2 && (String.equal name1 name2)
  | _ -> false

let list_eq eq l1 l2 = (List.length l1) = (List.length l2) && List.for_all2 eq l1 l2;;

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | ScmConst' (sexpr1), ScmConst' (sexpr2) -> sexpr_eq sexpr1 sexpr2
  | ScmVar' (var1), ScmVar' (var2) -> var_eq var1 var2
  | ScmIf' (testt1, dit1, dif1), ScmIf' (testt2, dit2, dif2) -> (expr'_eq testt1 testt2) &&
                                            (expr'_eq dit1 dit2) &&
                                              (expr'_eq dif1 dif2)
  | (ScmSeq' (exprs1), ScmSeq' (exprs2) | ScmOr' (exprs1), ScmOr' (exprs2)) ->
        List.for_all2 expr'_eq exprs1 exprs2
  | (ScmSet' (var1, val1), ScmSet' (var2, val2) | ScmDef' (var1, val1), ScmDef' (var2, val2)) ->
        (var_eq var1 var2) && (expr'_eq val1 val2)
  | ScmLambdaSimple' (vars1, body1), ScmLambdaSimple' (vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) && (expr'_eq body1 body2)
  | ScmLambdaOpt' (vars1, var1, body1), ScmLambdaOpt' (vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) && (expr'_eq body1 body2)
  | ScmApplic' (e1, args1), ScmApplic' (e2, args2) ->
     (expr'_eq e1 e2) && (List.for_all2 expr'_eq args1 args2)
  | ScmApplicTP' (e1, args1), ScmApplicTP' (e2, args2) ->
      (expr'_eq e1 e2) && (List.for_all2 expr'_eq args1 args2)
  | ScmBox' (v1), ScmBox' (v2) -> var_eq v1 v2
  | ScmBoxGet' (v1), ScmBoxGet' (v2) -> var_eq v1 v2
  | ScmBoxSet' (v1, e1), ScmBoxSet' (v2, e2) -> (var_eq v1 v2) && (expr'_eq e1 e2)
  | _ -> false;;

let unannotate_lexical_address = function
| (VarFree name | VarParam (name, _) | VarBound (name, _, _)) -> ScmVar name

let rec unanalyze expr' =
match expr' with
  | ScmConst' s -> ScmConst(s)
  | ScmVar' var -> unannotate_lexical_address var
  | ScmBox' var -> ScmApplic(ScmVar "box", [unannotate_lexical_address var])
  | ScmBoxGet' var -> unannotate_lexical_address var
  | ScmBoxSet' (var, expr') -> ScmSet (unannotate_lexical_address var, unanalyze expr')
  | ScmIf' (testt, dit, dif) -> ScmIf (unanalyze testt, unanalyze dit, unanalyze dif)
  | ScmSeq' expr's -> ScmSeq (List.map unanalyze expr's)
  | ScmSet' (var, expr') -> ScmSet (unannotate_lexical_address var, unanalyze expr')
  | ScmDef' (var, expr') -> ScmDef (unannotate_lexical_address var, unanalyze expr')
  | ScmOr' expr's -> ScmOr (List.map unanalyze expr's)
  | ScmLambdaSimple' (params, expr') ->
        ScmLambdaSimple (params, unanalyze expr')
  | ScmLambdaOpt'(params, param, expr') ->
        ScmLambdaOpt (params, param, unanalyze expr')
  | (ScmApplic' (expr', expr's) | ScmApplicTP' (expr', expr's)) ->
        ScmApplic (unanalyze expr', List.map unanalyze expr's);;

let string_of_expr' expr' =
    string_of_expr (unanalyze expr');;

module type SEMANTIC_ANALYSIS = sig
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
  val run_semantics : expr -> expr'
end;; (* end of module type SEMANTIC_ANALYSIS *)

module Semantic_Analysis : SEMANTIC_ANALYSIS = struct

  let rec lookup_in_rib name = function
    | [] -> None
    | name' :: rib ->
       if name = name'
       then Some(0)
       else (match (lookup_in_rib name rib) with
             | None -> None
             | Some min -> Some (min + 1));;

  let rec lookup_in_env name = function
    | [] -> None
    | rib :: env ->
       (match (lookup_in_rib name rib) with
        | None ->
           (match (lookup_in_env name env) with
            | None -> None
            | Some(maj, min) -> Some(maj + 1, min))
        | Some min -> Some(0, min));;

  let tag_lexical_address_for_var name params env = 
    match (lookup_in_rib name params) with
    | None ->
       (match (lookup_in_env name env) with
        | None -> VarFree name
        | Some(maj, min) -> VarBound(name, maj, min))
    | Some min -> VarParam(name, min);;

 (* run this first! *)
  let rec minor_finder curr_var vars pos = 
    if (curr_var = (List.hd vars)) then pos
    else minor_finder curr_var (List.tl vars) (pos+1);;


  let rec find_major_position curr_var vars major_num = 
    if (vars = []) then -1 else 
    if (List.mem curr_var (List.hd vars)) then major_num else
    find_major_position curr_var (List.tl vars) (major_num + 1)

    


  let rec create_bound_or_free_var curr_var vars =
    match find_major_position curr_var vars 0 with
   | -1 ->  VarFree(curr_var)
   | major -> VarBound(curr_var, major, (minor_finder curr_var (List.nth vars major) 0));;


    let rec check_var_address curr_var vars =
    if (List.length vars = 0) then (VarFree(curr_var)) else
    if (List.mem curr_var (List.hd vars)) then (VarParam(curr_var, (minor_finder curr_var (List.hd vars) 0) )) else
    create_bound_or_free_var curr_var (List.tl vars);;

  let rec annotate_lexical_addresses_rec pe vars = 
    match pe with 
    | ScmConst(const) ->  ScmConst'(const)
    | ScmVar(var) -> ScmVar'(check_var_address var vars)
    | ScmIf(test,dit,dif) -> ScmIf'(annotate_lexical_addresses_rec test vars, annotate_lexical_addresses_rec dit vars, annotate_lexical_addresses_rec dif vars)
    | ScmSeq(exprs) -> ScmSeq'(List.map (fun expr -> annotate_lexical_addresses_rec expr vars) exprs)
    | ScmSet(ScmVar(var),value) -> ScmSet'(check_var_address var vars , annotate_lexical_addresses_rec value vars)
    | ScmDef(ScmVar(var), value) -> ScmDef'(check_var_address var vars , annotate_lexical_addresses_rec value vars)
    | ScmOr(exprs) -> ScmOr'(List.map (fun expr -> annotate_lexical_addresses_rec expr vars) exprs)
    | ScmLambdaSimple(params,body) -> ScmLambdaSimple'(params, annotate_lexical_addresses_rec body (List.append [params] vars))
    | ScmLambdaOpt(params,opt,body) -> ScmLambdaOpt'(params, opt, annotate_lexical_addresses_rec body (List.append [List.append params [opt]] vars))
    | ScmApplic(rator,rands) -> ScmApplic'(annotate_lexical_addresses_rec rator vars, List.map (fun rand -> annotate_lexical_addresses_rec rand vars) rands )
    | _ -> raise X_this_should_not_happen;;

let annotate_2_lex pe vars = annotate_lexical_addresses_rec pe [];;

let annotate_lexical_addresses pe = annotate_2_lex pe [];;

let rec tails_call_rec pe tps = 
  match pe with
  | ScmLambdaSimple'(params,body) -> ScmLambdaSimple'(params,(tails_call_rec body true))
  | ScmLambdaOpt'(params,opt,body) -> ScmLambdaOpt'(params,opt,(tails_call_rec body true))
  | ScmApplic'(rator,rands) -> if (tps) then ScmApplicTP' ((tails_call_rec rator false), (List.map (fun exp -> tails_call_rec exp false) rands)) 
                                                  else ScmApplic' ((tails_call_rec rator false), (List.map (fun exp -> tails_call_rec exp false) rands))
  | ScmOr'(exprs) -> if (tps) then ScmOr'((check_last_in_tp exprs))
                                 else ScmOr'(List.map (fun exp -> tails_call_rec exp false) exprs)
  | ScmIf'(test,dit,dif) -> if (tps) then ScmIf'((tails_call_rec test false) ,(tails_call_rec dit true),(tails_call_rec dif true))
                                                     else ScmIf'((tails_call_rec test false) ,(tails_call_rec dit false),(tails_call_rec dif false))
  | ScmSeq'(exprs) -> if (tps) then ScmSeq'((check_last_in_tp exprs))
                                  else ScmSeq'(List.map (fun exp -> tails_call_rec exp false) exprs) 
  | ScmSet'(var,value) -> ScmSet'(var,(tails_call_rec value false))
  | ScmDef'(var, value) -> ScmDef'(var,(tails_call_rec value false)) 
  | _ -> pe 

  and check_last_in_tp lst =
    match lst with
    | car :: [] -> [tails_call_rec car true]
    | car :: cdr -> List.append [tails_call_rec car false] (check_last_in_tp cdr)
    | _ -> [];;

let annotate_2_tail_call pe vars = tails_call_rec pe vars;;

let annotate_tail_calls pe = annotate_2_tail_call pe false 

(*************** BOXING ***************)

let find_reads name enclosing_lambda expr = raise X_not_yet_implemented

let count = 
  ref 0;;

let get_next = 
  fun () ->
    count := (!count) + 1;
    !count;;


let rec read_or_write param exp lst exp_num = 
  match exp with 
  | ScmBoxSet'(var,val_) -> read_or_write param val_ lst exp_num 
  | ScmVar'(VarFree(var))-> if (var = param) then [0 ; exp_num]::lst else lst    
  | ScmVar'(VarParam(var, minor)) -> if (var = param) then [0 ; exp_num]::lst else lst
  | ScmVar'(VarBound(var, major, minor)) -> if (var = param) then [0 ; exp_num]::lst else lst
  | ScmSet'(VarFree(var), var_val) -> if (var = param) then read_or_write param var_val ([1 ; exp_num]::lst) exp_num   else read_or_write param var_val lst exp_num 
  | ScmSet'(VarParam(var, minor), var_val) -> if (var = param) then read_or_write param var_val ([1 ; exp_num]::lst) exp_num  else read_or_write param var_val lst exp_num 
  | ScmSet'(VarBound(var, major, minor), var_val) -> if (var = param) then read_or_write param var_val ([1 ; exp_num]::lst) exp_num  else read_or_write param var_val lst exp_num 
  | ScmIf'(test, dit, dif) -> List.append (List.append (read_or_write param test [] exp_num ) (read_or_write param dit [] exp_num )) (read_or_write param dif lst exp_num )
  | ScmOr'(exprs) -> (List.fold_left(fun  acc expr -> read_or_write param expr acc exp_num ) lst exprs)
  | ScmSeq'(exprs) -> (List.fold_left(fun  acc expr -> read_or_write param expr acc exp_num ) lst exprs)
  | ScmApplic'(rator, operands) -> (List.fold_left(fun  acc expr -> read_or_write param expr acc exp_num ) lst (rator::operands))
  | ScmApplicTP'(rator, operands) -> (List.fold_left(fun  acc expr -> read_or_write param expr acc exp_num ) lst (rator::operands))
  | ScmLambdaSimple'(params,body) -> if ((List.mem param params) ) then lst else read_or_write param body lst (get_next()) 
  | ScmLambdaOpt'(params,opt,body) -> if (List.mem param params || List.mem opt params) then lst else read_or_write param body lst (get_next()) 
  | _ -> lst;;
  

let rec make_reads_and_writes_rec var body list count = 
  match body with 
  | car :: [] -> read_or_write var car list (count) 
  | car :: cdr ->  List.append (read_or_write var car list (count) ) (make_reads_and_writes_rec var cdr list (get_next()))
  | _ -> []

let make_reads_and_writes var body list count = make_reads_and_writes_rec var body list count

let is_body_need_boxing lst = 
  List.fold_left(fun res first -> res ||
  List.fold_left(fun res2 second -> res2 ||
  ((not((List.nth first 1) = (List.nth second 1))) && (not((List.nth first 0) = (List.nth second 0)))))false lst) false lst;;
  
   
let to_box_or_not param body = 
  is_body_need_boxing (make_reads_and_writes param body [] (!count));; 

let rec box_it_rec param body = 
  match body with 
  | ScmBoxSet'(var, val_) -> ScmBoxSet'(var, box_it_rec param val_) 
  | ScmVar'(VarFree(var)) -> if (var = param) then ScmBoxGet'(VarFree(var)) else body
  | ScmVar'(VarParam(var, minor)) -> if (var = param) then ScmBoxGet'(VarParam(var, minor)) else body
  | ScmVar'(VarBound(var, major, minor)) -> if (var = param) then ScmBoxGet'(VarBound(var, major , minor)) else body
  | ScmIf'(test,dit,dif) -> ScmIf'(box_it_rec param test, box_it_rec param dit, box_it_rec param dif)
  | ScmSeq'(exprs) -> ScmSeq'(List.map (fun exp -> box_it_rec param exp) exprs) 
  | ScmSet'(VarFree(var), val_) -> if (var = param) then ScmBoxSet'(VarFree(var), box_it_rec param val_) else ScmSet'(VarFree(var), box_it_rec param val_)
  | ScmSet'(VarParam(var, minor), val_) -> if (var = param) then ScmBoxSet'(VarParam(var,minor), box_it_rec param val_) else  ScmSet'(VarParam(var, minor), box_it_rec param val_)
  | ScmSet'(VarBound(var, major, minor), val_) -> if (var = param) then ScmBoxSet'(VarBound(var, major, minor), box_it_rec param val_)  else  ScmSet'(VarBound(var, major, minor), box_it_rec param val_)
  | ScmDef'(var, val_) -> ScmDef'(var, box_it_rec param val_)
  | ScmOr'(exprs) -> ScmOr'(List.map (fun exp -> box_it_rec param exp) exprs) 
  | ScmApplic'(rator, operands) -> ScmApplic'(box_it_rec param rator, List.map (fun rand -> box_it_rec param rand) operands)
  | ScmApplicTP'(rator, operands) -> ScmApplicTP'(box_it_rec param rator, List.map (fun rand -> box_it_rec param rand) operands)
  | ScmLambdaSimple'(params, lambda_impl_body) -> if (List.mem param params) then body else ScmLambdaSimple'(params, box_it_rec param lambda_impl_body)   
  | ScmLambdaOpt'(params, opt, lambda_impl_body) -> if (List.mem param params || List.mem opt params) then body else ScmLambdaOpt'(params, opt, box_it_rec param lambda_impl_body)
  | _ -> body ;; 

let box_it param body  = box_it_rec param body 

let rec boxing var body minor =
  match body with 
  | ScmConst'(val_) -> body
  | ScmVar'(var_) -> body
  | ScmLambdaSimple'(params,lambda_impl_body) -> body
  | ScmLambdaOpt'(params,opt,lambda_impl_body) -> body
  | ScmSeq'(exprs) -> if (to_box_or_not var exprs) then ScmSeq'(ScmSet'(VarParam(var, minor), ScmBox'(VarParam(var,minor))):: (List.map (fun exp -> box_it var exp) exprs)) else body
  | _ -> if (to_box_or_not var [body]) then (ScmSeq'([ScmSet'(VarParam(var, minor), ScmBox'(VarParam(var,minor))); box_it var body])) else body;;




let rec box_set_rec expr = 
  match expr with 
  | ScmLambdaSimple'(params,body) -> ScmLambdaSimple'(params, List.fold_right(fun param body -> boxing param body (minor_finder param params 0)) params (box_set_rec body))
  | ScmLambdaOpt'(params,opt,body) -> ScmLambdaOpt'(params,opt, List.fold_right(fun param body -> boxing param body (minor_finder param (List.append params [opt]) 0)) (List.append params [opt]) (box_set_rec body))
  | ScmApplic'(rator,rands) ->  ScmApplic' ((box_set_rec rator ), (List.map (fun exp -> box_set_rec exp ) rands)) 
  | ScmApplicTP'(rator,rands) ->  ScmApplicTP' ((box_set_rec rator ), (List.map (fun exp -> box_set_rec exp ) rands)) 
  | ScmOr'(exprs) -> ScmOr'(List.map (fun exp -> box_set_rec exp) exprs)
  | ScmIf'(test,dit,dif) -> ScmIf'((box_set_rec test) ,(box_set_rec dit) ,(box_set_rec dif))
  | ScmSeq'(exprs) -> ScmSeq'(List.map (fun exp -> box_set_rec exp) exprs)
  | ScmSet'(var,value) -> ScmSet'(var,(box_set_rec value))
  | ScmDef'(var, value) -> ScmDef'(var,(box_set_rec value)) 
  | _ -> expr;;
  
let box_2_set expr = box_set_rec expr

let box_set expr = box_2_set expr;;






  let run_semantics expr =
    box_set
      (annotate_tail_calls
         (annotate_lexical_addresses expr))

end;; (* end of module Semantic_Analysis *)