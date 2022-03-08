#use "semantic-analyser.ml";;

(* This module is here for you convenience only!
   You are not required to use it.
   you are allowed to change it. *)
module type CODE_GEN = sig
  (* This signature assumes the structure of the constants table is
     a list of key-value pairs:
     - The keys are constant values (Sexpr(x) or Void)
     - The values are pairs of:
       * the offset from the base const_table address in bytes; and
       * a string containing the byte representation (or a sequence of nasm macros)
         of the constant value
     For example: [(Sexpr(Nil), (1, "T_NIL"))]
   *)
  val make_consts_tbl : expr' list -> (sexpr * (int * string)) list

  (* This signature assumes the structure of the fvars table is
     a list of key-value pairs:
     - The keys are the fvar names as strings
     - The values are the offsets from the base fvars_table address in bytes
     For example: [("boolean?", 0)]
   *)  
  val make_fvars_tbl : expr' list -> (string * int) list

  (* If you change the types of the constants and fvars tables, you will have to update
     this signature to match: The car argument is the constants table type, the second 
     argument is the fvars table type, and the third is an expr' that has been annotated 
     by the semantic analyser.
   *)
  val generate : (sexpr * (int * string)) list -> (string * int) list -> expr' -> string
end;;

module Code_Gen : CODE_GEN = struct


let rec gather_constst expr lst =

    match expr with
    | ScmConst'(ex) ->  lst @ [expr]
    | ScmBoxSet'(var,val_) -> gather_constst val_ lst
    | ScmIf'(test, dit , dif) -> ( (gather_constst test lst ) @ ( (gather_constst dit lst) @ (gather_constst dif lst)) )
    | ScmSeq'(exprs) -> lst @ (List.concat (List.map (fun expr -> gather_constst expr lst) exprs)) 
    | ScmSet'(var, val_) -> gather_constst val_ lst
    | ScmDef'(var,val_) -> gather_constst val_ lst
    | ScmOr'(exprs) -> lst @ (List.concat (List.map (fun expr -> gather_constst expr lst) exprs)) 
    | ScmLambdaSimple'(params,body) -> gather_constst body lst
    | ScmLambdaOpt'(params,opt,body) -> gather_constst body lst
    | ScmApplic'(rator,rands) -> List.fold_left (fun acc expr -> gather_constst expr acc) lst (rator::rands)
    | ScmApplicTP'(rator,rands) -> List.fold_left (fun acc expr -> gather_constst expr acc) lst (rator::rands)
    | _ -> lst


    let rec check_all_asts_in_exprs exprs = 
    match exprs with
    | car :: [] -> [gather_constst car []]
    | car :: cdr -> [gather_constst car []] @ (check_all_asts_in_exprs cdr)
    | _ -> raise X_this_should_not_happen;;


    let rec has_const_inside lst e =
      match lst with
      | car :: [] -> if (car = e) then true else false
      | car :: cdr -> if (car = e) then true else has_const_inside cdr e
      | [] -> false;;


    let rec dup_remover clean_lst lst = 
      match lst with 
      | car :: [] -> if (has_const_inside clean_lst car) then clean_lst else clean_lst @ [car]
      | car :: cdr -> if (has_const_inside clean_lst car) then dup_remover clean_lst cdr else dup_remover (clean_lst @ [car]) cdr
      | _ -> raise X_this_should_not_happen;;



    let rec pair_expander exp = 
      match exp with 
      | ScmPair(car, ScmNil) -> ([ScmConst'(exp)] @ ((pair_expander car) @ [ScmConst'(ScmNil)]))
      | ScmPair(car, cdr) -> ([ScmConst'(exp)] @ ((pair_expander car) @ (pair_expander cdr)))
      | other -> [ScmConst'(other)]



        let rec set_expander expanded_lst lst =
      match lst with 
      | ScmConst'(ScmPair(car,cdr)) :: [] -> (expanded_lst @ (List.rev (pair_expander (ScmPair(car,cdr)))) )
      | ScmConst'(sexpr) :: [] -> (expanded_lst @ [ScmConst'(sexpr)])
      | ScmConst'(ScmPair(car,rest)) :: cdr -> set_expander (expanded_lst @ (List.rev (pair_expander (ScmPair(car,rest)) )) ) cdr
      | ScmConst'(sexpr) :: cdr -> set_expander (expanded_lst @ [ScmConst'(sexpr)]) cdr 
      | _ -> raise X_this_should_not_happen;;


      let coun = 
        ref 0;;

      
      let get_next = 
        fun (i) ->
        coun := (!coun) + i;
        !coun - i;;



      let (#%) = Printf.sprintf;;



      let rec check_if_has_symbol_like_string lst symbol = 
        match lst with
        | ScmConst'(ScmString(string_val)) :: [] -> if (string_val = symbol) then true else false
        | ScmConst'(ScmString(string_val)) :: cdr -> if (string_val = symbol) then true else check_if_has_symbol_like_string cdr symbol
        | car_not_string :: [] -> false
        | car_not_string :: cdr -> check_if_has_symbol_like_string cdr symbol
        | _ -> raise X_this_should_not_happen;;

    

        let rec get_car_and_cdr_of_offset e current_table =
         match current_table with
         | (ScmVoid,(table_offset,byte)) :: cdr -> get_car_and_cdr_of_offset e cdr
         | (expr,(table_offset,byte)) :: [] -> if (sexpr_eq e expr) then table_offset else -1
         | (expr,(table_offset,byte)) :: cdr -> if (sexpr_eq e expr) then table_offset else get_car_and_cdr_of_offset e cdr
         | _ -> raise X_this_should_not_happen;;



        let rec set_table_entry_of_const const whole_input_set current_table = 
          match const with 
        | ScmConst'(ScmVoid) -> [(ScmVoid,(get_next 1,"db T_VOID"))]
        | ScmConst'(ScmNil) -> [(ScmNil,(get_next 1,"db T_NIL"))]
        | ScmConst'(ScmBoolean(true)) -> [(ScmBoolean(true),(get_next 2,"db T_BOOL, 1"))] 
        | ScmConst'(ScmBoolean(false)) ->  [(ScmBoolean(false),(get_next 2,"db T_BOOL, 0"))] 
        | ScmConst'(ScmNumber(ScmRational(num,den))) -> [(ScmNumber(ScmRational(num,den)),(get_next 17,("MAKE_LITERAL_RATIONAL(%d,%d)" #% num den)))]
        | ScmConst'(ScmNumber(ScmReal(float_num))) -> [(ScmNumber(ScmReal(float_num)),(get_next 9,("MAKE_LITERAL_REAL(%f)" #% float_num) ))]
        | ScmConst'(ScmChar(char_val)) -> [(ScmChar(char_val),(get_next 2, ("MAKE_LITERAL_CHAR("^(string_of_int (int_of_char char_val))^")")))]

        | ScmConst'(ScmString(string_val)) -> [(ScmString(string_val),(get_next (9 + (String.length string_val)), ("MAKE_LITERAL_STRING \""^(String.escaped string_val)^"\"")))]
        | ScmConst'(ScmSymbol(symbol)) -> if (check_if_has_symbol_like_string whole_input_set symbol) then [(ScmSymbol(symbol),(get_next 9, ("MAKE_LITERAL_SYMBOL(const_tbl+%d)" #% (get_car_and_cdr_of_offset (ScmString(symbol)) current_table) )))]
                                              else (List.rev 
                                              ([(ScmSymbol(symbol),(get_next 9, ("MAKE_LITERAL_SYMBOL(const_tbl+%d)" #% ((get_next 0) - 9 - (String.length symbol)))))] @ [(ScmString(symbol),(get_next (9 + (String.length symbol)), ("MAKE_LITERAL_STRING \""^(String.escaped symbol)^"\"")))]))
        | ScmConst'(ScmPair(car,cdr)) ->  [(ScmPair(car,cdr),(get_next 17,("MAKE_LITERAL_PAIR(const_tbl+%d,const_tbl+%d)" #% (get_car_and_cdr_of_offset car current_table) (get_car_and_cdr_of_offset cdr current_table) )))]
        | _ -> raise X_this_should_not_happen;;


      let rec set_table_entry_of_set_of_consts whole_input_set = 
      (List.fold_left (fun acc const -> List.append acc (set_table_entry_of_const const whole_input_set acc)) [] whole_input_set);;        

  let check_if_good lst = lst;;

  let make_consts_tbl asts = 
    let list_of_consts = check_all_asts_in_exprs asts in 
    let list_of_consts = List.flatten list_of_consts in
    let list_of_consts = check_if_good list_of_consts in
    let list_of_consts = [ScmConst'(ScmVoid); ScmConst'(ScmNil); ScmConst'(ScmBoolean(false)) ; ScmConst'(ScmBoolean(true))] @ list_of_consts in
    let set_of_consts = dup_remover [] list_of_consts in 
    let set_of_consts = check_if_good set_of_consts in
    let set_of_consts_expanded = set_expander [] set_of_consts in 
    let set_of_consts_expanded = dup_remover [] set_of_consts_expanded in
    let consts_table = set_table_entry_of_set_of_consts set_of_consts_expanded in 
    let consts_table = check_if_good consts_table in
    consts_table;;

(* --------------------- MAKE FVARS TBL --------------------- *)

  let rec collect_fvars expr lst = 

    match expr with
    | ScmVar'(VarFree(var)) -> var :: lst
    | ScmBox'(VarFree(var)) -> var :: lst
    | ScmBoxGet'(VarFree(var)) -> var :: lst
    | ScmBoxSet'(VarFree(var),val_) ->   var ::  collect_fvars val_ lst
    | ScmBoxSet'(var,val_) -> collect_fvars val_ lst
    | ScmIf'(test, dit , dif) -> ((collect_fvars test lst ) @ ((collect_fvars dit lst) @ (collect_fvars dif lst)) )
    | ScmSeq'(exprs) -> List.fold_left (fun acc expr -> collect_fvars expr acc) lst exprs
    | ScmSet'(VarFree(var),val_ ) ->  var ::  collect_fvars val_ lst
    | ScmSet'(var, val_) -> collect_fvars val_ lst
    | ScmDef'(VarFree(var),val_ ) ->  var ::  collect_fvars val_ lst
    | ScmDef'(var,val_) -> collect_fvars val_ lst 
    | ScmOr'(exprs) -> List.fold_left (fun acc expr -> collect_fvars expr acc) lst exprs
    | ScmLambdaSimple'(params,body) -> collect_fvars body lst
    | ScmLambdaOpt'(params,opt,body) -> collect_fvars body lst
    | ScmApplic'(rator,rands) -> List.fold_left (fun acc expr -> collect_fvars expr acc) lst (rator::rands)
    | ScmApplicTP'(rator,rands) -> List.fold_left (fun acc expr -> collect_fvars expr acc) lst (rator::rands)
    | _ -> lst ;;



  let rec check_all_asts_to_fvar exprs = 
    List.map (fun expr -> collect_fvars expr []) exprs


  let rec names_of_prims_list prims lst = 
    match prims with 
    | (prim, label) :: [] -> [prim]
    | (prim, label) :: cdr -> prim :: (names_of_prims_list cdr lst)
    | _ -> raise X_this_should_not_happen;;


  let rec put_offset lst offset = 
    match lst with 
    | car :: [] -> [(car, offset)]
    | car :: cdr -> (car,offset ) :: put_offset cdr (offset+8)
    | _ -> raise X_this_should_not_happen;;

  let append_with_prims list_of_fvars = List.append     
    [(* Type queries  *)
      "boolean?"; "flonum?"; "rational?";
      "pair?"; "null?"; "char?"; "string?";
      "procedure?"; "symbol?";
      (* String procedures *)
      "string-length"; "string-ref"; "string-set!";
      "make-string"; "symbol->string";
      (* Type conversions *)
      "char->integer"; "integer->char"; "exact->inexact";
      (* Identity test *)
      "eq?";
      (* Arithmetic ops *)
      "+"; "*"; "/"; "="; "<";
      (* Additional rational numebr ops *)
      "numerator"; "denominator"; "gcd";
      (* you can add yours here *)
      "cons"; "car"; "cdr";"set-car!";"set-cdr!";"apply"] list_of_fvars ;;

  let make_fvars_tbl asts =
    let list_of_fvars = check_all_asts_to_fvar asts in 
    let list_of_fvars = List.flatten list_of_fvars in 
    let list_of_fvars_with_prims = append_with_prims list_of_fvars in
    let set_of_fvars = dup_remover [] list_of_fvars_with_prims in 
    let fvar_tbl_with_offset = put_offset set_of_fvars in fvar_tbl_with_offset 0;; 


(* --------------------- GENERATE --------------------- *)
  let counter1 = 
    ref 0;;
  let next_counter1 = 
    fun () ->
    counter1 := (!counter1) + 1;
    (string_of_int !counter1);;


  let counter2 = 
    ref 0;;
  let next_counter2 = 
    fun () ->
    counter2 := (!counter2) + 1;
    (string_of_int !counter2);;


  let counter3 = 
    ref 0;;
  let next_counter3 = 
    fun () ->
    counter3 := (!counter3) + 1;
    (string_of_int !counter3);;


  let counter4 = 
    ref 0;;
  let next_counter4 = 
    fun () ->
    counter4 := (!counter4) + 1;
    (string_of_int !counter4);;


  let rec i_range curr i_needed =
    if (i_needed = 0) then [] else 
    if (curr = i_needed) then [curr] else curr :: i_range (curr + 1) (i_needed);;   
 

 let rec get_in_const_tbl const const_tbl = 
  match const_tbl with
  | (curr_const , (offset , asm_instruction)) :: [] ->  if (curr_const = const) then offset else raise X_this_should_not_happen
  |  (curr_const , (offset , asm_instruction)) :: cdr -> if (curr_const = const) then offset else get_in_const_tbl const cdr 
  | _ -> raise X_this_should_not_happen;;



  let rec get_in_fvar_tbl var_ fvar_tbl = 
    match fvar_tbl with
    | (var , offset) :: [] ->  if (var_ = var) then offset else raise X_this_should_not_happen
    | (var , offset) :: cdr -> if (var_ = var)  then offset else get_in_fvar_tbl var_ cdr 
    | _ -> raise X_this_should_not_happen;;



let rec generate_rec consts fvars e env_size = 
    match e with 
    | ScmConst'(const) -> "mov rax,(const_tbl+" ^ string_of_int(get_in_const_tbl const consts) ^ ")\n"
    | ScmVar'(VarParam(_,minor)) -> "mov rax, qword [rbp + 8*(4+" ^ (string_of_int minor) ^ ")]\n"
    | ScmSet'((VarParam(_,minor)),val_) -> make_varparam consts fvars minor val_ env_size
    | ScmVar'(VarBound(_,major,minor)) -> "mov rax, qword [rbp + 8*2]\n mov rax, qword [rax + 8*"^(string_of_int major)^"]\n mov rax, qword [rax +8*"^(string_of_int minor)^"]\n"
    | ScmSet'(VarBound(_,major,minor),val_) -> make_varbound consts fvars major minor val_ env_size
    | ScmVar'(VarFree(var)) -> "mov rax, qword [fvar_tbl + "^ string_of_int(get_in_fvar_tbl var fvars) ^ "]\n"
    | ScmSet'(VarFree(var),val_) -> make_varfree consts var fvars val_ env_size
    | ScmDef'(VarFree(var),val_) -> def_varfree consts var fvars val_ env_size      
    | ScmSeq'(exprs) -> (List.fold_left (fun acc expr -> acc ^ generate_rec consts fvars expr env_size) "" exprs)
    | ScmIf'(test,dit,else_expr) -> (if_generate consts fvars test dit else_expr env_size (next_counter2()))
    | ScmOr'(exprs) -> let lexit = "Lexit" ^ next_counter2() in
                          "\n" ^ (or_generate consts fvars env_size exprs lexit)
    | ScmBoxGet'(var) ->  (generate_rec consts fvars (ScmVar'(var)) env_size)^"\n mov rax, qword [rax]\n"
    | ScmBoxSet'(var,expr) -> (generate_rec consts fvars expr env_size)^"\n push rax\n"^(generate_rec consts fvars (ScmVar'(var)) env_size)^"pop qword [rax] \n mov rax,SOB_VOID_ADDRESS\n"
    | ScmBox'(var) -> "\n"^(generate_rec consts fvars (ScmVar'(var)) env_size)^"\npush rax"^"\nMALLOC rax, 8"^"\npop qword [rax]\n"
    | ScmLambdaSimple'(params,body) -> (lambda_generate consts fvars params body env_size (next_counter3()) )      
    | ScmLambdaOpt'(params,opt,body) -> (generate_lambda_opt consts fvars params opt body env_size (next_counter3()))
    | ScmApplic'(rator, rands) -> (generate_applic consts fvars rator rands env_size (next_counter3()))
    | ScmApplicTP'(rator, rands) -> (applic_tp_generate consts fvars rator rands env_size)


    and check_if_good_2 len = len


    and or_generate consts fvars env_size exprs lexit =
      let or_exp_code exp =
        (generate_rec consts fvars exp env_size) ^ "\n" ^
        "cmp rax, SOB_FALSE_ADDRESS\n" ^
        "jne " ^ lexit ^ "\n" in
      match exprs with
      | exp::[] ->  (generate_rec consts fvars exp env_size) ^ "\n" ^ lexit ^ ":\n"
      | exp::cdr -> (or_exp_code exp) ^ (or_generate consts fvars env_size cdr lexit)
      | _ -> raise X_this_should_not_happen


    and generate_lambda_opt consts fvars params opt body env_size lambda_num = 
      let ex_alloc = 
        "MALLOC rbx , 8*"^(string_of_int (env_size+1))^"\n"^
        "mov rcx , qword [rbp + 8*2]\n"in 
      let new_env_copier = 
        (String.concat "" (List.map (fun i -> "mov rdi, qword [rcx + 8*"^(string_of_int i)^"]\n"^
        "mov qword [rbx +8*"^(string_of_int (i+1))^"], rdi\n")
        (i_range 0 (env_size)))) in 
      let alloc_params =
        "alloc_params"^lambda_num^":\n"^
        "mov rcx , qword [rbp + 8*3]\n"^
        "inc rcx\n"^
        "mov r11, rcx\n"^
        "SHL_THREE r11\n"^
        "MALLOC r12 , r11\n"^
        "mov qword [rbx], r12\n"^
        "Lambda_loop"^lambda_num^":\n"^
        "mov rdx, [rbp + 8*3 + 8*rcx ]\n"^
        "mov [r12 + 8*rcx - 8], rdx\n"^
        "loop Lambda_loop"^lambda_num^"\n" in
    let make_closure = 
        "MAKE_CLOSURE(rax,rbx, Lcode"^lambda_num^")\n"^
        "jmp Lcont"^lambda_num^"\n" in
    (*closure body*)
    let body_string =
      "Lcode"^lambda_num^":\n"^
      "push rbp\n"^
      "mov rbp,rsp\n" in 
    let stack_fixing = 
      "mov rdx, "^(string_of_int (List.length params))^ " ; rdx = num of params\n"^
      "mov rcx , qword [rbp + 8*3]\n"^
      "mov r14,qword [rbp + 8*3]\n"^
      "cmp rcx, rdx\n"^
      "jz finish_fix_stack"^lambda_num^"\n"^
      "mov r11, rcx\n"^
      "ADD_THREE r11\n"^
      "SHL_THREE r11\n"^
      "add r11, rbp\n"^
      "sub rcx, rdx\n"^
      "mov rdx, qword [r11]\n"^
      "MAKE_PAIR(rsi, rdx, SOB_NIL_ADDRESS)\n"^
      "dec rcx\n"^
      "cmp rcx, 0\n"^
      "jz end_magic_loop"^lambda_num^"\n"^
      "magic_loop"^lambda_num^":\n"^
      "SUB_THREE r11\n"^
      "SUB_THREE r11\n"^
      "sub r11, 2\n"^
      "mov rdx, qword [r11]\n"^
      "mov r8, rsi\n"^
      "MAKE_PAIR(rsi,rdx,r8)\n"^
      "loop magic_loop"^lambda_num^"\n"^
      "end_magic_loop"^lambda_num^":\n"^
      "mov [r11], rsi\n"^
      "mov qword [rbp + 3*8], r14\n" in
      let end_of_fix = 
      "finish_fix_stack"^lambda_num^":\n"^
      (generate_rec consts fvars body (env_size+1))^
      "leave\n"^
      "ret\n"^
      "Lcont"^lambda_num^":\n" in 

      let total_lambda = String.concat "" [ex_alloc ; new_env_copier ; alloc_params ; make_closure ; body_string ; stack_fixing ; end_of_fix] in 
      
      total_lambda



    and applic_tp_generate consts fvars rator rands env_size = 
      let args_generate = 
        "mov rax , SOB_NIL_ADDRESS\n"^
        "push rax\n"^
        (List.fold_right (fun rand acc -> acc ^ (generate_rec consts fvars rand env_size) ^"push rax\n") rands ""  ) in
      let len = "push %d\n" #% (List.length rands) in
      let len = check_if_good_2 len in
      let rat_generate = (generate_rec consts fvars rator env_size) in 
      let fix_stack_push = "CLOSURE_ENV r9, rax\n"^
                               "push r9\n"^ 
                               "SHIFT_THE_FRAME "^(string_of_int ((List.length rands) + 5))^"\n" in
      let push_closure =       "CLOSURE_CODE r9, rax\n"^
                               "jmp r9\n" in
      let clean_applic =       "add rsp , 8*1 ; pop env\n"^
                               "pop rbx ; pop arg count\n"^
                               "inc rbx\n"^
                               "SHL_THREE rbx\n"^
                                "add rsp , rbx\n" in 
      let applic_total = String.concat "" [args_generate; len; rat_generate; fix_stack_push; push_closure; clean_applic ] in
      let applic_total_out =  ""^applic_total in
      applic_total_out



    and generate_applic consts fvars rator rands env_size counter4 = 
      let args_generate = 
        "applic"^counter4^":\n"^
        "mov rax , SOB_NIL_ADDRESS\n"^
        "push rax\n"^
        (List.fold_right (fun rand acc -> acc ^ (generate_rec consts fvars rand env_size) ^"push rax\n") rands ""  ) in
      let len = "push %d\n" #% (List.length rands) in
      let rat_generate = (generate_rec consts fvars rator env_size) in 
      let push_closure = "CLOSURE_ENV r9, rax\n"^
                          "push r9\n"^
                          "CLOSURE_CODE r9, rax\n"^ 
                      "call r9\n" in 
      let clean_applic = "add rsp , 8*1\n"^
                         "pop rbx\n"^
                          "inc rbx\n"^
                         "SHL_THREE rbx\n"^
                         "add rsp , rbx; pop args\n" in 
      let applic_total = String.concat "" [args_generate; len; rat_generate; push_closure; clean_applic] in 
      let applic_total_out =  ""^applic_total in
      applic_total_out





    and lambda_generate consts fvars params body env_size lambda_num = 
      let ex_alloc = 
        "MALLOC rbx , 8*"^(string_of_int (env_size+1))^"\n"^
        "mov rcx , qword [rbp + 8*2]\n"in 
      let new_env_copier = 
        (String.concat "" (List.map (fun i -> "mov rdi, qword [rcx + 8*"^(string_of_int i)^"]\n"^
        "mov qword [rbx +8*"^(string_of_int (i+1))^"], rdi\n")
        (i_range 0 (env_size)) )) in 
      let alloc_params =
        "alloc_params"^lambda_num^":\n"^
        "mov rcx , qword [rbp + 8*3]\n"^
        "inc rcx\n"^
        "mov r10, rcx\n"^
        "SHL_THREE r10\n"^
        "MALLOC r11 , r10\n"^
        "mov qword [rbx], r11\n"^
        "Lambda_loop"^lambda_num^":\n"^
        "mov rdx, [rbp + 8*3 + 8*rcx ]\n"^
        "mov [r11 + 8*rcx - 8], rdx\n"^
        "loop Lambda_loop"^lambda_num^"\n" in
    let make_closure = 
        "MAKE_CLOSURE(rax,rbx, Lcode"^lambda_num^")\n"^
        "jmp Lcont"^lambda_num^"\n" in
    let body = 
      "Lcode"^lambda_num^":\n"^
      "push rbp\n"^
      "mov rbp,rsp\n"^
      (generate_rec consts fvars body (env_size+1))^
      "leave\n"^
      "ret\n"^
      "Lcont"^lambda_num^":\n" in 


    let lambda_total = String.concat "" [ex_alloc ; new_env_copier ; alloc_params ; make_closure ; body] in 
    let lambda_total_out =  ""^lambda_total in
    lambda_total_out


  and make_varparam consts fvars minor val_ env_size  = 
    let value_to_str = generate_rec consts fvars val_ env_size in
    let returned = value_to_str  ^  "mov qword [rbp + 8*(4+" ^ (string_of_int minor) ^ ")], rax\n mov rax, SOB_VOID_ADDRESS\n" in 
    let ret = ""^returned in
    ret

  

  and make_varbound consts fvars major minor val_ env_size = 
    let value_to_str = generate_rec consts fvars val_ env_size in
    let returned = value_to_str ^ "mov rbx, qword [rbp + 8*2]\n mov rbx, qword [rbx + 8*"^(string_of_int major)^"]\n mov qword [rbx + 8*"^(string_of_int minor)^"], rax\n mov rax, SOB_VOID_ADDRESS\n" in 
    let ret = ""^returned in
    ret

  

  and make_varfree consts var fvars val_ env_size  = 
    let value_to_str = generate_rec consts fvars val_ env_size in
    let returned = value_to_str  ^  "mov qword [fvar_tbl + " ^ (string_of_int (get_in_fvar_tbl var fvars)) ^ "], rax\n mov rax, SOB_VOID_ADDRESS\n" in 
    let ret = ""^returned in
    ret
            
  and def_varfree consts var fvars val_ env_size  = 
    let value_to_str = generate_rec consts fvars val_ env_size in
    let returned = value_to_str  ^  "mov qword [fvar_tbl + " ^ (string_of_int (get_in_fvar_tbl var fvars)) ^ "], rax\n mov rax, SOB_VOID_ADDRESS\n" in 
    let ret = ""^returned in
    ret


  and if_generate consts fvars test dit else_expr env_size curr_counter2 = 
    let test = (generate_rec consts fvars test env_size) in
    let dit_dif = test ^
                                "cmp rax, SOB_FALSE_ADDRESS\n
                                je Lelse"^curr_counter2^"\n" 
                                ^ (generate_rec consts fvars dit env_size) ^ 
                                "jmp Lexit"^curr_counter2^"\n
                                Lelse"^curr_counter2^":\n"
                                ^ (generate_rec consts fvars else_expr env_size) ^
                                "Lexit"^curr_counter2^":\n" in dit_dif 

  let generate consts fvars e = generate_rec consts fvars e 0



end;;