#use "semantic-analyser.ml";;
open Semantics;;
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
  val make_consts_tbl : expr' list -> (constant * (int * string)) list

  (* This signature assumes the structure of the fvars table is
     a list of key-value pairs:
     - The keys are the fvar names as strings
     - The values are the offsets from the base fvars_table address in bytes
     For example: [("boolean?", 0)]
   *)  
  val make_fvars_tbl : expr' list -> (string * int) list

  (* If you change the types of the constants and fvars tables, you will have to update
     this signature to match: The first argument is the constants table type, the second 
     argument is the fvars table type, and the third is an expr' that has been annotated 
     by the semantic analyser.
   *)
  val generate : (constant * (int * string)) list -> (string * int) list -> expr' -> string
end;;


module Code_Gen : CODE_GEN = struct

  let index =ref 0;;

let get_index = 
  fun()->
  index := (!index) + 1;
  (string_of_int (!index));;





  let rec generate_let_rec consts fvars e env_size=
    match e with 
    | Const'(x) -> "mov rax, const_tbl+"^(string_of_int (addressInConstTable x consts))^"\n"
    | Var'(VarParam(_, minor)) -> "mov rax, qword[rbp+8 *(4+"^(string_of_int minor)^")]\n"
    | Set'(VarParam(_, minor),expr)-> 
        (generate_let_rec consts fvars expr env_size)^
          "\n;kaki_baain\nmov qword[rbp+8*(4+"^(string_of_int minor)^")],rax\n"^
          "mov rax,SOB_VOID_ADDRESS"
    | Var'(VarBound(_, major, minor))-> 
    "mov rax,qword[rbp+8*2]
     mov rax,qword[rax+8*"^(string_of_int (major+1))^"]
     mov rax,qword[rax+8*"^(string_of_int minor)^"]"
    | Set'(VarBound(_,major,minor),expr)->
      (generate_let_rec consts fvars expr env_size)^
      "\nmov rbx,qword[rbp+8*2]\n
      mov rbx,qword[rbx+8*"^(string_of_int (major+1))^"]\n
      mov qword[rbx+8*"^(string_of_int minor)^"],rax\n
      mov rax,SOB_VOID_ADDRESS\n"
    | Var'(VarFree(v))-> 
        "mov rax,qword[fvar_tbl+"^ (string_of_int (labelInFVarTable v fvars))^"]"
    | Set'(VarFree(v),expr)-> 
        (generate_let_rec consts fvars expr env_size)^
         "mov qword[fvar_tbl+"^ string_of_int (labelInFVarTable v fvars)^"],rax\n"^
         "mov rax,SOB_VOID_ADDRESS\n"
    | Def'(VarFree(v),expr)-> 
        (generate_let_rec consts fvars expr env_size)^
          "mov qword[fvar_tbl+"^ string_of_int (labelInFVarTable v fvars)^"],rax\n"^
          "mov rax,SOB_VOID_ADDRESS\n"
    | Seq'(exprs)-> (generate_let_rec_seq consts fvars exprs env_size)
    | Box'(VarParam (_,minor)) -> "
    MALLOC rax , 8
    mov r10, PVAR ("^(string_of_int minor)^")
    mov qword [rax] , r10\n "

    | Or'(exprs)-> 
      (let orIndex =get_index() in 
      (generate_let_rec_or consts fvars exprs orIndex env_size)^"Lexit"^(orIndex)^":\n")
    | If'(test,dit,dif) -> (
      let if_index= get_index() in   
      (generate_let_rec consts fvars test env_size)^ "cmp rax, SOB_FALSE_ADDRESS\n je Lelse"^( if_index)^"\n"^
      (generate_let_rec consts fvars dit env_size)^"jmp Lexit"^( if_index) ^"\nLelse"^(if_index)^":\n"^
      (generate_let_rec consts fvars dif env_size)^"Lexit"^if_index^":\n")
    | BoxGet'(v) -> (generate_let_rec consts fvars (Var'(v)) env_size)^
      "\nmov rax,qword[rax]\n"
    | BoxSet'(v,expr) -> "
    ;elad homo\n"^(generate_let_rec consts fvars expr env_size)^"\npush rax\n"^(generate_let_rec consts fvars (Var'(v)) env_size)^"\npop qword [rax]\nmov rax, SOB_VOID_ADDRESS\n"
    | LambdaSimple'(args,body) -> generate_lambda consts fvars args body (env_size+1) 
    | LambdaOpt'(args, opt ,body) -> generate_lambda_opt consts fvars args opt body (env_size+1) 
    | Applic'(proc , args) -> generate_apllic consts fvars proc args env_size
    | ApplicTP'(proc , args) -> generate_apllic consts fvars proc args env_size
    | never -> "ZAIN BAAIN"

    and generate_apllic_TP consts fvars proc args env_size = 
    let applic_size = (get_size args) in
    let applic_index = get_index() in
    let applic_args = ";;********START APPLIC TP*********
    " ^ ((generate_applic_args consts fvars args env_size)^"
    push "^(string_of_int applic_size))^"\n" in
    let proci =  generate_let_rec consts fvars proc env_size in
    let verify_closure_fix_stack = "
    mov sil, byte[rax]
    cmp sil ,T_CLOSURE
    jnz end_applic"^applic_index^"
    CLOSURE_ENV r10 , rax
    push r10
    push qword [rbp + 8*1] ; old return addr
    
    ;fix_stack:
    mov rbx, [rbp+ 8*3]; num of args in first frame
    imul rbx, rbx, 8
    add rbx, 8*3
    add rbx, rbp  ; rbx= rbp +8*3 +8*rbx
    
    mov rcx, rbp  ; rcx points on the last arg in new frame
    sub rcx, 8

    mov rbp, rbx

    mov r8, [rsp+ 8*2] ; r8 num of args in new frame
    add r8, 3  ;size of the loop 
    loop_fix_frame"^applic_index^":
    cmp r8, 0
    je end_loop_fix_frame"^applic_index^"
    mov r9, qword[rcx]
    mov qword[rbx], r9
    sub rbx, 8
    sub rcx,8 
    dec r8
    jmp loop_fix_frame"^applic_index^"
    end_loop_fix_frame"^applic_index^":
    
    add rbx, 8
    mov rsp, rbx ; important!!!! fix the rsp to bottom of the new frame

    ;----end fix stack

    CLOSURE_CODE r10 ,rax
    jmp r10    
    end_applic"^applic_index^":
    ;;********END APPLIC TP********* \n" in
      applic_args^proci^verify_closure_fix_stack 

  and generate_apllic consts fvars proc args env_size = 
    let applic_size = (get_size args) in
    let applic_index = get_index() in
    let applic_args = ";;********START APPLIC*********
    " ^ ((generate_applic_args consts fvars args env_size)^"
    push "^(string_of_int applic_size))^"\n" in
    let proci =  generate_let_rec consts fvars proc env_size in
    let verify_closure = "
    mov sil, byte[rax]
    cmp sil ,T_CLOSURE
    jnz end_applic"^applic_index^"
    CLOSURE_ENV r10 , rax
    push r10
    CLOSURE_CODE r10 ,rax
    call r10
    end_applic"^applic_index^":
    add rsp , 8*1 ;; pop env
    pop rbx ;; pop arg count
    shl rbx ,3 ;; ebx = ebx*8
    add rsp , rbx ; pop args 
    ;;********END APPLIC********* \n" in
      applic_args^proci^verify_closure 
    
  and generate_applic_args consts fvars args env_size =
    match args with 
    | [] -> ""
    | [x] ->( generate_let_rec consts fvars x env_size) ^ "\n push rax\n"
    | x :: y ->( generate_applic_args consts fvars y env_size) ^
      ( generate_let_rec consts fvars x env_size) ^ "\n push rax\n"


  and get_size args = 
  match args with 
  | [] -> 0
  | [x] -> 1
  | x :: y -> (1 + ( get_size y))

  and get_size_strings args = 
  match args with 
  | [] -> 0
  | [x] -> 1
  | x :: y -> (1 + ( get_size_strings y))

  and generate_lambda_opt consts fvars args opt body env_size = 
  let index_lambda = get_index() in
  let args_size = (string_of_int((get_size_strings args)))
  in
  ";-------start lambda opt ------
  MALLOC rax , "^(string_of_int (8*env_size))^"
  mov r8 , rax ;r8 point the new ExtEnv
  mov rbx , r8 ;; rbx point to ExtEnv[0]
  add rbx , 8 ;;rbx point to ExtEnv[1]
  mov r9 , "^(string_of_int (env_size))^"
  cmp r9 ,1
  jz First_Opt_lambda"^(index_lambda)^"
  ;---not first lambda opt ----
  mov r10 , qword[rbp+8*2] ; r10 = lexiacl env
  mov r11 , 1 ; index for ext env
  mov r12 , " ^(string_of_int (env_size-1))^";size for the loop
  
  loop_copy_env"^index_lambda^":
  cmp r12,0
  jz end_copy_env"^index_lambda^"
  mov r13 , qword[r10] ;env[i]
  mov [rbx] , r13 ; ExtEnv[i+1] = env[i]
  add rbx,8
  add r10 ,8
  dec r12 
  jmp loop_copy_env"^index_lambda^"
  
  end_copy_env"^index_lambda^":
  jmp end_first_lambda_opt"^(index_lambda)^"
  
  First_Opt_lambda"^(index_lambda)^":
  
  end_first_lambda_opt"^(index_lambda)^":
  
  MALLOC rax , 8*"^(args_size)^"+8
  mov qword[r8] , rax
  
  
  MAKE_CLOSURE (rax ,r8 , LCode"^index_lambda^")
  
  jmp LCont"^index_lambda^"
  
  LCode"^index_lambda^":
  mov r8 , qword[rsp+8*2] ; number of args
  sub r8 , "^args_size^" ;r8 num of opt parmas(num of params - args)
  imul r8 ,r8,8 
  mov r9 ,8*"^args_size^"
  add r8 , r9 
  add r8 , 8*2
  mov r12, rsp
  add r12, r8
  mov r9 , qword[r12] ; r9 = last arg of opt parmas
  
  mov r8 , qword[rsp+8*2] ; number of args
  sub r8 , "^args_size^" ;r8 num of opt parmas(num of params - args)
  
  mov r10,SOB_NIL_ADDRESS ;r10 will hold the list
  loop_opt_pairs"^index_lambda^":
  cmp r8 , 0
  jz end_loop_opt_pairs"^index_lambda^"
  MAKE_PAIR (r11 , r9 ,r10)
  mov r10, r11
  sub r12 , 8
  mov r9, qword [r12]
  dec r8
  jmp loop_opt_pairs"^index_lambda^"
  end_loop_opt_pairs"^index_lambda^":
  
  ; ---check if opt is empty
  mov r8 , qword[rsp+8*2] ; number of args
  sub r8 , "^args_size^" ;r8 num of opt parmas(num of params - args)
  cmp r8, 0
  jz do_shift"^ index_lambda^"
  mov r9, rsp
  add r9, 8*3
  add r9, 8*"^args_size^"  ;r9 poits to first opt param 
  mov [r9],r10  ;put the list in the stack
  jmp end_shift"^index_lambda^"

  do_shift"^ index_lambda^":
  mov rbx, rsp
  sub rsp, 8
  mov r8, 3+"^args_size^"   ;num of shifts
  shift_loop"^index_lambda^":
  cmp r8,0
  jz end_shift_loop"^index_lambda^"
  mov r9, [rbx]
  mov qword[rbx-8], r9
  add rbx,8
  dec r8
  jmp shift_loop"^index_lambda^"
  end_shift_loop"^index_lambda^":
  
  sub rbx, 8
  mov qword[rbx],r10    ; mov the nil to free place
  inc qword [rsp+8*2]   ; inc the num of args

  

  end_shift"^index_lambda^":
  mov r8 , qword[rsp+8]
  mov r8, qword[r8]
  mov qword[r8+8*"^args_size^"],r10
  

  push rbp
  mov rbp ,rsp

  mov r9 , "^args_size^" ;r9 = size loop (num of args)
  mov r14 ,8*4    ; r14 points the first arg
  mov r15 , qword[rbp+8*2] ;r15 points the env
  mov r15, qword[r15]

  loop_copy_args"^index_lambda^":
  cmp r9 , 0
  jz end_loop_copy_args"^index_lambda^"
  mov r10 , qword[rbp+r14] ; r10 =first arg
  mov qword[r15] , r10
  dec r9
  add r14 ,8
  add r15 ,8
  add r10, 8
  jmp loop_copy_args"^index_lambda^"

  end_loop_copy_args"^index_lambda^":


  "^(generate_let_rec consts fvars body env_size)^"
  leave
  ret
  LCont"^index_lambda^":
  ;------end lamnda opt-----------"
    



  and generate_lambda consts fvars args body env_size = 
  let index_lambda = get_index() in
  let args_size = (string_of_int(get_size_strings args))in
";-------start lambda ------
MALLOC rax , "^(string_of_int (8*env_size))^"
mov r8 , rax ;r8 point the new ExtEnv
mov rbx , r8 ;; rbx point to ExtEnv[0]
add rbx , 8 ;;rbx point to ExtEnv[1]
mov r9 , "^(string_of_int (env_size))^"
cmp r9 ,1
jz First_lambda"^(index_lambda)^"
;---not first lambda ----
mov r10 , qword[rbp+8*2] ; r10 = lexiacl env
mov r11 , 1 ; index for ext env
mov r12 , " ^(string_of_int (env_size-1))^";size for the loop

loop_copy_env"^index_lambda^":
cmp r12,0
jz end_copy_env"^index_lambda^"
mov r13 , qword[r10] ;env[i]
mov [rbx] , r13 ; ExtEnv[i+1] = env[i]
add rbx,8
add r10 ,8
dec r12 
jmp loop_copy_env"^index_lambda^"

end_copy_env"^index_lambda^":
jmp end_first_lambda"^(index_lambda)^"

First_lambda"^(index_lambda)^":

end_first_lambda"^(index_lambda)^":

MALLOC rax , 8*"^(args_size)^"
mov qword[r8] , rax



MAKE_CLOSURE (rax ,r8 , LCode"^index_lambda^")

jmp LCont"^index_lambda^"

LCode"^index_lambda^":
push rbp
mov rbp ,rsp
mov r9 , "^args_size^" ;r9 = size loop (num of args)
mov r14 ,8*4    ; r14 points the first arg
mov r15 , qword[rbp+8*2] ;r15 points the env
mov r15, qword[r15]

loop_copy_args"^index_lambda^":
cmp r9 , 0
jz end_loop_copy_args"^index_lambda^"
mov r10 , qword[rbp+r14] ; r10 =first arg
mov qword[r15] , r10
dec r9
add r14 ,8
add r15 ,8
add r10, 8
jmp loop_copy_args"^index_lambda^"

end_loop_copy_args"^index_lambda^":

"^(generate_let_rec consts fvars body env_size)^"
leave
ret
LCont"^index_lambda^":
;------end lambda--------
"


   (* and generate_lambda consts fvars args body env_size = 
      let allocate = "\nMALLOC rax,"^(string_of_int (8*env_size))^"\n" in
      let lambdaIndex = get_index() in
      let pointersVEctors=  
            "mov r9 ,"^(string_of_int (env_size-1))^";; size for the loop\n"^
            "mov r10, qword[rbp+16]\n ;;pointer to env\n"^
            "mov r11 , rax ;;save ExtEnv[0] in r11\n
            add rax, 8 ;; go for ExtENV[1]\n
            \nloopStart"^lambdaIndex^":\n
            mov r8 , [r10] ;;r10 = ENV[0]\n
            mov qword[rax],r8 ;; ExtEnv[j] = Env[i]\n
            add rax ,8 \n
            add r10 ,8 \n
            dec r9 \n
            cmp r9 ,0\n
            jnz loopStart"^(lambdaIndex)^"\n" in 
      
      let allocateParams = 
        "MALLOC rax, "^(string_of_int ((List.length args)*8))^"\n 
        mov qword[r11],rax ;; move the new vec to ExtEnv[0]\n" in
      let num_size = (get_size_strings args) in
      let copy_args =
        "
        mov r9 , qword[rbp + 8*4]  ;; r9 point to first arg on stack\n
        mov r10,"^(string_of_int num_size)^";;size of loop
        loop_copy_args"^lambdaIndex^":
        cmp r10 , 0
        jz endloop_copy_args"^lambdaIndex^"
        mov rbx , [r9] 
        mov qword[rax] , rbx
        add rax ,8
        add r9 , 8
        dec r10
        cmp r10, 0 
        jmp loop_copy_args"^lambdaIndex^"\n
        endloop_copy_args"^lambdaIndex^":\n" in 
      let closure= "MAKE_CLOSURE (rax ,r11 , LambdaCode"^lambdaIndex^")\n"^
          "jmp Lcont"^lambdaIndex^"\n" in
      let closure_first= "MAKE_CLOSURE (rax ,r11 , LambdaCode"^lambdaIndex^")\n"^
      "jmp Lcont"^lambdaIndex^"\n" in
      let body = "LambdaCode"^lambdaIndex^":\n"^
                "push rbp\n
                 mov rbp , rsp\n"^
         (generate_let_rec consts fvars body env_size)^
                "\nleave\n
                ret\n
                Lcont"^lambdaIndex^":\n" in
      let allocate_first_env = 
        "MALLOC rax , 8
        mov r11 , rax\n" in
      if(env_size>1) then 
      (";;**********Start Lambda***********\n"^allocate^pointersVEctors^allocateParams^copy_args^closure^body^"\n;;**********End Lambda***********\n")
      else (";;**********Start first Lambda*********
      \n"^allocate_first_env^allocateParams^copy_args^closure_first^ body^"\n;;**********End first Lambda***********\n") *)
          
      

  
    and generate_let_rec_or consts fvars exprs orIndex env_size=
    match exprs with
    | []->""
    | [x]-> (generate_let_rec consts fvars x env_size)^"\n"^
        "cmp rax, SOB_FALSE_ADDRESS\njne Lexit"^(orIndex)
    | x::y -> (generate_let_rec consts fvars x env_size)^"\n"^
    "cmp rax, SOB_FALSE_ADDRESS\njne Lexit"^(orIndex)^"\n"^(generate_let_rec_or consts fvars y orIndex env_size)

  and generate_let_rec_seq consts fvars exprs env_size=
  match exprs with 
  | []->""
  | [x]-> (generate_let_rec consts fvars x env_size)^"\n"
  | x::y -> (generate_let_rec consts fvars x env_size)^"\n"^(generate_let_rec_seq consts fvars y env_size)


  and labelInFVarTable v fvars =
  match fvars with 
    | [(y,index)] -> if (y=v) then index else -1
    | (y,index) ::z -> if (y=v) then index else labelInFVarTable v z 

  and addressInConstTable x consts=
    match consts with 
    | [(y,(off,str))] -> if (y=x) then off else -1
    | (y,(off,str)) ::z -> if (y=x) then off else addressInConstTable x z 





let rec make_consts_tbl_let_rec asts = 
   let consts=(get_consts_or_free asts [] 0) in 
   (make_const_table  consts [(Void, (0, "MAKE_VOID"));(Sexpr(Nil), (1, "MAKE_NIL"));(Sexpr(Bool(false)), (2, "MAKE_BOOL(0)"));(Sexpr(Bool(true)), (4, "MAKE_BOOL(1)"))]) 6


and make_fvars_tbl_let_rec asts =
  make_pairs (remove_dups ((get_strings (get_consts_or_free asts [] 1)) @ ["boolean?";"flonum?"; "rational?";
  "pair?";  "null?"; "char?"; "string?";
  "procedure?";  "symbol?";    "string-length"; "string-ref"; "string-set!";
  "make-string"; "symbol->string";
  "char->integer"; "integer->char";  "exact->inexact";
  (* Identity test *)
  "eq?";
  (* Arithmetic ops *)
  "+"; "*"; "/"; "="; "<";
  (* Additional rational numebr ops *)
  "numerator"; "denominator"; "gcd"]) ) 0

  and make_pairs arr index=
  match arr with
  | []-> []
  | [x]-> [(x,index)]
  | x::y -> (x, index) :: (make_pairs y (index+8))

  and remove_dups arr=
  match arr with
  | []-> []
  | [x] -> [x]
  | x::y -> if(List.mem x y) then (remove_dups y) else x::(remove_dups y)


  and get_strings arr=
  match arr with
  | [] -> []
  | [Var'(VarFree(x))] -> [x]
  | Var'(VarFree(x)) :: y -> x:: (get_strings y)
  | never -> raise X_syntax_error
  
  and get_consts_or_free asts arr flag=
   match asts with 
   | [] -> arr
   | [x] -> (find_const_or_free_vars x flag) @arr
   | x::y -> (find_const_or_free_vars x flag)@(get_consts_or_free y arr flag)

  and find_const_or_free_vars expr flag=
    match expr with
      | Const'(x) -> if(flag == 0) then [expr] else []
      | Var'(VarFree(x)) -> if(flag == 0) then [] else [expr]
      | Var'(x)-> []
      | Or'(exprs) -> handle_list_consts_or_free exprs flag
      | If'(test,dit,dif) -> (handle_list_consts_or_free [test;dit;dif] flag)
      | Def'(x,expr') -> find_const_or_free_vars expr' flag
      | Applic'(proc,exprs) ->  handle_list_consts_or_free (proc::exprs) flag
      | ApplicTP'(proc,exprs) ->  handle_list_consts_or_free (proc::exprs) flag
      | Set'(x,expr') -> find_const_or_free_vars expr' flag
      | LambdaSimple'(args, body) -> find_const_or_free_vars body flag
      | LambdaOpt'(args,arg ,body) -> find_const_or_free_vars body flag
      | Seq'(exprs) -> handle_list_consts_or_free exprs flag
      | BoxGet'(x)-> []
      | BoxSet'(x,expr')-> find_const_or_free_vars expr' flag
      | Box'(x) -> []
    
  and handle_list_consts_or_free exprs flag =
  match exprs with
      |[] -> []
      |[x] -> (find_const_or_free_vars x flag)
      |x :: y -> (find_const_or_free_vars x flag) @ (handle_list_consts_or_free y flag)








  and make_const_table consts arr offset=
   match consts with 
  | [] -> arr
  | [x] ->  (
    let (new_arr,off)= make_const_tuple arr x offset in
    new_arr
  )
  | x::y -> (
      let (new_arr,new_offset)=( make_const_tuple arr x offset) in 
      make_const_table y (new_arr) new_offset
  )


  and make_const_tuple arr const offset = 
    match const with
      | Const'(x) ->(
        match x with
        | Void -> ((arr @ [(x ,(offset ,"T_VOID"))]),(offset + 1))
        | Sexpr(Bool(true)) -> ((arr @ [(x,(offset ,"MAKE_BOOL(1)"))]) , (offset + 2) ) 
        | Sexpr(Bool(false)) -> ((arr @[(x,(offset ,"MAKE_BOOL(0)"))]) , (offset + 2 )) 
        | Sexpr(Nil) -> ((arr @ [(x,(offset,"MAKE_NILL"))]), (offset+1))
        | Sexpr(Number(Fraction(num,dim))) -> ((arr @ [(x,(offset,(Printf.sprintf "MAKE_LITERAL_RATIONAL(%d, %d)" num dim)))]), (offset+17))
        | Sexpr(Number(Float(num))) -> ((arr @ [(x,(offset,(Printf.sprintf "MAKE_LITERAL_FLOAT (%f)" num)))]), (offset+9))
        | Sexpr(Char(y)) -> ((arr @ [(x,(offset ,(Printf.sprintf "MAKE_LITERAL_CHAR(%c)" y)))]) , (offset + 2) )
        | Sexpr(String(y))-> ((arr @ [(x,(offset ,(Printf.sprintf 
        "db T_STRING
        dq %d
        db %s"(String.length y) (convert_string (string_to_list y)) ) ) )]) , (offset + 9 + (String.length y))) 
        | Sexpr(Symbol(y))-> ((arr @ [(Sexpr(String(y)),(offset ,(Printf.sprintf 
        "db T_STRING
        dq %d
        db %s"(String.length y) (convert_string (string_to_list y)) )))]  
                                @  [(x,((offset+9+(String.length y)) ,(Printf.sprintf "MAKE_LITERAL_SYMBOL(const_tbl+%d)" offset)))]) , (offset + 18 + (String.length y)) )
        | Sexpr(Pair(y1,y2)) -> 
        (
          let (arr_Car , new_offset_car) = make_const_tuple arr (Const'(Sexpr(y1))) offset in
          let (arr_Cdr , new_offset_cdr) = make_const_tuple arr_Car (Const'(Sexpr(y2))) new_offset_car in
          match y2 with
          |Pair(_)-> ((arr_Cdr @ [(x,(new_offset_cdr ,(Printf.sprintf "MAKE_LITERAL_PAIR(const_tbl+%d ,const_tbl+%d)" offset (new_offset_cdr-17))))]) , (new_offset_cdr + 17)) 
          |other-> ((arr_Cdr @ [(x,(new_offset_cdr ,(Printf.sprintf "MAKE_LITERAL_PAIR(const_tbl+%d ,const_tbl+%d)" offset new_offset_car)))]) , (new_offset_cdr + 17)) 
        )
        | never -> raise X_syntax_error)
        | never -> raise X_syntax_error
        


    and convert_string str =
      match str with
    | [] -> ""
    | [x] -> (string_of_int(Char.code x))
    | x::y ->  (string_of_int(Char.code x))^","^convert_string y
    ;;



  let make_consts_tbl asts = make_consts_tbl_let_rec asts;;
  let make_fvars_tbl asts = make_fvars_tbl_let_rec asts;;
  let generate consts fvars e = generate_let_rec  consts fvars e 0;;

end;;
(* 
let [x] = (Tag_Parser.tag_parse_expressions (read_sexprs "1") );;
  let y = run_semantics x;;


  let fre = Code_Gen.make_fvars_tbl [y];;
  let consts =Code_Gen.make_consts_tbl [y];;
  let a = Code_Gen.generate consts fre y;; *)


   
    








