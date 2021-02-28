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
  | Set' of var * expr'
  | Def' of var * expr'
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
  | Box'(VarFree v1), Box'(VarFree v2) -> String.equal v1 v2
  | Box'(VarParam (v1,mn1)), Box'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Box'(VarBound (v1,mj1,mn1)), Box'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | BoxGet'(VarFree v1), BoxGet'(VarFree v2) -> String.equal v1 v2
  | BoxGet'(VarParam (v1,mn1)), BoxGet'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | BoxGet'(VarBound (v1,mj1,mn1)), BoxGet'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | BoxSet'(VarFree v1,e1), BoxSet'(VarFree v2, e2) -> String.equal v1 v2 && (expr'_eq e1 e2)
  | BoxSet'(VarParam (v1,mn1), e1), BoxSet'(VarParam (v2,mn2),e2) -> String.equal v1 v2 && mn1 = mn2 && (expr'_eq e1 e2)
  | BoxSet'(VarBound (v1,mj1,mn1),e1), BoxSet'(VarBound (v2,mj2,mn2),e2) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2 && (expr'_eq e1 e2)
  | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                            (expr'_eq th1 th2) &&
                                              (expr'_eq el1 el2)
  | (Seq'(l1), Seq'(l2)
  | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
  | (Set'(var1, val1), Set'(var2, val2)
  | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq (Var'(var1)) (Var'(var2))) &&
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

  let rec box_set_rec e =
    match e with
    | Const'(x) -> e
    | Var'(x) -> e
    | Or'(exprs) -> Or'(handle_list_box exprs)
    | If'(test,dit,dif) -> If'((box_set_rec test), (box_set_rec dit) , (box_set_rec dif))
    | Def'(x,expr) -> Def'(x, (box_set_rec expr))
    | Applic'(proc,exprs) ->  Applic'((box_set_rec proc),(handle_list_box exprs))
    | ApplicTP'(proc,exprs) ->  ApplicTP'((box_set_rec proc),(handle_list_box exprs))
    |Set'(x,expr) -> Set'(x,(box_set_rec expr ))
    | LambdaSimple'(args, body) -> LambdaSimple'(args,(box_set_rec( handle_box_body args body 0)) )
    | LambdaOpt'(args,arg ,body) -> LambdaOpt'(args,arg, (box_set_rec( handle_box_body (args@[arg]) body 0)))
    |Seq'(exprs) -> Seq'(handle_list_box exprs )
    | BoxGet'(x)-> e
    | BoxSet'(x,expr)-> BoxSet'(x,box_set_rec expr)
    | Box'(x) -> e

and handle_list_box exprs =
match exprs with
    |[] -> []
    |[x] -> [(box_set_rec x)]
    |x :: y -> (box_set_rec x ) :: (handle_list_box y)

and handle_box_body args body index =
match args with
| [] -> body
| [x] -> handle_one_var x body index
| x :: y -> (
   let new_body = handle_one_var x body index in
   handle_box_body y new_body (index+1)
)

and handle_one_var str body minor =
  if((check_father str body (-1)))
    then (
      let box =(add_box str body (-1)) in
     match box with
     |Seq'(x) -> Seq' (insert_to_seq x str minor)
    | other -> (Seq'([Set'(VarParam(str, minor), Box'(VarParam(str,minor)));other]))
    ) else body

and insert_to_seq x str minor =
    match x with
    | [] ->  [(Set'(VarParam(str, minor), Box'(VarParam(str,minor))))]
    | [(Set'(_, Box'(_)))] -> x@[(Set'(VarParam(str, minor), Box'(VarParam(str,minor))))]
    | [y] -> [(Set'(VarParam(str, minor), Box'(VarParam(str,minor))));y]
    | (Set'(z, Box'(w))) :: y -> (Set'(z, Box'(w))) :: (insert_to_seq y str minor)
    | z :: y -> (Set'(VarParam(str, minor), Box'(VarParam(str,minor)))) :: x

and add_box str body level=
  match body with
    | Or'(exprs) -> Or'(handle_list_make_box str exprs level)
    | If'(test,dit,dif) -> If' ((add_box str test level   ) , (add_box str dit level  ) , (add_box str dif level ))
    | Def'(x,expr) -> Def'( x, add_box str expr level   )
    | LambdaSimple'(args, body) -> LambdaSimple' (args, add_box str body (level+1)   )
    | LambdaOpt'(args,arg ,body) ->LambdaOpt'( args,arg, add_box str body (level + 1)   )
    | Applic'(proc,exprs) ->  Applic' ((add_box str proc level   ) ,(handle_list_make_box str exprs level   ))
    | ApplicTP'(proc,exprs) -> ApplicTP' ((add_box str proc level   ),(handle_list_make_box str exprs level   ))
    | Set'(VarBound(x,depth,place),expr) -> if((x = str) && (depth = level)) then BoxSet'(VarBound(x,depth,place),(add_box str expr level))  else Set'(VarBound(x,depth,place),(add_box str expr level))
    | Set'(VarParam(x,place),expr) -> if((x = str) && (level=(-1))) then BoxSet'(VarParam(x,place),(add_box str expr level))  else Set'(VarParam(x,place),(add_box str expr level))
    | Set'(x,exp)-> Set'(x ,add_box str exp level )
    | Seq'(exprs) -> Seq'(handle_list_make_box str exprs level  )
    | Var'(VarBound(x,depth,place)) -> if((x = str) && (depth = level)) then BoxGet'(VarBound(x,depth,place))  else Var'(VarBound(x,depth,place))
    | Var'(VarParam(x,place)) -> if((x = str)&&(level=(-1))) then BoxGet'(VarParam(x,place))  else Var'(VarParam(x,place))
    | Var'(_) -> body
    | Const'(x) -> body
    | BoxGet'(x)-> body
    | BoxSet'(x,expr)-> BoxSet'(x,add_box str expr level)
    | Box'(x) -> body
    and handle_list_make_box str body level=
    match body with
    | []-> []
    | [x] -> [add_box str x level]
    | x::y -> (add_box str x level) :: (handle_list_make_box str y level)


and check_father str body level=
    let get_apperance_list = find_gets str body level [] 0 (-1) 0 in
    let set_apperance_list = find_sets str body level [] 0 (-1) 0 in
     (check_get_set get_apperance_list set_apperance_list str body)



and check_get_set get_list set_list str body=
    match (get_list,set_list) with
    | [],[] -> false
    | [],_ -> false
    | _, [] -> false
    | [[arg1;level1;seq1;add1;seq_index1]],[[arg2;level2;seq2;add2;seq_index2]] -> (((check_common_father str body add1 add2)=false) && (level1!=level2) && (check_seq seq1 seq2 add1 add2 seq_index1 seq_index2 body) )
    | [arg1;level1;seq1;add1;seq_index1]::rest1 , [[arg2;level2;seq2;add2;seq_index2]] -> ((((check_common_father str body add1 add2)=false)&&(level1!=level2) && (check_seq seq1 seq2 add1 add2 seq_index1 seq_index2 body)) || (check_get_set rest1 [[arg2;level2;seq2;add2;seq_index2]] str body))
    | [[arg1;level1;seq1;add1;seq_index1]], [arg2;level2;seq2;add2;seq_index2]::rest2 -> ((((check_common_father str body add1 add2)=false)&&(level1!=level2) &&(check_seq seq1 seq2 add1 add2 seq_index1 seq_index2 body)) || (check_get_set [[arg1;level1;seq1;add1;seq_index1]] rest2 str body))
    | [arg1;level1;seq1;add1;seq_index1]::rest1, [arg2;level2;seq2;add2;seq_index2]::rest2-> (
      ((((check_common_father str body add1 add2)=false)&&(level1!=level2)&&(check_seq seq1 seq2 add1 add2 seq_index1 seq_index2 body)) || (check_get_set rest1 [[arg2;level2;seq2;add2;seq_index2]] str body)) ||
      ((((check_common_father str body add1 add2)=false)&&(level1!=level2)&&(check_seq seq1 seq2 add1 add2 seq_index1 seq_index2 body)) || (check_get_set [[arg1;level1;seq1;add1;seq_index1]] rest2 str body)) ||
              (check_get_set rest1 rest2 str body))
    |other -> false

and check_seq  seq1 seq2 add1 add2 seq1_index seq2_index body=
    ((seq1!=seq2) || (seq1=(-1)) || (seq2=(-1)) ) ||
    (
      if(seq1_index <= seq2_index) then check_if_in_expr body add1 false false else if (seq1_index > seq2_index) then  check_if_in_expr body add2 false false else false
    )



and check_if_in_expr body add inside_seq inside_expr =
match body with
    | Or'(exprs) -> (check_if_in_expr_list exprs add inside_seq inside_seq)
    | If'(test,dit,dif) -> (check_if_in_expr_list [test;dit;dif] add inside_seq inside_seq)
    | Def'(x,expr) -> (check_if_in_expr expr add inside_seq inside_seq)
    | LambdaSimple'(args, body) -> (check_if_in_expr body add inside_seq inside_seq)
    | LambdaOpt'(args,arg ,body) ->(check_if_in_expr body add inside_seq inside_seq)
    | Applic'(proc,exprs) ->  (check_if_in_expr_list (proc::exprs) add inside_seq inside_seq)
    | ApplicTP'(proc,exprs) ->  (check_if_in_expr_list (proc::exprs) add inside_seq inside_seq)
    | Set'(x,expr) -> if ((1*(Obj.magic body))= add) then inside_expr else  (check_if_in_expr expr add inside_seq inside_seq)
    | Seq'(exprs) -> (check_if_in_expr_list exprs add true inside_expr)
    | Var'(VarBound(x,depth,_)) -> if ((1*(Obj.magic body))= add) then inside_expr else false
    | Var'(VarParam(x,_)) -> if ((1*(Obj.magic body))= add) then inside_expr else false
    | Var'(_) -> false
    | Const'(x) -> false
    | BoxGet'(x)-> false
    | BoxSet'(x,expr)->  (check_if_in_expr expr add inside_seq inside_seq)
    | Box'(x) -> false


    and check_if_in_expr_list exprs add inside_seq inside_expr=
match exprs with
|[] -> false
|[x] -> check_if_in_expr x add inside_seq inside_expr
| x :: y ->(check_if_in_expr x add inside_seq inside_expr || (check_if_in_expr_list  y add inside_seq inside_expr))


and find_gets str body level arr counter seq_num seq_index=
match body with
    | Or'(exprs) -> (handle_list_find_get str exprs level arr counter seq_num seq_index)
    | If'(test,dit,dif) -> ((find_gets str test level arr counter seq_num seq_index) @ (find_gets str dit level arr counter seq_num seq_index) @ (find_gets str dif level arr counter seq_num seq_index))
    | Def'(x,expr) -> (find_gets str expr level arr counter seq_num seq_index)
    | LambdaSimple'(args, body) -> (find_gets str body (level+1) arr (1*(Obj.magic body)) seq_num seq_index)
    | LambdaOpt'(args,arg ,body) ->(find_gets str body (level + 1) arr (1*(Obj.magic body)) seq_num seq_index)
    | Applic'(proc,exprs) ->  ((find_gets str proc level arr counter seq_num seq_index) @(handle_list_find_get str exprs level arr counter seq_num seq_index))
    | ApplicTP'(proc,exprs) ->  ((find_gets str proc level arr counter seq_num seq_index)@(handle_list_find_get str exprs level arr counter seq_num seq_index))
    | Set'(x,expr) ->(find_gets str expr level arr counter seq_num seq_index)
    | Seq'(exprs) -> (handle_list_find_get_seq str exprs level arr counter (1*(Obj.magic body)) 0)
    | Var'(VarBound(x,depth,_)) -> if((x = str) && (depth = level)) then ([depth;counter;seq_num;(1*(Obj.magic body));seq_index]::arr) else arr
    | Var'(VarParam(x,_)) -> if((x = str)) then ([(-1);counter;seq_num;(1*(Obj.magic body));seq_index]::arr) else arr
    | Var'(_) -> arr
    | Const'(x) -> arr
    | BoxGet'(x)-> arr
    | BoxSet'(x,expr)-> find_gets str expr level arr counter seq_num seq_index
    | Box'(x) -> arr


and handle_list_find_get str exprs level arr counter seq_num seq_index=
    match exprs with
        |[] -> []
        |[x] -> if((is_lambda x)) then  (find_gets str x level arr (1*(Obj.magic x)) seq_num seq_index) else if (is_seq x) then (find_gets str x level arr counter  (1*(Obj.magic x)) 0) else (find_gets str x level arr counter seq_num seq_index)
        |x :: y -> if((is_lambda x)) then  ((find_gets str x level arr (1*(Obj.magic x)) seq_num seq_index)@(handle_list_find_get str y level arr counter seq_num seq_index))
        else if (is_seq x) then  ((find_gets str x level arr counter  (1*(Obj.magic x)) 0)@(handle_list_find_get str y level arr counter seq_num seq_index))  else  ((find_gets str x level arr counter seq_num seq_index)@(handle_list_find_get str y level arr counter seq_num seq_index))


and handle_list_find_get_seq str exprs level arr counter seq_num seq_index=
        match exprs with
            |[] -> []
            |[x] -> if((is_lambda x)) then  (find_gets str x level arr (1*(Obj.magic x)) seq_num (seq_index+1)) else if (is_seq x) then (find_gets str x level arr counter (1*(Obj.magic x)) 0) else (find_gets str x level arr counter seq_num (seq_index+1))
            |x :: y -> if((is_lambda x)) then  ((find_gets str x level arr (1*(Obj.magic x)) seq_num (seq_index+1))@(handle_list_find_get_seq str y level arr counter seq_num (seq_index+1)))
            else if (is_seq x) then  ((find_gets str x level arr counter (1*(Obj.magic x)) 0)@(handle_list_find_get_seq str y level arr counter seq_num (seq_index+1)))  else  ((find_gets str x level arr counter seq_num (seq_index+1))@(handle_list_find_get_seq str y level arr counter seq_num (seq_index+2)))


and is_lambda x =
  match x with
  |LambdaSimple'(args, body) -> true
  | LambdaOpt'(args,arg ,body) -> true
  | _ -> false

  and is_seq x =
  match x with
  | Seq'(exprs) ->  true
  | _ -> false


and check_common_father str body add1 add2 =
match body with
| Const'(x) -> false
| Or'(exprs) -> (handle_list_check_common_father str exprs add1 add2)
| If'(test,dit,dif) ->(handle_list_check_common_father str [test;dit;dif] add1 add2 )
| Def'(x,expr) -> (check_common_father str expr add1 add2)
| LambdaSimple'(args, body) -> if ((check_common_father_lambda str body add1 add2) = (true,true)) then true else false
| LambdaOpt'(args,arg ,body) -> if ((check_common_father_lambda str body add1 add2) = (true,true)) then true else false
| Applic'(proc,exprs) ->  (handle_list_check_common_father str (proc::exprs) add1 add2 )
| ApplicTP'(proc,exprs) ->  (handle_list_check_common_father str (proc::exprs) add1 add2 )
| Set'(y ,expr) ->
    (match y with
  |VarParam(x,_) -> if((1*(Obj.magic y))= add2)  then (find_get_inside_lambda str expr false add1)   else (check_common_father str expr add1 add2)
  | other ->  (check_common_father str expr add1 add2) )
| Seq'(exprs) -> (handle_list_check_common_father str exprs add1 add2)
| Var'(VarParam(x,_)) -> if((1*(Obj.magic body))= add1) then false else false
| Var'(VarBound(x,_,_)) -> if((1*(Obj.magic body))= add1) then true else false
| Var'(_) ->false
| BoxGet'(x)-> false
| BoxSet'(x,expr)-> check_common_father str expr add1 add2
| Box'(x) -> false

and handle_list_check_common_father str body add1 add2 =
    match body with
    |[] -> false
    |[x] -> check_common_father str x add1 add2
    | x :: y -> (
      match x with
      | Var'(VarParam(name,_)) -> find_set_inside_lambda_list str y false add2
      | Var'(VarBound(name,_,_)) -> find_set_inside_lambda_list str y false add2
      | other -> (( check_common_father str x add1 add2) || (handle_list_check_common_father str y add1 add2)))

and find_set_inside_lambda str body inside add2 =
match body with
| Const'(x) -> false
| Or'(exprs) -> (find_set_inside_lambda_list str exprs inside add2)
| If'(test,dit,dif) ->((find_set_inside_lambda str test inside add2) || (find_set_inside_lambda str dit inside add2) ||(find_set_inside_lambda str dif inside add2 ))
| Def'(x,expr) -> (find_set_inside_lambda str expr inside add2)
| LambdaSimple'(args, body) -> (find_set_inside_lambda str body true add2)
| LambdaOpt'(args,arg ,body) -> (find_set_inside_lambda str body true add2)
| Applic'(proc,exprs) ->  ((find_set_inside_lambda str proc  inside add2) || (find_set_inside_lambda_list str exprs inside add2))
| ApplicTP'(proc,exprs) ->   ((find_set_inside_lambda str proc  inside add2) || (find_set_inside_lambda_list str exprs  inside add2))
| Set'(VarParam(x,_),expr) ->if(((1*(Obj.magic body))= add2)&&inside) then true else (find_set_inside_lambda str expr inside add2 )
| Set'(_,expr) ->(find_set_inside_lambda str expr inside add2 )
| Seq'(exprs) -> (find_set_inside_lambda_list str exprs inside add2)
| Var'(_) ->false
| BoxGet'(x)-> false
| BoxSet'(x,expr)-> find_set_inside_lambda str expr inside add2
| Box'(x) -> false

and find_set_inside_lambda_list str body inside add2=
match body with
|[] -> false
|[x] -> find_set_inside_lambda str x inside add2
| x :: y ->(( find_set_inside_lambda str x  inside add2) || (find_set_inside_lambda_list str y inside add2))


and find_get_inside_lambda str body inside add1=
match body with
| Const'(x) -> false
| Or'(exprs) -> (find_get_inside_lambda_list str exprs inside add1)
| If'(test,dit,dif) ->((find_get_inside_lambda str test inside add1) || (find_get_inside_lambda str dit inside add1) ||(find_get_inside_lambda str dif inside add1 ))
| Def'(x,expr) -> (find_get_inside_lambda str expr inside add1)
| LambdaSimple'(args, body) -> (find_get_inside_lambda str body true add1)
| LambdaOpt'(args,arg ,body) -> (find_get_inside_lambda str body true add1)
| Applic'(proc,exprs) ->  ((find_get_inside_lambda str proc  inside add1) || (find_get_inside_lambda_list str exprs inside add1))
| ApplicTP'(proc,exprs) ->   ((find_get_inside_lambda str proc   inside add1) || (find_get_inside_lambda_list str exprs  inside add1))
| Set'(x,expr) ->(find_get_inside_lambda str expr inside add1)
| Seq'(exprs) -> (find_get_inside_lambda_list str exprs inside add1)
| Var'(VarBound(x,_,_)) -> if(((1*(Obj.magic body))= add1)&&inside) then true else false
| Var'(_) ->false
| BoxGet'(x)-> false
| BoxSet'(x,expr)-> find_get_inside_lambda str expr inside add1
| Box'(x) -> false

and find_get_inside_lambda_list str body inside add1=
match body with
|[] -> false
|[x] -> find_get_inside_lambda str x inside add1
| x :: y ->(( find_get_inside_lambda str x  inside add1) || (find_get_inside_lambda_list str y inside add1))





and check_common_father_lambda str body add1 add2 =
match body with
| Const'(x) -> (false,false)
| Or'(exprs) -> (handle_list_check_common_father_lambda str exprs add1 add2)
| If'(test,dit,dif) ->
(
  let (test1,test2)= check_common_father_lambda str test add1 add2 in
  let (dit1, dit2) = check_common_father_lambda str dit add1 add2 in
  let (dif1, dif2) = check_common_father_lambda str dif add1 add2 in
  ((test1||dit1||dif1),(test2||dit2||dif2))
)
| Def'(x,expr) -> (check_common_father_lambda str expr add1 add2)
| LambdaSimple'(args, body) -> (check_common_father_lambda str body add1 add2)
| LambdaOpt'(args,arg ,body) ->(check_common_father_lambda str body add1 add2)
| Applic'(proc,exprs) ->
(
  let (proc1,proc2) = (check_common_father_lambda str proc add1 add2) in
  let (body1,body2) = (handle_list_check_common_father_lambda str exprs add1 add2) in
  ((proc1||body1),(proc2||body2))
)
| ApplicTP'(proc,exprs) ->  (
  let (proc1,proc2) = (check_common_father_lambda str proc add1 add2) in
  let (body1,body2) = (handle_list_check_common_father_lambda str exprs add1 add2) in
  ((proc1||body1),(proc2||body2))
)
| Set'(VarBound(x,_,_),expr) ->
(
  let( expr1,expr2) = check_common_father_lambda str expr add1 add2 in
  if(((1*(Obj.magic body))= add2)) then (expr1,true) else (expr1,expr2)
)
| Set'(VarParam(x,_),expr) ->
(
  let( expr1,expr2) = check_common_father_lambda str expr add1 add2 in
  if(((1*(Obj.magic body))= add2)) then (expr1,true) else (expr1,expr2)
)
| Set'(VarFree(_),expr) -> check_common_father_lambda str expr add1 add2
| Seq'(exprs) -> (handle_list_check_common_father_lambda str exprs add1 add2)
| Var'(VarBound(x,depth,_)) -> if(((1*(Obj.magic body))= add1)) then (true,false) else (false,false)
| Var'(VarParam(x,_)) -> if(((1*(Obj.magic body))= add1))  then  (true,false) else (false,false)
| Var'(_) -> (false,false)
| BoxGet'(x)-> (false,false)
| BoxSet'(x,expr)-> check_common_father_lambda str expr add1 add2
| Box'(x) -> (false,false)


and handle_list_check_common_father_lambda str body add1 add2 =
    match body with
    |[] -> (false,false)
    |[x] -> check_common_father_lambda str x add1 add2
    | x :: y ->
    (
      let (expr1,expr2) = check_common_father_lambda str x add1 add2 in
      let (rest1,rest2) = (handle_list_check_common_father_lambda str y add1 add2) in
      ((expr1||rest1),(expr2||rest2))
    )


and find_sets str body level arr counter seq_num seq_index=
match body with
    | Or'(exprs) -> (handle_list_find_set str exprs level arr counter seq_num seq_index)
    | If'(test,dit,dif) -> ((find_sets str test level arr counter seq_num seq_index) @ (find_sets str dit level arr counter seq_num seq_index) @ (find_sets str dif level arr counter seq_num seq_index))
    | Def'(x,expr) -> (find_sets str expr level arr counter seq_num seq_index)
    | LambdaSimple'(args, body) -> (find_sets str body (level+1) arr (1*(Obj.magic body)) seq_num seq_index)
    | LambdaOpt'(args,arg ,body) ->(find_sets str body (level + 1) arr (1*(Obj.magic body)) seq_num seq_index)
    | Applic'(proc,exprs) ->  ((find_sets str proc level arr counter seq_num seq_index) @(handle_list_find_set str exprs level arr counter seq_num seq_index))
    | ApplicTP'(proc,exprs) ->  ((find_sets str proc level arr counter seq_num seq_index) @(handle_list_find_set str exprs level arr counter seq_num seq_index))
    |Set'(VarBound(x,depth,_),expr) -> if((x = str) && (depth = level)) then (([depth;counter;seq_num;(1*(Obj.magic body));seq_index]::arr)@(find_sets str expr level arr counter seq_num seq_index)) else (find_sets str expr level arr counter seq_num seq_index)
    |Set'(VarParam(x,_),expr) -> if(x = str) then (([(-1);counter;seq_num;(1*(Obj.magic body));seq_index]::arr)@(find_sets str expr level arr counter seq_num seq_index)) else (find_sets str expr level arr counter seq_num seq_index)
    |Set'(x,expr) ->(find_sets str expr level arr counter seq_num seq_index)
    |Seq'(exprs) -> (handle_list_find_set_seq str exprs level arr counter (1*(Obj.magic body)) 0)
    |Var'(_) -> arr
    | Const'(x) -> arr
    | BoxGet'(x)-> arr
    | BoxSet'(x,expr)-> find_sets str expr level arr counter seq_num seq_index
    | Box'(x) -> arr



    and handle_list_find_set str exprs level arr counter seq_num seq_index=
    match exprs with
        |[] -> []
        |[x] -> if((is_lambda x)) then  (find_sets str x level arr (1*(Obj.magic x)) seq_num seq_index) else if (is_seq x) then (find_sets str x level arr counter  (1*(Obj.magic x)) 0) else (find_sets str x level arr counter seq_num seq_index)
        |x :: y -> if((is_lambda x)) then  ((find_sets str x level arr (1*(Obj.magic x)) seq_num seq_index)@(handle_list_find_set str y level arr counter seq_num seq_index))
        else if (is_seq x) then  ((find_sets str x level arr counter  (1*(Obj.magic x)) 0)@(handle_list_find_set str y level arr counter seq_num seq_index))  else  ((find_sets str x level arr counter seq_num seq_index)@(handle_list_find_set str y level arr counter seq_num seq_index))


and handle_list_find_set_seq str exprs level arr counter seq_num seq_index=
        match exprs with
            |[] -> []
            |[x] -> if((is_lambda x)) then  (find_sets str x level arr (1*(Obj.magic x)) seq_num (seq_index+1)) else if (is_seq x) then (find_sets str x level arr counter (1*(Obj.magic x)) 0) else (find_sets str x level arr counter seq_num (seq_index+1))
            |x :: y -> if((is_lambda x)) then  ((find_sets str x level arr (1*(Obj.magic x)) seq_num (seq_index+1))@(handle_list_find_set_seq str y level arr counter seq_num (seq_index+1)))
            else if (is_seq x) then  ((find_sets str x level arr counter (1*(Obj.magic x)) 0)@(handle_list_find_set_seq str y level arr counter seq_num (seq_index+1)))  else  ((find_sets str x level arr counter seq_num (seq_index+1))@(handle_list_find_set_seq str y level arr counter seq_num (seq_index+2)))






  let rec annotate_tail expr tp =
    match expr with
    | Const'(x) -> expr
    | Var'(x) -> expr
    | Or'(exprs) -> Or'(handle_list_tail exprs tp)
    | If'(test,dit,dif) -> If'((annotate_tail test false), (annotate_tail dit tp) , (annotate_tail dif tp))
    | Def'(x,expr) -> Def'(x, (annotate_tail expr false))
    | LambdaSimple'(args, body) -> LambdaSimple'(args,(annotate_tail body true) )
    | LambdaOpt'(args,arg ,body) -> LambdaOpt'(args,arg, (annotate_tail body true))
    | Applic'(proc,exprs) ->
          if(tp = true)
            then ApplicTP'((annotate_tail proc false),(handle_applic_tail exprs))
            else Applic'((annotate_tail proc false),(handle_applic_tail exprs))
    |Set'(x,expr) -> Set'(x,(annotate_tail expr false))
    |Seq'(exprs) -> Seq'(handle_list_tail exprs tp)
    |never -> Const'(Void)


    and handle_list_tail exprs tp =
    match exprs with
    |[] -> []
    |[x] -> [(annotate_tail x tp)]
    |x :: y -> (annotate_tail x false) :: (handle_list_tail y tp)

    and handle_applic_tail exprs =
    match exprs with
    |[] -> []
    |[x] -> [(annotate_tail x false)]
    |x :: y -> (annotate_tail x false) :: (handle_applic_tail y)



  let rec annotate_lexical e env=
    match e with
  | Const(exp) -> Const'(exp)
  | If(test,dit,dif) -> If'(annotate_lexical test env ,annotate_lexical dit env  ,annotate_lexical dif env)
  | Seq(exprs) -> Seq' (annotate_lex_list exprs env)
  | Set (Var(x), expr) -> Set'((handle_var x env), (annotate_lexical expr env))
  | Or (exprs) -> Or' (annotate_lex_list exprs env)
  | LambdaSimple (args, body) -> LambdaSimple' (args, (annotate_lexical  body (List.append env [args]) ))
  | LambdaOpt( args, arg, body) -> LambdaOpt' (args, arg,(annotate_lexical body (List.append env ([args@[arg]])) ))
  | Def(Var(x), expr2) -> Def'((handle_var x env), (annotate_lexical expr2 env))
  | Var(str) -> Var'(handle_var str env)
  | Applic(proc, args) -> Applic' ((annotate_lexical proc env), (annotate_lex_list args env))
  | other-> raise X_syntax_error





  and handle_var str args =
  let last_element = get_lest_elemnt args in
    if(List.mem str last_element) then
    (
      let index = get_index str last_element 0 in
      (VarParam(str,index))
    )
    else
    (
      let list_without_last = remove_last_element args in
      let (index1, index2) = get_index_list_list str list_without_last 0 in
      if(index1 = (-1))
        then (VarFree (str) )
        else (VarBound (str, index1, index2))
    )

    and get_index str args index =
      match args with
      |[] -> (-1)
      |[x] -> if (x = str) then index else -1
      |x :: y -> if (x = str) then index else get_index str y (index+1)

    and  get_lest_elemnt args =
        match args with
        |[] -> []
        |[x] -> x
        | h :: t -> get_lest_elemnt t

    and remove_last_element args =
    match args with
    |[] -> []
    |[x] -> []
    | h :: t -> h:: (remove_last_element t)

    and get_index_list_list str list_list curr=
      match list_list with
      | [] -> (-1,-1)
      | [x] -> if ((get_index str x 0 )=(-1)) then (-1,-1) else (curr,(get_index str x 0))
      | _ -> (
        let last= get_lest_elemnt list_list in
        if ((get_index str last 0 )=(-1))
          then (get_index_list_list str (remove_last_element list_list) (curr+1))
          else (curr, get_index str last 0)
      )



    and annotate_lex_list exprs env=
    match exprs with
    | [] -> []
    | [x]-> [(annotate_lexical x env)]
    | x::y -> (annotate_lexical x env):: (annotate_lex_list y env);;







let annotate_lexical_addresses e = annotate_lexical e [];;

let annotate_tail_calls e = annotate_tail e false;;

let box_set e = box_set_rec e;;

let run_semantics expr =
  box_set
    (annotate_tail_calls
       (annotate_lexical_addresses expr));;



end;; (* struct Semantics *)

 let [x]= Tag_Parser.tag_parse_expressions (Reader.read_sexprs "(letrec ((factorial (lambda (x)
 (if (= x 1) 1
    (* (factorial (+ x -1)) x)))))
(factorial 2)) ");;
 Semantics.run_semantics x;;
