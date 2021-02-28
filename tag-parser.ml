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
  val tag_parse_expressions : sexpr list -> expr list
end;; (* signature TAG_PARSER *)

module Tag_Parser : TAG_PARSER = struct
  let reserved_word_list =
    ["and"; "begin"; "cond"; "define"; "else";
     "if"; "lambda"; "let"; "let*"; "letrec"; "or";
     "quasiquote"; "quote"; "set!"; "pset!"; "unquote";
     "unquote-splicing"];;


  let rec check_lambda lst =
    match lst with
    |Nil->true
    |Pair(x,Nil) -> true
    |Pair(x,y) -> check_lambda(y)
    |_->false;;
  let rec tagVars args =
      match args with
      |Nil -> []
      |Pair(Symbol(x),y) -> x::(tagVars y)
      |never -> raise X_syntax_error;;

  let rec last_elemnt lst = match lst with
    | Pair(Symbol(x),Nil) -> x
    | Pair(x,y) -> last_elemnt y
    | Nil -> raise X_syntax_error
    |never -> raise X_syntax_error;;

  let rec last_elemnt_dotted lst = match lst with
    | Pair(x,Pair(y,z)) -> last_elemnt_dotted (Pair(y,z))
    | Pair(x,Symbol (y)) ->y
    |never -> raise X_syntax_error;;


  let rec get_all_but_last lst = match lst with
    |Pair (x,y)-> Pair(x,get_all_but_last y)
    |_-> Nil;;

  let rec func_on_pairs func pairs =
    match pairs with
    | Nil -> []
    | Pair(x,y) -> func (x) :: (func_on_pairs func y)
    |never -> raise X_syntax_error;;


  let rec func_on_pairs_flat_begin func pairs =
    match pairs with
    | Nil -> []
    | Pair(x,y) ->
        (let rest_parsed=func_on_pairs_flat_begin func y in
        match rest_parsed with
        |[Seq(exprs)]-> func(x)::exprs
        |exps-> func(x)::exps)
    |never -> raise X_syntax_error
  let rec get_vars bindings =
    match bindings with
    |Nil -> []
    |Pair(Pair(Symbol(x), Pair(y,Nil)),pairs) -> x::get_vars pairs
    |never -> raise X_syntax_error

  let rec get_vars_expr bindings =
      match bindings with
      |Nil -> Nil
      |Pair(Pair(x, Pair(y,Nil)),pairs) -> Pair(x,get_vars_expr pairs)
      |never -> raise X_syntax_error

  let rec make_binding_whatever vars =
    match vars with
    |Nil -> Nil
    |Pair(x,y) ->Pair (Pair(x,Pair (Pair (Symbol "quote", Pair (Symbol "whatever", Nil)),Nil)), make_binding_whatever y)
    |never -> raise X_syntax_error


  let rec make_sets vars vals =
    match vars,vals with
    |Nil,Nil -> Nil
    |Pair(x,Nil),Pair(a,Nil) ->(Pair (Symbol "set!", Pair ( x, Pair ( a, Nil))))
    |Pair(x,y),Pair(a,b) -> Pair (Pair (Symbol "set!", Pair ( x, Pair ( a, Nil))), make_sets y b)
    |never -> raise X_syntax_error


  let rec parse_tag sexp = match sexp with
  |Nil -> Const(Void)
  |Pair(Symbol("quasiquote"),Pair(sexp1,Nil))->parse_tag (parse_quasiquote sexp1)
  |Pair(Symbol("quote"), Pair(x, Nil)) -> Const(Sexpr(x))
  |Pair(Symbol("quote"), Nil) -> Const(Sexpr(Nil))
  |Number(x) -> Const(Sexpr(sexp))
  |Bool(x) -> Const(Sexpr(sexp))
  |Char(x) -> Const(Sexpr(sexp))
  |String(x) -> Const(Sexpr(sexp))
  |Pair(Symbol("cond"),ribs)-> parse_tag (parse_cond ribs)
  |Pair(Symbol("or"),args) -> parse_or args
  |Symbol(x) ->  if (List.exists (fun (u)->x=u) reserved_word_list) then raise X_syntax_error else Var(x)
  |Pair(Symbol("unquote"), Pair(Symbol(x), Nil)) -> if (List.exists (fun (u)->x=u) reserved_word_list) then raise X_syntax_error else Var(x)
  |Pair(Symbol("if"), Pair(test, Pair(dit, Pair(dif, Nil))))-> If(parse_tag test, parse_tag dit, parse_tag dif)
  |Pair(Symbol("if"), Pair(test, Pair(dit, Nil)))-> If(parse_tag test, parse_tag dit, Const(Void))
  |Pair(Symbol("lambda"), Pair(args,body)) -> parse_lambda args body
  |Pair(Symbol("let"), Pair(bindings,body)) -> parse_let bindings body
  |Pair(Symbol("let*"), Pair(bindings,body)) -> parse_tag (parse_let_star bindings body)
  |Pair(Symbol("letrec"), Pair(bindings,body)) -> parse_letrec_elad bindings body
  |Pair(Symbol("and"), exprs) -> parse_and exprs
  |Pair(Symbol("define"),Pair(Pair(name,vars),exprs)) -> parse_def_expand name vars exprs
  |Pair(Symbol("define"),Pair(name,Pair(exp,Nil))) -> Def (parse_tag name, parse_tag exp )
  |Pair(Symbol("set!"),Pair(exp1,Pair(exp2,Nil))) -> Set (parse_tag exp1, parse_tag exp2 )
  |Pair(Symbol("pset!"),pairs) -> parse_pset pairs
  |Pair(Symbol("begin"),exprs) -> parse_seq exprs
  |Pair(Symbol("unquote-splicing"), sexp) -> Const(Void)
  |Pair(procedure,args) -> parse_applic procedure args

  and parse_applic procedure args =
    let parse_args = func_on_pairs parse_tag args in
    Applic(parse_tag procedure,parse_args )

  and  get_vals bindings = match bindings with
    |Nil -> []
    |Pair(Pair(Symbol(x), Pair(y,Nil)),pairs) -> parse_tag y::get_vals pairs
    |never -> raise X_syntax_error

  and  get_vals_expr bindings = match bindings with
    |Nil -> Nil
    |Pair(Pair(Symbol(x), Pair(y,Nil)),pairs) -> Pair(y,get_vals_expr pairs)
    |never -> raise X_syntax_error




  and parse_let bindings body =
    let bindings_vars = get_vars bindings in
    let bindings_vals = get_vals bindings in
      Applic(LambdaSimple(bindings_vars,pars_body body),bindings_vals)


  and parse_let_star bindings body =
      match bindings with
      |Nil->  (Pair(Symbol("let"),Pair(Nil,body)))
      |Pair (rib, Nil)-> Pair(Symbol("let"), Pair(Pair(rib,Nil),body))
      |Pair(rib1,restRibs) -> Pair(Symbol ("let"), Pair(Pair(rib1,Nil),Pair(Pair(Symbol ("let*"),Pair(restRibs,body)),Nil)))
      |never -> raise X_syntax_error


  and parse_letrec_elad bindings body =
      let bindings_vars = get_vars_expr bindings in
      let new_bindings = make_binding_whatever bindings_vars in
      let bindings_vals = get_vals_expr bindings in
      let set_with_exprs = make_sets bindings_vars bindings_vals in
      let last_let = Pair (Symbol "let",Pair (Nil,body)) in
      let set_with_last_bind = make_set_with_let set_with_exprs last_let in
      let final = Pair (Symbol "let",Pair(new_bindings,set_with_last_bind)) in
      parse_tag final
and make_set_with_let sets last_let =
    match sets with
    |Pair(Symbol(x),_) ->Pair(sets,Pair(last_let,Nil))
    |Pair(setA,rest) -> Pair(setA,make_set_with_let rest last_let)
    |never -> raise X_syntax_error

  and parse_def_expand name args exprs =
    let la = (Pair(Symbol("lambda"),Pair(args,exprs))) in
    parse_tag (Pair(Symbol("define"),Pair(name,(Pair(la,Nil)))))


    and parse_pset pairs =
    let vars = get_vars pairs in
    let vals = get_vals_expr pairs in
   let vars_new_name = change_vars_name vars in
   let bindings = make_bindings vars_new_name vals in
    let sets= create_sets_for_pset vars vars_new_name in
     let final = Pair (Symbol "let",Pair(bindings,sets)) in
      parse_tag final

    and change_vars_name vars =
        if(vars = []) then []
        else
          (change_name ( List.hd vars) vars 1) ::  (change_vars_name (List.tl vars))


and change_name var vars number=
     let name = String.concat var [""; (string_of_int number)] in
    if ((List.exists (fun (u)-> name=u)  vars)) then
      (change_name var vars (number+1))
        else
    name


and make_bindings vars vals =
     match vals with
     | Pair(expr,Nil) ->Pair(Symbol(List.hd vars),Pair (expr,Nil))
    | (Pair(expr,rest)) ->Pair (Pair(Symbol(List.hd vars),Pair (expr,Nil)), make_bindings (List.tl vars) rest )
    |never -> raise X_syntax_error


and  create_sets_for_pset vars_name vars_new_name =
       match vars_name with
    |[] ->Nil
    |_ -> Pair (Pair (Symbol "set!", Pair ( Symbol(List.hd vars_name), Pair ( Symbol(List.hd vars_new_name), Nil))), create_sets_for_pset (List.tl vars_name) (List.tl vars_new_name) )

  and parse_and args =
    if(args = Nil) then Const(Sexpr(Bool(true)))
    else parse_tag (parse_test args)

  and parse_test args =
  match args with
      |Pair(exp1,Nil) -> exp1
      |Pair(exp1,exprs) ->
        Pair(Symbol("if"),Pair(exp1,Pair((parse_test exprs),Pair(Bool(false),Nil))))
      |never -> raise X_syntax_error


  and parse_cond ribs =
  match ribs with
  | Nil -> Nil
  |Pair(Pair(Symbol("else"),dits),_) ->(Pair(Symbol("begin"),dits))
  | Pair(Pair(test,Pair(Symbol("=>"),Pair(dit,Nil))),Nil) -> Pair (Symbol "let",Pair(Pair (Pair (Symbol "value", Pair (test, Nil)),                                                                                                    Pair
  (Pair (Symbol "f",
    Pair (Pair (Symbol "lambda", Pair (Nil, Pair (dit, Nil))),
     Nil)),
  Nil)),
Pair
(Pair (Symbol "if",
  Pair (Symbol "value",
   Pair (Pair (Pair (Symbol "f", Nil), Pair (Symbol "value", Nil)), Nil))),
Nil)))
  | Pair(Pair(test,Pair(Symbol("=>"),Pair(dit,Nil))),rest_ribs) ->
  Pair (Symbol "let",Pair(Pair (Pair (Symbol "value", Pair (test, Nil)),Pair
   (Pair (Symbol "f",Pair (Pair (Symbol "lambda", Pair (Nil, Pair (dit, Nil))),
      Nil)),
   Pair
    (Pair (Symbol "rest",
      Pair
       (Pair (Symbol "lambda", Pair (Nil, Pair (parse_cond rest_ribs, Nil))),
       Nil)),
    Nil))),
Pair
 (Pair (Symbol "if",
   Pair (Symbol "value",
    Pair (Pair (Pair (Symbol "f", Nil), Pair (Symbol "value", Nil)),
     Pair (Pair (Symbol "rest", Nil), Nil)))),
 Nil)))

|Pair(Pair(test,dit),rest_ribs) -> (Pair(Symbol("if"),Pair(test,Pair(Pair(Symbol("begin"),dit) ,Pair(parse_cond rest_ribs,Nil)))))
|never -> raise X_syntax_error



and parse_or args =
match args with
  |Nil -> Const(Sexpr(Bool(false)))
  |Pair(a,Nil) -> parse_tag a
  |args ->Or(func_on_pairs parse_tag args)
  and parse_seq exprs =
    match exprs with
    |Nil -> Const(Void)
    |Pair(exp,Nil) -> parse_tag exp
    |exprs -> Seq (func_on_pairs_flat_begin parse_tag exprs )

  and parse_lambda args body =
    if(check_lambda args) then
   LambdaSimple(tagVars args, pars_body body)
    else
    match args with
    |Symbol(x) -> LambdaOpt( [], x, (pars_body body))
    |_->LambdaOpt( tagVars(get_all_but_last args), (last_elemnt_dotted args), (pars_body body) )


  and parse_quasiquote sexp1 =
    match sexp1 with
  |Pair(Symbol("unquote"),Pair(sexp1,Nil)) ->sexp1
  |Pair(Symbol("unquote-splicing"),Pair(sexp1,Nil)) ->raise X_syntax_error
  |Nil-> Pair(Symbol("quote"), Pair(Nil,Nil))
  |Symbol(x)-> Pair(Symbol("quote"),Pair(Symbol(x), Nil))
  |Pair(sexpA,sexpB) ->
    (match sexpA, sexpB with
      |Pair(Symbol("unquote-splicing"),Pair(sexpA,Nil)), sexpB-> Pair(Symbol("append"),Pair(sexpA,Pair((parse_quasiquote sexpB),Nil)))
      |sexpA, Pair(Symbol("unquote-splicing"),Pair(sexpB,Nil)) -> Pair(Symbol("cons"),Pair((parse_quasiquote sexpA),Pair(sexpB,Nil)))
      |sexpA, sexpB -> Pair(Symbol("cons"),Pair((parse_quasiquote sexpA),Pair((parse_quasiquote sexpB),Nil))))
  |sexp1 -> sexp1


    and pars_body body=
    match body with
    |Pair(sexp,Nil)-> parse_tag sexp
    |Pair(sexp1,sexp2)->
                        (let rest_parsed=func_on_pairs_flat_begin parse_tag sexp2 in
                        match rest_parsed with
                        |[Seq(exprs)] -> Seq(parse_tag sexp1::exprs)
                        |[Seq(exprs1);exprs2] ->
                              let sexp1_sexps1= (parse_tag sexp1::exprs1)in
                              Seq (List.append sexp1_sexps1 [exprs2])
                        |exprs2 ->Seq(parse_tag sexp1::exprs2) )
    |never -> raise X_syntax_error


  let rec tag_parse_expressions_list sexpr = match sexpr with
    |[]->[]
    |car :: cdr -> (parse_tag car) ::(tag_parse_expressions_list cdr);;

let tag_parse_expressions sexpr = tag_parse_expressions_list sexpr;;

end;; (* struct Tag_Parser *)