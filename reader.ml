
#use "pc.ml";;
open PC;;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;

type number =
  | Fraction of int * int
  | Float of float;;

type sexpr =
  | Bool of bool
  | Nil
  | Number of number
  | Char of char
  | String of string
  | Symbol of string
  | Pair of sexpr * sexpr;;

let rec sexpr_eq s1 s2 =
  match s1, s2 with
  | Bool(b1), Bool(b2) -> b1 = b2
  | Nil, Nil -> true
  | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
  | Number(Fraction (n1, d1)), Number(Fraction (n2, d2)) -> n1 = n2 && d1 = d2
  | Char(c1), Char(c2) -> c1 = c2
  | String(s1), String(s2) -> s1 = s2
  | Symbol(s1), Symbol(s2) -> s1 = s2
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  | _ -> false;;

module Reader: sig
  val read_sexprs : string -> sexpr list
end
= struct
let normalize_scheme_symbol str =
  let s = string_to_list str in
  if (andmap
	(fun ch -> (ch = (lowercase_ascii ch)))
	s) then str
  else Printf.sprintf "|%s|" str;;


  let nt_whitespaces= star( const ( fun ch-> ch<=' '  ));;
  let nt_whitespace=  const ( fun ch-> ch<=' '  );;

  let nt_comments= char ';';;
  let nt_endLine= char '\n';;
  let nt_end = disj nt_endLine (pack nt_end_of_input (fun (_)->'i'));;
  let nt_all_but_n= star( const ( fun ch-> ch!='\n'));;
  let nt_all_but_geresh=( const ( fun ch-> ch!='\"'));;
  let nt_geresh=char '"';;


  let nt_ladder= char '#';;
  let nt_digit= range '0' '9';;
  let nt_singed_plus = char '+';;
  let nt_singed_minus = char '-';;
  let nt_signed= disj nt_singed_plus nt_singed_minus;;
  let nt_signed_maybe= maybe nt_signed;;
  let nt_a_z= range 'a' 'z';;
  let nt_A_Z= range 'A' 'Z';;
  let nt_punctuation= one_of "!$^*-_=+<>/?:";;
  let nt_dot= char '.';;

  let nt_sexp_comment = caten nt_ladder nt_comments;;

  let nt_not_follow= disj_list ([nt_a_z; nt_A_Z;nt_punctuation;nt_dot]);;
  let digits= (plus nt_digit ) ;;

  let nt_signed_digits=  caten nt_signed_maybe digits ;;
  let nt_slash =char  '/';;


  let nt_symbole= plus( disj_list [nt_digit;nt_a_z; nt_A_Z; nt_punctuation; nt_dot]);;
  let g =caten nt_signed_digits nt_dot;;
  let r = not_followed_by nt_signed_digits nt_not_follow
  let nt_float=   (caten(caten nt_signed_digits nt_dot) digits)  ;;
  let nt_fraction=  (caten(caten nt_signed_digits nt_slash) digits);;
  let nt_meta_char= caten (char '\\') (one_of "rtfn\\\"");;
  let parseComments= (caten(caten nt_comments nt_all_but_n)nt_end);;
  let nt_regular_slesh= char '\\';;
  let nt_char = caten nt_ladder nt_regular_slesh ;;
  let nt_nul = word_ci "nul";;
  let nt_newline = word_ci "newline";;
  let nt_return = word_ci "return";;
  let nt_page = word_ci "page";;
  let nt_tab = word_ci "tab";;
  let nt_space = word_ci "space";;
  let nt_named_chars= caten nt_char (disj_list ([nt_nul; nt_newline; nt_return; nt_page; nt_tab; nt_space]));;
  let nt_visible_char = caten nt_char (const ( fun ch-> ch>'\032')) ;;
  let nt_nil= caten (char '(') (char ')');;
  let nt_e= char_ci 'e';;
  let nt_scintific_float= caten (caten nt_float nt_e) nt_signed_digits;;
  let nt_scintific_integer= caten (caten nt_signed_digits nt_e) nt_signed_digits;;
  let nt_check = not_followed_by nt_signed_digits nt_ladder;;

  let nt_quoted= char '\039';;
  let nt_qquoted= char '`';;
  let nt_unquoted= char ',';;

  let nt_unquotedSliced= caten nt_unquoted (char '@');;

  let nt_quoteLike= disj_list([nt_quoted; nt_unquoted; nt_qquoted]);;

  let tok_comment=
    pack parseComments
    (fun (_)->());;
  let tok_sci_integer=
    pack (not_followed_by nt_scintific_integer nt_not_follow)
    (fun (((sign1,lst1),_),(sign2,lst2))->
     let num1= float_of_string(list_to_string lst1) in
     let num2= float_of_string(list_to_string lst2) in
    match (sign1,sign2) with
      |(Some '-',Some '-')->Number ( Float ( (num1 *. (-1.0)) *. (10.0 **(num2 *. (-1.0)))))
      |(Some '+',Some '-')->Number ( Float ( (num1) *. (10.0 **(num2 *. (-1.0)))))
      |(Some '-',Some '+')->Number ( Float ( (num1 *. (-1.0)) *. (10.0 **(num2))))
      |(Some '+',Some '+')->Number ( Float ( (num1 ) *. (10.0 **(num2 ))))
      |(Some '-',None)->Number ( Float ( (num1 *. (-1.0)) *. (10.0 **(num2))))
      |(Some '+',None)->Number ( Float ( (num1 ) *. (10.0 **(num2 ))))
      |(None,Some '+')->Number ( Float ( (num1 ) *. (10.0 **(num2 ))))
      |(None,Some '-')->Number ( Float ( (num1) *. (10.0 **(num2 *. (-1.0)))))
      |(None,None)->Number ( Float ( (num1 ) *. (10.0 **(num2 ))))
      | never -> raise X_no_match
    );;
    let tok_sci_float=
      pack (not_followed_by nt_scintific_float nt_not_follow)
      (fun (((((sign1,lst1),_),lst2),_),(sign2,lst3))->
        let left =list_to_string lst1 in
        let middle =list_to_string lst2 in
        let right =(list_to_string lst3) in
      match (sign1,sign2) with
        |(Some '-',Some '-')->Number ( Float (float_of_string ("-"^left^"."^middle^"e"^"-"^right )) )
        |(Some '+',Some '-')->Number ( Float ( float_of_string (left^"."^middle^"e"^"-"^right )))
        |(Some '-',Some '+')->Number ( Float (float_of_string ("-"^left^"."^middle^"e"^right ))  )
        |(Some '+',Some '+')->Number ( Float ( float_of_string (left^"."^middle^"e"^right ))  )
        |(Some '-',None)->Number ( Float ( float_of_string ("-"^left^"."^middle^"e"^right )))
        |(Some '+',None)->Number ( Float ( float_of_string (left^"."^middle^"e"^right )))
        |(None,Some '+')->Number ( Float ( float_of_string (left^"."^middle^"e"^right )))
        |(None,Some '-')->Number ( Float (float_of_string (left^"."^middle^"e"^"-"^right )))
        |(None,None)->Number ( Float ( float_of_string (left^"."^middle^"e"^right )))
        | never -> raise X_no_match
      );;
  let tok_nil=
    pack nt_nil
    (fun (ch)-> Nil);;

  let list_to_lower_string s =
      String.concat "" (List.map (fun ch -> String.make 1 (lowercase_ascii ch)) s);;
  let tok_named_char =
    pack nt_named_chars
    (fun ((_,_),ch) ->
    let stringed= list_to_lower_string ch in
    match stringed with
    |"nul"-> Char '\000'
    |"newline"-> Char '\010'
    |"return"-> Char '\013'
    |"tab" -> Char '\009'
    |"page" -> Char '\012'
    |"space"-> Char '\032'
    | never -> raise X_no_match
    );;

  let tok_visible_char=
    pack nt_visible_char
    (fun ((_,_),ch)->
      Char ch
    );;



  let tok_true =
    let nt_true= (char_ci 't') in
    let parseTrue =(caten nt_ladder nt_true ) in
    pack parseTrue (fun (ds) -> Bool true);;

  let tok_false =
    let nt_false= (char_ci 'f') in
    let parseFalse =(caten nt_ladder nt_false) in
    pack parseFalse (fun (ds) -> Bool false);;

  let tok_boolean = disj tok_false tok_true;;
  let tok_num=
    pack (not_followed_by nt_signed_digits nt_not_follow)
     (fun (signed,ds) ->
     let value = ((int_of_string(list_to_string ds))) in
     if(signed=Some('-')) then Number(Fraction ( value* (-1) ,1))
     else Number(Fraction (value ,1)));;

  let tok_float=
    pack (not_followed_by nt_float nt_not_follow)
    (fun (((signed,left),dot), right)->
     if(signed=Some('-')) then Number(Float (float_of_string ("-"^(list_to_string left)^"."^( list_to_string right))) )
      else Number(Float (float_of_string ((list_to_string left)^"."^(list_to_string right)))));;


  let rec gcd nominator denomerator =
    if denomerator = 0 then nominator
    else gcd denomerator (nominator mod denomerator);;
  let tok_fraction=
    pack (not_followed_by nt_fraction nt_not_follow)
    (fun (((signed,left),_), right)->
      let denominator= (int_of_string(list_to_string(right))) in
      let numerator= (int_of_string(list_to_string(left))) in
      let gcd_num = gcd numerator denominator in
      if(signed=Some('-')) then Number(Fraction ((numerator  * -1)/gcd_num, denominator/gcd_num))
      else Number(Fraction (numerator/gcd_num,denominator/gcd_num )));;

  let tok_symbole=
    pack nt_symbole
    (fun (lst)->
      let str= list_to_string lst in
      if((str = ".") ) then  raise X_no_match else
     Symbol(list_to_lower_string (string_to_list str))
    );;


    let nt_inside_chars =
      let fix= pack nt_meta_char
      (fun (_,ch)-> match ch with
      | '\\' -> '\\'
      | 'f' -> '\012'
      | 'r' -> '\r'
      | 'n' -> '\n'
      | 't' -> '\t'
      | '"' -> '\"'
      | never -> raise X_no_match) in
      star (disj fix nt_all_but_geresh);;
    let nt_all_chars = caten (caten nt_geresh nt_inside_chars) nt_geresh ;;
    let make_paired nt_left nt_right nt =
      let nt = caten nt_left nt in
      let nt = pack nt (function (_, e) -> e) in
      let nt = caten nt nt_right in
      let nt = pack nt (function (e, _) -> e) in
      nt;;
    let make_spaced nt =
       make_paired nt_whitespaces nt_whitespaces nt;;

    let clean_comment nt =
        make_paired parseComments parseComments nt;;

    let space_comment nt = disj (make_spaced nt) (clean_comment nt);;

    let tok_string=
      pack nt_all_chars
      (fun ((_,lst),_)->
      String (list_to_string lst));;


  let tok_atomic= ( disj_list([tok_sci_integer; tok_sci_float;tok_nil;tok_named_char;tok_visible_char; tok_boolean
            ; tok_fraction;tok_float; tok_string;tok_num;tok_symbole ]));;

  let tok_lparen =  ( char '(');;

  let tok_rparen =  ( char ')');;
  let tok_dot_paren =(char '.');;
   let nt_dot2= word " . ";;





  let rec nt_main_sexpr s =
     (clean (disj_list[tok_atomic;nt_dotted_list;nt_list;nt_quoted_sexpr;nt_unquotedSliced_sexpr; nt_nil])) s

    and nt_dotted_list s=
    let dotted_list_sexpr= (caten tok_lparen (caten (plus nt_main_sexpr) (caten tok_dot_paren (caten nt_main_sexpr tok_rparen)))) in
    let packed_dotted_list_sexpr= pack dotted_list_sexpr
      (fun (l,(sexp1,(dot,(sexp2,r))))-> List.fold_right (fun e1 e2-> Pair (e1, e2)) sexp1 sexp2) in
    packed_dotted_list_sexpr s
    and nt_list s=
      let list_sexpr= caten (caten tok_lparen (star nt_main_sexpr)) tok_rparen in
      let packed_list_sexpr= pack list_sexpr
        (fun ((_,e),_)-> match e with
        | []-> Nil
        | sexp_list->  List.fold_right (fun e1 e2-> Pair (e1, e2)) sexp_list Nil
         )in
      packed_list_sexpr s

    and nt_quoted_sexpr s=
      let quoted = caten nt_quoteLike nt_main_sexpr in
      let packed_quoted_sexpr = pack quoted
      (fun (q,sexp)-> match q with
      |'\039'-> Pair(Symbol("quote"),Pair(sexp,Nil))
      |'`'-> Pair(Symbol("quasiquote"),Pair(sexp,Nil))
      |','-> Pair(Symbol("unquote"),Pair(sexp,Nil))
      | never -> raise X_no_match)
        in
      packed_quoted_sexpr s

    and nt_unquotedSliced_sexpr s=
      let unquotedSliced= caten nt_unquotedSliced nt_main_sexpr in
      let packed_unquotedSliced=pack unquotedSliced
        (fun (_,sexp)-> Pair (Symbol("unquote-splicing"),Pair(sexp,Nil)))in
        packed_unquotedSliced s


    and nt_sexp_comments s =
      let tok_sexp_comment = (caten nt_sexp_comment nt_main_sexpr)  in
      let packed_tok_sexp_comment =pack tok_sexp_comment
      (fun (_)->Nil )in
      packed_tok_sexp_comment s

    and clean s =
      let whitespaces=(pack nt_whitespace (fun (_) -> Nil)) in
      let comments= (pack parseComments (fun (_) -> Nil)) in
      let whitespace_or_comment = disj_list [whitespaces; comments;nt_sexp_comments] in
      let nt1 nt = make_paired (star whitespace_or_comment) (star whitespace_or_comment) nt in
      nt1 s

    and nt_nil s=
      let whitespaces=(pack  nt_whitespace (fun (_) -> Nil)) in
      let comments= (pack  parseComments (fun (_) -> Nil)) in
      let whitespace_or_comment = disj_list [whitespaces; comments;nt_sexp_comments] in
      let nil= caten (caten (char '(') (star whitespace_or_comment)) (char ')') in
      let packed_nil= pack nil (fun (_)-> Nil) in
      packed_nil s;;


let read_sexprs string =
  let stared = star nt_main_sexpr  in
  let (l,r)=stared (string_to_list string) in
  l;;


end;; (* struct Reader *)