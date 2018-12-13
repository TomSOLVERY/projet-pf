(* #load "dynlink.cma"  *)
(* #load "camlp4/camlp4o.cma"  *)
#use "topfind";;
#camlp4o;;

type oper2 = 
  | Moins
  | Plus
  | Multi
  | Div
  
type oper3 =
  | Et
  | Ou

type oper4 = 
  | Non

type expr = 
  | Int of int
  | Op2 of oper2 * expr * expr

type expr_bool =
  | Bool of bool
  | OpBool1 of oper3 * expr_bool * expr_bool
  | OpBool2 of oper4 * expr_bool



let rec eval e =
  match e with
  | Int n -> n
  | Op2 (Moins, x, y) -> eval x - eval y
  | Op2 (Plus, x, y) -> eval x + eval y
  | Op2 (Multi, x, y) -> eval x * eval y
  | Op2 (Div, x, y) -> eval x / eval y

let rec eval_bool e =
  match e with
  | Bool b -> b
  | OpBool1 (Et, x, y) -> eval_bool x && eval_bool y
  | OpBool1 (Ou, x, y) -> eval_bool x || eval_bool y
  | OpBool2 (Non, x) ->  not (eval_bool x)

(* Impression avec toutes les parenthÃ¨ses explicites *)
let string_oper2 o =
  match o with
  | Moins -> "-"
  | Plus -> "+"
  | Multi -> "*"
  | Div -> "/"

let string_oper3 o =
  match o with
  | Et -> "&&"
  | Ou -> "||"

let string_oper4 o =
  match o with
  | Non -> " not "

let rec print_expr e =
  match e with
  | Int n -> print_int n
  | Op2 (o, x, y) ->
     (print_char '(';
      print_expr x;
      print_string (string_oper2 o);
      print_expr y;
      print_char ')')

let rec print_expr_bool e =
  match e with
  |Bool b -> print_string (string_of_bool b)
  |OpBool1 (b,x,y) ->
   (print_char '(';
      print_expr_bool x;
      print_string (string_oper3 b);
      print_expr_bool y;
      print_char ')')
  |OpBool2 (b,x) ->
    (print_char '(';
      print_string (string_oper4 b);
      print_expr_bool x;
      print_char ')')

    
(* FLOTS *)

(* Pour le test *)
let rec list_of_stream = parser
  | [< 'x; l = list_of_stream >] -> x :: l
  | [< >] -> []

(* ANALYSEUR LEXICAL sur un flot de caractÃ¨res *)
	      
(* SchÃ©ma de Horner *)
let valchiffre c = int_of_char c - int_of_char '0'
let rec horner n = parser 
  | [< '  '0'..'9' as c; s >] -> horner (10 * n + valchiffre c) s
  | [< >] -> n

(* test *)
let _ = horner 0 (Stream.of_string "45089")

(* Type des lexÃ¨mes *)
type token = 
  | Tent of int
  | Tbool of bool
  | Tet
  | Tou
  | Tnon
  | Tmoins
  | Tplus
  | Touvert
  | Tferme
  | Tmulti
  | Tdiv

(* 
Pour passer d'un flot de caractÃ¨res Ã  un flot de lexÃ¨mes,
on commence par une fonction qui analyse lexicalement les
caractÃ¨res d'un lexÃ¨me au dÃ©but d'un flot de caractÃ¨res.
La fonction next_token rend un token option, c'est-Ã -dire :
- soit Some (tk)   oÃ¹ tk est un token
  dans le cas oÃ¹ le dÃ©but du flot correspond lexÃ¨me
- soit None

Le type option est prÃ©dÃ©fini ainsi dans la bibliothÃ¨que standard OCaml :
type 'a option =
  | None           (* indique l'absence de valeur *)
  | Some of 'a     (* indique la prÃ©sence de valeur *)
*)
      
let rec next_token = parser
  | [< '  ' '|'\n'; tk = next_token >] -> tk (* Ã©limination des espaces *)
  | [< '  '0'..'9' as c; n = horner (valchiffre c) >] -> Some (Tent (n))
  | [<''v';''r';''a';''i'>] -> Some(Tbool(true))
  | [<''f';''a';''u';''x'>] -> Some(Tbool(false))
  | [<''&';''&'>] -> Some(Tet)
  | [<''|';''|'>] -> Some(Tou)
  | [<''n';''o';''n'>] -> Some(Tnon)
  | [< '  '-' >] -> Some (Tmoins)
  | [< '  '+' >] -> Some(Tplus)
  | [< '  '(' >] -> Some(Touvert)
  | [< '  ')' >] -> Some(Tferme)
  | [< '  '*' >] -> Some(Tmulti)
  | [< '  '/' >] -> Some(Tdiv)
  | [< >] -> None

(* tests *)
let s = Stream.of_string "45 - - 089"
let tk1 = next_token s
let tk2 = next_token s
let tk3 = next_token s
let tk4 = next_token s
let tk5 = next_token s
let tk6 = next_token s

(* L'analyseur lexical parcourt rÃ©cursivement le flot de caractÃ¨res s
   en produisant un flot de lexÃ¨mes *)
let rec tokens s =
  match next_token s with
  | None -> [< >]
  | Some tk -> [< 'tk; tokens s >]

let lex s = tokens s

(* tests *)
let s = Stream.of_string "45 - - 089"
let stk = lex s
let ltk = list_of_stream stk  

(*
Alternativement, la primitive Stream.from conduit au mÃªme rÃ©sultat,
on l'utilise comme ci-dessous.
*)

let lex s = Stream.from (fun _ -> next_token s)

(*
A savoir : cette derniÃ¨re version repose sur une reprÃ©sentation
interne des flots beaucoup plus efficace. Pour plus de dÃ©tails
sur Stream.from, consulter le manuel OCaml.
Dans un compilateur rÃ©aliste devant traiter de gros textes, 
c'est la version Ã  utiliser.
*)

let ltk1 = list_of_stream (lex (Stream.of_string "356 - 10 - 4"))

(* ANALYSEUR SYNTAXIQUE sur un flot de lexÃ¨mes *)

(* A noter : le passage d'un argument de type expr pour obtenir le
   bon parenthÃ¨sage de l'expression :
   41 - 20 - 1 est compris comme (41 - 20) - 1, non pas 41 - (20 - 1)
*)

let rec p_expr = parser
  | [< t = p_terme; e = p_s_add t >] -> e
and p_s_add a = parser 
  | [< ' Tmoins; t = p_terme; e = p_s_add (Op2(Moins,a,t)) >] -> e
  | [< ' Tplus; t = p_terme; e = p_s_add (Op2(Plus,a,t)) >] -> e
  | [< >] -> a

and p_terme = parser
  | [<t = p_facteur; e=p_s_mul t>] -> e
           
and p_s_mul a = parser
  | [< ' Tmulti; t = p_terme; e = p_s_mul (Op2(Multi,a,t)) >] -> e
  | [< ' Tdiv; t = p_terme; e = p_s_mul (Op2(Div,a,t)) >] -> e                                                                                                                  
  | [< >] -> a
           
and p_facteur = parser 
  | [< ' Tent(n)>] -> Int(n)
  | [< ' Touvert; t = p_expr;' Tferme>] -> t
                                         
let rec p_expr_bool = parser
                | [< t = p_conjonction; e = p_s_disjonctions t >] -> e

and p_s_disjonctions a = parser
                       | [< ' Tou; t = p_conjonction; e = p_s_disjonctions (OpBool1(Ou,a,t)) >] -> e
                       | [< >] -> a
                                
and p_conjonction = parser
                  | [<  t=p_litteral; e= p_s_conjonctions t >] -> e
                                                                 
and p_s_conjonctions a = parser
                       | [< 'Tet; t = p_litteral; e = p_s_conjonctions (OpBool1(Et,a,t)) >] -> e
                       | [< >] -> a
                                
and p_litteral = parser
                 | [<' Tnon; e = p_litteral>] -> OpBool2(Non,e)
                 | [<' Tbool(b)>] -> Bool(b)
                 | [<' Touvert;e = p_expr_bool;' Tferme>] -> e
                                                          
  
                                                                   
  

let ast s = p_expr (lex (Stream.of_string s))
let ast_bool s = p_expr_bool (lex (Stream.of_string s))
          

let e1 = ast_bool " (faux && non faux) || (faux || non vrai)"     
let x = eval_bool e1
let y = print_expr_bool e1
          
