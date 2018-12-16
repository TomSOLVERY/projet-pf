(* #load "dynlink.cma"  *)
(* #load "camlp4/camlp4o.cma"  *)
#use "topfind";;
#camlp4o;;
type oper2 = 
  | Moins
  | Plus
  | Multi
  | Div
  | Eg
  | Et
  | Ou

type oper3 = 
  | Non

type oper4 =
  | IfThenElse

type oper5 =
  | SoitDans

type ident = string
(*type var = ident * expr*)
  
type expr = 
  | Int of int
  | Bool of bool
  | Ident of ident
  | Op of oper2 * expr * expr
  | OpNon of oper3 * expr
  | OpIf of oper4 * expr * expr * expr
  | OpSD of oper5 * ident * expr * expr
          


(*type res =
  | Rint of int
  | Rbool of bool
 *)
type res_type =
  |Integer
  |Boolean 

type env = (ident*expr) list

let rec get id env =
  match env with
  |[] -> failwith "variable non trouvé dans l'environnement"
  |(ide, v)::ls -> if id = ide then v else get id ls

let rec eval e env =
  match e with
  | Int n -> Int n
  | Bool b -> Bool b
  | Ident x -> get x env
  | Op (Moins, x, y) -> (match (eval x env,eval y env) with
                        | (Int x, Int y) -> Int (x-y)
                        | _ -> failwith "Soustraction entre entiers seulement")                
  | Op (Plus, x, y) -> (match (eval x env,eval y env) with
                        | (Int x, Int y) -> Int (x+y)
                        | _ -> failwith "Addition entre entiers seulement")
  | Op (Multi, x, y) -> (match (eval x env,eval y env) with
                        |(Int x, Int y) -> Int (x*y)
                        |_ -> failwith "Multiplication entre entiers seulement")    
  | Op (Div, x, y) -> (match (eval x env,eval y env) with
                        |(Int x, Int y) -> if (y != 0) then Int (x/y) else failwith "Div par 0"
                        |_ -> failwith "Division entre entiers seulement")    
  | Op (Et, x, y) -> (match (eval x env,eval y env) with
                        |(Bool x, Bool y) -> Bool (x && y)
                        |_ -> failwith "Et entre booleens seulement")
  | Op (Ou, x, y) -> (match (eval x env,eval y env) with
                        |(Bool x, Bool y) -> Bool (x || y)
                        |_ -> failwith "Ou entre booleens seulement")
  | Op (Eg,x,y) -> (match (eval x env, eval y env) with
                      |(Int x, Int y) -> Bool (x = y)
                      |(Bool x, Bool y) -> Bool (x = y)
                      |_ -> failwith "Eg entre booleens ou entiers seulement")
  | OpNon (Non, x) ->  (match (eval x env) with
                    |(Bool x) -> Bool (not x)
                    |_ -> failwith "Non entre booleens seulement")
  | OpIf (IfThenElse,b,x,y) -> (match (eval b env, eval x env, eval y env) with
                                |(Bool b, Bool x, Bool y) -> if b then  Bool x  else Bool y 
                                |(Bool b, Int x, Int y) -> if b then Int x  else Int y 
                                |_ -> failwith "Probleme dans le If")
  | OpSD (SoitDans,id,exp,expIn) -> let x = (id, (eval exp env)) in eval expIn (x::env)


let rec eval_type e env =
  let x = eval e env in match x with
                        |Int(n) -> Integer
                        |Bool(n) -> Boolean
                        | _ -> failwith "Erreur dans l'evaluation"        

(* Impression avec toutes les parenthÃ¨ses explicites *)
let string_oper2 o =
  match o with
  | Moins -> " - "
  | Plus -> " + "
  | Multi -> " * "
  | Div -> " / "
  | Eg -> " = "
  | Et -> " && "
  | Ou -> " || "

let string_oper3 o =
  match o with
  | Non -> " not "

let rec print_expr e =
  match e with
  | Int n -> print_int n
  | Bool b -> print_string (string_of_bool b)
  | Ident x -> print_string x
  | Op (o, x, y) ->
     (print_char '(';
      print_expr x;
      print_string (string_oper2 o);
      print_expr y;
      print_char ')')
  | OpNon (b,x) ->
     (print_char '(';
      print_string (string_oper3 b);
      print_expr x;
      print_char ')')
  | OpIf (o,b,x,y) ->
    (print_char '(';
      print_string (" If ");
      print_expr b;
      print_string (" Then ");
      print_expr x;
      print_string (" Else ");
      print_expr y;
      print_char ')')
  | OpSD (o,i,e1,e2) ->
      (print_char '(';
      print_string (" Let ");
      print_string i;
      print_string (" = ");
      print_expr e1;
      print_string (" In ");
      print_expr e2;
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

let rec (parse_string : string -> char Stream.t -> string) = fun str ->
  parser
  |[<''a'..'z' | 'A'..'Z' | '0'..'9' as x; s>] -> String.make 1 x ^ (parse_string str s)
  |[< >] -> str ;;

(* Type des lexÃ¨mes *)
type token = 
  | Tent of int
  | Tbool of bool
  | Tident of string
  | Tmoins
  | Tplus
  | Tmulti
  | Tdiv        
  | Tet
  | Tou
  | Tnon
  | Teg
  | Tif
  | Tthen
  | Telse
  | Tlet
  | Tin
  | Touvert
  | Tferme


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
  | [< '  '=' >] -> Some(Teg)
  | [<''i';''f'>] -> Some(Tif)
  | [<''t';''h';''e';''n'>] -> Some(Tthen)
  | [<''e';''l';''s';''e'>] -> Some(Telse)
  | [<''s';''o';''i';''t'>] -> Some(Tlet)
  | [<''d';''a';''n';''s'>] -> Some(Tin)
  | [< id = parse_string "">] -> Some(Tident(id))
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
(*let s = Stream.of_string "45 - - 089"
let stk = lex s
let ltk = list_of_stream stk  *)

(*
Alternativement, la primitive Stream.from conduit au mÃªme rÃ©sultat,
on l'utilise comme ci-dessous.
*)

(*let lex s = Stream.from (fun _ -> next_token s)*)

(*
A savoir : cette derniÃ¨re version repose sur une reprÃ©sentation
interne des flots beaucoup plus efficace. Pour plus de dÃ©tails
sur Stream.from, consulter le manuel OCaml.
Dans un compilateur rÃ©aliste devant traiter de gros textes, 
c'est la version Ã  utiliser.
*)

(*let ltk1 = list_of_stream (lex (Stream.of_string "356 - 10 - 4"))*)

(* ANALYSEUR SYNTAXIQUE sur un flot de lexÃ¨mes *)

(* A noter : le passage d'un argument de type expr pour obtenir le
   bon parenthÃ¨sage de l'expression :
   41 - 20 - 1 est compris comme (41 - 20) - 1, non pas 41 - (20 - 1)
*)

let rec p_expr = parser
  |[<'Tif; b=p_expr; 'Tthen; x=p_expr; 'Telse; y=p_expr>] -> OpIf(IfThenElse,b,x,y)
  |[<'Tlet; 'Tident(id); 'Teg; e1=p_expr; 'Tin; e2=p_expr >] -> OpSD(SoitDans,id,e1,e2)
  | [< t = p_conjonction; e = p_s_disjonctions t >] -> e
and p_s_disjonctions a = parser
  | [< ' Tou; t = p_conjonction; e = p_s_disjonctions (Op(Ou,a,t)) >] -> e
  | [< >] -> a
and p_conjonction = parser
  | [<  t=p_litteral; e= p_s_conjonctions t >] -> e
and p_s_conjonctions a = parser
  | [< 'Tet; t = p_litteral; e = p_s_conjonctions (Op(Et,a,t)) >] -> e
  | [< >] -> a
and p_litteral = parser
  | [<' Tnon; e = p_litteral>] -> OpNon(Non,e)
  | [< t = p_expr_c; e = p_cmp t >] -> e
and p_cmp a = parser
  | [< ' Teg; t = p_expr_c >] -> Op(Eg,t,a)
  | [< >] -> a
and p_expr_c = parser
  | [< t = p_terme; e = p_s_add t >] -> e
and p_s_add a = parser
  | [< ' Tmoins; t = p_terme; e = p_s_add (Op(Moins,a,t)) >] -> e
  | [< ' Tplus; t = p_terme; e = p_s_add (Op(Plus,a,t)) >] -> e
  | [< >] -> a
and p_terme = parser
  | [<t = p_facteur; e=p_s_mul t>] -> e          
and p_s_mul a = parser
  | [< ' Tmulti; t = p_facteur; e = p_s_mul (Op(Multi,a,t)) >] -> e
  | [< ' Tdiv; t = p_facteur; e = p_s_mul (Op(Div,a,t)) >] -> e         
  | [< >] -> a
and p_facteur = parser 
  | [< ' Tent(n)>] -> Int(n)
  | [< ' Tbool(b)>] -> Bool(b)
  | [< ' Tident(id)>] -> Ident(id)
  | [<' Touvert;e = p_expr;' Tferme>] -> e


                                                          
  
                                                                   
  

let ast s = p_expr (lex (Stream.of_string s))


let e = ast "if vrai then 5 else faux"
let e1 = ast "if(5=5)then(if(vrai)then(4/2)else(4*2))else(50)"
let e2 = ast "soit x = 5 dans x + (soit x = 2 dans x * (soit x = 3 dans x)) - 3"
let e2l = ast "soit y = 2 dans (soit x = y + 5 dans (soit y = 1 dans x))"
let e3 = ast "soit x = (if (vrai) then 2 else 1000) dans (soit y = 3 dans (x + y))"
let t = eval_type e1 []
let x = eval e1 []
let y = print_expr e3
          
