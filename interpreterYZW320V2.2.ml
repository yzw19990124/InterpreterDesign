(* Interpreter assignment for CS320F20
   Author: Yanzheng Wu
   Email: sw1999@bu.edu
   Date: 12/06/2020
*)

(*************************************************************************************************)
(* HELPER FUNCTIONS *)
(*************************************************************************************************)

let explode (s : string) : char list =
  let rec expl i l = if i < 0 then l else expl (i - 1) (s.[i] :: l) in
  expl (String.length s - 1) []

let implode (cl : char list) : string =
  String.concat "" (List.map (String.make 1) cl)

let rec input_lines inp =
  try
    let ln = input_line inp in
    ln :: input_lines inp
  with End_of_file -> []

let input_string inp = inp |> input_lines |> String.concat "\n"

let is_alpha = function 'a' .. 'z' | 'A' .. 'Z' -> true | _ -> false

let is_digit = function '0' .. '9' -> true | _ -> false

let flip = Fun.flip

let ( %> ) f g x = g (f x)

let ( % ) f g x = f (g x)

(* Parser Combinator *)

type 'a parser = Parser of (string -> ('a * string) list)

let runParser (Parser f : 'a parser) (inp : string) = f inp

let return (a : 'a) : 'a parser = Parser (fun inp -> [ (a, inp) ])

let fail : 'a parser = Parser (fun _ -> [])

let ( <|> ) (p : 'a parser) (q : 'a parser) : 'a parser =
  Parser
    (fun inp -> match runParser p inp with [] -> runParser q inp | d -> d)

let ( >>= ) (p : 'a parser) (f : 'a -> 'b parser) : 'b parser =
  Parser
    (fun inp ->
      match runParser p inp with
      | [] -> []
      | (v, out) :: _ -> runParser (f v) out)

let ( let* ) = ( >>= )

let ( >> ) p q = p >>= fun _ -> q

let ( |>> ) p f = p >>= fun x -> return (f x)

let ( <$> ) p q =
  p >>= fun vp ->
  q |>> fun vq -> (vp, vq)

let ( $> ) p q = p <$> q |>> snd

let ( <$ ) p q = p <$> q |>> fst

let opt p = p |>> (fun x -> Some x) <|> return None

let read : char parser =
  Parser
    (fun cs ->
      match explode cs with c :: cs -> [ (c, implode cs) ] | [] -> [])

(* Read the string and return all the characters until n *)
let rec readn (n : int) : string parser =
  if n > 0 then
    let* c = read in
    let* cs = readn (n - 1) in
    return (String.make 1 c ^ cs)
  else return ""

let rec many (p : 'a parser) : 'a list parser =
  (let* a = p in
   let* ls = many p in
   return (a :: ls))
  <|> return []

let many1 (p : 'a parser) : 'a list parser =
  let* a = p in
  let* ls = many p in
  return (a :: ls)

let sepby1 p sep = p <$> many (sep $> p) |>> fun (p, ps) -> p :: ps

let string_p (str : string) : string parser =
  let len = String.length str in
  readn len >>= fun x -> if str = x then return x else fail

let sat f = read >>= fun x -> if f x then return x else fail

let digit_p = sat is_digit

let letter_p = sat is_alpha

let char_p x = sat (fun y -> y = x)

let nat_p = many1 digit_p |>> fun xs -> int_of_string (implode xs)

let int_p =
  opt (char_p '-') <$> nat_p |>> fun (sign, n) ->
  match sign with Some _ -> -n | _ -> n

let whitespace_p = char_p ' ' <|> char_p '\n' <|> char_p '\t' <|> char_p '\r'

let ws = many whitespace_p

let string_return str ret = ws >> string_p str >> return ret

let ws_string_p s = ws >> string_p s

let ascii_p =
  sat (fun x ->
      x <> '\n' && x <> '"' && x |> int_of_char |> fun y -> y >= 0 && y <= 0x7f)

let choice parsers = List.fold_left ( <|> ) (List.hd parsers) (List.tl parsers)

(* port from fparsec *)
let create_parser_forwarded_to_ref () =
  let dummy_parser =
    Parser
      (fun _ ->
        failwith
          "a parser created with createParserForwardedToRef was not initialized")
  in
  let r = ref dummy_parser in
  (Parser (fun x -> runParser !r x), r)

(*************************************************************************************************)
(* INTERPRETER FUNCTION *)
(*************************************************************************************************)

type stackvalue =
  | S of string
  | N of string
  | I of int
  | B of bool
  | Unit
  | Error
  | Closure of string * commands * (string * stackvalue) list

and command =
  | Push of stackvalue
  | Pop
  | Add
  | Sub
  | Mul
  | Div
  | Rem
  | Neg
  | Swap
  | Quit
  | And
  | Or
  | Not
  | Lte
  | Lt
  | Gte
  | Gt
  | Eq
  | Cat
  | Bnd
  | BeginExpr of commands
  | IfExpr of commands * commands * commands
  | Fun' of string * string * commands
  | Call
  | Return
  | TryExpr of commands * commands

and commands = command list

type stack = stackvalue list

let rec env_to_s env =
  env
  |> List.map (fun (n, v) -> Printf.sprintf "%s -> %s" n (stackvalue_to_s v))
  |> String.concat "\n"

and stackvalue_to_s = function
  | Unit -> "<unit>"
  | Error -> "<error>"
  | S s | N s -> s
  | B b -> "<" ^ string_of_bool b ^ ">"
  | I i -> string_of_int i
  | Closure (arg, _, _) -> "<closure> " ^ arg

let stack_to_s st = st |> List.map stackvalue_to_s |> String.concat "\n"

let rec commands_to_s ?(i = 0) xs =
  List.map (command_to_s ~i) xs |> String.concat "\n"

and command_to_s ?(i = 0) c =
  let indent = String.make i ' ' in
  ( match c with
  | Push v -> "Push " ^ stackvalue_to_s v
  | Pop -> "Pop"
  | Add -> "Add"
  | Sub -> "Sub"
  | Mul -> "Mul"
  | Div -> "Div"
  | Rem -> "Rem"
  | Neg -> "Neg"
  | Swap -> "Swap"
  | Quit -> "Quit"
  | And -> "And"
  | Or -> "Or"
  | Not -> "Not"
  | Lte -> "Lte"
  | Lt -> "Lt"
  | Gte -> "Gte"
  | Gt -> "Gt"
  | Eq -> "Eq"
  | Cat -> "Cat"
  | Bnd -> "Bnd"
  | Return -> "Return"
  | Call -> "Call"
  | BeginExpr xs -> "Begin\n" ^ commands_to_s ~i:(i + 2) xs
  | IfExpr (e1, e2, e3) ->
      "If\n"
      ^ commands_to_s ~i:(i + 2) e1
      ^ "\n" ^ indent ^ "Then\n"
      ^ commands_to_s ~i:(i + 2) e2
      ^ "\n" ^ indent ^ "Else\n"
      ^ commands_to_s ~i:(i + 2) e3
      ^ "\n" ^ indent ^ "EndIf"
  | Fun' (name, arg, e) ->
      "Fun " ^ name ^ " " ^ arg ^ "\n"
      ^ commands_to_s ~i:(i + 2) e
      ^ "\n" ^ indent ^ "EndFun"
  | TryExpr (e1, e2) ->
      "Try\n"
      ^ commands_to_s ~i:(i + 2) e1
      ^ "\n" ^ indent ^ "With\n"
      ^ commands_to_s ~i:(i + 2) e2 )
  |> fun x -> indent ^ x

let command_p, command_p_ref = create_parser_forwarded_to_ref ()

let const_int = int_p |>> fun x -> I x

let const_bool =
  char_p '<' $> (string_p "true" <|> string_p "false") <$ char_p '>'
  |>> fun x -> B (bool_of_string x)

let const_string =
  char_p '"' $> (many1 ascii_p |>> implode |>> fun x -> S x) <$ char_p '"'

let const_name =
  many (char_p '_') <$> many1 (letter_p <|> digit_p <|> char_p '_')
  |>> fun (a, b) ->
  a @ b |> implode |> fun x -> N x

let const_unit = string_return "<unit>" Unit

let const_error = string_return "<error>" Error

let push : command parser =
  ws >> string_p "Push" >> ws
  >> ( const_int <|> const_bool <|> const_string <|> const_name <|> const_unit
     <|> const_error )
  |>> fun x -> Push x

let pop = string_return "Pop" Pop

let add = string_return "Add" Add

let sub = string_return "Sub" Sub

let mul = string_return "Mul" Mul

let div = string_return "Div" Div

let rem = string_return "Rem" Rem

let neg = string_return "Neg" Neg

let swap = string_return "Swap" Swap

let quit = string_return "Quit" Quit

let cat' = string_return "Cat" Cat

let and' = string_return "And" And

let or' = string_return "Or" Or

let not' = string_return "Not" Not

let eq' = string_return "Eq" Eq

let lte' = string_return "Lte" Lte

let lt' = string_return "Lt" Lt

let gte' = string_return "Gte" Gte

let gt' = string_return "Gt" Gt

let bnd' = string_return "Bnd" Bnd

let call' = string_return "Call" Call

let return' = string_return "Return" Return

let commands_p : commands parser = ws >> sepby1 command_p ws

let if' =
  ws >> string_p "If" $> commands_p
  <$ (ws >> string_p "Then")
  <$> commands_p
  <$ (ws >> string_p "Else")
  <$> commands_p
  <$ (ws >> string_p "EndIf")
  |>> fun ((e1, e2), e3) -> IfExpr (e1, e2, e3)

let fun' =
  ws >> string_p "Fun" $> (ws >> const_name) <$> (ws >> const_name)
  <$> commands_p
  <$ (ws >> string_p "EndFun")
  >>= function
  | (N name, N arg), block -> return (Fun' (name, arg, block))
  | _ -> failwith "Should not be reachable"

let try' =
  ws >> string_p "Try" $> commands_p
  <$ (ws >> string_p "With")
  <$> commands_p
  <$ (ws >> string_p "EndTry")
  |>> fun (block1, block2) -> TryExpr (block1, block2)

let begin' =
  ws >> string_p "Begin" $> commands_p <$ (ws >> string_p "End") |>> fun x ->
  BeginExpr x

let () =
  command_p_ref :=
    ws
    >> choice
         [
           push;
           swap;
           pop;
           add;
           sub;
           mul;
           div;
           rem;
           neg;
           and';
           or';
           not';
           lte';
           lt';
           gte';
           gt';
           eq';
           cat';
           bnd';
           begin';
           if';
           fun';
           call';
           return';
           try';
           quit;
         ]

let prog_p = commands_p

let parse str = runParser prog_p str |> List.map fst |> List.flatten

let parse_channel channel = input_string channel |> fun inp -> (inp, parse inp)

let parse_file (f : string) = f |> open_in |> parse_channel

let rec apply2 op a b q =
  try
    let g a' b' = apply2 op a' b' q in
    match (a, b) with
    | I _, I _ | B _, B _ | S _, S _ -> op a b
    | N x, N y -> g (q x) (q y)
    | _, N y -> g a (q y)
    | N x, _ -> g (q x) b
    | _ -> None
  with
  | Not_found -> None
  | Division_by_zero -> None

let rec apply1 op a q =
  try
    match a with
    | I _ | B _ | S _ -> op a
    | N x -> apply1 op (q x) q
    | _ -> None
  with Not_found -> None

let map_i2 f a b =
  match (a, b) with I x, I y -> f x y |> Option.some | _ -> None

let map_b2 f a b =
  match (a, b) with B x, B y -> f x y |> Option.some | _ -> None

let map_s2 f a b =
  match (a, b) with S x, S y -> f x y |> Option.some | _ -> None

let map_i1 f = function I x -> f x |> Option.some | _ -> None

let map_b1 f = function B x -> f x |> Option.some | _ -> None

let is_debug = ref false

let is_quit = ref false

let is_fuck = ref false

let is_try = ref []

let rec eval coms st env : stack =
  let div_line () = print_endline @@ String.make 16 '-' in
  if !is_debug then (
    print_endline "commands:";
    coms |> commands_to_s |> print_endline;
    div_line ();
    print_endline "env:";
    if !is_try <> [] then print_endline "in try";
    if !is_quit then print_endline "in quit";
    print_endline @@ env_to_s env;
    div_line ();
    print_endline "stack:";
    st |> stack_to_s |> print_endline;
    print_endline "" );

  if coms = [] || !is_quit then st
  else
    let eval' st' = eval (List.tl coms) st' env in
    let q = flip List.assoc env in
    let q' = function N n -> q n | x -> x in
    let error () =
      match !is_try with [] -> eval' (Error :: st) | _ -> Error :: st
    in
    let or_error f opt =
      match opt with Some v -> eval' (f v) | _ -> error ()
    in
    match (coms, st) with
    | Quit :: _, _ ->
        is_quit := true;
        st
    | Push v :: _, _ -> eval' (v :: st)
    | Pop :: _, _ :: xs -> eval' xs
    | ((Add | Sub | Mul | Div | Rem) as op) :: _, a :: b :: xs ->
        let op =
          match op with
          | Add -> ( + )
          | Sub -> ( - )
          | Mul -> ( * )
          | Div -> ( / )
          | Rem -> ( mod )
          | _ -> failwith "Should not be reachable"
        in
        apply2 (map_i2 op) a b q |> or_error (fun x -> I x :: xs)
    | Neg :: _, a :: xs ->
        apply1 (map_i1 Int.neg) a q |> or_error (fun x -> I x :: xs)
    | Swap :: _, x :: y :: xs -> eval' (y :: x :: xs)
    | Not :: _, a :: xs ->
        apply1 (map_b1 not) a q |> or_error (fun x -> B x :: xs)
    | Cat :: _, a :: b :: xs ->
        apply2 (map_s2 ( ^ )) a b q |> or_error (fun x -> S x :: xs)
    | ((And | Or) as op) :: _, a :: b :: xs ->
        let op =
          match op with
          | And -> ( && )
          | Or -> ( || )
          | _ -> failwith "Should not be reachable"
        in
        apply2 (map_b2 op) a b q |> or_error (fun x -> B x :: xs)
    | ((Eq | Lte | Lt | Gte | Gt) as op) :: _, a :: b :: xs ->
        let op =
          match op with
          | Eq -> ( = )
          | Lte -> ( <= )
          | Lt -> ( < )
          | Gte -> ( >= )
          | Gt -> ( > )
          | _ -> failwith "Should not be reachable"
        in
        apply2 (map_i2 op) a b q |> or_error (fun x -> B x :: xs)
    (* more complex case *)
    | Bnd :: coms, N n :: v :: xs -> (
        try eval coms (Unit :: xs) ((n, q' v) :: env)
        with Not_found -> error () )
    | BeginExpr block :: _, _ ->
        let st' = eval block st env in
        eval' (List.hd st' :: st)
    | IfExpr (e_test, e_t, e_f) :: _, _ -> (
        let f xs =
          eval xs st env |> fun y ->
          if !is_quit then y else eval' (List.hd y :: st)
        in
        let rec g = function
          | B true -> f e_t
          | B false -> f e_f
          | N name -> g (q name)
          | _ -> error ()
        in
        try eval e_test st env |> List.hd |> g with Not_found -> error () )
    | Fun' (name, arg, block) :: xs, _ ->
        eval xs (Unit :: st) ((name, Closure (arg, block, env)) :: env)
    | Call :: _, x :: N fname :: st' -> (
        try
          let fn = q fname in
          match fn with
          | Closure (arg, block, env') -> (
              let st'' =
                if List.mem_assoc fname env' then env' else (fname, fn) :: env'
              in
              eval block st' ((arg, q' x) :: st'') |> fun y ->
              if !is_quit then y
              else match y with ret :: _ -> eval' (ret :: st') | _ -> error () )
          | _ -> error ()
        with Not_found -> error () )
    | Call :: _, x :: Closure (arg, block, env) :: st' -> (
        eval block st' ((arg, q' x) :: env) |> fun y ->
        if !is_quit then y
        else match y with ret :: _ -> eval' (ret :: st') | _ -> error () )
    | Return :: _, x :: _ -> ( try [ q' x ] with Not_found -> [ Error ] )
    | TryExpr (block, handle_block) :: _, _ -> (
        is_try := true :: !is_try;
        let down x =
          is_try := List.tl !is_try;
          x
        in
        match eval block st env with
        | Error :: _ -> (
            eval handle_block st env |> down |> function
            | Error :: _ -> Error :: st
            | x :: _ -> eval' (x :: st)
            | _ -> eval' st )
        | v :: _ ->
            down ();
            eval' (v :: st)
        | _ ->
            down ();
            error () )
    | _, _ -> error ()

let interpreter_channel inp out =
  is_quit := false;
  inp |> parse_channel |> snd |> (fun cs -> eval cs [] []) |> stack_to_s
  |> fun str ->
  output_string out str;
  flush_all ()

let interpreter (inp : string) (out : string) =
  interpreter_channel (open_in inp) (open_out out)

let interpreter_stdio (inp : string) = interpreter_channel (open_in inp) stdout

let interpreter_debug inp =
  is_debug := true;
  interpreter_stdio inp;
  is_debug := false
