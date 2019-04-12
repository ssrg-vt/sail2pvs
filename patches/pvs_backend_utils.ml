
open Output
open Typed_ast
open Backend_common

(* Backward compatibility functions *)

(* Available in OCaml since 4.01.00 - optimisable with "%apply" and "%revapply" *)
let (|>) x f = f x;;
let (@@) f x = f x;;
 
let r = Ulib.Text.of_latin1

let from_string x = meta x
let sep x s = ws s ^ x
let sep_before x s = x ^ ws s
let sep_block x y s = x ^ (ws s) ^ y
let path_sep = r"."

let star = Ulib.Text.of_latin1 "*"
let space = Output.ws (Some [Ast.Ws (Ulib.Text.of_latin1 " ")])
let identation = space ^ space
let newline = meta "\n"

let tyvar (_, tv, _) = id Type_var (Ulib.Text.of_string (String.uppercase (Ulib.Text.to_string tv)))
let concat_str s = concat (from_string s)

let comment_string s = Str.global_replace (Str.regexp "\n") ("\n% ") s


let lex_skip = function
    | Ast.Com(r) -> ml_comment_to_rope r
    | Ast.Ws(r) -> r
    | Ast.Nl -> r"\n"

let need_space t1 t2 = true

let output_to_string s = Ulib.Text.to_string (Output.to_rope (r"") lex_skip need_space s)


let rec case_concat sep = function
  | [] -> Output.concat sep []
  | [x] -> x
  | x::[y] -> if (Str.string_match (Str.regexp "ELSE")  (output_to_string @@ Output.remove_initial_ws y) 0) then x ^ y else x ^ sep ^ y
  | x::xs -> x ^ sep ^ case_concat sep xs


let constr_fun_app sep args = 
  let args_str = List.map (fun s -> output_to_string @@ Output.remove_initial_ws s) args in
  let is_flat = List.length (List.filter (fun s -> String.equal s ",") args_str) > 0 in
  let filtered = List.map from_string args_str in
  let block x = Output.flat [from_string "("; x; from_string ")"] in
  let result = if is_flat then Output.flat filtered else
  match filtered with
  | [] -> emp
  | [x] -> x
  | x::xs -> x ^ (Output.concat sep (List.map block xs)) in
  result

let comment_output s = from_string "%" ^ (from_string (comment_string (output_to_string s))) ^ new_line

let tyvar_to_upper s = Ulib.Text.of_string @@ String.uppercase @@ Ulib.Text.to_string (Tyvar.to_rope s)
let nvar_to_upper s = Ulib.Text.of_string @@ String.uppercase @@ Ulib.Text.to_string (Nvar.to_rope s)


