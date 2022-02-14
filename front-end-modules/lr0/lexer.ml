open Helpers

module Lexer = struct

type infop = Plus | Sub | Mult | Exp;;
type preop = Cos | Pos | Neg;;
type postop = Fact;;
type brkt = Lbrkt | Rbrkt;;
type whitespace = Space | Tab | Newline;;
type token = NUM | INF_OP of infop | PRE_OP of preop | BRKT of brkt | POST_OP of postop | WS of whitespace | Epsilon | EndMarker;;

let rec symbolDFA state input pos store tokens = 
  let current = List.nth input pos in
  (*In the following two lines, we don't add one to the pos counter if the end of the symbol is at state 2 or 3.
    These states correspond to the number states, and this is necessary because there is no defined length for
    how long numbers are; rather than adding one to the counter until we reach the last char, we are adding 
    one until the current char is *not* a number; as such, we will have added one more at the end. These lines,
    therefore, fix this discrepancy in how the values are handled.
    
    There is one other exception -- right bracket marks the end of a number, so a trailing + or - indicates an
    infix operation, not prefix operation, so we make a new state. Because we need a new state, however, we must
    not add one to the pos counter twice.*)
  let addToken t = 
    if state = 2 || state = 3 || state = 7 then symbolDFA 6 input pos "" (t::tokens) 
    else symbolDFA 1 input (pos+1) "" (t::tokens) in
  let skipToken t = symbolDFA 1 input (pos+(if state = 2 || state = 3 then 0 else 1)) "" tokens in
  let moveToState n = symbolDFA n input (pos+(if state = 6 then 0 else 1)) (store ^ Helpers.toStr current) tokens in
  match state with
    | 1 -> (
      match current with 
        | '$' -> List.rev (EndMarker :: tokens)
        | '+' -> addToken(PRE_OP Pos)
        | '-' -> addToken(PRE_OP Neg)
        | '!' -> addToken(POST_OP Fact)
        | '(' -> addToken(BRKT Lbrkt)
        | ')' -> moveToState 7
        | ' ' -> skipToken(WS Space)
        | '\t' -> skipToken(WS Tab)
        | '\n' -> skipToken(WS Newline)
        | '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9' -> moveToState 2
        | '.'  -> moveToState 3
        | 'c' -> moveToState 4
        | _ -> moveToState (-1)
    )
    | 2 -> ( (*This state is for the integer part of a number*)
      match current with 
        | '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9' -> moveToState 2
        | '.'  -> moveToState 3
        | _ -> addToken(NUM)
    )
    | 3 -> ( (*This state is for the decimal part of a number*)
      match current with
        | '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9' -> moveToState 3
        | _ -> addToken(NUM)
    )
    | 4 -> ( (*States 4 and 5 are for detecting `cos`*)
      match current with 
        | 'o' -> moveToState 5
        | _ -> moveToState (-1)
    )
    | 5 -> (
      match current with 
        | 's' -> addToken(PRE_OP Cos)
        | _ -> moveToState (-1)
    )
    | 6 -> (
      match current with 
        | '+' -> addToken(INF_OP Plus)
        | '-' -> addToken(INF_OP Sub)
        | '*' -> addToken(INF_OP Mult)
        | _ -> moveToState 1
    )
    | 7 -> addToken(BRKT Rbrkt)

    | -1 -> failwith ("input string not recognised: " ^ String.make 1 current ^ " @ " ^ string_of_int pos);
    | n -> failwith ("dfa in nonexistant state " ^ (string_of_int n));
;;


let explode str =
  let rec expl c l =
    if c < 0 then l else expl (c - 1) (str.[c] :: l)
  in expl (String.length str - 1) []
;;

let lexer s = symbolDFA 1 (explode (s^"$")) 0 "" [];;
(*  usage: lexer "-5--(10*3)";;  *)


end