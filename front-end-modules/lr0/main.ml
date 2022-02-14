open Lexer
open Parser


let x = Parser.parseTree "3+4+5";;

(*
not much to see here yet, designed to be the interface between front-back ends, but none of this would
be visible to a user.
*)
