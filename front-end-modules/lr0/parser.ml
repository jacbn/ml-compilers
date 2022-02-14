(* OCaml lexer / parser program, by Jacob Brown. *)

(* compile all, then run using e.g. `parse_tree "5+4*(3-2)+1" `*)


(*
lexer:

.
input: calculation string, e.g. '25+(14-12)!*2'
.
output: a series of tokens abstracting the lexemes into single units, 
  e.g. '<NUM, 25> <INF_OP, +> <LBRKT> <NUM, 14> <INF_OP, -> <NUM, 12> <RBRKT> <POST_OP, !> <INF_OP, *> <NUM, 2>'
  Represented as a list of tokens (see line 15).
.
method: simulate a DFA with states for every valid lexeme. 
  Most operations (single-character ones) will only require state 0; operations made of more characters, however, require their own states.
.


note that no input buffer is used as the input is assumed to be relatively small. 
*)

open Helpers

open Lexer

module Parser = struct

exception IndexError of string;;

(* parser *)

type nonterminal = Start | Aterm | Aterm' | Sterm | Sterm' | Factor | Factor' | Num;;
type symbol = NT of nonterminal | T of Lexer.token | Empty ;;
type production = Production of nonterminal * symbol list | EpsilonProduction of nonterminal;;
type item = Item of production * int;; (*the int is the position of the dot;*)

type state = item list;;
type action = Shift of state | Reduce of production | Accept | Error

exception StateNotFoundError of state;;

let tokenToSymbol t = T t;;
let nonterminalToSymbol n = NT n;;
let nonterminalOfProduction = function | Production(n, _) -> n | EpsilonProduction n -> n;;
let productionToSymbolList = function | Production(_, ps) -> ps | EpsilonProduction _ -> [T Epsilon];;
let headOfItem = function | Item(Production(n, _), _) -> n | Item(EpsilonProduction n, _) -> n;;
let productionOfItem (Item(p, n)) = p;;
let symbolAfterDot = function | Item(Production(n, l), i) -> if i = List.length l then Empty else List.nth l i | Item(EpsilonProduction n, _) -> Empty;;
let allNonterminals = [Start; Aterm; Aterm'; Sterm; Sterm'; Factor; Factor'; Num];; 
let allTokens = [Lexer.INF_OP Plus; Lexer.INF_OP Sub; Lexer.INF_OP Mult; Lexer.PRE_OP Cos; Lexer.PRE_OP Pos; Lexer.PRE_OP Neg; Lexer.POST_OP Fact; Lexer.BRKT Lbrkt; Lexer.BRKT Rbrkt; Lexer.NUM; Lexer.Epsilon];; (*plus epsilon? *)
let grammar = Helpers.map nonterminalToSymbol allNonterminals @ Helpers.map tokenToSymbol allTokens;;


let startProduction = Production(Start, [NT Aterm]);;
let startItem = Item(startProduction, 0);;


(*in: a symbol;   out: all productions of input symbol*)
let nonterminalProductions n = 
  let l = 
    match n with 
      | Start ->  [[NT Aterm; T EndMarker]]
      | Aterm -> [[NT Sterm; NT Aterm']]
      | Aterm' -> [[T (INF_OP Plus); NT Sterm; NT Aterm']; [T Epsilon]]
      | Sterm -> [[NT Factor; NT Sterm']]
      | Sterm' -> [[T (INF_OP Sub); NT Factor; NT Sterm']; [T Epsilon]]
      | Factor -> [[NT Num; NT Factor']]
      | Factor' -> [[T (INF_OP Mult); NT Num; NT Factor']; [T Epsilon]]
      | Num -> [[T (NUM)]; [T (PRE_OP Cos); NT Num]; [T (BRKT Lbrkt); NT Aterm; T (BRKT Rbrkt)]; [T (PRE_OP Pos); NT Num]; [T (PRE_OP Neg); NT Num]] (*[NT Num; T (POST_OP Fact)]; *)
  in 
    Helpers.map (fun x -> if x = [T Epsilon] then EpsilonProduction n else Production (n, x)) l
;;

let rec productions = function 
  | NT n -> nonterminalProductions n
  | T n -> []
  | Empty -> []
;;

let containsEpsilonProduction = function 
  | T t -> false
  | NT n -> List.mem [T Epsilon] (Helpers.map productionToSymbolList (nonterminalProductions n))
  | Empty -> true
;;


let filterUniqueFirstItems l =
  let rec aux seen = function 
    | [] -> [] 
    | h::t -> if List.mem (List.hd h) seen then aux seen t else h :: aux (List.hd h :: seen) t
  in aux [] l
;;

let rec first_aux checked = function 
  | [] -> [Lexer.Epsilon]
  | h::t -> (
    match h with 
    | T x -> [x]
    | NT y -> (
      let f = List.flatten (Helpers.map (first_aux (y::checked)) (filterUniqueFirstItems (Helpers.map productionToSymbolList (Helpers.filter (fun z -> List.hd (productionToSymbolList z) <> h) (productions h))))) in
      if containsEpsilonProduction h && not(List.mem y checked) then first_aux (y::checked) t @ f
      else if not(List.mem y checked) then f else []
    )
    | Empty -> []
  )
;;
let first = first_aux [];;

let rec productionsContaining s = Helpers.filter (fun x -> List.mem s (productionToSymbolList x)) (List.flatten (Helpers.map productions (Helpers.map nonterminalToSymbol allNonterminals)));;

let rec follow_aux = function 
  | T _ | Empty -> []
  | NT Start -> [Lexer.EndMarker]
  | NT n -> (
    (Helpers.filter (fun x -> x <> Lexer.Epsilon) (List.flatten (Helpers.map first (Helpers.filter (fun x -> x <> [] && x <> [Empty]) (Helpers.map (Helpers.after (NT n)) (Helpers.map productionToSymbolList (Helpers.filter (fun x -> nonterminalOfProduction x <> n) (productionsContaining (NT n)))))))))
    (*(Helpers.filter the epsilons out of)  the big union of  the first() of         all nonempty productions    which appear after the current symbol             while ignoring cyclic productions as to prevent infinite recursion*)

    @ List.flatten (Helpers.map follow_aux (Helpers.map (fun x -> NT x) (Helpers.map nonterminalOfProduction (Helpers.filter (fun x -> Helpers.after (NT n) (productionToSymbolList x) = [] || List.for_all containsEpsilonProduction (Helpers.after (NT n) (productionToSymbolList x))) (Helpers.filter (fun x -> nonterminalOfProduction x <> n) (productionsContaining (NT n))))))))
    (*the big union of  the follow of       all nonterminals which have a production           either      ending after the current symbol          or         for which all nonterminals after it contain epsilon                      while ignoring cyclic productions as to prevent infinite recursion*)
;;

let follow x = Helpers.unique (follow_aux x);;


(*
closure:
  allItems: running total
  items: closure of current nonterminal
  length: the length of allItems before aux runs; if unchanged after, we are done
  added: a list of all nonterminals for which we have already computed the closure
*)
let closure j : state = 
  let rec aux allItems items length =
    match items with
      | [] -> if length = (List.length allItems) then allItems else aux allItems allItems (List.length allItems)      
      | h::t -> ( 
        (*the filter allows only items whose production's closure has not already been found; the ma.p ma.ps production -> item*)
        let newAllItems = (Helpers.union allItems (Helpers.filter (fun i -> not(List.mem i allItems)) (Helpers.map (fun p -> Item(p, 0)) (productions (symbolAfterDot h))))) 
        in aux newAllItems t length
      )
  in aux j j (List.length j)
;;

(*goto: return the LR automata state generated, from current state i, by inputting symbol x.*)
let goto (i : state) x = closure (Helpers.map (fun (Item(p, n)) -> Item(p, n+1)) (Helpers.filter (fun j -> symbolAfterDot j = x) i));;


(*CC: generate all states of the LR automata.*)
let canonicalCollection = 
  let rec aux allC c length =
    match c with 
      | [] -> if length = (List.length allC) then allC else aux allC allC (List.length allC) (*repeat until no new items added*)
      | h::t -> aux (Helpers.union allC (Helpers.filter (fun i -> List.length i > 0 && not(List.mem i c)) (Helpers.map (fun x -> goto h x) grammar))) t length
          (*union current with goto currentItem x for all grammar symbols x, filter out nonempty and those already in current*)

          (*there is an unintentional issue in that if goto i x is the same for different grammar symbols x across the same state i, it will duplicate it; this shouldn't ever happen
            because all states reachable from i are reached by a different grammar symbol, but in case lr(k>0) is different, here is a warning*)
  in let close = [closure [startItem]]
  in aux close close 0
;;

let startState = List.hd (List.rev canonicalCollection);;



let isToken = function 
  | T _ -> true
  | _ -> false
;;

type ptpair = PTPair of state * symbol;;
type ptentry = PTEntry of ptpair * action;;

let getPTPair (PTEntry(pp, _)) = pp;;
let getPTAction (PTEntry(_, a)) = a;;

let rec generatePTLayer s acc = function 
  | [] -> acc
  | h::t -> ( (*h::t is the list of all items in a state (at least, when this func is first called)*)
    if isToken (symbolAfterDot h) then generatePTLayer s (PTEntry(PTPair(s, (symbolAfterDot h)), Shift (goto s (symbolAfterDot h)))::acc) t
    else if symbolAfterDot h = Empty && headOfItem h <> Start then generatePTLayer s (Helpers.map (fun a -> PTEntry(PTPair(s, a), Reduce (productionOfItem h))) (Helpers.map (fun x -> T x) (follow (NT (headOfItem h)))) @ acc) t
    else if (headOfItem h) = Start then generatePTLayer s (PTEntry(PTPair(s, T EndMarker), Accept)::acc) t
    else generatePTLayer s acc t
  ) 
;; 

let rec generateParsingTable = function
  | [] -> []
  | h::t -> generatePTLayer h [] h @ generateParsingTable t
;;

let parsingTable = generateParsingTable canonicalCollection;;

let stateNum s = try(Helpers.index s canonicalCollection) with IndexError _ -> raise (StateNotFoundError s);;
let stateFromNum i = List.nth canonicalCollection i;;

type raction = ShiftR of int | ReduceR of production | AcceptR | ErrorR;;
type ptpairnum = PTPairN of int * symbol;;
type ptentrynum = PTEntryN of ptpairnum * raction;;

let readableAction = function 
  | Shift x -> ShiftR (stateNum x)
  | Reduce p -> ReduceR p 
  | Accept -> AcceptR
  | Error -> ErrorR
;;

let readableParsingTable = Helpers.map (fun (PTEntry(PTPair(s, symb), a)) -> PTEntryN(PTPairN(stateNum s, symb), readableAction a)) parsingTable;;

let print_int_list l =
  let rec aux acc = function 
    | [] -> print_string (acc ^ "\n")
    | h::t -> aux (acc ^ "; " ^ string_of_int h) t
  in aux "" l
;;

let getAction i a = getPTAction (List.hd (Helpers.filter (fun x -> getPTPair x = PTPair(stateFromNum i, a)) parsingTable));;


let print_step = function 
  | Shift t -> print_string "shift\n"
  | Reduce n -> print_string "reduce\n"
  | _ -> ()
;;

let rec parser_aux tokenStream stack acc =
  print_int_list stack;
  match tokenStream with 
    | [] -> failwith "reached end of input string"
    | x::xs -> (
      (*print_step (getAction (List.hd stack) x);*)
      match getAction (List.hd stack) x with 
        | Shift t -> parser_aux xs (stateNum t::stack) (acc)
        | Reduce p -> (let poppedStack = (Helpers.pop (List.length (Helpers.filter (fun y -> y <> T Epsilon) (productionToSymbolList p))) stack) in parser_aux (x::xs) (stateNum (goto (stateFromNum (List.hd poppedStack)) (NT (nonterminalOfProduction p))) :: poppedStack) (p :: acc))
        | Accept -> print_string "Complete!\n"; startProduction :: acc
        | Error -> failwith "error recovery routine goes here" (*all invalid parsing table requests should lead here, not implemented yet*)
    )
;;

let parseSymbols inp = parser_aux inp [stateNum startState] [];;

let parser s = parseSymbols (Helpers.map (fun x -> T x) (Lexer.lexer s));;




type parseTree = Lf of Lexer.token | Br of nonterminal * parseTree list

let replaceRightmost t r =
  let replaced = ref false in (*references do technically make the entire parser non-pure, though admittedly it makes the implementation of this *so* much easier*)
    let rec aux tree repl =   (* (note that this is possible to code without, though) *)
    match tree with 
      | Lf t -> Lf t
      | Br(n, []) -> if not (!replaced) then (replaced := true; Br(n, repl)) else Br(n, [])
      | Br(n, sl) -> Br(n, (Helpers.map (fun x -> aux x repl) sl))
  in aux t r
;;

let rec genParseTree acc = function
  | [] -> acc
  | x::xs -> (match x with
    | Production(n, sl) -> genParseTree (replaceRightmost acc (Helpers.map (fun y -> match y with | NT nt -> Br(nt, []) | T t -> Lf t | Empty -> Lf Epsilon) sl)) xs
    | EpsilonProduction n -> genParseTree (replaceRightmost acc [Br(n, [Lf Epsilon])]) xs
  )
;;

let parseTree s = genParseTree (Br(Start, [])) (parser s);;


end