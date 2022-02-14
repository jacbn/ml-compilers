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

type infop = Plus | Sub | Mult | Exp;;
type preop = Cos | Pos | Neg;;
type postop = Fact;;
type brkt = Lbrkt | Rbrkt;;
type whitespace = Space | Tab | Newline;;
type token = NUM | INF_OP of infop | PRE_OP of preop | BRKT of brkt | POST_OP of postop | WS of whitespace | Epsilon | EndMarker;;

exception IndexError of string;;

let toStr = String.make 1;;

let rec union l1 = function 
  | [] -> l1 
  | h::t -> if List.mem h l1 then union l1 t else union (h::l1) t
;;

let rec intersection l1 = function 
  | [] -> [] 
  | h::t -> if List.mem h l1 then h :: intersection l1 t else intersection l1 t 
;;


let rec index x = function
  | [] -> raise (IndexError "index out of range")
  | h::t -> if h = x then 0 else 1 + index x t
;;

let rec map f = function 
  | [] -> []
  | h::t -> f h :: map f t
;;

let rec filter p = function 
  | [] -> []
  | h::t -> if p h then h::filter p t else filter p t
;;

let rec after x = function (*return all elements after the first instance of x*)
  | [] -> []
  | h::t -> if h = x then t else after x t
;;

let rec pop n = function  (*remove the first n items from a list*)
  | [] -> if n = 0 then [] else failwith "can't pop from empty list"
  | h::t -> if n < 1 then (h::t) else pop (n-1) t
;;

let cons_unique x xs = if List.mem x xs then xs else x::xs;;
let unique xs = List.fold_right cons_unique xs [];; (*create a new list with only the unique elements of the given list*)




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
  let moveToState n = symbolDFA n input (pos+(if state = 6 then 0 else 1)) (store ^ toStr current) tokens in
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

(*  usage: lexer "-5--(10*3)";;  *)

let explode str =
  let rec expl c l =
    if c < 0 then l else expl (c - 1) (str.[c] :: l)
  in expl (String.length str - 1) []
;;

let lexer s = symbolDFA 1 (explode (s^"$")) 0 "" [];;




(* parser *)

type nonterminal = Start | Aterm | Aterm' | Sterm | Sterm' | Factor | Factor' | Num;;
type symbol = NT of nonterminal | T of token | Empty ;;
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
let allTokens = [INF_OP Plus; INF_OP Sub; INF_OP Mult; PRE_OP Cos; PRE_OP Pos; PRE_OP Neg; POST_OP Fact; BRKT Lbrkt; BRKT Rbrkt; NUM; Epsilon];; (*plus epsilon? *)
let grammar = map nonterminalToSymbol allNonterminals @ map tokenToSymbol allTokens;;


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
    map (fun x -> if x = [T Epsilon] then EpsilonProduction n else Production (n, x)) l
;;

let rec productions = function 
  | NT n -> nonterminalProductions n
  | T n -> []
  | Empty -> []
;;

let containsEpsilonProduction = function 
  | T t -> false
  | NT n -> List.mem [T Epsilon] (map productionToSymbolList (nonterminalProductions n))
  | Empty -> true
;;


let filterUniqueFirstItems l =
  let rec aux seen = function 
    | [] -> [] 
    | h::t -> if List.mem (List.hd h) seen then aux seen t else h :: aux (List.hd h :: seen) t
  in aux [] l
;;

let rec first_aux checked = function 
  | [] -> [Epsilon]
  | h::t -> (
    match h with 
    | T x -> [x]
    | NT y -> (
      let f = List.flatten (map (first_aux (y::checked)) (filterUniqueFirstItems (map productionToSymbolList (filter (fun z -> List.hd (productionToSymbolList z) <> h) (productions h))))) in
      if containsEpsilonProduction h && not(List.mem y checked) then first_aux (y::checked) t @ f
      else if not(List.mem y checked) then f else []
    )
    | Empty -> []
  )
;;
let first = first_aux [];;

let rec productionsContaining s = filter (fun x -> List.mem s (productionToSymbolList x)) (List.flatten (map productions (map nonterminalToSymbol allNonterminals)));;

let rec follow_aux = function 
  | T _ | Empty -> []
  | NT Start -> [EndMarker]
  | NT n -> (
    (filter (fun x -> x <> Epsilon) (List.flatten (map first (filter (fun x -> x <> [] && x <> [Empty]) (map (after (NT n)) (map productionToSymbolList (filter (fun x -> nonterminalOfProduction x <> n) (productionsContaining (NT n)))))))))
    (*(filter the epsilons out of)  the big union of  the first() of         all nonempty productions    which appear after the current symbol             while ignoring cyclic productions as to prevent infinite recursion*)

    @ List.flatten (map follow_aux (map (fun x -> NT x) (map nonterminalOfProduction (filter (fun x -> after (NT n) (productionToSymbolList x) = [] || List.for_all containsEpsilonProduction (after (NT n) (productionToSymbolList x))) (filter (fun x -> nonterminalOfProduction x <> n) (productionsContaining (NT n))))))))
    (*the big union of  the follow of       all nonterminals which have a production           either      ending after the current symbol          or         for which all nonterminals after it contain epsilon                      while ignoring cyclic productions as to prevent infinite recursion*)
;;

let follow x = unique (follow_aux x);;


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
        (*the filter allows only items whose production's closure has not already been found; the map maps production -> item*)
        let newAllItems = (union allItems (filter (fun i -> not(List.mem i allItems)) (map (fun p -> Item(p, 0)) (productions (symbolAfterDot h))))) 
        in aux newAllItems t length
      )
  in aux j j (List.length j)
;;

(*goto: return the LR automata state generated, from current state i, by inputting symbol x.*)
let goto (i : state) x = closure (map (fun (Item(p, n)) -> Item(p, n+1)) (filter (fun j -> symbolAfterDot j = x) i));;


(*CC: generate all states of the LR automata.*)
let canonicalCollection = 
  let rec aux allC c length =
    match c with 
      | [] -> if length = (List.length allC) then allC else aux allC allC (List.length allC) (*repeat until no new items added*)
      | h::t -> aux (union allC (filter (fun i -> List.length i > 0 && not(List.mem i c)) (map (fun x -> goto h x) grammar))) t length
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
    else if symbolAfterDot h = Empty && headOfItem h <> Start then generatePTLayer s (map (fun a -> PTEntry(PTPair(s, a), Reduce (productionOfItem h))) (map (fun x -> T x) (follow (NT (headOfItem h)))) @ acc) t
    else if (headOfItem h) = Start then generatePTLayer s (PTEntry(PTPair(s, T EndMarker), Accept)::acc) t
    else generatePTLayer s acc t
  ) 
;; 

let rec generateParsingTable = function
  | [] -> []
  | h::t -> generatePTLayer h [] h @ generateParsingTable t
;;

let parsingTable = generateParsingTable canonicalCollection;;

let stateNum s = try(index s canonicalCollection) with IndexError _ -> raise (StateNotFoundError s);;
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

let readableParsingTable = map (fun (PTEntry(PTPair(s, symb), a)) -> PTEntryN(PTPairN(stateNum s, symb), readableAction a)) parsingTable;;

let print_int_list l =
  let rec aux acc = function 
    | [] -> print_string (acc ^ "\n")
    | h::t -> aux (acc ^ "; " ^ string_of_int h) t
  in aux "" l
;;

let getAction i a = getPTAction (List.hd (filter (fun x -> getPTPair x = PTPair(stateFromNum i, a)) parsingTable));;


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
        | Reduce p -> (let poppedStack = (pop (List.length (filter (fun y -> y <> T Epsilon) (productionToSymbolList p))) stack) in parser_aux (x::xs) (stateNum (goto (stateFromNum (List.hd poppedStack)) (NT (nonterminalOfProduction p))) :: poppedStack) (p :: acc))
        | Accept -> print_string "Complete!\n"; startProduction :: acc
        | Error -> failwith "error recovery routine goes here" (*all invalid parsing table requests should lead here, not implemented yet*)
    )
;;

let parser inp = parser_aux inp [stateNum startState] [];;

let testParser s = parser (map (fun x -> T x) (lexer s));;




type parseTree = Lf of token | Br of nonterminal * parseTree list

let replaceRightmost t r =
  let replaced = ref false in (*references do technically make the entire parser non-pure, though admittedly it makes the implementation of this *so* much easier*)
    let rec aux tree repl =
    match tree with 
      | Lf t -> Lf t
      | Br(n, []) -> if not (!replaced) then (replaced := true; Br(n, repl)) else Br(n, [])
      | Br(n, sl) -> Br(n, (map (fun x -> aux x repl) sl))
  in aux t r
;;

let rec genParseTree acc = function
  | [] -> acc
  | x::xs -> (match x with
    | Production(n, sl) -> genParseTree (replaceRightmost acc (map (fun y -> match y with | NT nt -> Br(nt, []) | T t -> Lf t | Empty -> Lf Epsilon) sl)) xs
    | EpsilonProduction n -> genParseTree (replaceRightmost acc [Br(n, [Lf Epsilon])]) xs
  )
;;

let parseTree s = genParseTree (Br(Start, [])) (testParser s);;


parseTree "5*(4-3*(2+7))";;