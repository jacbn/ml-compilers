# ml-compilers
Source code for different types of compilers made in OCaml (ported from website for easier management).


## front-end-interpret
Contains the source code to put into an interpreter, to easily view the results of each function.
Throw the whole program in to an interpreter, then run some code!
You can parse any mathematical expression with the LR0 parser -- use a mix of [0-9], ., +, -, *, /, (, ), cos.
If you just want to see the output, use the `parseTree "..."` command. Try `parseTree "5+4*(8/2)`!

You'll notice there's code for supporting post-operations and right-associative operators (e.g. exponent),
but these can't be parsed in the LR0. Keep an eye out for the LALR1!


## front-end-modules
Contains the same as above, split into modules for the lexer/parser (and one for common functions).
Easier to read, but won't run standalone as it needs to be compiled with ocamlc.
