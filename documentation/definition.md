### Goal

The goal was to make a scientific calculator which, primarily, allows entering mathematical expressions, and computes and displays the result.
These expressions may contain basic operators, parentheses, function calls, integer and non-integer constants and references to variables.

Additionally, it should be possible to define functions with an arbitrary number of parameters to be able to re-use an expression.

The project will be written in the Rust programming language. Rust not only enables the code to be fast, but promotes memory safety, correctness 
and reliability. I also considered Java, C and C++, each of which I am proficient with. Python I also know on a surface level, but I prefer a stronger 
type system.

The language for all documentation and code will be English.

### Usage and implementation

The calculator has a command-line REPL (read-eval-print-loop) interface, with syntax mostly borrowed from 
typical math notation (operators from programming languages):
```console
> 5 + (4 + 3) / 2
8.5

> x = 5
x = 5

> 5x + (4x + 3x) / 2x
28.5

> f(x) = sqrt(sin(x)^2 + cos(x)^2)
Created function f(x)

> f(51241829.1281529)
1

> f(-24147.51825798)
1
```

These inputs will be fed to a parser module. 
* Expression-only inputs will be directly evaluated (using the Shunting-Yard algorithm), printed and dropped. 
* Functions and variables will be stored in a symbol table (functions as an array of tokens in postfix form)
likely implemented as a hash table of function/variable names mapped to the function/variable definitions.

The shunting-yard algorithm, which runs in O(n) time, allows for both immediate evaluation and AST building in linear time. It is therefore reasonable
to assume no higher time complexities will be involved in expression parsing and evaluation, since hash tables allow function and variable look-ups
to be O(1) (amortized). Additionally, the evaluation of postfix trees is trivially O(n).


### References

* [the Shunting-Yard algorithm (Wikipedia)](https://en.wikipedia.org/wiki/Shunting_yard_algorithm)
* [Abstract Syntax Tree (Wikipedia)](https://en.wikipedia.org/wiki/Abstract_syntax_tree)

### Notes for the course
I am a Computer Science (TKT) undergraduate in Helsinki University. 
