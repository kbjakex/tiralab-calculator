## Implementation

The program consists of primarily three parts:
1. The user interface code, located in `main.rs`.
2. The state of the calculator, located in `state.rs`, which contains all of the code related to storage of variables and functions.
3. The parsing code, located in `parsing.rs`. This contains the code for tokenization and infix->postfix conversion.

Shunting yard is at the core of the application. All expressions are first converted to postfix with shunting yard, and then either evaluated directly,
or stored if declaring a function. The postfix form (also called a "postfix tree") turned out to be a simple and compact form to store the expressions, 
so that is the data structure used for stored expressions. The only other data structures used are Vec (~ArrayList) and HashMap, provided by the standard 
library. The vector doubles as the stack used to implement shunting yard.

Shunting yard is [known to be O(n)](https://en.wikipedia.org/wiki/Shunting_yard_algorithm) in time complexity, and the evaluation algorithm (trivial) 
is O(n).


