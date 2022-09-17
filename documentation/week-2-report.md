## Report for week 2

This week I have managed my time poorly, and got much less done than anticipated. What I did do is:
- finish the initial implementation of the shunting yard algorithm
- write a handful of tests for it
- and do a bit of housekeeping in the codebase (such as commenting), although somewhat minor.

Additionally, I spent an annoying amount of time setting up test coverage. This will need more investigation, but the problem is clear: the Rust compiler
(rustc) needs to be "nightly" (which I have), but since the LLVM version used in rustc needs to match the LLVM I process the generated coverage reports
with, the versions have to match. This is an issue, because nightly rustc uses LLVM 15.0, [which has yet been released](https://github.com/llvm/llvm-project/releases/tag/llvmorg-14.0.6),
so the solution will be to wait for LLVM 15 to release -- which is not an option -- or to build LLVM myself. Regrettably, I could've had this done by now,
but didn't get around to it in time for the deadline. 

What proved surprisingly challenging was managing the different formats of data. I have the AST, and two different token types, that all are relatively similar,
but re-using would've ultimately led to worse code. Clear in hindsight, but took some back-and-forth dancing.

All in all, I hadn't touched code coverage in Rust before, this is definitely useful to know.

Functions (as inputs) also turned out to be a small problem with the algorithm: while the Wikipedia sample code has accounted for that, it is too loose for my needs;
I would rather parse and collect the parameters in isolation from the current expression. This is mostly for validation purposes - the code in the Wikipedia
article doesn't keep track of parameter count for example, and at least my current understanding is that based on the postfix output alone I can't always
determine if the input had too few arguments (consuming more tokens than provided as funtion parameters probably causes detectable issues elsewhere, but I can't
imagine this being a good solution in a longer run).

Another 'issue' right now is that I use the shunting yard algorithm in its "purest form"; I use it just to convert an infix input to a postfix output.
Performance/efficiency-wise this is non-ideal:
* If I simply wanted to evaluate the expression, this could be done without allocating and building the list of output nodes (and thereafter traversing *that*);
it seems fairly trivial to modify the algorithm to evaluate directly.
* If instead I want to build an AST (wihch is whenever a function is being declared/modified), I could build the AST directly within the algorithm, also eliminating an extra allocation + traversal step.
This would effectively require me to duplicate the algorithm though, as the modifications differ, and it doesn't help the time complexity, only performance. It is also unclear
how much this would win in performance in practice, so I have decided to leave it as is for now.

About code style checks: I'm using `cargo clippy` as my linter. It does not produce a webview of the issues, but rather an in-console report which I used to clean up some of the warnings. My IDE also invokes clippy and displays its warnings directly in the editor, and I'm using the official code formatter, so my code should be fairly good at all times.

Next is what I wanted to have done by now, and will have by Sunday (tomorrow) evening instead, which is printing the evaluation result to the console.
I will also get the code coverage working, and after that is time for functions. By the next deadline, I wish to have the ability to add and call functions in and tested.

Time spent, not including the hours spent mostly idling, would be roughly 6. Out of 16.6, I know this is low.
