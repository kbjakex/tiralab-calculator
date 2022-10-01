## Report for week 4

Struggle but also progress. Here's a summary of this week:
* Function calls no longer recursively run the shunting yard algorithm (last week, it was invoked once per parameter, so `f(g(1,2),h(1,2,3))` 
would invoke it 7 times). This did end up greatly simplifying the logic and I felt like I wasn't solving the wrong problems anymore.
* Functions now actually work. They can now be declared, with an arbitrary number of parameters, and invoked as freely as you'd expect.
* Unary operators do *not* work.
* Code coverage is a bit better now. Still more work to do here.

Getting functions to work took most of the available time, as suspected. There was a lot of going back and forth with the code; I'm glad the end result
is as tidy as it is, although the algorithm *has* grown fairly sizeable. There were a myriad of small bugs that had to be dug up and fixed too. Subtle
things such as function parameters being evaluated in the opposite order.. New tests had to be written as well.

A surprising amount of time was spent on unary operators. The problem is not really about finding a way to make them work, but about doing so without more 
or less duplicating the code I have for binary operators, for unary ones. Even detecting an unary minus requires keeping state, and where this detection 
should be done isn't entirely obvious (in the tokenizer? in the algorithm itself? both have downsides.) I almost wanted to do away with the strong 
separation of binary and unary operators entirely, but this caused some awkwardness elsewhere in the codebase (how should `Operator::apply(f64, f64)` 
work with unary operators?). Overall, problems, needs more thinking.

My primary concern now is the code quality, which has certainly degraded from last week. Functions are too long, logic can probably be simplified.
Additionally, despite what I thought last week, the separation of the user interface and the actual testable logic is not sufficient for testing.

I was hoping to be "done" with the application at this point, so that I'd have time left to expand on what the functions can do (most of all, allowing for
multi-line functions with local variables), but at this pace, I'm not sure I'll have the time, considering the code quality & test coverage concerns I've
been having.

Time spent this week: 12.5 hours. More or less efficiently.

A question that I meant to ask on Friday via email but forgot: are benchmarks relevant for this project? Nothing I have is particularly computationally
demanding nor time critical, so I assume not, in which case, is there some other type of testing I should be doing instead?

### Next up

The clear top three on the to-be-done list are now unary operators, code quality and code coverage. I wish to have unary operators in and tested by the
next deadline.
