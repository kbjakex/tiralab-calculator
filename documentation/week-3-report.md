## Report for week 3

Poor time management continues, but progress has also been made. In summary:
* Code coverage has indeed been set up, with GitHub Actions now automatically computing it on every push
* Variables are fully functional (you can declare them and refer to them)
* A fair amount of work has been put into getting functions work, though this does not work yet

A nice realization this week was that I can actually just use the postfix token array as my "AST". 
It probably still counts as an AST given how general the concept is, and "postfix tree" is a thing, so this is also technically still a tree. But a very
implicit one! Trivially flat in memory, just as easy to evaluate, and it's never going to take more memory than a binary tree - rather the opposite, since
I don't have to store pointers to the children anymore. Not very significant, but very cool!

Functions take quite a bit of work. One of the current struggles is with where I draw the line between making good use of the computer versus 
not having duplicate code: to store functions, I need a token type that, instead of storing variable names (which are references, by the way, making
storing the original token type impossibe unless I heap-allocate each name in all cases even when it's completely unnecessary), I'd rather just
store the value of the variable directly, since that ought to be known by the time the function is being declared. Unless it's a parameter, which is
another part of the problem, since only functions are concerned with parameters. 

And, since I now have two (actually three, but not relevant) different 'token' types, I need two different functions to evaluate the tree.
It's not a very complex operation, but I'm not super happy with this. It's probably just going to stay this way, though.

Secondly, parsing function parameters with shunting yard is the hassle I expected it to be, even if I do understand the algorithm now. I *can*
do it inline in a single invocation of the algorithm, and add some extra logic to be able to validate the input, too, but that remains to be done -
for now, I picked the (probably) easy way out and just invoke shunting yard recursively (one invocation per function parameter).

Though right now I suspect this might've not been an easier choice in the end, because for this to work, I have to know where the parameter ends.
That's a bunch of extra logic, which in hindsight I should've just written instead of trying to retrofit the actual shunting yard algorithm to be able to
detect when it's *probably* at the end, which doesn't work (yet, anyways). So, this is the current status of the functions - does not work, because
the recursive invocation consumes the delimiters (,) and the closing ) of each function call, which leaves the calling function unable to determine
if there are more parameters. I'd rather not keep spending my weekends on this, so I might defer finishing this to next week, hopefully mon/tue.

Also, code coverage is admittedly currently poor. I didn't leave myself enough time to add tests for all the changes.

### Next up

Functions will work by the next deadline, and code coverage will be brought back up. 

That will conclude all main functionality for the project. 

After that, I expect I'll get the low-hanging fruits in optimization, but I think it's fairly clear by now I'll have time to at least add 
multi-statement functions, so looking forward to that.
