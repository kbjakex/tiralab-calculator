## Report for week 6

This week, I bit off more than I could chew!

Since the project was done except for the built-in functions / constants last week, I decided I'd have time to add a small type system, and to have at 
least 3 types: rationals, (big) decimals and booleans. I ended up finding [`rug`](https://docs.rs/rug/latest/rug/) which seemed to have everything 
I wanted and more.

So, integrating that has been what I've been doing. I'm not going to be able to push a fully funcional & commented & tested version this week, because turns out,
this was not trivial! Here is some of what I ran into:
* The old value type, `f64`, was trivially zero-cost copyable. These new types are not. This had major effects on the entire codebase.
* Testing is no longer easy, because now I have to account for the different types of values that can be outputted.
* Despite rug supporting a myriad of functions on all of its types, it turns out some that *seem* basic at first are not, and those are not present.
  For example, there is no `pow(rational, rational)`, or `sqrt(rational)`, .. at all. I wanted rationals because of the exactness they provide, so
  converting to a decimal, which is inherently lossy regardless of the number of bits, is not an option.

  It is understandable that these don't exist: `pow(rational, rational)` is actually very non-trivial, because rational is signed, which means 
  `a^(c/d) != (a^c)^(1/d) or (a^(1/d))^c`, and there are infinitely many rationals for which the squareroot does not give back a rational. This meant 
  I had to special-case the implementations for rationals, which was a non-zero amount of work, amplified by the fact that the library is a bit clunky 
  to use.
* Instead of implementing each (binary) operator for each pair of types, which would've given me an explosion of combinations, I opted to first promote
  both sides to the same type. Rational, being the most restrictive, is promoted to Decimal, which again is promoted to Complex. Even this was a bit of a 
  hassle, though largely because of the library being a bit clunky to use.
* Printing became less trivial. The default formatting of floats is, frankly, not great - `0.5` is printed as `5.000000000000000000e-1` which is not ideal.
  I still don't have a good solution to this; by default, the library prints the value in a format that will be guaranteed to parse to the same value,
  and apparently this means the output looks like this. I need to therefore figure out the number of required digits myself, which I'm sure will be fun
  to also have to write tests for. Complex numbers are also outputted as `(real, imag)` rather than `real + imag i` which I'd prefer.
* I have to also implement every built-in function for every built-in type. `sqrt()` is one of these, and although this is the first function I've implemented,
  I already ran into the aforementioned issues with rationals. Not looking forward to the rest of the functions.
* I found issues with the existing code while testing this. Notably, declaring `f(a,b) = a < b` called with `f(-1, 1)` outputs `false`, but `f((-1), 1)` outputs `true`. 
  I really hope this is a surface-level issue.
* The types provided by the library don't account for complex results out of the box. They do return NaN, but in any case, I have to myself make sure things like
  exponentiating negatives or taking even roots of negatives gives complex numbers rather than just "not a number". In hindsight, I'm unsure if introducing
  complex number support was ideal, but I'm too far in now.
* `rug` is implemented using GNU libraries and is therefore GPL licensed. Oops. There goes my MIT license. This is a bit of a bummer.

So there we go. I have the infrastructure all set up, there's just a _lot_ of busywork to do now. 
Mostly, I hope I won't end up having to revert all of this, because this does have a big coolness factor: since it's now easy to check if rationals
are integers, I can also implement bitwise operators for example, and because the library lets me pick the precision at runtime for each value,
I can in theory have the user enter the desired output precision. Assuming I do have time for that anyways.

Time spent this week: roughly 10 hours.

### Next steps

Looks like the rest of the course will be spent finishing the integration, and importantly, getting tests back in. I'm currently not yet at a state
where uncommenting the tests makes sense, but that is absolutely a high priority not just because tests are mandated by the course, but because I'm 
having bugs that would've been caught by the tests.
