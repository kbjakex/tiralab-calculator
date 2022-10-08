## User guide

I'll try to have a release ready for the next peer review, but otherwise, here are the steps to run the program.

1. Install the Rust language if not already installed. Installation instructions can be found from the [official website](https://www.rust-lang.org/learn/get-started).
(Should be a very painless process!)
3. Verify your installation works by running `cargo --verson`. It should show `cargo 1.64.0` or newer.
4. Clone the project with `git clone https://github.com/kbjakex/tiralab-calculator && cd tiralab-calculator`
5. Run `cargo run --release`

#### Tests
To run the tests, type `cargo tests`.

#### Code coverage
To run the code coverage evaluation yourself, you'll have to first install the `cargo-llvm-codecov` tool with the following:
```
cargo install cargo-llvm-cov
```
Then (once that has finished compiling), within the project directory, run `cargo llvm-cov`. If `cargo-llvm-codecov` was just installed, it'll probably 
prompt you to install the tools it requires to run - type `yes`.

To generate a HTML report, which lets you visually see which lines have been tested (probably an easy way to find flaws in my testing!...),
type `cargo llvm-cov --html`. It'll show where the HTML was generated, but generally, it'll be under `<project>/target/llvm-cov/`.


### Calculator usage

Once open, the calculator will be waiting for input. There are currently three types of inputs:
1. Direct evaluation: type any expression with no unknowns, and it will be evaluated. For example: `2 * (3 - 4) + 1`, or `3a + b` if `a` and `b` have been defined.
2. Variable declaration: to declare a variable, use the syntax `variableName = value`. For example: `a = 7`, `b = 5`, `k = 3a + b`. `k` will now have the value 26.
3. Function declarations: to declare a function, use the syntax `functionName(a, b, c, ...) = value`. For example: `f() = 5`, `g(x) = -3x`, `h(a,b) = 3a + b`. Now `h(16 - f(3), f())` will output 26.

Variables and functions can be overridden by using the same name again. **Note**: multiple functions with the same name but different number of parameters
is not (currently?) supported, and so `f() = 5` followed by `f(x) = 2x` will make `f()` (without parameters) invalid.

Example of use:
```console
> 2 + 3
5
> f(x) = 2x + 3
Defined function 'f'!
> g(x, y) = (f(x) + f(y)) / (f(x) - f(y))
Defined function 'g'!
> f(-0.5)
2
> g(-1, 7)
-0.375
> k = 1/3
k = 0.333333333333
> f(x) = k*x
Updated function 'f'!
> f(27)
9
> f(f(f(f(27))))
0.3333333333333333
```
