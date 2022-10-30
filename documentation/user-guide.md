## User guide

The prebuilt releases can be found [here](https://github.com/kbjakex/tiralab-calculator/releases). Alternatively, here are the steps to build & run the program yourself:

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
type `cargo +nightly llvm-cov --html --ignore-filename-regex tui`. It'll show where the HTML was generated, but generally, it'll be under `<project>/target/llvm-cov/`. Note: `+nightly` is _required_ because `no_coverage` is not in stable yet.


### Calculator usage

Once open, the calculator will be waiting for input. There are currently three types of inputs:
1. Direct evaluation: type any expression with no unknowns, and it will be evaluated. For example: `2 * (3 - 4) + 1`, or `3a + b` if `a` and `b` have been defined.
2. Variable declaration: to declare a variable, use the syntax `variableName = value`. For example: `a = 7`, `b = 5`, `k = 3a + b`. `k` will now have the value 26.
3. Function declarations: to declare a function, use the syntax `functionName(a, b, c, ...) = value`. For example: `f() = 5`, `g(x) = -3x`, `h(a,b) = 3a + b`. Now `h(16 - f(3), f())` will output 26.

Variables and functions can be overridden by using the same name again. **Note**: multiple functions with the same name but different number of parameters
is not supported, and so `f() = 5` followed by `f(x) = 2x` will make `f()` (without parameters) invalid.

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

## Features

* Input can be entered as base10, binary (with the `0b` prefix) or hexadecimal (with the `0x` prefix).
* Output format can be changed with the `dec()`, `bin()` and `hex()` functions; for example, `hex(0b110101)` will print `0x35`.
* There are 4 built-in constants defined: `pi`/`π`, `phi`/`ϕ`, `tau` (2π) and `e`.
* There are 23 built-in functions:
  * `sqrt(x)`, `cbrt(x`)
  * `sin(x)`, `cos(x)`, `tan(x)` (x in radians)
  * `asin(x)`/`arcsin(x)`, `acos(x)`/...
  * `exp(x)`
  * `ln(x)`, `log10(x)`, `log2(x)`
  * `gcd(a, b)`, `lcm(a,b)` (greatest common divisor & lowest common multiple)
  * `abs(x)`
  * `floor(x)`, `round(x)`, `ceil(x)`
  * `frac(x)` (fractional part)
  * `int(x)` (truncation)
  * `min(...)`, `max(...)`, `avg(...)` (each take an arbitrary number of parameters)
* Imaginary numbers can be entered with the `i` constant; for example, `2 + 3i` or `1 - i`. They can alternatively be acquired with functions or operators that can result in complex numbers, such as `sqrt(-1)`.
* Functions can be defined with the synax `functionName(parameters) = definition`; for example, `f(x, y) = cos(x + y) + i * sin(x + y)`.
* Variables can be defined with the syntax `variableName = value`. Note that changing the value of a variable will not update the values already computed using the previous value of the variable.
* Available operators are: `+`, `-`, `*`, `/` (division),`%` (remainder), `^` (exponentiation), `<`, `>`, `<=`, `>=`, `==` (equal to), `!=` (not equal to), `<<` (bit left shift), `>>` (bit right shift), `&` (bit and), `&&` (logical and), `|` (bit or), `||` (logical or), `xor`, and `!` (not).

  Not all operators can be used with every type; this was mainly driven by what the underlying number library implemented.
* Bit operators (`&`, `|`, `xor`, `<<`, `>>`) can be used with integers only. Rounding functions (`floor()`, `round()`, `ceil()`) or truncation (`int()`) can be used to convert to an integer as necessary, though integer inputs will already work as is. (Internally, integers are represented as rationals with denominator of 1)
