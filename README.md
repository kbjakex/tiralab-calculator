[![codecov](https://codecov.io/gh/kbjakex/tiralab-calculator/branch/main/graph/badge.svg?token=61DBA3W6JW)](https://codecov.io/gh/kbjakex/tiralab-calculator)
# tiralab-calculator
A scientific calculator University project

<img src="https://raw.githubusercontent.com/kbjakex/tiralab-calculator/main/documentation/images/calculator.png" width="300">

For the peer reviews: feel free to reach out for any questions or concerns or such on Discord - PM jetp250#8243 through [The Programmer's Hangout](https://discord.gg/programming).

### Project status

The project is over halfway done. You can evaluate expressions such as `(2 - 3) / (4 - 5) * 13 + 4` and declare and use variables and functions. Input validation is quite good now and error messages more specific. The only major missing feature is unary operator support, but after that, all that remains to be done is add built-in constants/functions, improve error messages, add more operators and improve testing & code quality.

### Rust version

I develop on the latest nightly and update fairly regularly, but there is a good chance the code works on the latest stable as well.
Use `rustup toolchain install nightly` to add the nightly toolchain and `cargo run +nightly` to run as nightly, if necessary.

### Code coverage

Code coverage is automatically generated using GitHub Actions, and can be viewed for the latest commit [here](https://app.codecov.io/gh/kbjakex/tiralab-calculator).

### Tests

To run the tests, the only precursor is having Rust itself installed. Run `cargo test` to run the tests.

The tests are contained within the same file as the contents they test, at the bottom, as is common.

### Linting

For linting, I'm using [Clippy](https://github.com/rust-lang/rust-clippy). Run with `cargo clippy`. 
