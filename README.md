[![codecov](https://codecov.io/gh/kbjakex/tiralab-calculator/branch/main/graph/badge.svg?token=61DBA3W6JW)](https://codecov.io/gh/kbjakex/tiralab-calculator)
# tiralab-calculator
A scientific calculator University project

<img src="https://raw.githubusercontent.com/kbjakex/tiralab-calculator/main/documentation/images/calculator.png" width="550">

### Documentation

[Project definition](https://github.com/kbjakex/tiralab-calculator/blob/main/documentation/definition.md)

[User guide](https://github.com/kbjakex/tiralab-calculator/blob/main/documentation/user-guide.md)

### Project status

The project is done. Type system is integrated & tested, all planned operators are there, most important functions are there,
constants are there, the user interface is polished, a _lot_ of testing (both unit and manual) has been done.

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
