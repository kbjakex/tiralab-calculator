[![codecov](https://codecov.io/gh/kbjakex/tiralab-calculator/branch/main/graph/badge.svg?token=61DBA3W6JW)](https://codecov.io/gh/kbjakex/tiralab-calculator)
# tiralab-calculator
A scientific calculator University project

### Project status

Project is at an early stage and does not have meaningful functionality. Main functionality should hopefully be done by the next Saturday (24/9).

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
