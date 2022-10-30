### Testing

The online code coverage report can be found [here (codecov.io)](https://app.codecov.io/gh/kbjakex/tiralab-calculator). 
The site includes a visual summary.

Testing the program is fairly trivial, given the nature of the input and the outputs. The program is hand-tested from the command line 
after any changes in behavior with correct and incorrect inputs, supplementing the unit tests which currently do not cover the user interface code.

The code has been written with unit testing of the user interface in mind as well (simply by extracting all of the logic to a function taking simply the
current calculator state, and the input string, as parameters), and some full-program unit testing is done to complement manual tests.