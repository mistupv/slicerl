# slicerl: Slicing for Erlang

Now available [online][slicerl-kaz]!

## Installation

* **Requirement**: Erlang/OTP version 19.2.X (tested against 19.2.3). See [this issue][otp-3221] if you get an error with `hipe` in the stack trace.
* Place Erlang 19.2 in your PATH:
```
export PATH=/opt/erlang/19.2.3/bin:$PATH
```
* Generate a dialyzer PLT cache and set it as such:
```
make dialyzer
export DIALYZER_PLT=$PWD/.dialyzer_plt
```
* Compile the program
```
make
```

## Usage

**Important**: the variables set in the installation (`PATH` and `DIALYZER_PLT`) must be set before using the program.

Place the program you want to slice in a file, for example `program.erl` and run the following:

    ./slicerl -i program.erl -o sliced.erl -os 10 -oe 11

where `-os 10` and `-oe 11` tells the program the start and end position of the slicing criterion, respectively. The number represents the characters from the beginning of the file.

[slicerl-kaz]: https://kaz.dsic.upv.es/slicErlang.html
[otp-3221]: https://github.com/erlang/otp/issues/3221
