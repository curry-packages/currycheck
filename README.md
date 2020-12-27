# CurryCheck - A Property Testing Tool for Curry

This package contains the tool `curry-check` that supports
the automation of testing Curry programs.
The tests to be executed can be unit tests as well as
property tests parameterized over some arguments.
The tests can be part of any Curry source program
and, thus, they are also useful to document the code.


## Installing the tool

The tool can be directly installed by the command

    > cypm install currycheck

This installs the executable `curry-check` in the bin directory of CPM.


## Using the tool

If the bin directory of CPM (default: `~/.cpm/bin`) is in your path,
execute the tool with the module containing the properties, e.g.,

    > curry-check Nats

