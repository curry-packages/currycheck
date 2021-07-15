CurryCheck - A Property Testing Tool for Curry
==============================================

This package contains the tool `curry-check` that supports
the automation of testing Curry programs.
The tests to be executed can be unit tests as well as
property tests parameterized over some arguments.
The tests can be part of any Curry source program
and, thus, they are also useful to document the code.
The basic ideas of CurryCheck are described in a
[LOPSTR 2016 paper](http://dx.doi.org/10.1007/978-3-319-63139-4_13).

In addition to the functionality of other property-based tools,
like [QuickCheck](https://en.wikipedia.org/wiki/QuickCheck),
CurryCheck tests also
[specifications and contracts in Curry programs](http://dx.doi.org/10.1007/978-3-642-27694-1_4),
[determinism properties of operations](http://dx.doi.org/10.1007/978-3-319-51676-9_1),
[equivalence of operations](http://dx.doi.org/10.1007/978-3-319-90686-7_10),
and performs some source code analysis to check the correct usage
of some Curry features, like
[set functions](http://doi.acm.org/10.1145/1599410.1599420),
[default rules](http://doi.org/10.1017/S1471068416000168),
or primitives to implement
[functional patterns](https://doi.org/10.1007/11680093_2).
Thus, it is recommended to use CurryCheck regularly
when developing Curry programs.


Installing CurryCheck
---------------------

The tool can be directly installed by the command

    > cypm install currycheck

This installs the executable `curry-check` in the bin directory of CPM.


Using CurryCheck
----------------

If the bin directory of CPM (default: `~/.cpm/bin`) is in your path,
execute the tool with the module containing the properties, e.g.,

    > curry-check Nats


Examples
--------

The directory `examples` of this package contains
various example programs to demonstrate the functionality
of CurryCheck. It also contains the following subdirectories
with specific examples:

* `equivalent_operations`: Examples to check the semantic equivalence
  of operations as described in the
  [FLOPS 2018 paper](http://dx.doi.org/10.1007/978-3-319-90686-7_10).
* `withVerification`: Examples to demonstrate the combination of
  testing and verification.
* `illegal_programs`: Some programs showing unindented uses of
  Curry features that are detected by CurryCheck.
