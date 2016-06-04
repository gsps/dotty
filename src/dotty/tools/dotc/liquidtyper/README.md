LiquidTyper Readme
----------

This branch of Dotty introduces syntax and type checking for logically qualified base types in Scala.
An additional typer phase, the *LiquidTyper*, tabulates subtyping relations among such qualified types and discharges
the proof obligations using an SMT solver.

Be aware that LiquidTyper is currently under active development and in an experimental state.
There are, however, several examples that demonstrate the extension of Scala's capabilities already supported.
To run them,
* First, obtain a packaged copy of [Leon](https://github.com/epfl-lara/leon) by cloning the project
    and running `sbt package` in its root,
* Get a copy of *this* Dotty branch,
* Move the `leon_2.11-3.0.jar` produced in step one to the `lib/` sub-directory of the Dotty root,
* Compile Dotty (`sbt compile`),
* Make sure that [Z3](https://github.com/Z3Prover/z3) is available on the $PATH of your system, and finally
* Run the tests using `sbt testOnly *liquidtyper*`.
