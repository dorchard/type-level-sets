# v0.9.1.0
- Expanded test suite to cover README examples
- Added tests for Map union with Combine behavior
- Added tests for Set examples with Natural numbers
- Uses [rearrangements](https://github.com/finnbar/rearrangements) library to simplify the implementation.
- Migrated examples from explicit type annotations to `TypeApplications` syntax (e.g. `Var @"x"`).
- Updated to GHC 9.8

# v0.9.0.0
- GHC 9.2 support
- Add Elem typeclass to retrieve the value at a type in a set
- Fix Member typeclass (now returns False instead of failing to typecheck)
- Add some more examples, tests

# v0.8.9.0
- GHC 8.4 and 8.6 support.
- Fixed bug in the delete operation.
- Non-membership predicates
