# Formalized Quicksort

Implementation and Formal Verification of the Quicksort Algorithm

## Usage

Add the following to your `lakefile.lean`:
```lean
require quicksort from git "https://github.com/somombo/formalized-quicksort" @ "main"
```

or to your `lakefile.toml`:
```toml
[[require]]
name = "quicksort"
git = "https://github.com/somombo/formalized-quicksort"
rev = "main"
```

and then import and use the `qs` function in your code like:

```lean
import Quicksort

#eval qs #[9, 3, 1, 8, 6, 2, 5, -0, 7, 4] 
-- Result> #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9] : Array Int
```

## Formal Verification

This project formally verifies several key properties of the implemented quicksort algorithm:

- **Termination**: The function is guaranteed to always finish processing any input list, preventing infinite loops.
- **Memory Safety**: The function operates within the valid bounds of the input array, eliminating potential out-of-bounds errors that could cause crashes. This is achieved by proving the operations are safe beforehand, effectively performing static bounds checking.
- **Correctness**: The function reliably sorts the input list, ensuring the output is a permutation (each element appears only once) and is monotonically ordered (elements are in the desired order).
- **Customizable Paritioning**: While a default partitioning algorithm is provided for partitioning the input array, users have the option to define their own custom partitioning schemes. This flexibility allows users to investigate alternative partitioning strategies that may be more efficient for their particular use case. We establish Lawful partitioning schemes as those that terminate, are memory safe, and correctly partition elements around a pivot.

These guarantees are achieved through rigorous theorem proving within Lean 4. We created definitions and stated theorems that formally capture these desired properties and then prove them using various logical reasoning techniques. This approach provides a high level of confidence in the correctness of the implemented quicksort algorithm.