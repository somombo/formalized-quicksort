# Formalized Quicksort

Implementation and Formal Verification of the Quicksort Algorithm

## Usage

Add the following

```lean
require quicksort from git "https://github.com/somombo/formalized-quicksort" @ "main"
```

to your `lakefile.lean` and then import and use the `qs` function in your code like:

```lean
import Quicksort

#eval qs #[9, 3, 1, 8, 6, 2, 5, -0, 7, 4] 
-- Result> #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9] : Array Int
```

## Formal Verification

This project formally verifies several key properties of the implemented quicksort algorithm:

- **Termination**: The function is guaranteed to always finish processing any input list, preventing infinite loops.
- **Correctness**: The function reliably sorts the input list, ensuring the output is a permutation (each element appears only once) and is monotonically ordered (elements are in the desired order).
- **Memory Safety**: The function operates within the valid bounds of the input array, eliminating potential out-of-bounds errors that could cause crashes. This is achieved by proving the operations are safe beforehand, effectively performing static bounds checking.
- **Customizable Pivoting**: While a default "arithmetic average" pivot selection is provided, the user can define their custom pivotFactory function. This allows users to explore alternative pivot selection strategies that might be more efficient for their specific use case, as long as they meet the established validity criteria for pivots.

These guarantees are achieved through rigorous theorem proving within Lean 4. We created definitions and stated theorems that formally capture these desired properties and then prove them using various logical reasoning techniques. This approach provides a high level of confidence in the correctness and reliability of the implemented quicksort algorithm.