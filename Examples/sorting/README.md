# Sorting

Sorting algorithms over `int array`s, each verified at one of two levels.
**Safety** uses a shared array, which exposes only its length in
specifications: the verified property is that every read, write, and swap index
stays in bounds. **Correctness** uses an owned array (`[@owned]`), whose
contents the specification binds as an `int vec`, and the postcondition states
that the final contents are sorted. A dash is work not done, not a property 
known to fail.

| Algorithm | Safety | Correctness |
|---|---|---|
| `bubblesort.ml` | ✓ | — |
| `insertionsort.ml` | ✓ | ✓ |
| `mergesort.ml` | ✓ | — |
| `quicksort.ml` | ✓ | ✓ |
| `selectionsort.ml` | ✓ | ✓ |

Heapsort lives with the binary min-heap in `../heap.ml`, safety only. No
example states that its result is a permutation of its input; that needs
multiset equality over vector contents.
