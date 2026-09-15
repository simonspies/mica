# Sorting

Sorting algorithms, each verified at three levels. **Safety** uses a shared
`int array`, which exposes only its length in specifications: the verified
property is that every read, write, and swap index stays in bounds.
**Correctness** uses an owned array (`[@owned]`), whose contents the
specification binds as an `int vec`, and the postcondition states that the
final contents are sorted. **List** sorts an immutable `int list`, and the
postcondition states that the result is sorted, with a recursive specification
function over adjacent elements.

| Algorithm | Safety | Correctness | List |
|---|---|---|---|
| `bubblesort.ml` | ✓ | ✓ | ✓ |
| `insertionsort.ml` | ✓ | ✓ | ✓ |
| `mergesort.ml` | ✓ | ✓ | ✓ |
| `quicksort.ml` | ✓ | ✓ | ✓ |
| `selectionsort.ml` | ✓ | ✓ | ✓ |

Heapsort lives with the binary min-heap in `../heap.ml`, safety only. No
example states that its result is a permutation of its input.
