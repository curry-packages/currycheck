Equivalence checking with CurryCheck
====================================

This directory contains some examples for the use
of CurryCheck to check the equivalence of operations.

Since most of these are examples to test whether CurryCheck
is able to report counter-examples, their test fails intentionally.
These are the programs
- BacciEtAl12 (simple example from Bacci et al PPDP'12)
- Intersperse (inserting separators in a list [Christiansen/Seidel'11])
- Ints12 (generators for infinite lists)
- MultBin (multiplication on a binary representation of natural numbers)
- MultPeano (multiplication on Peano numbers)
- NDInsert (non-deterministic list insertion)
- Perm (permutation from library Combinatorial vs. less strict version)
- Primes (computing an infinite list of all prime numbers)
- RevRev (double reverse)
- SortEquiv (two variants of permutation sort)
- SortPermute (two variants of permutation sort with a stricter permutation)
- Take (two variants of take [Foner/Zhang/Lampropoulos'18])
- Unzip (two variants of unzip [Chitil'11])

The following programs contain successful equivalence tests:
- Fac (recursive specification of factorial vs. iterative implementation)
- SelectionSort
- SortISortEquiv
