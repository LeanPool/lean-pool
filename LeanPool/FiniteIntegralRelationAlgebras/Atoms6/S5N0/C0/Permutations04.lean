/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

/-! Batch 4 of permutations for the symmetry certificate. -/

@[expose] public section

namespace RACert.S5N0.C0

/-- High-variable permutations in batch 4. -/
def permutations4 : List (List Nat × List Nat) :=
  [
    ([9, 3, 6, 4, 7, 0, 5, 8, 1, 2], [5, 8, 9, 1, 3, 6, 2, 4, 7, 0]),
    ([9, 3, 6, 5, 8, 1, 4, 7, 0, 2], [8, 5, 9, 1, 6, 3, 2, 7, 4, 0]),
    ([9, 4, 7, 3, 6, 0, 5, 8, 2, 1], [5, 9, 8, 3, 1, 6, 4, 2, 7, 0]),
    ([9, 4, 7, 5, 8, 2, 3, 6, 0, 1], [8, 9, 5, 6, 1, 3, 7, 2, 4, 0]),
    ([9, 5, 8, 3, 6, 1, 4, 7, 2, 0], [9, 5, 8, 3, 6, 1, 4, 7, 2, 0]),
    ([9, 5, 8, 4, 7, 2, 3, 6, 1, 0], [9, 8, 5, 6, 3, 1, 7, 4, 2, 0]),
    ([9, 6, 3, 7, 4, 0, 8, 5, 1, 2], [5, 8, 9, 2, 4, 7, 1, 3, 6, 0]),
    ([9, 6, 3, 8, 5, 1, 7, 4, 0, 2], [8, 5, 9, 2, 7, 4, 1, 6, 3, 0]),
    ([9, 7, 4, 6, 3, 0, 8, 5, 2, 1], [5, 9, 8, 4, 2, 7, 3, 1, 6, 0]),
    ([9, 7, 4, 8, 5, 2, 6, 3, 0, 1], [8, 9, 5, 7, 2, 4, 6, 1, 3, 0]),
    ([9, 8, 5, 6, 3, 1, 7, 4, 2, 0], [9, 5, 8, 4, 7, 2, 3, 6, 1, 0]),
    ([9, 8, 5, 7, 4, 2, 6, 3, 1, 0], [9, 8, 5, 7, 4, 2, 6, 3, 1, 0])]

end RACert.S5N0.C0
