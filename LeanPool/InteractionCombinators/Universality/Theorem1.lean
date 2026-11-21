/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Universality.General.CodeCompatible

/-!
# Lafont, "Interaction Combinators" (1997): Theorem 1

The target of this project, proved. The statements are those fixed before any proof was written;
the proofs are `universal'` and `universal_strict'` of `Universality/General/CodeCompatible.lean`,
by the translation of Fig. 10.

Contents, in the order of the file:

1. Main results: `universal`, Theorem 1 of the paper, and `universal_strict`, the same with a
   strict translation.
-/

@[expose] public section

namespace INet.Comb

-- ============================================================================================
-- 1. Main results: Theorem 1
-- ============================================================================================

/-- **Theorem 1** (Lafont 1997, stated on page 82; its proof ends on page 90). Any interaction
system can be translated into the system of interaction combinators. -/
theorem universal :
    -- the system of `con`, `dup` and `era` is universal: every interaction system over a finite
    -- alphabet has a translation into it (`Universal`, in `Core/Translation.lean`)
    Universal system :=
  universal'

/-- The form of Theorem 1 this project aimed at: the translation is strict. It implies `universal`
by `StrictlyUniversal.universal`. Lafont's translation has a cell at the root of every symbol
(Fig. 6 and Fig. 10), so it is strict. -/
theorem universal_strict :
    -- the system of `con`, `dup` and `era` is strictly universal: every interaction system over
    -- a finite alphabet has a translation into it that sends no symbol to a single wire
    -- (`StrictlyUniversal`, in `Core/Translation.lean`)
    StrictlyUniversal system :=
  universal_strict'

end INet.Comb
