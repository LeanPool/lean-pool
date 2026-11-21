/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Reduction.NormalFormE

/-!
# Irreducible and "no cut" (pages 73, 77-79)

Lafont 1997, page 73: a net is irreducible when no interaction applies; page 77: a cut is a pair
of cells joined by their principal ports. Page 79: "An irreducible net is not necessarily
reduced, since it may contain irreducible cuts". A net without a cut is always irreducible
(`StepE.Normal.of_not_hasCut`). The converse holds when every pair of symbols has a rule in one
order or the other, as for the combinators.

Contents, in the order of the file:

1. Main result for a general system: `StepE.Normal.iff_not_hasCut`, in a system with a rule for
   every pair of symbols, irreducible is "no cut".
2. The instance for the combinators: `Comb.system_complete`, the combinators have a rule for
   every pair of symbols, in one order or the other; `Comb.normal_iff_not_hasCut`, for the
   combinators, irreducible is "no cut".
-/

@[expose] public section

namespace INet

variable {S : Signature}

-- ============================================================================================
-- 1. Main result: irreducible is "no cut" in a complete system
-- ============================================================================================

/-- **Irreducible is "no cut" in a complete system** (Lafont 1997, pages 73 and 77; pages 77-78:
an irreducible cut is a cut without a rule). If every pair of symbols has a rule in one order or
the other, a net is irreducible exactly when it has no cut. -/
theorem StepE.Normal.iff_not_hasCut
    -- the system: every pair of symbols has a rule, in one order or the other
    {I : System S}
    (hI : ∀ α β, (I.rule α β).isSome ∨ (I.rule β α).isSome)
    -- the net
    {N : Net S ℕ} :
    -- no interaction applies to the net exactly when it has no cut
    StepE.Normal I N ↔ ¬ N.HasCut :=
  ⟨fun h hc => (Net.HasCut.stepE hI hc).elim h, StepE.Normal.of_not_hasCut⟩

namespace Comb

-- ============================================================================================
-- 2. The instance for the combinators
-- ============================================================================================

/-- **The combinators are complete** (Lafont 1997, page 81, Fig. 2): every pair of symbols among
`con`, `dup`, `era` has a rule, in one order or the other. -/
theorem system_complete :
    -- for every pair of symbols, a rule in one order or the other
    ∀ α β : sig.Sym, (system.rule α β).isSome ∨ (system.rule β α).isSome := by
  intro α β
  cases α <;> cases β <;> first | exact Or.inl rfl | exact Or.inr rfl

/-- **For the combinators, irreducible is "no cut"** (Lafont 1997, pages 73 and 77, with the rules
of Fig. 2, page 81). -/
theorem normal_iff_not_hasCut
    -- a net of combinators
    {N : Net sig ℕ} :
    -- no interaction applies to the net exactly when it has no cut
    StepE.Normal system N ↔ ¬ N.HasCut :=
  StepE.Normal.iff_not_hasCut system_complete

end Comb

end INet
