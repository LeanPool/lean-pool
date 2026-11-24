/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorIncreasingStepP
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorIncreasingStepW
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorIncreasingCollar
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.IncreasingTruncationReduction

/-!
# Bedford–Taylor convergence along increasing sequences

Let `u₁ʲ, …, uₙʲ` be sequences of locally bounded plurisubharmonic functions on an open
set `Ω ⊆ ℂⁿ`, each increasing and converging Lebesgue-almost everywhere to a locally
bounded plurisubharmonic `uᵢ`. Then the mixed Monge–Ampère measures
`ddᶜu₁ʲ ∧ ⋯ ∧ ddᶜuₙʲ` converge vaguely to `ddᶜu₁ ∧ ⋯ ∧ ddᶜuₙ`, and the same holds
after multiplying by an increasing sequence of weights (Bedford–Taylor; Błocki,
*The complex Monge–Ampère operator in pluripotential theory*, lecture notes, Thm 2.2.5).

The proof is Cegrell's, which avoids the Dirichlet problem: an induction on the number of
varying slots, whose steps are `incPClaim_succ` (integration by parts against smooth
tests), `incWClaim_of_collar` (localization to collared data on balls) and
`incWCollarClaim_succ` (quasi-continuity and the symmetric integration by parts).

The diagonal case is the input `BoundedIncreasingConvergence` of the semicontinuity
theorem for non-pluripolar measures in `Pending.IncreasingTruncationReduction`.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylor

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere

variable {n : ℕ}

/-- Both convergence claims hold at every level `q ≤ n`. -/
theorem incClaims_of_le : ∀ q : ℕ, q ≤ n → IncPClaim n q ∧ IncWClaim n q
  | 0, _ => ⟨incPClaim_zero, incWClaim_zero⟩
  | q + 1, h => by
    obtain ⟨hP, hW⟩ := incClaims_of_le q (Nat.le_of_succ_le h)
    have hq : q < n := h
    have hP' := incPClaim_succ hq hP hW
    exact ⟨hP', incWClaim_of_collar hP' (incWCollarClaim_succ hq hP' hW)⟩

/-- **Bedford–Taylor convergence along increasing sequences**, unweighted. -/
theorem incPClaim_all : IncPClaim n n := (incClaims_of_le n le_rfl).1

/-- **Bedford–Taylor convergence along increasing sequences**, with increasing weights. -/
theorem incWClaim_all : IncWClaim n n := (incClaims_of_le n le_rfl).2

end SGPT.Foundations.Analysis.Pending.BedfordTaylor

namespace SGPT.Foundations.Analysis.Pending.IncreasingTruncationLimit

open FirstPass FirstPass.MongeAmpere MongeAmpere BedfordTaylor

variable {n : ℕ}

/-- The diagonal Monge–Ampère measures `(ddᶜwⱼ)ⁿ` and `wⱼ (ddᶜwⱼ)ⁿ` of an increasing
sequence of locally bounded plurisubharmonic functions converge vaguely to those of the
almost-everywhere limit. -/
theorem boundedIncreasingConvergence (Ω : Opens (ComplexModel n)) :
    BoundedIncreasingConvergence Ω := by
  intro w W hw hW hmono hae χ hχ hχc hχΩ
  have hG : IsIncApprox Ω W w := isIncApprox_of_monotone_ae hW hw hmono hae
  have hadm : IsIncAdmissible n Ω (fun _ => W) (fun _ => w) :=
    ⟨fun _ => hW, fun _ => hG, fun i hi => absurd i.isLt (not_lt.mpr hi)⟩
  have hμs : ∀ j, IsBTLimit Ω (fun _ => w j) (canonicalBedfordTaylorMeasure Ω (w j) (hw j)) :=
    fun j => isBTLimit_canonicalBedfordTaylorMeasure (hw j)
  have hμ := isBTLimit_canonicalBedfordTaylorMeasure hW
  exact ⟨incPClaim_all Ω _ _ _ _ hadm hμs hμ χ hχ hχc hχΩ,
    incWClaim_all Ω _ _ _ _ hadm hμs hμ W w hW hG χ hχ hχc hχΩ⟩

end SGPT.Foundations.Analysis.Pending.IncreasingTruncationLimit

end
