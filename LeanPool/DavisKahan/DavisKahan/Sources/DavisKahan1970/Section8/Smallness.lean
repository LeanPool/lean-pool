/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module


public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section8.SelectedBranch

/-! # Smallness -/

@[expose] public section

open TauCeti.DavisKahan.Angle


/-!
# Davis--Kahan 1970, Theorem 8.2: explicit smallness bridges

The source theorem has two alternatives: small perturbation norm or small
residual norm.  The continuation library proves the branch conclusion once a
common contour has an explicit projection-Lipschitz coefficient below
`sqrt 2 / 2`.  The bridge records in this file package a printed half-gap
hypothesis together with that contour bound, which the caller supplies.

The bridges are a conditional route: they do not derive the contour bound from
the half-gap hypothesis.  The printed alternatives, in directed-gap form, are
proved without them by `theorem8_2_perturbationHalfGap_complex` and
`theorem8_2_residualHalfGap_complex` in `Section8/Theorem82Branch.lean`; the
residual one uses Krein's self-adjoint completion.
-/

namespace TauCeti
namespace DavisKahan1970
namespace Section8

open Set
open scoped InnerProductSpace
open DavisKahanExt
open TauCeti.DavisKahan

universe v w

section SmallnessBridges

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {F : Type w} [NormedAddCommGroup F] [NormedSpace ℂ F]
variable {A V : H →L[ℂ] H} {s : Set ℝ}

/-- Proof data converting the perturbation-norm half-gap condition in Theorem
8.2 into the quantitative common-contour condition already consumed by the
continuation stack. -/
structure PerturbationHalfGapBridge
    (C : SpectralContinuationWitness A V s) (delta : ℝ) : Prop where
  delta_pos : 0 < delta
  perturbation_small : ‖V‖ < delta / 2
  contour_selects_quarter_branch :
    selectedBranchProjectionLipschitzConstant C.contour V C.margin <
      Real.sqrt 2 / 2

/-- Caller-supplied data for the residual-norm alternative in Theorem 8.2: the
printed residual smallness of `R`, and a bound below `sqrt 2 / 2` on the
selected-branch Lipschitz constant of the witness contour for `V`.  No field
relates `R` to `V`.  The printed residual alternative is
`theorem8_2_residualHalfGap_complex`. -/
structure ResidualHalfGapBridge
    (C : SpectralContinuationWitness A V s)
    (R : F →L[ℂ] H) (delta : ℝ) : Prop where
  delta_pos : 0 < delta
  residual_small : ‖R‖ < delta / 2
  contour_selects_quarter_branch :
    selectedBranchProjectionLipschitzConstant C.contour V C.margin <
      Real.sqrt 2 / 2

/-- The selected-branch conclusion from the contour bound stored in the bridge.  The field
`perturbation_small` is not used: the caller supplies the contour bound when building `B`. -/
theorem theorem82_branch_of_perturbationHalfGapBridge
    (C : SpectralContinuationWitness A V s) {delta : ℝ}
    (B : PerturbationHalfGapBridge C delta) :
    SelectedBranchConclusion C :=
  selectedBranchConclusion_of_contour_bound C
    B.contour_selects_quarter_branch

/-- The selected-branch conclusion from the contour bound stored in the bridge.  The field
`residual_small` is not used: the caller supplies the contour bound when building `B`, and
no Krein replacement happens here. -/
theorem theorem82_branch_of_residualHalfGapBridge
    (C : SpectralContinuationWitness A V s)
    (R : F →L[ℂ] H) {delta : ℝ}
    (B : ResidualHalfGapBridge C R delta) :
    SelectedBranchConclusion C :=
  selectedBranchConclusion_of_contour_bound C
    B.contour_selects_quarter_branch

/-! This conditional layer stops here: the Section 7 theorem family
supplies the corresponding `sin(2 Theta)` inequalities, while these bridge
theorems add the strict selected-branch conclusion.  Keeping the two layers
separate prevents a generic proposition parameter from masquerading as the
source inequality. -/

end SmallnessBridges

end Section8
end DavisKahan1970
end TauCeti
