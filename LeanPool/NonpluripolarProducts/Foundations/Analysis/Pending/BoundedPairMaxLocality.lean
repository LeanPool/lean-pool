/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorMaxObstacle
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorGauge

/-! # Mixed maximum locality for arbitrary locally bounded PSH obstacles

The complete mathematical statements and entire proofs preceded this file.
ROOT13 is strictly excluded from the fixed C90 batch.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.BoundedPairMaxLocality

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere SmoothMax BedfordTaylor

variable {n : ℕ}

/-- Genuine original BT limits are local above arbitrary locally bounded PSH obstacles. -/
theorem restrict_eq_of_bounded_pair_max {Ω : Opens (ComplexModel n)}
    {u w g : Fin n → ComplexModel n → ℝ} {μ ν : Measure (ComplexModel n)}
    (hμ : IsBTLimit Ω u μ) (hν : IsBTLimit Ω w ν)
    (hg : ∀ i, IsLocallyBoundedPshOn Ω (g i))
    (hmax : ∀ i, EqOn (w i) (fun z ↦ max (u i z) (g i z)) Ω) :
    ν.restrict {z | z ∈ Ω ∧ ∀ i, g i z < u i z} =
      μ.restrict {z | z ∈ Ω ∧ ∀ i, g i z < u i z} := by
  refine restrict_eq_of_relativelyCompact_model (model := maxTupleObstacle u g n)
    {z | ∀ i, g i z < u i z} hμ.2.1 hν.2.1 hμ.2.2 hν.2.2 ?_ ?_
  · intro i z hz
    simpa [maxTupleObstacle] using hmax i hz
  · intro V hV μV νV hμVf hμVT hF hνVc hνVf hνVT
    choose J hJ using fun i ↦ HolomorphicPullback.exists_decreasingMollifierApproximation (hg i) hV
    have hgV (i : Fin n) : IsDecApprox V (g i) (J i) :=
      isDecApprox_of_isDecreasingApproximation (hg i) (subset_closure.trans hV.2) (hJ i)
    exact restrict_eq_joint_maxTuple hgV hμVf hμVT hF n le_rfl νV hνVc hνVf hνVT

end SGPT.Foundations.Analysis.Pending.BoundedPairMaxLocality
