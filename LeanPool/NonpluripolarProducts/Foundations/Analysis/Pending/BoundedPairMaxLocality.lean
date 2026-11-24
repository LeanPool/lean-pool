/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.JointDecreasingMaxLocality
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

/-- Actual joint stages supply every intermediate maximum tuple. -/
theorem exists_isAdmissible_joint_maxTuple {U : Opens (ComplexModel n)}
    {u g : Fin n → ComplexModel n → ℝ} {F : Fin n → ℕ → ComplexModel n → ℝ}
    {J : Fin n → ℕ → ComplexModel n → ℝ}
    (hF : IsAdmissible n U u F) (hJ : ∀ i, IsDecApprox U (g i) (J i)) (k : ℕ) :
    ∃ F', IsAdmissible n U (maxTupleObstacle u g k) F' := by
  classical
  refine ⟨fun i ↦ if i.val < k then
    (fun j ↦ scaledSmoothMax (maxScale j) (F i j) (J i j)) else F i,
    fun i ↦ ?_, fun i hi ↦ absurd i.isLt (not_lt.mpr hi)⟩
  by_cases h : i.val < k
  · simpa [maxTupleObstacle, h] using
      JointDecreasingSmoothMax.isDecApprox_joint_scaledSmoothMax (hF.1 i) (hJ i)
  · simpa [maxTupleObstacle, h] using hF.1 i

/-- Finite-slot comparison on the original common strict-superlevel set. -/
theorem restrict_eq_joint_maxTuple {U : Opens (ComplexModel n)}
    {u g : Fin n → ComplexModel n → ℝ} {J : Fin n → ℕ → ComplexModel n → ℝ}
    (hJ : ∀ i, IsDecApprox U (g i) (J i))
    {μ : Measure (ComplexModel n)} (hμf : ∀ K, IsCompact K → K ⊆ U → μ K < ⊤)
    (hμ : ∀ F, IsAdmissible n U u F → TendstoMixed U F μ)
    (hex : ∃ F, IsAdmissible n U u F) :
    ∀ k, k ≤ n → ∀ μ' : Measure (ComplexModel n), μ' (U : Set (ComplexModel n))ᶜ = 0 →
      (∀ K, IsCompact K → K ⊆ U → μ' K < ⊤) →
      (∀ F, IsAdmissible n U (maxTupleObstacle u g k) F → TendstoMixed U F μ') →
      μ'.restrict {z | z ∈ U ∧ ∀ i, g i z < u i z} =
        μ.restrict {z | z ∈ U ∧ ∀ i, g i z < u i z} := by
  obtain ⟨F, hF⟩ := hex
  refine restrict_eq_of_tuple_steps (U := U) (P := {z | z ∈ U ∧ ∀ i, g i z < u i z})
    (S := fun i => {z | z ∈ U ∧ g i z < maxTupleObstacle u g i i z})
    (fun _ hz => hz.1) (maxTupleObstacle u g) (maxTupleObstacle_zero u g) ?_ hμf hμ ⟨F, hF⟩ ?_
  · intro i z hz
    exact ⟨hz.1, by rw [maxTupleObstacle_apply_self]; exact hz.2 i⟩
  · intro k hk μk μ' hμkc hμkf hμkT hμ'c hμ'f hμ'
    rw [maxTupleObstacle_succ u g hk] at hμ'
    exact JointDecreasingMaxLocality.restrict_eq_of_joint_max_slot
      (u := maxTupleObstacle u g k) ⟨k, hk⟩ (hJ ⟨k, hk⟩) hμkc hμkf hμkT hμ'c hμ'f hμ'
      (exists_isAdmissible_joint_maxTuple hF hJ k)

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
