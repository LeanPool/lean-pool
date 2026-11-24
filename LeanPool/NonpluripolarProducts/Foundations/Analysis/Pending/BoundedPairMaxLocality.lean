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
  obtain ⟨U, -, hUrc, hUabs⟩ := exists_exhaustion Ω
  have hUΩ (m : ℕ) : U m ≤ Ω := subset_closure.trans (hUrc m).2
  have hQ : {z | z ∈ Ω ∧ ∀ i, g i z < u i z} =
      ⋃ m, {z | z ∈ U m ∧ ∀ i, g i z < u i z} := by
    ext z
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨hzΩ, hz⟩
      obtain ⟨m, hm⟩ := hUabs {z} isCompact_singleton (singleton_subset_iff.2 hzΩ)
      exact ⟨m, hm rfl, hz⟩
    · rintro ⟨m, hzm, hz⟩
      exact ⟨hUΩ m hzm, hz⟩
  rw [hQ, Measure.restrict_iUnion_congr]
  intro m
  set V := U m
  set P := {z | z ∈ V ∧ ∀ i, g i z < u i z}
  have hPV : P ⊆ V := fun z hz ↦ hz.1
  choose J hJ using fun i ↦ HolomorphicPullback.exists_decreasingMollifierApproximation (hg i)
    (hUrc m)
  have hgV (i : Fin n) : IsDecApprox V (g i) (J i) :=
    isDecApprox_of_isDecreasingApproximation (hg i) (hUΩ m) (hJ i)
  have hfinV (ρ : Measure (ComplexModel n)) (hρ : ∀ K, IsCompact K → K ⊆ Ω → ρ K < ⊤) :
      ∀ K, IsCompact K → K ⊆ V → ρ K < ⊤ := fun K hK hKV ↦ hρ K hK (hKV.trans (hUΩ m))
  obtain ⟨F, hF, hFT⟩ := hμ.2.2 V (hUrc m)
  obtain ⟨μV, -, hμVf, hμVT⟩ := pClaim_all (n := n) V u
  have e1 : μ.restrict V = μV.restrict V :=
    restrict_eq_of_testFunction_integral_eq (hfinV μ hμ.2.1) hμVf fun φ ↦
      tendsto_nhds_unique (hFT φ φ.continuous φ.hasCompactSupport φ.tsupport_subset)
        (hμVT F hF φ φ.continuous φ.hasCompactSupport φ.tsupport_subset)
  obtain ⟨G, hG, hGT⟩ := hν.2.2 V (hUrc m)
  have hG' : IsAdmissible n V (maxTupleObstacle u g n) G := by
    refine ⟨fun i ↦ (hG.1 i).congr fun z hz ↦ ?_, fun i hi ↦ absurd i.isLt (not_lt.mpr hi)⟩
    simpa [maxTupleObstacle] using hmax i (hUΩ m hz)
  obtain ⟨νV, hνVc, hνVf, hνVT⟩ := pClaim_all (n := n) V (maxTupleObstacle u g n)
  have e2 : ν.restrict V = νV.restrict V :=
    restrict_eq_of_testFunction_integral_eq (hfinV ν hν.2.1) hνVf fun φ ↦
      tendsto_nhds_unique (hGT φ φ.continuous φ.hasCompactSupport φ.tsupport_subset)
        (hνVT G hG' φ φ.continuous φ.hasCompactSupport φ.tsupport_subset)
  have hchain := restrict_eq_joint_maxTuple hgV hμVf hμVT ⟨F, hF⟩ n le_rfl νV hνVc hνVf hνVT
  rw [← Measure.restrict_restrict_of_subset hPV, e2, Measure.restrict_restrict_of_subset hPV,
    hchain, ← Measure.restrict_restrict_of_subset hPV, ← e1,
    Measure.restrict_restrict_of_subset hPV]

end SGPT.Foundations.Analysis.Pending.BoundedPairMaxLocality
