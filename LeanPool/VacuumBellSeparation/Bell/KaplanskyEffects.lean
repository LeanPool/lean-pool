/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.StrongApproximationNets
public import LeanPool.VacuumBellSeparation.Bell.EffectResolventParameter
public import LeanPool.VacuumBellSeparation.Bell.RationalResolventStrong

/-!
# Bounded effect approximation from the double commutant

For a unital star algebra stable under real continuous functional calculus,
every effect in its double commutant is a strong limit of actual effects in
the algebra. Directed unions of von Neumann algebras satisfy the stability
condition by the proved same-stage CFC lemma. No density or approximation
existence theorem is assumed.
-/

@[expose] public section

namespace VacuumBellSeparation

open Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_scaled_effect_strong_approximation
    (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (hfc : ∀ (f : ℝ → ℝ) (A : H →L[ℂ] H), A ∈ S → cfc f A ∈ S)
    {E : H →L[ℂ] H} (hE : E ∈ generatedVNA (S : Set (H →L[ℂ] H)))
    (hE0 : 0 ≤ E) (hE1 : E ≤ 1) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    ∃ Es : (Finset H × ℕ) → (H →L[ℂ] H),
      (∀ i, Es i ∈ S ∧ 0 ≤ Es i ∧ Es i ≤ 1) ∧
        ∀ x : H, Tendsto (fun i => Es i x) atTop (𝓝 ((r • E) x)) := by
  let B := effectResolventParameter r E
  have hB : B ∈ generatedVNA (S : Set (H →L[ℂ] H)) := effectResolventParameter_mem _ hE r
  have hsa : IsSelfAdjoint B := effectResolventParameter_isSelfAdjoint r E
  obtain ⟨As, hAs, hstrong⟩ := exists_selfAdjoint_strong_approximation S hB hsa
  refine ⟨fun i => 1 - quadraticResolvent (As i), ?_, ?_⟩
  · intro i
    exact ⟨S.sub_mem S.one_mem (hfc _ _ (hAs i).1),
      one_sub_quadraticResolvent_effect (hAs i).2⟩
  · intro x
    have ht := one_sub_quadraticResolvent_strong_tendsto (fun i => (hAs i).2) hsa hstrong x
    simpa only [B, one_sub_quadraticResolvent_effectResolventParameter hE0 hE1 hr hr1] using ht

/-- Tuples obtained by applying one positive contraction in the algebra to the given vectors. -/
def effectTupleSet (S : StarSubalgebra ℂ (H →L[ℂ] H)) {ι : Type*}
    (x : ι → H) : Set (PiLp 2 (fun _ : ι => H)) :=
  {y | ∃ E ∈ S, 0 ≤ E ∧ E ≤ 1 ∧ WithLp.toLp 2 (fun i => E (x i)) = y}

/-- The limiting scalar factor is removed in the actual finite tuple norm. -/
theorem effect_bicommutant_tuple_mem_closure
    (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (hfc : ∀ (f : ℝ → ℝ) (A : H →L[ℂ] H), A ∈ S → cfc f A ∈ S)
    {E : H →L[ℂ] H} (hE : E ∈ generatedVNA (S : Set (H →L[ℂ] H)))
    (hE0 : 0 ≤ E) (hE1 : E ≤ 1) {ι : Type*} [Finite ι] (x : ι → H) :
    WithLp.toLp 2 (fun i => E (x i)) ∈ closure (effectTupleSet S x) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  have hscaled (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
      WithLp.toLp 2 (fun i => (r • E) (x i)) ∈ closure (effectTupleSet S x) := by
    obtain ⟨Es, hEs, hstrong⟩ := exists_scaled_effect_strong_approximation S hfc hE hE0 hE1 hr hr1
    have ht : Tendsto (fun j => WithLp.toLp 2 (fun i => Es j (x i))) atTop
        (𝓝 (WithLp.toLp 2 (fun i => (r • E) (x i)))) :=
      (PiLp.continuous_toLp 2 (fun _ : ι => H)).continuousAt.tendsto.comp
        (tendsto_pi_nhds.mpr (fun i => hstrong (x i)))
    exact mem_closure_of_tendsto ht (Eventually.of_forall (fun j =>
      ⟨Es j, (hEs j).1, (hEs j).2.1, (hEs j).2.2, rfl⟩))
  have hc : Continuous (fun r : ℝ => WithLp.toLp 2 (fun i => (r • E) (x i))) := by
    fun_prop
  have ht : Tendsto (fun r : ℝ => WithLp.toLp 2 (fun i => (r • E) (x i))) (𝓝[<] 1)
      (𝓝 (WithLp.toLp 2 (fun i => E (x i)))) := by
    simpa only [one_smul] using (hc.tendsto 1).mono_left nhdsWithin_le_nhds
  apply isClosed_closure.mem_of_tendsto ht
  have hp : ∀ᶠ r : ℝ in 𝓝[<] 1, 0 < r :=
    (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hp, self_mem_nhdsWithin] with r hr hr1
  exact hscaled r hr.le hr1

theorem effect_bicommutant_approximate_finite_family
    (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (hfc : ∀ (f : ℝ → ℝ) (A : H →L[ℂ] H), A ∈ S → cfc f A ∈ S)
    {E : H →L[ℂ] H} (hE : E ∈ generatedVNA (S : Set (H →L[ℂ] H)))
    (hE0 : 0 ≤ E) (hE1 : E ≤ 1) {ι : Type*} [Finite ι] (x : ι → H)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ A ∈ S, 0 ≤ A ∧ A ≤ 1 ∧ ∀ i, ‖E (x i) - A (x i)‖ < ε := by
  let _ : Fintype ι := Fintype.ofFinite ι
  obtain ⟨y, ⟨A, hA, hA0, hA1, rfl⟩, hdist⟩ := Metric.mem_closure_iff.mp
    (effect_bicommutant_tuple_mem_closure S hfc hE hE0 hE1 x) ε hε
  exact ⟨A, hA, hA0, hA1, fun i => lt_of_le_of_lt (PiLp.norm_apply_le
    (WithLp.toLp 2 (fun i => E (x i)) - WithLp.toLp 2 (fun i => A (x i))) i)
      (by simpa only [dist_eq_norm] using hdist)⟩

theorem exists_effect_strong_approximation
    (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (hfc : ∀ (f : ℝ → ℝ) (A : H →L[ℂ] H), A ∈ S → cfc f A ∈ S)
    {E : H →L[ℂ] H} (hE : E ∈ generatedVNA (S : Set (H →L[ℂ] H)))
    (hE0 : 0 ≤ E) (hE1 : E ≤ 1) :
    ∃ Es : (Finset H × ℕ) → (H →L[ℂ] H),
      (∀ i, Es i ∈ S ∧ 0 ≤ Es i ∧ Es i ≤ 1) ∧
        ∀ x : H, Tendsto (fun i => Es i x) atTop (𝓝 (E x)) := by
  classical
  apply exists_strong_net_of_finite_approximation {A | A ∈ S ∧ 0 ≤ A ∧ A ≤ 1} E
  intro s ε hε
  obtain ⟨A, hA, hA0, hA1, hdist⟩ := effect_bicommutant_approximate_finite_family
    S hfc hE hE0 hE1 (fun x : s => (x : H)) hε
  exact ⟨A, ⟨hA, hA0, hA1⟩, fun x hx => hdist ⟨x, hx⟩⟩

end VacuumBellSeparation
