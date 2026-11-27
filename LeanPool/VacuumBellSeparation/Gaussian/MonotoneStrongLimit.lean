/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.PositiveTrace
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Decreasing positive bounded operators

The strong limit is constructed from Cauchy sequences on every Hilbert-space
vector. Positivity, the operator order and isometric compression pass to the
actual pointwise limit. This supplies the analytic limit step for singular
operator means, independently of any finite-dimensional spectral model.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap Filter
open scoped Topology

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- A positive operator controls its squared action by its quadratic form. -/
theorem norm_apply_sq_le_norm_mul_inner {A : E →L[ℂ] E} (hA : 0 ≤ A) (x : E) :
    ‖A x‖ ^ 2 ≤ ‖A‖ * (inner ℂ x (A x)).re := by
  have hnorm : ‖A x‖ ≤ ‖CFC.sqrt A‖ * ‖CFC.sqrt A x‖ := by
    conv_lhs => rw [← CFC.sqrt_mul_sqrt_self A hA]
    exact (CFC.sqrt A).le_opNorm _
  have hs : ‖CFC.sqrt A‖ ^ 2 = ‖A‖ := by
    rw [← (CFC.sqrt_nonneg A).isSelfAdjoint.norm_mul_self,
      CFC.sqrt_mul_sqrt_self A hA]
  calc
    ‖A x‖ ^ 2 ≤ (‖CFC.sqrt A‖ * ‖CFC.sqrt A x‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hnorm
    _ = _ := by rw [mul_pow, hs, sqrt_norm_sq_eq_diagonal hA]

omit [CompleteSpace E] in
/-- Loewner order is closed under pointwise norm convergence. -/
theorem operator_le_of_strong_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {A B : ι → E →L[ℂ] E} {C D : E →L[ℂ] E}
    (hA : ∀ x, Tendsto (fun i => A i x) l (𝓝 (C x)))
    (hB : ∀ x, Tendsto (fun i => B i x) l (𝓝 (D x)))
    (hAB : ∀ᶠ i in l, A i ≤ B i) : C ≤ D := by
  apply ContinuousLinearMap.le_def.mpr
  rw [isPositive_iff_complex]
  intro x
  have ht : Tendsto (fun i => inner ℂ ((B i - A i) x) x) l
      (𝓝 (inner ℂ ((D - C) x) x)) := (hB x |>.sub (hA x)).inner tendsto_const_nhds
  have he := hAB.mono fun i hi =>
    (isPositive_iff_complex (B i - A i)).mp (ContinuousLinearMap.le_def.mp hi) x
  have htre : Tendsto (fun i => (inner ℂ ((B i - A i) x) x).re) l
      (𝓝 (inner ℂ ((D - C) x) x).re) := Complex.continuous_re.continuousAt.tendsto.comp ht
  constructor
  · exact tendsto_nhds_unique (Complex.continuous_ofReal.continuousAt.tendsto.comp htre)
      (ht.congr' (he.mono fun _ h => h.1.symm))
  · exact ge_of_tendsto htre (he.mono fun _ h => h.2)

/-- A decreasing sequence of positive operators is Cauchy on each vector. -/
theorem cauchySeq_apply_of_antitone_nonneg (A : ℕ → E →L[ℂ] E)
    (hanti : Antitone A) (hpos : ∀ n, 0 ≤ A n) (x : E) :
    CauchySeq (fun n => A n x) := by
  let q : ℕ → ℝ := fun n => (inner ℂ x (A n x)).re
  have hqanti : Antitone q := by
    intro n m hnm
    have h := (ContinuousLinearMap.le_def.mp (hanti hnm)).re_inner_nonneg_right x
    simpa [q, inner_sub_right, sub_nonneg] using h
  have hqpos (n : ℕ) : 0 ≤ q n :=
    (nonneg_iff_isPositive.mp (hpos n)).re_inner_nonneg_right x
  have hqc : CauchySeq q := (tendsto_atTop_ciInf hqanti
    ⟨0, by rintro _ ⟨n, rfl⟩; exact hqpos n⟩).cauchySeq
  rw [Metric.cauchySeq_iff']
  intro ε hε
  let K : ℝ := ‖A 0‖ + 1
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hqc (ε ^ 2 / K) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hD : 0 ≤ A N - A n := sub_nonneg.mpr (hanti hn)
  have hDle : A N - A n ≤ A 0 :=
    (sub_le_self _ (hpos n)).trans (hanti (Nat.zero_le N))
  have hDn : ‖A N - A n‖ ≤ ‖A 0‖ :=
    CStarAlgebra.norm_le_norm_of_le_of_nonneg hDle hD
  have hq : 0 ≤ q N - q n := sub_nonneg.mpr (hqanti hn)
  have hsmall : q N - q n < ε ^ 2 / K := by
    have hh := hN N le_rfl n hn
    simpa [Real.dist_eq, abs_of_nonneg hq] using hh
  have hbound := norm_apply_sq_le_norm_mul_inner hD x
  have he : (inner ℂ x ((A N - A n) x)).re = q N - q n := by
    simp [q]
  rw [he] at hbound
  have hsq : ‖(A N - A n) x‖ ^ 2 < ε ^ 2 := calc
    _ ≤ ‖A 0‖ * (q N - q n) :=
      hbound.trans (mul_le_mul_of_nonneg_right hDn hq)
    _ ≤ K * (q N - q n) := by dsimp [K]; nlinarith
    _ < ε ^ 2 := by
      have hh := mul_lt_mul_of_pos_left hsmall hK
      rwa [mul_div_cancel₀ _ (ne_of_gt hK)] at hh
  have hnorm : ‖(A N - A n) x‖ < ε :=
    (sq_lt_sq₀ (norm_nonneg _) hε.le).mp hsq
  simpa only [dist_eq_norm, sub_apply, norm_sub_rev] using hnorm

/-- Every decreasing positive sequence has a bounded strong limit, which is
its greatest lower bound in the Loewner order. -/
theorem exists_strongLimit_of_antitone_nonneg (A : ℕ → E →L[ℂ] E)
    (hanti : Antitone A) (hpos : ∀ n, 0 ≤ A n) :
    ∃ B : E →L[ℂ] E, (∀ x, Tendsto (fun n => A n x) atTop (𝓝 (B x))) ∧
      0 ≤ B ∧ IsGLB (Set.range A) B := by
  classical
  have hex (x : E) : ∃ y, Tendsto (fun n => A n x) atTop (𝓝 y) :=
    cauchySeq_tendsto_of_complete (cauchySeq_apply_of_antitone_nonneg A hanti hpos x)
  let f : E → E := fun x => Classical.choose (hex x)
  have hf (x : E) : Tendsto (fun n => A n x) atTop (𝓝 (f x)) :=
    Classical.choose_spec (hex x)
  let L : E →ₗ[ℂ] E :=
    { toFun := f
      map_add' := fun x y => tendsto_nhds_unique (hf (x + y))
        (by simpa using (hf x).add (hf y))
      map_smul' := fun c x => tendsto_nhds_unique (hf (c • x))
        (by simpa using (hf x).const_smul c) }
  have hb (x : E) : ‖L x‖ ≤ ‖A 0‖ * ‖x‖ := by
    apply le_of_tendsto (hf x).norm
    exact Filter.Eventually.of_forall fun n => (A n).le_opNorm x |>.trans
      (mul_le_mul_of_nonneg_right
        (CStarAlgebra.norm_le_norm_of_le_of_nonneg (hanti (Nat.zero_le n)) (hpos n))
        (norm_nonneg x))
  let B : E →L[ℂ] E := L.mkContinuous ‖A 0‖ hb
  have hB (x : E) : Tendsto (fun n => A n x) atTop (𝓝 (B x)) := hf x
  refine ⟨B, hB, ?_, ?_⟩
  · exact operator_le_of_strong_tendsto (fun _ => tendsto_const_nhds) hB
      (Filter.Eventually.of_forall hpos)
  · constructor
    · rintro _ ⟨n, rfl⟩
      exact operator_le_of_strong_tendsto hB (fun _ => tendsto_const_nhds)
        (Filter.eventually_atTop.mpr ⟨n, fun m hm => hanti hm⟩)
    · intro C hC
      exact operator_le_of_strong_tendsto (fun _ => tendsto_const_nhds) hB
        (Filter.Eventually.of_forall fun n => hC ⟨n, rfl⟩)

end VacuumBellSeparation.Gaussian
