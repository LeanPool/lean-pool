/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.NumberTheory.LSeries.SumCoeff
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.MeasureTheory.Function.Floor
public import LeanPool.Siegel.CharSum

/-!
# The transforms `J g s = ∫_{t>1} g(t) t^{-(s+1)}`

Integrability, bounds and holomorphy on `Re s > 0` for bounded `g`; the integral
representation of `L(s, χ)` on `Re s > 0` (target 2) and bounds for `L(s, χ)`.
-/

@[expose] public section

open MeasureTheory Set Complex Filter Asymptotics Topology

namespace SiegelThmLib

/-- `J g s = ∫_{t>1} g(t) t^{-(s+1)} dt`. -/
noncomputable def J (g : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ t in Ioi (1 : ℝ), g t * (t : ℂ) ^ (-(s + 1))

lemma norm_ofReal_cpow_neg {t : ℝ} (ht : 0 < t) (s : ℂ) :
    ‖(t : ℂ) ^ (-(s + 1))‖ = t ^ (-(s.re + 1)) := by
  rw [norm_cpow_eq_rpow_re_of_pos ht]; simp

lemma continuousOn_cpow_neg (s : ℂ) :
    ContinuousOn (fun t : ℝ => (t : ℂ) ^ (-(s + 1))) (Ioi 0) := fun t ht =>
  (continuousAt_ofReal_cpow_const t _ (Or.inr (ne_of_gt ht))).continuousWithinAt

/-- Integrability of the integrand of `J`, for `‖g t‖ ≤ B t^κ`, `κ < Re s`. -/
lemma integrableOn_J {g : ℝ → ℂ} (hg : AEStronglyMeasurable g (volume.restrict (Ioi 1)))
    {B κ : ℝ} (hB : ∀ t, 1 < t → ‖g t‖ ≤ B * t ^ κ) {s : ℂ} (hs : κ < s.re) :
    IntegrableOn (fun t : ℝ => g t * (t : ℂ) ^ (-(s + 1))) (Ioi 1) := by
  have hint : IntegrableOn (fun t : ℝ => B * t ^ (κ - (s.re + 1))) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul B
  refine hint.mono' ?_ ?_
  · refine hg.mul ?_
    exact ((continuousOn_cpow_neg s).mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable
      measurableSet_Ioi
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht' : (0 : ℝ) < t := lt_trans one_pos ht
    rw [norm_mul, norm_ofReal_cpow_neg ht']
    calc ‖g t‖ * t ^ (-(s.re + 1)) ≤ (B * t ^ κ) * t ^ (-(s.re + 1)) :=
          mul_le_mul_of_nonneg_right (hB t ht) (Real.rpow_nonneg ht'.le _)
      _ = B * t ^ (κ - (s.re + 1)) := by
          rw [mul_assoc, ← Real.rpow_add ht']; ring_nf

/-- Bound for `J`, for `‖g t‖ ≤ B t^κ`, `κ < Re s`. -/
lemma norm_J_le {g : ℝ → ℂ}
    {B κ : ℝ} (hB : ∀ t, 1 < t → ‖g t‖ ≤ B * t ^ κ) {s : ℂ} (hs : κ < s.re) :
    ‖J g s‖ ≤ B / (s.re - κ) := by
  have hint : IntegrableOn (fun t : ℝ => B * t ^ (κ - (s.re + 1))) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul B
  have h1 : ‖J g s‖ ≤ ∫ t in Ioi (1 : ℝ), B * t ^ (κ - (s.re + 1)) := by
    refine norm_integral_le_of_norm_le hint ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht' : (0 : ℝ) < t := lt_trans one_pos ht
    rw [norm_mul, norm_ofReal_cpow_neg ht']
    calc ‖g t‖ * t ^ (-(s.re + 1)) ≤ (B * t ^ κ) * t ^ (-(s.re + 1)) :=
          mul_le_mul_of_nonneg_right (hB t ht) (Real.rpow_nonneg ht'.le _)
      _ = B * t ^ (κ - (s.re + 1)) := by
          rw [mul_assoc, ← Real.rpow_add ht']; ring_nf
  have h2 : ∫ t in Ioi (1 : ℝ), B * t ^ (κ - (s.re + 1)) = B / (s.re - κ) := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) one_pos, Real.one_rpow]
    have : κ - (s.re + 1) + 1 = -(s.re - κ) := by ring
    rw [this, div_neg, neg_div, neg_neg, mul_one_div]
  exact h1.trans h2.le

/-- `J g` is a Mellin transform. -/
lemma J_eq_mellin (g : ℝ → ℂ) (s : ℂ) : J g s = mellin ((Ioi (1 : ℝ)).indicator g) (-s) := by
  rw [J, mellin]
  have h1 : (fun t : ℝ => (t : ℂ) ^ (-s - 1) • (Ioi (1 : ℝ)).indicator g t) =
      (Ioi (1 : ℝ)).indicator (fun t => (t : ℂ) ^ (-s - 1) • g t) := by
    funext t
    exact (indicator_smul_apply (Ioi (1 : ℝ)) (fun t : ℝ => (t : ℂ) ^ (-s - 1)) g t).symm
  rw [h1, setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi,
    sup_of_le_right zero_le_one]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [smul_eq_mul, show -s - 1 = -(s + 1) by ring, mul_comm]

/-- `J g` is holomorphic on `Re s > 0` for bounded measurable `g`. -/
lemma differentiableAt_J {g : ℝ → ℂ} (hg : Measurable g) {B : ℝ} (hB : ∀ t, ‖g t‖ ≤ B)
    {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ (J g) s := by
  set f : ℝ → ℂ := (Ioi (1 : ℝ)).indicator g with hf
  have hJ : J g = fun s => mellin f (-s) := funext fun s => J_eq_mellin g s
  have hfm : Measurable f := hg.indicator measurableSet_Ioi
  have hfB : ∀ t, ‖f t‖ ≤ B := fun t =>
    (norm_indicator_le_norm_self g t).trans (hB t)
  have hloc : LocallyIntegrable f volume := by
    refine (locallyIntegrable_const B).mono hfm.aestronglyMeasurable ?_
    refine Eventually.of_forall fun t => ?_
    exact (hfB t).trans (le_abs_self B |>.trans (Real.norm_eq_abs B).symm.le)
  have hmel : DifferentiableAt ℂ (mellin f) (-s) := by
    refine mellin_differentiableAt_of_isBigO_rpow (a := 0) (b := (-s).re - 1)
      (hloc.locallyIntegrableOn _) ?_ ?_ ?_ (by linarith)
    · refine IsBigO.of_bound B (Eventually.of_forall fun t => ?_)
      simp only [neg_zero, Real.rpow_zero, norm_one, mul_one]
      exact hfB t
    · simp only [neg_re]; linarith
    · refine IsBigO.of_bound 0 ?_
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
      have : f t = 0 := by
        rw [hf, indicator_of_notMem]
        simp only [mem_Ioi, not_lt]; exact ht.2.le
      simp [this]
  rw [hJ]
  exact hmel.comp s differentiableAt_id.neg

/-! ### Partial sums of characters -/

variable {N : ℕ} [NeZero N]

/-- `A_χ(t) = ∑_{1 ≤ k ≤ t} χ k`. -/
noncomputable def A (χ : DirichletCharacter ℂ N) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ k

omit [NeZero N] in
lemma measurable_A (χ : DirichletCharacter ℂ N) : Measurable (A χ) :=
  (measurable_from_nat (f := fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, χ k)).comp Nat.measurable_floor

lemma norm_A_le {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (t : ℝ) : ‖A χ t‖ ≤ N :=
  norm_sum_Icc_le hχ _

omit [NeZero N] in
lemma norm_A_le_floor (χ : DirichletCharacter ℂ N) (t : ℝ) : ‖A χ t‖ ≤ ⌊t⌋₊ := by
  unfold A
  calc ‖∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ k‖ ≤ ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ‖χ k‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.Icc 1 ⌊t⌋₊, (1 : ℝ) :=
        Finset.sum_le_sum fun k _ => DirichletCharacter.norm_le_one χ _
    _ = ⌊t⌋₊ := by simp

/-- `‖A_χ(t)‖ ≤ N^η t^{1-η}` for `t ≥ 0`, `0 ≤ η ≤ 1`. -/
lemma norm_A_le_rpow {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {t : ℝ} (ht : 0 ≤ t) {η : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) : ‖A χ t‖ ≤ (N : ℝ) ^ η * t ^ (1 - η) := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hm : ‖A χ t‖ ≤ min t N :=
    le_min ((norm_A_le_floor χ t).trans (Nat.floor_le ht)) (norm_A_le hχ t)
  rcases le_total t N with htN | htN
  · calc ‖A χ t‖ ≤ t := hm.trans (min_le_left _ _)
      _ = t ^ η * t ^ (1 - η) := by
          rw [← Real.rpow_add' ht (by norm_num : η + (1 - η) ≠ 0)]; simp
      _ ≤ (N : ℝ) ^ η * t ^ (1 - η) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow ht htN hη0) (Real.rpow_nonneg ht _)
  · calc ‖A χ t‖ ≤ N := hm.trans (min_le_right _ _)
      _ = (N : ℝ) ^ η * (N : ℝ) ^ (1 - η) := by
          rw [← Real.rpow_add' hN (by norm_num : η + (1 - η) ≠ 0)]; simp
      _ ≤ (N : ℝ) ^ η * t ^ (1 - η) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hN htN (by linarith))
            (Real.rpow_nonneg hN _)

lemma differentiableAt_J_A {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (J (A χ)) s :=
  differentiableAt_J (measurable_A χ) (norm_A_le hχ) hs

/-- The integral representation for `Re s > 1` (Abel summation, Mathlib). -/
lemma LFunction_eq_mul_J_of_one_lt {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {s : ℂ}
    (hs : 1 < s.re) : DirichletCharacter.LFunction χ s = s * J (A χ) s := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  refine LSeries_eq_mul_integral _ le_rfl (by linarith) (ZMod.LSeriesSummable_of_one_lt_re χ hs) ?_
  refine IsBigO.of_bound N (Eventually.of_forall fun n => ?_)
  simp only [Real.rpow_zero, norm_one, mul_one]
  exact norm_sum_Icc_le hχ n

/-- **Target 2** (in `J` form). -/
lemma LFunction_eq_mul_J {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.LFunction χ s = s * J (A χ) s := by
  have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const continuous_re
  have hf : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) {s : ℂ | 0 < s.re} :=
    ((DirichletCharacter.differentiable_LFunction hχ).differentiableOn).analyticOnNhd hU
  have hg : AnalyticOnNhd ℂ (fun s => s * J (A χ) s) {s : ℂ | 0 < s.re} := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hU
    exact (differentiableAt_id.mul (differentiableAt_J_A hχ hz)).differentiableWithinAt
  have h2 : (2 : ℂ) ∈ {s : ℂ | 0 < s.re} := by simp
  have hev : DirichletCharacter.LFunction χ =ᶠ[𝓝 (2 : ℂ)] fun s => s * J (A χ) s := by
    have : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by simp)
    filter_upwards [this] with z hz using LFunction_eq_mul_J_of_one_lt hχ hz
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg (convex_halfSpace_re_gt 0).isPreconnected
    h2 hev hs

/-- **Target 2.** -/
theorem LFunction_eq_integral (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (s : ℂ) (hs : 0 < s.re) :
    DirichletCharacter.LFunction χ s =
      s * ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ k) * (t : ℂ) ^ (-(s + 1)) :=
  LFunction_eq_mul_J hχ hs

/-- `‖L(s, χ)‖ ≤ ‖s‖ N / Re s`. -/
lemma norm_LFunction_le {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ ‖s‖ * N / s.re := by
  rw [LFunction_eq_mul_J hχ hs, norm_mul, mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have := norm_J_le (g := A χ) (B := N) (κ := 0)
    (fun t _ => by simpa using norm_A_le hχ t) hs
  simpa using this

/-- `‖L(1, χ)‖ ≤ N^η / η` for `0 < η ≤ 1`. -/
lemma norm_LFunction_one_le {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {η : ℝ} (hη0 : 0 < η)
    (hη1 : η ≤ 1) : ‖DirichletCharacter.LFunction χ 1‖ ≤ (N : ℝ) ^ η / η := by
  rw [LFunction_eq_mul_J hχ (by simp), one_mul]
  have := norm_J_le (g := A χ) (B := (N : ℝ) ^ η)
    (κ := 1 - η) (fun t ht => norm_A_le_rpow hχ (by linarith) hη0.le hη1)
    (s := 1) (by simp; linarith)
  simpa using this

end SiegelThmLib
