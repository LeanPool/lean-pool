/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.Siegel.Zeta
public import LeanPool.Siegel.Coeff
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Calculus.Deriv.ZPow

/-!
# Goldfeld's auxiliary function: holomorphy, bounds, derivatives at `2`

`P = L(·,χ₁) L(·,χ₂) L(·,ψ)`, `F(s) = (1/(s-1) + H(s)) P(s)` (`= ζ(s) P(s)` on `Re s > 1`),
`G = dslope P 1 + H P` (holomorphic on `Re s > 0`, `G = F - P(1)/(s-1)`).
-/

@[expose] public section

open Complex DirichletCharacter Metric Set Filter Topology LSeries

open scoped ComplexOrder LSeries.notation Nat

namespace SiegelThmLib

variable {N₁ N₂ : ℕ} [NeZero N₁] [NeZero N₂]

/-- `P(s) = L(s,χ₁) L(s,χ₂) L(s,χ₁χ₂)`. -/
noncomputable def P (χ₁ : DirichletCharacter ℂ N₁) (χ₂ : DirichletCharacter ℂ N₂) (s : ℂ) : ℂ :=
  LFunction χ₁ s * LFunction χ₂ s * LFunction (prodChar χ₁ χ₂) s

/-- The regular part `G = dslope P 1 + H P`. -/
noncomputable def G (χ₁ : DirichletCharacter ℂ N₁) (χ₂ : DirichletCharacter ℂ N₂) (s : ℂ) : ℂ :=
  dslope (P χ₁ χ₂) 1 s + Hz s * P χ₁ χ₂ s

/-- `F(s) = (1/(s-1) + H(s)) P(s)`. -/
noncomputable def F (χ₁ : DirichletCharacter ℂ N₁) (χ₂ : DirichletCharacter ℂ N₂) (s : ℂ) : ℂ :=
  (1 / (s - 1) + Hz s) * P χ₁ χ₂ s

variable {χ₁ : DirichletCharacter ℂ N₁} {χ₂ : DirichletCharacter ℂ N₂}

lemma differentiable_P (hχ₁ : χ₁ ≠ 1) (hχ₂ : χ₂ ≠ 1) (hψ : prodChar χ₁ χ₂ ≠ 1) :
    Differentiable ℂ (P χ₁ χ₂) := by
  unfold P
  exact ((differentiable_LFunction hχ₁).mul (differentiable_LFunction hχ₂)).mul
    (differentiable_LFunction hψ)

lemma differentiableOn_G (hχ₁ : χ₁ ≠ 1) (hχ₂ : χ₂ ≠ 1) (hψ : prodChar χ₁ χ₂ ≠ 1) :
    DifferentiableOn ℂ (G χ₁ χ₂) {s | 0 < s.re} := by
  have hP := differentiable_P hχ₁ hχ₂ hψ
  have hd : DifferentiableOn ℂ (dslope (P χ₁ χ₂) 1) univ :=
    (Complex.differentiableOn_dslope Filter.univ_mem).mpr hP.differentiableOn
  intro s hs
  unfold G
  exact ((hd.differentiableAt Filter.univ_mem).add
    ((differentiableAt_Hz hs).mul (hP s))).differentiableWithinAt

lemma G_eq {s : ℂ} (hs : s ≠ 1) :
    G χ₁ χ₂ s = F χ₁ χ₂ s - P χ₁ χ₂ 1 / (s - 1) := by
  have hs' : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  unfold G F
  rw [dslope_of_ne _ hs, slope_def_field]
  field_simp
  ring

lemma F_eq_LSeries {s : ℂ} (hs : 1 < s.re) :
    F χ₁ χ₂ s = LSeries ↗(coeff χ₁ χ₂) s := by
  rw [LSeries_coeff _ _ hs, LSeries_one_eq hs]; rfl

/-! ### Bounds on the circle `|s - 2| = 3/2` -/

lemma sphere_facts {s : ℂ} (hs : s ∈ sphere (2 : ℂ) (3 / 2)) :
    1 / 2 ≤ s.re ∧ ‖s‖ ≤ 7 / 2 ∧ 1 / 2 ≤ ‖s - 1‖ := by
  rw [mem_sphere_iff_norm] at hs
  refine ⟨?_, ?_, ?_⟩
  · have h := abs_re_le_norm (s - 2)
    rw [hs, sub_re] at h
    have := (abs_le.mp h).1
    norm_num at this ⊢; linarith
  · calc ‖s‖ = ‖(s - 2) + 2‖ := by rw [sub_add_cancel]
      _ ≤ ‖s - 2‖ + ‖(2 : ℂ)‖ := norm_add_le _ _
      _ = 7 / 2 := by norm_num [hs]
  · have h := norm_sub_norm_le (s - 2) (-1)
    rw [hs, show s - 2 - -1 = s - 1 by ring, norm_neg, norm_one] at h
    linarith

lemma norm_L_sphere {M : ℕ} [NeZero M] {χ : DirichletCharacter ℂ M} (hχ : χ ≠ 1) {s : ℂ}
    (hs : s ∈ sphere (2 : ℂ) (3 / 2)) : ‖LFunction χ s‖ ≤ 7 * M := by
  obtain ⟨h1, h2, -⟩ := sphere_facts hs
  have hre : 0 < s.re := by linarith only [h1]
  refine (norm_LFunction_le hχ hre).trans ?_
  rw [div_le_iff₀ hre]
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  nlinarith only [h1, h2, hM]

lemma norm_L_one {M : ℕ} [NeZero M] {χ : DirichletCharacter ℂ M} (hχ : χ ≠ 1) :
    ‖LFunction χ 1‖ ≤ M := by
  simpa using norm_LFunction_le hχ (s := 1) (by simp)

lemma norm_P_one_le (hχ₁ : χ₁ ≠ 1) (hχ₂ : χ₂ ≠ 1) (hψ : prodChar χ₁ χ₂ ≠ 1) :
    ‖P χ₁ χ₂ 1‖ ≤ ((N₁ : ℝ) * N₂) ^ 2 := by
  unfold P
  rw [norm_mul, norm_mul]
  have a := norm_L_one hχ₁
  have b := norm_L_one hχ₂
  have c := norm_L_one hψ
  push_cast at c
  calc ‖LFunction χ₁ 1‖ * ‖LFunction χ₂ 1‖ * ‖LFunction (prodChar χ₁ χ₂) 1‖
      ≤ (N₁ : ℝ) * N₂ * (N₁ * N₂) := by gcongr
    _ = ((N₁ : ℝ) * N₂) ^ 2 := by ring

lemma norm_P_sphere (hχ₁ : χ₁ ≠ 1) (hχ₂ : χ₂ ≠ 1) (hψ : prodChar χ₁ χ₂ ≠ 1) {s : ℂ}
    (hs : s ∈ sphere (2 : ℂ) (3 / 2)) : ‖P χ₁ χ₂ s‖ ≤ 343 * ((N₁ : ℝ) * N₂) ^ 2 := by
  unfold P
  rw [norm_mul, norm_mul]
  have a := norm_L_sphere hχ₁ hs
  have b := norm_L_sphere hχ₂ hs
  have c := norm_L_sphere hψ hs
  push_cast at c
  calc ‖LFunction χ₁ s‖ * ‖LFunction χ₂ s‖ * ‖LFunction (prodChar χ₁ χ₂) s‖
      ≤ (7 * N₁ : ℝ) * (7 * N₂) * (7 * (N₁ * N₂)) := by gcongr
    _ = 343 * ((N₁ : ℝ) * N₂) ^ 2 := by ring

/-- `‖G‖ ≤ 4000 Q²` on the circle `|s - 2| = 3/2`. -/
lemma norm_G_sphere (hχ₁ : χ₁ ≠ 1) (hχ₂ : χ₂ ≠ 1) (hψ : prodChar χ₁ χ₂ ≠ 1) {s : ℂ}
    (hs : s ∈ sphere (2 : ℂ) (3 / 2)) : ‖G χ₁ χ₂ s‖ ≤ 4000 * ((N₁ : ℝ) * N₂) ^ 2 := by
  obtain ⟨h1, h2, h3⟩ := sphere_facts hs
  have hre : 0 < s.re := by linarith only [h1]
  have hs1 : s ≠ 1 := by
    intro h; rw [h, sub_self, norm_zero] at h3; norm_num at h3
  set Q2 := ((N₁ : ℝ) * N₂) ^ 2 with hQ2
  have hQ : 0 ≤ Q2 := sq_nonneg _
  have hP := norm_P_sphere hχ₁ hχ₂ hψ hs
  have hP1 := norm_P_one_le hχ₁ hχ₂ hψ
  have hH : ‖Hz s‖ ≤ 8 := by
    refine (norm_Hz_le hre).trans ?_
    rw [add_comm, ← le_sub_iff_add_le, div_le_iff₀ hre]
    linarith only [h1, h2]
  have hds : ‖dslope (P χ₁ χ₂) 1 s‖ ≤ 2 * (344 * Q2) := by
    rw [dslope_of_ne _ hs1, slope_def_field, norm_div]
    rw [div_le_iff₀ (by linarith only [h3])]
    calc ‖P χ₁ χ₂ s - P χ₁ χ₂ 1‖ ≤ ‖P χ₁ χ₂ s‖ + ‖P χ₁ χ₂ 1‖ := norm_sub_le _ _
      _ ≤ 344 * Q2 := by linarith only [hP, hP1]
      _ ≤ 2 * (344 * Q2) * ‖s - 1‖ := by nlinarith only [h3, hQ]
  have hHP : ‖Hz s * P χ₁ χ₂ s‖ ≤ 8 * (343 * Q2) := by
    rw [norm_mul]; exact mul_le_mul hH hP (norm_nonneg _) (by norm_num)
  unfold G
  calc ‖dslope (P χ₁ χ₂) 1 s + Hz s * P χ₁ χ₂ s‖
      ≤ ‖dslope (P χ₁ χ₂) 1 s‖ + ‖Hz s * P χ₁ χ₂ s‖ := norm_add_le _ _
    _ ≤ 4000 * Q2 := by linarith only [hds, hHP, hQ]

/-- Cauchy's estimate: `‖G⁽ⁿ⁾(2)‖ ≤ n! · 4000 Q² / (3/2)ⁿ`. -/
lemma norm_iteratedDeriv_G_le (hχ₁ : χ₁ ≠ 1) (hχ₂ : χ₂ ≠ 1) (hψ : prodChar χ₁ χ₂ ≠ 1)
    (n : ℕ) : ‖iteratedDeriv n (G χ₁ χ₂) 2‖ ≤
      n ! * (4000 * ((N₁ : ℝ) * N₂) ^ 2) / (3 / 2) ^ n := by
  refine norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n (by norm_num) ?_
    (fun z hz => norm_G_sphere hχ₁ hχ₂ hψ hz)
  refine DifferentiableOn.diffContOnCl ((differentiableOn_G hχ₁ hχ₂ hψ).mono ?_)
  rw [closure_ball (2 : ℂ) (by norm_num)]
  intro z hz
  rw [mem_closedBall, dist_eq] at hz
  have h := abs_re_le_norm (z - 2)
  rw [sub_re] at h
  have := (abs_le.mp (h.trans hz)).1
  simp only [mem_ofPred_eq]
  norm_num at this ⊢; linarith

/-! ### Derivatives at `2` -/

lemma two_mem_abscissa (χ₁ : DirichletCharacter ℂ N₁) (χ₂ : DirichletCharacter ℂ N₂) :
    abscissaOfAbsConv ↗(coeff χ₁ χ₂) < ((2 : ℝ) : EReal) :=
  (abscissa_coeff_le χ₁ χ₂).trans_lt (EReal.coe_lt_coe_iff.mpr (by norm_num))

lemma iteratedDeriv_inv_sub_one (n : ℕ) :
    iteratedDeriv n (fun s : ℂ => (s - 1)⁻¹) 2 = (-1) ^ n * n ! := by
  rw [iteratedDeriv_eq_iterate]
  have h := iter_deriv_inv_linear_sub n (1 : ℂ) 1
  simp only [one_mul, one_pow, mul_one] at h
  rw [h]
  norm_num

/-- `G⁽ⁿ⁾(2) = (∑ aₙ n^{-s})⁽ⁿ⁾(2) - P(1) (-1)ⁿ n!`. -/
lemma iteratedDeriv_G (n : ℕ) :
    iteratedDeriv n (G χ₁ χ₂) 2 =
      iteratedDeriv n (LSeries ↗(coeff χ₁ χ₂)) 2 - P χ₁ χ₂ 1 * ((-1) ^ n * n !) := by
  have hU : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const continuous_re
  have h2 : (2 : ℂ) ∈ {s : ℂ | 1 < s.re} := by simp
  have heq : EqOn (G χ₁ χ₂) (fun s => LSeries ↗(coeff χ₁ χ₂) s - P χ₁ χ₂ 1 • (s - 1)⁻¹)
      {s : ℂ | 1 < s.re} := by
    intro s hs
    have hs1 : s ≠ 1 := by
      intro h; rw [h] at hs; simp at hs
    simp only
    rw [G_eq hs1, F_eq_LSeries hs, smul_eq_mul, div_eq_mul_inv]
  rw [heq.iteratedDeriv_of_isOpen hU n h2]
  have hA : ContDiffAt ℂ n (LSeries ↗(coeff χ₁ χ₂)) 2 := by
    have h2' : (2 : ℂ) ∈ {s | abscissaOfAbsConv ↗(coeff χ₁ χ₂) < s.re} := by
      simpa using two_mem_abscissa χ₁ χ₂
    exact (LSeries_analyticOnNhd _ 2 h2').contDiffAt
  have hB : ContDiffAt ℂ n (fun s : ℂ => (s - 1)⁻¹) 2 := by
    exact (contDiffAt_id.sub contDiffAt_const).inv (by norm_num)
  rw [iteratedDeriv_fun_sub hA (hB.const_smul (P χ₁ χ₂ 1)),
    iteratedDeriv_fun_const_smul hB, iteratedDeriv_inv_sub_one, smul_eq_mul]

lemma Dn_nonneg (h₁ : χ₁ ^ 2 = 1) (h₂ : χ₂ ^ 2 = 1) (n : ℕ) :
    0 ≤ (-1) ^ n * iteratedDeriv n (LSeries ↗(coeff χ₁ χ₂)) 2 := by
  have := LSeries.iteratedDeriv_alternating (a := ↗(coeff χ₁ χ₂))
    (fun k => coeff_nonneg h₁ h₂ k) (two_mem_abscissa χ₁ χ₂) n
  simpa using this

lemma one_le_D0 (h₁ : χ₁ ^ 2 = 1) (h₂ : χ₂ ^ 2 = 1) :
    1 ≤ (LSeries ↗(coeff χ₁ χ₂) 2).re := by
  have hs : LSeriesHasSum ↗(coeff χ₁ χ₂) 2 (LSeries ↗(coeff χ₁ χ₂) 2) :=
    (LSeriesSummable_coeff χ₁ χ₂ (by norm_num)).LSeriesHasSum
  have hre := Complex.reCLM.hasSum hs
  have h := le_hasSum hre 1 (fun j _ => by
    have := LSeries.term_nonneg (coeff_nonneg h₁ h₂ j) (2 : ℝ)
    simpa using (Complex.le_def.mp this).1)
  simpa [LSeries.term_def, coeff_one] using h

end SiegelThmLib
