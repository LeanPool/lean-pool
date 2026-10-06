/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Window.PsiShellAlgebra
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# High-contrast homogenization: Provider.Window.PsiShellFinite

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport
namespace IndependentSums

open MeasureTheory Set Filter
open scoped ENNReal BigOperators Interval

noncomputable section

private theorem pred_le_triangular (r : ℕ) : r - 1 ≤ natTriangular r := by
  cases r with
  | zero => simp
  | succ r =>
      rw [natTriangular_succ]
      exact Nat.le_add_left r (natTriangular r)

private theorem triangular_add_cross (j r : ℕ) :
    natTriangular (j + r + 1) =
      natTriangular (j + 1) + (j + 1) * r + natTriangular r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [show j + (r + 1) + 1 = (j + r + 1) + 1 by omega,
        natTriangular_succ, ih, natTriangular_succ]
      rw [natTriangular_succ r]
      ring

private theorem shell_exponent_le {j n : ℕ} (hj : j < n) :
    natTriangular (j + 1) + (j + 1) * (n - j) + (n - j - 1) ≤
      natTriangular (n + 1) := by
  let r : ℕ := n - j
  have hjle : j ≤ n := hj.le
  have hn : j + r = n := by dsimp only [r]; exact Nat.add_sub_of_le hjle
  have hr : r - 1 ≤ natTriangular r := pred_le_triangular r
  rw [← hn, triangular_add_cross]
  simp only [Nat.add_sub_cancel_left]
  exact Nat.add_le_add_left hr _

theorem lintegral_Ioc_pow_le_shell_sum (f : ℝ → ℝ≥0∞)
    {B : ℝ} (hB : 1 ≤ B) (n : ℕ) :
    ∫⁻ t in Ioc 1 (B ^ n), f t ∂volume ≤
      ∑ j ∈ Finset.range n, ∫⁻ t in Ioc (B ^ j) (B ^ (j + 1)), f t ∂volume := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h1 : (1 : ℝ) ≤ B ^ n := one_le_pow₀ hB
      have hstep : B ^ n ≤ B ^ (n + 1) := pow_le_pow_right₀ hB (by omega)
      rw [← Ioc_union_Ioc_eq_Ioc h1 hstep]
      calc
        ∫⁻ t in Ioc 1 (B ^ n) ∪ Ioc (B ^ n) (B ^ (n + 1)), f t ∂volume ≤
            (∫⁻ t in Ioc 1 (B ^ n), f t ∂volume) +
              ∫⁻ t in Ioc (B ^ n) (B ^ (n + 1)), f t ∂volume :=
          lintegral_union_le _ _ _
        _ ≤ (∑ j ∈ Finset.range n,
              ∫⁻ t in Ioc (B ^ j) (B ^ (j + 1)), f t ∂volume) +
              ∫⁻ t in Ioc (B ^ n) (B ^ (n + 1)), f t ∂volume :=
          add_le_add ih le_rfl
        _ = ∑ j ∈ Finset.range (n + 1),
              ∫⁻ t in Ioc (B ^ j) (B ^ (j + 1)), f t ∂volume := by
          rw [Finset.sum_range_succ]

private theorem shell_term_le {Ψ : ℝ → ℝ} {B : ℝ} (n j : ℕ)
    (hB : 2 ≤ B) (hΨ : HasPsiGrowth Ψ B) (hAdmissible : AdmissiblePsi Ψ)
    (hj : j < n) :
    ∫⁻ t in Ioc (B ^ j) (B ^ (j + 1)),
        ENNReal.ofReal (t ^ ((n : ℝ) - 1) / Ψ t) ∂volume ≤
      ENNReal.ofReal ((1 - B⁻¹) * B ^ natTriangular (n + 1) *
        (B⁻¹) ^ (n - j - 1)) := by
  let C : ℝ := B ^ natTriangular (j + 1) *
    (B ^ (j + 1)) ^ (n - j - 1)
  have hBpos : 0 < B := zero_lt_two.trans_le hB
  have hB1 : 1 ≤ B := one_le_two.trans hB
  have hC0 : 0 ≤ C := by dsimp only [C]; positivity
  have hdom : ∀ᵐ t ∂volume.restrict (Ioc (B ^ j) (B ^ (j + 1))),
      ENNReal.ofReal (t ^ ((n : ℝ) - 1) / Ψ t) ≤ ENNReal.ofReal C := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall ?_
    intro t ht
    have htpos : 0 < t := lt_trans (pow_pos hBpos j) ht.1
    have hkernel := rpow_div_psi_le n j hB1 hΨ hAdmissible ht.1.le
    have hexp : (n : ℝ) - (j : ℝ) - 1 = (n - j - 1 : ℕ) := by
      exact_mod_cast (show (n : ℤ) - j - 1 = (n - j - 1 : ℕ) by omega)
    have hpow : t ^ ((n : ℝ) - (j : ℝ) - 1) ≤
        (B ^ (j + 1)) ^ (n - j - 1) := by
      rw [hexp, Real.rpow_natCast]
      exact pow_le_pow_left₀ htpos.le ht.2 (n - j - 1)
    apply ENNReal.ofReal_le_ofReal
    exact hkernel.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
  have hconst :
      ∫⁻ _t : ℝ in Ioc (B ^ j) (B ^ (j + 1)), ENNReal.ofReal C ∂volume =
        ENNReal.ofReal (C * (B ^ (j + 1) - B ^ j)) := by
    rw [lintegral_const, Measure.restrict_apply_univ,
      Real.volume_Ioc, ← ENNReal.ofReal_mul hC0]
  have hlen : B ^ (j + 1) - B ^ j = (1 - B⁻¹) * B ^ (j + 1) := by
    rw [pow_succ]
    field_simp [hBpos.ne']
  let e : ℕ := natTriangular (j + 1) + (j + 1) * (n - j)
  let s : ℕ := n - j - 1
  let T : ℕ := natTriangular (n + 1)
  have hinner : (B ^ (j + 1)) ^ (n - j - 1) * B ^ (j + 1) =
      B ^ ((j + 1) * (n - j)) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    calc
      (j + 1) * (n - j - 1) + (j + 1) =
          (j + 1) * ((n - j - 1) + 1) := by rw [Nat.mul_add, Nat.mul_one]
      _ = (j + 1) * (n - j) := by congr 1; omega
  have hraw : C * (B ^ (j + 1) - B ^ j) = (1 - B⁻¹) * B ^ e := by
    dsimp only [C, e]
    rw [hlen]
    calc
      B ^ natTriangular (j + 1) * (B ^ (j + 1)) ^ (n - j - 1) *
          ((1 - B⁻¹) * B ^ (j + 1)) =
          (1 - B⁻¹) * (B ^ natTriangular (j + 1) *
            ((B ^ (j + 1)) ^ (n - j - 1) * B ^ (j + 1))) := by ring
      _ = (1 - B⁻¹) * (B ^ natTriangular (j + 1) *
            B ^ ((j + 1) * (n - j))) := by rw [hinner]
      _ = (1 - B⁻¹) * B ^
            (natTriangular (j + 1) + (j + 1) * (n - j)) := by rw [pow_add]
  have hes : e + s ≤ T := by
    dsimp only [e, s, T]
    exact shell_exponent_le hj
  have hspos : 0 < B ^ s := pow_pos hBpos s
  have hpowmul : B ^ e * B ^ s ≤ B ^ T := by
    rw [← pow_add]
    exact pow_le_pow_right₀ hB1 hes
  have hpow : B ^ e ≤ B ^ T * (B⁻¹) ^ s := by
    calc
      B ^ e = (B ^ e * B ^ s) * (B ^ s)⁻¹ := by
        field_simp [hspos.ne']
      _ ≤ B ^ T * (B ^ s)⁻¹ :=
        mul_le_mul_of_nonneg_right hpowmul (inv_nonneg.mpr hspos.le)
      _ = B ^ T * (B⁻¹) ^ s := by rw [inv_pow]
  have hfactor : 0 ≤ 1 - B⁻¹ := by
    exact sub_nonneg.mpr (inv_le_one_of_one_le₀ hB1)
  calc
    ∫⁻ t in Ioc (B ^ j) (B ^ (j + 1)),
        ENNReal.ofReal (t ^ ((n : ℝ) - 1) / Ψ t) ∂volume ≤
        ∫⁻ _t : ℝ in Ioc (B ^ j) (B ^ (j + 1)),
          ENNReal.ofReal C ∂volume := lintegral_mono_ae hdom
    _ = ENNReal.ofReal (C * (B ^ (j + 1) - B ^ j)) := hconst
    _ = ENNReal.ofReal ((1 - B⁻¹) * B ^ e) := by rw [hraw]
    _ ≤ ENNReal.ofReal ((1 - B⁻¹) * B ^ T * (B⁻¹) ^ s) := by
      apply ENNReal.ofReal_le_ofReal
      calc
        (1 - B⁻¹) * B ^ e ≤ (1 - B⁻¹) * (B ^ T * (B⁻¹) ^ s) :=
          mul_le_mul_of_nonneg_left hpow hfactor
        _ = (1 - B⁻¹) * B ^ T * (B⁻¹) ^ s := by ring
    _ = ENNReal.ofReal ((1 - B⁻¹) * B ^ natTriangular (n + 1) *
        (B⁻¹) ^ (n - j - 1)) := by rfl

/-- The shells below `B^n` sum to one triangular growth factor. -/
theorem lintegral_finite_psi_shells_le {Ψ : ℝ → ℝ} {B : ℝ} (n : ℕ)
    (hB : 2 ≤ B) (hΨ : HasPsiGrowth Ψ B) (hAdmissible : AdmissiblePsi Ψ) :
    (∑ j ∈ Finset.range n,
      ∫⁻ t in Ioc (B ^ j) (B ^ (j + 1)),
        ENNReal.ofReal (t ^ ((n : ℝ) - 1) / Ψ t) ∂volume) ≤
      ENNReal.ofReal (B ^ natTriangular (n + 1)) := by
  let q : ℝ := B⁻¹
  let T : ℕ := natTriangular (n + 1)
  have hBpos : 0 < B := zero_lt_two.trans_le hB
  have hq0 : 0 < q := by dsimp only [q]; positivity
  have hq1 : q < 1 := by
    dsimp only [q]
    exact (inv_lt_one₀ hBpos).2 (one_lt_two.trans_le hB)
  have hfac : 0 ≤ (1 - q) * B ^ T := mul_nonneg (sub_nonneg.mpr hq1.le) (by positivity)
  have hterms := Finset.sum_le_sum fun j hj =>
    shell_term_le n j hB hΨ hAdmissible (Finset.mem_range.mp hj)
  have hnonneg : ∀ j ∈ Finset.range n,
      0 ≤ (1 - q) * B ^ T * q ^ (n - j - 1) := by
    intro j _
    positivity
  have hsum : ∑ j ∈ Finset.range n, q ^ (n - j - 1) ≤ (1 - q)⁻¹ := by
    have hreflect : (∑ j ∈ Finset.range n, q ^ (n - j - 1)) =
        ∑ j ∈ Finset.range n, q ^ j := by
      calc
        (∑ j ∈ Finset.range n, q ^ (n - j - 1)) =
            ∑ j ∈ Finset.range n, q ^ (n - 1 - j) := by
              apply Finset.sum_congr rfl
              intro j hj
              congr 1
              omega
        _ = ∑ j ∈ Finset.range n, q ^ j := Finset.sum_range_reflect _ _
    rw [hreflect]
    simpa only [Nat.Ico_zero_eq_range, pow_zero, one_div] using
      (geom_sum_Ico_le_of_lt_one (m := 0) (n := n) hq0.le hq1)
  calc
    (∑ j ∈ Finset.range n,
      ∫⁻ t in Ioc (B ^ j) (B ^ (j + 1)),
        ENNReal.ofReal (t ^ ((n : ℝ) - 1) / Ψ t) ∂volume) ≤
        ∑ j ∈ Finset.range n,
          ENNReal.ofReal ((1 - q) * B ^ T * q ^ (n - j - 1)) := by
            simpa only [q, T] using hterms
    _ = ENNReal.ofReal (∑ j ∈ Finset.range n,
          (1 - q) * B ^ T * q ^ (n - j - 1)) := by
      rw [ENNReal.ofReal_sum_of_nonneg hnonneg]
    _ ≤ ENNReal.ofReal ((1 - q) * B ^ T * (1 - q)⁻¹) := by
      apply ENNReal.ofReal_le_ofReal
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left hsum hfac
    _ = ENNReal.ofReal (B ^ T) := by
      congr 1
      have hne : 1 - q ≠ 0 := sub_ne_zero.mpr hq1.ne.symm
      calc
        (1 - q) * B ^ T * (1 - q)⁻¹ =
            B ^ T * ((1 - q) * (1 - q)⁻¹) := by ring
        _ = B ^ T := by rw [mul_inv_cancel₀ hne, mul_one]
    _ = ENNReal.ofReal (B ^ natTriangular (n + 1)) := by rfl

end
end IndependentSums
end HCPolySupport
