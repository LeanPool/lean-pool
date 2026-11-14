/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MultiscaleEllipticity.Public
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MultiscaleEllipticity.Finite.Series

/-!
# GeometricResummation

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Descendant resummation in the corrected `3/8` coarse gauge

This module proves the geometric resummation over triadic descendants that
underlies the `Lambda_{s,2}` sensitivity estimate.  The source mechanism is the
display in ABK26: the weighted descendant sum of the
per-cube lower coarse-grained ellipticity inverses is bounded by a multiple of
the global lower coarse-grained ellipticity inverse, by a sum interchange plus a
geometric series, producing a pole constant.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.Multiscale

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open scoped BigOperators

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## `q = 2` series formulas -/

/-- Bridge between CoarseGraining's explicit `Real.rpow` applications and the `^`
notation used by Mathlib's `rpow` lemmas. -/
private theorem rpow_eq_pow (x y : ℝ) : Real.rpow x y = x ^ y := rfl

private theorem rpow_two_div_two (x : ℝ) : Real.rpow x (2 / 2) = x := by
  simp only [rpow_eq_pow]
  norm_num

private theorem rpow_neg_two_div_two (x : ℝ) : Real.rpow x (-2 / 2) = x⁻¹ := by
  simp only [rpow_eq_pow]
  rw [show (-2 : ℝ) / 2 = ((-1 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
  simp

/-- Summability of the weighted `sigma_*^{-1}` descendant maxima at `q = 2`. -/
theorem summable_weighted_maxDescendantSigmaStarInv_two
    (Q : TriadicCube d) (A : TriadicCoeffFamily d) {s : ℝ} (hs : 0 < s) :
    Summable (fun n : ℕ => Ch02.geometricWeight s 2 n *
      maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) A) := by
  refine (summable_sigmaStarInv_series_pointwiseCoeffField Q A hs
    (by norm_num : (0 : ℝ) < 2)).congr (fun n => ?_)
  rw [rpow_two_div_two]

/-- Summability of the weighted `b` descendant maxima at `q = 2`. -/
theorem summable_weighted_maxDescendantB_two
    (Q : TriadicCube d) (A : TriadicCoeffFamily d) {s : ℝ} (hs : 0 < s) :
    Summable (fun n : ℕ => Ch02.geometricWeight s 2 n *
      maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) A) := by
  refine (summable_B_series_pointwiseCoeffField Q A hs
    (by norm_num : (0 : ℝ) < 2)).congr (fun n => ?_)
  rw [rpow_two_div_two]

omit [NeZero d] in
/-- The literal `q = 2` series formula for `lambda_{s,2}^{-1}`. -/
theorem lambdaSq_two_inv_eq_tsum
    (Q : TriadicCube d) (A : TriadicCoeffFamily d) {s : ℝ} (hs : 0 < s) :
    (Ch02.lambdaSq Q s (.finite 2) A)⁻¹ =
      ∑' n : ℕ, Ch02.geometricWeight s 2 n *
        maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) A := by
  have h := lambdaSqFinite_rpow_neg_q_div_two_eq_tsum Q s 2 A
    (by norm_num : (0 : ℝ) < 2) (by nlinarith : (0 : ℝ) ≤ s * 2)
  rw [rpow_neg_two_div_two] at h
  rw [h]
  exact tsum_congr fun n => by rw [rpow_two_div_two]

omit [NeZero d] in
/-- The literal `q = 2` series formula for `Lambda_{s,2}`. -/
theorem LambdaSq_two_eq_tsum
    (Q : TriadicCube d) (A : TriadicCoeffFamily d) {s : ℝ} (hs : 0 < s) :
    Ch02.LambdaSq Q s (.finite 2) A =
      ∑' n : ℕ, Ch02.geometricWeight s 2 n *
        maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) A := by
  have h := LambdaSqFinite_rpow_q_div_two_eq_tsum Q s 2 A
    (by norm_num : (0 : ℝ) < 2) (by nlinarith : (0 : ℝ) ≤ s * 2)
  rw [rpow_two_div_two] at h
  rw [h]
  exact tsum_congr fun n => by rw [rpow_two_div_two]

/-! ## The corrected geometric kernel -/

/-- The corrected kernel ratio `3^{2s-3/4}` is `< 1` exactly on `s < 3/8`. -/
theorem rpow_three_two_mul_sub_lt_one {s : ℝ} (hs : s < 3 / 8) :
    Real.rpow (3 : ℝ) (2 * s - 3 / 4) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)

/-- The corrected geometric series bound.  This is the exact place where the
admissible range tightens from the printed `s < 1/2` to `s < 3/8`, and where the
pole `(3/8-s)^{-1}` appears. -/
theorem tsum_geometric_threeEighths_le_pole {s : ℝ} (hs0 : 0 < s) (hs : s < 3 / 8) :
    (∑' j : ℕ, (Real.rpow (3 : ℝ) (2 * s - 3 / 4)) ^ j) ≤ (3 / 8 - s)⁻¹ := by
  simp only [rpow_eq_pow]
  set u : ℝ := 3 / 4 - 2 * s with hu
  set r : ℝ := (3 : ℝ) ^ (2 * s - 3 / 4) with hr
  have hu0 : 0 < u := by rw [hu]; linarith
  have hu1 : u < 1 := by rw [hu]; linarith
  have hr0 : 0 < r := by rw [hr]; positivity
  have hr1 : r < 1 := by
    rw [hr]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hsum : (∑' j : ℕ, r ^ j) = (1 - r)⁻¹ := tsum_geometric_of_lt_one hr0.le hr1
  -- `3^u ≥ 1 + u log 3 ≥ 1 + u`, hence `r = 3^{-u} ≤ (1+u)^{-1}`.
  have hlog : (1 : ℝ) ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    linarith [Real.exp_one_lt_d9]
  have h3u : (1 : ℝ) + u ≤ (3 : ℝ) ^ u := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
    nlinarith [Real.add_one_le_exp (Real.log 3 * u)]
  have hden : (0 : ℝ) < 1 + u := by linarith
  have hru : r ≤ (1 + u)⁻¹ := by
    rw [hr, show 2 * s - 3 / 4 = -u by rw [hu]; ring,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
    exact inv_anti₀ hden h3u
  have hone_sub : u / (1 + u) ≤ 1 - r := by
    have : 1 - (1 + u)⁻¹ = u / (1 + u) := by field_simp; ring
    linarith [this ▸ (sub_le_sub_left hru 1)]
  have hpos : (0 : ℝ) < 1 - r := by linarith [div_pos hu0 hden]
  rw [hsum]
  have hstep : (1 - r)⁻¹ ≤ (u / (1 + u))⁻¹ :=
    inv_anti₀ (div_pos hu0 hden) hone_sub
  refine hstep.trans ?_
  rw [inv_div]
  rw [show (3 / 8 - s : ℝ) = u / 2 by rw [hu]; ring, inv_div]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.mpr hu0.le)

/-! ## The triangular reindexing

The nonnegative-series reindexing below is not an assumed Fubini step: the map
`(n,j) ↦ (n+j, j)` is an injection of `ℕ × ℕ` into itself, so the monotone
comparison for injections applies directly. -/

private theorem shiftInj : Function.Injective (fun p : ℕ × ℕ => (p.1 + p.2, p.2)) := by
  rintro ⟨n, j⟩ ⟨n', j'⟩ h
  have hj : j = j' := congrArg Prod.snd h
  subst hj
  have hn : n = n' := Nat.add_right_cancel (congrArg Prod.fst h)
  subst hn
  rfl

/-- Triangular reindexing bound for nonnegative series. -/
theorem tsum_shifted_product_le (F r : ℕ → ℝ)
    (hF0 : ∀ n, 0 ≤ F n) (hr0 : ∀ j, 0 ≤ r j)
    (hF : Summable F) (hr : Summable r) :
    (∑' n : ℕ, ∑' j : ℕ, F (n + j) * r j) ≤ (∑' n : ℕ, F n) * ∑' j : ℕ, r j := by
  set G : ℕ × ℕ → ℝ := fun p => F p.1 * r p.2 with hG
  set φ : ℕ × ℕ → ℕ × ℕ := fun p => (p.1 + p.2, p.2) with hφdef
  have hG0 : ∀ p, 0 ≤ G p := by rintro ⟨n, j⟩; exact mul_nonneg (hF0 n) (hr0 j)
  have hGsum : Summable G := hF.mul_of_nonneg hr hF0 hr0
  have hGφ : Summable (G ∘ φ) := hGsum.comp_injective shiftInj
  have hle : (∑' p : ℕ × ℕ, (G ∘ φ) p) ≤ ∑' p : ℕ × ℕ, G p :=
    tsum_comp_le_tsum_of_inj hGsum hG0 shiftInj
  calc (∑' n : ℕ, ∑' j : ℕ, F (n + j) * r j)
      = ∑' p : ℕ × ℕ, (G ∘ φ) p := (hGφ.tsum_prod).symm
    _ ≤ ∑' p : ℕ × ℕ, G p := hle
    _ = (∑' n : ℕ, F n) * ∑' j : ℕ, r j := (hF.tsum_mul_tsum hr hGsum).symm

/-- Summability of the outer triangular series. -/
theorem summable_tsum_shifted_product (F r : ℕ → ℝ)
    (hF0 : ∀ n, 0 ≤ F n) (hr0 : ∀ j, 0 ≤ r j)
    (hF : Summable F) (hr : Summable r) :
    Summable (fun n : ℕ => ∑' j : ℕ, F (n + j) * r j) := by
  set G : ℕ × ℕ → ℝ := fun p => F p.1 * r p.2 with hG
  set φ : ℕ × ℕ → ℕ × ℕ := fun p => (p.1 + p.2, p.2) with hφdef
  have hGsum : Summable G := hF.mul_of_nonneg hr hF0 hr0
  have hGφ : Summable (G ∘ φ) := hGsum.comp_injective shiftInj
  have hGφ0 : (0 : ℕ × ℕ → ℝ) ≤ G ∘ φ := by
    rintro ⟨n, j⟩; exact mul_nonneg (hF0 _) (hr0 _)
  exact ((summable_prod_of_nonneg hGφ0).mp hGφ).2

/-! ## The descendant expansion in the `3/8` gauge -/

/-- The weight identity behind the reindexing: the outer `s`-weight times the
inner `3/8`-weight equals the shifted `s`-weight times the corrected kernel
`3^{(2s-3/4) j}`, up to the fixed discount `c_{3/4}`. -/
private theorem geometricWeight_mul_threeEighths_shift (s : ℝ) (n j : ℕ) :
    Ch02.geometricWeight s 2 n * Ch02.geometricWeight (3 / 8 : ℝ) 2 j =
      Ch02.geometricDiscount (3 / 8 : ℝ) 2 *
        (Ch02.geometricWeight s 2 (n + j) *
          Real.rpow (3 : ℝ) ((2 * s - 3 / 4) * (j : ℝ))) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hsplit :
      (3 : ℝ) ^ (-s * 2 * (((n : ℝ) + (j : ℝ)))) *
          (3 : ℝ) ^ ((2 * s - 3 / 4) * (j : ℝ)) =
        (3 : ℝ) ^ (-s * 2 * (n : ℝ)) *
          (3 : ℝ) ^ (-(3 / 8 : ℝ) * 2 * (j : ℝ)) := by
    rw [← Real.rpow_add h3, ← Real.rpow_add h3]
    congr 1
    ring
  simp only [Ch02.geometricWeight, rpow_eq_pow]
  push_cast
  linear_combination
    (-(Ch02.geometricDiscount s 2 * Ch02.geometricDiscount (3 / 8 : ℝ) 2)) * hsplit

/-- The inverse lower ellipticity of every depth-`n` descendant has the literal
`q = 2` expansion over its own descendants; transitivity of triadic descendants
embeds those terms at global depth `n + j`.  This is the structural
(non-numerical) half of the double resummation. -/
theorem maxDescendantLowerEllipticityInv_threeEighths_le_nested_tsum
    (Q : TriadicCube d) (A : TriadicCoeffFamily d) (n : ℕ) :
    maxDescendantLowerEllipticityInvAtScale Q (Q.scale - (n : ℤ))
        (3 / 8 : ℝ) (.finite 2) A ≤
      ∑' j : ℕ, Ch02.geometricWeight (3 / 8 : ℝ) 2 j *
        maxDescendantSigmaStarInvMatrixNormAtScale Q
          (Q.scale - ((n + j : ℕ) : ℤ)) A := by
  have hk : Q.scale - (n : ℤ) ≤ Q.scale :=
    sub_le_self _ (by exact_mod_cast Nat.zero_le n)
  have hsumQ := summable_weighted_maxDescendantSigmaStarInv_two Q A
    (by norm_num : (0 : ℝ) < 3 / 8)
  have hsumShift : Summable (fun j : ℕ =>
      Ch02.geometricWeight (3 / 8 : ℝ) 2 j *
        maxDescendantSigmaStarInvMatrixNormAtScale Q
          (Q.scale - ((n + j : ℕ) : ℤ)) A) := by
    have htail : Summable (fun j : ℕ =>
        Ch02.geometricWeight (3 / 8 : ℝ) 2 (j + n) *
          maxDescendantSigmaStarInvMatrixNormAtScale Q
            (Q.scale - ((j + n : ℕ) : ℤ)) A) :=
      (summable_nat_add_iff (f := fun k : ℕ =>
        Ch02.geometricWeight (3 / 8 : ℝ) 2 k *
          maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (k : ℤ)) A) n).2 hsumQ
    refine (htail.mul_left (Real.rpow (3 : ℝ) ((3 / 8 : ℝ) * 2 * (n : ℝ)))).congr
      (fun j => ?_)
    have hweight : Ch02.geometricWeight (3 / 8 : ℝ) 2 j =
        Real.rpow (3 : ℝ) ((3 / 8 : ℝ) * 2 * (n : ℝ)) *
          Ch02.geometricWeight (3 / 8 : ℝ) 2 (j + n) := by
      simpa [geometricWeight_eq_old] using
        HCPolySupport.geometricWeight_shift (s := (3 / 8 : ℝ)) (q := 2) n j
    rw [hweight, show ((j + n : ℕ) : ℤ) = ((n + j : ℕ) : ℤ) by push_cast; ring]
    ring
  refine finsetSupReal_le _ (descendantsAtScale_nonempty Q hk) ?_
  intro R hR
  have hRsum := summable_weighted_maxDescendantSigmaStarInv_two R A
    (by norm_num : (0 : ℝ) < 3 / 8)
  rw [lambdaSq_two_inv_eq_tsum R A (by norm_num : (0 : ℝ) < 3 / 8)]
  refine Summable.tsum_le_tsum (fun j => ?_) hRsum hsumShift
  have hscale : R.scale - (j : ℤ) = Q.scale - ((n + j : ℕ) : ℤ) := by
    rw [HCPolySupport.descendant_scale_eq_of_mem_descendantsAtScale hR]
    push_cast
    ring
  have hmax : maxDescendantSigmaStarInvMatrixNormAtScale R (R.scale - (j : ℤ)) A ≤
      maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - ((n + j : ℕ) : ℤ)) A := by
    have hl : R.scale - (j : ℤ) ≤ R.scale :=
      sub_le_self _ (by exact_mod_cast Nat.zero_le j)
    simpa [hscale] using
      maxDescendantSigmaStarInvMatrixNormAtScale_le_of_mem_descendantsAtScale
        (Q := Q) (R := R) (k := Q.scale - (n : ℤ)) (l := R.scale - (j : ℤ)) A hR hl
  refine mul_le_mul_of_nonneg_left hmax ?_
  simpa [geometricWeight_eq_old] using
    HCPolySupport.geometricWeight_nonneg j (by norm_num : (0 : ℝ) ≤ (3 / 8 : ℝ) * 2)

/-! ## The main resummation -/

private theorem weighted_maxDescendantLowerEllipticityInv_package
    (Q : TriadicCube d) (A : TriadicCoeffFamily d) {s : ℝ}
    (hs0 : 0 < s) (hs : s < 3 / 8) :
    (∑' n : ℕ, Ch02.geometricWeight s 2 n *
        maxDescendantLowerEllipticityInvAtScale Q (Q.scale - (n : ℤ))
          (3 / 8 : ℝ) (.finite 2) A)
        ≤ (3 / 8 - s)⁻¹ * (Ch02.lambdaSq Q s (.finite 2) A)⁻¹ ∧
      Summable (fun n : ℕ => Ch02.geometricWeight s 2 n *
        maxDescendantLowerEllipticityInvAtScale Q (Q.scale - (n : ℤ))
          (3 / 8 : ℝ) (.finite 2) A) := by
  set m : ℕ → ℝ := fun k =>
    maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (k : ℤ)) A with hm
  set F : ℕ → ℝ := fun k => Ch02.geometricWeight s 2 k * m k with hF
  set r : ℕ → ℝ := fun j => (Real.rpow (3 : ℝ) (2 * s - 3 / 4)) ^ j with hrdef
  set gt : ℝ := Ch02.geometricDiscount (3 / 8 : ℝ) 2 with hgt
  have hm0 : ∀ k, 0 ≤ m k := fun k =>
    maxDescendantSigmaStarInvMatrixNormAtScale_nonneg Q
      (sub_le_self _ (by exact_mod_cast Nat.zero_le k)) A
  have hw0 : ∀ k, 0 ≤ Ch02.geometricWeight s 2 k := fun k => by
    simpa [geometricWeight_eq_old] using
      HCPolySupport.geometricWeight_nonneg k
        (mul_nonneg hs0.le (by norm_num : (0 : ℝ) ≤ 2))
  have hF0 : ∀ k, 0 ≤ F k := fun k => mul_nonneg (hw0 k) (hm0 k)
  have hbase0 : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (2 * s - 3 / 4) :=
    Real.rpow_nonneg (by norm_num) _
  have hr0 : ∀ j, 0 ≤ r j := fun j => by rw [hrdef]; exact pow_nonneg hbase0 j
  have hr1 : Real.rpow (3 : ℝ) (2 * s - 3 / 4) < 1 :=
    rpow_three_two_mul_sub_lt_one hs
  have hsumF : Summable F := summable_weighted_maxDescendantSigmaStarInv_two Q A hs0
  have hsumr : Summable r := by
    rw [hrdef]; exact summable_geometric_of_lt_one hbase0 hr1
  have hgt0 : 0 ≤ gt := by
    rw [hgt]
    simpa [geometricDiscount_eq_old] using
      HCPolySupport.geometricDiscount_nonneg (s := (3 / 8 : ℝ)) (q := 2)
        (by norm_num)
  have hgt1 : gt ≤ 1 := by
    rw [hgt, Ch02.geometricDiscount]
    have : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (-(3 / 8 : ℝ) * 2) :=
      Real.rpow_nonneg (by norm_num) _
    linarith
  have hkernel : gt * ∑' j : ℕ, r j ≤ (3 / 8 - s)⁻¹ := by
    have hpole : (∑' j : ℕ, r j) ≤ (3 / 8 - s)⁻¹ :=
      tsum_geometric_threeEighths_le_pole hs0 hs
    have hnn : 0 ≤ ∑' j : ℕ, r j := tsum_nonneg hr0
    nlinarith [hpole, hnn, hgt0, hgt1]
  have hcoreSummable := summable_tsum_shifted_product F r hF0 hr0 hsumF hsumr
  have hlocal : ∀ n : ℕ,
      maxDescendantLowerEllipticityInvAtScale Q (Q.scale - (n : ℤ))
          (3 / 8 : ℝ) (.finite 2) A ≤
        ∑' j : ℕ, Ch02.geometricWeight (3 / 8 : ℝ) 2 j * m (n + j) := fun n => by
    simpa [hm] using
      maxDescendantLowerEllipticityInv_threeEighths_le_nested_tsum Q A n
  have hinner : ∀ n : ℕ, Summable (fun j : ℕ =>
      Ch02.geometricWeight (3 / 8 : ℝ) 2 j * m (n + j)) := by
    intro n
    have hbase : Summable (fun k : ℕ => Ch02.geometricWeight (3 / 8 : ℝ) 2 k * m k) :=
      summable_weighted_maxDescendantSigmaStarInv_two Q A
        (by norm_num : (0 : ℝ) < 3 / 8)
    have htail : Summable (fun j : ℕ =>
        Ch02.geometricWeight (3 / 8 : ℝ) 2 (j + n) * m (j + n)) :=
      (summable_nat_add_iff
        (f := fun k : ℕ => Ch02.geometricWeight (3 / 8 : ℝ) 2 k * m k) n).2 hbase
    refine (htail.mul_left (Real.rpow (3 : ℝ) ((3 / 8 : ℝ) * 2 * (n : ℝ)))).congr
      (fun j => ?_)
    have hweight : Ch02.geometricWeight (3 / 8 : ℝ) 2 j =
        Real.rpow (3 : ℝ) ((3 / 8 : ℝ) * 2 * (n : ℝ)) *
          Ch02.geometricWeight (3 / 8 : ℝ) 2 (j + n) := by
      simpa [geometricWeight_eq_old] using
        HCPolySupport.geometricWeight_shift (s := (3 / 8 : ℝ)) (q := 2) n j
    rw [hweight, show j + n = n + j from Nat.add_comm j n]
    ring
  have hcoreFiber : ∀ n : ℕ, Summable (fun j : ℕ => F (n + j) * r j) := by
    intro n
    have htail : Summable (fun j : ℕ => F (n + j)) := by
      simpa [Nat.add_comm] using (summable_nat_add_iff n).2 hsumF
    refine Summable.of_nonneg_of_le (fun j => mul_nonneg (hF0 _) (hr0 _))
      (fun j => ?_) htail
    have hrle : r j ≤ 1 := by
      rw [hrdef]; exact pow_le_one₀ hbase0 hr1.le
    exact mul_le_of_le_one_right (hF0 _) hrle
  have hlocalWeighted : ∀ n : ℕ,
      Ch02.geometricWeight s 2 n *
          maxDescendantLowerEllipticityInvAtScale Q (Q.scale - (n : ℤ))
            (3 / 8 : ℝ) (.finite 2) A ≤
        gt * ∑' j : ℕ, F (n + j) * r j := by
    intro n
    have hleft := mul_le_mul_of_nonneg_left (hlocal n) (hw0 n)
    have hterm : ∀ j : ℕ,
        Ch02.geometricWeight s 2 n *
            (Ch02.geometricWeight (3 / 8 : ℝ) 2 j * m (n + j)) =
          gt * (F (n + j) * r j) := by
      intro j
      have hrpow : r j = Real.rpow (3 : ℝ) ((2 * s - 3 / 4) * (j : ℝ)) := by
        simp only [hrdef, rpow_eq_pow]
        rw [← Real.rpow_natCast ((3 : ℝ) ^ (2 * s - 3 / 4)) j,
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      have hshift := geometricWeight_mul_threeEighths_shift s n j
      rw [hF, hgt, hrpow]
      calc Ch02.geometricWeight s 2 n *
              (Ch02.geometricWeight (3 / 8 : ℝ) 2 j * m (n + j))
          = (Ch02.geometricWeight s 2 n * Ch02.geometricWeight (3 / 8 : ℝ) 2 j) *
              m (n + j) := by ring
        _ = (Ch02.geometricDiscount (3 / 8 : ℝ) 2 *
              (Ch02.geometricWeight s 2 (n + j) *
                Real.rpow (3 : ℝ) ((2 * s - 3 / 4) * (j : ℝ)))) * m (n + j) := by
              rw [hshift]
        _ = Ch02.geometricDiscount (3 / 8 : ℝ) 2 *
              ((Ch02.geometricWeight s 2 (n + j) * m (n + j)) *
                Real.rpow (3 : ℝ) ((2 * s - 3 / 4) * (j : ℝ))) := by ring
    calc Ch02.geometricWeight s 2 n *
            maxDescendantLowerEllipticityInvAtScale Q (Q.scale - (n : ℤ))
              (3 / 8 : ℝ) (.finite 2) A
        ≤ Ch02.geometricWeight s 2 n *
            (∑' j : ℕ, Ch02.geometricWeight (3 / 8 : ℝ) 2 j * m (n + j)) := hleft
      _ = ∑' j : ℕ, Ch02.geometricWeight s 2 n *
            (Ch02.geometricWeight (3 / 8 : ℝ) 2 j * m (n + j)) :=
          ((hinner n).tsum_mul_left _).symm
      _ = ∑' j : ℕ, gt * (F (n + j) * r j) := tsum_congr hterm
      _ = gt * ∑' j : ℕ, F (n + j) * r j := (hcoreFiber n).tsum_mul_left gt
  have hrightSummable : Summable (fun n : ℕ => gt * ∑' j : ℕ, F (n + j) * r j) :=
    hcoreSummable.mul_left gt
  have hleft0 : ∀ n : ℕ, 0 ≤ Ch02.geometricWeight s 2 n *
      maxDescendantLowerEllipticityInvAtScale Q (Q.scale - (n : ℤ))
        (3 / 8 : ℝ) (.finite 2) A := by
    intro n
    refine mul_nonneg (hw0 n) ?_
    unfold maxDescendantLowerEllipticityInvAtScale
    exact finsetSupReal_nonneg _ _ fun R _ =>
      inv_nonneg.mpr (lambdaSq_finite_nonneg R A (by norm_num) (by norm_num))
  have hleftSummable : Summable (fun n : ℕ =>
      Ch02.geometricWeight s 2 n *
        maxDescendantLowerEllipticityInvAtScale Q (Q.scale - (n : ℤ))
          (3 / 8 : ℝ) (.finite 2) A) :=
    Summable.of_nonneg_of_le hleft0 hlocalWeighted hrightSummable
  refine ⟨?_, hleftSummable⟩
  have hseries := Summable.tsum_le_tsum hlocalWeighted hleftSummable hrightSummable
  have hcore := tsum_shifted_product_le F r hF0 hr0 hsumF hsumr
  rw [lambdaSq_two_inv_eq_tsum Q A hs0]
  calc (∑' n : ℕ, Ch02.geometricWeight s 2 n *
          maxDescendantLowerEllipticityInvAtScale Q (Q.scale - (n : ℤ))
            (3 / 8 : ℝ) (.finite 2) A)
      ≤ ∑' n : ℕ, gt * ∑' j : ℕ, F (n + j) * r j := hseries
    _ = gt * (∑' n : ℕ, ∑' j : ℕ, F (n + j) * r j) := hcoreSummable.tsum_mul_left gt
    _ ≤ gt * ((∑' n : ℕ, F n) * ∑' j : ℕ, r j) :=
        mul_le_mul_of_nonneg_left hcore hgt0
    _ = (gt * ∑' j : ℕ, r j) * ∑' n : ℕ, F n := by ring
    _ ≤ (3 / 8 - s)⁻¹ * ∑' n : ℕ, F n :=
        mul_le_mul_of_nonneg_right hkernel (tsum_nonneg hF0)

/-- **Descendant resummation in the corrected `3/8` gauge.**  The weighted
descendant sum of the per-cube lower coarse-grained ellipticity inverses
`lambda_{3/8,2}^{-1}(z + cube_n; a)` is bounded by the pole constant
`(3/8-s)^{-1}` times the global `lambda_{s,2}^{-1}(cube_0; a)`.  This is the
corrected form of the display in ABK26. -/
theorem tsum_weighted_maxDescendantLowerEllipticityInv_threeEighths_le
    (Q : TriadicCube d) (A : TriadicCoeffFamily d) {s : ℝ}
    (hs0 : 0 < s) (hs : s < 3 / 8) :
    (∑' n : ℕ, Ch02.geometricWeight s 2 n *
        maxDescendantLowerEllipticityInvAtScale Q (Q.scale - (n : ℤ))
          (3 / 8 : ℝ) (.finite 2) A)
      ≤ (3 / 8 - s)⁻¹ * (Ch02.lambdaSq Q s (.finite 2) A)⁻¹ :=
  (weighted_maxDescendantLowerEllipticityInv_package Q A hs0 hs).1

/-- Summability companion of
`tsum_weighted_maxDescendantLowerEllipticityInv_threeEighths_le`. -/
theorem summable_weighted_maxDescendantLowerEllipticityInv_threeEighths
    (Q : TriadicCube d) (A : TriadicCoeffFamily d) {s : ℝ}
    (hs0 : 0 < s) (hs : s < 3 / 8) :
    Summable (fun n : ℕ => Ch02.geometricWeight s 2 n *
      maxDescendantLowerEllipticityInvAtScale Q (Q.scale - (n : ℤ))
        (3 / 8 : ℝ) (.finite 2) A) :=
  (weighted_maxDescendantLowerEllipticityInv_package Q A hs0 hs).2

/-! ## The `Lambda_{s,2}` endpoint -/

omit [NeZero d] in
/-- Passage from a per-descendant one-cube estimate to the finite descendant
maximum, with a general same-index coefficient `c`. -/
theorem maxDescendantB_le_of_descendant_bound_coeff
    (Q : TriadicCube d) (A₀ A₁ : TriadicCoeffFamily d) {K c : ℝ}
    (hK : 0 ≤ K) (hc : 0 ≤ c)
    (hdesc : ∀ n : ℕ, ∀ R ∈ descendantsAtScale Q (Q.scale - (n : ℤ)),
      coarseBMatrixNorm R A₁ ≤
        c * coarseBMatrixNorm R A₀ +
          K * (Ch02.lambdaSq R (3 / 8 : ℝ) (.finite 2) A₀)⁻¹)
    (n : ℕ) :
    maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) A₁ ≤
      c * maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) A₀ +
        K * maxDescendantLowerEllipticityInvAtScale Q (Q.scale - (n : ℤ))
          (3 / 8 : ℝ) (.finite 2) A₀ := by
  have hk : Q.scale - (n : ℤ) ≤ Q.scale :=
    sub_le_self _ (by exact_mod_cast Nat.zero_le n)
  refine finsetSupReal_le _ (descendantsAtScale_nonempty Q hk) ?_
  intro R hR
  have hbase : coarseBMatrixNorm R A₀ ≤
      maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) A₀ :=
    coarseBMatrixNorm_le_maxDescendantBMatrixNormAtScale_of_mem_descendantsAtScale A₀ hR
  have hlocal : (Ch02.lambdaSq R (3 / 8 : ℝ) (.finite 2) A₀)⁻¹ ≤
      maxDescendantLowerEllipticityInvAtScale Q (Q.scale - (n : ℤ))
        (3 / 8 : ℝ) (.finite 2) A₀ := by
    unfold maxDescendantLowerEllipticityInvAtScale finsetSupReal
    exact le_csSup ((Set.toFinite _).image
      (fun S : TriadicCube d => (Ch02.lambdaSq S (3 / 8 : ℝ) (.finite 2) A₀)⁻¹)).bddAbove
      ⟨R, hR, rfl⟩
  exact (hdesc n R hR).trans
    (add_le_add (mul_le_mul_of_nonneg_left hbase hc)
      (mul_le_mul_of_nonneg_left hlocal hK))

/-- **The `Lambda_{s,2}` endpoint with a general same-index coefficient `c`.**
Its sole analytic input `hdesc` is the per-descendant one-cube estimate; the
finite maxima, the nested descendant expansion, the triangular reindexing, and
both `q = 2` observable rewrites happen inside this proof. -/
theorem LambdaSq_two_le_of_descendant_bound_coeff
    (Q : TriadicCube d) (A₀ A₁ : TriadicCoeffFamily d) {K c s : ℝ}
    (hK : 0 ≤ K) (hc : 0 ≤ c) (hs0 : 0 < s) (hs : s < 3 / 8)
    (hdesc : ∀ n : ℕ, ∀ R ∈ descendantsAtScale Q (Q.scale - (n : ℤ)),
      coarseBMatrixNorm R A₁ ≤
        c * coarseBMatrixNorm R A₀ +
          K * (Ch02.lambdaSq R (3 / 8 : ℝ) (.finite 2) A₀)⁻¹) :
    Ch02.LambdaSq Q s (.finite 2) A₁ ≤
      c * Ch02.LambdaSq Q s (.finite 2) A₀ +
        K * (3 / 8 - s)⁻¹ * (Ch02.lambdaSq Q s (.finite 2) A₀)⁻¹ := by
  set b₀ : ℕ → ℝ := fun n =>
    maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) A₀ with hb₀
  set b₁ : ℕ → ℝ := fun n =>
    maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) A₁ with hb₁
  set l : ℕ → ℝ := fun n =>
    maxDescendantLowerEllipticityInvAtScale Q (Q.scale - (n : ℤ))
      (3 / 8 : ℝ) (.finite 2) A₀ with hl
  set w : ℕ → ℝ := Ch02.geometricWeight s 2 with hw
  have hw0 : ∀ n, 0 ≤ w n := fun n => by
    rw [hw]
    simpa [geometricWeight_eq_old] using
      HCPolySupport.geometricWeight_nonneg n
        (mul_nonneg hs0.le (by norm_num : (0 : ℝ) ≤ 2))
  have hbase0 : Summable (fun n : ℕ => w n * b₀ n) :=
    summable_weighted_maxDescendantB_two Q A₀ hs0
  have hbase1 : Summable (fun n : ℕ => w n * b₁ n) :=
    summable_weighted_maxDescendantB_two Q A₁ hs0
  have hlocal : (∑' n : ℕ, w n * l n) ≤
      (3 / 8 - s)⁻¹ * (Ch02.lambdaSq Q s (.finite 2) A₀)⁻¹ :=
    tsum_weighted_maxDescendantLowerEllipticityInv_threeEighths_le Q A₀ hs0 hs
  have hlocalSummable : Summable (fun n : ℕ => w n * l n) :=
    summable_weighted_maxDescendantLowerEllipticityInv_threeEighths Q A₀ hs0 hs
  have hmax : ∀ n : ℕ, b₁ n ≤ c * b₀ n + K * l n := fun n =>
    maxDescendantB_le_of_descendant_bound_coeff Q A₀ A₁ hK hc hdesc n
  have hterm : ∀ n : ℕ, w n * b₁ n ≤ c * (w n * b₀ n) + K * (w n * l n) := by
    intro n
    calc w n * b₁ n ≤ w n * (c * b₀ n + K * l n) :=
          mul_le_mul_of_nonneg_left (hmax n) (hw0 n)
      _ = c * (w n * b₀ n) + K * (w n * l n) := by ring
  have hfirstSummable : Summable (fun n : ℕ => c * (w n * b₀ n)) := hbase0.mul_left c
  have hsecondSummable : Summable (fun n : ℕ => K * (w n * l n)) :=
    hlocalSummable.mul_left K
  have hrightSummable : Summable (fun n : ℕ =>
      c * (w n * b₀ n) + K * (w n * l n)) := hfirstSummable.add hsecondSummable
  have hsum := Summable.tsum_le_tsum hterm hbase1 hrightSummable
  rw [LambdaSq_two_eq_tsum Q A₁ hs0, LambdaSq_two_eq_tsum Q A₀ hs0]
  calc (∑' n : ℕ, w n * b₁ n)
      ≤ ∑' n : ℕ, (c * (w n * b₀ n) + K * (w n * l n)) := hsum
    _ = c * (∑' n : ℕ, w n * b₀ n) + K * (∑' n : ℕ, w n * l n) := by
        rw [hfirstSummable.tsum_add hsecondSummable, hbase0.tsum_mul_left,
          hlocalSummable.tsum_mul_left]
    _ ≤ c * (∑' n : ℕ, w n * b₀ n) +
          K * ((3 / 8 - s)⁻¹ * (Ch02.lambdaSq Q s (.finite 2) A₀)⁻¹) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hlocal hK)
    _ = c * (∑' n : ℕ, w n * b₀ n) +
          K * (3 / 8 - s)⁻¹ * (Ch02.lambdaSq Q s (.finite 2) A₀)⁻¹ := by ring

/-- **The `Lambda_{s,2}` endpoint of the corrected coarse-gauge argument.**
Its sole analytic input `hdesc` is the per-descendant one-cube estimate; the
finite maxima, the nested descendant expansion, the triangular reindexing, and
both `q = 2` observable rewrites happen inside this proof.  The `4` and the
`(3/8-s)^{-1}` pole are exactly the constants appearing in the frozen
`bigLambda_sensitivity`. -/
theorem LambdaSq_two_le_of_descendant_bound
    (Q : TriadicCube d) (A₀ A₁ : TriadicCoeffFamily d) {K s : ℝ} (hK : 0 ≤ K)
    (hs0 : 0 < s) (hs : s < 3 / 8)
    (hdesc : ∀ n : ℕ, ∀ R ∈ descendantsAtScale Q (Q.scale - (n : ℤ)),
      coarseBMatrixNorm R A₁ ≤
        4 * coarseBMatrixNorm R A₀ +
          K * (Ch02.lambdaSq R (3 / 8 : ℝ) (.finite 2) A₀)⁻¹) :
    Ch02.LambdaSq Q s (.finite 2) A₁ ≤
      4 * Ch02.LambdaSq Q s (.finite 2) A₀ +
        K * (3 / 8 - s)⁻¹ * (Ch02.lambdaSq Q s (.finite 2) A₀)⁻¹ :=
  LambdaSq_two_le_of_descendant_bound_coeff Q A₀ A₁ hK
    (by norm_num : (0 : ℝ) ≤ 4) hs0 hs hdesc

end

end Algsuperdiff.Section24.Sensitivity.Provider.Multiscale
