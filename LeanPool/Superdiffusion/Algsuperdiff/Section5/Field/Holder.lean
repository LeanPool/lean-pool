/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Field.Growth
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.Step3Arith
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.BoundsEaL.TailSummability
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Holder

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# A quantitative subcritical Hölder modulus for the stream matrix

The sharp shell carrier has a linear weight at the shell/cube crossover.  At
the critical exponent this produces a logarithmic loss.  Dropping from `gamma`
to `gamma / 2` leaves a geometric factor which absorbs that weight.  This file
performs that deterministic summation and records a modulus whose dependence on
the observation radius is linear.
-/

namespace Algsuperdiff.Section5.Field

open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Stream
open HCPolySupport
open HCPolySupport.Book.Ch02
open scoped Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-- The subcritical Hölder exponent: half the shell exponent `gamma`. -/
def streamHolderExponent (M : ABKModel d) : ℝ := M.gamma / 2

theorem streamHolderExponent_pos (M : ABKModel d) : 0 < streamHolderExponent M := by
  unfold streamHolderExponent
  linarith only [M.shellPrefix.gamma_pos]

/-- A concrete sample constant for the sharp two-sided shell estimates. -/
def streamSharpConst (M : ABKModel d) (omega : FullSample d M.gamma) : ℕ :=
  Classical.choose (fullTailGood_sharp omega.2)

theorem streamSharpConst_spec (M : ABKModel d) (omega : FullSample d M.gamma) :
    SharpTailBounded M.gamma (streamSharpConst M omega) omega.1 :=
  Classical.choose_spec (fullTailGood_sharp omega.2)

/-- The geometric ratio for the low-frequency part of the Hölder estimate. -/
def holderLowerRatio (M : ABKModel d) : ℝ := Real.rpow 3 (-M.gamma)

/-- The geometric ratio for the high-frequency part of the Hölder estimate. -/
def holderUpperRatio (M : ABKModel d) : ℝ := Real.rpow 3 (M.gamma - 1)

/-- The geometric ratio determined by the stream Hölder exponent. -/
def holderGapRatio (M : ABKModel d) : ℝ :=
  Real.rpow 3 (-streamHolderExponent M)

private theorem holderLowerRatio_pos (M : ABKModel d) : 0 < holderLowerRatio M :=
  Real.rpow_pos_of_pos (by norm_num) _

private theorem holderLowerRatio_lt_one (M : ABKModel d) : holderLowerRatio M < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    (neg_neg_of_pos M.shellPrefix.gamma_pos)

private theorem holderUpperRatio_pos (M : ABKModel d) : 0 < holderUpperRatio M :=
  Real.rpow_pos_of_pos (by norm_num) _

private theorem holderUpperRatio_lt_one (M : ABKModel d) : holderUpperRatio M < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    (by linarith only [M.shellPrefix.gamma_le_quarter])

private theorem holderGapRatio_pos (M : ABKModel d) : 0 < holderGapRatio M :=
  Real.rpow_pos_of_pos (by norm_num) _

private theorem holderGapRatio_lt_one (M : ABKModel d) : holderGapRatio M < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    (neg_neg_of_pos (streamHolderExponent_pos M))

/-- The weighted geometric sum for the low-frequency Hölder bound. -/
def holderLowerSum (M : ABKModel d) : ℝ :=
  ∑' r : ℕ, ((r : ℝ) + 1) * holderLowerRatio M ^ r

/-- The weighted geometric sum for the high-frequency Hölder bound. -/
def holderUpperSum (M : ABKModel d) : ℝ :=
  ∑' r : ℕ, ((r : ℝ) + 1) * holderUpperRatio M ^ r

/-- The weighted geometric sum for the Hölder-exponent gap bound. -/
def holderGapSum (M : ABKModel d) : ℝ :=
  ∑' r : ℕ, ((r : ℝ) + 1) * holderGapRatio M ^ r

private theorem summable_holderLower (M : ABKModel d) :
    Summable fun r : ℕ => ((r : ℝ) + 1) * holderLowerRatio M ^ r :=
  Section4.Provider.Annular.summable_poly1_geom
    (holderLowerRatio_pos M).le (holderLowerRatio_lt_one M)

private theorem summable_holderUpper (M : ABKModel d) :
    Summable fun r : ℕ => ((r : ℝ) + 1) * holderUpperRatio M ^ r :=
  Section4.Provider.Annular.summable_poly1_geom
    (holderUpperRatio_pos M).le (holderUpperRatio_lt_one M)

private theorem summable_holderGap (M : ABKModel d) :
    Summable fun r : ℕ => ((r : ℝ) + 1) * holderGapRatio M ^ r :=
  Section4.Provider.Annular.summable_poly1_geom
    (holderGapRatio_pos M).le (holderGapRatio_lt_one M)

private theorem holderLowerSum_nonneg (M : ABKModel d) : 0 ≤ holderLowerSum M :=
  tsum_nonneg fun _ => mul_nonneg (by positivity)
    (pow_nonneg (holderLowerRatio_pos M).le _)

private theorem holderUpperSum_nonneg (M : ABKModel d) : 0 ≤ holderUpperSum M :=
  tsum_nonneg fun _ => mul_nonneg (by positivity)
    (pow_nonneg (holderUpperRatio_pos M).le _)

private theorem holderGapSum_nonneg (M : ABKModel d) : 0 ≤ holderGapSum M :=
  tsum_nonneg fun _ => mul_nonneg (by positivity)
    (pow_nonneg (holderGapRatio_pos M).le _)

private theorem sharpTailWeight_sub_crossover_le (m ell : ℤ) (r : ℕ) :
    sharpTailWeight (m - (r : ℤ)) ell ≤
      3 * sharpTailWeight m ell * ((r : ℝ) + 1) := by
  have habs : (m - (r : ℤ)).natAbs ≤ m.natAbs + r := by
    exact (Int.natAbs_sub_le m (r : ℤ)).trans_eq (by simp)
  unfold sharpTailWeight
  have habsR : ((m - (r : ℤ)).natAbs : ℝ) ≤ (m.natAbs : ℝ) + (r : ℝ) := by
    exact_mod_cast habs
  have hm0 : (0 : ℝ) ≤ (m.natAbs : ℝ) := Nat.cast_nonneg _
  have he0 : (0 : ℝ) ≤ (ell.natAbs : ℝ) := Nat.cast_nonneg _
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg _
  push_cast
  nlinarith only [habsR, hm0, he0, hr0]

private theorem sharpTailWeight_add_crossover_le (m ell : ℤ) (r : ℕ) :
    sharpTailWeight (m + 1 + (r : ℤ)) ell ≤
      3 * sharpTailWeight m ell * ((r : ℝ) + 1) := by
  have habs : (m + 1 + (r : ℤ)).natAbs ≤ m.natAbs + 1 + r := by
    have h1 := Int.natAbs_add_le m (1 : ℤ)
    have h2 := Int.natAbs_add_le (m + 1) (r : ℤ)
    simp only [Int.natAbs_one, Int.natAbs_natCast] at h1 h2
    omega
  unfold sharpTailWeight
  have habsR : ((m + 1 + (r : ℤ)).natAbs : ℝ) ≤
      (m.natAbs : ℝ) + 1 + (r : ℝ) := by
    exact_mod_cast habs
  have hm0 : (0 : ℝ) ≤ (m.natAbs : ℝ) := Nat.cast_nonneg _
  have he0 : (0 : ℝ) ≤ (ell.natAbs : ℝ) := Nat.cast_nonneg _
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg _
  push_cast
  nlinarith only [habsR, hm0, he0, hr0]

private theorem sharpValueScale_crossover (M : ABKModel d) (m : ℤ) (r : ℕ) :
    Real.rpow 3 (M.gamma * ((m - (r : ℤ) : ℤ) : ℝ)) =
      Real.rpow 3 (M.gamma * (m : ℝ)) * holderLowerRatio M ^ r := by
  rw [show M.gamma * ((m - (r : ℤ) : ℤ) : ℝ) =
      M.gamma * (m : ℝ) + (-M.gamma) * (r : ℝ) by push_cast; ring,
    Section4.Provider.BoundsEaL.rpow3_add]
  congr 1
  exact Section4.Provider.BoundsEaL.rpow3_mul_natCast (-M.gamma) r

private theorem sharpGradientScale_crossover (M : ABKModel d) (m : ℤ) (r : ℕ) :
    Real.rpow 3 ((M.gamma - 1) * ((m + 1 + (r : ℤ) : ℤ) : ℝ)) =
      Real.rpow 3 ((M.gamma - 1) * ((m : ℝ) + 1)) * holderUpperRatio M ^ r := by
  rw [show (M.gamma - 1) * ((m + 1 + (r : ℤ) : ℤ) : ℝ) =
      (M.gamma - 1) * ((m : ℝ) + 1) + (M.gamma - 1) * (r : ℝ) by
        push_cast; ring,
    Section4.Provider.BoundsEaL.rpow3_add]
  congr 1
  exact Section4.Provider.BoundsEaL.rpow3_mul_natCast (M.gamma - 1) r

/-- The shell mean-value estimate between two points of the same origin cube. -/
theorem norm_sub_le_of_mem_openOriginCube (ell : ℤ) (j : ShellField d)
    {x y : Vec d} (hx : x ∈ openCubeSet (originCube d ell))
    (hy : y ∈ openCubeSet (originCube d ell)) :
    ‖j x - j y‖ ≤ (d : ℝ) * localCubeDerivNorm ell j * ‖x - y‖ := by
  have hbound := Section5.Support.holderSeminormBoundOn_one_of_hasFDerivAt
    (U := openCubeSet (originCube d ell)) (convex_openCubeSet _)
    (F := fun z : Vec d => j z) (F' := fun z : Vec d => ShellField.deriv j z)
    (fun z _ => j.hasFDerivAt z)
    (L := (d : ℝ) * localCubeDerivNorm ell j)
    (fun z hz => (Section5.Support.norm_le_dim_mul_matrixDerivativeNorm
        (ShellField.deriv j z)).trans
      (mul_le_mul_of_nonneg_left
        (matrixDerivativeNorm_deriv_le_localCubeDerivNorm ell j hz)
        (Nat.cast_nonneg d)))
  simpa only [Real.rpow_one] using hbound x hx y hy

private theorem abs_entry_sub_le_of_mem_openOriginCube_two (ell : ℤ)
    (j : ShellField d) {x y : Vec d}
    (hx : x ∈ openCubeSet (originCube d ell))
    (hy : y ∈ openCubeSet (originCube d ell)) (i k : Fin d) :
    |j x i k - j y i k| ≤ (d : ℝ) * localCubeDerivNorm ell j * ‖x - y‖ := by
  refine le_trans ?_ (norm_sub_le_of_mem_openOriginCube ell j hx hy)
  have h := Matrix.norm_entry_le_entrywise_sup_norm (j x - j y) (i := i) (j := k)
  simpa only [Matrix.sub_apply, Real.norm_eq_abs] using h

private theorem localCubeDerivNorm_le_sharpGradientGauge
    (ell n : ℤ) (omega : CutoffSample d) :
    localCubeDerivNorm ell (omega.1 n) ≤ sharpGradientGauge ell n omega := by
  rw [sharpGradientGauge_eq]
  exact le_add_of_nonneg_right
    (mul_nonneg (zpow_pos (by norm_num) _).le (localCubeSecondDerivNorm_nonneg _ _))

private theorem matrixOperatorNorm_le_sum_abs_entries_holder (A : Mat d) :
    matrixOperatorNorm A ≤ ∑ i, ∑ k, |A i k| := by
  have h := matrixOperatorNorm_le_matrixOperatorNorm_add_sum_abs_sub_entries A (0 : Mat d)
  simpa only [matrixOperatorNorm_zero, Matrix.zero_apply, sub_zero, zero_add] using h

private theorem sum_abs_entries_le_of_forall_holder (A : Mat d) {b : ℝ}
    (h : ∀ i k, |A i k| ≤ b) : (∑ i, ∑ k, |A i k|) ≤ (d : ℝ) ^ 2 * b := by
  calc
    (∑ i, ∑ k, |A i k|) ≤ ∑ _i : Fin d, ∑ _k : Fin d, b := by
      exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => h i k
    _ = (d : ℝ) ^ 2 * b := by
      simp [pow_two]
      ring

private theorem summable_shellEntry_descending (omega : CutoffSample d)
    (ell m : ℤ) {x : Vec d} (hx : x ∈ openCubeSet (originCube d ell))
    (i k : Fin d) :
    Summable fun r : ℕ => omega.1 (m - (r : ℤ)) x i k := by
  exact (summable_localCubeControl_descending omega ell m).of_norm_bounded fun r => by
    simpa only [Real.norm_eq_abs] using
      abs_entry_le_localCubeControl ell (omega.1 (m - (r : ℤ))) hx i k

private theorem cutoff_entry_sub_eq_tsum (omega : CutoffSample d)
    (ell m : ℤ) {x y : Vec d}
    (hx : x ∈ openCubeSet (originCube d ell))
    (hy : y ∈ openCubeSet (originCube d ell)) (i k : Fin d) :
    cutoff m omega x i k - cutoff m omega y i k =
      ∑' r : ℕ, (omega.1 (m - (r : ℤ)) x i k -
        omega.1 (m - (r : ℤ)) y i k) := by
  rw [cutoff_apply_entry, cutoff_apply_entry,
    (summable_shellEntry_descending omega ell m hx i k).tsum_sub
      (summable_shellEntry_descending omega ell m hy i k)]

private theorem summable_lowerCrossoverMajorant (M : ABKModel d)
    (C : ℕ) (m ell : ℤ) :
    Summable fun r : ℕ =>
      6 * (C : ℝ) * sharpTailWeight m ell *
        Real.rpow 3 (M.gamma * (m : ℝ)) *
          (((r : ℝ) + 1) * holderLowerRatio M ^ r) :=
  (((summable_holderLower M).mul_left
    (6 * (C : ℝ) * sharpTailWeight m ell)).mul_left
      (Real.rpow 3 (M.gamma * (m : ℝ)))).congr fun r => by ring

private theorem abs_cutoff_entry_sub_le_crossover (M : ABKModel d)
    (omega : FullSample d M.gamma) {C : ℕ}
    (hC : SharpTailBounded M.gamma C omega.1) (ell m : ℤ)
    {x y : Vec d} (hx : x ∈ openCubeSet (originCube d ell))
    (hy : y ∈ openCubeSet (originCube d ell)) (i k : Fin d) :
    |cutoff m omega.1 x i k - cutoff m omega.1 y i k| ≤
      6 * (C : ℝ) * sharpTailWeight m ell *
        Real.rpow 3 (M.gamma * (m : ℝ)) * holderLowerSum M := by
  have hmaj : ∀ r : ℕ,
      |omega.1.1 (m - (r : ℤ)) x i k - omega.1.1 (m - (r : ℤ)) y i k| ≤
        6 * (C : ℝ) * sharpTailWeight m ell *
          Real.rpow 3 (M.gamma * (m : ℝ)) *
            (((r : ℝ) + 1) * holderLowerRatio M ^ r) := by
    intro r
    have hxv := abs_entry_le_localCubeControl ell
      (omega.1.1 (m - (r : ℤ))) hx i k
    have hyv := abs_entry_le_localCubeControl ell
      (omega.1.1 (m - (r : ℤ))) hy i k
    have hshell := (hC (m - (r : ℤ)) ell).1
    have hw := sharpTailWeight_sub_crossover_le m ell r
    have hC0 : (0 : ℝ) ≤ (C : ℝ) := Nat.cast_nonneg C
    have hscale0 : 0 ≤ Real.rpow 3 (M.gamma * (m : ℝ)) :=
      (Real.rpow_pos_of_pos (by norm_num) _).le
    have hratio0 : 0 ≤ holderLowerRatio M ^ r :=
      pow_nonneg (holderLowerRatio_pos M).le _
    calc
      |omega.1.1 (m - (r : ℤ)) x i k - omega.1.1 (m - (r : ℤ)) y i k| ≤
          |omega.1.1 (m - (r : ℤ)) x i k| +
            |omega.1.1 (m - (r : ℤ)) y i k| := abs_sub _ _
      _ ≤ 2 * localCubeControl ell (omega.1.1 (m - (r : ℤ))) := by
        linarith only [hxv, hyv]
      _ ≤ 2 * ((C : ℝ) * Real.rpow 3
          (M.gamma * ((m - (r : ℤ) : ℤ) : ℝ)) *
            sharpTailWeight (m - (r : ℤ)) ell) :=
        mul_le_mul_of_nonneg_left hshell (by norm_num)
      _ = 2 * ((C : ℝ) *
          (Real.rpow 3 (M.gamma * (m : ℝ)) * holderLowerRatio M ^ r) *
            sharpTailWeight (m - (r : ℤ)) ell) := by
        rw [sharpValueScale_crossover]
      _ ≤ 2 * ((C : ℝ) *
          (Real.rpow 3 (M.gamma * (m : ℝ)) * holderLowerRatio M ^ r) *
            (3 * sharpTailWeight m ell * ((r : ℝ) + 1))) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hw
            (mul_nonneg hC0 (mul_nonneg hscale0 hratio0))) (by norm_num)
      _ = 6 * (C : ℝ) * sharpTailWeight m ell *
          Real.rpow 3 (M.gamma * (m : ℝ)) *
            (((r : ℝ) + 1) * holderLowerRatio M ^ r) := by ring
  have hsummableAbs : Summable fun r : ℕ =>
      |omega.1.1 (m - (r : ℤ)) x i k - omega.1.1 (m - (r : ℤ)) y i k| :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hmaj
      (summable_lowerCrossoverMajorant M C m ell)
  have hsummableNorm : Summable fun r : ℕ =>
      ‖omega.1.1 (m - (r : ℤ)) x i k - omega.1.1 (m - (r : ℤ)) y i k‖ := by
    simpa only [Real.norm_eq_abs] using hsummableAbs
  rw [cutoff_entry_sub_eq_tsum omega ell m hx hy i k]
  calc
    |∑' r : ℕ, (omega.1.1 (m - (r : ℤ)) x i k -
        omega.1.1 (m - (r : ℤ)) y i k)| ≤
      ∑' r : ℕ, |omega.1.1 (m - (r : ℤ)) x i k -
          omega.1.1 (m - (r : ℤ)) y i k| := by
      rw [← Real.norm_eq_abs]
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hsummableNorm
    _ ≤ ∑' r : ℕ, 6 * (C : ℝ) * sharpTailWeight m ell *
        Real.rpow 3 (M.gamma * (m : ℝ)) *
          (((r : ℝ) + 1) * holderLowerRatio M ^ r) :=
      hsummableAbs.tsum_le_tsum hmaj (summable_lowerCrossoverMajorant M C m ell)
    _ = 6 * (C : ℝ) * sharpTailWeight m ell *
        Real.rpow 3 (M.gamma * (m : ℝ)) * holderLowerSum M := by
      unfold holderLowerSum
      rw [← tsum_mul_left]

private theorem summable_upperCrossoverMajorant (M : ABKModel d)
    (C : ℕ) (m ell : ℤ) (h : ℝ) :
    Summable fun r : ℕ =>
      3 * (d : ℝ) * (C : ℝ) * sharpTailWeight m ell * h *
        Real.rpow 3 ((M.gamma - 1) * ((m : ℝ) + 1)) *
          (((r : ℝ) + 1) * holderUpperRatio M ^ r) :=
  (((((summable_holderUpper M).mul_left
    (3 * (d : ℝ) * (C : ℝ) * sharpTailWeight m ell)).mul_left h).mul_left
      (Real.rpow 3 ((M.gamma - 1) * ((m : ℝ) + 1))))).congr fun r => by ring

private theorem abs_upperTail_entry_sub_le_crossover (M : ABKModel d)
    (omega : FullSample d M.gamma) {C : ℕ}
    (hC : SharpTailBounded M.gamma C omega.1) (ell m : ℤ)
    {x y : Vec d} (hx : x ∈ openCubeSet (originCube d ell))
    (hy : y ∈ openCubeSet (originCube d ell)) (i k : Fin d) :
    |∑' r : ℕ, (omega.1.1 (m + 1 + (r : ℤ)) x i k -
        omega.1.1 (m + 1 + (r : ℤ)) y i k)| ≤
      3 * (d : ℝ) * (C : ℝ) * sharpTailWeight m ell * ‖x - y‖ *
        Real.rpow 3 ((M.gamma - 1) * ((m : ℝ) + 1)) * holderUpperSum M := by
  have hmaj : ∀ r : ℕ,
      |omega.1.1 (m + 1 + (r : ℤ)) x i k -
          omega.1.1 (m + 1 + (r : ℤ)) y i k| ≤
        3 * (d : ℝ) * (C : ℝ) * sharpTailWeight m ell * ‖x - y‖ *
          Real.rpow 3 ((M.gamma - 1) * ((m : ℝ) + 1)) *
            (((r : ℝ) + 1) * holderUpperRatio M ^ r) := by
    intro r
    have hmv := abs_entry_sub_le_of_mem_openOriginCube_two ell
      (omega.1.1 (m + 1 + (r : ℤ))) hx hy i k
    have hgrad := localCubeDerivNorm_le_sharpGradientGauge ell
      (m + 1 + (r : ℤ)) omega.1
    have hshell := (hC (m + 1 + (r : ℤ)) ell).2
    have hw := sharpTailWeight_add_crossover_le m ell r
    calc
      |omega.1.1 (m + 1 + (r : ℤ)) x i k -
          omega.1.1 (m + 1 + (r : ℤ)) y i k| ≤
        (d : ℝ) * localCubeDerivNorm ell
          (omega.1.1 (m + 1 + (r : ℤ))) * ‖x - y‖ := hmv
      _ ≤ (d : ℝ) * sharpGradientGauge ell (m + 1 + (r : ℤ)) omega.1 *
          ‖x - y‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hgrad (Nat.cast_nonneg d)) (norm_nonneg (x - y))
      _ ≤ (d : ℝ) * ((C : ℝ) * Real.rpow 3
          ((M.gamma - 1) * ((m + 1 + (r : ℤ) : ℤ) : ℝ)) *
            sharpTailWeight (m + 1 + (r : ℤ)) ell) * ‖x - y‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hshell (Nat.cast_nonneg d)) (norm_nonneg (x - y))
      _ = (d : ℝ) * ((C : ℝ) *
          (Real.rpow 3 ((M.gamma - 1) * ((m : ℝ) + 1)) *
            holderUpperRatio M ^ r) *
              sharpTailWeight (m + 1 + (r : ℤ)) ell) * ‖x - y‖ := by
        rw [sharpGradientScale_crossover]
      _ ≤ (d : ℝ) * ((C : ℝ) *
          (Real.rpow 3 ((M.gamma - 1) * ((m : ℝ) + 1)) *
            holderUpperRatio M ^ r) *
              (3 * sharpTailWeight m ell * ((r : ℝ) + 1))) * ‖x - y‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg d)
        apply mul_le_mul_of_nonneg_left hw
        exact mul_nonneg (Nat.cast_nonneg C)
          (mul_nonneg (Real.rpow_pos_of_pos (by norm_num) _).le
            (pow_nonneg (holderUpperRatio_pos M).le _))
      _ = 3 * (d : ℝ) * (C : ℝ) * sharpTailWeight m ell * ‖x - y‖ *
          Real.rpow 3 ((M.gamma - 1) * ((m : ℝ) + 1)) *
            (((r : ℝ) + 1) * holderUpperRatio M ^ r) := by ring
  have hsummableAbs : Summable fun r : ℕ =>
      |omega.1.1 (m + 1 + (r : ℤ)) x i k -
        omega.1.1 (m + 1 + (r : ℤ)) y i k| :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hmaj
      (summable_upperCrossoverMajorant M C m ell ‖x - y‖)
  have hsummableNorm : Summable fun r : ℕ =>
      ‖omega.1.1 (m + 1 + (r : ℤ)) x i k -
        omega.1.1 (m + 1 + (r : ℤ)) y i k‖ := by
    simpa only [Real.norm_eq_abs] using hsummableAbs
  calc
    |∑' r : ℕ, (omega.1.1 (m + 1 + (r : ℤ)) x i k -
        omega.1.1 (m + 1 + (r : ℤ)) y i k)| ≤
      ∑' r : ℕ, |omega.1.1 (m + 1 + (r : ℤ)) x i k -
        omega.1.1 (m + 1 + (r : ℤ)) y i k| := by
      rw [← Real.norm_eq_abs]
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hsummableNorm
    _ ≤ ∑' r : ℕ, 3 * (d : ℝ) * (C : ℝ) * sharpTailWeight m ell * ‖x - y‖ *
        Real.rpow 3 ((M.gamma - 1) * ((m : ℝ) + 1)) *
          (((r : ℝ) + 1) * holderUpperRatio M ^ r) :=
      hsummableAbs.tsum_le_tsum hmaj
        (summable_upperCrossoverMajorant M C m ell ‖x - y‖)
    _ = 3 * (d : ℝ) * (C : ℝ) * sharpTailWeight m ell * ‖x - y‖ *
        Real.rpow 3 ((M.gamma - 1) * ((m : ℝ) + 1)) * holderUpperSum M := by
      unfold holderUpperSum
      rw [← tsum_mul_left]

private theorem streamField_entry_sub_eq_crossover {gamma : ℝ}
    (omega : FullSample d gamma)
    (m : ℤ) (x y : Vec d) (i k : Fin d) :
    streamField omega x i k - streamField omega y i k =
      (cutoff m omega.1 x i k - cutoff m omega.1 y i k) +
        ∑' r : ℕ, (omega.1.1 (m + 1 + (r : ℤ)) x i k -
          omega.1.1 (m + 1 + (r : ℤ)) y i k) := by
  have hx := streamField_eq_cutoff_add_upperTail omega m x i k
  have hy := streamField_eq_cutoff_add_upperTail omega m y i k
  have hsx := summable_streamIncrement_ascending omega (m + 1) x i k
  have hsy := summable_streamIncrement_ascending omega (m + 1) y i k
  have hsub :
      (∑' r : ℕ, (omega.1.1 (m + 1 + (r : ℤ)) x i k -
        omega.1.1 (m + 1 + (r : ℤ)) 0 i k)) -
      (∑' r : ℕ, (omega.1.1 (m + 1 + (r : ℤ)) y i k -
        omega.1.1 (m + 1 + (r : ℤ)) 0 i k)) =
      ∑' r : ℕ, (omega.1.1 (m + 1 + (r : ℤ)) x i k -
        omega.1.1 (m + 1 + (r : ℤ)) y i k) := by
    rw [← hsx.tsum_sub hsy]
    apply tsum_congr
    intro r
    ring
  rw [hx, hy, ← hsub]
  ring

private theorem abs_streamField_entry_sub_le_crossover (M : ABKModel d)
    (omega : FullSample d M.gamma) {C : ℕ}
    (hC : SharpTailBounded M.gamma C omega.1) (ell m : ℤ)
    {x y : Vec d} (hx : x ∈ openCubeSet (originCube d ell))
    (hy : y ∈ openCubeSet (originCube d ell)) (i k : Fin d) :
    |streamField omega x i k - streamField omega y i k| ≤
      (C : ℝ) * sharpTailWeight m ell *
        (6 * holderLowerSum M * Real.rpow 3 (M.gamma * (m : ℝ)) +
          3 * (d : ℝ) * holderUpperSum M * ‖x - y‖ *
            Real.rpow 3 ((M.gamma - 1) * ((m : ℝ) + 1))) := by
  rw [streamField_entry_sub_eq_crossover omega m x y i k]
  have hlo := abs_cutoff_entry_sub_le_crossover M omega hC ell m hx hy i k
  have hup := abs_upperTail_entry_sub_le_crossover M omega hC ell m hx hy i k
  calc
    |cutoff m omega.1 x i k - cutoff m omega.1 y i k +
        ∑' r : ℕ, (omega.1.1 (m + 1 + (r : ℤ)) x i k -
          omega.1.1 (m + 1 + (r : ℤ)) y i k)| ≤
      |cutoff m omega.1 x i k - cutoff m omega.1 y i k| +
        |∑' r : ℕ, (omega.1.1 (m + 1 + (r : ℤ)) x i k -
          omega.1.1 (m + 1 + (r : ℤ)) y i k)| := abs_add_le _ _
    _ ≤ 6 * (C : ℝ) * sharpTailWeight m ell *
          Real.rpow 3 (M.gamma * (m : ℝ)) * holderLowerSum M +
        3 * (d : ℝ) * (C : ℝ) * sharpTailWeight m ell * ‖x - y‖ *
          Real.rpow 3 ((M.gamma - 1) * ((m : ℝ) + 1)) * holderUpperSum M :=
      add_le_add hlo hup
    _ = (C : ℝ) * sharpTailWeight m ell *
        (6 * holderLowerSum M * Real.rpow 3 (M.gamma * (m : ℝ)) +
          3 * (d : ℝ) * holderUpperSum M * ‖x - y‖ *
            Real.rpow 3 ((M.gamma - 1) * ((m : ℝ) + 1))) := by ring

private theorem norm_le_sqrt_vecNormSq_holder (x : Vec d) :
    ‖x‖ ≤ Real.sqrt (vecNormSq x) := by
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
  rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (HCPolySupport.sq_apply_le_vecNormSq x i)

private theorem exists_holder_originCube {R : ℝ} (hR : 1 ≤ R)
    {x y : Vec d} (hx : Real.sqrt (vecNormSq x) ≤ R)
    (hy : Real.sqrt (vecNormSq y) ≤ R) :
    ∃ ell : ℕ,
      x ∈ openCubeSet (originCube d (ell : ℤ)) ∧
      y ∈ openCubeSet (originCube d (ell : ℤ)) ∧
      (ell : ℝ) ≤ 6 * R := by
  have hRpos : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR
  have hex : ∃ n : ℕ, 2 * R < (3 : ℝ) ^ n :=
    ((tendsto_pow_atTop_atTop_of_one_lt
      (show (1 : ℝ) < 3 by norm_num)).eventually_gt_atTop (2 * R)).exists
  obtain ⟨ell, hell, hpowUpper⟩ :
      ∃ ell : ℕ, 2 * R < (3 : ℝ) ^ ell ∧ (3 : ℝ) ^ ell ≤ 6 * R := by
    have hfind : 2 * R < (3 : ℝ) ^ Nat.find hex := Nat.find_spec hex
    have hpos : 0 < Nat.find hex := by
      rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | h0
      · rw [h0, pow_zero] at hfind
        linarith only [hfind, hR]
      · exact h0
    obtain ⟨q, hq⟩ : ∃ q : ℕ, Nat.find hex = q + 1 :=
      ⟨Nat.find hex - 1, by omega⟩
    have hprev : (3 : ℝ) ^ q ≤ 2 * R :=
      not_lt.1 (Nat.find_min hex (by omega))
    refine ⟨Nat.find hex, hfind, ?_⟩
    rw [hq, pow_succ]
    linarith only [hprev]
  have hmem : ∀ {z : Vec d}, Real.sqrt (vecNormSq z) ≤ R →
      z ∈ openCubeSet (originCube d (ell : ℤ)) := by
    intro z hz
    rw [mem_openCubeSet_originCube_iff]
    intro i
    have hzpow : (3 : ℝ) ^ ((ell : ℕ) : ℤ) = (3 : ℝ) ^ ell := by simp
    have hcoord : |z i| ≤ ‖z‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm z i
    have hzi : |z i| ≤ R :=
      hcoord.trans ((norm_le_sqrt_vecNormSq_holder z).trans hz)
    have hhalf : R < (1 / 2 : ℝ) * (3 : ℝ) ^ ell := by
      linarith only [hell]
    rw [hzpow]
    constructor
    · linarith only [hzi, hhalf, neg_abs_le (z i)]
    · linarith only [hzi, hhalf, le_abs_self (z i)]
  have hellPow : (ell : ℝ) ≤ (3 : ℝ) ^ ell := by
    have h := Nat.cast_le_pow_div_sub (α := ℝ) (show (1 : ℝ) < 3 by norm_num) ell
    norm_num at h
    exact h.trans (by
      have hp : (0 : ℝ) ≤ (3 : ℝ) ^ ell := pow_nonneg (by norm_num) _
      linarith only [hp])
  exact ⟨ell, hmem hx, hmem hy, hellPow.trans hpowUpper⟩

private theorem exists_crossover {h : ℝ} (hh : 0 < h) :
    ∃ m : ℤ, Real.rpow 3 (m : ℝ) ≤ h ∧
      h < Real.rpow 3 ((m : ℝ) + 1) := by
  let m : ℤ := ⌊Real.logb 3 h⌋
  refine ⟨m, ?_, ?_⟩
  · have hm : (m : ℝ) ≤ Real.logb 3 h := Int.floor_le _
    have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hm
    rw [Real.rpow_logb (by norm_num : (0 : ℝ) < 3) (by norm_num) hh] at hp
    exact hp
  · have hm : Real.logb 3 h < (m : ℝ) + 1 := Int.lt_floor_add_one _
    have hp := (Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 3)).2 hm
    rw [Real.rpow_logb (by norm_num : (0 : ℝ) < 3) (by norm_num) hh] at hp
    exact hp

private theorem crossover_nonpos {h : ℝ} (hh1 : h < 1)
    {m : ℤ} (hm : Real.rpow 3 (m : ℝ) ≤ h) : m ≤ 0 := by
  have hpow : Real.rpow 3 (m : ℝ) < Real.rpow 3 (0 : ℝ) := by
    calc
      Real.rpow 3 (m : ℝ) < 1 := hm.trans_lt hh1
      _ = Real.rpow 3 (0 : ℝ) := (Real.rpow_zero 3).symm
  have hmR : (m : ℝ) < 0 :=
    (Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 3)).1 hpow
  exact_mod_cast hmR.le

private theorem crossover_scales_le (M : ABKModel d) {h : ℝ} (hh : 0 < h)
    {m : ℤ} (hmLow : Real.rpow 3 (m : ℝ) ≤ h)
    (hmHigh : h < Real.rpow 3 ((m : ℝ) + 1)) :
    Real.rpow 3 (M.gamma * (m : ℝ)) ≤ Real.rpow h M.gamma ∧
      h * Real.rpow 3 ((M.gamma - 1) * ((m : ℝ) + 1)) ≤
        Real.rpow h M.gamma := by
  have hgamma0 : 0 ≤ M.gamma := M.shellPrefix.gamma_pos.le
  have hgm1 : M.gamma - 1 ≤ 0 := by
    linarith only [M.shellPrefix.gamma_le_quarter]
  constructor
  · calc
      Real.rpow 3 (M.gamma * (m : ℝ)) =
          Real.rpow (Real.rpow 3 (m : ℝ)) M.gamma := by
        rw [mul_comm]
        exact Real.rpow_mul (x := 3) (by norm_num) (m : ℝ) M.gamma
      _ ≤ Real.rpow h M.gamma :=
        Real.rpow_le_rpow (Real.rpow_pos_of_pos (by norm_num) _).le hmLow hgamma0
  · have hpow := Real.rpow_le_rpow_of_nonpos hh hmHigh.le hgm1
    have hscale : Real.rpow 3 ((M.gamma - 1) * ((m : ℝ) + 1)) =
        Real.rpow (Real.rpow 3 ((m : ℝ) + 1)) (M.gamma - 1) := by
      rw [show (M.gamma - 1) * ((m : ℝ) + 1) =
          ((m : ℝ) + 1) * (M.gamma - 1) by ring]
      exact Real.rpow_mul (x := 3) (by norm_num) ((m : ℝ) + 1) (M.gamma - 1)
    calc
      h * Real.rpow 3 ((M.gamma - 1) * ((m : ℝ) + 1)) ≤
          h * Real.rpow h (M.gamma - 1) :=
        mul_le_mul_of_nonneg_left (hscale ▸ hpow) hh.le
      _ = Real.rpow h M.gamma := by
        calc
          h * Real.rpow h (M.gamma - 1) =
              Real.rpow h 1 * Real.rpow h (M.gamma - 1) := by
            exact congrArg (fun z : ℝ => z * Real.rpow h (M.gamma - 1))
              (Real.rpow_one h).symm
          _ = Real.rpow h (1 + (M.gamma - 1)) :=
            (Real.rpow_add hh 1 (M.gamma - 1)).symm
          _ = Real.rpow h M.gamma := by congr 1; ring

private theorem crossover_weight_absorption (M : ABKModel d) {R h : ℝ}
    (hR : 1 ≤ R) (hh : 0 < h) (hh1 : h < 1) {m : ℤ}
    (hmLow : Real.rpow 3 (m : ℝ) ≤ h)
    (hmHigh : h < Real.rpow 3 ((m : ℝ) + 1)) {ell : ℕ}
    (hell : (ell : ℝ) ≤ 6 * R) :
    sharpTailWeight m (ell : ℤ) * Real.rpow h M.gamma ≤
      Real.rpow 3 (streamHolderExponent M) * (7 + holderGapSum M) *
        (1 + R) * Real.rpow h (streamHolderExponent M) := by
  have hm0 := crossover_nonpos hh1 hmLow
  have hmcast : (m : ℝ) = -(m.natAbs : ℝ) := by
    have hmInt := Int.ofNat_natAbs_of_nonpos hm0
    have hmInt' : m = -(m.natAbs : ℤ) := by omega
    exact_mod_cast hmInt'
  have hbeta := streamHolderExponent_pos M
  have hbetaLe : Real.rpow h (streamHolderExponent M) ≤
      Real.rpow 3 (streamHolderExponent M) * holderGapRatio M ^ m.natAbs := by
    calc
      Real.rpow h (streamHolderExponent M) ≤
          Real.rpow (Real.rpow 3 ((m : ℝ) + 1)) (streamHolderExponent M) :=
        Real.rpow_le_rpow hh.le hmHigh.le hbeta.le
      _ = Real.rpow 3 (((m : ℝ) + 1) * streamHolderExponent M) := by
        exact (Real.rpow_mul (x := 3) (by norm_num)
          ((m : ℝ) + 1) (streamHolderExponent M)).symm
      _ = Real.rpow 3 (streamHolderExponent M +
          (-streamHolderExponent M) * (m.natAbs : ℝ)) := by
        congr 1
        rw [hmcast]
        ring
      _ = Real.rpow 3 (streamHolderExponent M) *
          Real.rpow 3 ((-streamHolderExponent M) * (m.natAbs : ℝ)) :=
        Section4.Provider.BoundsEaL.rpow3_add _ _
      _ = Real.rpow 3 (streamHolderExponent M) *
          holderGapRatio M ^ m.natAbs := by
        congr 1
        exact Section4.Provider.BoundsEaL.rpow3_mul_natCast
          (-streamHolderExponent M) m.natAbs
  have hq0 : 0 ≤ holderGapRatio M := (holderGapRatio_pos M).le
  have hq1 : holderGapRatio M ≤ 1 := (holderGapRatio_lt_one M).le
  have hgapTerm : ((m.natAbs : ℝ) + 1) * holderGapRatio M ^ m.natAbs ≤
      holderGapSum M := by
    simpa only [Finset.sum_singleton, holderGapSum] using
      (summable_holderGap M).sum_le_tsum {m.natAbs}
        (fun _ _ => mul_nonneg (by positivity) (pow_nonneg hq0 _))
  have hweightQ : sharpTailWeight m (ell : ℤ) *
      holderGapRatio M ^ m.natAbs ≤ (ell : ℝ) + 1 + holderGapSum M := by
    have hqpow : holderGapRatio M ^ m.natAbs ≤ 1 :=
      pow_le_one₀ hq0 hq1
    unfold sharpTailWeight
    simp only [Int.natAbs_natCast]
    push_cast
    calc
      (2 + (m.natAbs : ℝ) + (ell : ℝ)) * holderGapRatio M ^ m.natAbs =
          ((ell : ℝ) + 1) * holderGapRatio M ^ m.natAbs +
            ((m.natAbs : ℝ) + 1) * holderGapRatio M ^ m.natAbs := by ring
      _ ≤ ((ell : ℝ) + 1) * 1 + holderGapSum M :=
        add_le_add (mul_le_mul_of_nonneg_left hqpow (by positivity)) hgapTerm
      _ = (ell : ℝ) + 1 + holderGapSum M := by ring
  have hweightBeta : sharpTailWeight m (ell : ℤ) *
      Real.rpow h (streamHolderExponent M) ≤
      Real.rpow 3 (streamHolderExponent M) *
        ((ell : ℝ) + 1 + holderGapSum M) := by
    calc
      sharpTailWeight m (ell : ℤ) * Real.rpow h (streamHolderExponent M) ≤
          sharpTailWeight m (ell : ℤ) *
            (Real.rpow 3 (streamHolderExponent M) *
              holderGapRatio M ^ m.natAbs) :=
        mul_le_mul_of_nonneg_left hbetaLe (sharpTailWeight_pos _ _).le
      _ = Real.rpow 3 (streamHolderExponent M) *
          (sharpTailWeight m (ell : ℤ) * holderGapRatio M ^ m.natAbs) := by ring
      _ ≤ Real.rpow 3 (streamHolderExponent M) *
          ((ell : ℝ) + 1 + holderGapSum M) :=
        mul_le_mul_of_nonneg_left hweightQ
          (Real.rpow_pos_of_pos (by norm_num) _).le
  have hradial : (ell : ℝ) + 1 + holderGapSum M ≤
      (7 + holderGapSum M) * (1 + R) := by
    have hgap0 := holderGapSum_nonneg M
    have hfirst : (ell : ℝ) + 1 + holderGapSum M ≤
        6 * R + 1 + holderGapSum M :=
      by linarith only [hell]
    have hsecond : 6 * R + 1 + holderGapSum M ≤
        (7 + holderGapSum M) * R := by
      have hmul := mul_le_mul_of_nonneg_left hR hgap0
      calc
        6 * R + 1 + holderGapSum M = 6 * R + 1 + holderGapSum M * 1 := by ring
        _ ≤ 6 * R + R + holderGapSum M * R :=
          add_le_add (by
            have hadd := add_le_add_right hR (6 * R)
            linarith only [hadd]) hmul
        _ = (7 + holderGapSum M) * R := by ring
    have hthird : (7 + holderGapSum M) * R ≤
        (7 + holderGapSum M) * (1 + R) := by
      apply mul_le_mul_of_nonneg_left
      · linarith only
      · linarith only [hgap0]
    exact hfirst.trans (hsecond.trans hthird)
  change sharpTailWeight m (ell : ℤ) * h ^ M.gamma ≤ _
  rw [show M.gamma = streamHolderExponent M + streamHolderExponent M by
      unfold streamHolderExponent; ring,
    Real.rpow_add hh]
  calc
    sharpTailWeight m (ell : ℤ) *
        (Real.rpow h (streamHolderExponent M) *
          Real.rpow h (streamHolderExponent M)) =
      (sharpTailWeight m (ell : ℤ) * Real.rpow h (streamHolderExponent M)) *
        Real.rpow h (streamHolderExponent M) := by ring
    _ ≤ (Real.rpow 3 (streamHolderExponent M) *
        ((ell : ℝ) + 1 + holderGapSum M)) *
          Real.rpow h (streamHolderExponent M) :=
      mul_le_mul_of_nonneg_right hweightBeta
        (Real.rpow_pos_of_pos hh _).le
    _ ≤ (Real.rpow 3 (streamHolderExponent M) *
        ((7 + holderGapSum M) * (1 + R))) *
          Real.rpow h (streamHolderExponent M) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hradial
          (Real.rpow_pos_of_pos (by norm_num) _).le)
        (Real.rpow_pos_of_pos hh _).le
    _ = Real.rpow 3 (streamHolderExponent M) * (7 + holderGapSum M) *
        (1 + R) * Real.rpow h (streamHolderExponent M) := by ring

/-- An explicit radius-independent coefficient in the Hölder modulus. -/
def streamFieldHolderConst (M : ABKModel d) (omega : FullSample d M.gamma) : ℝ :=
  2 * (d : ℝ) ^ 2 * streamFieldGrowthConst M omega +
    (d : ℝ) ^ 2 * (streamSharpConst M omega : ℝ) *
      (6 * holderLowerSum M + 3 * (d : ℝ) * holderUpperSum M) *
        Real.rpow 3 (streamHolderExponent M) * (7 + holderGapSum M)

/-- The radius-dependent modulus; its growth exponent is explicitly one. -/
def streamFieldHolderModulus (M : ABKModel d) (omega : FullSample d M.gamma)
    (R : ℝ) : ℝ := streamFieldHolderConst M omega * (1 + R)

theorem streamFieldHolderConst_nonneg (M : ABKModel d)
    (omega : FullSample d M.gamma) : 0 ≤ streamFieldHolderConst M omega := by
  have hL := holderLowerSum_nonneg M
  have hU := holderUpperSum_nonneg M
  have hG := holderGapSum_nonneg M
  have hgrowth := streamFieldGrowthConst_nonneg M omega
  unfold streamFieldHolderConst
  have hfirst : 0 ≤ 2 * (d : ℝ) ^ 2 * streamFieldGrowthConst M omega :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg (d : ℝ))) hgrowth
  have hsum : 0 ≤ 6 * holderLowerSum M + 3 * (d : ℝ) * holderUpperSum M :=
    add_nonneg (mul_nonneg (by norm_num) hL)
      (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d)) hU)
  have hsecond : 0 ≤ (d : ℝ) ^ 2 * (streamSharpConst M omega : ℝ) *
      (6 * holderLowerSum M + 3 * (d : ℝ) * holderUpperSum M) *
        Real.rpow 3 (streamHolderExponent M) * (7 + holderGapSum M) :=
    mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (sq_nonneg (d : ℝ)) (Nat.cast_nonneg _)) hsum)
        (Real.rpow_pos_of_pos (by norm_num) _).le)
      (by linarith only [hG])
  exact add_nonneg hfirst hsecond

theorem two_mul_dim_sq_mul_growthConst_le_holderConst (M : ABKModel d)
    (omega : FullSample d M.gamma) :
    2 * (d : ℝ) ^ 2 * streamFieldGrowthConst M omega ≤
      streamFieldHolderConst M omega := by
  have hL := holderLowerSum_nonneg M
  have hU := holderUpperSum_nonneg M
  have hG := holderGapSum_nonneg M
  unfold streamFieldHolderConst
  apply le_add_of_nonneg_right
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg (sq_nonneg (d : ℝ)) (Nat.cast_nonneg _))
        (add_nonneg (mul_nonneg (by norm_num) hL)
          (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d)) hU)))
      (Real.rpow_pos_of_pos (by norm_num) _).le)
    (by linarith only [hG])

/-- The crossover estimate in the small-distance regime. -/
theorem matrixOperatorNorm_streamField_sub_le_small (M : ABKModel d)
    (omega : FullSample d M.gamma) {R : ℝ} (hR : 1 ≤ R)
    {x y : Vec d} (hx : Real.sqrt (vecNormSq x) ≤ R)
    (hy : Real.sqrt (vecNormSq y) ≤ R) (hxy : x ≠ y)
    (hsmall : ‖x - y‖ < 1) :
    matrixOperatorNorm (streamField omega x - streamField omega y) ≤
      streamFieldHolderModulus M omega R *
        Real.rpow ‖x - y‖ (streamHolderExponent M) := by
  have hh : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  obtain ⟨ell, hxCube, hyCube, hell⟩ := exists_holder_originCube hR hx hy
  obtain ⟨m, hmLow, hmHigh⟩ := exists_crossover hh
  have hscales := crossover_scales_le M hh hmLow hmHigh
  have habsorb := crossover_weight_absorption M hR hh hsmall hmLow hmHigh hell
  have hC := streamSharpConst_spec M omega
  have hentry : ∀ i k : Fin d,
      |(streamField omega x - streamField omega y) i k| ≤
        (streamSharpConst M omega : ℝ) *
          (6 * holderLowerSum M + 3 * (d : ℝ) * holderUpperSum M) *
            (Real.rpow 3 (streamHolderExponent M) * (7 + holderGapSum M) *
              (1 + R) * Real.rpow ‖x - y‖ (streamHolderExponent M)) := by
    intro i k
    have hraw := abs_streamField_entry_sub_le_crossover M omega hC
      (ell : ℤ) m hxCube hyCube i k
    have hlow0 : 0 ≤ 6 * holderLowerSum M :=
      mul_nonneg (by norm_num) (holderLowerSum_nonneg M)
    have hupp0 : 0 ≤ 3 * (d : ℝ) * holderUpperSum M :=
      mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d))
        (holderUpperSum_nonneg M)
    have hsum : 6 * holderLowerSum M * Real.rpow 3 (M.gamma * (m : ℝ)) +
        3 * (d : ℝ) * holderUpperSum M * ‖x - y‖ *
          Real.rpow 3 ((M.gamma - 1) * ((m : ℝ) + 1)) ≤
        (6 * holderLowerSum M + 3 * (d : ℝ) * holderUpperSum M) *
          Real.rpow ‖x - y‖ M.gamma := by
      convert add_le_add
        (mul_le_mul_of_nonneg_left hscales.1 hlow0)
        (mul_le_mul_of_nonneg_left hscales.2 hupp0) using 1
      all_goals first | rfl | ring
    simp only [Matrix.sub_apply]
    calc
      |streamField omega x i k - streamField omega y i k| ≤
          (streamSharpConst M omega : ℝ) * sharpTailWeight m (ell : ℤ) *
            (6 * holderLowerSum M * Real.rpow 3 (M.gamma * (m : ℝ)) +
              3 * (d : ℝ) * holderUpperSum M * ‖x - y‖ *
                Real.rpow 3 ((M.gamma - 1) * ((m : ℝ) + 1))) := hraw
      _ ≤ (streamSharpConst M omega : ℝ) * sharpTailWeight m (ell : ℤ) *
            ((6 * holderLowerSum M + 3 * (d : ℝ) * holderUpperSum M) *
              Real.rpow ‖x - y‖ M.gamma) :=
        mul_le_mul_of_nonneg_left hsum
          (mul_nonneg (Nat.cast_nonneg _) (sharpTailWeight_pos _ _).le)
      _ ≤ (streamSharpConst M omega : ℝ) *
          (6 * holderLowerSum M + 3 * (d : ℝ) * holderUpperSum M) *
            (Real.rpow 3 (streamHolderExponent M) * (7 + holderGapSum M) *
              (1 + R) * Real.rpow ‖x - y‖ (streamHolderExponent M)) := by
        have hcoef : 0 ≤ (streamSharpConst M omega : ℝ) *
            (6 * holderLowerSum M + 3 * (d : ℝ) * holderUpperSum M) :=
          mul_nonneg (Nat.cast_nonneg _)
            (add_nonneg (mul_nonneg (by norm_num) (holderLowerSum_nonneg M))
              (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d))
                (holderUpperSum_nonneg M)))
        have hstep := mul_le_mul_of_nonneg_left habsorb hcoef
        convert hstep using 1
        all_goals first | rfl | ring
  have hmatrix := (matrixOperatorNorm_le_sum_abs_entries_holder
    (streamField omega x - streamField omega y)).trans
      (sum_abs_entries_le_of_forall_holder _ hentry)
  have hR0 : 0 ≤ 1 + R := by linarith only [hR]
  have hp0 := (Real.rpow_pos_of_pos hh (streamHolderExponent M)).le
  have hfactor0 : 0 ≤ (1 + R) * Real.rpow ‖x - y‖ (streamHolderExponent M) :=
    mul_nonneg hR0 hp0
  unfold streamFieldHolderModulus streamFieldHolderConst
  have hgrowth0 : 0 ≤ 2 * (d : ℝ) ^ 2 * streamFieldGrowthConst M omega := by
    exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg (d : ℝ)))
      (streamFieldGrowthConst_nonneg M omega)
  let S : ℝ := (d : ℝ) ^ 2 * (streamSharpConst M omega : ℝ) *
    (6 * holderLowerSum M + 3 * (d : ℝ) * holderUpperSum M) *
      Real.rpow 3 (streamHolderExponent M) * (7 + holderGapSum M)
  have hmatrix' : matrixOperatorNorm (streamField omega x - streamField omega y) ≤
      S * ((1 + R) * Real.rpow ‖x - y‖ (streamHolderExponent M)) := by
    exact hmatrix.trans_eq (by unfold S; ring)
  have hmono := mul_le_mul_of_nonneg_right
    (le_add_of_nonneg_left hgrowth0 : S ≤ 2 * (d : ℝ) ^ 2 *
      streamFieldGrowthConst M omega + S) hfactor0
  exact hmatrix'.trans (by
    unfold S at hmono
    convert hmono using 1
    all_goals ring)


end

end Algsuperdiff.Section5.Field
