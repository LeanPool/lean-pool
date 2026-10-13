/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Field.SharpTailProbability
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.Step3Arith
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.BoundsEaL.TailSummability

/-!
# SharpTailGrowth

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# From sharp shell rates to the quantitative growth budget

For an admissible ABK exponent, the all-crossover sharp bounds imply the
two-leg partial-sum estimate used by the original field construction.  The
polynomial crossover weight is absorbed twice: geometrically in the shell gap
and geometrically in the observation scale.
-/

namespace Algsuperdiff.Section5.Field

open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Stream
open HCPolySupport

noncomputable section

variable {d : ℕ}

def sharpSpatialRatio : ℝ := Real.rpow 3 (-(3 / 4 : ℝ))

def sharpLowerRatio (M : ABKModel d) : ℝ := Real.rpow 3 (-M.gamma)

def sharpUpperRatio (M : ABKModel d) : ℝ := Real.rpow 3 (M.gamma - 1)

private theorem sharpSpatialRatio_pos : 0 < sharpSpatialRatio :=
  Real.rpow_pos_of_pos (by norm_num) _

private theorem sharpSpatialRatio_lt_one : sharpSpatialRatio < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

private theorem sharpLowerRatio_pos (M : ABKModel d) : 0 < sharpLowerRatio M :=
  Real.rpow_pos_of_pos (by norm_num) _

private theorem sharpLowerRatio_lt_one (M : ABKModel d) : sharpLowerRatio M < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    (neg_neg_of_pos M.shellPrefix.gamma_pos)

private theorem sharpUpperRatio_pos (M : ABKModel d) : 0 < sharpUpperRatio M :=
  Real.rpow_pos_of_pos (by norm_num) _

private theorem sharpUpperRatio_lt_one (M : ABKModel d) : sharpUpperRatio M < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    (by linarith only [M.shellPrefix.gamma_le_quarter])

private theorem summable_sharpSpatialProfile :
    Summable fun ell : ℕ => ((ell : ℝ) + 1) * sharpSpatialRatio ^ ell :=
  Section4.Provider.Annular.summable_poly1_geom sharpSpatialRatio_pos.le
    sharpSpatialRatio_lt_one

private theorem summable_sharpRadialProfile (M : ABKModel d) :
    Summable fun r : ℕ => ((r : ℝ) + 1) *
      (sharpLowerRatio M ^ r + sharpUpperRatio M ^ r) := by
  have hl := Section4.Provider.Annular.summable_poly1_geom
    (sharpLowerRatio_pos M).le (sharpLowerRatio_lt_one M)
  have hu := Section4.Provider.Annular.summable_poly1_geom
    (sharpUpperRatio_pos M).le (sharpUpperRatio_lt_one M)
  refine (hl.add hu).congr fun r => ?_
  ring

private theorem sharpSpatialProfile_nonneg (ell : ℕ) :
    0 ≤ ((ell : ℝ) + 1) * sharpSpatialRatio ^ ell :=
  mul_nonneg (by positivity) (pow_nonneg sharpSpatialRatio_pos.le _)

private theorem sharpRadialProfile_nonneg (M : ABKModel d) (r : ℕ) :
    0 ≤ ((r : ℝ) + 1) * (sharpLowerRatio M ^ r + sharpUpperRatio M ^ r) :=
  mul_nonneg (by positivity)
    (add_nonneg (pow_nonneg (sharpLowerRatio_pos M).le _)
      (pow_nonneg (sharpUpperRatio_pos M).le _))

private theorem sharpTailWeight_sub_le (ell r : ℕ) :
    sharpTailWeight ((ell : ℤ) - (r : ℤ)) (ell : ℤ) ≤
      2 * ((ell : ℝ) + 1) * ((r : ℝ) + 1) := by
  have habs : ((ell : ℤ) - (r : ℤ)).natAbs ≤ ell + r := by
    exact (Int.natAbs_sub_le (ell : ℤ) (r : ℤ)).trans_eq (by simp)
  have hnat : 2 + ((ell : ℤ) - (r : ℤ)).natAbs + ell ≤
      2 * (ell + 1) * (r + 1) := by
    nlinarith only [habs, Nat.zero_le ell, Nat.zero_le r]
  unfold sharpTailWeight
  exact_mod_cast hnat

private theorem sharpTailWeight_add_le (ell r : ℕ) :
    sharpTailWeight ((ell : ℤ) + (r : ℤ)) (ell : ℤ) ≤
      2 * ((ell : ℝ) + 1) * ((r : ℝ) + 1) := by
  unfold sharpTailWeight
  simp only [Int.natAbs_add_of_nonneg (Int.natCast_nonneg _)
    (Int.natCast_nonneg _), Int.natAbs_natCast]
  have hnat : 2 + (ell + r) + ell ≤ 2 * (ell + 1) * (r + 1) := by
    nlinarith only [Nat.zero_le ell, Nat.zero_le r]
  exact_mod_cast hnat

private theorem sharpValueScale_le (M : ABKModel d) (ell r : ℕ) :
    Real.rpow 3 (M.gamma * (((ell : ℤ) - (r : ℤ) : ℤ) : ℝ)) ≤
      (3 : ℝ) ^ ell * sharpSpatialRatio ^ ell * sharpLowerRatio M ^ r := by
  have hexp : M.gamma * ((ell : ℝ) - (r : ℝ)) ≤
      (ell : ℝ) + (-(3 / 4 : ℝ)) * (ell : ℝ) + (-M.gamma) * (r : ℝ) := by
    have hg := M.shellPrefix.gamma_le_quarter
    have hell : (0 : ℝ) ≤ (ell : ℝ) := Nat.cast_nonneg ell
    nlinarith only [hg, hell]
  have hmono := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hexp
  have hspatial : Real.rpow 3 (-(3 / 4 : ℝ) * (ell : ℝ)) =
      sharpSpatialRatio ^ ell := by
    exact Section4.Provider.BoundsEaL.rpow3_mul_natCast (-(3 / 4 : ℝ)) ell
  have hlower : Real.rpow 3 (-M.gamma * (r : ℝ)) = sharpLowerRatio M ^ r := by
    exact Section4.Provider.BoundsEaL.rpow3_mul_natCast (-M.gamma) r
  have hellPow : Real.rpow 3 (ell : ℝ) = (3 : ℝ) ^ ell :=
    Real.rpow_natCast 3 ell
  calc
    Real.rpow 3 (M.gamma * (((ell : ℤ) - (r : ℤ) : ℤ) : ℝ)) =
        Real.rpow 3 (M.gamma * ((ell : ℝ) - (r : ℝ))) := by push_cast; ring
    _ ≤ Real.rpow 3 ((ell : ℝ) + (-(3 / 4 : ℝ)) * (ell : ℝ) +
        (-M.gamma) * (r : ℝ)) := hmono
    _ = (3 : ℝ) ^ ell * sharpSpatialRatio ^ ell * sharpLowerRatio M ^ r := by
      rw [show (ell : ℝ) + -(3 / 4 : ℝ) * (ell : ℝ) + (-M.gamma) * (r : ℝ) =
          (ell : ℝ) + (-(3 / 4 : ℝ) * (ell : ℝ) + (-M.gamma) * (r : ℝ)) by ring,
        Section4.Provider.BoundsEaL.rpow3_add,
        Section4.Provider.BoundsEaL.rpow3_add, hellPow, hspatial, hlower]
      ring

private theorem sharpGradientScale_le (M : ABKModel d) (ell r : ℕ) :
    (3 : ℝ) ^ ell *
        Real.rpow 3 ((M.gamma - 1) * (((ell : ℤ) + (r : ℤ) : ℤ) : ℝ)) ≤
      (3 : ℝ) ^ ell * sharpSpatialRatio ^ ell * sharpUpperRatio M ^ r := by
  have hexp : (ell : ℝ) + (M.gamma - 1) * ((ell : ℝ) + (r : ℝ)) ≤
      (ell : ℝ) + (-(3 / 4 : ℝ)) * (ell : ℝ) +
        (M.gamma - 1) * (r : ℝ) := by
    have hg := M.shellPrefix.gamma_le_quarter
    have hell : (0 : ℝ) ≤ (ell : ℝ) := Nat.cast_nonneg ell
    nlinarith only [hg, hell]
  have hmono := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hexp
  have hspatial : Real.rpow 3 (-(3 / 4 : ℝ) * (ell : ℝ)) =
      sharpSpatialRatio ^ ell := by
    exact Section4.Provider.BoundsEaL.rpow3_mul_natCast (-(3 / 4 : ℝ)) ell
  have hupper : Real.rpow 3 ((M.gamma - 1) * (r : ℝ)) = sharpUpperRatio M ^ r := by
    exact Section4.Provider.BoundsEaL.rpow3_mul_natCast (M.gamma - 1) r
  have hellPow : Real.rpow 3 (ell : ℝ) = (3 : ℝ) ^ ell :=
    Real.rpow_natCast 3 ell
  calc
    (3 : ℝ) ^ ell *
        Real.rpow 3 ((M.gamma - 1) * (((ell : ℤ) + (r : ℤ) : ℤ) : ℝ)) =
      Real.rpow 3 ((ell : ℝ) + (M.gamma - 1) * ((ell : ℝ) + (r : ℝ))) := by
        calc
          (3 : ℝ) ^ ell * Real.rpow 3
              ((M.gamma - 1) * (((ell : ℤ) + (r : ℤ) : ℤ) : ℝ)) =
            Real.rpow 3 (ell : ℝ) * Real.rpow 3
              ((M.gamma - 1) * (((ell : ℤ) + (r : ℤ) : ℤ) : ℝ)) := by rw [hellPow]
          _ = Real.rpow 3 ((ell : ℝ) +
              (M.gamma - 1) * (((ell : ℤ) + (r : ℤ) : ℤ) : ℝ)) :=
            (Section4.Provider.BoundsEaL.rpow3_add _ _).symm
          _ = _ := by
            congr 1
            push_cast
            ring
    _ ≤ Real.rpow 3 ((ell : ℝ) + (-(3 / 4 : ℝ)) * (ell : ℝ) +
        (M.gamma - 1) * (r : ℝ)) := hmono
    _ = (3 : ℝ) ^ ell * sharpSpatialRatio ^ ell * sharpUpperRatio M ^ r := by
      rw [show (ell : ℝ) + -(3 / 4 : ℝ) * (ell : ℝ) + (M.gamma - 1) * (r : ℝ) =
          (ell : ℝ) + (-(3 / 4 : ℝ) * (ell : ℝ) +
            (M.gamma - 1) * (r : ℝ)) by ring,
        Section4.Provider.BoundsEaL.rpow3_add,
        Section4.Provider.BoundsEaL.rpow3_add, hellPow, hspatial, hupper]
      ring

private theorem scale_mul_shellW1InfGradNorm_le_sharpGradientGauge
    (ell r : ℕ) (omega : CutoffSample d) :
    (3 : ℝ) ^ ell * Section4.Support.shellW1InfGradNorm (ell : ℤ)
        (omega.1 ((ell : ℤ) + (r : ℤ))) ≤
      sharpGradientGauge (ell : ℤ) ((ell : ℤ) + (r : ℤ)) omega := by
  let j := omega.1 ((ell : ℤ) + (r : ℤ))
  have hp : (0 : ℝ) < (3 : ℝ) ^ ell := by positivity
  have hpow : (3 : ℝ) ^ ell ≤ (3 : ℝ) ^ ((ell : ℤ) + (r : ℤ)) := by
    rw [← zpow_natCast]
    exact zpow_le_zpow_right₀ (by norm_num) (by omega)
  rw [sharpGradientGauge_eq, Section4.Support.shellW1InfGradNorm_def,
    mul_max_of_nonneg _ _ hp.le]
  apply max_le
  · exact (mul_le_mul_of_nonneg_right hpow (localCubeSecondDerivNorm_nonneg _ _)).trans
      (le_add_of_nonneg_left (localCubeDerivNorm_nonneg _ _))
  · have hcancel : (3 : ℝ) ^ ell *
        ((3 : ℝ) ^ (-(ell : ℤ)) * localCubeDerivNorm (ell : ℤ) j) =
        localCubeDerivNorm (ell : ℤ) j := by
      rw [← zpow_natCast, ← mul_assoc, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      simp
    rw [hcancel]
    exact le_add_of_nonneg_right
      (mul_nonneg (zpow_pos (by norm_num) _).le (localCubeSecondDerivNorm_nonneg _ _))

private theorem sharpGrowthTerm_le (M : ABKModel d) {C : ℕ}
    {omega : CutoffSample d} (hC : SharpTailBounded M.gamma C omega)
    (ell r : ℕ) :
    localCubeControl (ell : ℤ) (omega.1 ((ell : ℤ) - (r : ℤ))) +
        (3 : ℝ) ^ (2 * ell) * Section4.Support.shellW1InfGradNorm (ell : ℤ)
          (omega.1 ((ell : ℤ) + (r : ℤ))) ≤
      (C : ℝ) * (3 : ℝ) ^ ell *
        (2 * (((ell : ℝ) + 1) * sharpSpatialRatio ^ ell) *
          (((r : ℝ) + 1) *
            (sharpLowerRatio M ^ r + sharpUpperRatio M ^ r))) := by
  have hvalue := (hC ((ell : ℤ) - (r : ℤ)) (ell : ℤ)).1
  have hgrad := (hC ((ell : ℤ) + (r : ℤ)) (ell : ℤ)).2
  have hweightSub := sharpTailWeight_sub_le ell r
  have hweightAdd := sharpTailWeight_add_le ell r
  have hvalueScale := sharpValueScale_le M ell r
  have hgradScale := sharpGradientScale_le M ell r
  have hC0 : (0 : ℝ) ≤ (C : ℝ) := Nat.cast_nonneg C
  have hvalue' : localCubeControl (ell : ℤ) (omega.1 ((ell : ℤ) - (r : ℤ))) ≤
      (C : ℝ) * ((3 : ℝ) ^ ell * sharpSpatialRatio ^ ell) *
        (2 * ((ell : ℝ) + 1) * ((r : ℝ) + 1) * sharpLowerRatio M ^ r) := by
    calc
      localCubeControl (ell : ℤ) (omega.1 ((ell : ℤ) - (r : ℤ))) ≤
          (C : ℝ) * Real.rpow 3
            (M.gamma * (((ell : ℤ) - (r : ℤ) : ℤ) : ℝ)) *
              sharpTailWeight ((ell : ℤ) - (r : ℤ)) (ell : ℤ) := hvalue
      _ ≤ (C : ℝ) * ((3 : ℝ) ^ ell * sharpSpatialRatio ^ ell *
            sharpLowerRatio M ^ r *
            (2 * ((ell : ℝ) + 1) * ((r : ℝ) + 1))) := by
        have hs : Real.rpow 3
                (M.gamma * (((ell : ℤ) - (r : ℤ) : ℤ) : ℝ)) *
              sharpTailWeight ((ell : ℤ) - (r : ℤ)) (ell : ℤ) ≤
            ((3 : ℝ) ^ ell * sharpSpatialRatio ^ ell * sharpLowerRatio M ^ r) *
              (2 * ((ell : ℝ) + 1) * ((r : ℝ) + 1)) := by
          calc
          Real.rpow 3 (M.gamma * (((ell : ℤ) - (r : ℤ) : ℤ) : ℝ)) *
              sharpTailWeight ((ell : ℤ) - (r : ℤ)) (ell : ℤ) ≤
            ((3 : ℝ) ^ ell * sharpSpatialRatio ^ ell * sharpLowerRatio M ^ r) *
              sharpTailWeight ((ell : ℤ) - (r : ℤ)) (ell : ℤ) :=
            mul_le_mul_of_nonneg_right hvalueScale (sharpTailWeight_pos _ _).le
          _ ≤ ((3 : ℝ) ^ ell * sharpSpatialRatio ^ ell * sharpLowerRatio M ^ r) *
              (2 * ((ell : ℝ) + 1) * ((r : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left hweightSub
              (mul_nonneg
                (mul_nonneg (pow_nonneg (by norm_num) _)
                  (pow_nonneg sharpSpatialRatio_pos.le _))
                (pow_nonneg (sharpLowerRatio_pos M).le _))
        have hsC := mul_le_mul_of_nonneg_left hs hC0
        convert hsC using 1
        all_goals first | rfl | ring
      _ = _ := by ring
  have hbridge := scale_mul_shellW1InfGradNorm_le_sharpGradientGauge ell r omega
  have hupperBridge : (3 : ℝ) ^ (2 * ell) *
      Section4.Support.shellW1InfGradNorm (ell : ℤ)
        (omega.1 ((ell : ℤ) + (r : ℤ))) ≤
      (3 : ℝ) ^ ell * sharpGradientGauge (ell : ℤ)
        ((ell : ℤ) + (r : ℤ)) omega := by
    rw [two_mul, pow_add, mul_assoc]
    exact mul_le_mul_of_nonneg_left hbridge (by positivity)
  have hgrad' : (3 : ℝ) ^ (2 * ell) *
      Section4.Support.shellW1InfGradNorm (ell : ℤ)
        (omega.1 ((ell : ℤ) + (r : ℤ))) ≤
      (C : ℝ) * ((3 : ℝ) ^ ell * sharpSpatialRatio ^ ell) *
        (2 * ((ell : ℝ) + 1) * ((r : ℝ) + 1) * sharpUpperRatio M ^ r) := by
    calc
      (3 : ℝ) ^ (2 * ell) * Section4.Support.shellW1InfGradNorm (ell : ℤ)
          (omega.1 ((ell : ℤ) + (r : ℤ))) ≤
        (3 : ℝ) ^ ell * sharpGradientGauge (ell : ℤ)
          ((ell : ℤ) + (r : ℤ)) omega := hupperBridge
      _ ≤ (3 : ℝ) ^ ell * ((C : ℝ) * Real.rpow 3
            ((M.gamma - 1) * (((ell : ℤ) + (r : ℤ) : ℤ) : ℝ)) *
              sharpTailWeight ((ell : ℤ) + (r : ℤ)) (ell : ℤ)) :=
        mul_le_mul_of_nonneg_left hgrad (pow_nonneg (by norm_num) _)
      _ ≤ (C : ℝ) * ((3 : ℝ) ^ ell * sharpSpatialRatio ^ ell *
            (2 * ((ell : ℝ) + 1) * ((r : ℝ) + 1))) * sharpUpperRatio M ^ r := by
        have hs : (3 : ℝ) ^ ell * Real.rpow 3
                ((M.gamma - 1) * (((ell : ℤ) + (r : ℤ) : ℤ) : ℝ)) *
              sharpTailWeight ((ell : ℤ) + (r : ℤ)) (ell : ℤ) ≤
            ((3 : ℝ) ^ ell * sharpSpatialRatio ^ ell * sharpUpperRatio M ^ r) *
              (2 * ((ell : ℝ) + 1) * ((r : ℝ) + 1)) := by
          calc
          (3 : ℝ) ^ ell * Real.rpow 3
                ((M.gamma - 1) * (((ell : ℤ) + (r : ℤ) : ℤ) : ℝ)) *
              sharpTailWeight ((ell : ℤ) + (r : ℤ)) (ell : ℤ) ≤
            ((3 : ℝ) ^ ell * sharpSpatialRatio ^ ell * sharpUpperRatio M ^ r) *
              sharpTailWeight ((ell : ℤ) + (r : ℤ)) (ell : ℤ) :=
            mul_le_mul_of_nonneg_right hgradScale (sharpTailWeight_pos _ _).le
          _ ≤ ((3 : ℝ) ^ ell * sharpSpatialRatio ^ ell * sharpUpperRatio M ^ r) *
              (2 * ((ell : ℝ) + 1) * ((r : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left hweightAdd
              (mul_nonneg
                (mul_nonneg (pow_nonneg (by norm_num) _)
                  (pow_nonneg sharpSpatialRatio_pos.le _))
                (pow_nonneg (sharpUpperRatio_pos M).le _))
        have hsC := mul_le_mul_of_nonneg_left hs hC0
        convert hsC using 1
        all_goals first | rfl | ring
      _ = _ := by ring
  linarith only [hvalue', hgrad']

/-- The sharp all-crossover bounds imply the original quantitative growth
condition at every exponent admitted by an `ABKModel`. -/
theorem exists_streamGrowthBounded_of_sharpTailGood (M : ABKModel d)
    {omega : CutoffSample d} (h : SharpTailGood M.gamma omega) :
    ∃ C : ℕ, StreamGrowthBounded C omega := by
  obtain ⟨C₀, hC₀⟩ := h
  let A : ℝ := ∑' ell : ℕ, ((ell : ℝ) + 1) * sharpSpatialRatio ^ ell
  let B : ℝ := ∑' r : ℕ, ((r : ℝ) + 1) *
    (sharpLowerRatio M ^ r + sharpUpperRatio M ^ r)
  obtain ⟨C, hC⟩ := exists_nat_ge (2 * (C₀ : ℝ) * A * B)
  refine ⟨C, fun ell q => ?_⟩
  have hA : ((ell : ℝ) + 1) * sharpSpatialRatio ^ ell ≤ A := by
    simpa only [Finset.sum_singleton] using
      (summable_sharpSpatialProfile.sum_le_tsum {ell}
        (fun _ _ => sharpSpatialProfile_nonneg _))
  have hB : (∑ r ∈ Finset.range q, ((r : ℝ) + 1) *
      (sharpLowerRatio M ^ r + sharpUpperRatio M ^ r)) ≤ B := by
    exact (summable_sharpRadialProfile M).sum_le_tsum _
      (fun _ _ => sharpRadialProfile_nonneg M _)
  have hA0 : 0 ≤ A := tsum_nonneg sharpSpatialProfile_nonneg
  have hsum : lowerValuePartialSum ell q omega +
      (3 : ℝ) ^ (2 * ell) * upperGradPartialSum (ell : ℤ) 0 q omega =
      ∑ r ∈ Finset.range q,
        (localCubeControl (ell : ℤ) (omega.1 ((ell : ℤ) - (r : ℤ))) +
          (3 : ℝ) ^ (2 * ell) * Section4.Support.shellW1InfGradNorm (ell : ℤ)
            (omega.1 ((ell : ℤ) + (r : ℤ)))) := by
    rw [lowerValuePartialSum, upperGradPartialSum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    simp only [ShellField.translate_zero]
  rw [hsum]
  calc
    ∑ r ∈ Finset.range q,
        (localCubeControl (ell : ℤ) (omega.1 ((ell : ℤ) - (r : ℤ))) +
          (3 : ℝ) ^ (2 * ell) * Section4.Support.shellW1InfGradNorm (ell : ℤ)
            (omega.1 ((ell : ℤ) + (r : ℤ)))) ≤
      ∑ r ∈ Finset.range q, (C₀ : ℝ) * (3 : ℝ) ^ ell *
        (2 * (((ell : ℝ) + 1) * sharpSpatialRatio ^ ell) *
          (((r : ℝ) + 1) *
            (sharpLowerRatio M ^ r + sharpUpperRatio M ^ r))) := by
      exact Finset.sum_le_sum fun r _ => sharpGrowthTerm_le M hC₀ ell r
    _ = (C₀ : ℝ) * (3 : ℝ) ^ ell * 2 *
        (((ell : ℝ) + 1) * sharpSpatialRatio ^ ell) *
          (∑ r ∈ Finset.range q, ((r : ℝ) + 1) *
            (sharpLowerRatio M ^ r + sharpUpperRatio M ^ r)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ ≤ (C₀ : ℝ) * (3 : ℝ) ^ ell * 2 * A * B := by
      have hleft := mul_le_mul hA hB
        (Finset.sum_nonneg fun r _ => sharpRadialProfile_nonneg M r) hA0
      have hcoef : 0 ≤ (C₀ : ℝ) * (3 : ℝ) ^ ell * 2 :=
        mul_nonneg (mul_nonneg (Nat.cast_nonneg C₀) (pow_nonneg (by norm_num) _))
          (by norm_num)
      convert mul_le_mul_of_nonneg_left hleft hcoef using 1
      all_goals first | rfl | ring
    _ = (2 * (C₀ : ℝ) * A * B) * (3 : ℝ) ^ ell := by ring
    _ ≤ (C : ℝ) * (3 : ℝ) ^ ell :=
      mul_le_mul_of_nonneg_right hC (pow_nonneg (by norm_num) _)

end

end Algsuperdiff.Section5.Field
