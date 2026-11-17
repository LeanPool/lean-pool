/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.AuxiliaryPolynomial.PrimeScaledAffineHeight
public import LeanPool.CCDN.AuxiliaryPolynomial.ScalingPrime
import LeanPool.CCDN.AuxiliaryPolynomial.HypersurfaceHeightTransfer
import LeanPool.CCDN.AuxiliaryPolynomial.PrimeScaledAffineAuxiliary
import LeanPool.CCDN.AuxiliaryPolynomial.PrimeScaledAffineHeight
import LeanPool.CCDN.AuxiliaryPolynomial.ScaledHypersurfaceBadPrimes
import LeanPool.CCDN.Height.ScaledHypersurfaceHeight

/-! Both bounds for the bad-prime factor apply to the same homogeneous
auxiliary. Their minimum therefore survives the affine exponent saving. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The affine auxiliary degree bound in which the coefficient-sensitive main term involves the
minimum of `log L + d log B + d²` and `d² b`, where `L` is the height of the leading form and
`b` a bad-prime factor, with box exponent `1 / d^(1/(n+1))` up to the factor `A`. -/
def affineMinimumAuxiliaryBound (n d : ℕ) (A B L b : ℝ) : ℝ :=
  hypersurfaceAbsoluteAuxiliaryConstant n *
    (max (affineHeightTransferConstant n) (Real.exp 1) * A *
        (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) *
        min (Real.log L + d * Real.log B + (d : ℝ) ^ 2) ((d : ℝ) ^ 2 * b) *
        B ^ (1 / (d : ℝ) ^ (1 / (n + 1 : ℝ))) /
          L ^ (1 / ((n + 1 : ℝ) * d * (d : ℝ) ^ (1 / (n + 1 : ℝ)))) +
      (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B +
        (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)))

/-- The scaled auxiliary degree bound for any bad-prime factor `c` with
`c ≤ Real.exp 1 * b` and `0 ≤ b`. -/
theorem scaled_hypersurface_auxiliary_bound_of_badPrime_le {n : ℕ}
    (f : MvPolynomial (Fin (n + 2)) ℤ) (hf : f ≠ 0) (hd : 0 < f.totalDegree)
    {p : ℕ} (hp : p.Prime) {A B : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B)
    (hBp : B / A ≤ p) {c b : ℝ} (hFbad : 0 ≤ c) (hb : 0 ≤ b)
    (hbad : c ≤ Real.exp 1 * b) :
    hypersurfaceAuxiliaryDegreeBound n f.totalDegree B c
        (integerCoefficientHeight (scaledHomogenize f.totalDegree (p : ℤ) f) : ℝ) ≤
      hypersurfaceAbsoluteAuxiliaryConstant n *
        (Real.exp 1 * A * (f.totalDegree : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) *
            ((f.totalDegree : ℝ) ^ 2 *
              b) *
            B ^ (1 / (f.totalDegree : ℝ) ^ (1 / (n + 1 : ℝ))) /
              (integerCoefficientHeight (homogeneousComponent f.totalDegree f) : ℝ) ^
                (1 / ((n + 1 : ℝ) * f.totalDegree *
                  (f.totalDegree : ℝ) ^ (1 / (n + 1 : ℝ)))) +
          (f.totalDegree : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B +
            (f.totalDegree : ℝ) ^ (4 - 1 / (n + 1 : ℝ))) := by
  let d := f.totalDegree
  let F := scaledHomogenize d (p : ℤ) f
  let L := (integerCoefficientHeight (homogeneousComponent d f) : ℝ)
  let H := (integerCoefficientHeight F : ℝ)
  let Y := (p : ℝ) ^ d * L
  let α := (n + 2 : ℝ) / ((n + 1 : ℝ) * (d : ℝ) ^ (1 / (n + 1 : ℝ)))
  let β := 1 / ((n + 1 : ℝ) * (d : ℝ) ^ (1 / (n + 1 : ℝ)))
  let q := 1 / ((n + 1 : ℝ) * d * (d : ℝ) ^ (1 / (n + 1 : ℝ)))
  have hd0 : (0 : ℝ) < d := by dsimp only [d]; exact_mod_cast hd
  have hpZ : (1 : ℤ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hL : 1 ≤ L := leading_height_one_le f hf
  have hL0 : 0 < L := by linarith
  have hY0 : 0 < Y := mul_pos (pow_pos hp0 _) hL0
  have hYH : Y ≤ H := by
    simpa only [Int.cast_natCast] using scaledHomogenize_leading_height_lower f hpZ
  have hH0 : 0 < H := hY0.trans_le hYH
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hYpow : Y ^ q = (p : ℝ) ^ β * L ^ q := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      scaled_height_rpow (r := n + 1) (by omega) hd hp0 hL0
  have hdenom : Y ^ q ≤ H ^ q := Real.rpow_le_rpow hY0.le hYH hq
  have hnR : (n : ℝ) + 1 + 1 = n + 2 := by ring
  have hpower : B ^ α / (p : ℝ) ^ β ≤ A * B ^ (1 / (d : ℝ) ^ (1 / (n + 1 : ℝ))) := by
    simpa only [Nat.cast_add, Nat.cast_one, hnR] using
      affine_scaling_box_power (r := n + 1) (by omega) hd hB hA hp0 hBp
  have hpowers : (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) =
      (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) * (d : ℝ) ^ 2 :=
    rpow_four_sub_eq_mul_sq hd0 n
  have hmain : (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * c * B ^ α / H ^ q ≤
      Real.exp 1 * A * (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) * ((d : ℝ) ^ 2 * b) *
        B ^ (1 / (d : ℝ) ^ (1 / (n + 1 : ℝ))) / L ^ q := by
    calc
      _ ≤ (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * c * B ^ α / Y ^ q :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hdenom
      _ ≤ (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * (Real.exp 1 * b) * B ^ α / Y ^ q := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hbad (by positivity)) (by positivity)
      _ = (Real.exp 1 * (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * b / L ^ q) *
          (B ^ α / (p : ℝ) ^ β) := by rw [hYpow]; ring
      _ ≤ (Real.exp 1 * (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * b / L ^ q) *
          (A * B ^ (1 / (d : ℝ) ^ (1 / (n + 1 : ℝ)))) :=
        mul_le_mul_of_nonneg_left hpower (by positivity)
      _ = _ := by rw [hpowers]; ring
  unfold hypersurfaceAuxiliaryDegreeBound
  exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add hmain le_rfl) le_rfl)
    (hypersurfaceAbsoluteAuxiliaryConstant_pos n).le

private theorem scaled_hypersurface_auxiliary_badPrime_bound {n : ℕ}
    (f : MvPolynomial (Fin (n + 2)) ℤ) (hf : f ≠ 0) (hd : 0 < f.totalDegree)
    {p : ℕ} (hp : p.Prime) {A B : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B)
    (hBp : B / A ≤ p) :
    hypersurfaceAuxiliaryDegreeBound n f.totalDegree B
        (hypersurfaceBadPrimeFactor (scaledHomogenize f.totalDegree (p : ℤ) f))
        (integerCoefficientHeight (scaledHomogenize f.totalDegree (p : ℤ) f) : ℝ) ≤
      hypersurfaceAbsoluteAuxiliaryConstant n *
        (Real.exp 1 * A * (f.totalDegree : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) *
            ((f.totalDegree : ℝ) ^ 2 *
              hypersurfaceBadPrimeFactor (scaledHomogenize f.totalDegree 1 f)) *
            B ^ (1 / (f.totalDegree : ℝ) ^ (1 / (n + 1 : ℝ))) /
              (integerCoefficientHeight (homogeneousComponent f.totalDegree f) : ℝ) ^
                (1 / ((n + 1 : ℝ) * f.totalDegree *
                  (f.totalDegree : ℝ) ^ (1 / (n + 1 : ℝ)))) +
          (f.totalDegree : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B +
            (f.totalDegree : ℝ) ^ (4 - 1 / (n + 1 : ℝ))) := by
  have hbad := hypersurfaceBadPrimeFactor_scaledHomogenize_le f hf hp
  exact scaled_hypersurface_auxiliary_bound_of_badPrime_le f hf hd hp hA hB hBp
    (hypersurfaceBadPrimeFactor_nonneg _) (hypersurfaceBadPrimeFactor_nonneg _) hbad

/-- The auxiliary degree bound of the `p`-scaled homogenization is at most
`affineMinimumAuxiliaryBound`, the minimum of the two coefficient estimates, so the auxiliary
polynomial satisfies the better of the two without changing its zero set. -/
private theorem scaled_hypersurface_auxiliary_minimum_bound {n : ℕ}
    (f : MvPolynomial (Fin (n + 2)) ℤ) (hf : f ≠ 0) (hd : 0 < f.totalDegree)
    {p : ℕ} (hp : p.Prime) {A B : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B)
    (hpB : (p : ℝ) ≤ B) (hBp : B / A ≤ p) :
    hypersurfaceAuxiliaryDegreeBound n f.totalDegree B
        (hypersurfaceBadPrimeFactor (scaledHomogenize f.totalDegree (p : ℤ) f))
        (integerCoefficientHeight (scaledHomogenize f.totalDegree (p : ℤ) f) : ℝ) ≤
      affineMinimumAuxiliaryBound n f.totalDegree A B
        (integerCoefficientHeight (homogeneousComponent f.totalDegree f) : ℝ)
        (hypersurfaceBadPrimeFactor (scaledHomogenize f.totalDegree 1 f)) := by
  let d := f.totalDegree
  let L := (integerCoefficientHeight (homogeneousComponent d f) : ℝ)
  let b := hypersurfaceBadPrimeFactor (scaledHomogenize d 1 f)
  let T := Real.log L + d * Real.log B + (d : ℝ) ^ 2
  let K := max (affineHeightTransferConstant n) (Real.exp 1)
  have hL : 1 ≤ L := leading_height_one_le f hf
  have hT : 0 ≤ T := add_nonneg
    (add_nonneg (Real.log_nonneg hL) (mul_nonneg (Nat.cast_nonneg d) (Real.log_nonneg hB)))
    (sq_nonneg _)
  have hb : 0 ≤ b := hypersurfaceBadPrimeFactor_nonneg _
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  by_cases hmin : T ≤ (d : ℝ) ^ 2 * b
  · apply (scaled_hypersurface_auxiliary_bound f hf hd
      (by exact_mod_cast hp.one_lt.le : (1 : ℤ) ≤ p) hA hB
      (by simpa only [Int.cast_natCast] using hpB)
      (by simpa only [Int.cast_natCast] using hBp)).trans
    change affineLogarithmicAuxiliaryBound n d A B L ≤ affineMinimumAuxiliaryBound n d A B L b
    unfold affineLogarithmicAuxiliaryBound affineMinimumAuxiliaryBound
    rw [min_eq_left hmin]
    apply mul_le_mul_of_nonneg_left _ (hypersurfaceAbsoluteAuxiliaryConstant_pos n).le
    apply add_le_add _ le_rfl
    apply add_le_add _ le_rfl
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left _ _) hA0) (by positivity)) hT) (by positivity)
  · apply (scaled_hypersurface_auxiliary_badPrime_bound f hf hd hp hA hB hBp).trans
    change _ ≤ affineMinimumAuxiliaryBound n d A B L b
    unfold affineMinimumAuxiliaryBound
    rw [min_eq_right (le_of_not_ge hmin)]
    apply mul_le_mul_of_nonneg_left _ (hypersurfaceAbsoluteAuxiliaryConstant_pos n).le
    apply add_le_add _ le_rfl
    apply add_le_add _ le_rfl
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right _ _) hA0) (by positivity)) (by positivity))
        (by positivity)

private theorem prime_scaled_affine_auxiliary_minimum {n : ℕ}
    (f : MvPolynomial (Fin (n + 2)) ℤ) (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible f) (hd : 0 < f.totalDegree)
    {p : ℕ} (hp : p.Prime) (hp0 : ¬ (p : ℤ) ∣ f.coeff 0)
    {A B : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hpB : (p : ℝ) ≤ B) (hBp : B / A ≤ p) :
    ∃ g, IsBoxAuxiliary f g B ∧
      (g.totalDegree : ℝ) ≤ affineMinimumAuxiliaryBound n f.totalDegree A B
        (integerCoefficientHeight (homogeneousComponent f.totalDegree f) : ℝ)
        (hypersurfaceBadPrimeFactor (scaledHomogenize f.totalDegree 1 f)) := by
  obtain ⟨g, hg, hgdegree⟩ := prime_scaled_affine_auxiliary f hprim hir hd hp hp0 hB hpB
  exact ⟨g, hg, hgdegree.trans
    (scaled_hypersurface_auxiliary_minimum_bound f hir.ne_zero hd hp hA hB hpB hBp)⟩

/-- If the constant coefficient `c` of a primitive irreducible integer polynomial `f` is nonzero
and `log |c| < B / scalingPrimeRatio`, with `B ≥ scalingPrimeRatio`, then `f` has a box
auxiliary polynomial of degree at most `affineMinimumAuxiliaryBound`, with ratio
`scalingPrimeRatio` and the bad-prime factor of the homogenization of `f`. -/
theorem affine_auxiliary_minimum_of_small_constant_coefficient {n : ℕ}
    (f : MvPolynomial (Fin (n + 2)) ℤ) (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible f) (hd : 0 < f.totalDegree) (hc : f.coeff 0 ≠ 0)
    {B : ℝ} (hB : scalingPrimeRatio ≤ B)
    (hheight : Real.log |(f.coeff 0 : ℝ)| < B / scalingPrimeRatio) :
    ∃ g, IsBoxAuxiliary f g B ∧
      (g.totalDegree : ℝ) ≤ affineMinimumAuxiliaryBound n f.totalDegree scalingPrimeRatio B
        (integerCoefficientHeight (homogeneousComponent f.totalDegree f) : ℝ)
        (hypersurfaceBadPrimeFactor (scaledHomogenize f.totalDegree 1 f)) := by
  obtain ⟨p, hp, hlo, hhi, hnd⟩ := exists_scaling_prime hB hc hheight
  exact prime_scaled_affine_auxiliary_minimum f hprim hir hd hp hnd
    scalingPrimeRatio_one_le (scalingPrimeRatio_one_le.trans hB) hhi hlo.le

end
end CCDN
