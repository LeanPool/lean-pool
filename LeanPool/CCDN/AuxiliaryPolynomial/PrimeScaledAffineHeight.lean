/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.ScaledHomogenization
public import LeanPool.CCDN.AuxiliaryPolynomial.AbsoluteAuxiliary
public import LeanPool.CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimeFactor
import LeanPool.CCDN.AuxiliaryPolynomial.HypersurfaceHeightTransfer
import LeanPool.CCDN.AuxiliaryPolynomial.PrimeScaledAffineAuxiliary
import LeanPool.CCDN.Height.ScaledHypersurfaceHeight

/-!
The coefficient-sensitive affine degree saving for a prime comparable
to the box radius. The leading homogeneous height belongs to the original equation.

The prime-scaled height gain gives the affine exponent 1/d^(1/r).
-/

@[expose] public section
namespace CCDN

/-- For a scaling prime `p ≥ B / A` with `A, B ≥ 1`, the box term `B ^ ((r + 1) / (r d^(1/r)))`
divided by `p ^ (1 / (r d^(1/r)))` is at most `A * B ^ (1 / d^(1/r))`. -/
lemma affine_scaling_box_power {r d : ℕ} (hr : 0 < r) (hd : 0 < d)
    {B A p : ℝ} (hB : 1 ≤ B) (hA : 1 ≤ A) (hp : 0 < p) (hBp : B / A ≤ p) :
    B ^ (((r : ℝ) + 1) / ((r : ℝ) * (d : ℝ) ^ (1 / (r : ℝ)))) /
        p ^ (1 / ((r : ℝ) * (d : ℝ) ^ (1 / (r : ℝ)))) ≤
      A * B ^ (1 / (d : ℝ) ^ (1 / (r : ℝ))) := by
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hroot : (1 : ℝ) ≤ (d : ℝ) ^ (1 / (r : ℝ)) := Real.one_le_rpow hd1 (by positivity)
  have hr0 : (0 : ℝ) < r := by linarith
  have hroot0 : (0 : ℝ) < (d : ℝ) ^ (1 / (r : ℝ)) := by positivity
  let β := 1 / ((r : ℝ) * (d : ℝ) ^ (1 / (r : ℝ)))
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have hβ1 : β ≤ 1 := by
    apply (div_le_one (by positivity : (0 : ℝ) < (r : ℝ) * (d : ℝ) ^ (1 / (r : ℝ)))).mpr
    exact one_le_mul_of_one_le_of_one_le hr1 hroot
  have hBA : B / p ≤ A := by
    apply (div_le_iff₀ hp).mpr
    have hh := (div_le_iff₀ (by linarith : 0 < A)).mp hBp
    nlinarith
  have hpow : (B / p) ^ β ≤ A :=
    (Real.rpow_le_rpow (by positivity) hBA hβ).trans
      (by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hA hβ1)
  have he : ((r : ℝ) + 1) / ((r : ℝ) * (d : ℝ) ^ (1 / (r : ℝ))) =
      1 / (d : ℝ) ^ (1 / (r : ℝ)) + β := by dsimp [β]; field_simp
  calc
    _ = B ^ (1 / (d : ℝ) ^ (1 / (r : ℝ))) * (B / p) ^ β := by
      rw [he, Real.rpow_add (by linarith), Real.div_rpow (by linarith) hp.le]
      ring
    _ ≤ B ^ (1 / (d : ℝ) ^ (1 / (r : ℝ))) * A :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := mul_comm _ _

/-- Splitting the power of the scaled height: `(p^d L) ^ (1/(r d d^(1/r)))` equals
`p ^ (1/(r d^(1/r))) * L ^ (1/(r d d^(1/r)))` for positive `p` and `L`. -/
lemma scaled_height_rpow {r d : ℕ} (hr : 0 < r) (hd : 0 < d)
    {p L : ℝ} (hp : 0 < p) (hL : 0 < L) :
    (p ^ d * L) ^ (1 / ((r : ℝ) * d * (d : ℝ) ^ (1 / (r : ℝ)))) =
      p ^ (1 / ((r : ℝ) * (d : ℝ) ^ (1 / (r : ℝ)))) *
        L ^ (1 / ((r : ℝ) * d * (d : ℝ) ^ (1 / (r : ℝ)))) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  rw [Real.mul_rpow (by positivity) hL.le, ← Real.rpow_natCast, ← Real.rpow_mul hp.le]
  congr 2
  field_simp

end CCDN

namespace CCDN
noncomputable section
open MvPolynomial

/-- The dimension constant `(n + 1) exp (2 mertensError + 1) hypersurfaceHeightConstant (n + 3)`
by which the logarithmic height term of a prime-scaled model is compared with that of the
original affine equation. -/
def affineHeightTransferConstant (n : ℕ) : ℝ :=
  (n + 1 : ℝ) * Real.exp (2 * mertensError + 1) * hypersurfaceHeightConstant (n + 3)

/-- The logarithmic-branch affine auxiliary degree bound: the bound of CCDN Theorem 3.1.1 with the
bad-prime factor replaced by `log L + d log B + d²`, where `L` is the height of the leading form,
and the box exponent saved to `1 / d^(1/(n+1))` up to the factor `A`. -/
def affineLogarithmicAuxiliaryBound (n d : ℕ) (A B L : ℝ) : ℝ :=
  hypersurfaceAbsoluteAuxiliaryConstant n *
    (affineHeightTransferConstant n * A * (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) *
        (Real.log L + d * Real.log B + (d : ℝ) ^ 2) *
        B ^ (1 / (d : ℝ) ^ (1 / (n + 1 : ℝ))) /
          L ^ (1 / ((n + 1 : ℝ) * d * (d : ℝ) ^ (1 / (n + 1 : ℝ)))) +
      (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B + (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)))

/-- For a scaling factor `1 ≤ p ≤ B` with `B / A ≤ p`, the auxiliary degree bound of the `p`-scaled
homogenization of `f`, with its own bad-prime factor and coefficient height, is at most
`affineLogarithmicAuxiliaryBound` in terms of the height of the leading form of `f`. -/
theorem scaled_hypersurface_auxiliary_bound {n : ℕ}
    (f : MvPolynomial (Fin (n + 2)) ℤ) (hf : f ≠ 0) (hd : 0 < f.totalDegree)
    {p : ℤ} (hp : 1 ≤ p) {A B : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B)
    (hpB : (p : ℝ) ≤ B) (hBp : B / A ≤ p) :
    hypersurfaceAuxiliaryDegreeBound n f.totalDegree B
        (hypersurfaceBadPrimeFactor (scaledHomogenize f.totalDegree p f))
        (integerCoefficientHeight (scaledHomogenize f.totalDegree p f) : ℝ) ≤
      affineLogarithmicAuxiliaryBound n f.totalDegree A B
        (integerCoefficientHeight (homogeneousComponent f.totalDegree f) : ℝ) := by
  let d := f.totalDegree
  let F := scaledHomogenize d p f
  let L := (integerCoefficientHeight (homogeneousComponent d f) : ℝ)
  let H := (integerCoefficientHeight F : ℝ)
  let Y := (p : ℝ) ^ d * L
  let α := (n + 2 : ℝ) / ((n + 1 : ℝ) * (d : ℝ) ^ (1 / (n + 1 : ℝ)))
  let β := 1 / ((n + 1 : ℝ) * (d : ℝ) ^ (1 / (n + 1 : ℝ)))
  let q := 1 / ((n + 1 : ℝ) * d * (d : ℝ) ^ (1 / (n + 1 : ℝ)))
  let K := affineHeightTransferConstant n
  let T := Real.log L + d * Real.log B + (d : ℝ) ^ 2
  have hd0 : (0 : ℝ) < d := by dsimp only [d]; exact_mod_cast hd
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hL : 1 ≤ L := leading_height_one_le f hf
  have hL0 : 0 < L := by linarith
  have hY : 1 ≤ Y := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hp1) hL
  have hYH : Y ≤ H := scaledHomogenize_leading_height_lower f hp
  have hF0 : F ≠ 0 := scaledHomogenize_ne_zero d (by omega) hf
  have hFdegree : F.totalDegree = d := (scaledHomogenize_homogeneous p f le_rfl).totalDegree hF0
  have hK : 0 ≤ K := by
    dsimp only [K, affineHeightTransferConstant]
    exact mul_nonneg (by positivity) (zero_le_one.trans (hypersurfaceHeightConstant_one_le _))
  have hlogY : Real.log Y = d * Real.log p + Real.log L := by
    dsimp only [Y]
    rw [Real.log_mul (by positivity) hL0.ne', Real.log_pow]
  have hT : 0 ≤ T := add_nonneg
    (add_nonneg (Real.log_nonneg hL) (mul_nonneg hd0.le (Real.log_nonneg hB))) (sq_nonneg _)
  have hnum : Real.log Y + (d : ℝ) ^ 2 ≤ T := by
    rw [hlogY]
    dsimp only [T]
    have hh := mul_le_mul_of_nonneg_left (Real.log_le_log hp0 hpB) hd0.le
    linarith
  have hYpow : Y ^ q = (p : ℝ) ^ β * L ^ q := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      scaled_height_rpow (r := n + 1) (by omega) hd hp0 hL0
  have htransfer : (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * hypersurfaceBadPrimeFactor F / H ^ q ≤
      K * (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) * (Real.log Y + (d : ℝ) ^ 2) / ((p : ℝ) ^ β * L ^ q) := by
    have hh := hypersurface_badPrime_height_transfer F hF0 hFdegree hd hY hYH
    rw [hYpow] at hh
    exact hh
  have hnR : (n : ℝ) + 1 + 1 = n + 2 := by ring
  have hpower : B ^ α / (p : ℝ) ^ β ≤ A * B ^ (1 / (d : ℝ) ^ (1 / (n + 1 : ℝ))) := by
    simpa only [Nat.cast_add, Nat.cast_one, hnR] using
      affine_scaling_box_power (r := n + 1) (by omega) hd hB hA hp0 hBp
  have hmain : (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * hypersurfaceBadPrimeFactor F * B ^ α / H ^ q ≤
      K * A * (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) * T *
        B ^ (1 / (d : ℝ) ^ (1 / (n + 1 : ℝ))) / L ^ q := by
    calc
      _ ≤ K * (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) * (Real.log Y + (d : ℝ) ^ 2) * B ^ α /
          ((p : ℝ) ^ β * L ^ q) := by
        convert mul_le_mul_of_nonneg_right htransfer (show 0 ≤ B ^ α by positivity) using 1 <;> ring
      _ = K * (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) *
          ((Real.log Y + (d : ℝ) ^ 2) / L ^ q) * (B ^ α / (p : ℝ) ^ β) := by ring
      _ ≤ K * (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) * (T / L ^ q) *
          (A * B ^ (1 / (d : ℝ) ^ (1 / (n + 1 : ℝ)))) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hnum (by positivity))
            (by positivity)
        · exact hpower
        · positivity
        · positivity
      _ = _ := by ring
  unfold hypersurfaceAuxiliaryDegreeBound affineLogarithmicAuxiliaryBound
  apply mul_le_mul_of_nonneg_left _ (hypersurfaceAbsoluteAuxiliaryConstant_pos n).le
  exact add_le_add (add_le_add hmain le_rfl) le_rfl

/-- The logarithmic-height branch of the affine auxiliary bound, provided
a scaling prime lies between B/A and B and avoids the constant term.
The constructed polynomial vanishes on every original integer zero in the box. -/
theorem prime_scaled_affine_auxiliary_height {n : ℕ}
    (f : MvPolynomial (Fin (n + 2)) ℤ) (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible f) (hd : 0 < f.totalDegree)
    {p : ℕ} (hp : p.Prime) (hp0 : ¬ (p : ℤ) ∣ f.coeff 0)
    {A B : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hpB : (p : ℝ) ≤ B) (hBp : B / A ≤ p) :
    ∃ g, IsBoxAuxiliary f g B ∧
      (g.totalDegree : ℝ) ≤ affineLogarithmicAuxiliaryBound n f.totalDegree A B
        (integerCoefficientHeight (homogeneousComponent f.totalDegree f) : ℝ) := by
  obtain ⟨g, hg, hgdegree⟩ := prime_scaled_affine_auxiliary f hprim hir hd hp hp0 hB hpB
  refine ⟨g, hg, hgdegree.trans ?_⟩
  exact scaled_hypersurface_auxiliary_bound f hir.ne_zero hd
    (by exact_mod_cast hp.one_lt.le : (1 : ℤ) ≤ p) hA hB
    (by simpa only [Int.cast_natCast] using hpB) (by simpa only [Int.cast_natCast] using hBp)

end
end CCDN
