/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.AuxiliaryPolynomial.HypersurfaceLargeHeightDegree
public import LeanPool.CCDN.AuxiliaryPolynomial.HypersurfaceNormalizedComparison
public import LeanPool.CCDN.AuxiliaryPolynomial.HypersurfaceSmallHeightAuxiliary
import LeanPool.CCDN.AuxiliaryPolynomial.HypersurfaceLargeHeightAuxiliary

/-! Combine the two height ranges under the paper's explicit leading-coefficient
position condition. The main term retains the bad-prime factor of any finite prime
set whose normalized comparison holds. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private lemma inverse_rpow_le_of_log_position {H L q D : ℝ} (hH : 0 < H) (hL : 0 < L)
    (hq : 0 ≤ q) (hposition : Real.log H ≤ Real.log L + D) :
    1 / L ^ q ≤ Real.exp (q * D) / H ^ q := by
  apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
  rw [Real.log_div one_ne_zero (by positivity), Real.log_div (Real.exp_pos _).ne' (by positivity),
    Real.log_one, Real.log_exp, Real.log_rpow hL, Real.log_rpow hH]
  nlinarith [mul_le_mul_of_nonneg_left hposition hq]

/-- Replacing the coefficient height `H` by the leading height `L` in the small-height threshold
costs at most a factor `exp (T / (n + 1))`, provided `log H ≤ log L + T d d^(1/(n+1))`. -/
lemma hypersurfaceSmallThreshold_position {n d : ℕ} {B H L A T : ℝ}
    (hd : 0 < d) (hB : 0 ≤ B) (hH : 0 < H) (hL : 0 < L) (hA : 0 ≤ A)
    (hposition : Real.log H ≤ Real.log L + T * d * degreeRoot n d) :
    hypersurfaceSmallThreshold n d B L A ≤
      Real.exp (T / (n + 1 : ℝ)) * hypersurfaceSmallThreshold n d B H A := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hX : (0 : ℝ) < (d : ℝ) ^ (1 / (n + 1 : ℝ)) := by positivity
  have hh := inverse_rpow_le_of_log_position hH hL
    (show 0 ≤ 1 / ((n + 1 : ℝ) * d * (d : ℝ) ^ (1 / (n + 1 : ℝ))) by positivity) hposition
  have he : (1 / ((n + 1 : ℝ) * d * (d : ℝ) ^ (1 / (n + 1 : ℝ)))) *
      (T * d * (d : ℝ) ^ (1 / (n + 1 : ℝ))) = T / (n + 1 : ℝ) := by field_simp
  rw [he] at hh
  have hm := mul_le_mul_of_nonneg_left hh
    (show 0 ≤
      Real.exp (hypersurfaceSmallHeightError (n + 1) (hypersurfaceBadPrimeNormalizedError n)) *
      (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * A *
        B ^ ((n + 2 : ℝ) / ((n + 1 : ℝ) * (d : ℝ) ^ (1 / (n + 1 : ℝ)))) by positivity)
  simpa only [hypersurfaceSmallThreshold, div_eq_mul_inv, one_mul, mul_assoc, mul_left_comm,
    mul_comm] using hm

/-- Explicit constant for the positioned absolutely irreducible case. -/
def hypersurfacePositionedAuxiliaryConstant (n : ℕ) (T : ℝ) : ℝ :=
  4 + 8 * (n + 2 : ℝ) +
    Real.exp (hypersurfaceLargeHeightError (n + 1) (hypersurfaceNormalizedError n) T) +
    Real.exp (T / (n + 1 : ℝ)) *
      Real.exp (hypersurfaceSmallHeightError (n + 1) (hypersurfaceBadPrimeNormalizedError n))

/-- The small-height degree bound fits under the positioned bound. -/
private lemma small_height_bound_le_positioned {n d : ℕ} (hd : 0 < d) {B b H T : ℝ} (hB : 1 ≤ B)
    (hb : 0 ≤ b) (hH : 0 ≤ H) :
    2 * d + (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B +
        Real.exp (T / (n + 1 : ℝ)) * Real.exp (hypersurfaceSmallHeightError (n + 1)
          (hypersurfaceBadPrimeNormalizedError n)) * auxMainTerm n d B b H + 2 ≤
      hypersurfacePositionedAuxiliaryConstant n T * auxDegreeBound n d B b H := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  let Q := auxMainTerm n d B b H
  let l := (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B
  let D := (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ))
  let C := hypersurfacePositionedAuxiliaryConstant n T
  let Cs := Real.exp (T / (n + 1 : ℝ)) *
    Real.exp (hypersurfaceSmallHeightError (n + 1) (hypersurfaceBadPrimeNormalizedError n))
  have hQ : 0 ≤ Q := by
    have : (0 : ℝ) ≤ B := by linarith
    dsimp [Q, auxMainTerm]; positivity
  have hl : 0 ≤ l := mul_nonneg (Real.rpow_nonneg hd0.le _) (Real.log_nonneg hB)
  have hD : 0 ≤ D := Real.rpow_nonneg hd0.le _
  have hlarge := Real.exp_pos
    (hypersurfaceLargeHeightError (n + 1) (hypersurfaceNormalizedError n) T)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hCs : Cs ≤ C := by
    dsimp only [Cs, C, hypersurfacePositionedAuxiliaryConstant]
    linarith
  have hC4 : 4 ≤ C := by
    have : 0 < Cs := mul_pos (Real.exp_pos _) (Real.exp_pos _)
    dsimp only [C, hypersurfacePositionedAuxiliaryConstant]
    dsimp only [Cs] at this
    linarith
  have hdD : (d : ℝ) ≤ D := le_rpow_four_sub_inv hd
  change 2 * d + l + Cs * Q + 2 ≤ C * (Q + l + D)
  have h1 := mul_le_mul_of_nonneg_right hCs hQ
  have h2 := mul_le_mul_of_nonneg_right (show 1 ≤ C by linarith) hl
  have h3 := mul_le_mul_of_nonneg_right hC4 hD
  nlinarith

/-- The large-height degree bound fits under the positioned bound. -/
private lemma large_height_bound_le_positioned {n d : ℕ} (hd : 0 < d) {B b H T : ℝ} (hB : 1 ≤ B)
    (hb : 0 ≤ b) (hH : 0 ≤ H) :
    (8 * (n + 2 : ℝ) + Real.exp (hypersurfaceLargeHeightError (n + 1)
        (hypersurfaceNormalizedError n) T) + 2) * (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) ≤
      hypersurfacePositionedAuxiliaryConstant n T * auxDegreeBound n d B b H := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hD : 0 ≤ (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) := Real.rpow_nonneg hd0.le _
  have hQl : 0 ≤ auxMainTerm n d B b H + (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B := by
    have : (0 : ℝ) ≤ B := by linarith
    have := Real.log_nonneg hB
    unfold auxMainTerm; positivity
  have hS : 0 < Real.exp (T / (n + 1 : ℝ)) *
      Real.exp (hypersurfaceSmallHeightError (n + 1) (hypersurfaceBadPrimeNormalizedError n)) :=
    mul_pos (Real.exp_pos _) (Real.exp_pos _)
  have hlarge := Real.exp_pos
    (hypersurfaceLargeHeightError (n + 1) (hypersurfaceNormalizedError n) T)
  have hCl : 8 * (n + 2 : ℝ) + Real.exp (hypersurfaceLargeHeightError (n + 1)
      (hypersurfaceNormalizedError n) T) + 2 ≤ hypersurfacePositionedAuxiliaryConstant n T := by
    unfold hypersurfacePositionedAuxiliaryConstant
    linarith
  have hC : 0 ≤ hypersurfacePositionedAuxiliaryConstant n T := by
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  unfold auxDegreeBound
  nlinarith [mul_le_mul_of_nonneg_right hCl hD, mul_nonneg hC hQl]

/-- The coefficient-sensitive auxiliary theorem for an absolutely irreducible
homogeneous equation satisfying explicit leading-coefficient positioning, for any
finite prime set `bad` for which the normalized comparison holds. Both height ranges
and the degree are constructed. -/
theorem positioned_auxiliary_degree_of_comparison
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {n d t : ℕ}
    (order : MonomialOrder (Fin (n + 3))) (f : MvPolynomial (Fin (n + 3)) ℤ)
    (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hir : Irreducible (map (Int.castRingHom K) f))
    (H : ℝ) (hH : 1 ≤ H) (hcoeff : CoefficientHeightLE f H)
    {B : ℝ} {z : Fin t → IntPoint (n + 3)} (hzB : IsPrimitiveBoxZeroFamily f B z)
    (bad : Finset ℕ) (hcomp : AuxiliaryRankComparison order f d z bad)
    (T : ℝ) (hT : 0 ≤ T)
    (hposition : Real.log H ≤ Real.log |((order.leadingCoeff f : ℤ) : ℝ)| +
      T * d * degreeRoot n d) :
    ∃ M : ℕ,
      (M : ℝ) ≤ hypersurfacePositionedAuxiliaryConstant n T *
        auxDegreeBound n d B (primeSetFactor bad) H ∧
      ∃ g, IsPointAuxiliary f g M z := by
  obtain ⟨⟨hB, hz, hbox⟩, hprim⟩ := hzB
  have hf0 := ne_zero_of_irreducible_map hir
  have hL : 0 < |((order.leadingCoeff f : ℤ) : ℝ)| :=
    abs_pos.mpr (Int.cast_ne_zero.mpr (order.leadingCoeff_ne_zero_iff.mpr hf0))
  have hb : 0 ≤ primeSetFactor bad := (Real.exp_pos _).le
  by_cases hsmall : Real.log H ≤ 2 * d * (n + 2 : ℝ) * Real.log B
  · have hlead : |((order.leadingCoeff f : ℤ) : ℝ)| ≤ H := hcoeff (order.degree f)
    obtain ⟨M, hbound, hg⟩ := auxiliary_small_height_degree_of_comparison order f hf0 hd z hB
      hbox bad hcomp ((Real.log_le_log hL hlead).trans hsmall)
    have hp := hypersurfaceSmallThreshold_position hd (by linarith : 0 ≤ B)
      (by linarith : 0 < H) hL hb hposition
    have hp' : hypersurfaceSmallThreshold n d B |((order.leadingCoeff f : ℤ) : ℝ)|
        (primeSetFactor bad) ≤ Real.exp (T / (n + 1 : ℝ)) *
          Real.exp (hypersurfaceSmallHeightError (n + 1) (hypersurfaceBadPrimeNormalizedError n)) *
          auxMainTerm n d B (primeSetFactor bad) H := by
      convert hp using 1
      unfold hypersurfaceSmallThreshold auxMainTerm
      ring
    refine ⟨M, le_trans ?_ (small_height_bound_le_positioned hd hB hb (by linarith)), hg⟩
    linarith
  · obtain ⟨M, hbound, g, hg⟩ := hypersurface_auxiliary_large_height_degree order f hf hd hir H hH
      hcoeff z hprim hz hB hbox T hT (le_of_not_ge hsmall) hposition
    exact ⟨M, hbound.trans (large_height_bound_le_positioned hd hB hb (by linarith)), g,
      isPointAuxiliary_iff.mpr hg⟩
end
end CCDN
