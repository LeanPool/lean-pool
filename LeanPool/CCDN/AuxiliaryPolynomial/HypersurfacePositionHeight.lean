/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.HomogeneousTranslation
public import LeanPool.CCDN.Height.IntegerCoefficientHeight
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import LeanPool.CCDN.Algebra.HomogeneousChart
import LeanPool.CCDN.Height.MultivariateGridHeight
import LeanPool.CCDN.Height.PolynomialBoxHeight
import LeanPool.CCDN.Plane.HomogeneousLeadingCoefficient

/-!
The bounded shear has a dimension-uniform logarithmic positioning cost.

Bounded integer shears placing a large coefficient first, in all dimensions.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The large leading-coefficient witness in arbitrary projective dimension.
Every original coefficient is controlled by one bounded grid evaluation. -/
private theorem exists_hypersurface_leading_coefficient_translation {n d : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ) (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) :
    ∃ a : Fin n → ℤ, (∀ j, 0 ≤ a j ∧ a j ≤ d) ∧
      MonomialOrder.lex.leadingCoeff (homogeneousTranslation ℤ a f) ≠ 0 ∧
      CoefficientHeightLE f (((d : ℝ) + 1) ^ (n * (d + 1)) *
        |((MonomialOrder.lex.leadingCoeff (homogeneousTranslation ℤ a f) : ℤ) : ℝ)|) := by
  have hc0 : affineChart n f ≠ 0 := by
    intro hz
    exact hf0 (affineChart_injective_on_homogeneous hf (isHomogeneous_zero _ _ d)
      (by simpa only [map_zero] using hz))
  obtain ⟨a, ha, hval, hcoeff⟩ := exists_integer_multivariate_grid_height_witness (affineChart n f)
    hc0 ((affineChart_totalDegree_le f).trans hf.totalDegree_le)
  have he : (homogeneousTranslation ℤ a f).coeff (Finsupp.single 0 d) =
      eval a (affineChart n f) := by
    rw [homogeneousTranslation_pure_first a f hf, affineChart_eval]
  have hlc := lex_leadingCoeff_eq_pure_first (homogeneousTranslation ℤ a f)
    (homogeneousTranslation_homogeneous a hf).totalDegree_le (he ▸ hval)
  refine ⟨a, ha, by rw [hlc, he]; exact hval, ?_⟩
  intro m
  by_cases hm : m.degree = d
  · obtain ⟨j, rfl⟩ := homogeneousMonomials_surjective n d m hm
    rw [← affineChart_homogeneous_coefficient f hf j, hlc, he]
    exact hcoeff _
  · rw [hf.coeff_eq_zero hm, Int.cast_zero, abs_zero]
    positivity

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial

private def hypersurfacePositionHeightFactor (n d : ℕ) : ℝ :=
  ((d : ℝ) + 1) ^ ((n + 1) * (d + 1) + (n + 1) + n * (d + 1) + 2 * d)

private lemma hypersurfacePositionHeightFactor_one_le (n d : ℕ) :
    1 ≤ hypersurfacePositionHeightFactor n d := by
  apply one_le_pow₀
  have := Nat.cast_nonneg (α := ℝ) d
  linarith

private lemma hypersurfacePositionHeightFactor_ge_grid (n d : ℕ) :
    ((d : ℝ) + 1) ^ (n * (d + 1)) ≤ hypersurfacePositionHeightFactor n d := by
  apply pow_le_pow_right₀ (by have := Nat.cast_nonneg (α := ℝ) d; linarith)
  omega

/-- Full homogeneous coefficient control after a bounded shear. -/
private theorem hypersurfaceTranslation_coefficient_bound {n d : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ) (hf : f.IsHomogeneous d) (hf0 : f ≠ 0)
    (a : Fin n → ℤ) (ha : ∀ j, 0 ≤ a j ∧ a j ≤ d)
    {L : ℝ} (hL : 0 ≤ L)
    (hcoeff : CoefficientHeightLE f (((d : ℝ) + 1) ^ (n * (d + 1)) * L))
    (m : Fin (n + 1) →₀ ℕ) :
    |((homogeneousTranslation ℤ a f).coeff m : ℝ)| ≤ hypersurfacePositionHeightFactor n d * L := by
  let K := ((d : ℝ) + 1) ^ (n * (d + 1))
  let V := ((d : ℝ) + 1) ^ (n + 1) * (K * L) * (((d : ℝ) + 1) ^ 2) ^ d
  have heval (z : Fin (n + 1) → ℕ) (hz : ∀ j, z j ≤ d) :
      |(eval (fun i => (z i : ℤ)) (homogeneousTranslation ℤ a f) : ℝ)| ≤ V := by
    let w : Fin (n + 1) → ℤ := Fin.cons (z 0 : ℤ)
      (fun j => (z j.succ : ℤ) + a j * (z 0 : ℤ))
    have hbox : InBox w (((d : ℝ) + 1) ^ 2) := by
      intro j
      have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      refine Fin.cases ?_ (fun k => ?_) j
      · have hz0 : (z 0 : ℝ) ≤ d := by exact_mod_cast hz 0
        simp only [w, Fin.cons_zero, Int.cast_natCast,
          abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (z 0))]
        nlinarith
      · have hz1 : (z k.succ : ℝ) ≤ d := by exact_mod_cast hz k.succ
        have hz0 : (z 0 : ℝ) ≤ d := by exact_mod_cast hz 0
        have ha0 : (0 : ℝ) ≤ a k := by exact_mod_cast (ha k).1
        have had : (a k : ℝ) ≤ d := by exact_mod_cast (ha k).2
        simp only [w, Fin.cons_succ, Int.cast_add, Int.cast_mul, Int.cast_natCast]
        rw [abs_of_nonneg (by positivity)]
        nlinarith [mul_le_mul had hz0 (Nat.cast_nonneg (z 0)) hd0]
    have hh := polynomial_eval₂_box_bound f (K * L) (((d : ℝ) + 1) ^ 2)
      (by dsimp [K]; positivity) (one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) d; linarith))
      hcoeff (fun j => (w j : ℝ)) hbox
    rw [hf.totalDegree hf0] at hh
    rw [homogeneousTranslation_eval]
    change |(eval w f : ℝ)| ≤ V
    have he : eval₂ (Int.castRingHom ℝ) (fun j => (w j : ℝ)) f = (eval w f : ℝ) :=
      (eval₂_comp (Int.castRingHom ℝ) w f).symm
    simpa only [he, Fintype.card_fin, V] using hh
  have hh := integer_multivariate_coefficient_bound_of_grid (homogeneousTranslation ℤ a f)
    (homogeneousTranslation_homogeneous a hf).totalDegree_le
    (show 0 ≤ V by dsimp [V, K]; positivity)
    heval m
  convert hh using 1
  dsimp only [hypersurfacePositionHeightFactor, V, K]
  simp only [pow_add, pow_mul]
  ring

/-- For positive integers `r` and `d`, `log (d + 1) ≤ (r + 1) * d ^ (1/r)`. -/
lemma log_nat_add_one_le_root {r d : ℕ} (hr : 0 < r) (hd : 0 < d) :
    Real.log ((d : ℝ) + 1) ≤ ((r : ℝ) + 1) * (d : ℝ) ^ (1 / (r : ℝ)) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hroot : (1 : ℝ) ≤ (d : ℝ) ^ (1 / (r : ℝ)) :=
    Real.one_le_rpow hd1 (by positivity)
  have hlog := Real.log_le_rpow_div (by linarith : (0 : ℝ) ≤ d)
    (show (0 : ℝ) < 1 / (r : ℝ) by positivity)
  have h2 : Real.log (2 : ℝ) ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  have hh := Real.log_le_log (by positivity : (0 : ℝ) < d + 1)
    (show (d : ℝ) + 1 ≤ 2 * d by linarith)
  rw [Real.log_mul (by norm_num) (by positivity)] at hh
  rw [div_div_eq_mul_div, div_one] at hlog
  nlinarith

/-- The loss is O_{n,r}(d^(1+1/r)), as required by the auxiliary theorem. -/
private lemma hypersurfacePositionHeightFactor_log_le {r d : ℕ} (n : ℕ) (hr : 0 < r) (hd : 0 < d) :
    Real.log (hypersurfacePositionHeightFactor n d) ≤
      (5 * (n : ℝ) + 5) * ((r : ℝ) + 1) * d * (d : ℝ) ^ (1 / (r : ℝ)) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hlog := log_nat_add_one_le_root hr hd
  have he : (((n + 1) * (d + 1) + (n + 1) + n * (d + 1) + 2 * d : ℕ) : ℝ) ≤
      (5 * (n : ℝ) + 5) * d := by push_cast; nlinarith
  unfold hypersurfacePositionHeightFactor
  rw [Real.log_pow]
  have hmul := mul_le_mul he hlog (Real.log_nonneg (by linarith : (1 : ℝ) ≤ d + 1))
    (show 0 ≤ (5 * (n : ℝ) + 5) * d by positivity)
  nlinarith

/-- Integer coordinates supply the logarithmic positioning condition,
and the chosen height bounds both the original and translated coefficients. -/
theorem exists_hypersurface_coefficient_position {n r d : ℕ} (hr : 0 < r) (hd : 0 < d)
    (f : MvPolynomial (Fin (n + 1)) ℤ) (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) :
    ∃ (a : Fin n → ℤ) (H : ℝ), (∀ j, 0 ≤ a j ∧ a j ≤ d) ∧ 1 ≤ H ∧
      CoefficientHeightLE f H ∧
      CoefficientHeightLE (homogeneousTranslation ℤ a f) H ∧
      Real.log H ≤
        Real.log |((MonomialOrder.lex.leadingCoeff (homogeneousTranslation ℤ a f) : ℤ) : ℝ)| +
          ((5 * (n : ℝ) + 5) * ((r : ℝ) + 1)) * d * (d : ℝ) ^ (1 / (r : ℝ)) := by
  obtain ⟨a, ha, hne, hc⟩ := exists_hypersurface_leading_coefficient_translation f hf hf0
  let L := |((MonomialOrder.lex.leadingCoeff (homogeneousTranslation ℤ a f) : ℤ) : ℝ)|
  have hL : 1 ≤ L := by dsimp only [L]; exact_mod_cast Int.one_le_abs hne
  have hL0 : 0 < L := by linarith
  have hP := hypersurfacePositionHeightFactor_one_le n d
  refine ⟨a, hypersurfacePositionHeightFactor n d * L, ha,
    one_le_mul_of_one_le_of_one_le hP hL, ?_,
    hypersurfaceTranslation_coefficient_bound f hf hf0 a ha hL0.le hc, ?_⟩
  · intro m
    exact (hc m).trans
      (mul_le_mul_of_nonneg_right (hypersurfacePositionHeightFactor_ge_grid n d) hL0.le)
  · rw [Real.log_mul (by linarith) hL0.ne']
    have hh := hypersurfacePositionHeightFactor_log_le n hr hd
    dsimp only [L]
    linarith

end
end CCDN
