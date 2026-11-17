/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Height.Box
public import LeanPool.CCDN.Height.IntegerCoefficientHeight
public import LeanPool.CCDN.Surface.CongruencePrimeWindow
public import Mathlib.Algebra.MvPolynomial.PDeriv
import LeanPool.CCDN.AuxiliaryPolynomial.PlaneAuxiliaryCount
import LeanPool.CCDN.Determinant.PlaneSingularities
import LeanPool.CCDN.Height.PolynomialBoxHeight

/-! Nonsingular integer points have many smooth reduction primes
in one common finite window. The excluded primes divide one nonzero partial
derivative value, whose height is bounded directly from the equation. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

private theorem integer_pderiv_coefficient_bound {σ : Type*} [Finite σ]
    (f : MvPolynomial σ ℤ) (j : σ) {H : ℝ} (hH : 0 ≤ H)
    (hcoeff : CoefficientHeightLE f H) (e : σ →₀ ℕ) :
    |((pderiv j f).coeff e : ℝ)| ≤ ((f.totalDegree : ℝ) + 1) * H := by
  classical
  let := Fintype.ofFinite σ
  rw [coeff_pderiv]
  by_cases hz : f.coeff (e + Finsupp.single j 1) = 0
  · simp only [hz, zero_mul, Int.cast_zero, abs_zero]
    positivity
  · have he : e j + 1 ≤ f.totalDegree := by
      have h := ((degreeOf_le_iff).mp (degreeOf_le_totalDegree f j))
        (e + Finsupp.single j 1) (mem_support_iff.mpr hz)
      simpa only [Finsupp.add_apply, Finsupp.single_eq_same] using h
    push_cast
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (e j : ℝ) + 1)]
    have heR : (e j : ℝ) + 1 ≤ (f.totalDegree : ℝ) + 1 := by
      exact_mod_cast (by omega : e j + 1 ≤ f.totalDegree + 1)
    calc
      _ ≤ H * ((e j : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right (hcoeff _) (by positivity)
      _ ≤ H * ((f.totalDegree : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left heR hH
      _ = _ := by ring

private theorem integer_pderiv_totalDegree_le {σ : Type*}
    (f : MvPolynomial σ ℤ) (j : σ) :
    (pderiv j f).totalDegree ≤ f.totalDegree := by
  rw [← rational_map_totalDegree (pderiv j f), ← pderiv_map]
  exact (pderiv_totalDegree_le (map (Int.castRingHom ℚ) f) j).trans
    (by rw [rational_map_totalDegree]; omega)

private theorem integer_pderiv_evaluation_bound {n : ℕ}
    (f : MvPolynomial (Fin n) ℤ) (j : Fin n) {H B : ℝ}
    (hH : 0 ≤ H) (hB : 1 ≤ B)
    (hcoeff : CoefficientHeightLE f H)
    (x : IntPoint n) (hx : InBox x B) :
    |(eval x (pderiv j f) : ℝ)| ≤
      ((f.totalDegree : ℝ) + 1) ^ (n + 1) * H * B ^ f.totalDegree := by
  have hb := polynomial_eval₂_box_bound (pderiv j f)
    (((f.totalDegree : ℝ) + 1) * H) B (by positivity) hB
    (integer_pderiv_coefficient_bound f j hH hcoeff)
    (fun i => (x i : ℝ)) hx
  have heval : (eval x (pderiv j f) : ℝ) =
      eval₂ (Int.castRingHom ℝ) (fun i => (x i : ℝ)) (pderiv j f) := by
    simpa only [eval₂_id, RingHom.comp_id, Function.comp_def, Int.coe_castRingHom] using
      eval₂_comp_left (Int.castRingHom ℝ) (RingHom.id ℤ) x (pderiv j f)
  rw [← heval, Fintype.card_fin] at hb
  have hdeg := integer_pderiv_totalDegree_le f j
  have hdegR : ((pderiv j f).totalDegree : ℝ) ≤ f.totalDegree := by exact_mod_cast hdeg
  calc
    _ ≤ (((pderiv j f).totalDegree : ℝ) + 1) ^ n *
        (((f.totalDegree : ℝ) + 1) * H) * B ^ (pderiv j f).totalDegree := hb
    _ ≤ ((f.totalDegree : ℝ) + 1) ^ n *
        (((f.totalDegree : ℝ) + 1) * H) * B ^ f.totalDegree := by
      gcongr
    _ = _ := by rw [pow_succ]; ring

private theorem integer_pderiv_log_bound {n : ℕ}
    (f : MvPolynomial (Fin n) ℤ) (j : Fin n) {H B : ℝ}
    (hH : 1 ≤ H) (hB : 1 ≤ B)
    (hcoeff : CoefficientHeightLE f H)
    (x : IntPoint n) (hx : InBox x B)
    (hne : eval x (pderiv j f) ≠ 0) :
    Real.log |(eval x (pderiv j f) : ℝ)| ≤
      (n + 1 : ℝ) * Real.log ((f.totalDegree : ℝ) + 1) +
        Real.log H + f.totalDegree * Real.log B := by
  have hpos : (0 : ℝ) < |(eval x (pderiv j f) : ℝ)| :=
    abs_pos.mpr (by exact_mod_cast hne)
  have hdpos : (0 : ℝ) < (f.totalDegree : ℝ) + 1 := by positivity
  have hH0 : 0 < H := by linarith
  have hB0 : 0 < B := by linarith
  have hlog := Real.log_le_log hpos
    (integer_pderiv_evaluation_bound f j hH0.le hB hcoeff x hx)
  rw [Real.log_mul (mul_pos (pow_pos hdpos _) hH0).ne' (pow_pos hB0 _).ne',
    Real.log_mul (pow_pos hdpos _).ne' hH0.ne', Real.log_pow, Real.log_pow] at hlog
  simpa only [Nat.cast_add, Nat.cast_one] using hlog

/-- If `x` is an integer point of the box at which some partial derivative of `f` is nonzero,
and `L` dominates the logarithmic size of such a derivative, then the prime window of
logarithmic size `L` contains a set of primes with product at least `exp L` modulo each of
which `x` is a smooth point of `f`. -/
theorem exists_smooth_prime_window_subset {n : ℕ}
    (f : MvPolynomial (Fin n) ℤ) {H B L : ℝ}
    (hH : 1 ≤ H) (hB : 1 ≤ B) (hL : 1 ≤ L)
    (hcoeff : CoefficientHeightLE f H)
    (hheight : (n + 1 : ℝ) * Real.log ((f.totalDegree : ℝ) + 1) +
      Real.log H + f.totalDegree * Real.log B ≤ L)
    (x : IntPoint n) (hx : InBox x B)
    (hsmooth : ∃ j, eval x (pderiv j f) ≠ 0) :
    ∃ P : Finset ℕ, P ⊆ congruencePrimeWindow L ∧
      Real.exp L ≤ ∏ p ∈ P, (p : ℝ) ∧
      ∀ p ∈ P, ∃ j, eval (fun i => (x i : ZMod p))
        (pderiv j (map (Int.castRingHom (ZMod p)) f)) ≠ 0 := by
  classical
  obtain ⟨j, hj⟩ := hsmooth
  let D := eval x (pderiv j f)
  have hD : D ≠ 0 := hj
  have hbound : Real.log |(D : ℝ)| ≤ L :=
    (integer_pderiv_log_bound f j hH hB hcoeff x hx hj).trans hheight
  let P := (congruencePrimeWindow L).filter (fun p : ℕ => ¬ (p : ℤ) ∣ D)
  refine ⟨P, filter_subset _ _, congruencePrimeWindow_avoiding_product hL hD hbound, ?_⟩
  intro p hp
  refine ⟨j, ?_⟩
  have hnd := (mem_filter.mp hp).2
  have he : eval (fun i => (x i : ZMod p))
      (pderiv j (map (Int.castRingHom (ZMod p)) f)) = (D : ZMod p) := by
    rw [pderiv_map]
    exact (map_eval (Int.castRingHom (ZMod p)) x (pderiv j f)).symm
  rw [he]
  exact fun h => hnd ((ZMod.intCast_zmod_eq_zero_iff_dvd D p).mp h)

end
end CCDN
