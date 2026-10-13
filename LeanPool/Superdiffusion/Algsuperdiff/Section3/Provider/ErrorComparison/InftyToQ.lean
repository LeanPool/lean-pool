/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.HomogenizationError.ResponseBounds

/-!
# InftyToQ

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: bounding the `p = ∞` error by the finite-`p` error

This file proves a local version of the display `e.mathcalE.infty.to.q` of
ABK26: for every `p, q ∈ [1,∞]` and `s ∈ (d/p, 1)`,

> `𝓔_{s,∞,q}(□_m, n; a, a₀)
>    ≤ 3^{(d/p)(m-n)} (c_{sq} / c_{q(s - d/p)})^{1/q}
>        𝓔_{s - d/p, p, q}(□_m, n; a, a₀)`,

where `c_{sq} = 1 - 3^{-sq}` is `Homogenization.Book.Ch02.geometricDiscount s q`.

## Scope

The proof printed in the source is the finite-`q` computation; the endpoint `q =
∞` is obtained there by sending `q → ∞`.  Accordingly this file proves the
finite-`p`, finite-`q` case, which is the case carrying the printed constant.
The exponent restriction `s ∈ (d/p, 1)` of the display is kept verbatim as the
pair of hypotheses `(d : ℝ) / p < s` and `s < 1`; only the lower restriction is
used in the proof, and the upper restriction `s < 1` is retained (with the
Mathlib underscore name `_hs1` for an unused hypothesis) because the source
states the display only in that range.

The truncation parameter `n` of `𝓔_{s,p,q}(□_m, n; ·)` is carried explicitly, so
the geometric prefactor `3^{(d/p)(m-n)}` appears exactly as printed; `n ≤ m` is
required, as in the source, where the sum defining `𝓔` runs over scales `l ≤ n`
inside `□_m`.

## Main results

* `scaleResponseAtScale_infinity_rpow_le_card_mul_finite`: the one-scale
  Hölder/counting step `max_z ≤ (∑_z)^{...}` of the printed proof.
* `homogenizationError_infinity_le_finite`: the display.

## References

* ABK26 (`e.mathcalE.infty.to.q` and its proof).
-/

namespace Algsuperdiff.Section3.Provider.ErrorComparison

open HCPolySupport

/-! ## Real-power bookkeeping -/

/-- `Real.mul_rpow`, restated with explicit `Real.rpow` applications so that it is
usable by `rw` against CoarseGraining's `Real.rpow` spelling. -/
theorem mul_rpow' {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (z : ℝ) :
    Real.rpow (x * y) z = Real.rpow x z * Real.rpow y z :=
  Real.mul_rpow hx hy

/-- `Real.rpow_natCast`, restated with an explicit `Real.rpow` application. -/
theorem rpow_natCast' (x : ℝ) (m : ℕ) : Real.rpow x (m : ℝ) = x ^ m :=
  Real.rpow_natCast x m

/-- Iterated real powers of a nonnegative base multiply their exponents. -/
theorem rpow_rpow {x : ℝ} (hx : 0 ≤ x) (y z : ℝ) :
    Real.rpow (Real.rpow x y) z = Real.rpow x (y * z) :=
  (Real.rpow_mul hx y z).symm

/-- Iterated real powers with reciprocal exponents cancel. -/
theorem rpow_rpow_of_mul_eq_one {x y z : ℝ} (hx : 0 ≤ x) (hyz : y * z = 1) :
    Real.rpow (Real.rpow x y) z = x := by
  rw [rpow_rpow hx, hyz]
  exact Real.rpow_one x

/-! ## Averages over a finite set -/

/-- A `finsetAverageReal` of nonnegative values is nonnegative. -/
theorem finsetAverageReal_nonneg {α : Type*} (s : Finset α) {f : α → ℝ}
    (hf : ∀ x ∈ s, 0 ≤ f x) : 0 ≤ Book.Ch02.finsetAverageReal s f := by
  unfold Book.Ch02.finsetAverageReal
  exact mul_nonneg (by positivity) (Finset.sum_nonneg hf)

/-- A `finsetAverageReal` is bounded by any nonnegative pointwise bound. -/
theorem finsetAverageReal_le {α : Type*} (s : Finset α) {f : α → ℝ} {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ x ∈ s, f x ≤ C) :
    Book.Ch02.finsetAverageReal s f ≤ C := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simpa [Book.Ch02.finsetAverageReal] using hC0
  · have hcard : (0 : ℝ) < (s.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hs
    have hsum : s.sum f ≤ (s.card : ℝ) * C := by
      calc
        s.sum f ≤ ∑ _x ∈ s, C := Finset.sum_le_sum hC
        _ = (s.card : ℝ) * C := by simp [Finset.sum_const, nsmul_eq_mul]
    unfold Book.Ch02.finsetAverageReal
    exact (inv_mul_le_iff₀ hcard).mpr hsum

/-! ## The finite-`p` one-scale response -/

/-- Definitional form of the finite-`p` one-scale response. -/
theorem scaleResponseAtScale_finite_eq {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (k : ℤ) (p : ℝ) (F : Book.Ch02.TriadicCoeffFamily d) (a0 : Mat d) :
    Book.Ch02.scaleResponseAtScale Q k (.finite p) F a0 =
      Real.rpow
        (Book.Ch02.finsetAverageReal (descendantsAtScale Q k)
          (fun R => Real.rpow (Book.Ch02.normalizedBlockResponseMax R F a0) (p / 2)))
        (1 / p) :=
  rfl

/-- The average appearing in the finite-`p` one-scale response is nonnegative. -/
theorem finsetAverage_normalizedBlockResponseMax_rpow_nonneg {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (k : ℤ) (F : Book.Ch02.TriadicCoeffFamily d)
    (a0 : Mat d) (p : ℝ) :
    0 ≤
      Book.Ch02.finsetAverageReal (descendantsAtScale Q k)
        (fun R => Real.rpow (Book.Ch02.normalizedBlockResponseMax R F a0) (p / 2)) :=
  finsetAverageReal_nonneg _ fun R _ =>
    Real.rpow_nonneg (Book.Ch02.normalizedBlockResponseMax_nonneg R F a0) _

/-! ## The one-scale counting step -/

/-- The one-scale step of the printed proof of `e.mathcalE.infty.to.q`: the
maximum over the descendants at one scale is bounded by the `p`-average over the
same scale, at the cost of the number of descendants. -/
theorem scaleResponseAtScale_infinity_rpow_le_card_mul_finite {d : ℕ} [NeZero d]
    (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale)
    (F : Book.Ch02.TriadicCoeffFamily d) (a0 : Mat d) {p q : ℝ}
    (hp : 0 < p) (hq : 0 < q) :
    Real.rpow (Book.Ch02.scaleResponseAtScale Q k .infinity F a0) q ≤
      Real.rpow ((descendantsAtScale Q k).card : ℝ) (q / p) *
        Real.rpow (Book.Ch02.scaleResponseAtScale Q k (.finite p) F a0) q := by
  classical
  have hDne : (descendantsAtScale Q k).Nonempty := descendantsAtScale_nonempty Q hk
  have hcard : (0 : ℝ) < ((descendantsAtScale Q k).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hDne
  set A : ℝ :=
    Book.Ch02.finsetAverageReal (descendantsAtScale Q k)
      (fun R => Real.rpow (Book.Ch02.normalizedBlockResponseMax R F a0) (p / 2))
    with hAdef
  have hA_nonneg : 0 ≤ A := by
    rw [hAdef]
    exact finsetAverage_normalizedBlockResponseMax_rpow_nonneg Q k F a0 p
  set S : ℝ :=
    ∑ R ∈ descendantsAtScale Q k,
      Real.rpow (Book.Ch02.normalizedBlockResponseMax R F a0) (p / 2) with hSdef
  have hS_nonneg : 0 ≤ S := by
    rw [hSdef]
    exact Finset.sum_nonneg fun R _ =>
      Real.rpow_nonneg (Book.Ch02.normalizedBlockResponseMax_nonneg R F a0) _
  have hSA : S = ((descendantsAtScale Q k).card : ℝ) * A := by
    rw [hAdef, hSdef, Book.Ch02.finsetAverageReal]
    field_simp
  have hM :
      Book.Ch02.maxDescendantNormalizedBlockResponseAtScale Q k F a0 ≤
        Real.rpow S (2 / p) := by
    refine Book.Ch02.finsetSupReal_le (descendantsAtScale Q k) hDne ?_
    intro R hR
    have hle :
        Real.rpow (Book.Ch02.normalizedBlockResponseMax R F a0) (p / 2) ≤ S := by
      rw [hSdef]
      exact Finset.single_le_sum
        (f := fun R' =>
          Real.rpow (Book.Ch02.normalizedBlockResponseMax R' F a0) (p / 2))
        (fun R' _ =>
          Real.rpow_nonneg (Book.Ch02.normalizedBlockResponseMax_nonneg R' F a0) _)
        hR
    have hstep :
        Real.rpow
            (Real.rpow (Book.Ch02.normalizedBlockResponseMax R F a0) (p / 2))
            (2 / p) ≤ Real.rpow S (2 / p) :=
      Real.rpow_le_rpow
        (Real.rpow_nonneg (Book.Ch02.normalizedBlockResponseMax_nonneg R F a0) _)
        hle (by positivity)
    have hcancel :
        Real.rpow
            (Real.rpow (Book.Ch02.normalizedBlockResponseMax R F a0) (p / 2))
            (2 / p) = Book.Ch02.normalizedBlockResponseMax R F a0 := by
      refine rpow_rpow_of_mul_eq_one
        (Book.Ch02.normalizedBlockResponseMax_nonneg R F a0) ?_
      field_simp
    rw [hcancel] at hstep
    exact hstep
  have hMnonneg :
      0 ≤ Book.Ch02.maxDescendantNormalizedBlockResponseAtScale Q k F a0 :=
    Book.Ch02.maxDescendantNormalizedBlockResponseAtScale_nonneg Q hk F a0
  have hleft :
      Real.rpow (Book.Ch02.scaleResponseAtScale Q k .infinity F a0) q =
        Real.rpow
          (Book.Ch02.maxDescendantNormalizedBlockResponseAtScale Q k F a0)
          (q / 2) := by
    rw [Book.Ch02.scaleResponseAtScale_infinity_eq, rpow_rpow hMnonneg]
    congr 1
    ring
  have hright :
      Real.rpow (Book.Ch02.scaleResponseAtScale Q k (.finite p) F a0) q =
        Real.rpow A (q / p) := by
    rw [scaleResponseAtScale_finite_eq, ← hAdef, rpow_rpow hA_nonneg]
    congr 1
    ring
  have hchain :
      Real.rpow
          (Book.Ch02.maxDescendantNormalizedBlockResponseAtScale Q k F a0)
          (q / 2) ≤ Real.rpow S (q / p) := by
    have hstep :
        Real.rpow
            (Book.Ch02.maxDescendantNormalizedBlockResponseAtScale Q k F a0)
            (q / 2) ≤ Real.rpow (Real.rpow S (2 / p)) (q / 2) :=
      Real.rpow_le_rpow hMnonneg hM (by positivity)
    have hcollapse :
        Real.rpow (Real.rpow S (2 / p)) (q / 2) = Real.rpow S (q / p) := by
      rw [rpow_rpow hS_nonneg]
      congr 1
      field_simp
    rw [hcollapse] at hstep
    exact hstep
  have hsplit :
      Real.rpow S (q / p) =
        Real.rpow ((descendantsAtScale Q k).card : ℝ) (q / p) *
          Real.rpow A (q / p) := by
    rw [hSA]
    exact Real.mul_rpow hcard.le hA_nonneg
  rw [hleft, hright]
  calc
    Real.rpow (Book.Ch02.maxDescendantNormalizedBlockResponseAtScale Q k F a0)
        (q / 2) ≤ Real.rpow S (q / p) := hchain
    _ = Real.rpow ((descendantsAtScale Q k).card : ℝ) (q / p) *
        Real.rpow A (q / p) := hsplit

/-! ## Counting the descendants of a cube -/

/-- The number of descendants at a given depth, as a real power of `3`. -/
theorem card_descendantsAtScale_eq_rpow {d : ℕ} (Q : TriadicCube d) {k : ℤ}
    (hk : k ≤ Q.scale) :
    ((descendantsAtScale Q k).card : ℝ) =
      Real.rpow (3 : ℝ) ((d : ℝ) * ((Int.toNat (Q.scale - k) : ℕ) : ℝ)) := by
  rw [descendantsAtScale_eq_descendantsAtDepth Q hk, descendantsAtDepth_card]
  have hcast :
      (d : ℝ) * ((Int.toNat (Q.scale - k) : ℕ) : ℝ) =
        ((d * Int.toNat (Q.scale - k) : ℕ) : ℝ) := by
    push_cast
    ring
  rw [hcast, rpow_natCast']
  push_cast
  rw [pow_mul]

/-! ## The display -/

/-- Definitional form of the finite-`q` homogenization error with truncation
scale `n`. -/
theorem homogenizationError_finite_eq_rpow_tsum {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (n : ℤ) (s : ℝ) (P : Book.Ch02.MultiscaleExponent)
    (q : ℝ) (F : Book.Ch02.TriadicCoeffFamily d) (a0 : Mat d) :
    Book.Ch02.HomogenizationError Q n s P (.finite q) F a0 =
      Real.rpow
        (∑' l : ℕ,
          Book.Ch02.geometricWeight s q l *
            Real.rpow (Book.Ch02.scaleResponseAtScale Q (n - (l : ℤ)) P F a0) q)
        (1 / q) :=
  rfl

end Algsuperdiff.Section3.Provider.ErrorComparison
