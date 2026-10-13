/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.HomogenizationError.ResponseBounds

/-!
# Monotonicity

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: monotonicity of the multiscale homogenization error

This file proves a local version of the display `e.mathcalE.monotone.ordered` of
ABK26:

> For every `m ∈ ℤ`, `p, q ∈ [1,∞]` and `t, s ∈ (0,∞)` with `t < s`, >
`max_{|e| = 1} J(□_m, A₀^{-1/2} e, A₀^{1/2} e; a)^{1/2} >  ≤ 𝓔_{s,p,q}(□_m; a,
a₀) ≤ 𝓔_{t,p,q}(□_m; a, a₀)`.

The carrier is CoarseGraining's
`Homogenization.Book.Ch02.HomogenizationErrorOnCube`, whose one-cube response
`max_{|e| = 1} J(□_m, A₀^{-1/2} e, A₀^{1/2} e; a)` is
`Homogenization.Book.Ch02.normalizedBlockResponseMax`.

## Scope

Both inequalities are proved here at the endpoint `p = ∞`, for every admissible
`q`, i.e. for `q ∈ [1,∞)` (`MultiscaleExponent.finite q`) and for `q = ∞`
(`MultiscaleExponent.infinity`).  CoarseGraining previously had only the
special case `(p, q) = (∞, 1)`
(`Homogenization.Book.Ch02.homogenizationErrorOnCube_infinity_one_le_of_lt` and
`Homogenization.Book.Ch02.scaleResponseAtScale_infinity_self_le_homogenizationErrorOnCube_infinity_one`).

## Main results

* `rpow_half_normalizedBlockResponseMax_le_homogenizationErrorOnCube_infinity_finite`:
  the first inequality of the display.
* `homogenizationErrorOnCube_infinity_finite_le_of_lt`: the second inequality
  of the display, i.e. antitonicity in the smoothness exponent `s`.

## References

* ABK26, `e.mathcalE.monotone.ordered`.
-/

namespace Algsuperdiff.Section3.Provider.ErrorComparison

open HCPolySupport

/-! ## The `p = ∞` scale response along the descending scales of a cube -/

/-- Nonnegativity of the `p = ∞` scale response at depth `l` below `Q`. -/
theorem scaleResponse_depth_nonneg {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (F : Book.Ch02.TriadicCoeffFamily d) (a0 : Mat d) (l : ℕ) :
    0 ≤ Book.Ch02.scaleResponseAtScale Q (Q.scale - (l : ℤ)) .infinity F a0 :=
  Book.Ch02.scaleResponseAtScale_infinity_nonneg Q
    (sub_le_self Q.scale (by exact_mod_cast Nat.zero_le l)) F a0

/-- The `p = ∞` scale response at depth `l` below `Q` is bounded by the uniform
deterministic bound of the root cube. -/
theorem scaleResponse_depth_le_uniform {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (F : Book.Ch02.TriadicCoeffFamily d) (a0 : Mat d)
    (l : ℕ) :
    Book.Ch02.scaleResponseAtScale Q (Q.scale - (l : ℤ)) .infinity F a0 ≤
      Real.rpow (Book.Ch02.normalizedBlockResponseUniformBound Q F a0)
        (1 / 2 : ℝ) :=
  Book.Ch02.scaleResponseAtScale_infinity_le_uniform Q
    (sub_le_self Q.scale (by exact_mod_cast Nat.zero_le l)) F a0

/-- The `p = ∞` scale response increases as one descends the scales of `Q`. -/
theorem scaleResponse_depth_monotone {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (F : Book.Ch02.TriadicCoeffFamily d) (a0 : Mat d) :
    Monotone fun l : ℕ =>
      Book.Ch02.scaleResponseAtScale Q (Q.scale - (l : ℤ)) .infinity F a0 := by
  intro m n hmn
  have hmnz : (m : ℤ) ≤ (n : ℤ) := by exact_mod_cast hmn
  have hkl : Q.scale - (n : ℤ) ≤ Q.scale - (m : ℤ) := by linarith
  have hlQ : Q.scale - (m : ℤ) ≤ Q.scale :=
    sub_le_self Q.scale (by exact_mod_cast Nat.zero_le m)
  exact Book.Ch02.scaleResponseAtScale_infinity_le_of_le
    (Q := Q) (k := Q.scale - (n : ℤ)) (l := Q.scale - (m : ℤ)) hkl hlQ F a0

/-- The `q`-th power of the `p = ∞` scale response increases as one descends the
scales of `Q`. -/
theorem scaleResponse_depth_rpow_monotone {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (F : Book.Ch02.TriadicCoeffFamily d) (a0 : Mat d)
    {q : ℝ} (hq : 0 ≤ q) :
    Monotone fun l : ℕ =>
      Real.rpow
        (Book.Ch02.scaleResponseAtScale Q (Q.scale - (l : ℤ)) .infinity F a0) q := by
  intro m n hmn
  exact Real.rpow_le_rpow (scaleResponse_depth_nonneg Q F a0 m)
    (scaleResponse_depth_monotone Q F a0 hmn) hq

/-- Summability of the geometrically weighted `q`-th powers of the `p = ∞` scale
responses. -/
theorem summable_geometricWeight_mul_scaleResponse_rpow {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (F : Book.Ch02.TriadicCoeffFamily d) (a0 : Mat d)
    {s q : ℝ} (hs : 0 < s) (hq : 0 < q) :
    Summable fun l : ℕ =>
      Book.Ch02.geometricWeight s q l *
        Real.rpow
          (Book.Ch02.scaleResponseAtScale Q (Q.scale - (l : ℤ)) .infinity F a0)
          q := by
  have hold :
      Summable fun l : ℕ =>
        HCPolySupport.geometricWeight s q l *
          Real.rpow
            (Book.Ch02.scaleResponseAtScale Q (Q.scale - (l : ℤ)) .infinity F a0)
            q := by
    refine HCPolySupport.summable_geometricWeight_mul_of_nonneg_of_le
      (s := s) (q := q)
      (C := Real.rpow
        (Real.rpow (Book.Ch02.normalizedBlockResponseUniformBound Q F a0)
          (1 / 2 : ℝ)) q)
      (mul_pos hs hq) (fun l => Real.rpow_nonneg
        (scaleResponse_depth_nonneg Q F a0 l) q) (fun l => ?_)
    exact Real.rpow_le_rpow (scaleResponse_depth_nonneg Q F a0 l)
      (scaleResponse_depth_le_uniform Q F a0 l) hq.le
  simpa [Book.Ch02.geometricWeight_eq_old] using hold

/-- The finite-`q`, `p = ∞` homogenization error of a cube, written out as the
`1/q`-th power of a geometrically weighted sum. -/
theorem homogenizationErrorOnCube_infinity_finite_eq_rpow_tsum {d : ℕ}
    [NeZero d] (Q : TriadicCube d) (F : Book.Ch02.TriadicCoeffFamily d)
    (a0 : Mat d) (s q : ℝ) :
    Book.Ch02.HomogenizationErrorOnCube Q s .infinity (.finite q) F a0 =
      Real.rpow
        (∑' l : ℕ,
          Book.Ch02.geometricWeight s q l *
            Real.rpow
              (Book.Ch02.scaleResponseAtScale Q (Q.scale - (l : ℤ)) .infinity F a0)
              q)
        (1 / q) :=
  rfl

/-! ## The first inequality of `e.mathcalE.monotone.ordered` -/

/-- First inequality of `e.mathcalE.monotone.ordered` (ABK26) at `p = ∞` and
finite `q`: the square root of the one-cube normalized block response of `Q` is
bounded by `𝓔_{s,∞,q}(Q; a, a₀)`. -/
theorem rpow_half_normalizedBlockResponseMax_le_homogenizationErrorOnCube_infinity_finite
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (F : Book.Ch02.TriadicCoeffFamily d)
    (a0 : Mat d) {s q : ℝ} (hs : 0 < s) (hq : 1 ≤ q) :
    Real.rpow (Book.Ch02.normalizedBlockResponseMax Q F a0) (1 / 2 : ℝ) ≤
      Book.Ch02.HomogenizationErrorOnCube Q s .infinity (.finite q) F a0 := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hzero :
      Real.rpow
        (Book.Ch02.scaleResponseAtScale Q (Q.scale - ((0 : ℕ) : ℤ)) .infinity F a0)
        q ≤
      ∑' l : ℕ,
        Book.Ch02.geometricWeight s q l *
          Real.rpow
            (Book.Ch02.scaleResponseAtScale Q (Q.scale - (l : ℤ)) .infinity F a0)
            q := by
    have hold :=
      HCPolySupport.self_le_tsum_geometricWeight_of_monotone
        (H := fun l : ℕ =>
          Real.rpow
            (Book.Ch02.scaleResponseAtScale Q (Q.scale - (l : ℤ)) .infinity F a0)
            q)
        (s := s) (q := q)
        (scaleResponse_depth_rpow_monotone Q F a0 hq0.le) (mul_pos hs hq0)
        (by
          simpa [Book.Ch02.geometricWeight_eq_old] using
            summable_geometricWeight_mul_scaleResponse_rpow Q F a0 hs hq0)
    simpa [Book.Ch02.geometricWeight_eq_old] using hold
  have hbase :
      Book.Ch02.scaleResponseAtScale Q (Q.scale - ((0 : ℕ) : ℤ)) .infinity F a0 =
        Real.rpow (Book.Ch02.normalizedBlockResponseMax Q F a0) (1 / 2 : ℝ) := by
    simp
  have hnonneg :
      0 ≤ Real.rpow (Book.Ch02.normalizedBlockResponseMax Q F a0) (1 / 2 : ℝ) := by
    rw [← hbase]
    exact scaleResponse_depth_nonneg Q F a0 0
  rw [homogenizationErrorOnCube_infinity_finite_eq_rpow_tsum]
  have hstep :
      Real.rpow
          (Real.rpow
            (Real.rpow (Book.Ch02.normalizedBlockResponseMax Q F a0) (1 / 2 : ℝ))
            q)
          (1 / q) ≤
        Real.rpow
          (∑' l : ℕ,
            Book.Ch02.geometricWeight s q l *
              Real.rpow
                (Book.Ch02.scaleResponseAtScale Q (Q.scale - (l : ℤ)) .infinity F a0)
                q)
          (1 / q) := by
    refine Real.rpow_le_rpow (Real.rpow_nonneg hnonneg q) ?_ (by positivity)
    rw [← hbase]
    exact hzero
  have hcollapse :
      Real.rpow
          (Real.rpow
            (Real.rpow (Book.Ch02.normalizedBlockResponseMax Q F a0) (1 / 2 : ℝ))
            q)
          (1 / q) =
        Real.rpow (Book.Ch02.normalizedBlockResponseMax Q F a0) (1 / 2 : ℝ) := by
    have hqq : q * (1 / q) = 1 := by field_simp
    have hmul := Real.rpow_mul hnonneg q (1 / q)
    rw [hqq, Real.rpow_one] at hmul
    exact hmul.symm
  rw [hcollapse] at hstep
  exact hstep

/-! ## The second inequality of `e.mathcalE.monotone.ordered` -/

/-- Second inequality of `e.mathcalE.monotone.ordered` (ABK26) at `p
= ∞` and finite `q`: `𝓔_{s,∞,q}` is antitone in the smoothness
exponent. -/
theorem homogenizationErrorOnCube_infinity_finite_le_of_lt {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (F : Book.Ch02.TriadicCoeffFamily d) (a0 : Mat d)
    {t s q : ℝ} (ht : 0 < t) (hts : t < s) (hq : 1 ≤ q) :
    Book.Ch02.HomogenizationErrorOnCube Q s .infinity (.finite q) F a0 ≤
      Book.Ch02.HomogenizationErrorOnCube Q t .infinity (.finite q) F a0 := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hs : 0 < s := lt_trans ht hts
  have htsum :
      (∑' l : ℕ,
          Book.Ch02.geometricWeight s q l *
            Real.rpow
              (Book.Ch02.scaleResponseAtScale Q (Q.scale - (l : ℤ)) .infinity F a0)
              q) ≤
        ∑' l : ℕ,
          Book.Ch02.geometricWeight t q l *
            Real.rpow
              (Book.Ch02.scaleResponseAtScale Q (Q.scale - (l : ℤ)) .infinity F a0)
              q := by
    have hold :=
      HCPolySupport.tsum_geometricWeight_le_of_monotone
        (H := fun l : ℕ =>
          Real.rpow
            (Book.Ch02.scaleResponseAtScale Q (Q.scale - (l : ℤ)) .infinity F a0)
            q)
        (scaleResponse_depth_rpow_monotone Q F a0 hq0.le)
        (fun l => Real.rpow_nonneg (scaleResponse_depth_nonneg Q F a0 l) q)
        hq0 ht hts
        (by
          simpa [Book.Ch02.geometricWeight_eq_old] using
            summable_geometricWeight_mul_scaleResponse_rpow Q F a0 ht hq0)
    simpa [Book.Ch02.geometricWeight_eq_old] using hold
  have hnonneg :
      0 ≤
        ∑' l : ℕ,
          Book.Ch02.geometricWeight s q l *
            Real.rpow
              (Book.Ch02.scaleResponseAtScale Q (Q.scale - (l : ℤ)) .infinity F a0)
              q := by
    refine tsum_nonneg fun l => mul_nonneg ?_ ?_
    · simpa [Book.Ch02.geometricWeight_eq_old] using
        HCPolySupport.geometricWeight_nonneg (s := s) (q := q) l
          (mul_pos hs hq0).le
    · exact Real.rpow_nonneg (scaleResponse_depth_nonneg Q F a0 l) q
  rw [homogenizationErrorOnCube_infinity_finite_eq_rpow_tsum,
    homogenizationErrorOnCube_infinity_finite_eq_rpow_tsum]
  exact Real.rpow_le_rpow hnonneg htsum (by positivity)

end Algsuperdiff.Section3.Provider.ErrorComparison
