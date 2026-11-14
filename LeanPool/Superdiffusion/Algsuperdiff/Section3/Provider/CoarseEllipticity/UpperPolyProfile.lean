/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.FiniteQProfile

/-!
# UpperPolyProfile

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The polynomial finite-`q` upper profile

This module isolates the deterministic depth arithmetic in the upper half of
ABK26.  After the grid maximum, the ordinary lane has the profile

`A * (n + 1)^2 * 3^(gamma n)`.

For every finite exponent `q >= 2`, its defining weighted `ell^(q/2)`
aggregate is bounded by a dimension-free multiple of

`A * s * (2s - gamma)^(-3)`.

The proof keeps the `ell^(q/2)` aggregate intact.  In particular it does not
use the false uniform estimate `gridSumConst s q <= C * s` at large `q`.
Instead, half of the collar pays the quadratic polynomial, after which the
already-proved exact geometric-profile estimate applies with gap `(2s - gamma)
/ 2`.

This is only model-free profile arithmetic.  It does not manufacture the
per-depth random variables or a joint `Gamma_1` certificate for their
`ell^(q/2)` aggregate.

## Source and provenance

* ABK26, especially the ordinary profile and its cubic pole.
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open HCPolySupport

noncomputable section

/-- The quadratic-times-geometric profile produced by the ordinary upper
per-depth estimate after the grid maximum. -/
def upperPolyProfile (A gamma : ℝ) (n : ℕ) : ℝ :=
  A * (((n : ℝ) + 1) ^ 2) * (3 : ℝ) ^ (gamma * (n : ℝ))

theorem upperPolyProfile_nonneg {A : ℝ} (hA : 0 ≤ A) (gamma : ℝ) (n : ℕ) :
    0 ≤ upperPolyProfile A gamma n :=
  mul_nonneg (mul_nonneg hA (sq_nonneg _)) (Real.rpow_nonneg (by norm_num) _)

/-- Half of a positive collar absorbs the quadratic depth factor.  The
constant is deliberately coarse and dimension-free. -/
theorem natCast_succ_sq_le_inv_sq_mul_three_rpow {rho : ℝ}
    (hrho : 0 < rho) (hrho2 : rho ≤ 2) (n : ℕ) :
    ((n : ℝ) + 1) ^ 2 ≤
      96 * rho⁻¹ ^ 2 * (3 : ℝ) ^ ((rho / 2) * (n : ℝ)) := by
  let N : ℝ := (n : ℝ) + 1
  let x : ℝ := rho * Real.log 3 * N / 4
  have hlog : (1 : ℝ) < Real.log 3 := by
    have h3 : Real.exp 1 < (3 : ℝ) := lt_trans Real.exp_one_lt_d9 (by norm_num)
    exact (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)).2 h3
  have hN : 0 < N := by
    dsimp [N]
    positivity
  have hx : 0 ≤ x := by
    dsimp [x]
    positivity
  have hseries := Real.pow_div_factorial_le_exp x hx 2
  norm_num [Nat.factorial] at hseries
  have hxSq : x ^ 2 ≤ 2 * Real.exp x := by linarith
  have hscaled : rho ^ 2 * N ^ 2 ≤ 32 * Real.exp x := by
    have hlogSq : (1 : ℝ) ≤ (Real.log 3) ^ 2 := by nlinarith
    have hfac : 0 ≤ rho ^ 2 * N ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
    have hbase : rho ^ 2 * N ^ 2 ≤ rho ^ 2 * (Real.log 3) ^ 2 * N ^ 2 := by
      calc
        rho ^ 2 * N ^ 2 = (rho ^ 2 * N ^ 2) * 1 := by ring
        _ ≤ (rho ^ 2 * N ^ 2) * (Real.log 3) ^ 2 :=
          mul_le_mul_of_nonneg_left hlogSq hfac
        _ = rho ^ 2 * (Real.log 3) ^ 2 * N ^ 2 := by ring
    have hxId : x ^ 2 = rho ^ 2 * (Real.log 3) ^ 2 * N ^ 2 / 16 := by
      dsimp [x]
      ring
    rw [hxId] at hxSq
    nlinarith
  have hNexp : N ^ 2 ≤ 32 * rho⁻¹ ^ 2 * Real.exp x := by
    have hrhoNe : rho ≠ 0 := ne_of_gt hrho
    have hmul := mul_le_mul_of_nonneg_left hscaled (sq_nonneg (rho⁻¹))
    have hcancel : rho⁻¹ ^ 2 * (rho ^ 2 * N ^ 2) = N ^ 2 := by
      field_simp
    rw [hcancel] at hmul
    nlinarith
  have hxBound : x ≤ Real.log 3 + (rho / 2) * (n : ℝ) * Real.log 3 := by
    have hn : (0 : ℝ) ≤ n := by positivity
    have hcoeff : rho * ((n : ℝ) + 1) / 4 ≤ 1 + (rho / 2) * (n : ℝ) := by
      nlinarith
    have hlog0 : (0 : ℝ) ≤ Real.log 3 := le_trans zero_le_one hlog.le
    have := mul_le_mul_of_nonneg_right hcoeff hlog0
    dsimp [x, N]
    linarith
  have hexpBound : Real.exp x ≤
      3 * (3 : ℝ) ^ ((rho / 2) * (n : ℝ)) := by
    calc
      Real.exp x ≤ Real.exp
          (Real.log 3 + (rho / 2) * (n : ℝ) * Real.log 3) :=
        Real.exp_le_exp.mpr hxBound
      _ = Real.exp (Real.log 3) *
          Real.exp ((rho / 2) * (n : ℝ) * Real.log 3) := by
        rw [Real.exp_add]
      _ = 3 * (3 : ℝ) ^ ((rho / 2) * (n : ℝ)) := by
        rw [Real.exp_log (by norm_num : (0 : ℝ) < 3),
          Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
        congr 2
        ring
  have hfactor : 0 ≤ 32 * rho⁻¹ ^ 2 := by positivity
  calc
    ((n : ℝ) + 1) ^ 2 = N ^ 2 := rfl
    _ ≤ 32 * rho⁻¹ ^ 2 * Real.exp x := hNexp
    _ ≤ 32 * rho⁻¹ ^ 2 *
        (3 * (3 : ℝ) ^ ((rho / 2) * (n : ℝ))) :=
      mul_le_mul_of_nonneg_left hexpBound hfactor
    _ = 96 * rho⁻¹ ^ 2 *
        (3 : ℝ) ^ ((rho / 2) * (n : ℝ)) := by ring

/-- The quadratic upper profile is pointwise dominated by a pure geometric
profile after spending half of the positive gap. -/
theorem upperPolyProfile_le_finiteQGeometricProfile {A rho : ℝ}
    (hA : 0 ≤ A) (hrho : 0 < rho) (hrho2 : rho ≤ 2)
    (gamma : ℝ) (n : ℕ) :
    upperPolyProfile A gamma n ≤
      finiteQGeometricProfile (96 * A * rho⁻¹ ^ 2) (gamma + rho / 2) n := by
  have hpoly := natCast_succ_sq_le_inv_sq_mul_three_rpow hrho hrho2 n
  have hpow : 0 ≤ (3 : ℝ) ^ (gamma * (n : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hstep := mul_le_mul_of_nonneg_left hpoly hA
  have hstep' := mul_le_mul_of_nonneg_right hstep hpow
  rw [upperPolyProfile, finiteQGeometricProfile]
  calc
    A * (((n : ℝ) + 1) ^ 2) * (3 : ℝ) ^ (gamma * (n : ℝ))
        ≤ (A * (96 * rho⁻¹ ^ 2 *
          (3 : ℝ) ^ ((rho / 2) * (n : ℝ)))) *
            (3 : ℝ) ^ (gamma * (n : ℝ)) := hstep'
    _ = (96 * A * rho⁻¹ ^ 2) *
          (3 : ℝ) ^ ((gamma + rho / 2) * (n : ℝ)) := by
      rw [show (3 : ℝ) ^ ((gamma + rho / 2) * (n : ℝ)) =
          (3 : ℝ) ^ ((rho / 2) * (n : ℝ)) *
            (3 : ℝ) ^ (gamma * (n : ℝ)) by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
        congr 1
        ring]
      ring

/-- The source's quadratic ordinary profile has the printed cubic pole at
every finite exponent `q >= 2`. -/
theorem upperPolyProfile_aggregate_le_of_two_le {A gamma s q : ℝ}
    (hA : 0 ≤ A) (hgamma : 0 ≤ gamma) (hs : 0 < s) (hs1 : s ≤ 1)
    (hq : 2 ≤ q) (hgap : 0 < 2 * s - gamma) :
    ( ∑' n : ℕ, Book.Ch02.geometricWeight s q n *
        upperPolyProfile A gamma n ^ (q / 2)) ^ (2 / q) ≤
      384 * A * s * (2 * s - gamma)⁻¹ ^ 3 := by
  let rho : ℝ := 2 * s - gamma
  let C : ℝ := 96 * A * rho⁻¹ ^ 2
  let gamma' : ℝ := gamma + rho / 2
  have hrho : 0 < rho := by simpa [rho] using hgap
  have hrho2 : rho ≤ 2 := by
    dsimp [rho]
    linarith
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hsq : 0 ≤ s * q := mul_nonneg hs.le hq0.le
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hgamma' : 0 ≤ gamma' := by
    dsimp [gamma']
    positivity
  have hgap' : 0 < 2 * s - gamma' := by
    have hid : 2 * s - gamma' = rho / 2 := by
      dsimp [gamma', rho]
      ring
    rw [hid]
    positivity
  have hprofile : ∀ n : ℕ,
      upperPolyProfile A gamma n ≤ finiteQGeometricProfile C gamma' n := by
    intro n
    simpa [C, gamma'] using
      upperPolyProfile_le_finiteQGeometricProfile hA hrho hrho2 gamma n
  have hleftNonneg : ∀ n : ℕ, 0 ≤
      Book.Ch02.geometricWeight s q n * upperPolyProfile A gamma n ^ (q / 2) :=
    fun n => mul_nonneg (HCPolySupport.geometricWeight_nonneg n hsq)
      (Real.rpow_nonneg (upperPolyProfile_nonneg hA gamma n) _)
  have hrightSum : Summable fun n : ℕ =>
      Book.Ch02.geometricWeight s q n *
        finiteQGeometricProfile C gamma' n ^ (q / 2) :=
    summable_geometricWeight_mul_finiteQGeometricProfile_rpow hC hgap' hq0
  have hterm : ∀ n : ℕ,
      Book.Ch02.geometricWeight s q n * upperPolyProfile A gamma n ^ (q / 2) ≤
        Book.Ch02.geometricWeight s q n *
          finiteQGeometricProfile C gamma' n ^ (q / 2) := by
    intro n
    refine mul_le_mul_of_nonneg_left ?_ (HCPolySupport.geometricWeight_nonneg n hsq)
    exact Real.rpow_le_rpow (upperPolyProfile_nonneg hA gamma n) (hprofile n) (by linarith)
  have hleftSum : Summable fun n : ℕ =>
      Book.Ch02.geometricWeight s q n * upperPolyProfile A gamma n ^ (q / 2) :=
    Summable.of_nonneg_of_le hleftNonneg hterm hrightSum
  have htsum : (∑' n : ℕ, Book.Ch02.geometricWeight s q n *
      upperPolyProfile A gamma n ^ (q / 2)) ≤
      ∑' n : ℕ, Book.Ch02.geometricWeight s q n *
        finiteQGeometricProfile C gamma' n ^ (q / 2) :=
    hleftSum.tsum_le_tsum hterm hrightSum
  have hroot :
      (∑' n : ℕ, Book.Ch02.geometricWeight s q n *
          upperPolyProfile A gamma n ^ (q / 2)) ^ (2 / q) ≤
        (∑' n : ℕ, Book.Ch02.geometricWeight s q n *
          finiteQGeometricProfile C gamma' n ^ (q / 2)) ^ (2 / q) :=
    Real.rpow_le_rpow (tsum_nonneg hleftNonneg) htsum (by positivity)
  have hgeom := finiteQGeometricProfile_aggregate_le_of_two_le
    hC hgamma' hs hq hgap'
  calc
    (∑' n : ℕ, Book.Ch02.geometricWeight s q n *
        upperPolyProfile A gamma n ^ (q / 2)) ^ (2 / q) ≤
      (∑' n : ℕ, Book.Ch02.geometricWeight s q n *
        finiteQGeometricProfile C gamma' n ^ (q / 2)) ^ (2 / q) := hroot
    _ ≤ 2 * C * s * (2 * s - gamma')⁻¹ := hgeom
    _ = 384 * A * s * (2 * s - gamma)⁻¹ ^ 3 := by
      have hrhoNe : rho ≠ 0 := ne_of_gt hrho
      have hgapEq : 2 * s - gamma' = rho / 2 := by
        dsimp [gamma', rho]
        ring
      rw [hgapEq]
      dsimp [C]
      rw [show 2 * s - gamma = rho by rfl]
      field_simp
      ring

end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
