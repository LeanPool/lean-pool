/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.FiniteQProfile
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.PayloadSandwich

/-!
# FiniteQAggregateBridge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The exact finite-`q` lower aggregate at the cutoff field

This file keeps the lower coarse-ellipticity observable in its defining
weighted `ell^(q/2)` aggregate.  It first lifts
`lambdaSqFinite_inv_eq_rpow` from a Chapter 2 triadic coefficient family to
Chapter 4's totalized coefficient-field carrier.  It then transports the
identity to the Section 3 cutoff observable and moves a nonnegative scalar
normalization inside the aggregate.

The bridge deliberately does not apply
`LambdaGridBridge.tsum_weighted_rpow_root_le`.  Linearizing the whole aggregate
would reintroduce the `q > 2` normalizer loss documented in
`LowerLegProfile.lean`.
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open HCPolySupport
open Algsuperdiff.Section3

noncomputable section

variable {d : ℕ}

/-- Chapter 4's inverse finite-`q` lower ellipticity is exactly the defining
weighted `ell^(q/2)` aggregate.  The non-elliptic branch is included: both
sides are zero there. -/
theorem lambdaSqCoeffField_inv_eq_rpow [NeZero d] (Q : TriadicCube d)
    (a : RegCoeffField d) {s q : ℝ} (hsq : 0 ≤ s * q) (hq : 0 < q) :
    (Book.Ch04.lambdaSqCoeffField Q s (.finite q) a)⁻¹ =
      (∑' n : ℕ, Book.Ch02.geometricWeight s q n *
        Book.Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale Q
            (Q.scale - (n : ℤ)) a ^ (q / 2)) ^ (2 / q) := by
  classical
  by_cases ha : Book.Ch04.AELocallyUniformlyEllipticField a
  · simp only [Book.Ch04.lambdaSqCoeffField,
      Book.Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale, ha, dite_eq_left]
    exact lambdaSqFinite_inv_eq_rpow Q hsq
      (Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)
  · simp [Book.Ch04.lambdaSqCoeffField,
      Book.Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale, ha,
      Real.zero_rpow (by positivity : q / 2 ≠ 0),
      Real.zero_rpow (by positivity : 2 / q ≠ 0)]

/-- The exported cutoff lower observable, multiplied by a nonnegative scalar,
is the same scalar moved inside every depth of its defining finite-`q`
aggregate.  This is the exact carrier needed to split deterministic and random
profiles before taking the `2/q` root. -/
theorem cutoffLowerEllipticityInv_mul_eq_rpow [NeZero d] (M : ABKModel d)
    (m L : ℤ) {s r : ℝ} (hs : 0 < s) {q : CoarseEllipticityExponent}
    (hqval : q.1 = Book.Ch02.MultiscaleExponent.finite r) (hr : 0 < r)
    {scaling : ℝ} (hscaling : 0 ≤ scaling) (omega : Cutoff.CutoffSample d) :
    Observable.cutoffLowerEllipticityInv M m L s hs q omega * scaling =
      (∑' n : ℕ, Book.Ch02.geometricWeight s r n *
        (scaling *
          Book.Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
            (originCube d m) (m - (n : ℤ))
            (Cutoff.coefficientCutoff M.nu L omega)) ^ (r / 2)) ^ (2 / r) := by
  let a : RegCoeffField d := Cutoff.coefficientCutoff M.nu L omega
  let H : ℕ → ℝ := fun n =>
    Book.Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
      (originCube d m) (m - (n : ℤ)) a
  have hscale : (originCube d m).scale = m := rfl
  have hsr : 0 ≤ s * r := (mul_pos hs hr).le
  have hH : ∀ n, 0 ≤ H n := by
    intro n
    exact Book.Ch05.Section52.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale_nonneg_of_le
      (originCube d m) a (by rw [hscale]; omega)
  have hS : 0 ≤ ∑' n : ℕ,
      Book.Ch02.geometricWeight s r n * H n ^ (r / 2) :=
    tsum_nonneg fun n => mul_nonneg (geometricWeight_nonneg' hsr n)
      (Real.rpow_nonneg (hH n) _)
  have hseries :
      (∑' n : ℕ, Book.Ch02.geometricWeight s r n *
          (scaling * H n) ^ (r / 2)) =
        scaling ^ (r / 2) *
          ∑' n : ℕ, Book.Ch02.geometricWeight s r n * H n ^ (r / 2) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    rw [Real.mul_rpow hscaling (hH n)]
    ring
  have hcancel : r / 2 * (2 / r) = 1 := by
    field_simp
  rw [congrFun (Observable.cutoffLowerEllipticityInv_eq_literal M m L s hs q) omega,
    cutoffLowerEllipticityInvLiteral_eq_coeffField, hqval,
    lambdaSqCoeffField_inv_eq_rpow (originCube d m) a hsr hr]
  change
    (∑' n : ℕ, Book.Ch02.geometricWeight s r n * H n ^ (r / 2)) ^ (2 / r) *
        scaling =
      (∑' n : ℕ, Book.Ch02.geometricWeight s r n *
        (scaling * H n) ^ (r / 2)) ^ (2 / r)
  rw [hseries, Real.mul_rpow (Real.rpow_nonneg hscaling _) hS,
    ← Real.rpow_mul hscaling, hcancel, Real.rpow_one]
  ring

end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
