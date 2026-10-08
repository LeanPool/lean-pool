/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Geometry.ProjectiveDistance
public import LeanPool.HighContrastHomogenization.Provider.Transport.WindowTerminalNormalization

/-!
# High-contrast homogenization: Provider.ShortHop.Eccentricity

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The witness eccentricity is the exponential of the projective distance

The hop-index bootstrap `e.global.selection.eccentricity` reads the
identity

`d_pr([I],[μ]) = ½ log(|μ| |μ^{-1}|) = log 𝔢_q`

and turns the prefix bound `d_pr([I],[μ_i]) ≤ i c_hop` into the eccentricity
bound `𝔢_{q_i} ≤ e^{i c_hop}`, hence into a bound on the boundary constant
`B_q = C_d 𝔢_q ζ_g`.

The identity is immediate in the encoding used here.  The projective distance is
half the sum of the logarithms of the two relative sizes, the relative size of a
positive witness against the identity is its spectral size, the relative size of
the identity against it is the spectral size of its inverse, and the witness
eccentricity is the square root of the product of the two.  The square root
halves the logarithm, which is exactly the factor the projective distance
carries.

Nothing in this file mentions a grid: the eccentricity is a function of the
witness alone, as the carrier layer records.
-/

namespace HCPolySupport
namespace HighContrast
namespace ShortHop

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

variable {d : ℕ}

/-! ## The relative size against the identity -/

/-- Measuring a matrix against the identity reads off its spectral size. -/
theorem relSize_one_right (X : Mat d) : relSize X 1 = ‖X‖ := by
  rw [relSize_def, inv_one, Recurrence.matSqrt_one, Matrix.one_mul, Matrix.mul_one]

/-! ## The eccentricity identity -/

/-- **The logarithm of the witness eccentricity is the projective distance to the
identity** (the display of `e.global.selection.eccentricity`). -/
theorem log_witnessEccentricity [NeZero d] {m : Mat d} (hm : m.PosDef) :
    Real.log (witnessEccentricity m) = projDist 1 m := by
  have : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩
  have hL : relSize m 1 = ‖m‖ := relSize_one_right m
  have hA : relSize 1 m = ‖m⁻¹‖ := relSize_one_left hm
  have h1 : (0 : ℝ) < ‖m‖ := norm_pos_iff.mpr hm.isUnit.ne_zero
  have h2 : (0 : ℝ) < ‖m⁻¹‖ := norm_pos_iff.mpr hm.inv.isUnit.ne_zero
  rw [witnessEccentricity, specBound_eq_norm hm.posSemidef,
    specBound_eq_norm hm.inv.posSemidef, Real.log_sqrt (by positivity),
    Real.log_mul h1.ne' h2.ne', projDist_def, hL, hA]
  ring

/-- **The witness eccentricity is the exponential of the projective distance to
the identity.** -/
theorem witnessEccentricity_eq_exp [NeZero d] {m : Mat d} (hm : m.PosDef) :
    witnessEccentricity m = Real.exp (projDist 1 m) := by
  rw [← log_witnessEccentricity hm, Real.exp_log (Transport.zero_lt_witnessEccentricity hm)]

/-- **The prefix bound on the eccentricity.**  A witness within projective
distance `t` of the identity has eccentricity at most `e^t`. -/
theorem witnessEccentricity_le_exp [NeZero d] {m : Mat d} (hm : m.PosDef) {t : ℝ}
    (h : projDist 1 m ≤ t) : witnessEccentricity m ≤ Real.exp t := by
  rw [witnessEccentricity_eq_exp hm]
  exact Real.exp_le_exp.mpr h

/-- **The prefix bound on the boundary constant.**  Since `B_q = C_d 𝔢_q ζ_g`,
the eccentricity bound is a bound on the boundary constant. -/
theorem boundaryConst_le_exp [NeZero d] {Cd g : ℝ} (hCd : 0 ≤ Cd) (hg : g < 1)
    {m : Mat d} (hm : m.PosDef) {t : ℝ} (h : projDist 1 m ≤ t) :
    boundaryConst Cd g m ≤ Cd * Real.exp t * zetaG g := by
  rw [boundaryConst]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (witnessEccentricity_le_exp hm h) hCd)
    (Transport.zero_lt_zetaG hg).le

end

end ShortHop
end HighContrast
end HCPolySupport
