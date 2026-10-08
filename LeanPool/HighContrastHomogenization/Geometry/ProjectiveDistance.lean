/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Geometry.RelativeSize
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# High-contrast homogenization: Geometry.ProjectiveDistance

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The projective distance between positive matrices

The reference text defines, for positive `m₀, m₁`,

    d_pr([m₀],[m₁]) = ½ (log λ_max(m₀^{-1/2} m₁ m₀^{-1/2})
                          - log λ_min(m₀^{-1/2} m₁ m₀^{-1/2})),

which is `e.scale.selection.projective.distance`.  Writing `X := m₀^{-1/2} m₁ m₀^{-1/2}`,
which is positive definite, the two eigenvalues are read off by the relative
size of `HCPoly.Geometry.RelativeSize`:

* `relSize m₁ m₀ = ‖X‖ = λ_max(X)` holds by the definition of `relSize`;
* `relSize m₀ m₁ = ‖X⁻¹‖ = λ_min(X)⁻¹`, which is
  `relSize_eq_norm_normalize_inv`.

Because `log (λ_min(X)) = - log (‖X⁻¹‖)`, the printed *difference* of
logarithms is the *sum* used here as the definition:

    projDist m₀ m₁ = ½ (log (relSize m₁ m₀) + log (relSize m₀ m₁)).

This encoding never names an eigenvalue and never inverts a matrix, so the
symmetry `projDist_comm`, the scale invariance `projDist_smul_left` and
`projDist_smul_right` — the invariances that make the bracket notation `[m]`
legitimate — and the triangle inequality all reduce to the least-scalar-bound
characterization `relSize_le_iff`.

The workhorse for the canonical-geometry estimates is `projDist_le_of_le`: a
two-sided Loewner sandwich `a m₀ ≤ m₁ ≤ b m₀` bounds the distance by
`½ log (b/a)`.  The triangle inequality is exactly that bound applied to the
composition of two sandwiches with the sharp constants.

Statements whose truth needs `‖(1 : Matrix n n ℝ)‖ = 1` carry a `Nonempty`
instance on the index type; on an empty index type every relative size vanishes
and the definition degenerates.
-/

namespace HCPolySupport
namespace HighContrast

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Logarithm arithmetic

The logarithm is kept opaque: these helpers speak only about abstract positive
reals, and no later proof lets a linear-arithmetic step see `Real.log` applied
to a matrix expression. -/

private theorem log_mul_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.log (x * y) = Real.log x + Real.log y :=
  Real.log_mul hx.ne' hy.ne'

private theorem log_div_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.log (x / y) = Real.log x - Real.log y := by
  rw [div_eq_mul_inv, log_mul_pos hx (inv_pos.mpr hy), Real.log_inv]
  ring

private theorem log_inv_mul_add_log_mul {c x y : ℝ} (hc : 0 < c) (hx : 0 < x) (hy : 0 < y) :
    Real.log (c⁻¹ * x) + Real.log (c * y) = Real.log x + Real.log y := by
  rw [log_mul_pos (inv_pos.mpr hc) hx, log_mul_pos hc hy, Real.log_inv]
  ring

private theorem log_four_split {p q r s : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hs : 0 < s) :
    Real.log (p * q * (r * s)) = Real.log p + Real.log r + (Real.log q + Real.log s) := by
  rw [log_mul_pos (mul_pos hp hq) (mul_pos hr hs), log_mul_pos hp hq, log_mul_pos hr hs]
  ring

/-! ## The distance -/

/-- The projective distance of `e.scale.selection.projective.distance`, encoded through the
relative sizes of the pair in both directions. -/
@[expose]
def projDist (m₀ m₁ : Matrix n n ℝ) : ℝ :=
  (1 / 2) * (Real.log (relSize m₁ m₀) + Real.log (relSize m₀ m₁))

theorem projDist_def (m₀ m₁ : Matrix n n ℝ) :
    projDist m₀ m₁ = (1 / 2) * (Real.log (relSize m₁ m₀) + Real.log (relSize m₀ m₁)) := rfl

/-- **The printed form.**  With `X = m₀^{-1/2} m₁ m₀^{-1/2}` the definition is
the reference text's difference of the logarithms of the extreme eigenvalues of
`X`: the first term is `log ‖X‖` and the second is `- log (λ_min X)`. -/
theorem projDist_eq_norm_form {m₀ m₁ : Matrix n n ℝ} (h₀ : m₀.PosDef) (h₁ : m₁.PosDef) :
    projDist m₀ m₁ =
      (1 / 2) * (Real.log ‖matSqrt m₀⁻¹ * m₁ * matSqrt m₀⁻¹‖ +
        Real.log ‖(matSqrt m₀⁻¹ * m₁ * matSqrt m₀⁻¹)⁻¹‖) := by
  rw [projDist_def, relSize_def m₁ m₀, relSize_eq_norm_normalize_inv h₀ h₁]

/-- The projective distance is symmetric. -/
theorem projDist_comm (m₀ m₁ : Matrix n n ℝ) : projDist m₀ m₁ = projDist m₁ m₀ := by
  simp only [projDist_def]
  ring

/-- The projective distance from a positive definite matrix to itself is zero. -/
theorem projDist_self [Nonempty n] {m : Matrix n n ℝ} (hm : m.PosDef) :
    projDist m m = 0 := by
  rw [projDist_def, relSize_self_eq_one hm, Real.log_one]
  norm_num

/-- The projective distance is nonnegative. -/
theorem projDist_nonneg [Nonempty n] {m₀ m₁ : Matrix n n ℝ} (h₀ : m₀.PosDef)
    (h₁ : m₁.PosDef) : 0 ≤ projDist m₀ m₁ := by
  have hL : 0 < relSize m₁ m₀ := relSize_pos h₁ h₀
  have hA : 0 < relSize m₀ m₁ := relSize_pos h₀ h₁
  have hprod : 1 ≤ relSize m₁ m₀ * relSize m₀ m₁ := one_le_relSize_mul_relSize h₁ h₀
  have hlog : 0 ≤ Real.log (relSize m₁ m₀ * relSize m₀ m₁) := Real.log_nonneg hprod
  rw [log_mul_pos hL hA] at hlog
  rw [projDist_def]
  linarith only [hlog]

/-! ## Invariances -/

/-- Scaling the first matrix by a positive scalar leaves the distance
unchanged. -/
theorem projDist_smul_left [Nonempty n] {c : ℝ} (hc : 0 < c) {m₀ m₁ : Matrix n n ℝ}
    (h₀ : m₀.PosDef) (h₁ : m₁.PosDef) : projDist (c • m₀) m₁ = projDist m₀ m₁ := by
  have h1 : relSize m₁ (c • m₀) = c⁻¹ * relSize m₁ m₀ :=
    relSize_smul_right hc h₁.posSemidef h₀
  have h2 : relSize (c • m₀) m₁ = c * relSize m₀ m₁ := relSize_smul_left hc.le m₀ m₁
  rw [projDist_def, projDist_def, h1, h2,
    log_inv_mul_add_log_mul hc (relSize_pos h₁ h₀) (relSize_pos h₀ h₁)]

/-- Scaling the second matrix by a positive scalar leaves the distance
unchanged. -/
theorem projDist_smul_right [Nonempty n] {c : ℝ} (hc : 0 < c) {m₀ m₁ : Matrix n n ℝ}
    (h₀ : m₀.PosDef) (h₁ : m₁.PosDef) : projDist m₀ (c • m₁) = projDist m₀ m₁ := by
  rw [projDist_comm, projDist_smul_left hc h₁ h₀, projDist_comm]

/-! ## The two-sided bound -/

/-- **The workhorse bound.**  A two-sided Loewner sandwich
`a m₀ ≤ m₁ ≤ b m₀` bounds the projective distance by `½ log (b/a)`. -/
theorem projDist_le_of_le [Nonempty n] {m₀ m₁ : Matrix n n ℝ} (h₀ : m₀.PosDef)
    (h₁ : m₁.PosDef) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hlow : a • m₀ ≤ m₁)
    (hhigh : m₁ ≤ b • m₀) : projDist m₀ m₁ ≤ (1 / 2) * Real.log (b / a) := by
  have hupper : relSize m₁ m₀ ≤ b := (relSize_le_iff h₁.posSemidef h₀ hb.le).mpr hhigh
  have hlower : relSize m₀ m₁ ≤ a⁻¹ := by
    refine (relSize_le_iff h₀.posSemidef h₁ (inv_nonneg.mpr ha.le)).mpr ?_
    have h := smul_le_smul_of_le (inv_nonneg.mpr ha.le) hlow
    rwa [smul_smul, inv_mul_cancel₀ ha.ne', one_smul] at h
  have hlogU : Real.log (relSize m₁ m₀) ≤ Real.log b :=
    Real.log_le_log (relSize_pos h₁ h₀) hupper
  have hlogL : Real.log (relSize m₀ m₁) ≤ Real.log a⁻¹ :=
    Real.log_le_log (relSize_pos h₀ h₁) hlower
  have hlogInv : Real.log a⁻¹ = -Real.log a := Real.log_inv a
  rw [projDist_def, log_div_pos hb ha]
  rw [hlogInv] at hlogL
  linarith only [hlogU, hlogL]

/-! ## The triangle inequality -/

/-- **The triangle inequality of `e.scale.selection.projective.distance`.**  The sharp
constants of the two sandwiches compose, and the logarithm of the quotient of
the composed constants splits into the two distances. -/
theorem projDist_triangle [Nonempty n] {m₀ m₁ m₂ : Matrix n n ℝ} (h₀ : m₀.PosDef)
    (h₁ : m₁.PosDef) (h₂ : m₂.PosDef) :
    projDist m₀ m₂ ≤ projDist m₀ m₁ + projDist m₁ m₂ := by
  -- The four sharp constants of `e.scale.selection.projective.distance`.
  have hL₀₁ : (0 : ℝ) < relSize m₁ m₀ := relSize_pos h₁ h₀
  have hA₀₁ : (0 : ℝ) < relSize m₀ m₁ := relSize_pos h₀ h₁
  have hL₁₂ : (0 : ℝ) < relSize m₂ m₁ := relSize_pos h₂ h₁
  have hA₁₂ : (0 : ℝ) < relSize m₁ m₂ := relSize_pos h₁ h₂
  -- Upper composition: `m₂ ≤ L₀₁ L₁₂ m₀`.
  have hup : m₂ ≤ (relSize m₁ m₀ * relSize m₂ m₁) • m₀ := by
    have h1 : m₂ ≤ relSize m₂ m₁ • m₁ := le_relSize_smul h₂.posSemidef h₁
    have h2 : relSize m₂ m₁ • m₁ ≤ relSize m₂ m₁ • (relSize m₁ m₀ • m₀) :=
      smul_le_smul_of_le hL₁₂.le (le_relSize_smul h₁.posSemidef h₀)
    rw [smul_smul, mul_comm (relSize m₂ m₁) (relSize m₁ m₀)] at h2
    exact h1.trans h2
  -- Lower composition: `(A₀₁ A₁₂)⁻¹ m₀ ≤ m₂`.
  have hm₀ : m₀ ≤ (relSize m₀ m₁ * relSize m₁ m₂) • m₂ := by
    have h1 : m₀ ≤ relSize m₀ m₁ • m₁ := le_relSize_smul h₀.posSemidef h₁
    have h2 : relSize m₀ m₁ • m₁ ≤ relSize m₀ m₁ • (relSize m₁ m₂ • m₂) :=
      smul_le_smul_of_le hA₀₁.le (le_relSize_smul h₁.posSemidef h₂)
    rw [smul_smul] at h2
    exact h1.trans h2
  have hprodA : (0 : ℝ) < relSize m₀ m₁ * relSize m₁ m₂ := mul_pos hA₀₁ hA₁₂
  have hdown : (relSize m₀ m₁ * relSize m₁ m₂)⁻¹ • m₀ ≤ m₂ := by
    have h := smul_le_smul_of_le (inv_nonneg.mpr hprodA.le) hm₀
    rwa [smul_smul, inv_mul_cancel₀ hprodA.ne', one_smul] at h
  -- The sandwich bound with the composed constants.
  have hbound := projDist_le_of_le h₀ h₂ (inv_pos.mpr hprodA)
    (mul_pos hL₀₁ hL₁₂) hdown hup
  -- The quotient of the composed constants splits into the two distances.
  have hquot : relSize m₁ m₀ * relSize m₂ m₁ / (relSize m₀ m₁ * relSize m₁ m₂)⁻¹
      = relSize m₁ m₀ * relSize m₀ m₁ * (relSize m₂ m₁ * relSize m₁ m₂) := by
    rw [div_eq_mul_inv, inv_inv]
    ring
  rw [hquot, log_four_split hL₀₁ hA₀₁ hL₁₂ hA₁₂] at hbound
  simp only [projDist_def] at hbound ⊢
  linarith only [hbound]

end

end HighContrast
end HCPolySupport
