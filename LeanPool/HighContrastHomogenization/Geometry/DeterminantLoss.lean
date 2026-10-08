/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Geometry.Canonical
public import LeanPool.HighContrastHomogenization.Geometry.DetOrder
public import LeanPool.HighContrastHomogenization.Geometry.ProjectiveDistance

/-!
# High-contrast homogenization: Geometry.DeterminantLoss

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Comparison of canonical geometries under determinant loss

This file proves `e.global.selection.metric.loss`: for positive doubled blocks
`F ≤ E` with determinant ratio `r = det(E)^{1/d}/det(F)^{1/d}`, the Loewner
comparison `F ≤ E ≤ r^d F`, the two-sided comparison
`r^{-d/2} M(F) ≤ M(E) ≤ r^{d/2} M(F)` of the canonical metric blocks, the two
imbalance bounds `𝔡(F) ≤ r^d 𝔡(E)` and `𝔡(E) ≤ r^{2d} 𝔡(F)`, and the projective
bound `d_pr([m(E)],[m(F)]) ≤ (d/2) log r`.

The reference proof opens by saying that every eigenvalue of `F^{-1/2}EF^{-1/2}`
is at least one and their product is `det(E)/det(F)`, so each of them is at most
that product.  In the encoding used here no eigenvalue is ever named: the
largest one is the relative size `Λ(F;E)`, the product is a determinant, and the
sentence is exactly `relSize_le_det_div`.  Everything else is the geometric-mean
toolkit, the sharp rules, and the least-scalar-bound characterization of the
relative size.

The scalar `r` is carried as a hypothesis-bound real satisfying `r^d = det(E)/det(F)`,
so that only the single power `r^d` — never a real exponent — occurs inside a
Loewner inequality, and `r^{d/2}` is the square root of that power.  The printed
`d`-th root is `canonDetRatio`, and `canonDeterminantLoss_canonDetRatio`
instantiates the lemma at it.

The file also collects the three steps that `e.global.selection.metric.comparison`
shares with this lemma: the unconditional upper half `E ≤ 𝔡(E)^{1/2} M(E)` of the
balance chain, the passage from a scalar bound against `M(F)` to a bound on
`𝔡(F)` by squaring, and the step "take the lower-right principal blocks, then
invert" that turns a comparison of canonical metric blocks into a projective
bound on the canonical metrics.
-/

namespace HCPolySupport
namespace HighContrast

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

/-! ## Scalar bookkeeping for the Loewner order -/

section Scalars

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
/-- A scalar Loewner bound may be moved to the other side. -/
theorem smul_inv_le_of_le_smul {c : ℝ} (hc : 0 < c) {A B : Matrix n n ℝ} (h : A ≤ c • B) :
    c⁻¹ • A ≤ B := by
  have h2 := smul_le_smul_of_le (inv_nonneg.mpr hc.le) h
  rwa [smul_smul, inv_mul_cancel₀ hc.ne', one_smul] at h2

omit [Fintype n] [DecidableEq n] in
/-- A scalar Loewner bound may be moved to the other side. -/
theorem le_smul_of_smul_inv_le {c : ℝ} (hc : 0 < c) {A B : Matrix n n ℝ} (h : c⁻¹ • A ≤ B) :
    A ≤ c • B := by
  have h2 := smul_le_smul_of_le hc.le h
  rwa [smul_smul, mul_inv_cancel₀ hc.ne', one_smul] at h2

/-- The inverse of a dilation of an invertible matrix. -/
theorem inv_smul_of_isUnit {c : ℝ} (hc : c ≠ 0) {P : Matrix n n ℝ} (hP : IsUnit P.det) :
    (c • P)⁻¹ = c⁻¹ • P⁻¹ := by
  refine Matrix.inv_eq_right_inv ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_nonsing_inv _ hP,
    mul_inv_cancel₀ hc, one_smul]

end Scalars

/-! ## Square-root arithmetic

These helpers speak only about abstract nonnegative reals; no later step lets a
linear-arithmetic call see `Real.sqrt` applied to a matrix expression. -/

private theorem sq_sqrt_mul_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.sqrt a * Real.sqrt b) ^ 2 = a * b := by
  rw [mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hb]

private theorem div_inv_sqrt {u : ℝ} (hu : 0 ≤ u) :
    Real.sqrt u / (Real.sqrt u)⁻¹ = u := by
  rw [div_eq_mul_inv, inv_inv, Real.mul_self_sqrt hu]

/-! ## Steps shared with the near-isometric comparison -/

variable {d : ℕ}

/-- The imbalance is a square, hence nonnegative. -/
theorem canonImbalance_nonneg (E : FullBlockMat d) : 0 ≤ canonImbalance E := by
  rw [canonImbalance]
  positivity

/-- **The upper half of the balance chain**, unconditionally.  The reference text
reads it off the definition of `𝔡(E)`: the positive matrix
`C = M(E)^{-1/2} E M(E)^{-1/2}` satisfies `C ≤ |C| I = 𝔡(E)^{1/2} I`.  No
comparison between `E` and `E^♯` is needed. -/
theorem le_sqrt_canonImbalance_smul {E : FullBlockMat d} (hE : E.PosDef) :
    E ≤ Real.sqrt (canonImbalance E) • canonBlock E := by
  rw [sqrt_canonImbalance E]
  exact le_relSize_smul hE.posSemidef (posDef_canonBlock hE)

/-- **Squaring the largest generalized eigenvalue relative to `M(F)`.**  A scalar
Loewner bound of `F` against its own canonical metric block bounds the
imbalance by the square of the scalar. -/
theorem canonImbalance_le_sq {F : FullBlockMat d} (hF : F.PosDef) {c : ℝ} (hc : 0 ≤ c)
    (h : F ≤ c • canonBlock F) : canonImbalance F ≤ c ^ 2 := by
  have hrel : relSize F (canonBlock F) ≤ c :=
    (relSize_le_iff hF.posSemidef (posDef_canonBlock hF) hc).mpr h
  rw [canonImbalance, pow_two, pow_two]
  exact mul_self_le_mul_self (relSize_nonneg _ _) hrel

/-- **The lower-right principal blocks, followed by inversion.**  This is the
step that both `e.global.selection.metric.loss` and
`e.global.selection.metric.comparison` take to pass from a symmetric comparison of the
canonical metric blocks to a bound on the projective distance of the canonical
metrics; the passage to the blocks is `e.scale.selection.canonical.metric`, through
`(M(E))₂₂ = m(E)^{-1}`. -/
theorem projDist_canonMetric_le (hd : 0 < d) {E F : FullBlockMat d} (hE : E.PosDef)
    (hF : F.PosDef) {u : ℝ} (hu : 0 < u)
    (hlow : (Real.sqrt u)⁻¹ • canonBlock F ≤ canonBlock E)
    (hhigh : canonBlock E ≤ Real.sqrt u • canonBlock F) :
    projDist (canonMetric E) (canonMetric F) ≤ (1 / 2) * Real.log u := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hmE : (canonMetric E).PosDef := posDef_canonMetric hE
  have hmF : (canonMetric F).PosDef := posDef_canonMetric hF
  have hdetE : IsUnit (canonMetric E).det := isUnit_det_of_posDef hmE
  have hdetF : IsUnit (canonMetric F).det := isUnit_det_of_posDef hmF
  have hdetFinv : IsUnit ((canonMetric F)⁻¹).det := isUnit_det_of_posDef hmF.inv
  set s : ℝ := Real.sqrt u with hsdef
  have hs : 0 < s := Real.sqrt_pos.mpr hu
  -- the principal blocks
  have hb₁ : s⁻¹ • (canonMetric F)⁻¹ ≤ (canonMetric E)⁻¹ := by
    have h := toBlocks₂₂_mono hlow
    rwa [toBlocks₂₂_smul, toBlocks₂₂_canonBlock hF, toBlocks₂₂_canonBlock hE] at h
  have hb₂ : (canonMetric E)⁻¹ ≤ s • (canonMetric F)⁻¹ := by
    have h := toBlocks₂₂_mono hhigh
    rwa [toBlocks₂₂_smul, toBlocks₂₂_canonBlock hF, toBlocks₂₂_canonBlock hE] at h
  -- inversion
  have hinv₂ := inv_le_inv_of_le hmE.inv (posDef_smul hmF.inv hs) hb₂
  rw [inv_smul_of_isUnit hs.ne' hdetFinv, Matrix.nonsing_inv_nonsing_inv _ hdetE,
    Matrix.nonsing_inv_nonsing_inv _ hdetF] at hinv₂
  have hinv₁ := inv_le_inv_of_le (posDef_smul hmF.inv (inv_pos.mpr hs)) hmE.inv hb₁
  rw [inv_smul_of_isUnit (inv_pos.mpr hs).ne' hdetFinv, inv_inv,
    Matrix.nonsing_inv_nonsing_inv _ hdetE, Matrix.nonsing_inv_nonsing_inv _ hdetF] at hinv₁
  -- the sandwich for the canonical metrics themselves
  have hup : canonMetric F ≤ s • canonMetric E := le_smul_of_smul_inv_le hs hinv₂
  have hdown : s⁻¹ • canonMetric E ≤ canonMetric F := smul_inv_le_of_le_smul hs hinv₁
  have hbound := projDist_le_of_le hmE hmF (inv_pos.mpr hs) hs hdown hup
  rwa [hsdef, div_inv_sqrt hu.le] at hbound

/-! ## The comparison in terms of the determinant quotient -/

/-- **The Loewner comparison** produced by a determinant loss, with the
determinant quotient in place of `r^d`. -/
theorem le_det_div_smul {E F : FullBlockMat d} (hE : E.PosDef) (hF : F.PosDef) (hFE : F ≤ E) :
    E ≤ (E.det / F.det) • F :=
  (relSize_le_iff hE.posSemidef hF (div_pos hE.det_pos hF.det_pos).le).mp
    (relSize_le_det_div hE hF hFE)

/-- **Sharp order reversal** applied to the Loewner comparison: the reference
text's `r^{-d} F^♯ ≤ E^♯`.  The companion inequality `E^♯ ≤ F^♯` is order
reversal of the primal-adjoint involution applied to `F ≤ E` directly. -/
theorem smul_fullBlockSharp_le {E F : FullBlockMat d} (hE : E.PosDef) (hF : F.PosDef)
    (hFE : F ≤ E) : (E.det / F.det)⁻¹ • fullBlockSharp F ≤ fullBlockSharp E := by
  have hρ : 0 < E.det / F.det := div_pos hE.det_pos hF.det_pos
  have h := fullBlockSharp_le_fullBlockSharp hE (posDef_smul hF hρ) (le_det_div_smul hE hF hFE)
  rwa [fullBlockSharp_smul hF hρ] at h

/-- **The upper comparison of the canonical metric blocks**, the right-hand half
of the comparison of the canonical metrics after a determinant loss. -/
theorem canonBlock_le_smul {E F : FullBlockMat d} (hE : E.PosDef) (hF : F.PosDef)
    (hFE : F ≤ E) : canonBlock E ≤ Real.sqrt (E.det / F.det) • canonBlock F := by
  have hρ : 0 < E.det / F.det := div_pos hE.det_pos hF.det_pos
  have hSE : (fullBlockSharp E).PosDef := posDef_fullBlockSharp hE
  have hSF : (fullBlockSharp F).PosDef := posDef_fullBlockSharp hF
  have hmono := matGeomMean_mono hE (posDef_smul hF hρ) hSE hSF (le_det_div_smul hE hF hFE)
    (fullBlockSharp_le_fullBlockSharp hF hE hFE)
  have hhom := matGeomMean_smul hF hSF hρ one_pos
  rw [one_smul, mul_one] at hhom
  rw [hhom] at hmono
  exact hmono

/-- **The lower comparison of the canonical metric blocks**, the left-hand half
of the comparison of the canonical metrics after a determinant loss. -/
theorem smul_canonBlock_le {E F : FullBlockMat d} (hE : E.PosDef) (hF : F.PosDef)
    (hFE : F ≤ E) : (Real.sqrt (E.det / F.det))⁻¹ • canonBlock F ≤ canonBlock E := by
  have hρ : 0 < E.det / F.det := div_pos hE.det_pos hF.det_pos
  have hSE : (fullBlockSharp E).PosDef := posDef_fullBlockSharp hE
  have hSF : (fullBlockSharp F).PosDef := posDef_fullBlockSharp hF
  have hmono := matGeomMean_mono hF hE (posDef_smul hSF (inv_pos.mpr hρ)) hSE hFE
    (smul_fullBlockSharp_le hE hF hFE)
  have hhom := matGeomMean_smul hF hSF one_pos (inv_pos.mpr hρ)
  rw [one_smul, one_mul] at hhom
  rw [hhom, Real.sqrt_inv] at hmono
  exact hmono

/-- **The first imbalance bound** for the imbalances after a determinant loss,
with the determinant quotient in place of `r^d`. -/
theorem canonImbalance_le_det_div_mul {E F : FullBlockMat d} (hE : E.PosDef) (hF : F.PosDef)
    (hFE : F ≤ E) : canonImbalance F ≤ (E.det / F.det) * canonImbalance E := by
  have hρ : 0 < E.det / F.det := div_pos hE.det_pos hF.det_pos
  have hchain : F ≤ (Real.sqrt (canonImbalance E) * Real.sqrt (E.det / F.det)) • canonBlock F := by
    calc F ≤ E := hFE
      _ ≤ Real.sqrt (canonImbalance E) • canonBlock E := le_sqrt_canonImbalance_smul hE
      _ ≤ Real.sqrt (canonImbalance E) • (Real.sqrt (E.det / F.det) • canonBlock F) :=
          smul_le_smul_of_le (Real.sqrt_nonneg _) (canonBlock_le_smul hE hF hFE)
      _ = (Real.sqrt (canonImbalance E) * Real.sqrt (E.det / F.det)) • canonBlock F :=
          smul_smul _ _ _
  have hsq := canonImbalance_le_sq hF
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hchain
  rwa [sq_sqrt_mul_sqrt (canonImbalance_nonneg E) hρ.le, mul_comm] at hsq

/-- **The second imbalance bound** for the imbalances after a determinant loss,
with the determinant quotient in place of `r^d`.  This is the only place where
the sharp-pair identity `e.response.canonical.imbalance` is used. -/
theorem canonImbalance_le_det_div_sq_mul {E F : FullBlockMat d} (hE : E.PosDef) (hF : F.PosDef)
    (hFE : F ≤ E) : canonImbalance E ≤ (E.det / F.det) ^ 2 * canonImbalance F := by
  have hρ : 0 < E.det / F.det := div_pos hE.det_pos hF.det_pos
  have hSE : (fullBlockSharp E).PosDef := posDef_fullBlockSharp hE
  have hSF : (fullBlockSharp F).PosDef := posDef_fullBlockSharp hF
  have hdF : 0 ≤ canonImbalance F := canonImbalance_nonneg F
  have hFsharp : F ≤ canonImbalance F • fullBlockSharp F := by
    have h := le_relSize_smul hF.posSemidef hSF
    rwa [← canonImbalance_eq hF] at h
  have hsharp : fullBlockSharp F ≤ (E.det / F.det) • fullBlockSharp E :=
    le_smul_of_smul_inv_le hρ (smul_fullBlockSharp_le hE hF hFE)
  have hchain : E ≤ ((E.det / F.det) ^ 2 * canonImbalance F) • fullBlockSharp E := by
    calc E ≤ (E.det / F.det) • F := le_det_div_smul hE hF hFE
      _ ≤ (E.det / F.det) • (canonImbalance F • fullBlockSharp F) :=
          smul_le_smul_of_le hρ.le hFsharp
      _ = ((E.det / F.det) * canonImbalance F) • fullBlockSharp F := smul_smul _ _ _
      _ ≤ ((E.det / F.det) * canonImbalance F) • ((E.det / F.det) • fullBlockSharp E) :=
          smul_le_smul_of_le (mul_nonneg hρ.le hdF) hsharp
      _ = ((E.det / F.det) ^ 2 * canonImbalance F) • fullBlockSharp E := by
          rw [smul_smul]
          congr 1
          ring
  have hrel := (relSize_le_iff hE.posSemidef hSE
    (by positivity : (0:ℝ) ≤ (E.det / F.det) ^ 2 * canonImbalance F)).mpr hchain
  rwa [← canonImbalance_eq hE] at hrel

/-- **The projective bound** `e.global.selection.metric.loss`, with the
determinant quotient in place of `r^d`. -/
theorem projDist_canonMetric_le_log_det_div (hd : 0 < d) {E F : FullBlockMat d} (hE : E.PosDef)
    (hF : F.PosDef) (hFE : F ≤ E) :
    projDist (canonMetric E) (canonMetric F) ≤ (1 / 2) * Real.log (E.det / F.det) :=
  projDist_canonMetric_le hd hE hF (div_pos hE.det_pos hF.det_pos)
    (smul_canonBlock_le hE hF hFE) (canonBlock_le_smul hE hF hFE)

/-! ## The printed form -/

/-- The determinant-loss ratio `r = det(E)^{1/d}/det(F)^{1/d}` of two ordered
blocks. -/
@[expose]
def canonDetRatio (E F : FullBlockMat d) : ℝ := (E.det / F.det) ^ ((d : ℝ)⁻¹)

theorem canonDetRatio_nonneg {E F : FullBlockMat d} (h : 0 ≤ E.det / F.det) :
    0 ≤ canonDetRatio E F := Real.rpow_nonneg h _

/-- The `d`-th power of the determinant-loss ratio is the determinant
quotient. -/
theorem canonDetRatio_pow {E F : FullBlockMat d} (hd : d ≠ 0) (h : 0 ≤ E.det / F.det) :
    canonDetRatio E F ^ d = E.det / F.det := Real.rpow_inv_natCast_pow h hd

/-- **Comparison under determinant loss** (`e.global.selection.metric.loss`).
The scalar `r` is any nonnegative real whose `d`-th power is the determinant
quotient; `canonDetRatio` is the printed choice. -/
theorem canonDeterminantLoss (hd : 2 ≤ d) {E F : FullBlockMat d} (hE : E.PosDef) (hF : F.PosDef)
    (hFE : F ≤ E) {r : ℝ} (hr₀ : 0 ≤ r) (hrd : r ^ d = E.det / F.det) :
    1 ≤ r ∧
      (F ≤ E ∧ E ≤ r ^ d • F) ∧
      ((Real.sqrt (r ^ d))⁻¹ • canonBlock F ≤ canonBlock E ∧
        canonBlock E ≤ Real.sqrt (r ^ d) • canonBlock F) ∧
      (canonImbalance F ≤ r ^ d * canonImbalance E ∧
        canonImbalance E ≤ r ^ (2 * d) * canonImbalance F) ∧
      projDist (canonMetric E) (canonMetric F) ≤ ((d : ℝ) / 2) * Real.log r := by
  have hdpos : 0 < d := lt_of_lt_of_le two_pos hd
  have h1ρ : 1 ≤ E.det / F.det := (one_le_div hF.det_pos).mpr (det_le_det_of_le hF hE hFE)
  have h1r : 1 ≤ r := by
    by_contra hlt
    push Not at hlt
    have hpow := pow_lt_one₀ hr₀ hlt hdpos.ne'
    rw [hrd] at hpow
    linarith only [hpow, h1ρ]
  refine ⟨h1r, ⟨hFE, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · rw [hrd]; exact le_det_div_smul hE hF hFE
  · rw [hrd]; exact smul_canonBlock_le hE hF hFE
  · rw [hrd]; exact canonBlock_le_smul hE hF hFE
  · rw [hrd]; exact canonImbalance_le_det_div_mul hE hF hFE
  · rw [pow_mul', hrd]; exact canonImbalance_le_det_div_sq_mul hE hF hFE
  · have hlog : ((d : ℝ) / 2) * Real.log r = (1 / 2) * Real.log (E.det / F.det) := by
      rw [← hrd, Real.log_pow]
      ring
    rw [hlog]
    exact projDist_canonMetric_le_log_det_div hdpos hE hF hFE

/-- `e.global.selection.metric.loss` at the printed ratio
`r = det(E)^{1/d}/det(F)^{1/d}`. -/
theorem canonDeterminantLoss_canonDetRatio (hd : 2 ≤ d) {E F : FullBlockMat d} (hE : E.PosDef)
    (hF : F.PosDef) (hFE : F ≤ E) :
    1 ≤ canonDetRatio E F ∧
      (F ≤ E ∧ E ≤ canonDetRatio E F ^ d • F) ∧
      ((Real.sqrt (canonDetRatio E F ^ d))⁻¹ • canonBlock F ≤ canonBlock E ∧
        canonBlock E ≤ Real.sqrt (canonDetRatio E F ^ d) • canonBlock F) ∧
      (canonImbalance F ≤ canonDetRatio E F ^ d * canonImbalance E ∧
        canonImbalance E ≤ canonDetRatio E F ^ (2 * d) * canonImbalance F) ∧
      projDist (canonMetric E) (canonMetric F) ≤
        ((d : ℝ) / 2) * Real.log (canonDetRatio E F) := by
  have hdpos : 0 < d := lt_of_lt_of_le two_pos hd
  have hρ : (0 : ℝ) ≤ E.det / F.det := (div_pos hE.det_pos hF.det_pos).le
  exact canonDeterminantLoss hd hE hF hFE (canonDetRatio_nonneg hρ)
    (canonDetRatio_pow hdpos.ne' hρ)

end

end HighContrast
end HCPolySupport
