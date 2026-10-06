/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Geometry.Canonical
public import LeanPool.HighContrastHomogenization.Geometry.ProjectiveDistance

/-!
# High-contrast homogenization: Geometry.ReferenceRadius

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The canonical metric of a reference block

The reference-radius estimate in `e.initial.geometry.bounds` reads the canonical
balance chain on the lower-right principal blocks.  If the Schur
data of a self-dominating block `E` are `(s, s_*, k)`, the balance chain
`E^♯ ≤ M(E) ≤ E` becomes `s^{-1} ≤ m(E)^{-1} ≤ s_*^{-1}`, that is
`s_* ≤ m(E) ≤ s`; the aspect bounds `λ_0 I ≤ s_*` and `s ≤ Λ_0 I` of
`e.reference.aspect.ratio` then place `m(E)` between `λ_0 I` and `Λ_0 I` and bound
its projective distance to the identity by `(1/2) log Π`.

Both statements here are about the matrix core of the corollary and carry no
probabilistic hypothesis: the reference block enters through its Schur data and
through the hypothesis `E^♯ ≤ E`, which for the coefficient law of
`e.coarse.ellipticity` is the primal-adjoint order for the reference block.
-/

namespace HCPolySupport
namespace HighContrast

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

variable {d : ℕ}

/-- **The canonical metric of a self-dominating block sits between its Schur
blocks**, the principal blocks of the reference metric. -/
theorem schurStar_le_canonMetric_le_schur {E : FullBlockMat d} (hE : E.PosDef)
    (hle : fullBlockSharp E ≤ E) {s sStar k : Mat d} (hs : s.PosDef)
    (hstar : sStar.PosDef) (hform : E = schurBlock s sStar k) :
    sStar ≤ canonMetric E ∧ canonMetric E ≤ s := by
  obtain ⟨hlow, hhigh, -⟩ := canonBalance hE hle
  have hm : (canonMetric E).PosDef := posDef_canonMetric hE
  have hMlr : (canonBlock E).toBlocks₂₂ = (canonMetric E)⁻¹ := toBlocks₂₂_canonBlock hE
  have hElr : E.toBlocks₂₂ = sStar⁻¹ := by rw [hform, toBlocks₂₂_schurBlock]
  have hSlr : (fullBlockSharp E).toBlocks₂₂ = s⁻¹ := by
    rw [hform, fullBlockSharp_schurBlock hs hstar, toBlocks₂₂_schurBlock]
  have h1 : s⁻¹ ≤ (canonMetric E)⁻¹ := by
    have := toBlocks₂₂_mono hlow
    rwa [hSlr, hMlr] at this
  have h2 : (canonMetric E)⁻¹ ≤ sStar⁻¹ := by
    have := toBlocks₂₂_mono hhigh
    rwa [hMlr, hElr] at this
  refine ⟨?_, ?_⟩
  · have := inv_le_inv_of_le hm.inv hstar.inv h2
    rwa [Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_posDef hstar),
      Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_posDef hm)] at this
  · have := inv_le_inv_of_le hs.inv hm.inv h1
    rwa [Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_posDef hs),
      Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_posDef hm)] at this

/-- **The reference radius**.  The canonical
metric of a self-dominating block lies between the two scalar aspect bounds of
its Schur data, and its projective distance to the identity is at most half the
logarithm of their quotient — the reference aspect ratio `Π` of
`e.reference.aspect.ratio`. -/
theorem canonMetric_reference_radius [Nonempty (Fin d)] {E : FullBlockMat d}
    (hE : E.PosDef) (hle : fullBlockSharp E ≤ E) {s sStar k : Mat d}
    (hs : s.PosDef) (hstar : sStar.PosDef) (hform : E = schurBlock s sStar k)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : 0 < Lam)
    (hlow : lam • (1 : Mat d) ≤ sStar) (hhigh : s ≤ Lam • (1 : Mat d)) :
    lam • (1 : Mat d) ≤ canonMetric E ∧ canonMetric E ≤ Lam • (1 : Mat d) ∧
      projDist 1 (canonMetric E) ≤ (1 / 2) * Real.log (Lam / lam) := by
  obtain ⟨h1, h2⟩ := schurStar_le_canonMetric_le_schur hE hle hs hstar hform
  have hlow' : lam • (1 : Mat d) ≤ canonMetric E := hlow.trans h1
  have hhigh' : canonMetric E ≤ Lam • (1 : Mat d) := h2.trans hhigh
  refine ⟨hlow', hhigh', ?_⟩
  exact projDist_le_of_le Matrix.PosDef.one (posDef_canonMetric hE) hlam hLam hlow' hhigh'

end

end HighContrast
end HCPolySupport
