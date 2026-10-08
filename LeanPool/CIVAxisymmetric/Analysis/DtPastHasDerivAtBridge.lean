/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.DtPast
public import Mathlib.Analysis.Calculus.TangentCone.Real

/-!
# Bridge from `dtPast` to `HasDerivAt`

`dtPast` is defined in `CIV.Statements.DtPast` as a `derivWithin` over `Set.Iic` — Mathlib's
junk-value-on-non-differentiability one-sided derivative.  These lemmas bridge that identity
to a genuine `HasDerivAt` of the time-slice, so that a `dtPast`-shaped identity from a
zoom PDE (`CIV.zoomTheta_pde`, `CIV.zoomOmega_pde`) can certify a derivative once
differentiability in time is separately known, feeding differentiation under the integral sign
toward the equation-based time-pairing estimate `hpair`.
-/

public section

open Set

noncomputable section

namespace CIV



theorem dtPast_eq_of_hasDerivAt {phi : (ℝ × ℝ) × ℝ → ℝ} {p : (ℝ × ℝ) × ℝ} {v : ℝ}
    (h : HasDerivAt (fun t => phi (p.1, t)) v p.2) :
    dtPast phi p = v := by
  unfold dtPast
  exact h.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iic p.2)

theorem hasDerivAt_of_dtPast_eq {phi : (ℝ × ℝ) × ℝ → ℝ} {p : (ℝ × ℝ) × ℝ} {v : ℝ}
    (hdiff : DifferentiableAt ℝ (fun t => phi (p.1, t)) p.2) (heq : dtPast phi p = v) :
    HasDerivAt (fun t => phi (p.1, t)) v p.2 := by
  have hhas := hdiff.hasDerivAt
  have hd := dtPast_eq_of_hasDerivAt hhas
  rw [hd] at heq
  rw [← heq]
  exact hhas

theorem hasDerivAt_iff_dtPast_eq {phi : (ℝ × ℝ) × ℝ → ℝ} {p : (ℝ × ℝ) × ℝ} {v : ℝ}
    (hdiff : DifferentiableAt ℝ (fun t => phi (p.1, t)) p.2) :
    HasDerivAt (fun t => phi (p.1, t)) v p.2 ↔ dtPast phi p = v := by
  constructor
  · exact dtPast_eq_of_hasDerivAt
  · exact hasDerivAt_of_dtPast_eq hdiff

end CIV
