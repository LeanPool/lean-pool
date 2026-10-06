/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Frozen.CoarseEllipticityDagger
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.BlockMatrixProperties
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.CoarseBounds
public import LeanPool.HighContrastHomogenization.Setup.Response
public import LeanPool.HighContrastHomogenization.Entry.Geometry.StandardCell
public import LeanPool.HighContrastHomogenization.Support.Probability.IndependentSums.PsiCalculus
public import LeanPool.HighContrastHomogenization.Setup.CoefficientSpace
public import LeanPool.HighContrastHomogenization.Frozen.Stationarity
public import LeanPool.HighContrastHomogenization.Setup.LocalSigmaFields
public import LeanPool.HighContrastHomogenization.Frozen.UnitRange
public import LeanPool.HighContrastHomogenization.Setup.BlockAlgebra
public import LeanPool.HighContrastHomogenization.Entry.PolynomialEntry

/-!
# High-contrast homogenization: Entry.Statements.PolynomialEntry

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Theorem `t.polynomial.entry` — polynomial entry into small contrast

The paper's Theorem A, stated directly in `σ`.

`C` is bound before `P`, `E`, `Ψ`, `K` and `S`. That binder order is the content of the
sentence following the theorem — "the constant `C` above is independent of `E`, the coefficient
law, `Π`, and `K_{Ψ_S}`" — and it is what lets one `C` serve two arbitrary laws at once.

The conclusion is the printed one: `Θ_m ≤ 1 + σ` for every scale `m ≥ m_ent`, where
`m_ent := ⌈C log₃(2 + Π K_{Ψ_S})⌉`. Nothing asserts that `m_ent` is the first scale at which
the contrast is small, and `γ` is bound before `C`, so no uniformity is claimed as `γ ↑ 1`.

`Θ_m` is `annealedContrast` (`e.Theta.m`); `Π K_{Ψ_S}` is `aspectRatio E * K`.

The proof is one application of `HCPolySupport.HighContrast.Entry.polynomial_entry`
(`HCPoly/Entry/PolynomialEntry.lean`) to the binders of the statement.
-/

open HCPolySupport.HighContrast (CoeffSpace annealedContrast aspectRatio)
namespace HCPolySupport.HighContrast

open MeasureTheory

/-- **Theorem `t.polynomial.entry`.** For every `d ≥ 2`, `γ ∈ [0,1)` and `σ ∈ (0,1]` there is
`C(σ,d,γ) > 0` such that, under the standing assumptions, `Θ_m ≤ 1 + σ` for every scale
`m ≥ ⌈C log₃(2 + Π K)⌉`. -/
theorem polynomial_entry
    (d : ℕ) (hd : 2 ≤ d)
    (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (σ : ℝ) (hσ : σ ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
        (S : CoeffSpace d → ℝ),
        IsProbabilityMeasure P →
        IsStationaryLaw P →
        IsUnitRangeLaw P →
        CoarseEllipticityDagger P γ E Ψ K S →
        ∀ m : ℤ, ⌈C * Real.logb 3 (2 + aspectRatio E * K)⌉ ≤ m →
          annealedContrast P m ≤ 1 + σ := by
  exact HCPolySupport.HighContrast.Entry.polynomial_entry d hd γ hγ σ hσ


end HCPolySupport.HighContrast
