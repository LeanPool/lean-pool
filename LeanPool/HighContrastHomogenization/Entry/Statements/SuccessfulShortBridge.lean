/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Frozen.CoarseEllipticityDagger
public import LeanPool.HighContrastHomogenization.Setup.BlockAlgebra
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.BlockMatrixProperties
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.CoarseBounds
public import LeanPool.HighContrastHomogenization.Setup.Response
public import LeanPool.HighContrastHomogenization.Entry.Geometry.StandardCell
public import LeanPool.HighContrastHomogenization.Support.Probability.IndependentSums.PsiCalculus
public import LeanPool.HighContrastHomogenization.Setup.CoefficientSpace
public import LeanPool.HighContrastHomogenization.Entry.Setup.Profile
public import LeanPool.HighContrastHomogenization.Entry.Setup.ProjectiveDistance
public import LeanPool.HighContrastHomogenization.Frozen.Stationarity
public import LeanPool.HighContrastHomogenization.Setup.LocalSigmaFields
public import LeanPool.HighContrastHomogenization.Frozen.UnitRange
public import LeanPool.HighContrastHomogenization.Entry.Geometry.RoundedGridBasic
public import LeanPool.HighContrastHomogenization.Entry.SuccessfulShortBridge

/-!
# High-contrast homogenization: Entry.Statements.SuccessfulShortBridge

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Proposition `p.successful.short.bridge` — comparison after a change of geometry

`p.successful.short.bridge`, the paper's Proposition "Comparison after a change of geometry",
transcribed from the printed display.

Reading of the display, stated here so that no divergence is silent:

* **The source lower scale is a standing hypothesis.** Near `e.source.lower.scale` reads "From now
  on `j_*` satisfies `e.source.lower.scale`", i.e. `j_* ≥ ⌈C_src(d,γ) log_3(2K_{Ψ_S})⌉` with
  `C_src` the constant of the source estimate (near `e.source.lower.scale`). That sentence stands
  from there
  onward, of the same kind as `3^{j_*} ≥ 2d` near `e.rounded.grid.bounds`: every later statement
  whose type
  mentions `j_*` carries it as a premise, whether or not its own display restates it, and whether
  or not its proof will use the source estimate. It is therefore a hypothesis here, with `C_src`
  existential in the outermost constant group, depending on `(d,γ)` only, since the manuscript
  fixes one such constant for the whole argument.
* `L_0(d,γ) ∈ ℕ` and `c_0(d,γ) ∈ (0,1)` depend on `d` and `γ` only and are bound first;
  `B_0(σ,L,d,γ) ≥ 1` depends also on `σ` and `L` and is bound after them, before the coefficient
  law and the geometry — the printed argument lists fix these scopes.
* `L ∈ ℕ` with `L ≥ L_0 + ⌈log_3(σ^{-1})⌉`; the ceiling is the ceiling into `ℤ`, and the
  comparison is made in `ℤ`.
* `𝔪, 𝔪_+ > 0` are `Matrix.PosDef`, `q = 𝒬(𝔪)` and `q_+ = 𝒬(𝔪_+)` are
`Geometry.explicitRoundedGrid`,
  `Π` is `aspectRatio E`, `Q` is `bigQ d γ`, `d_pr` is `projectiveDistance`, `𝒫_q(n;k)` is
  `profile P γ q jStar k n`, `D_{q,j_*}` is `determinantDrift` and `Δ^q_{n,n+2L}` is
  `detIncrement`. The standing `3^{j_*} ≥ 2d` near `e.rounded.grid.bounds` is `hj` and the
  standing `d ≥ 2`
  of `t.polynomial.entry` is `hd`.
* `⋄^q_{n+2L} ∪ ⋄^{q_+}_{n+L} ⊆ □_{2j_*}` is the printed containment, with `□_{2j_*}` the
  centered cube `HighContrast.centeredCube d (2 j_*)`.
* The conclusion `(1−σ)𝐀hom_{n+2L,q} ≤ 𝐀hom_{n+L,q_+} ≤ (1+σ)𝐀hom_{n+2L,q}` is the Loewner
  order `BlockMatLoewnerLE` of the scaled annealed blocks (`blockScale`).
* The display names no hypothesis on the coefficient law; the manuscript's standing assumptions
  are in force throughout and are carried in the binder order of the root statement
  `HCPoly/Entry/Statements/PolynomialEntry.lean`, after the constants, which the printed argument
  lists say
  are independent of the law.

The proof is one application of `HCPolySupport.HighContrast.Entry.successful_short_bridge`
(`HCPoly/Entry/SuccessfulShortBridge.lean`) to the binders of the statement.
-/

open HCPolySupport.HighContrast (CoeffSpace adaptedMean aspectRatio blockScale)
namespace HCPolySupport.HighContrast

open MeasureTheory
open scoped Matrix.Norms.L2Operator

/-- **Proposition `p.successful.short.bridge`**. There are
`L_0(d,γ) ∈ ℕ` and `c_0(d,γ) ∈ (0,1)` such that for every `σ ∈ (0,1]` and `L ≥ L_0 +
⌈log_3(σ^{-1})⌉` there is `B_0(σ,L,d,γ) ≥ 1` with: under the printed containment, eccentricity,
`n ≥ k+2Q`, `d_pr([𝔪],[𝔪_+]) ≤ 1` and `𝒫_q(n;k)+D_{q,j_*}(n)+Δ^q_{n,n+2L} ≤ c_0σ`, one has
`(1−σ)𝐀hom_{n+2L,q} ≤ 𝐀hom_{n+L,q_+} ≤ (1+σ)𝐀hom_{n+2L,q}`. -/
theorem successful_short_bridge
    (d : ℕ) (hd : 2 ≤ d)
    (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ (L₀ : ℕ) (c₀ : ℝ), c₀ ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∃ Csrc : ℝ, 0 < Csrc ∧
        ∀ σ : ℝ, σ ∈ Set.Ioc (0 : ℝ) 1 →
        ∀ L : ℕ, (L₀ : ℤ) + ⌈Real.logb 3 σ⁻¹⌉ ≤ (L : ℤ) →
          ∃ B₀ : ℝ, 1 ≤ B₀ ∧
            ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
              (S : CoeffSpace d → ℝ),
              IsProbabilityMeasure P →
              IsStationaryLaw P →
              IsUnitRangeLaw P →
              CoarseEllipticityDagger P γ E Ψ K S →
              ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
                ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
                ∀ (m mPlus : Mat d), m.PosDef → mPlus.PosDef →
                  ∀ k n : ℤ, (jStar : ℤ) ≤ k → k ≤ n →
                    HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar m) (n + 2 * (L : ℤ)) ∪
                        HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar mPlus)
                          (n + (L : ℤ)) ⊆
                      HighContrast.centeredCube d (2 * (jStar : ℤ)) →
                    Real.log (‖m‖ * ‖m⁻¹‖) ≤
                      c₀ / (L : ℝ) *
                        ((k : ℝ) - (jStar : ℝ) -
                          (⌈B₀ * Real.logb 3 (2 + aspectRatio E)⌉ : ℤ)) →
                    k + 2 * (bigQ d γ : ℤ) ≤ n →
                    projectiveDistance m mPlus ≤ 1 →
                    profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k n +
                          determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar n +
                        detIncrement P (Geometry.explicitRoundedGrid jStar m) n (n + 2 * (L : ℤ)) ≤
                      c₀ * σ →
                    BlockMatLoewnerLE
                        (blockScale (1 - σ)
                          (adaptedMean P (Geometry.explicitRoundedGrid jStar m) (n + 2 * (L : ℤ))))
                        (adaptedMean P (Geometry.explicitRoundedGrid jStar mPlus) (n + (L : ℤ))) ∧
                      BlockMatLoewnerLE
                        (adaptedMean P (Geometry.explicitRoundedGrid jStar mPlus) (n + (L : ℤ)))
                        (blockScale (1 + σ)
                          (adaptedMean P (Geometry.explicitRoundedGrid jStar m)
                            (n + 2 * (L : ℤ)))) := by exact HCPolySupport.HighContrast.Entry.successful_short_bridge d hd γ hγ

end HCPolySupport.HighContrast
