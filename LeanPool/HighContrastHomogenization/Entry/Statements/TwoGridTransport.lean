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
public import LeanPool.HighContrastHomogenization.Entry.TwoGridTransport

/-!
# High-contrast homogenization: Entry.Statements.TwoGridTransport

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Proposition `p.two.grid.transport` — transport of the complete profile

`p.two.grid.transport`, the paper's Proposition "Transport of the complete profile",
transcribed from the printed display.

Reading of the display, stated here so that no divergence is silent:

* `C(d,γ) ≥ 1` depends on `d` and `γ` only, so its quantifier precedes `ρ`, `δ`, the coefficient
  law, `j_*` and the geometry. The same `C` occurs in all four printed places (the scale
  separation, the lower bound on `L`, and the conclusion), exactly as the display writes it.
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
* `ρ ∈ (0,1]` and `δ ∈ [0,¼]` are the printed ranges; `L ∈ ℕ`.
* `𝔪, 𝔪_+ > 0` are `Matrix.PosDef`, `q = 𝒬(𝔪)` and `q_+ = 𝒬(𝔪_+)` are
`Geometry.explicitRoundedGrid`,
  `Π` is `aspectRatio E`, `d_pr` is `projectiveDistance`, `𝒫_q(m;n)` is `profile P γ q jStar n m`
  and `D_{q,j_*}` is `determinantDrift`. The standing `3^{j_*} ≥ 2d` near `e.rounded.grid.bounds`
  is `hj`
  and the standing `d ≥ 2` of `t.polynomial.entry` is `hd`.
* `|𝔪||𝔪^{-1}|` inside the logarithm is transcribed literally with Mathlib's L2 operator norm.
* Both the hypothesis `(1−δ)𝐀hom_{n+2L,q} ≤ 𝐀hom_{n+L,q_+} ≤ (1+δ)𝐀hom_{n+2L,q}` and the
  conclusion are Loewner statements (`BlockMatLoewnerLE`) about scaled annealed blocks.
* The display names no hypothesis on the coefficient law; the manuscript's standing assumptions
  are in force throughout and are carried in the binder order of the root statement
  `HCPoly/Entry/Statements/PolynomialEntry.lean`, after `C`, which the printed argument list says is
  independent of the law.

The proof is one application of `HCPolySupport.HighContrast.Entry.two_grid_transport`
(`HCPoly/Entry/TwoGridTransport.lean`) to the binders of the statement.
-/

open HCPolySupport.HighContrast (CoeffSpace adaptedMean aspectRatio blockScale)
namespace HCPolySupport.HighContrast

open MeasureTheory
open scoped Matrix.Norms.L2Operator

/-- **Proposition `p.two.grid.transport`**. There is `C(d,γ) ≥ 1`
such that, for `ρ ∈ (0,1]`, `δ ∈ [0,¼]`, `𝔪,𝔪_+ > 0`, `j_* ≤ k ≤ n` and `L ∈ ℕ` with the printed
containment, scale separation, `d_pr([𝔪],[𝔪_+]) ≤ 1`, `L ≥ C + log_3(ρ^{-1})`,
`𝒫_q(n+2L;k)+D_{q,j_*}(n+2L) ≤ 3^{−½(1−γ)L}ρ` and `(1−δ)𝐀hom_{n+2L,q} ≤ 𝐀hom_{n+L,q_+} ≤
(1+δ)𝐀hom_{n+2L,q}`, one has `𝒫_{q_+}(n+L;n+L)+D_{q_+,j_*}(n+L) ≤ C(δ+ρ)`. -/
theorem two_grid_transport
    (d : ℕ) (hd : 2 ≤ d)
    (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∃ Csrc : ℝ, 0 < Csrc ∧
        ∀ ρ : ℝ, ρ ∈ Set.Ioc (0 : ℝ) 1 →
        ∀ δ : ℝ, δ ∈ Set.Icc (0 : ℝ) (1 / 4) →
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
                  ∀ L : ℕ,
                    HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar m) (n + 2 * (L : ℤ)) ∪
                        HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar mPlus) (n + (L : ℤ)) ⊆
                      HighContrast.centeredCube d (2 * (jStar : ℤ)) →
                    C * ((L : ℝ) +
                        Real.logb 3 ((2 + aspectRatio E) * (‖m‖ * ‖m⁻¹‖))) ≤
                      (n : ℝ) - (jStar : ℝ) →
                    projectiveDistance m mPlus ≤ 1 →
                    C + Real.logb 3 ρ⁻¹ ≤ (L : ℝ) →
                    profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k (n + 2 * (L : ℤ)) +
                        determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar
                          (n + 2 * (L : ℤ)) ≤
                      (3 : ℝ) ^ (-(1 / 2) * (1 - γ) * (L : ℝ)) * ρ →
                    BlockMatLoewnerLE
                        (blockScale (1 - δ)
                          (adaptedMean P (Geometry.explicitRoundedGrid jStar m) (n + 2 * (L : ℤ))))
                        (adaptedMean P (Geometry.explicitRoundedGrid jStar mPlus) (n + (L : ℤ))) →
                    BlockMatLoewnerLE
                        (adaptedMean P (Geometry.explicitRoundedGrid jStar mPlus) (n + (L : ℤ)))
                        (blockScale (1 + δ)
                          (adaptedMean P (Geometry.explicitRoundedGrid jStar m) (n + 2 * (L : ℤ)))) →
                    profile P γ (Geometry.explicitRoundedGrid jStar mPlus) jStar (n + (L : ℤ))
                          (n + (L : ℤ)) +
                        determinantDrift P γ (Geometry.explicitRoundedGrid jStar mPlus) jStar
                          (n + (L : ℤ)) ≤
                      C * (δ + ρ) := by exact HCPolySupport.HighContrast.Entry.two_grid_transport d hd γ hγ

end HCPolySupport.HighContrast
