/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Setup.BlockAlgebra
public import LeanPool.HighContrastHomogenization.Entry.Setup.ProjectiveDistance
public import LeanPool.HighContrastHomogenization.Frozen.CoarseEllipticityDagger
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.BlockMatrixProperties
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.CoarseBounds
public import LeanPool.HighContrastHomogenization.Setup.Response
public import LeanPool.HighContrastHomogenization.Entry.Geometry.StandardCell
public import LeanPool.HighContrastHomogenization.Support.Probability.IndependentSums.PsiCalculus
public import LeanPool.HighContrastHomogenization.Setup.CoefficientSpace
public import LeanPool.HighContrastHomogenization.Entry.Setup.GeometryUpdate
public import LeanPool.HighContrastHomogenization.Entry.Setup.Profile
public import LeanPool.HighContrastHomogenization.Frozen.Stationarity
public import LeanPool.HighContrastHomogenization.Setup.LocalSigmaFields
public import LeanPool.HighContrastHomogenization.Frozen.UnitRange
public import LeanPool.HighContrastHomogenization.Entry.Geometry.RoundedGridBasic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# High-contrast homogenization: Entry.Setup.SelectionData

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The selection data of `p.scale.selection`

`p.scale.selection`, the opening of Proposition `p.scale.selection`:

> There exist `h(d,γ) ∈ ℕ` and `ε_0(d,γ), c(d,γ) ∈ (0,1)` such that, for every `ε ∈ (0,ε_0]`
> and `σ ∈ (0,ε]`, there exist `L(ε,σ,d,γ) ∈ ℕ` and `B_0(ε,σ,d,γ) ≥ 1` such that the
> following holds for every `B ≥ B_0`.  Set `η := cεσ`.

Two later statements reach back for these constants:

> Fix `h(d,γ) ∈ ℕ` and `ε_0(d,γ) ∈ (0,1)` from Proposition `p.scale.selection`.  Let
> `0 < σ ≤ ε ≤ ε_0`, and fix `L(ε,σ,d,γ) ∈ ℕ` and `B_0(ε,σ,d,γ) ≥ 1` furnished there.
> (`p.initial.fixed.grid.scale`)

> There exists `ε(d,γ) ∈ (0,ε_0]` with the following property.  Fix an integer
> `H ≥ max{4,h}` and `σ ∈ (0,ε]`, and choose `L`, `η`, and `B_0` as in Proposition
> `p.scale.selection`.  (`p.global.selection`,
> `p.global.selection`)

**One structure, in the functional form**: the outer constants `h`, `ε_0`,
`c`, which depend only on `d` and `γ`, together with the inner constants `L` and `B_0` as
*functions* of `(ε, σ)`, each with its printed range.  The form is forced by
`p.global.selection`, which chooses `ε` and then `σ` inside its own statement and only then
uses `L`, `η` and `B_0` at that pair: a structure with `ε` and `σ` as fields could not be
quantified over before they are chosen.

**The predicate `SelectionData.Selects`.**  The words
"furnished there" and "as in Proposition `p.scale.selection`" bind these constants to the
*conclusion* of that proposition, and it is stated in the
objects (`𝒫`, `D`, `Δ`, `Δ̂`, `m(F)`, `d_pr`, `𝔪_+`) that are all fixed.  The structure
`SelectionData` packages the constants with their printed ranges, and the predicate
`S.Selects d γ` is the printed
conclusion of `p.scale.selection` with `S`'s constants in
the printed places.  The statement in `HCPoly/Entry/Statements/ScaleSelection.lean` then reads
`∃ S : SelectionData, S.Selects d γ`, and the two fragment propositions take
`(S : SelectionData) (hS : S.Selects d γ)`.

The predicate adds no constant and no constraint that the display does not print.

Note, for the statements that will use it, that the printed `σ ∈ (0,ε]` of
`p.scale.selection` and the printed `0 < σ ≤ ε ≤ ε_0` of `p.initial.fixed.grid.scale` are
the same constraint, while `p.global.selection` narrows `ε` further to some
`ε(d,γ) ∈ (0,ε_0]`; that narrowing is part of that statement, not of this structure.

`η := cεσ` is a formula in the data and the chosen pair, so it is a function of the
structure — `S.eta ε σ` — and not a field.

-/

open HCPolySupport.HighContrast (CoeffSpace adaptedMean aspectRatio blockScale)
namespace HCPolySupport.HighContrast

open MeasureTheory
open scoped Matrix.Norms.L2Operator

/-- The selection constants of `p.scale.selection` as
one package: the outer constants `h`, `ε_0`, `c` depending only on `d` and `γ`, and the
inner constants `L(ε,σ)` and `B_0(ε,σ)`, each in its printed range.  This carries no
assertion about what the constants achieve; see the module docstring. -/
structure SelectionData where
  /-- The generation gap `h(d,γ) ∈ ℕ`. -/
  h : ℕ
  /-- The upper bound `ε_0(d,γ) ∈ (0,1)` on the step `ε`. -/
  eps0 : ℝ
  /-- The constant `c(d,γ) ∈ (0,1)` of `η = cεσ`. -/
  c : ℝ
  /-- The scale gap `L(ε,σ,d,γ) ∈ ℕ`. -/
  L : ℝ → ℝ → ℕ
  /-- The threshold `B_0(ε,σ,d,γ) ≥ 1`. -/
  B0 : ℝ → ℝ → ℝ
  /-- `ε_0 ∈ (0,1)`. -/
  eps0_mem : eps0 ∈ Set.Ioo (0 : ℝ) 1
  /-- `c ∈ (0,1)`. -/
  c_mem : c ∈ Set.Ioo (0 : ℝ) 1
  /-- `B_0(ε,σ) ≥ 1` for every `ε ∈ (0,ε_0]` and `σ ∈ (0,ε]`. -/
  one_le_B0 : ∀ ε σ : ℝ, ε ∈ Set.Ioc (0 : ℝ) eps0 → σ ∈ Set.Ioc (0 : ℝ) ε → 1 ≤ B0 ε σ

/-- The step `η = cεσ` of `p.scale.selection`, at the pair `(ε, σ)`. -/
@[expose]
def SelectionData.eta (S : SelectionData) (ε σ : ℝ) : ℝ :=
  S.c * ε * σ

/-- **The conclusion of Proposition `p.scale.selection`**
as a predicate on the selection data, at the dimension `d` and the coarse-ellipticity exponent
`γ`: "for every `ε ∈ (0,ε_0]` and `σ ∈ (0,ε]` … the following holds for every `B ≥ B_0`. Set
`η := cεσ`. … Exactly one of the following alternatives holds. … In every alternative,
[`e.renormalization.eccentricity.output`] and [`e.renormalization.output`]."

The display is read in the following terms:

* `C(d,γ)`, the constant of `e.renormalization.startup`, `e.renormalization.service` and
  `e.renormalization.transport.output`, depends on `d` and `γ` only; it is therefore existential
  at the outermost level, before `ε`, `σ`, `B`, the coefficient law and the geometry. The print
  writes `C(d,γ)` at each of the three places, so one constant serves all three.
* **The source lower scale is a standing hypothesis.** `C_src(d,γ)` is the constant
  of the source estimate (near `e.source.lower.scale`), and the sentence "From now on `j_*`
  satisfies
  `e.source.lower.scale`" (near `e.source.lower.scale`, printed immediately before this
  proposition) is the
  standing hypothesis `⌈C_src log_3(2K_{Ψ_S})⌉ ≤ j_*` carried here.  That sentence holds from
  then on, of the same kind as `3^{j_*} ≥ 2d` near `e.rounded.grid.bounds`: every later statement
  whose type
  mentions `j_*` carries it as a premise, whether or not its own display restates it, and whether
  or not its proof will use the source estimate. `C_src` is existential, in the same outermost
  group as `C`, since the manuscript fixes one such constant for the entire argument; a
  universally quantified `C_src` would be a different, stronger claim.
* The standing assumptions on the coefficient law (`t.polynomial.entry`) are quantified *inside*,
  after the constants: the printed argument lists `h(d,γ)`, `ε_0(d,γ)`, `c(d,γ)`, `L(ε,σ,d,γ)`,
  `B_0(ε,σ,d,γ)` say that none of them depends on the law.
* `𝔪 > 0` is `Matrix.PosDef`, `q = 𝒬(𝔪)` is `Geometry.explicitRoundedGrid jStar m`, `Π` is
  `aspectRatio E`, `Q` is `bigQ d γ`, `𝒫_q(m;n)` is `profile P γ q jStar n m`, `D_{q,j_*}` is
  `determinantDrift`, `Δ` is `detIncrement`, `Δ̂_h` is `synchCharge`, `m(F)` is
  `explicitCanonicalMetric`, `𝔪_+` is `geometryUpdate ε 𝔪 𝔪_*` and `η` is `S.eta ε σ`. The three
  local
  abbreviations `𝔪_*`, `𝔪_+`, `q_+` are `let`-bound exactly where the display introduces them.
* "Exactly one of the following alternatives holds" is the disjunction of the
  five guarded clauses the three alternatives contain (alternative 1 has two, alternative 3 has
  two). The guards are `k = n` against `k < n`, then `𝒫+D > η` against `𝒫+D ≤ η`, then
  `d^{-1}Δ̂_h(n) ≤ σ` against `> σ` and `d^{-1}Δ_{n,n+2L} ≤ εσ` against `> εσ`: pairwise
  contradictory and, under the hypothesis `k ≤ n`, exhaustive. "Exactly one" therefore follows
  from the disjunction and adds nothing to it.
* Each clause carries its own output tuple `(𝔪',q',k',n')` and, with it, the two conclusions
  "in every alternative" (`e.renormalization.eccentricity.output`,
  `e.renormalization.output`), instantiated at that tuple. The print states them once for all
  alternatives; stating them per clause is the same content with the tuple substituted.
* `½ log(|𝔪||𝔪^{-1}|)` and the ceilings match the printed display symbol for symbol, with
  Mathlib's L2 operator norm and the ceiling into `ℤ`.

This predicate asserts nothing about `d ≥ 2` or `γ ∈ [0,1)`; those are hypotheses of the
statements that use it. -/
@[expose]
def SelectionData.Selects (S : SelectionData) (d : ℕ) (γ : ℝ) : Prop :=
  (∃ C : ℝ, 0 < C ∧
    ∃ Csrc : ℝ, 0 < Csrc ∧
      (∀ ε σ : ℝ, ε ∈ Set.Ioc (0 : ℝ) S.eps0 → σ ∈ Set.Ioc (0 : ℝ) ε →
        ∀ B : ℝ, S.B0 ε σ ≤ B →
          ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
            (Src : CoeffSpace d → ℝ),
            IsProbabilityMeasure P →
            IsStationaryLaw P →
            IsUnitRangeLaw P →
            CoarseEllipticityDagger P γ E Ψ K Src →
            ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
              ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
                ∀ (m : Mat d), m.PosDef →
                  ∀ k n : ℤ, (jStar : ℤ) ≤ k → k ≤ n →
                    1 / 2 * Real.log (‖m‖ * ‖m⁻¹‖) ≤
                        ε / (S.L ε σ : ℝ) *
                          ((k : ℝ) - (jStar : ℝ) -
                            (⌈B * Real.logb 3 (2 + aspectRatio E)⌉ : ℤ)) →
                      (k = n →
                        profile P γ (Geometry.explicitRoundedGrid jStar m) jStar n n +
                          determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar n ≤ 1) →
                      (k < n → k + (S.h : ℤ) ≤ n) →
                      let mStar :=
                        explicitCanonicalMetric
                          (adaptedMean P (Geometry.explicitRoundedGrid jStar m)
                            (n + 2 * (S.L ε σ : ℤ)));
                      let mPlus := geometryUpdate ε m mStar;
                      HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar m)
                            (n + 2 * (S.L ε σ : ℤ)) ∪
                          HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar mPlus)
                            (n + (S.L ε σ : ℤ)) ⊆
                        HighContrast.centeredCube d (2 * (jStar : ℤ)) →
                      -- Alternative 1, same geometry, the start-up case `k = n`.
                      ((k = n ∧
                          profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k
                                (n + (S.h : ℤ)) +
                              determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar
                                (n + (S.h : ℤ)) ≤
                            C *
                              (profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k n +
                                determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar n +
                                Real.exp ((bigQ d γ : ℝ) *
                                  detIncrement P (Geometry.explicitRoundedGrid jStar m) n
                                    (n + (S.h : ℤ))) - 1)) ∧
                          1 / 2 * Real.log (‖m‖ * ‖m⁻¹‖) ≤
                            ε / (S.L ε σ : ℝ) *
                              ((k : ℝ) - (jStar : ℝ) -
                                (⌈B * Real.logb 3 (2 + aspectRatio E)⌉ : ℤ)) ∧
                          (k = n + (S.h : ℤ) →
                            profile P γ (Geometry.explicitRoundedGrid jStar m) jStar
                                  (n + (S.h : ℤ)) (n + (S.h : ℤ)) +
                                determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar
                                  (n + (S.h : ℤ)) ≤ 1) ∧
                          (k < n + (S.h : ℤ) → k + (S.h : ℤ) ≤ n + (S.h : ℤ))) ∨
                      -- Alternative 1, same geometry, the service case `k < n`.
                      ((k < n ∧
                          profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k n +
                              determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar n >
                            S.eta ε σ ∧
                          (d : ℝ)⁻¹ *
                              synchCharge P (Geometry.explicitRoundedGrid jStar m)
                                (S.h : ℤ) n ≤ σ ∧
                          profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k
                                (n + (S.h : ℤ)) +
                              determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar
                                (n + (S.h : ℤ)) ≤
                            1 / 4 *
                                (profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k n +
                                  determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar n) +
                              C *
                                synchCharge P (Geometry.explicitRoundedGrid jStar m)
                                  (S.h : ℤ) n) ∧
                          1 / 2 * Real.log (‖m‖ * ‖m⁻¹‖) ≤
                            ε / (S.L ε σ : ℝ) *
                              ((k : ℝ) - (jStar : ℝ) -
                                (⌈B * Real.logb 3 (2 + aspectRatio E)⌉ : ℤ)) ∧
                          (k = n + (S.h : ℤ) →
                            profile P γ (Geometry.explicitRoundedGrid jStar m) jStar
                                  (n + (S.h : ℤ)) (n + (S.h : ℤ)) +
                                determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar
                                  (n + (S.h : ℤ)) ≤ 1) ∧
                          (k < n + (S.h : ℤ) → k + (S.h : ℤ) ≤ n + (S.h : ℤ))) ∨
                      -- Alternative 2, change of geometry.
                      ((k < n ∧
                          profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k n +
                              determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar n ≤
                            S.eta ε σ ∧
                          (d : ℝ)⁻¹ *
                              detIncrement P (Geometry.explicitRoundedGrid jStar m) n
                                (n + 2 * (S.L ε σ : ℤ)) ≤ ε * σ ∧
                          profile P γ (Geometry.explicitRoundedGrid jStar mPlus) jStar
                                (n + (S.L ε σ : ℤ)) (n + (S.L ε σ : ℤ)) +
                              determinantDrift P γ (Geometry.explicitRoundedGrid jStar mPlus) jStar
                                (n + (S.L ε σ : ℤ)) ≤
                            C * σ ^ ((1 - γ) / 8)) ∧
                          1 / 2 * Real.log (‖mPlus‖ * ‖mPlus⁻¹‖) ≤
                            ε / (S.L ε σ : ℝ) *
                              (((n : ℝ) + (S.L ε σ : ℝ)) - (jStar : ℝ) -
                                (⌈B * Real.logb 3 (2 + aspectRatio E)⌉ : ℤ)) ∧
                          (n + (S.L ε σ : ℤ) = n + (S.L ε σ : ℤ) →
                            profile P γ (Geometry.explicitRoundedGrid jStar mPlus) jStar
                                  (n + (S.L ε σ : ℤ)) (n + (S.L ε σ : ℤ)) +
                                determinantDrift P γ (Geometry.explicitRoundedGrid jStar mPlus) jStar
                                  (n + (S.L ε σ : ℤ)) ≤ 1) ∧
                          (n + (S.L ε σ : ℤ) < n + (S.L ε σ : ℤ) →
                            n + (S.L ε σ : ℤ) + (S.h : ℤ) ≤ n + (S.L ε σ : ℤ))) ∨
                      -- Alternative 3, determinant obstruction, the synchronized case.
                      ((k < n ∧
                          profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k n +
                              determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar n >
                            S.eta ε σ ∧
                          (d : ℝ)⁻¹ *
                              synchCharge P (Geometry.explicitRoundedGrid jStar m)
                                (S.h : ℤ) n > σ) ∧
                          1 / 2 * Real.log (‖m‖ * ‖m⁻¹‖) ≤
                            ε / (S.L ε σ : ℝ) *
                              ((k : ℝ) - (jStar : ℝ) -
                                (⌈B * Real.logb 3 (2 + aspectRatio E)⌉ : ℤ)) ∧
                          (k = n + (S.h : ℤ) →
                            profile P γ (Geometry.explicitRoundedGrid jStar m) jStar
                                  (n + (S.h : ℤ)) (n + (S.h : ℤ)) +
                                determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar
                                  (n + (S.h : ℤ)) ≤ 1) ∧
                          (k < n + (S.h : ℤ) → k + (S.h : ℤ) ≤ n + (S.h : ℤ))) ∨
                      -- Alternative 3, determinant obstruction, the long case.
                      ((k < n ∧
                          profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k n +
                              determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar n ≤
                            S.eta ε σ ∧
                          (d : ℝ)⁻¹ *
                              detIncrement P (Geometry.explicitRoundedGrid jStar m) n
                                (n + 2 * (S.L ε σ : ℤ)) > ε * σ) ∧
                          1 / 2 * Real.log (‖m‖ * ‖m⁻¹‖) ≤
                            ε / (S.L ε σ : ℝ) *
                              ((k : ℝ) - (jStar : ℝ) -
                                (⌈B * Real.logb 3 (2 + aspectRatio E)⌉ : ℤ)) ∧
                          (k = n + 2 * (S.L ε σ : ℤ) →
                            profile P γ (Geometry.explicitRoundedGrid jStar m) jStar
                                  (n + 2 * (S.L ε σ : ℤ)) (n + 2 * (S.L ε σ : ℤ)) +
                                determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar
                                  (n + 2 * (S.L ε σ : ℤ)) ≤ 1) ∧
                          (k < n + 2 * (S.L ε σ : ℤ) →
                            k + (S.h : ℤ) ≤ n + 2 * (S.L ε σ : ℤ)))) ∧
      -- **C3**: the short bridge applied at the tolerance the proof uses,
      -- `δ = ε^{1/2}σ`, with `L = L(ε,σ)` unchanged (`p.scale.selection`).
      (∀ ε σ : ℝ, ε ∈ Set.Ioc (0 : ℝ) S.eps0 → σ ∈ Set.Ioc (0 : ℝ) ε →
        ∀ B : ℝ, S.B0 ε σ ≤ B →
          ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
            (Src : CoeffSpace d → ℝ),
            IsProbabilityMeasure P →
            IsStationaryLaw P →
            IsUnitRangeLaw P →
            CoarseEllipticityDagger P γ E Ψ K Src →
            ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
              ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
                ∀ (m mPlus : Mat d), m.PosDef → mPlus.PosDef →
                  ∀ k n : ℤ, (jStar : ℤ) ≤ k → k ≤ n →
                    HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar m)
                          (n + 2 * (S.L ε σ : ℤ)) ∪
                        HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar mPlus)
                          (n + (S.L ε σ : ℤ)) ⊆
                      HighContrast.centeredCube d (2 * (jStar : ℤ)) →
                    1 / 2 * Real.log (‖m‖ * ‖m⁻¹‖) ≤
                        ε / (S.L ε σ : ℝ) *
                          ((k : ℝ) - (jStar : ℝ) -
                            (⌈B * Real.logb 3 (2 + aspectRatio E)⌉ : ℤ)) →
                      k + 2 * (bigQ d γ : ℤ) ≤ n →
                      projectiveDistance m mPlus ≤ 1 →
                      profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k n +
                            determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar n +
                          detIncrement P (Geometry.explicitRoundedGrid jStar m) n
                            (n + 2 * (S.L ε σ : ℤ)) ≤
                        (S.c + (d : ℝ)) * ε * σ →
                        BlockMatLoewnerLE
                            (blockScale (1 - Real.sqrt ε * σ)
                              (adaptedMean P (Geometry.explicitRoundedGrid jStar m)
                                (n + 2 * (S.L ε σ : ℤ))))
                            (adaptedMean P (Geometry.explicitRoundedGrid jStar mPlus)
                              (n + (S.L ε σ : ℤ))) ∧
                          BlockMatLoewnerLE
                            (adaptedMean P (Geometry.explicitRoundedGrid jStar mPlus)
                              (n + (S.L ε σ : ℤ)))
                            (blockScale (1 + Real.sqrt ε * σ)
                              (adaptedMean P (Geometry.explicitRoundedGrid jStar m)
                                (n + 2 * (S.L ε σ : ℤ)))))) ∧
    -- **C1**: the generation gap is at least the printed `2Q`
    -- (near `p.scale.selection`, `s.polynomial.entry.proof`), an inequality, not a selection.
    2 * bigQ d γ ≤ S.h ∧
    -- **C2a**: the scale gap is a length (`p.scale.selection`, `e.bridge.length.choice`).
    (∀ ε σ : ℝ, ε ∈ Set.Ioc (0 : ℝ) S.eps0 → σ ∈ Set.Ioc (0 : ℝ) ε → 1 ≤ S.L ε σ) ∧
    -- **C2b**: the scale gap clears the short bridge's length threshold at the
    -- tolerance `ε^{1/2}σ` (`p.scale.selection`); the bridge's own
    -- `L_0` is not nameable here, so it is existential, as `C_src` already is.
    ∃ Lbr : ℕ, ∀ ε σ : ℝ, ε ∈ Set.Ioc (0 : ℝ) S.eps0 → σ ∈ Set.Ioc (0 : ℝ) ε →
      (Lbr : ℤ) + ⌈Real.logb 3 (Real.sqrt ε * σ)⁻¹⌉ ≤ (S.L ε σ : ℤ)

end HCPolySupport.HighContrast
