/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Setup.SelectionData
public import LeanPool.HighContrastHomogenization.Entry.GlobalSelection

/-!
# High-contrast homogenization: Entry.Statements.GlobalSelection

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Proposition `p.global.selection` — global selection

`p.global.selection`, the paper's Proposition "Global
selection", transcribed from the printed display.

Reading of the display, stated here so that no divergence is silent:

* "choose `L`, `η`, and `B_0` as in Proposition `p.scale.selection`" is `(S : SelectionData)`
  together with `(hS : S.Selects d γ)`, at the pair `(ε,σ)` this proposition
  chooses: `L = S.L ε σ`, `η = S.eta ε σ`, `B_0 = S.B0 ε σ`. Only `B_0` occurs in the printed
  statement; `L` and `η` occur in its proof.
* `ε(d,γ) ∈ (0,ε_0]` is existential and outermost, and `σ ∈ (0,ε]`; `H ≥ max{4,h}` is an
  integer.
* **The source lower scale is a standing hypothesis.** `C_src(d,γ)` is the constant
  of the source estimate (near `e.source.lower.scale`), existential in the same outermost group,
  exactly as
  in `p.initial.fixed.grid.scale`. This fragment prints the source term in its own lower-scale
  display, and near `e.source.lower.scale` ("From now on `j_*` satisfies `e.source.lower.scale`")
  makes the
  condition standing from there onward in any case; that reading applies to every
  statement whose type mentions `j_*`, whether or not its display restates the condition
  and whether or not its proof uses the source estimate. This is the fragment in which the
  standing condition is discharged by the choice of `j_*`.
* The display writes three constants with different argument lists: `C(H,σ,d,γ)` (the one in
  the lower bound on `j_*`, in `⌈(B+C)log_3(2+Π)⌉` and in `(2+Π)^C`), and `C(H,d,γ)` in
  `e.global.selection.profile`, which does **not** depend on `σ`. They are two quantifiers here:
  `Cprof` is bound before `σ`, `C` after it. Conflating them would weaken the profile bound.
* `F` is a "deterministic positive block": a `BlockMat d` that is symmetric and
  `Book.Ch02.BlockPosDef`, the block analogue of Mathlib's `Matrix.PosDef`, whose symmetry the
  manuscript's positive matrices always have. `𝔪 = m(F)` is `explicitCanonicalMetric F` and
  `q = 𝒬(𝔪)` is `Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)`, both written out
  at their
  occurrences rather than named.
* `Π` is `aspectRatio E`, `K_{Ψ_S}` is `K`, `𝒫_q(m;n)` is `profile P γ q jStar n m`,
  `D_{q,j_*}` is `determinantDrift`, `Δ^q_{s,t}` is `detIncrement`, `□_{2j_*}` is
  `HighContrast.centeredCube d (2 j_*)`, and `ε^{1/2}` is `Real.sqrt ε`. `(|𝔪||𝔪^{-1}|)^{1/2}` is
  transcribed as the printed real power of the product of the two L2 operator norms.
* `s < t` is printed ("generations `s < t`") and is carried, although it also follows from
  `t = s + H` and `H ≥ 4`.
* The display names no hypothesis on the coefficient law; the manuscript's standing assumptions
  are in force throughout and are carried in the binder order of the root statement
  `HCPoly/Entry/Statements/PolynomialEntry.lean`, after the constants, whose printed argument
  lists say they
  do not depend on the law.

The proof is one application of `HCPolySupport.HighContrast.Entry.global_selection`
(`HCPoly/Entry/GlobalSelection.lean`) to the binders of the statement.
-/

open HCPolySupport.HighContrast (CoeffSpace adaptedMean aspectRatio blockScale)
namespace HCPolySupport.HighContrast

open MeasureTheory
open scoped Matrix.Norms.L2Operator

/-- **Proposition `p.global.selection`**.
There is `ε(d,γ) ∈ (0,ε_0]` such that, for an integer `H ≥ max{4,h}` and `σ ∈ (0,ε]` with `L`,
`η`, `B_0` as in `p.scale.selection`, there is `C(H,σ,d,γ)` such that, for every `B ≥ B_0` and
every `j_*` above the printed threshold, there are a deterministic positive block `F`,
`𝔪 = m(F)`, `q = 𝒬(𝔪)` and generations `s < t` with `t = s+H`, the printed scale bounds,
`⋄_t^q ⊆ □_{2j_*}`, `(1−ε^{1/2}σ)F ≤ 𝐀hom_{s,q} ≤ (1+ε^{1/2}σ)F`, `d^{-1}Δ^q_{s,t} < σ`, the
printed profile bound and `(|𝔪||𝔪^{-1}|)^{1/2} ≤ (2+Π)^C`. -/
theorem global_selection
    (d : ℕ) (hd : 2 ≤ d)
    (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (S : SelectionData) (hS : S.Selects d γ) :
    ∃ ε : ℝ, ε ∈ Set.Ioc (0 : ℝ) S.eps0 ∧
      ∃ Csrc : ℝ, 0 < Csrc ∧
        ∀ H : ℕ, max 4 S.h ≤ H →
          ∃ Cprof : ℝ, 0 < Cprof ∧
            ∀ σ : ℝ, σ ∈ Set.Ioc (0 : ℝ) ε →
              ∃ C : ℝ, 0 < C ∧
                ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
                  (Src : CoeffSpace d → ℝ),
                  IsProbabilityMeasure P →
                  IsStationaryLaw P →
                  IsUnitRangeLaw P →
                  CoarseEllipticityDagger P γ E Ψ K Src →
                  ∀ B : ℝ, S.B0 ε σ ≤ B →
                    ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
                      ⌈C * (B + 1) * Real.logb 3 (2 + aspectRatio E) +
                          Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
                        ∃ (F : BlockMat d) (s t : ℤ),
                          IsSymmetricBlockMat F ∧
                            Book.Ch02.BlockPosDef F ∧
                            s < t ∧
                            t = s + (H : ℤ) ∧
                            (jStar : ℤ) + ⌈B * Real.logb 3 (2 + aspectRatio E)⌉ ≤ s ∧
                            t ≤ (jStar : ℤ) + ⌈(B + C) * Real.logb 3 (2 + aspectRatio E)⌉ ∧
                            HighContrast.adaptedCell
                                (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) t ⊆
                              HighContrast.centeredCube d (2 * (jStar : ℤ)) ∧
                            BlockMatLoewnerLE (blockScale (1 - Real.sqrt ε * σ) F)
                              (adaptedMean P
                                (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) s) ∧
                            BlockMatLoewnerLE
                              (adaptedMean P
                                (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) s)
                              (blockScale (1 + Real.sqrt ε * σ) F) ∧
                            (d : ℝ)⁻¹ *
                                detIncrement P
                                  (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) s t < σ ∧
                            max
                                  (max
                                    (profile P γ
                                      (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) jStar
                                      s s)
                                    (profile P γ
                                      (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) jStar
                                      s t))
                                  (profile P γ
                                    (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) jStar
                                    t t) +
                                determinantDrift P γ
                                  (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) jStar s +
                                determinantDrift P γ
                                  (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) jStar t ≤
                              Cprof * σ ^ ((1 - γ) / 8) ∧
                            (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) ^ ((1 : ℝ) / 2) ≤
                              (2 + aspectRatio E) ^ C := by exact HCPolySupport.HighContrast.Entry.global_selection d hd γ hγ S hS

end HCPolySupport.HighContrast
