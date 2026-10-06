/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Setup.AdaptedGridCells
public import LeanPool.HighContrastHomogenization.Setup.SourceObjects
public import LeanPool.HighContrastHomogenization.Entry.Geometry.RoundedGridBasic
public import LeanPool.HighContrastHomogenization.Entry.TwoGridWhitney

/-!
# High-contrast homogenization: Entry.Statements.TwoGridWhitney

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Lemma `l.two.grid.whitney` — Whitney partitions between adapted grids

`l.two.grid.whitney`, the paper's Lemma "Whitney partitions between adapted grids",
transcribed from the printed display.

Reading of the display, stated here so that no divergence is silent:

* `C(d,K_0)` depends on the dimension and on `K_0` only, so its quantifier follows `K_0` and
  precedes `γ`, `K_{Ψ_S}`, `j_*`, the matrices, `j` and `ℓ`; in particular it is independent of
  `γ`. `0 < C` is written for the printed `C < ∞` of a constant used as an upper bound, as the
  root statement does.
* **The source lower scale is a standing hypothesis.** Near `e.source.lower.scale` reads "From now
  on `j_*` satisfies `e.source.lower.scale`", i.e. `j_* ≥ ⌈C_src(d,γ) log_3(2K_{Ψ_S})⌉` with
  `C_src` the constant of the source estimate (near `e.source.lower.scale`). That sentence stands
  from there
  onward, of the same kind as `3^{j_*} ≥ 2d` near `e.rounded.grid.bounds`: every later statement
  whose type
  mentions `j_*` carries it as a premise, whether or not its own display restates it, and whether
  or not its proof will use the source estimate. `q = 𝒬(𝔪)` and `q' = 𝒬(𝔪')` do mention `j_*`,
  so this display, which does not restate the condition, carries it. `C_src` is the source
  constant **family** at the fixed dimension, `C_src : ℝ → ℝ` evaluated at `γ`, chosen before
  `K_0` so that `C(d,K_0)` stays independent of `γ`; `γ ∈ [0,1)` and the growth witness
  `K_{Ψ_S} > 1` are then universally quantified, exactly as the manuscript's standing data.
* `𝔪, 𝔪' > 0` are `Matrix.PosDef`, `q = 𝒬(𝔪)` and `q' = 𝒬(𝔪')` are `Geometry.explicitRoundedGrid`,
  `K(q,q')` is `gridRatio` (near `s.geometry.transport`), the standing `3^{j_*} ≥ 2d` near
  `e.rounded.grid.bounds`
  is `hj` and the standing `d ≥ 2` of `t.polynomial.entry` is `hd`. The constructions and the
  estimates
  are pure geometry: no coefficient law occurs in them, so none of the standing probabilistic
  assumptions is carried. `γ` and `K_{Ψ_S}` occur only in the standing source-scale premise on
  `j_*` above; they are bare reals in the printed ranges, and no measure, no ellipticity
  hypothesis and no random object enters this statement.
* The two constructions are the definition layer's `HCPoly/Entry/Setup/AdaptedGridCells.lean`: the
maximal
  adapted cubes of the `q`-grid contained in a set with generations at most `j−ℓ` are
  `IsMaximalAdaptedCellIn · q (j−ℓ) r w`, their centers `𝒵_r(W)` are
  `maximalAdaptedCellCenters`, and the first family of (ii) — all `q'`-cubes of generation
  `j−ℓ` contained in `W` — is `adaptedCoveredPart W q' (j−ℓ)`, with the uncovered part
  `adaptedUncoveredPart W q' (j−ℓ)` in which (ii) selects.
* "partition `W` up to a null set" is, as in the `l.source.whitney`: each selected cube
  lies in `W` (in (ii): in the uncovered part), distinct selected cubes are disjoint, and what
  is left of `W` after removing their union (in (ii): after removing the covered part as well)
  is Lebesgue-null. That the selected cubes of (ii) are disjoint from the covered part is
  automatic — they lie in its complement — and is not restated.
* The print's `#𝒵_r(W)` presupposes each family finite; as in `l.source.whitney` the finiteness
  is asserted (`∃ hfin`, one proof per admissible generation) and the printed counts and sums are
  then taken over `hfin.toFinset`. `Σ_{r ≤ j−ℓ}` is the unconditional sum over all integers
  `r ≤ j−ℓ`, written as a `tsum` over that subtype, since the print sums over an infinite range.
* `|⋄_r^q|/|W|` is the ratio of Lebesgue volumes as a real number, and every printed power of `3`
  is a real power. The final paper states the first estimate of
  `e.two.grid.whitney.counts` for `r < j−ℓ`; the Lean theorem also proves it
  at the top generation `r = j−ℓ`. The cardinality bounds retain the printed
  ranges.

The proof applies `HCPolySupport.HighContrast.Entry.two_grid_whitney`
(`HCPoly/Entry/TwoGridWhitney.lean`).
-/

open HCPolySupport.HighContrast (gridRatio)
namespace HCPolySupport.HighContrast

open MeasureTheory

/-- **Lemma `l.two.grid.whitney`**. There is a source-constant
family `C_src(d,·)` such that, for every `K_0 ≥ 1` there is `C(d,K_0)` for which, whenever `j_*`
satisfies `e.source.lower.scale` (standing near `e.source.lower.scale`), `𝔪,𝔪' > 0` with
`q = 𝒬(𝔪)`, `q' = 𝒬(𝔪')` and `K(q,q') ≤ K_0`, and `j ∈ ℤ`, `ℓ ≥ 1`: (i) in
`W = y + ⋄_j^{q'}` the maximal `q`-cubes of generations at most `j−ℓ` partition `W` up to a null
set with the printed counts and volume sums; (ii) in `W = y + ⋄_j^q`
the `q'`-cubes of generation `j−ℓ` contained in `W` together with the maximal `q`-cubes of the
uncovered part partition `W` up to a null set with the printed volume sum. -/
theorem two_grid_whitney
    (d : ℕ) (hd : 2 ≤ d) :
    ∃ Csrc : ℝ → ℝ, (∀ γ : ℝ, γ ∈ Set.Ico (0 : ℝ) 1 → 0 < Csrc γ) ∧
      ∀ K₀ : ℝ, 1 ≤ K₀ →
      ∃ C : ℝ, 0 < C ∧
      ∀ γ : ℝ, γ ∈ Set.Ico (0 : ℝ) 1 →
      ∀ K : ℝ, 1 < K →
      ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
        ⌈Csrc γ * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
        ∀ (m m' : Mat d), m.PosDef → m'.PosDef →
          gridRatio (Geometry.explicitRoundedGrid jStar m) (Geometry.explicitRoundedGrid jStar m') ≤ K₀ →
            ∀ (j : ℤ) (ℓ : ℕ), 1 ≤ ℓ →
              (∀ y ∈ adaptedLatticeAtScale (Geometry.explicitRoundedGrid jStar m') j,
                ∃ hfin : ∀ r : ℤ, r ≤ j - (ℓ : ℤ) →
                    (maximalAdaptedCellCenters
                      (HighContrast.adaptedCellTranslate (Geometry.explicitRoundedGrid jStar m') j y)
                      (Geometry.explicitRoundedGrid jStar m) (j - (ℓ : ℤ)) r).Finite,
                  (∀ (r : ℤ) (w : Fin d → ℤ),
                      IsMaximalAdaptedCellIn
                        (HighContrast.adaptedCellTranslate (Geometry.explicitRoundedGrid jStar m') j y)
                        (Geometry.explicitRoundedGrid jStar m) (j - (ℓ : ℤ)) r w →
                      adaptedCellAtCenter (Geometry.explicitRoundedGrid jStar m) r w ⊆
                        HighContrast.adaptedCellTranslate (Geometry.explicitRoundedGrid jStar m') j y) ∧
                    Set.PairwiseDisjoint
                      {p : ℤ × (Fin d → ℤ) |
                        IsMaximalAdaptedCellIn
                          (HighContrast.adaptedCellTranslate (Geometry.explicitRoundedGrid jStar m') j y)
                          (Geometry.explicitRoundedGrid jStar m) (j - (ℓ : ℤ)) p.1 p.2}
                      (fun p => adaptedCellAtCenter (Geometry.explicitRoundedGrid jStar m) p.1 p.2) ∧
                    volume
                        (HighContrast.adaptedCellTranslate (Geometry.explicitRoundedGrid jStar m') j y \
                          ⋃ p ∈ {p : ℤ × (Fin d → ℤ) |
                              IsMaximalAdaptedCellIn
                                (HighContrast.adaptedCellTranslate
                                  (Geometry.explicitRoundedGrid jStar m') j y)
                                (Geometry.explicitRoundedGrid jStar m) (j - (ℓ : ℤ)) p.1 p.2},
                            adaptedCellAtCenter (Geometry.explicitRoundedGrid jStar m) p.1 p.2) = 0 ∧
                    (∀ r : ℤ, r ≤ j - (ℓ : ℤ) →
                      (volume (HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar m) r)).toReal /
                          (volume (HighContrast.adaptedCellTranslate
                            (Geometry.explicitRoundedGrid jStar m') j y)).toReal ≤
                        C * (3 : ℝ) ^ (-(d : ℝ) * ((j : ℝ) - (r : ℝ)))) ∧
                    (((hfin (j - (ℓ : ℤ)) le_rfl).toFinset.card : ℝ) ≤
                      C * (3 : ℝ) ^ ((d : ℝ) * (ℓ : ℝ))) ∧
                    (∀ (r : ℤ) (hr : r < j - (ℓ : ℤ)),
                      ((hfin r hr.le).toFinset.card : ℝ) ≤
                        C * (3 : ℝ) ^ (((d : ℝ) - 1) * ((j : ℝ) - (r : ℝ)))) ∧
                    (∑' r : {r : ℤ // r ≤ j - (ℓ : ℤ)},
                        ∑ _z ∈ (hfin r.1 r.2).toFinset,
                          (volume (HighContrast.adaptedCell
                              (Geometry.explicitRoundedGrid jStar m) r.1)).toReal /
                            (volume (HighContrast.adaptedCellTranslate
                              (Geometry.explicitRoundedGrid jStar m') j y)).toReal) = 1 ∧
                    (∀ (r : ℤ) (hr : r < j - (ℓ : ℤ)),
                      ∑ _z ∈ (hfin r hr.le).toFinset,
                          (volume (HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar m) r)).toReal /
                            (volume (HighContrast.adaptedCellTranslate
                              (Geometry.explicitRoundedGrid jStar m') j y)).toReal ≤
                        C * (3 : ℝ) ^ ((r : ℝ) - (j : ℝ)))) ∧
                (∀ y ∈ adaptedLatticeAtScale (Geometry.explicitRoundedGrid jStar m) j,
                  ∃ hfin : ∀ r : ℤ, r ≤ j - (ℓ : ℤ) →
                      (maximalAdaptedCellCenters
                        (adaptedUncoveredPart
                          (HighContrast.adaptedCellTranslate (Geometry.explicitRoundedGrid jStar m) j y)
                          (Geometry.explicitRoundedGrid jStar m') (j - (ℓ : ℤ)))
                        (Geometry.explicitRoundedGrid jStar m) (j - (ℓ : ℤ)) r).Finite,
                    (∀ (r : ℤ) (w : Fin d → ℤ),
                        IsMaximalAdaptedCellIn
                          (adaptedUncoveredPart
                            (HighContrast.adaptedCellTranslate (Geometry.explicitRoundedGrid jStar m) j y)
                            (Geometry.explicitRoundedGrid jStar m') (j - (ℓ : ℤ)))
                          (Geometry.explicitRoundedGrid jStar m) (j - (ℓ : ℤ)) r w →
                        adaptedCellAtCenter (Geometry.explicitRoundedGrid jStar m) r w ⊆
                          adaptedUncoveredPart
                            (HighContrast.adaptedCellTranslate (Geometry.explicitRoundedGrid jStar m) j y)
                            (Geometry.explicitRoundedGrid jStar m') (j - (ℓ : ℤ))) ∧
                      Set.PairwiseDisjoint
                        {p : ℤ × (Fin d → ℤ) |
                          IsMaximalAdaptedCellIn
                            (adaptedUncoveredPart
                              (HighContrast.adaptedCellTranslate (Geometry.explicitRoundedGrid jStar m) j y)
                              (Geometry.explicitRoundedGrid jStar m') (j - (ℓ : ℤ)))
                            (Geometry.explicitRoundedGrid jStar m) (j - (ℓ : ℤ)) p.1 p.2}
                        (fun p => adaptedCellAtCenter (Geometry.explicitRoundedGrid jStar m) p.1 p.2) ∧
                      volume
                          (HighContrast.adaptedCellTranslate (Geometry.explicitRoundedGrid jStar m) j y \
                            (adaptedCoveredPart
                                (HighContrast.adaptedCellTranslate
                                  (Geometry.explicitRoundedGrid jStar m) j y)
                                (Geometry.explicitRoundedGrid jStar m') (j - (ℓ : ℤ)) ∪
                              ⋃ p ∈ {p : ℤ × (Fin d → ℤ) |
                                  IsMaximalAdaptedCellIn
                                    (adaptedUncoveredPart
                                      (HighContrast.adaptedCellTranslate
                                        (Geometry.explicitRoundedGrid jStar m) j y)
                                      (Geometry.explicitRoundedGrid jStar m') (j - (ℓ : ℤ)))
                                    (Geometry.explicitRoundedGrid jStar m) (j - (ℓ : ℤ)) p.1 p.2},
                                adaptedCellAtCenter (Geometry.explicitRoundedGrid jStar m) p.1 p.2)) = 0 ∧
                      (∀ (r : ℤ) (hr : r ≤ j - (ℓ : ℤ)),
                        ∑ _z ∈ (hfin r hr).toFinset,
                            (volume (HighContrast.adaptedCell
                                (Geometry.explicitRoundedGrid jStar m) r)).toReal /
                              (volume (HighContrast.adaptedCellTranslate
                                (Geometry.explicitRoundedGrid jStar m) j y)).toReal ≤
                          C * (3 : ℝ) ^ ((r : ℝ) - (j : ℝ)))) := by exact HCPolySupport.HighContrast.Entry.two_grid_whitney d hd

end HCPolySupport.HighContrast
