/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Setup.SelectionData
public import LeanPool.HighContrastHomogenization.Entry.InitialFixedGridScale

/-!
# High-contrast homogenization: Entry.Statements.InitialFixedGridScale

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Proposition `p.initial.fixed.grid.scale` — Euclidean initialization

`p.initial.fixed.grid.scale`, the paper's Proposition "Euclidean
initialization", transcribed from the printed display.

Reading of the display, stated here so that no divergence is silent:

* "Fix `h(d,γ) ∈ ℕ` and `ε_0(d,γ) ∈ (0,1)` from Proposition `p.scale.selection` … and fix
  `L(ε,σ,d,γ) ∈ ℕ` and `B_0(ε,σ,d,γ) ≥ 1` furnished there" is `(S : SelectionData)` together
  with `(hS : S.Selects d γ)` — the constants *and* the property that makes them the ones that
  proposition furnishes. `L` and `B_0` are `S.L ε σ` and `S.B0 ε σ`.
* **The source lower scale is a standing hypothesis.** "Let `j_*` satisfy
  `e.source.lower.scale`" is `⌈C_src log_3(2K_{Ψ_S})⌉ ≤ j_*`, with `C_src` the constant of the
  source estimate (near `e.source.lower.scale`). This fragment restates the condition, and near
  `e.source.lower.scale`
  ("From now on `j_*` satisfies `e.source.lower.scale`") makes it standing from that line onward
  in any case; records that
  reading and applies it to every statement whose type mentions `j_*`, whether or not its
  display restates the condition and whether or not its proof uses the source estimate. `C_src`
  is existentially bound, after `γ` and the selection data and before `η_init`: the manuscript
  fixes one such constant for the whole argument at `(d,γ)`, so a universally quantified `C_src`
  would be a different, stronger claim.
* `C(d,γ,η_init) < ∞` is bound after `η_init` and before `ε`, `σ`, the coefficient law, `j_*`
  and `B`, which is what its printed argument list says. The printed order lists
  `0 < σ ≤ ε ≤ ε_0` before `η_init`; since `C` does not depend on `ε` or `σ`, its quantifier
  precedes theirs, and the conclusion depends on `ε, σ` only through `B ≥ B_0(ε,σ)`.
* `C(d)` of `e.initial.geometry.bounds` is a *second* constant, and its printed argument list is
  `d` alone: it depends on neither `γ`, nor the selection data, nor `η_init`, `ε`, `σ`, the
  coefficient law, `j_*` or `B`. It is therefore chosen as `Cgeom` **immediately after `d` and
  `hd`, before `γ` and `S`**, so that one `Cgeom` serves every admissible `γ` and every furnished
  selection package; `γ`, `hγ`, `S` and `hS` are quantified inside its scope. Choosing it after
  `γ` would assert less than the display does.
* The Euclidean grid `Id` is `(1 : Mat d)`: the print writes `𝒫_{Id}`, `D_{Id,j_*}` and
  `𝐀hom_{n_0,Id}` with the grid `Id` itself (`𝒬(Id) = Id`, the fragment's first proof line).
* `R := j_* + ⌈B log_3(2+Π)⌉` is written out at its two occurrences rather than named, `Π` is
  `aspectRatio E`, `𝐑` is `blockSwap d`, `m(F)` is `explicitCanonicalMetric`, `d_pr` is
  `projectiveDistance`, `𝒫_q(m;n)` is `profile P γ q jStar n m` and `D_{q,j_*}` is
  `determinantDrift`. `𝐑𝐄^{-1}𝐑` is the matrix product through `toFullBlockMat`.
* The generation `n_0` is an integer, as every generation in the manuscript is; "deterministic"
  is the content of its being a single integer rather than a random variable.
* The display names no hypothesis on the coefficient law; the manuscript's standing assumptions
  are in force throughout and are carried in the binder order of the root statement
  `HCPoly/Entry/Statements/PolynomialEntry.lean`.

The proof is one application of `HCPolySupport.HighContrast.Entry.initial_fixed_grid_scale`
(`HCPoly/Entry/InitialFixedGridScale.lean`) to the binders of the statement.
-/

open HCPolySupport.HighContrast (CoeffSpace adaptedMean aspectRatio blockScale)
namespace HCPolySupport.HighContrast

open MeasureTheory

/-- **Proposition `p.initial.fixed.grid.scale`**.
There is `C(d)` such that, for every `γ`, with `h`, `ε_0`, `L`, `B_0` furnished by
`p.scale.selection`, `0 < σ ≤ ε ≤ ε_0` and `j_*` above the source scale: for every
`η_init ∈ (0,1]` there is `C(d,γ,η_init)` such that, for every
`B ≥ B_0`, some deterministic generation `n_0` satisfies `R ≤ n_0 ≤ R + ⌈C log_3(2+Π)⌉` with
`R = j_* + ⌈B log_3(2+Π)⌉` and `𝒫_Id(n_0;n_0) + D_{Id,j_*}(n_0) ≤ η_init`; moreover
`½𝐑𝐄^{-1}𝐑 ≤ 𝐀hom_{n_0,Id} ≤ 2𝐄` and `d_pr([Id],[m(𝐀hom_{n_0,Id})]) ≤ C(d) log(2+4Π)`. -/
theorem initial_fixed_grid_scale
    (d : ℕ) (hd : 2 ≤ d) :
    ∃ Cgeom : ℝ, 0 < Cgeom ∧
      ∀ γ : ℝ, γ ∈ Set.Ico (0 : ℝ) 1 →
      ∀ S : SelectionData, S.Selects d γ →
      ∃ Csrc : ℝ, 0 < Csrc ∧
        ∀ ηinit : ℝ, ηinit ∈ Set.Ioc (0 : ℝ) 1 →
          ∃ C : ℝ, 0 < C ∧
            ∀ ε σ : ℝ, 0 < σ → σ ≤ ε → ε ≤ S.eps0 →
              ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
                (Src : CoeffSpace d → ℝ),
                IsProbabilityMeasure P →
                IsStationaryLaw P →
                IsUnitRangeLaw P →
                CoarseEllipticityDagger P γ E Ψ K Src →
                ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
                  ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
                    ∀ B : ℝ, S.B0 ε σ ≤ B →
                      ∃ n₀ : ℤ,
                        (jStar : ℤ) + ⌈B * Real.logb 3 (2 + aspectRatio E)⌉ ≤ n₀ ∧
                          n₀ ≤ (jStar : ℤ) + ⌈B * Real.logb 3 (2 + aspectRatio E)⌉ +
                            ⌈C * Real.logb 3 (2 + aspectRatio E)⌉ ∧
                          profile P γ (1 : Mat d) jStar n₀ n₀ +
                              determinantDrift P γ (1 : Mat d) jStar n₀ ≤ ηinit ∧
                          BlockMatLoewnerLE
                            (blockScale (1 / 2)
                              (ofFullBlockMat
                                (toFullBlockMat (blockSwap d) * (toFullBlockMat E)⁻¹ *
                                  toFullBlockMat (blockSwap d))))
                            (adaptedMean P (1 : Mat d) n₀) ∧
                          BlockMatLoewnerLE (adaptedMean P (1 : Mat d) n₀) (blockScale 2 E) ∧
                          projectiveDistance (1 : Mat d)
                              (explicitCanonicalMetric (adaptedMean P (1 : Mat d) n₀)) ≤
                            Cgeom * Real.log (2 + 4 * aspectRatio E) := by
  exact HCPolySupport.HighContrast.Entry.initial_fixed_grid_scale d hd


end HCPolySupport.HighContrast
