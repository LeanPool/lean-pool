/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Setup.GeometryUpdate
public import LeanPool.HighContrastHomogenization.Setup.SourceObjects
public import LeanPool.HighContrastHomogenization.Entry.Geometry.RoundedGridBasic
public import LeanPool.HighContrastHomogenization.Entry.ProjectiveStep

/-!
# High-contrast homogenization: Entry.Statements.ProjectiveStep

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Lemma `l.projective.step` — the projective step

`l.projective.step`, the paper's Lemma "The projective step", transcribed from the
printed display.

Reading of the display, stated here so that no divergence is silent:

* `𝔪 > 0` and `𝔪_* > 0` are `Matrix.PosDef` (Mathlib's positive definiteness, which includes
  symmetry — the manuscript's positive matrices are symmetric).
* "define `𝔪_+` by `e.renormalization.geometry.update`" is `geometryUpdate ε m mStar` of
  `HCPoly/Entry/Setup/GeometryUpdate.lean`, the rendering of `e.renormalization.geometry.update`,
  including
  its case split on the projective classes.
* `d_pr([𝔪],[𝔪_+])` is `projectiveDistance m (geometryUpdate ε m mStar)`: the definition takes
  the two matrices and is the printed function of their classes
  (`e.scale.selection.projective.distance`).
* `½ log(|𝔪||𝔪^{-1}|)` is transcribed literally rather than through the eccentricity `𝔢(𝔪)`
  near `s.geometry.transport`, because this display writes the logarithm out; `|·|` is Mathlib's L2
  operator norm.
* `𝒬(𝔪)` is `Geometry.explicitRoundedGrid jStar m`, whose entries depend on `j_*`; the standing
  constraint `3^{j_*} ≥ 2d` near `e.rounded.grid.bounds` is the hypothesis `hj`, and the ambient
  dimension is
  the standing `d ≥ 2` of `t.polynomial.entry`. `K(q,q')` is `gridRatio`.
* **The source lower scale is a standing hypothesis.** Near `e.source.lower.scale` reads "From now
  on `j_*` satisfies `e.source.lower.scale`", i.e. `j_* ≥ ⌈C_src(d,γ) log_3(2K_{Ψ_S})⌉` with
  `C_src` the constant of the source estimate (near `e.source.lower.scale`). That sentence stands
  from there
  onward, of the same kind as `3^{j_*} ≥ 2d` near `e.rounded.grid.bounds`: every later statement
  whose type
  mentions `j_*` carries it as a premise, whether or not its own display restates it, and whether
  or not its proof will use the source estimate. `𝒬(𝔪)` and `𝒬(𝔪_+)` mention `j_*`, so this
  display, which does not restate the condition, carries it. `C_src` is the source constant
  **family** at the fixed dimension, `C_src : ℝ → ℝ` evaluated at `γ`; `γ ∈ [0,1)` and the growth
  witness `K_{Ψ_S} > 1` are then universally quantified. No coefficient law, no measure and no
  ellipticity hypothesis enters this statement: `γ` and `K_{Ψ_S}` are bare reals in the printed
  ranges, and the conclusions remain pure geometry.
* `C(d)` depends on the dimension alone, so its quantifier precedes `γ`, `K_{Ψ_S}`, `j_*`, the
  matrices and `ε`; in particular it is independent of `γ`. The two unconditional conclusions are
  inside its scope, which weakens nothing. The third conclusion is guarded by the printed
  `0 < ε ≤ 1`; `0 < ε` is already a hypothesis, so the guard carried there is `ε ≤ 1`.

The proof applies `HCPolySupport.HighContrast.Entry.projective_step`
(`HCPoly/Entry/ProjectiveStep.lean`).
-/

open HCPolySupport.HighContrast (gridRatio)
namespace HCPolySupport.HighContrast

open scoped Matrix.Norms.L2Operator

/-- **Lemma `l.projective.step`**. There are a source-constant
family `C_src(d,·)` and `C(d)` such that, whenever `j_*` satisfies `e.source.lower.scale`
(standing near `e.source.lower.scale`), `𝔪, 𝔪_* > 0`, `ε > 0`, `𝔪_+` is defined by
`e.renormalization.geometry.update`, `q = 𝒬(𝔪)` and `q_+ = 𝒬(𝔪_+)`:
`d_pr([𝔪],[𝔪_+]) ≤ ε`; moreover `½ log(|𝔪_+||𝔪_+^{-1}|) ≤ ½ log(|𝔪||𝔪^{-1}|) + ε`; and if
`0 < ε ≤ 1`, then `K(q,q_+) ≤ C(d)`. -/
theorem projective_step
    (d : ℕ) (hd : 2 ≤ d) :
    ∃ Csrc : ℝ → ℝ, (∀ γ : ℝ, γ ∈ Set.Ico (0 : ℝ) 1 → 0 < Csrc γ) ∧
    ∃ C : ℝ, 0 < C ∧
      ∀ γ : ℝ, γ ∈ Set.Ico (0 : ℝ) 1 →
      ∀ K : ℝ, 1 < K →
      ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
        ⌈Csrc γ * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
        ∀ (m mStar : Mat d), m.PosDef → mStar.PosDef →
          ∀ ε : ℝ, 0 < ε →
            projectiveDistance m (geometryUpdate ε m mStar) ≤ ε ∧
              1 / 2 *
                    Real.log (‖geometryUpdate ε m mStar‖ * ‖(geometryUpdate ε m mStar)⁻¹‖) ≤
                  1 / 2 * Real.log (‖m‖ * ‖m⁻¹‖) + ε ∧
                (ε ≤ 1 →
                  gridRatio (Geometry.explicitRoundedGrid jStar m)
                      (Geometry.explicitRoundedGrid jStar (geometryUpdate ε m mStar)) ≤ C) := by
                        exact HCPolySupport.HighContrast.Entry.projective_step d hd

end HCPolySupport.HighContrast
