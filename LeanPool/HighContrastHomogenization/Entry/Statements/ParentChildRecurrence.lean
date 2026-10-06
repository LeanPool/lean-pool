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
public import LeanPool.HighContrastHomogenization.Setup.Moments
public import LeanPool.HighContrastHomogenization.Entry.Setup.NormalizedFluctuation
public import LeanPool.HighContrastHomogenization.Entry.Setup.SchattenNorm
public import LeanPool.HighContrastHomogenization.Frozen.Stationarity
public import LeanPool.HighContrastHomogenization.Setup.LocalSigmaFields
public import LeanPool.HighContrastHomogenization.Frozen.UnitRange
public import LeanPool.HighContrastHomogenization.Entry.Geometry.RoundedGridBasic
public import LeanPool.HighContrastHomogenization.Entry.ParentChildRecurrence

/-!
# High-contrast homogenization: Entry.Statements.ParentChildRecurrence

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Proposition `p.fixed.geometry.parent.child.recurrence` — parent--child recurrence

`p.fixed.geometry.parent.child.recurrence`, the paper's Proposition "Parent--child recurrence",
transcribed from
the printed display.

Reading of the display, stated here so that no divergence is silent:

* `V^q_j` is `normalizedFluctuationSelf P q j`, the diagonal fluctuation `V^q_{j,j}(0)`
  near `e.scale.selection.normalized.mean.fluctuation`, and `Δ^q_{j,j+h}` is `detIncrement P q j
  (j+h)`
  (`e.scale.selection.logdet.loss`); `‖·‖_{L^N(S_N)}` is `lqSchattenNorm`, real-valued under the
  real-valued reading, with the even `N ≥ 2` coerced to its real Schatten index.
* `𝔪 > 0` is `Matrix.PosDef`, `q = 𝒬(𝔪)` is `Geometry.explicitRoundedGrid jStar m`, the standing
  `3^{j_*} ≥ 2d` near `e.rounded.grid.bounds` is `hj` and the standing `d ≥ 2` of
  `t.polynomial.entry` is `hd`.
  `j ≥ j_*` and `h ≥ 1` are the printed integer constraints.
* **The source lower scale is a standing hypothesis.** Near `e.source.lower.scale` reads "From now
  on `j_*` satisfies `e.source.lower.scale`", i.e. `j_* ≥ ⌈C_src(d,γ) log_3(2K_{Ψ_S})⌉` with
  `C_src` the constant of the source estimate (near `e.source.lower.scale`). That sentence stands
  from there
  onward, of the same kind as `3^{j_*} ≥ 2d` near `e.rounded.grid.bounds`: every later statement
  whose type
  mentions `j_*` carries it as a premise, whether or not its own display restates it, and whether
  or not its proof will use the source estimate. This display does not restate it; it is carried
  here as `hsrc`. `C_src` is existential in the outermost constant group, before the coefficient
  law and the geometry, since the manuscript fixes one such constant for the whole argument at
  `(d,γ)`; a universally quantified `C_src` would be a different, stronger claim.
* The display names no hypothesis on the coefficient law; the manuscript's standing assumptions
  are in force throughout and are carried here in the binder order of the root statement
  `HCPoly/Entry/Statements/PolynomialEntry.lean`. The proof uses stationarity and subadditivity of
  the coarse
  response, the range of dependence (through `l.fixed.geometry.matrix.averaging`), and the
  bounded-window estimate.
* **Not carried**: the `L^N(S_N)` integrability of `V^q_j` and `V^q_{j+h}`. The display asserts
  none — the printed proof derives it from the standing assumptions ("the bounded-window estimate
  gives the required `L^N(S_N)`-integrability", `p.fixed.geometry.parent.child.recurrence`) — and
  under the real-valued reading a
  non-integrable moment makes the corresponding norm Mathlib's junk `0`. The dependency graph
  records that integrability as a hypothesis of this node; the printed display does not, and the
  display governs. No `SchattenMemLp` premise is added.
* `3^{-(d/2)h}`, `(2d)^{1/N}`, `d^{1−1/N}` and `(e^{Δ}−1)^{1/N}` are real powers, as printed.

The proof is one application of
`HCPolySupport.HighContrast.Entry.fixed_geometry_parent_child_recurrence`
(`HCPoly/Entry/ParentChildRecurrence.lean`) to the binders of the statement.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast

open MeasureTheory

/-- **Proposition `p.fixed.geometry.parent.child.recurrence`**.
There is `C_src(d,γ)` such that, for every `j_*` satisfying `e.source.lower.scale` (standing
near `e.source.lower.scale`), every even `N ≥ 2`, `𝔪 > 0` with `q = 𝒬(𝔪)`, and all integers
`j ≥ j_*` and `h ≥ 1`:
`‖V^q_{j+h}‖_{L^N(S_N)} ≤ N 3^{d/2}(1+(2d)^{1/N}) 3^{−dh/2} e^{Δ^q_{j,j+h}} ‖V^q_j‖_{L^N(S_N)}
+ 2(1+d^{1−1/N}) e^{(1−1/N)Δ^q_{j,j+h}} (e^{Δ^q_{j,j+h}} − 1)^{1/N}`. -/
theorem fixed_geometry_parent_child_recurrence
    (d : ℕ) (hd : 2 ≤ d)
    (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc : ℝ, 0 < Csrc ∧
      ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ),
        IsProbabilityMeasure P → IsStationaryLaw P → IsUnitRangeLaw P →
        CoarseEllipticityDagger P γ E Ψ K S →
        ∀ (N : ℕ), 2 ≤ N → Even N →
        ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
        ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
        ∀ (m : Mat d), m.PosDef →
        ∀ (j h : ℤ), (jStar : ℤ) ≤ j → 1 ≤ h →
        lqSchattenNorm P (N : ℝ)
            (normalizedFluctuationSelf P (Geometry.explicitRoundedGrid jStar m) (j + h)) ≤
          (N : ℝ) * (3 : ℝ) ^ ((d : ℝ) / 2) * (1 + (2 * (d : ℝ)) ^ ((N : ℝ))⁻¹) *
                (3 : ℝ) ^ (-((d : ℝ) / 2) * (h : ℝ)) *
                Real.exp (detIncrement P (Geometry.explicitRoundedGrid jStar m) j (j + h)) *
              lqSchattenNorm P (N : ℝ)
                (normalizedFluctuationSelf P (Geometry.explicitRoundedGrid jStar m) j) +
            2 * (1 + (d : ℝ) ^ (1 - ((N : ℝ))⁻¹)) *
                Real.exp
                  ((1 - ((N : ℝ))⁻¹) *
                    detIncrement P (Geometry.explicitRoundedGrid jStar m) j (j + h)) *
                (Real.exp (detIncrement P (Geometry.explicitRoundedGrid jStar m) j (j + h)) - 1) ^
                  ((N : ℝ))⁻¹ := by exact HCPolySupport.HighContrast.Entry.fixed_geometry_parent_child_recurrence d hd γ hγ

end HCPolySupport.HighContrast
