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
public import LeanPool.HighContrastHomogenization.Entry.Setup.NormalizedFluctuation
public import LeanPool.HighContrastHomogenization.Entry.Setup.SchattenNorm
public import LeanPool.HighContrastHomogenization.Frozen.Stationarity
public import LeanPool.HighContrastHomogenization.Setup.LocalSigmaFields
public import LeanPool.HighContrastHomogenization.Frozen.UnitRange
public import LeanPool.HighContrastHomogenization.Entry.Geometry.RoundedGridBasic
public import LeanPool.HighContrastHomogenization.Entry.MatrixAveraging

/-!
# High-contrast homogenization: Entry.Statements.MatrixAveraging

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Lemma `l.fixed.geometry.matrix.averaging` — finite-range matrix averaging

`l.fixed.geometry.matrix.averaging`, the paper's Lemma "Finite-range matrix averaging",
transcribed from
the printed display.

Reading of the display, stated here so that no divergence is silent:

* `N ≥ 2` even is a natural number, coerced to the real Schatten index that
  `HCPoly/Entry/Setup/SchattenNorm.lean` takes; `‖·‖_{L^N(S_N)}` is `lqSchattenNorm`, real-valued
  under the real-valued reading.
* The display names no hypothesis on the coefficient law, because the manuscript's standing
  assumptions (`t.polynomial.entry`: a stationary, unit-range probability law satisfying coarse
  ellipticity `†`) are in force throughout; they are carried here in the binder order of the root
  statement `HCPoly/Entry/Statements/PolynomialEntry.lean`, and the proof of this lemma uses two
  of them
  (the range of dependence, for the independence of a colour class, and stationarity). The
  printed `𝐀hom_{j,q}` is meaningless without the law.
* `𝔪 > 0` is `Matrix.PosDef` and `q = 𝒬(𝔪)` is `Geometry.explicitRoundedGrid jStar m`; the standing
  `3^{j_*} ≥ 2d` near `e.rounded.grid.bounds` is `hj` and the standing `d ≥ 2` of
  `t.polynomial.entry` is `hd`.
  The display does not restate `𝔪 > 0`; `𝒬(𝔪)` presupposes it, and it is carried as `hm`.
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
* `Z` is a nonempty finite subset of `3^j q ℤ^d` = `adaptedLatticeAtScale q j`, as a `Finset` with
its
  printed inclusion; `#Z` is `Z.card`.
* "a deterministic positive definite `2d`-by-`2d` matrix `R`" is a `BlockMat d` that is symmetric
  and `Book.Ch02.BlockPosDef` — the block analogue of Mathlib's `Matrix.PosDef`, whose symmetry
  the manuscript's positive matrices always have. `R^{-1/2} · R^{-1/2}` is `normalizedBlock · R`
  of `HCPoly/Entry/Setup/ProjectiveDistance.lean`.
* The average `⨍_{z∈Z}` is `(#Z)⁻¹ • ∑_{z∈Z}` of the conjugated centered blocks, taken in the
  `2d`-by-`2d` matrix algebra through `toFullBlockMat`/`ofFullBlockMat`: the definition layer
  names the difference and the conjugation but no block addition, and the printed average needs
  no new definition.
* `𝐀(⋄_j^q)` on the right is the cell at the origin, untranslated, exactly as printed.
* **Not carried**: the integrability of either side. The display asserts none, and the proof
  derives it from the standing assumptions ("the bounded-window estimate gives the required
  `L^N(S_N)`-integrability", `p.fixed.geometry.parent.child.recurrence`); under the real-valued
  reading a
  non-integrable moment makes the corresponding norm Mathlib's junk `0`. No `SchattenMemLp`
  premise is added here, since the manuscript prints one only in `l.fixed.geometry.positive.gap`.

The proof applies `HCPolySupport.HighContrast.Entry.fixed_geometry_matrix_averaging`
(`HCPoly/Entry/MatrixAveraging.lean`).
-/

open HCPolySupport.HighContrast (CoeffSpace adaptedMean blockSub coarseBlock normalizedBlock)
namespace HCPolySupport.HighContrast

open MeasureTheory

/-- **Lemma `l.fixed.geometry.matrix.averaging`**. There is
`C_src(d,γ)` such that, for every `j_*` satisfying `e.source.lower.scale` (standing
near `e.source.lower.scale`), every even `N ≥ 2`, `q = 𝒬(𝔪)`, `j ≥ j_*`, every nonempty finite
`Z ⊆ 3^j q ℤ^d`, and every deterministic positive definite `2d`-by-`2d` matrix `R`:
`‖⨍_{z∈Z} R^{-1/2}(𝐀(z+⋄_j^q) − 𝐀hom_{j,q})R^{-1/2}‖_{L^N(S_N)}
≤ (N 3^{d/2}/(#Z)^{1/2}) ‖R^{-1/2}(𝐀(⋄_j^q) − 𝐀hom_{j,q})R^{-1/2}‖_{L^N(S_N)}`. -/
theorem fixed_geometry_matrix_averaging
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
        ∀ (j : ℤ), (jStar : ℤ) ≤ j →
        ∀ (Z : Finset (Vec d)), Z.Nonempty →
        (Z : Set (Vec d)) ⊆ adaptedLatticeAtScale (Geometry.explicitRoundedGrid jStar m) j →
        ∀ (R : BlockMat d), IsSymmetricBlockMat R → Book.Ch02.BlockPosDef R →
        lqSchattenNorm P (N : ℝ)
            (fun a =>
              ofFullBlockMat
                ((Z.card : ℝ)⁻¹ •
                  ∑ z ∈ Z,
                    toFullBlockMat
                      (normalizedBlock
                        (blockSub
                          (coarseBlock
                            (HighContrast.adaptedCellTranslate (Geometry.explicitRoundedGrid jStar m) j z) a)
                          (adaptedMean P (Geometry.explicitRoundedGrid jStar m) j))
                        R))) ≤
          (N : ℝ) * (3 : ℝ) ^ ((d : ℝ) / 2) / (Z.card : ℝ) ^ ((1 : ℝ) / 2) *
            lqSchattenNorm P (N : ℝ)
              (fun a =>
                normalizedBlock
                  (blockSub (coarseBlock (HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar m) j) a)
                    (adaptedMean P (Geometry.explicitRoundedGrid jStar m) j))
                  R) := by exact HCPolySupport.HighContrast.Entry.fixed_geometry_matrix_averaging d hd γ hγ

end HCPolySupport.HighContrast
