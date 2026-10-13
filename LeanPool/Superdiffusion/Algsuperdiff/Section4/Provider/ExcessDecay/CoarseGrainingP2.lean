/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.GeneralCoarseGrainingL2TwoExponent
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.StabilityExponentComparison

/-!
# CoarseGrainingP2

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `p.general.coarse.graining` at `p = 2`: the CoarseGraining interface

Nothing here imports that file, and nothing here claims the anchor or any
source node.

## The finding

```text
  Homogenization.Book.Ch03.generalCoarseGrainingL2TwoExponentTheory
      (d : ℕ) [NeZero d] : GeneralCoarseGrainingL2TwoExponentTheory d
```

(`Homogenization/Book/Ch03/Theorems/GeneralCoarseGrainingL2TwoExponent.lean`).
Its single field packages the manuscript display
`e.general.coarse.graining.estimate` at `p = 2` in a *scale-separated* form: the
flux-response exponent `r` (the manuscript's `s_1`) and the forcing exponent
`r₂` (the manuscript's `s_2`) are independent, and the forcing term carries the
visible inverse depth factor `3^{-r₂ (m-n)}`.

This module turns that package into a usable estimate with a **named `d`-only
constant** and supplies the two conversions the Section 4.3 chain needs:

* the left-hand side of CoarseGraining's estimate dominates its *first*
  summand, the constant-coefficient gradient defect `a₀(∇u − ∇v)` (the second
  summand is the flux defect the manuscript "throws away");
* CoarseGraining's depth-truncated `q = 1` error
  `coarseGrainingHomogenizationErrorAtDepth Q a a₀ r j` is dominated by the
  development's own `q = 2` one-cube error at any index `t ≤ r/2`, at the
  single cost `3^{t j}` — and at `j = 0` (the manuscript's `m = n`
  specialization) it *is* the one-cube `q = 1` error, with no cost at all.

## Divergences from the printed proposition (reported, not hidden)

* **Hypothesis `r < s/2`.**  The printed proposition asks only `s_1 < s < s_2`;
  CoarseGraining's package asks `r < s/2` (a factor-two-stricter separation)
  together with `s < 1` and `r ≤ r₂`.  This is what forces the Section 4.3
  comparison exponent above the printed `s/2` — see
  `CoarseGrainingL2Interior.lean`.
* **The forcing bracket.**  The printed proposition writes the forcing
  prefactor as `(1 + 𝓔²_{s_1/2,∞,2})`; CoarseGraining writes it through the
  coarse-grained ellipticity factors `Λ^{1/2}_{r/2,2}`, `λ^{-1/2}_{r/2,2}`,
  `λ^{-1}_{r/2,2}` and one further `𝓔 λ^{-1/2}` product.  The two are related
  by `l.mathcal.E.to.Lambdas`; on the good event both are capped by `C(d)`.
* **The mesoscopic index.**  The printed `𝓔_{s_1,∞,1}(□_m, n; a, σ₀)` is a
  two-index object; CoarseGraining encodes it as the maximum of the *one-cube*
  error over the depth-`j` descendants of `Q`.  At `j = 0` the two encodings
  agree.

Nothing above is asserted to be the printed statement; every deviation is
carried in the statements themselves.

## References

* ABK26, `p.general.coarse.graining`.
* ABK26, `l.harmonic.approximation.good.scales`,
  (`e.homogenization.L2.interior`).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport HCPolySupport.Book

noncomputable section

variable {d : ℕ}

/-! ## 1. The scalar comparison background -/

/-- The constant isotropic background `σ Id`, bundled as CoarseGraining's
`ConstantCoeffMatrix`.  See the duplication disclosure. -/
def scalarComparator {sigma : ℝ} (hsigma : 0 < sigma) : Ch03.ConstantCoeffMatrix d where
  matrix := scalarMatrix (d := d) sigma
  isSymm := scalarMatrix_isSymm sigma
  lam := sigma
  Lam := sigma
  lam_pos := hsigma
  lam_le_Lam := le_rfl
  elliptic := isEllipticMatrix_scalarMatrix hsigma

theorem scalarComparator_matrix {sigma : ℝ} (hsigma : 0 < sigma) :
    (scalarComparator (d := d) hsigma).matrix = scalarMatrix (d := d) sigma :=
  rfl

theorem scalarComparator_isPositiveScalarMatrix {sigma : ℝ} (hsigma : 0 < sigma) :
    IsPositiveScalarMatrix (scalarComparator (d := d) hsigma).matrix :=
  ⟨sigma, hsigma, rfl⟩

/-- `|σ Id| = σ` in CoarseGraining's Chapter 2 (Euclidean operator) normalization. -/
theorem matrixNorm_scalarMatrix [NeZero d] {sigma : ℝ} (hsigma : 0 ≤ sigma) :
    Ch02.matrixNorm (scalarMatrix (d := d) sigma) = sigma := by
  simp [Ch02.matrixNorm, scalarMatrix, norm_smul, abs_of_nonneg hsigma]

/-- `|a₀|^{1/2} = σ^{1/2}` at the scalar background. -/
theorem constantCoeffMatrixNormHalf_scalarComparator [NeZero d] {sigma : ℝ}
    (hsigma : 0 < sigma) :
    Ch03.constantCoeffMatrixNormHalf (scalarComparator (d := d) hsigma) =
      Real.rpow sigma (1 / 2 : ℝ) := by
  rw [Ch03.constantCoeffMatrixNormHalf, scalarComparator_matrix,
    matrixNorm_scalarMatrix hsigma.le]

/-- `|a₀| = σ` at the scalar background. -/
theorem constantCoeffMatrixNorm_scalarComparator [NeZero d] {sigma : ℝ}
    (hsigma : 0 < sigma) :
    Ch03.constantCoeffMatrixNorm (scalarComparator (d := d) hsigma) = sigma := by
  rw [Ch03.constantCoeffMatrixNorm, scalarComparator_matrix,
    matrixNorm_scalarMatrix hsigma.le]

/-! ## 2. The `d`-only constant and the estimate -/

/-- The `d`-only constant of CoarseGraining's scale-separated `p = 2` general
coarse-graining package.  It is the constant produced by
`Homogenization.Book.Ch03.generalCoarseGrainingL2TwoExponentTheory`;
CoarseGraining exposes it only existentially, so it is named here by choice. -/
def coarseGrainingP2Const (d : ℕ) [NeZero d] : ℝ :=
  Classical.choose (Ch03.generalCoarseGrainingL2TwoExponentTheory d).exists_constant

theorem coarseGrainingP2Const_pos (d : ℕ) [NeZero d] : 0 < coarseGrainingP2Const d :=
  (Classical.choose_spec
    (Ch03.generalCoarseGrainingL2TwoExponentTheory d).exists_constant).1

/-- **The general coarse-graining estimate at `p = 2`, with a named constant.**

For a coarse-graining datum `w` on the triadic cube `Q` (CoarseGraining's
`CoarseGrainingComparisonDatum`: `u` solves `−∇·a∇u = ∇·g`, `v` solves `−∇·a₀∇v
= ∇·g`, and `u − v` has zero trace), a positive scalar background `a₀`, and
exponents `0 < r < s/2`, `s < 1`, `r ≤ r₂` with `g ∈ H^{r₂}(Q)`:

```text
  [a₀(∇u − ∇v)]_{B^{-s}_{2,2}(Q)} + [a∇u − a₀∇v]_{B^{-s}_{2,2}(Q)}
      ≤ generalCoarseGrainingL2TwoExponentRHS (coarseGrainingP2Const d) … .
```

This is ABK26's `e.general.coarse.graining.estimate` at `p = 2`, in
CoarseGraining's own carriers and with CoarseGraining's own scale-separated
right-hand side. -/
theorem coarseGrainingP2_estimate [NeZero d] {Q : TriadicCube d}
    {a : Ch03.CoeffFamily d} {a0 : Ch03.ConstantCoeffMatrix d}
    (ha0 : IsPositiveScalarMatrix a0.matrix) {s r r₂ : ℝ} {j : ℕ}
    {g : Vec d → Vec d} (w : Ch03.CoarseGrainingComparisonDatum Q a a0 g)
    (hs : 0 < s) (hr : 0 < r) (hrs : r < s / 2) (hs1 : s < 1) (hr₂ : r ≤ r₂)
    (hg : Ch03.ForceBesovRegularity Q r₂ g) :
    Ch03.homogenizationComparisonNegativeBesovLHS Q a a0 s w.u w.v ≤
      Ch03.generalCoarseGrainingL2TwoExponentRHS (coarseGrainingP2Const d) Q a a0
        s r r₂ j g w.u :=
  (Classical.choose_spec
    (Ch03.generalCoarseGrainingL2TwoExponentTheory d).exists_constant).2
      ha0 w hs hr hrs hs1 hr₂ hg

/-- The right-hand side is linear in its constant. -/
theorem generalCoarseGrainingL2TwoExponentRHS_eq_const_mul [NeZero d] (C : ℝ)
    (Q : TriadicCube d) (a : Ch03.CoeffFamily d) (a0 : Ch03.ConstantCoeffMatrix d)
    (s r r₂ : ℝ) (j : ℕ) (g : Vec d → Vec d)
    (u : H1Function (Ch02.cubeDomain Q : Set (Vec d))) :
    Ch03.generalCoarseGrainingL2TwoExponentRHS C Q a a0 s r r₂ j g u =
      C * Ch03.generalCoarseGrainingL2TwoExponentRHS 1 Q a a0 s r r₂ j g u := by
  rw [Ch03.generalCoarseGrainingL2TwoExponentRHS,
    Ch03.generalCoarseGrainingL2TwoExponentRHS,
    Ch03.generalCoarseGrainingL2TwoExponentFluxDefectRHS,
    Ch03.generalCoarseGrainingL2TwoExponentFluxDefectRHS]
  ring

/-! ## 3. Discarding the flux summand -/

/-- The `q = 2` negative Besov seminorm is nonnegative, with no boundedness
hypothesis.  See the duplication disclosure. -/
theorem negativeSeminormTwo_nonneg (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d) :
    0 ≤ cubeBesovNegativeVectorSeminormTwo Q s F := by
  by_cases hb : BddAbove (Set.range fun N : ℕ =>
      cubeBesovNegativeVectorPartialSeminormTwo Q s N F)
  · have h0 : (0 : ℝ) ≤ cubeBesovNegativeVectorPartialSeminormTwo Q s 0 F := by
      rw [cubeBesovNegativeVectorPartialSeminormTwo]
      exact Real.sqrt_nonneg _
    exact h0.trans (le_csSup hb (Set.mem_range_self 0))
  · rw [cubeBesovNegativeVectorSeminormTwo, Real.sSup_of_not_bddAbove hb]

/-- **"Throwing away the flux term".**  The first summand of CoarseGraining's
comparison left-hand side — the constant-coefficient gradient defect `a₀(∇u −
∇v)`, which is what ABK26's display `e.homogenization.L2.interior` keeps — is
dominated by the full left-hand side. -/
theorem constantGradientSeminorm_le_comparisonLHS (Q : TriadicCube d)
    (a : Ch03.CoeffFamily d) (a0 : Ch03.ConstantCoeffMatrix d) (s : ℝ)
    (u v : H1Function (Ch02.cubeDomain Q : Set (Vec d))) :
    cubeBesovNegativeVectorSeminormTwo Q s
        (Ch03.homogenizationComparisonConstantGradientField a0 u v) ≤
      Ch03.homogenizationComparisonNegativeBesovLHS Q a a0 s u v := by
  rw [Ch03.homogenizationComparisonNegativeBesovLHS]
  have hflux := negativeSeminormTwo_nonneg Q s
    (Ch03.homogenizationComparisonFluxField Q a a0 u v)
  linarith only [hflux]

/-! ## 4. The homogenization error: CoarseGraining's depth maximum vs the development object -/

/-- **CoarseGraining's `q = 1` depth maximum, in the development's `q = 2` one-cube
object.**

For `0 < t ≤ r/2`,

```text
  max_{R ∈ descendants_j(Q)} 𝓔_{r,∞,1}(R; a, a₀)  ≤  3^{t j} 𝓔_{t,∞,2}(Q; a, a₀) .
```

At `j = 0` the factor is `1`, and at `t = r/2` the index is exactly half the
flux-response index. -/
theorem coarseGrainingHomogenizationErrorAtDepth_le [NeZero d] (Q : TriadicCube d)
    (a : Ch03.CoeffFamily d) (a0 : Ch03.ConstantCoeffMatrix d) {r t : ℝ} (j : ℕ)
    (ht : 0 < t) (htr : t ≤ r / 2) :
    Ch03.coarseGrainingHomogenizationErrorAtDepth Q a a0 r j ≤
      Real.rpow (3 : ℝ) (t * (j : ℝ)) *
        Ch02.HomogenizationErrorOnCube Q t .infinity (.finite 2) a a0.matrix := by
  classical
  have hr : 0 < r := by linarith only [ht, htr]
  rw [Ch03.coarseGrainingHomogenizationErrorAtDepth]
  refine Ch02.finsetSupReal_le _ (descendantsAtDepth_nonempty Q j) ?_
  intro R hR
  have h1 : Ch02.HomogenizationErrorOnCube R r .infinity (.finite 1) a a0.matrix ≤
      Ch02.HomogenizationErrorOnCube R (r / 2) .infinity (.finite 2) a a0.matrix :=
    homogenizationErrorOnCube_infinity_one_le_infinity_two_half R a a0.matrix hr
  have hmem : R ∈ descendantsAtScale Q (Q.scale - (j : ℤ)) :=
    mem_descendantsAtScale_sub_nat_of_mem_descendantsAtDepth hR
  have h2 := homogenizationErrorOnCube_infinity_two_descendant_index_le
    (Q := Q) (R := R) (k := Q.scale - (j : ℤ)) a a0.matrix ht htr hmem
  have hj : Int.toNat (Q.scale - (Q.scale - (j : ℤ))) = j := by
    simp
  rw [hj] at h2
  exact h1.trans h2

end

end Algsuperdiff.Section4.Provider.ExcessDecay
