/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Besov.Carriers
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MultiscaleEllipticity.Localization
public import LeanPool.HighContrastHomogenization.Support.Book.Ch05.Theorems.Section53.WeakNormsMaximizer.EnergyDefect

/-!
# PerScaleDefect

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The per-scale defect estimate of the Section 3.5 negative-norm lemma

This module proves the per-scale estimate that feeds the large-scale half of
`l.Besov.norms`.  Fix a cube `Q = \cu_m`, a depth `j = m - n`, and let
`v = v(\cdot,\cu_m,p,q;\a)` be the canonical maximizer on `Q`.  For every
descendant `R = z+\cu_n` of `Q` at depth `j`, the manuscript compares the
average `(\nabla v)_R` with the *local* coarse projection
`\s_*^{-1}(R)(q+\k(R)p) - p` attached to `R` itself, and shows that the
descendant average of the squared deviation is controlled by the response
defect average, at the price of the multiscale ellipticity weight
`3^{2s(m-n)} \lambda_{s,r}^{-1}(\cu_m;\a)`.

The estimate is proved here at an **arbitrary admissible exponent**
`r \in [1,\infty]`, which is the range the manuscript states.

## How the manuscript displays are distributed over the declarations

The upstream Chapter 5 estimate used below already carries the one-cube step
*composed with the first inequality*: it is proved from
`Ch02.vecNormSq_averageGradient_le_matrixNorm_sigmaStarInvCoarse_mul_variationEnergyValue`,
which is the single inequality `|(\nabla w)_R|^2 \le |\s_*^{-1}(R)| \fint_R
\nabla w \cdot \s \nabla w`.  Consequently the square root `\s_*^{1/2}(R)`
never has to be constructed: the manuscript's two-step passage through
`\s_*^{1/2}` is realized upstream as one inequality with the same endpoints.
What remains is the second inequality, `e.bound.one.cube.by.lambdas`, and that
is `maxDescendantSigmaStarInv_le_lambdaSqCoeffField_inv` below.

## Formalization readings

1. *The descendant index set.*  The manuscript sums over
   `z \in 3^n\Zd \cap \cu_m`; that index set is the set of triadic descendants
   of `\cu_m` at depth `m-n`, and `\avsum` is `descendantsAverage`.  The
   translation is the one already used throughout the Chapter 5 vocabulary.
2. *The local coarse projection.*  The comparison vector at the descendant `R`
   is `coarseScaleSeparation a ha R p q` of `Carriers.lean`, evaluated at `R`
   and not at the parent cube.  This is the vector printed the same
   descendant-evaluated coarse projection occurs inside a difference, with the
   two `- p` summands cancelled.  By the identity of `Carriers.lean` it is the
   Chapter 4 measurable representative of `(\nabla v_{n,z})_R`, which is how
   the manuscript's `e.v.spatial.averages` enters.
3. *The exponent carrier.*  The manuscript's `r \in [1,\infty]` is
   `Ch02.MultiscaleExponent` together with `IsAdmissible`, and
   `\lambda_{s,r}(\cu_m;\a)` is `Ch04.lambdaSqCoeffField`.  No exponent is
   pinned: the two Chapter 2 inputs used below are already stated for every
   admissible exponent.
-/

namespace Algsuperdiff.Section3.Provider.Besov

open HCPolySupport HCPolySupport.Book
open HCPolySupport.Book.Ch05.Section53

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## The per-scale squared deviation -/

/-- The manuscript quantity `| (\nabla v)_R - (\s_*^{-1}(R)(q + \k(R)p) - p)
|^2`, for the canonical maximizer `v = v(\cdot,Q,p,q;\a)` of the parent cube
`Q` and a descendant cube `R`.

The first summand is the Chapter 4 measurable representative of the average of
`\nabla v` over `R`, and the second is the local coarse projection of
`Carriers.lean` at `R`. -/
def coarseScaleSeparationDeviationSq (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) (Q : TriadicCube d)
    (p q : Vec d) (R : TriadicCube d) : ℝ :=
  vecNormSq
    (Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q a.toFun -
      coarseScaleSeparation a ha R p q)

omit [NeZero d] in
theorem coarseScaleSeparationDeviationSq_nonneg (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) (Q : TriadicCube d)
    (p q : Vec d) (R : TriadicCube d) :
    0 ≤ coarseScaleSeparationDeviationSq a ha Q p q R :=
  vecNormSq_nonneg _

/-! ## The ellipticity weight conversion -/

/-- Nonnegativity of the manuscript quantity `\lambda_{s,r}(Q;\a)` at every
admissible exponent. -/
private theorem lambdaSqCoeffField_nonneg (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) (Q : TriadicCube d) {s : ℝ}
    (hs : 0 < s) {r : Ch02.MultiscaleExponent} (hr : r.IsAdmissible) :
    0 ≤ Ch04.lambdaSqCoeffField Q s r a := by
  simp only [Ch04.lambdaSqCoeffField, dite_eq_left ha]
  exact Ch02.lambdaSq_nonneg Q _ hs hr

/-- **The ellipticity weight conversion, at an arbitrary admissible exponent.**
The largest coarse `|\s_*^{-1}|` over the depth-`j` descendants of `Q` is at
most `3^{2sj} \lambda_{s,r}^{-1}(Q;\a)`.

Its first inequality, `|P|^2 \le |\s_*^{-1}(R)| |\s_*^{1/2}(R)P|^2`
(`e.ellipticities.monotone.ordered`), is already contained in the Chapter 5
estimate quoted in the next theorem. -/
theorem maxDescendantSigmaStarInv_le_lambdaSqCoeffField_inv (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) (Q : TriadicCube d) (j : ℕ)
    {s : ℝ} (hs : 0 < s) {r : Ch02.MultiscaleExponent} (hr : r.IsAdmissible) :
    Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (j : ℤ))
        (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) ≤
      (3 : ℝ) ^ (2 * s * (j : ℝ)) * (Ch04.lambdaSqCoeffField Q s r a)⁻¹ := by
  have hk : Q.scale - (j : ℤ) ≤ Q.scale :=
    sub_le_self _ (by exact_mod_cast Nat.zero_le j)
  have h1 :=
    Ch02.maxDescendant_sigmaStarInv_le_maxDescendant_lambdaSq_inv Q
      (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) hk hs hr
  have h2 :=
    Ch02.maxDescendant_lambdaSq_inv_le Q
      (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) hk hs hr
  have hw : Ch02.multiscaleDescendantWeight Q (Q.scale - (j : ℤ)) s
      = (3 : ℝ) ^ (2 * s * (j : ℝ)) := by
    unfold Ch02.multiscaleDescendantWeight
    have hsub : Q.scale - (Q.scale - (j : ℤ)) = (j : ℤ) := by omega
    rw [hsub]
    norm_num
  refine h1.trans (h2.trans ?_)
  rw [hw]
  simp only [Ch04.lambdaSqCoeffField, dite_eq_left ha]
  exact le_rfl

/-! ## The defect display -/

/-- **The display chain on the `Carriers.lean` carrier.** The descendant average of
the squared deviation of `(\nabla v)_R` from the local coarse projection at `R`
is at most twice the largest coarse `|\s_*^{-1}|` over those descendants times
the response partition defect.

The one-cube step (composed with the first inequality) is
`e.v.spatial.averages` together with `e.energymaps.nonsymm`, and the passage to
the average is `e.quadresp.nosymm`; both are supplied by the Chapter 5
energy-defect theory.  The only work done here is the replacement of the
Chapter 4 average `(\nabla v_{n,z})_R` by the printed vector
`\s_*^{-1}(R)(q+\k(R)p) - p`, which is the identity of `Carriers.lean`. -/
theorem descendantsAverage_coarseScaleSeparationDeviationSq_le_maxSigmaStarInv
    (a : RegCoeffField d) (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) (j : ℕ) (p q : Vec d) :
    descendantsAverage Q j (coarseScaleSeparationDeviationSq a ha Q p q) ≤
      2 * Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (j : ℤ))
            (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) *
        JUpperBoundWeakNorms.responseJPartitionDefectOnFamilyAtDepth
          (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) Q j p q := by
  have hfun : coarseScaleSeparationDeviationSq a ha Q p q =
      fun R =>
        vecNormSq
          (Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q a.toFun -
            Ch04.canonicalScalarResponseGradientAverageCubeSet R R p q a.toFun) := by
    funext R
    rw [coarseScaleSeparationDeviationSq,
      coarseScaleSeparation_eq_canonicalScalarResponseGradientAverageCubeSet]
  rw [hfun]
  exact
    WeakNormsMaximizer.descendantsAverage_ch04GradientMismatch_le_maxSigmaStarInv_mul_responseDefect
      a ha Q j p q

/-! ## The per-scale defect estimate -/

/-- **The per-scale defect estimate, at an arbitrary admissible exponent `r \in
[1,\infty]`.**

For a cube `Q` and a depth `j`, the descendant average of `| (\nabla v)_R -
(\s_*^{-1}(R)(q + \k(R)p) - p) |^2` is at most `2 \cdot 3^{2sj}
\lambda_{s,r}^{-1}(Q;\a)` times the response defect average.  This is the
combination of the three displays, with the literal manuscript factor `2`. -/
theorem descendantsAverage_coarseScaleSeparationDeviationSq_le (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) (Q : TriadicCube d) (j : ℕ)
    {s : ℝ} (hs : 0 < s) {r : Ch02.MultiscaleExponent} (hr : r.IsAdmissible)
    (p q : Vec d) :
    descendantsAverage Q j (coarseScaleSeparationDeviationSq a ha Q p q) ≤
      2 * ((3 : ℝ) ^ (2 * s * (j : ℝ)) * (Ch04.lambdaSqCoeffField Q s r a)⁻¹) *
        JUpperBoundWeakNorms.responseJPartitionDefectOnFamilyAtDepth
          (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) Q j p q := by
  have hD :
      0 ≤ JUpperBoundWeakNorms.responseJPartitionDefectOnFamilyAtDepth
        (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) Q j p q :=
    WeakNormsMaximizer.responseJPartitionDefectOnFamilyAtDepth_nonneg _ Q j p q
  have hM := maxDescendantSigmaStarInv_le_lambdaSqCoeffField_inv a ha Q j hs hr
  calc
    descendantsAverage Q j (coarseScaleSeparationDeviationSq a ha Q p q)
        ≤ 2 * Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (j : ℤ))
              (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) *
            JUpperBoundWeakNorms.responseJPartitionDefectOnFamilyAtDepth
              (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) Q j p q :=
          descendantsAverage_coarseScaleSeparationDeviationSq_le_maxSigmaStarInv a ha Q j p q
    _ = 2 * (Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (j : ℤ))
              (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) *
            JUpperBoundWeakNorms.responseJPartitionDefectOnFamilyAtDepth
              (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) Q j p q) := by
          ring
    _ ≤ 2 * (((3 : ℝ) ^ (2 * s * (j : ℝ)) * (Ch04.lambdaSqCoeffField Q s r a)⁻¹) *
            JUpperBoundWeakNorms.responseJPartitionDefectOnFamilyAtDepth
              (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) Q j p q) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hM hD) (by norm_num)
    _ = 2 * ((3 : ℝ) ^ (2 * s * (j : ℝ)) * (Ch04.lambdaSqCoeffField Q s r a)⁻¹) *
          JUpperBoundWeakNorms.responseJPartitionDefectOnFamilyAtDepth
            (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) Q j p q := by
          ring

/-- **The per-scale defect estimate in the manuscript's scale indexing.**  For
`n \le m` the descendants of `\cu_m` at depth `m-n` are the cubes `z+\cu_n`
with `z \in 3^n\Zd \cap \cu_m`, and the right side is the manuscript's
`2 \avsum_z ( J(z+\cu_n,p,q;\a) - J(\cu_m,p,q;\a) )` weighted by
`3^{2s(m-n)} \lambda_{s,r}^{-1}(\cu_m;\a)`. -/
theorem descendantsAverage_coarseScaleSeparationDeviationSq_le_atScale
    (a : RegCoeffField d) (ha : Ch04.AELocallyUniformlyEllipticField a)
    {m n : ℤ} (hnm : n ≤ m) {s : ℝ} (hs : 0 < s)
    {r : Ch02.MultiscaleExponent} (hr : r.IsAdmissible) (p q : Vec d) :
    descendantsAverage (originCube d m) (m - n).toNat
        (coarseScaleSeparationDeviationSq a ha (originCube d m) p q) ≤
      2 * ((3 : ℝ) ^ (2 * s * ((m - n : ℤ) : ℝ)) *
            (Ch04.lambdaSqCoeffField (originCube d m) s r a)⁻¹) *
        WeakNormsMaximizer.responseDefectAverageAtScale m n p q a := by
  have hcast : (((m - n).toNat : ℕ) : ℝ) = ((m - n : ℤ) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ m - n)
  rw [WeakNormsMaximizer.responseDefectAverageAtScale_eq_responseJPartitionDefectOnDependentFamily
      a ha, ← hcast]
  exact descendantsAverage_coarseScaleSeparationDeviationSq_le a ha (originCube d m)
    (m - n).toNat hs hr p q

/-- **The square-root form of the per-scale defect estimate.**  This is the shape
in which sums the estimate over `n`: the factor `3^{s(m-n)}` is the one that
turns the multiscale Poincaré weight `3^{-(m-n)}` into the manuscript's
`3^{-(1-s)(m-n)}`. -/
theorem sqrt_descendantsAverage_coarseScaleSeparationDeviationSq_le_atScale
    (a : RegCoeffField d) (ha : Ch04.AELocallyUniformlyEllipticField a)
    {m n : ℤ} (hnm : n ≤ m) {s : ℝ} (hs : 0 < s)
    {r : Ch02.MultiscaleExponent} (hr : r.IsAdmissible) (p q : Vec d) :
    Real.sqrt
        (descendantsAverage (originCube d m) (m - n).toNat
          (coarseScaleSeparationDeviationSq a ha (originCube d m) p q)) ≤
      Real.sqrt 2 * (3 : ℝ) ^ (s * ((m - n : ℤ) : ℝ)) *
        Real.sqrt ((Ch04.lambdaSqCoeffField (originCube d m) s r a)⁻¹) *
        Real.sqrt (WeakNormsMaximizer.responseDefectAverageAtScale m n p q a) := by
  set lamInv : ℝ := (Ch04.lambdaSqCoeffField (originCube d m) s r a)⁻¹ with hlamInv
  set Dsc : ℝ := WeakNormsMaximizer.responseDefectAverageAtScale m n p q a with hDsc
  have hlam0 : 0 ≤ lamInv :=
    inv_nonneg.mpr (lambdaSqCoeffField_nonneg a ha (originCube d m) hs hr)
  have hD0 : 0 ≤ Dsc :=
    WeakNormsMaximizer.responseDefectAverageAtScale_nonneg_of_aelocallyUniformlyEllipticField
      a ha m n p q
  have hpow : ((3 : ℝ) ^ (s * ((m - n : ℤ) : ℝ))) ^ 2
      = (3 : ℝ) ^ (2 * s * ((m - n : ℤ) : ℝ)) := by
    calc
      ((3 : ℝ) ^ (s * ((m - n : ℤ) : ℝ))) ^ 2
          = (3 : ℝ) ^ (s * ((m - n : ℤ) : ℝ) * 2) := by
            simpa [Real.rpow_natCast] using
              (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)
                (s * ((m - n : ℤ) : ℝ)) (2 : ℝ)).symm
      _ = (3 : ℝ) ^ (2 * s * ((m - n : ℤ) : ℝ)) := by ring_nf
  set Y : ℝ :=
    Real.sqrt 2 * (3 : ℝ) ^ (s * ((m - n : ℤ) : ℝ)) * Real.sqrt lamInv * Real.sqrt Dsc with hY
  have hY0 : 0 ≤ Y := by positivity
  have hYsq : Y ^ 2
      = 2 * ((3 : ℝ) ^ (2 * s * ((m - n : ℤ) : ℝ)) * lamInv) * Dsc := by
    rw [hY, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Real.sq_sqrt hlam0, Real.sq_sqrt hD0, hpow]
    ring
  have hbase :
      descendantsAverage (originCube d m) (m - n).toNat
          (coarseScaleSeparationDeviationSq a ha (originCube d m) p q) ≤ Y ^ 2 := by
    rw [hYsq]
    exact descendantsAverage_coarseScaleSeparationDeviationSq_le_atScale a ha hnm hs hr p q
  calc
    Real.sqrt
        (descendantsAverage (originCube d m) (m - n).toNat
          (coarseScaleSeparationDeviationSq a ha (originCube d m) p q))
        ≤ Real.sqrt (Y ^ 2) := Real.sqrt_le_sqrt hbase
    _ = Y := Real.sqrt_sq hY0

end

end Algsuperdiff.Section3.Provider.Besov
