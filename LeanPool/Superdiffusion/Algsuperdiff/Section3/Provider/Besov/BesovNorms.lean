/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Besov.MultiscalePoincareBridge
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Besov.SmallScaleTail

/-!
# BesovNorms

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The four-term negative-norm display of Section 3.5

This module assembles the display `e.Besov.norms.gradient` of ABK26 for the
canonical maximizer on `\cu_m` from the four estimates already available in
this directory: the multiscale Poincare bridge, the per-scale defect estimate,
the summed large-scale split and the small-scale tail.  Nothing about the
status of the lemma `l.Besov.norms` is asserted here.

The left-hand side is `Carriers.scaledNegHMinusOne` of the maximizer gradient
defect, that is
`3^{-m} \| \nabla v(\cdot,\cu_m,p,q;\a) - (\s_*^{-1}(\cu_m)(q+\k(\cu_m)p)-p) \|_{\Hminusul(\cu_m)}`,
and the right-hand side is the printed four-term sum with one dimension-only
constant `besovNormsConstant d`.

## Route

1. `sqrt_sum_sq_sum_le_sum_mul_sqrt_sum_sq` is the Minkowski conversion
   `(\sum_i (\sum_j w_j a_{ij})^2)^{1/2} \le \sum_j w_j (\sum_i a_{ij}^2)^{1/2}`
   for nonnegative weights, proved by induction on the `j`-range from the
   two-term `\ell^2` triangle inequality, itself proved from the Cauchy--Schwarz
   inequality for finite sums.  This is the conversion that
   `MultiscalePoincareBridge.lean` states but does not formalize: its conclusion
   aggregates the coordinates in `\ell^2`, while the printed display
   `e.msp.plus.split.begin` is the `\ell^1`-of-`\ell^2` form.
2. At `(s,p,q) = (1,2,1)` the depth-`N` entry of the negative circ norm is the
   partial sum `\sum_{j \le N+1} 3^{m-j} (\avsum_R |(u)_R|^2)^{1/2}`
   (`cubeBesovCircNormEntry_one_two_one`, with the weight identified by
   `MultiscalePoincareBridge.cubeBesovCircDepthWeight_one`), so after the scale
   factor `3^{-m}` the summand is the printed `3^{-(m-n)}` term with `n = m-j`.
3. `sum_cubeBesovCircDepthAverage_maximizerGradientDefect` identifies the
   coordinate sum of the depth-`j` circ averages of the gradient defect with
   `descendantsAverage Q j (parentCoarseScaleSeparationDeviationSq ...)`, the
   carrier of `LargeScaleSplit.lean`.  Averaging is linear in the coordinate, so
   the Euclidean length of the average vector is the coordinate sum of the
   squared scalar averages; the upstream Chapter 5 identity
   `cubeAverageVec_canonicalMaximizerGradientDefectOnDependentFamily_eq_ch04`
   supplies the Chapter 4 representative on each descendant.
4. `sum_range_multiscaleTerm_le_fourTerm` splits the depth range at the base
   scale: depths `j \le m-L_0` are the scales `n \in [L_0,m]` and are bounded by
   `LargeScaleSplit.sum_Icc_weighted_...`, while depths `j > m-L_0` are the
   scales `n < L_0` and are bounded by
   `SmallScaleTail.sum_range_smallScale_multiscaleTerm_le`.  The two upstream
   statements are on the identical summand, so the split is exact; the bound is
   uniform in the depth cutoff `N`.
5. `mul_sqrt_sum_sq_ciSup_le` passes from the partial circ norms to the circ
   norm itself.  The circ norm is the supremum of the partial sums, which are
   monotone and, by the previous step, uniformly bounded; the limit therefore
   obeys the same bound.  This is where the manuscript's bi-infinite sum
   `\sum_{n=-\infty}^m` is realized.
6. `scaledNegHMinusOne_maximizerGradientDefect_le_besovNormsSum` composes the
   above with the bridge of `MultiscalePoincareBridge.lean` and converts the
   `ℝ≥0∞`-valued left-hand side by `ENNReal.ofReal`.

## Correspondence with the printed display

* `C \lambda_{s,r}^{-1/2}(\cu_m;\a) \sum_{n=L_0}^m 3^{-(1-s)(m-n)} (\avsum_z
  J(z+\cu_n,p,q;\a) - J(\cu_m,p,q;\a))^{1/2}`, realized with
  `WeakNormsMaximizer.responseDefectAverageAtScale m n p q a` for the bracket;
* `C \sum_{n=L_0}^m 3^{-(m-n)} (\avsum_z | \s_*^{-1}(\cu_m)(q+\k(\cu_m)p) -
  \s_*^{-1}(z+\cu_n)(q+\k(z+\cu_n)p) |^2)^{1/2}`, realized with
  `LargeScaleSplit.coarseMatrixVariationSq`;
* `C \lambda_{s,r}^{-1/2}(\cu_m;\a) 3^{-(1-s)(m-L_0)}
  \| \s^{1/2} \nabla v \|_{\underline L^2(\cu_m)}`, realized with
  `SmallScaleTail.maximizerEnergyL2Norm`;
* `C 3^{-(m-L_0)} | \s_*^{-1}(\cu_m)(q+\k(\cu_m)p) - p |`, realized as the
  square root of `vecNormSq (coarseScaleSeparation a ha (originCube d m) p q)`.

The manuscript constant `C(d)` is given the explicit value `besovNormsConstant
d = 2\sqrt 2 \cdot multiscalePoincareConstant d`, which dominates the four
constants produced by the chain: `2` on the defect leg (`\sqrt 2` from the
split times `\sqrt 2` from the defect estimate), `\sqrt 2` on the coarse-matrix
leg, and `2\sqrt 2` on both tails (`\sqrt 2` from the triangle step times `2`
from the geometric tail `\rho/(1-\rho) \le 2`).  All four are multiplied by the
multiscale Poincare constant of the bridge.

## Formalization readings

The readings of `Carriers.lean` (the dual pairing is volume normalized; a vector
field's dual seminorm is the Euclidean `\ell^2` aggregate of the scalar
seminorms of its coordinates) and of `PerScaleDefect.lean` (the manuscript index
set `z \in 3^n\Zd \cap \cu_m` is the set of triadic descendants at depth `m-n`,
and `\avsum` is `descendantsAverage`) are inherited unchanged.  Two further
readings are specific to this module.

1. *The multiscale sum is the negative circ norm at `(s,p,q) = (1,2,1)`.*  The
   manuscript's right-hand side is `\sum_{n=-\infty}^m 3^{-(m-n)} (\avsum_z
   |(f)_{z+\cu_n}|^2)^{1/2}`.  Here `3^{-m} \cdot cubeBesovCircNorm Q 1 2 1 f`
   is that sum: item 2 of the route proves that each partial sum of the circ
   norm is the printed sum truncated at a finite depth, with the same weight
   and the same average, and the circ norm is the supremum of those partial
   sums.  Unlike in `MultiscalePoincareBridge.lean`, where only the weight half
   was formalized, the depth average and the depth sum are identified here in
   Lean, for the maximizer gradient defect.
2. *The bi-infinite sum is a supremum of partial sums.*  The manuscript sums
   over all `n \le m`.  The upstream circ norm is `sSup` of the set of partial
   sums, which for a nonnegative summand is the value of the series, finite or
   not.  The passage from the uniform bound on partial sums to the bound on the
   supremum is `mul_sqrt_sum_sq_ciSup_le` and uses monotone convergence of a
   bounded monotone real sequence; no summability is assumed, it is a
   consequence of the four-term bound.
-/

namespace Algsuperdiff.Section3.Provider.Besov

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open HCPolySupport.Book.Ch05.Section53
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## The per-depth identification -/

omit [NeZero d] in
private theorem sum_descendantsAverage (Q : TriadicCube d) (j : ℕ)
    (f : Fin d → TriadicCube d → ℝ) :
    ∑ i : Fin d, descendantsAverage Q j (f i) =
      descendantsAverage Q j fun R => ∑ i : Fin d, f i R := by
  dsimp only [descendantsAverage]
  rw [← Finset.mul_sum, Finset.sum_comm]

/-- **The per-depth identification.**  Summing the depth-`j` circ averages of the
coordinates of the maximizer gradient defect over the coordinate index gives the
descendant average of the squared deviation from the parent comparison
vector.
It is public because the `l.J.bound.by.Besov` assembly re-enters the chain at
this depth, before the coordinate aggregation. -/
theorem sum_cubeBesovCircDepthAverage_maximizerGradientDefect (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) (Q : TriadicCube d) (p q : Vec d) (j : ℕ) :
    ∑ i : Fin d,
        cubeBesovCircDepthAverage Q (2 : ℝ≥0∞)
          (fun x => maximizerGradientDefect a ha Q p q x i) j =
      descendantsAverage Q j (parentCoarseScaleSeparationDeviationSq a ha Q p q) := by
  have hnorm : ∀ x : ℝ, ‖x‖ ^ (2 : ℝ≥0∞).toReal = x ^ 2 := by
    intro x
    rw [show ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      Real.norm_eq_abs, sq_abs]
  simp only [cubeBesovCircDepthAverage]
  rw [sum_descendantsAverage]
  refine JUpperBoundWeakNorms.descendantsAverage_congr_of_eq_on_descendants Q j ?_
  intro R hR
  have hfield : maximizerGradientDefect a ha Q p q =
      JUpperBoundWeakNorms.canonicalMaximizerGradientDefectOnCube Q
        ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q) p q
        (coarseScaleSeparation a ha Q p q) := rfl
  have havg : cubeAverageVec R (maximizerGradientDefect a ha Q p q) =
      Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q a.toFun -
        coarseScaleSeparation a ha Q p q := by
    rw [hfield]
    exact
      JUpperBoundWeakNorms.cubeAverageCanonicalGradientDefect_eq_responseGradientAverage
        a ha hR p q _
  calc
    ∑ i : Fin d, ‖cubeAverage R (fun x => maximizerGradientDefect a ha Q p q x i)‖ ^
          (2 : ℝ≥0∞).toReal
        = ∑ i : Fin d, cubeAverageVec R (maximizerGradientDefect a ha Q p q) i ^ 2 :=
          Finset.sum_congr rfl fun i _ => hnorm _
    _ = vecNormSq (cubeAverageVec R (maximizerGradientDefect a ha Q p q)) := by
          simp [vecNormSq, vecDot, pow_two]
    _ = parentCoarseScaleSeparationDeviationSq a ha Q p q R := by
          rw [havg, parentCoarseScaleSeparationDeviationSq]

/-! ## The depth-indexed multiscale term -/

private theorem rpow_neg_natCast_eq_inv_pow (j : ℕ) :
    (3 : ℝ) ^ (-(j : ℝ)) = ((3 : ℝ) ^ j)⁻¹ := by
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_natCast]

/-! ## Splitting the depth range at the base scale -/

private theorem sum_range_le_head_add_tail (K N : ℕ) (T : ℕ → ℝ) (hT : ∀ j, 0 ≤ T j) :
    ∑ j ∈ Finset.range (N + 2), T j ≤
      (∑ j ∈ Finset.range (K + 1), T j) + ∑ i ∈ Finset.range (N + 2), T (K + 1 + i) := by
  classical
  set B : Finset ℕ := (Finset.range (N + 2)).image (fun i => K + 1 + i) with hB
  have hsub : Finset.range (N + 2) ⊆ Finset.range (K + 1) ∪ B := by
    intro j hj
    simp only [Finset.mem_range] at hj
    by_cases hjk : j < K + 1
    · exact Finset.mem_union_left _ (Finset.mem_range.mpr hjk)
    · refine Finset.mem_union_right _ ?_
      refine Finset.mem_image.mpr ⟨j - (K + 1), Finset.mem_range.mpr (by omega), by omega⟩
  have h1 : ∑ j ∈ Finset.range (N + 2), T j ≤ ∑ j ∈ Finset.range (K + 1) ∪ B, T j :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => hT j
  have h2 : (∑ j ∈ Finset.range (K + 1) ∪ B, T j) +
      ∑ j ∈ Finset.range (K + 1) ∩ B, T j =
      (∑ j ∈ Finset.range (K + 1), T j) + ∑ j ∈ B, T j :=
    Finset.sum_union_inter
  have h3 : 0 ≤ ∑ j ∈ Finset.range (K + 1) ∩ B, T j :=
    Finset.sum_nonneg fun j _ => hT j
  have h4 : ∑ j ∈ B, T j = ∑ i ∈ Finset.range (N + 2), T (K + 1 + i) := by
    rw [hB]
    exact Finset.sum_image fun x _ y _ hxy => by omega
  linarith

/-! ## Reindexing the two ranges -/

omit [NeZero d] in
/-- The head of the depth range is the manuscript sum over `n \in [L_0,m]`. -/
private theorem sum_range_head_eq_sum_Icc (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) {m L₀ : ℤ} (hLm : L₀ ≤ m) (p q : Vec d) :
    ∑ j ∈ Finset.range ((m - L₀).toNat + 1),
        ((3 : ℝ) ^ j)⁻¹ *
          Real.sqrt (descendantsAverage (originCube d m) j
            (parentCoarseScaleSeparationDeviationSq a ha (originCube d m) p q)) =
      ∑ n ∈ Finset.Icc L₀ m,
        (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
          Real.sqrt (descendantsAverage (originCube d m) (m - n).toNat
            (parentCoarseScaleSeparationDeviationSq a ha (originCube d m) p q)) := by
  refine Finset.sum_nbij' (fun j : ℕ => m - (j : ℤ)) (fun n : ℤ => (m - n).toNat) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_range] at hj
    simp only [Finset.mem_Icc]
    omega
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    simp only [Finset.mem_range]
    omega
  · intro j hj
    simp only [Finset.mem_range] at hj
    show (m - (m - (j : ℤ))).toNat = j
    omega
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    show m - (((m - n).toNat : ℕ) : ℤ) = n
    omega
  · intro j _
    have hj2 : m - (m - (j : ℤ)) = (j : ℤ) := by ring
    rw [hj2, Int.toNat_natCast, Int.cast_natCast, rpow_neg_natCast_eq_inv_pow]

omit [NeZero d] in
/-- The tail of the depth range is the manuscript sum over `n < L_0`. -/
private theorem sum_range_tail_eq (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) {m L₀ : ℤ} (hLm : L₀ ≤ m) (p q : Vec d)
    (M : ℕ) :
    ∑ i ∈ Finset.range M,
        ((3 : ℝ) ^ ((m - L₀).toNat + 1 + i))⁻¹ *
          Real.sqrt (descendantsAverage (originCube d m) ((m - L₀).toNat + 1 + i)
            (parentCoarseScaleSeparationDeviationSq a ha (originCube d m) p q)) =
      ∑ i ∈ Finset.range M,
        (3 : ℝ) ^ (-((m - (L₀ - 1 - (i : ℤ)) : ℤ) : ℝ)) *
          Real.sqrt (descendantsAverage (originCube d m) (m - (L₀ - 1 - (i : ℤ))).toNat
            (parentCoarseScaleSeparationDeviationSq a ha (originCube d m) p q)) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  have hK : ((m - L₀).toNat : ℤ) = m - L₀ := Int.toNat_of_nonneg (by omega)
  have hidx : m - (L₀ - 1 - (i : ℤ)) = (((m - L₀).toNat + 1 + i : ℕ) : ℤ) := by
    push_cast
    omega
  rw [hidx, Int.toNat_natCast, Int.cast_natCast, rpow_neg_natCast_eq_inv_pow]

/-! ## The four-term bound at every depth cutoff -/

/-- **The four printed right-hand terms bound every partial multiscale sum.**
The head of the depth range is discharged by the summed large-scale display and
the tail by the small-scale tail, on the identical summand.
It is public because the `l.J.bound.by.Besov` assembly bounds its own partial
multiscale sums by the same four terms. -/
theorem sum_range_multiscaleTerm_le_fourTerm (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) {m L₀ : ℤ} (hLm : L₀ ≤ m)
    {s : ℝ} (hs : 0 < s) (hs2 : s ≤ 1 / 2)
    {r : Ch02.MultiscaleExponent} (hr : r.IsAdmissible) (p q : Vec d) (N : ℕ) :
    ∑ j ∈ Finset.range (N + 2),
        ((3 : ℝ) ^ j)⁻¹ *
          Real.sqrt (descendantsAverage (originCube d m) j
            (parentCoarseScaleSeparationDeviationSq a ha (originCube d m) p q)) ≤
      2 * Real.sqrt ((Ch04.lambdaSqCoeffField (originCube d m) s r a)⁻¹) *
            (∑ n ∈ Finset.Icc L₀ m,
              (3 : ℝ) ^ (-(1 - s) * ((m - n : ℤ) : ℝ)) *
                Real.sqrt (WeakNormsMaximizer.responseDefectAverageAtScale m n p q a)) +
          Real.sqrt 2 *
            (∑ n ∈ Finset.Icc L₀ m,
              (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
                Real.sqrt (descendantsAverage (originCube d m) (m - n).toNat
                  (coarseMatrixVariationSq a ha (originCube d m) p q))) +
          2 * Real.sqrt 2 *
            ((3 : ℝ) ^ (-(1 - s) * ((m - L₀ : ℤ) : ℝ)) *
              Real.sqrt ((Ch04.lambdaSqCoeffField (originCube d m) s r a)⁻¹) *
              maximizerEnergyL2Norm a ha (originCube d m) p q) +
          2 * Real.sqrt 2 *
            ((3 : ℝ) ^ (-((m - L₀ : ℤ) : ℝ)) *
              Real.sqrt (vecNormSq (coarseScaleSeparation a ha (originCube d m) p q))) := by
  have hT : ∀ j : ℕ,
      0 ≤ ((3 : ℝ) ^ j)⁻¹ *
        Real.sqrt (descendantsAverage (originCube d m) j
          (parentCoarseScaleSeparationDeviationSq a ha (originCube d m) p q)) := by
    intro j
    positivity
  have hP3 :=
    sum_Icc_weighted_sqrt_descendantsAverage_parentCoarseScaleSeparationDeviationSq_le
      a ha m L₀ hs hr p q
  have hP4 := sum_range_smallScale_multiscaleTerm_le a ha hLm hs hs2 hr p q (N + 2)
  calc
    ∑ j ∈ Finset.range (N + 2),
        ((3 : ℝ) ^ j)⁻¹ *
          Real.sqrt (descendantsAverage (originCube d m) j
            (parentCoarseScaleSeparationDeviationSq a ha (originCube d m) p q))
        ≤ (∑ j ∈ Finset.range ((m - L₀).toNat + 1),
              ((3 : ℝ) ^ j)⁻¹ *
                Real.sqrt (descendantsAverage (originCube d m) j
                  (parentCoarseScaleSeparationDeviationSq a ha (originCube d m) p q))) +
            ∑ i ∈ Finset.range (N + 2),
              ((3 : ℝ) ^ ((m - L₀).toNat + 1 + i))⁻¹ *
                Real.sqrt (descendantsAverage (originCube d m) ((m - L₀).toNat + 1 + i)
                  (parentCoarseScaleSeparationDeviationSq a ha (originCube d m) p q)) :=
          sum_range_le_head_add_tail ((m - L₀).toNat) N _ hT
    _ = (∑ n ∈ Finset.Icc L₀ m,
              (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
                Real.sqrt (descendantsAverage (originCube d m) (m - n).toNat
                  (parentCoarseScaleSeparationDeviationSq a ha (originCube d m) p q))) +
            ∑ i ∈ Finset.range (N + 2),
              (3 : ℝ) ^ (-((m - (L₀ - 1 - (i : ℤ)) : ℤ) : ℝ)) *
                Real.sqrt (descendantsAverage (originCube d m) (m - (L₀ - 1 - (i : ℤ))).toNat
                  (parentCoarseScaleSeparationDeviationSq a ha (originCube d m) p q)) := by
          rw [sum_range_head_eq_sum_Icc a ha hLm p q, sum_range_tail_eq a ha hLm p q (N + 2)]
    _ ≤ (2 * Real.sqrt ((Ch04.lambdaSqCoeffField (originCube d m) s r a)⁻¹) *
              (∑ n ∈ Finset.Icc L₀ m,
                (3 : ℝ) ^ (-(1 - s) * ((m - n : ℤ) : ℝ)) *
                  Real.sqrt (WeakNormsMaximizer.responseDefectAverageAtScale m n p q a)) +
            Real.sqrt 2 *
              ∑ n ∈ Finset.Icc L₀ m,
                (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
                  Real.sqrt (descendantsAverage (originCube d m) (m - n).toNat
                    (coarseMatrixVariationSq a ha (originCube d m) p q))) +
            (2 * Real.sqrt 2 *
                ((3 : ℝ) ^ (-(1 - s) * ((m - L₀ : ℤ) : ℝ)) *
                  Real.sqrt ((Ch04.lambdaSqCoeffField (originCube d m) s r a)⁻¹) *
                  maximizerEnergyL2Norm a ha (originCube d m) p q) +
              2 * Real.sqrt 2 *
                ((3 : ℝ) ^ (-((m - L₀ : ℤ) : ℝ)) *
                  Real.sqrt (vecNormSq (coarseScaleSeparation a ha (originCube d m) p q)))) :=
          add_le_add hP3 hP4
    _ = _ := by ring

end

end Algsuperdiff.Section3.Provider.Besov
