/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Besov.PerScaleDefect

/-!
# LargeScaleSplit

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The large-scale split of the Section 3.5 negative-norm lemma

This module establishes the deterministic estimates behind the large-scale part
of the multiscale sum that occurs in the proof of `l.Besov.norms`.  Fix a cube
`Q = \cu_m` and a scale `n` with `L_0 \le n \le m`.
The manuscript compares the descendant averages `(\nabla v)_{z+\cu_n}` with the
*parent* comparison vector `\s_*^{-1}(\cu_m)(q+\k(\cu_m)p) - p`, and splits that
deviation into

* the **local** deviation from the comparison vector of the descendant itself,
  which is `coarseScaleSeparationDeviationSq` of `PerScaleDefect.lean`; and
* the **coarse-matrix variation**
  `\s_*^{-1}(\cu_m)(q+\k(\cu_m)p) - \s_*^{-1}(z+\cu_n)(q+\k(z+\cu_n)p)`.

The two summed right-hand sides produced here have the shape of the first two
right-hand terms of `e.Besov.norms.gradient`.  Nothing about the left-hand side
of that display, and nothing about the status of the lemma, is asserted here.

## Formalization readings

1. *The manuscript constant `C`.*  ABK26 prints an unspecified `C` in front
   of both legs of the split.  The explicit value obtained from the
   pointwise Euclidean inequality `|x-y|^2 \le 2(|x|^2+|y|^2)` is `\sqrt
   2`, and that literal value is carried here; every statement below is
   therefore an instance of the printed display with `C` given a value.
2. *The index set.*  The manuscript sums over `z \in 3^n\Zd \cap \cu_m`, which
   is the set of triadic descendants of `\cu_m` at depth `m-n`, and `\avsum`
   is `descendantsAverage`.  The outer sum over `n` from `L_0` to `m` is
   `Finset.Icc L₀ m` in `\Z`.
3. *The coarse-matrix variation.*  ABK26 prints
   `\s_*^{-1}(\cu_m)(q+\k(\cu_m)p) - \s_*^{-1}(z+\cu_n)(q+\k(z+\cu_n)p)`,
   without the `-p` that both comparison vectors carry.  Since the `-p`
   cancels in the difference, `coarseMatrixVariationSq` is the difference
   of the two `coarseScaleSeparation` vectors, which is literally the
   printed vector.
-/

namespace Algsuperdiff.Section3.Provider.Besov

open HCPolySupport HCPolySupport.Book
open HCPolySupport.Book.Ch05.Section53

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## The two squared deviations of the split -/

/-- The comparison vector is the one attached to the *parent* cube `Q`, and is
constant in `R`. -/
def parentCoarseScaleSeparationDeviationSq (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) (Q : TriadicCube d)
    (p q : Vec d) (R : TriadicCube d) : ℝ :=
  vecNormSq
    (Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q a.toFun -
      coarseScaleSeparation a ha Q p q)

/-- The manuscript quantity `| \s_*^{-1}(\cu_m)(q + \k(\cu_m)p) - \s_*^{-1}(R)(q
+ \k(R)p) |^2`, written as the squared length of the difference of the two
  `Carriers.lean` comparison vectors.  The `-p` carried by each of them cancels
  in the difference, so this is literally the printed vector. -/
def coarseMatrixVariationSq (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) (Q : TriadicCube d)
    (p q : Vec d) (R : TriadicCube d) : ℝ :=
  vecNormSq (coarseScaleSeparation a ha Q p q - coarseScaleSeparation a ha R p q)

omit [NeZero d] in
theorem coarseMatrixVariationSq_nonneg (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) (Q : TriadicCube d)
    (p q : Vec d) (R : TriadicCube d) :
    0 ≤ coarseMatrixVariationSq a ha Q p q R :=
  vecNormSq_nonneg _

/-! ## The per-scale two-term split -/

omit [NeZero d] in
/-- **The per-scale split.**  At a fixed depth the root of the descendant average
of the deviation from the *parent* comparison vector is at most `\sqrt 2` times
the root of the descendant average of the deviation from the *local* comparison
vector, plus `\sqrt 2` times the root of the descendant average of the
coarse-matrix variation.

The literal `\sqrt 2` is the explicit value of the manuscript constant `C`
printed; it comes from the pointwise Euclidean inequality `|x-y|^2 \le
2(|x|^2+|y|^2)`. -/
theorem sqrt_descendantsAverage_parentCoarseScaleSeparationDeviationSq_le
    (a : RegCoeffField d) (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) (j : ℕ) (p q : Vec d) :
    Real.sqrt (descendantsAverage Q j (parentCoarseScaleSeparationDeviationSq a ha Q p q)) ≤
      Real.sqrt 2 *
          Real.sqrt (descendantsAverage Q j (coarseScaleSeparationDeviationSq a ha Q p q)) +
        Real.sqrt 2 *
          Real.sqrt (descendantsAverage Q j (coarseMatrixVariationSq a ha Q p q)) := by
  set A : ℝ := descendantsAverage Q j (coarseScaleSeparationDeviationSq a ha Q p q) with hA
  set B : ℝ := descendantsAverage Q j (coarseMatrixVariationSq a ha Q p q) with hB
  have hA0 : 0 ≤ A :=
    descendantsAverage_nonneg Q j _ fun R _ =>
      coarseScaleSeparationDeviationSq_nonneg a ha Q p q R
  have hB0 : 0 ≤ B :=
    descendantsAverage_nonneg Q j _ fun R _ => coarseMatrixVariationSq_nonneg a ha Q p q R
  have hpoint : ∀ R ∈ descendantsAtDepth Q j,
      parentCoarseScaleSeparationDeviationSq a ha Q p q R ≤
        2 * (coarseScaleSeparationDeviationSq a ha Q p q R +
          coarseMatrixVariationSq a ha Q p q R) := by
    intro R _
    have hsplit :
        Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q a.toFun -
              coarseScaleSeparation a ha Q p q =
          (Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q a.toFun -
              coarseScaleSeparation a ha R p q) -
            (coarseScaleSeparation a ha Q p q - coarseScaleSeparation a ha R p q) := by
      abel
    rw [parentCoarseScaleSeparationDeviationSq, hsplit]
    exact vecNormSq_sub_le _ _
  have havg : descendantsAverage Q j (parentCoarseScaleSeparationDeviationSq a ha Q p q) ≤
      2 * A + 2 * B := by
    calc
      descendantsAverage Q j (parentCoarseScaleSeparationDeviationSq a ha Q p q)
          ≤ descendantsAverage Q j
              (fun R => 2 * (coarseScaleSeparationDeviationSq a ha Q p q R +
                coarseMatrixVariationSq a ha Q p q R)) :=
            descendantsAverage_le_descendantsAverage Q j hpoint
      _ = 2 * descendantsAverage Q j
            (fun R => coarseScaleSeparationDeviationSq a ha Q p q R +
              coarseMatrixVariationSq a ha Q p q R) :=
            descendantsAverage_smul Q j 2 _
      _ = 2 * (A + B) := by rw [descendantsAverage_add]
      _ = 2 * A + 2 * B := by ring
  calc
    Real.sqrt (descendantsAverage Q j (parentCoarseScaleSeparationDeviationSq a ha Q p q))
        ≤ Real.sqrt (2 * A + 2 * B) := Real.sqrt_le_sqrt havg
    _ ≤ Real.sqrt (2 * A) + Real.sqrt (2 * B) :=
          sqrt_add_le_add_sqrt_of_nonneg (by positivity) (by positivity)
    _ = Real.sqrt 2 * Real.sqrt A + Real.sqrt 2 * Real.sqrt B := by
          rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
            Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]

/-! ## The weighted per-scale display -/

/-- Weight arithmetic: the multiscale weight `3^{-(m-n)}` composed with the
ellipticity factor `3^{s(m-n)}` is the manuscript discount `3^{-(1-s)(m-n)}`. -/
theorem rpow_neg_mul_rpow_mul (s x : ℝ) :
    (3 : ℝ) ^ (-x) * (3 : ℝ) ^ (s * x) = (3 : ℝ) ^ (-(1 - s) * x) := by
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  congr 1
  ring

/-- The constant `2` of the first summand is `\sqrt 2` from the split times `\sqrt
2` from the defect estimate. -/
theorem weighted_sqrt_descendantsAverage_parentCoarseScaleSeparationDeviationSq_le_atScale
    (a : RegCoeffField d) (ha : Ch04.AELocallyUniformlyEllipticField a)
    {m n : ℤ} (hnm : n ≤ m) {s : ℝ} (hs : 0 < s)
    {r : Ch02.MultiscaleExponent} (hr : r.IsAdmissible) (p q : Vec d) :
    (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
        Real.sqrt
          (descendantsAverage (originCube d m) (m - n).toNat
            (parentCoarseScaleSeparationDeviationSq a ha (originCube d m) p q)) ≤
      2 * Real.sqrt ((Ch04.lambdaSqCoeffField (originCube d m) s r a)⁻¹) *
          ((3 : ℝ) ^ (-(1 - s) * ((m - n : ℤ) : ℝ)) *
            Real.sqrt (WeakNormsMaximizer.responseDefectAverageAtScale m n p q a)) +
        Real.sqrt 2 *
          ((3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
            Real.sqrt
              (descendantsAverage (originCube d m) (m - n).toNat
                (coarseMatrixVariationSq a ha (originCube d m) p q))) := by
  set Q : TriadicCube d := originCube d m with hQ
  set j : ℕ := (m - n).toNat with hj
  set w : ℝ := (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) with hw
  have hw0 : 0 ≤ w := (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).le
  have hsplit :=
    sqrt_descendantsAverage_parentCoarseScaleSeparationDeviationSq_le a ha Q j p q
  have hdefect :=
    sqrt_descendantsAverage_coarseScaleSeparationDeviationSq_le_atScale a ha hnm hs hr p q
  have hstep :
      w *
          Real.sqrt
            (descendantsAverage Q j (parentCoarseScaleSeparationDeviationSq a ha Q p q)) ≤
        w * (Real.sqrt 2 *
              (Real.sqrt 2 * (3 : ℝ) ^ (s * ((m - n : ℤ) : ℝ)) *
                Real.sqrt ((Ch04.lambdaSqCoeffField Q s r a)⁻¹) *
                Real.sqrt (WeakNormsMaximizer.responseDefectAverageAtScale m n p q a)) +
            Real.sqrt 2 *
              Real.sqrt (descendantsAverage Q j (coarseMatrixVariationSq a ha Q p q))) := by
    refine mul_le_mul_of_nonneg_left (hsplit.trans ?_) hw0
    have hmono :
        Real.sqrt 2 * Real.sqrt (descendantsAverage Q j
              (coarseScaleSeparationDeviationSq a ha Q p q)) ≤
          Real.sqrt 2 *
            (Real.sqrt 2 * (3 : ℝ) ^ (s * ((m - n : ℤ) : ℝ)) *
              Real.sqrt ((Ch04.lambdaSqCoeffField Q s r a)⁻¹) *
              Real.sqrt (WeakNormsMaximizer.responseDefectAverageAtScale m n p q a)) :=
      mul_le_mul_of_nonneg_left hdefect (Real.sqrt_nonneg 2)
    exact add_le_add hmono le_rfl
  refine hstep.trans_eq ?_
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 :=
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hweight :
      w * (3 : ℝ) ^ (s * ((m - n : ℤ) : ℝ)) =
        (3 : ℝ) ^ (-(1 - s) * ((m - n : ℤ) : ℝ)) :=
    rpow_neg_mul_rpow_mul s _
  calc
    w * (Real.sqrt 2 *
            (Real.sqrt 2 * (3 : ℝ) ^ (s * ((m - n : ℤ) : ℝ)) *
              Real.sqrt ((Ch04.lambdaSqCoeffField Q s r a)⁻¹) *
              Real.sqrt (WeakNormsMaximizer.responseDefectAverageAtScale m n p q a)) +
          Real.sqrt 2 *
            Real.sqrt (descendantsAverage Q j (coarseMatrixVariationSq a ha Q p q)))
        = (Real.sqrt 2 * Real.sqrt 2) *
              Real.sqrt ((Ch04.lambdaSqCoeffField Q s r a)⁻¹) *
              ((w * (3 : ℝ) ^ (s * ((m - n : ℤ) : ℝ))) *
                Real.sqrt (WeakNormsMaximizer.responseDefectAverageAtScale m n p q a)) +
            Real.sqrt 2 *
              (w * Real.sqrt (descendantsAverage Q j (coarseMatrixVariationSq a ha Q p q))) := by
          ring
    _ = 2 * Real.sqrt ((Ch04.lambdaSqCoeffField Q s r a)⁻¹) *
            ((3 : ℝ) ^ (-(1 - s) * ((m - n : ℤ) : ℝ)) *
              Real.sqrt (WeakNormsMaximizer.responseDefectAverageAtScale m n p q a)) +
          Real.sqrt 2 *
            (w * Real.sqrt (descendantsAverage Q j (coarseMatrixVariationSq a ha Q p q))) := by
          rw [hsq, hweight]

/-! ## The summed large-scale display -/

/-- **The summed large-scale display.**  Summing the weighted per-scale display
over `n \in [L_0,m] \cap \Z` produces exactly the first two right-hand terms of
`e.Besov.norms.gradient`, with the manuscript constant `C` given the explicit
values `2` and `\sqrt 2`. -/
theorem sum_Icc_weighted_sqrt_descendantsAverage_parentCoarseScaleSeparationDeviationSq_le
    (a : RegCoeffField d) (ha : Ch04.AELocallyUniformlyEllipticField a)
    (m L₀ : ℤ) {s : ℝ} (hs : 0 < s)
    {r : Ch02.MultiscaleExponent} (hr : r.IsAdmissible) (p q : Vec d) :
    (∑ n ∈ Finset.Icc L₀ m,
        (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
          Real.sqrt
            (descendantsAverage (originCube d m) (m - n).toNat
              (parentCoarseScaleSeparationDeviationSq a ha (originCube d m) p q))) ≤
      2 * Real.sqrt ((Ch04.lambdaSqCoeffField (originCube d m) s r a)⁻¹) *
          (∑ n ∈ Finset.Icc L₀ m,
            (3 : ℝ) ^ (-(1 - s) * ((m - n : ℤ) : ℝ)) *
              Real.sqrt (WeakNormsMaximizer.responseDefectAverageAtScale m n p q a)) +
        Real.sqrt 2 *
          ∑ n ∈ Finset.Icc L₀ m,
            (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
              Real.sqrt
                (descendantsAverage (originCube d m) (m - n).toNat
                  (coarseMatrixVariationSq a ha (originCube d m) p q)) := by
  have hterm : ∀ n ∈ Finset.Icc L₀ m,
      (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
          Real.sqrt
            (descendantsAverage (originCube d m) (m - n).toNat
              (parentCoarseScaleSeparationDeviationSq a ha (originCube d m) p q)) ≤
        2 * Real.sqrt ((Ch04.lambdaSqCoeffField (originCube d m) s r a)⁻¹) *
            ((3 : ℝ) ^ (-(1 - s) * ((m - n : ℤ) : ℝ)) *
              Real.sqrt (WeakNormsMaximizer.responseDefectAverageAtScale m n p q a)) +
          Real.sqrt 2 *
            ((3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
              Real.sqrt
                (descendantsAverage (originCube d m) (m - n).toNat
                  (coarseMatrixVariationSq a ha (originCube d m) p q))) := by
    intro n hn
    have hnm : n ≤ m := (Finset.mem_Icc.mp hn).2
    exact
      weighted_sqrt_descendantsAverage_parentCoarseScaleSeparationDeviationSq_le_atScale
        a ha hnm hs hr p q
  refine (Finset.sum_le_sum hterm).trans_eq ?_
  rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

end

end Algsuperdiff.Section3.Provider.Besov
