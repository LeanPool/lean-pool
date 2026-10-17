/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Besov.BesovNorms
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Besov.CentralChildCaccioppoli
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Besov.JBesovPrefactor
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Besov.OscillationPoincare
public import LeanPool.Superdiffusion.Support.Book.Ch03.Theorems.CoarseCaccioppoliRHS.PublicRHSMonotonicity
public import LeanPool.HighContrastHomogenization.Support.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.Additivity.CrossTerm
public import LeanPool.HighContrastHomogenization.Support.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.Additivity.ParentRestriction

/-!
# JBoundByBesov

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The `J`-bound composite of Section 3.5, on the multiscale right-hand side

This module assembles the estimate of ABK26 `l.J.bound.by.Besov` for the
canonical maximizer on a centred cube, with the negative Sobolev factor of the
printed display replaced by the proved multiscale upper bound of this
directory.  The two structural features of the printed right-hand side that the
consumer needs are retained verbatim: the literal factor `2` and the literal
depth-one sum `\sum_{z \in 3^{m-1}\Zd \cap \cu_m}` of the response defects.

Nothing about the status of the lemma `l.J.bound.by.Besov` is asserted here.

## Route

1. *The digging room*.  The response of the ordinary central child is the child
   average of the child half-energy
   (`JUpperBoundWeakNorms.responseJOnCube_eq_cubeAverage_topHalfEnergy`); the
   pointwise polarization `\tfrac12 \xi\cdot\s\xi \le \eta\cdot\s\eta +
   (\eta-\xi)\cdot\s(\eta-\xi)` at an elliptic matrix replaces it by the parent
   energy plus the parent-minus-child difference energy; the difference
   energies of the other depth-one children are nonnegative and are added; and
   the summed difference energy is the summed response defect, by the upstream
   partition identity
for the descendant average of the half-difference energy and the response partition defect.
   The last step is where the literal `2` and the literal depth-one sum are
   produced.
2. *The Caccioppoli step*.  `CentralChildCaccioppoli.lean` bounds the
   parent-coefficient energy on the ordinary central child by the upstream
   interior Caccioppoli right-hand side of the parent, and
   `JBesovPrefactor.lean` bounds the diagonal prefactor on `0 < s \le 1/4` by a
   dimension-only envelope times the three displayed factors
   `\Theta^{s/(1-2s)}`, `\Lambda_{s,1}` and `3^{-2m}`.
3. *The oscillation step*, replacing.  `OscillationPoincare.lean` bounds the
   parent oscillation `L^2` square that the Caccioppoli right-hand side leaves
   by the square of the coordinate sum of the negative circ Besov norms of the
   gradient coordinates at `(s,p,q) = (1,2,1)`.
4. *The centring step.*  Each depth-`j` circ average of a gradient coordinate is
   bounded by twice the depth-`j` circ average of the corresponding coordinate
   of the gradient *defect* plus twice the squared coordinate of the comparison
   vector `c = \s_*^{-1}(\cu_m)(q+\k(\cu_m)p) - p`, because the descendant
   average of the gradient is the descendant average of the defect shifted by
   `c`.  Summing the circ weights, whose total is at most `\tfrac32 \cdot 3^m`,
   and passing to the supremum with
   `Homogenization.cubeBesovCircNorm_le_of_forall_entry_le`, which is taken
   one coordinate at a time, by dominating a single coordinate entry with the
   full coordinate sum and re-summing over the `d` coordinates, at the cost of
   a further factor `d`, converts the coordinate sum of circ norms into the
   multiscale average sum of the centred gradient plus the length of `c`.
5. *The coordinate aggregation.*  The bound produced by step 3 aggregates the
   coordinates in `\ell^1`, while the printed multiscale sum aggregates them
   inside each depth term in the Euclidean norm.  Cauchy's inequality in the
   coordinate index converts one into the other at the cost of `\sqrt d`, which
   the dimension-only constant absorbs.  This is the conversion that
   `OscillationPoincare.lean` records but does not formalize; it is formalized
   here, in `weighted_sum_sqrt_le`.

## Correspondence with the printed display

The printed right-hand side is

`C \Lambda_{s,1}(\cu_m) (\Lambda_{s,1}/\lambda_{s,1})^{s/(1-2s)} 3^{-2m} \|
\nabla v \|_{\Hminusul(\cu_m)}^2
  + \sum_{z\in 3^{m-1}\Zd\cap\cu_m} 2 (J(z+\cu_{m-1}) - J(\cu_m))`.

The composite below carries `\Lambda_{s,1}(\cu_m;\a)` as
`Ch02.LambdaS (originCube d m) s`, whose body is the `q = 1` convention
`Ch02.LambdaSq (originCube d m) s (.finite 1)`; the ellipticity ratio as
`Ch02.ThetaRatio (originCube d m) s s`, whose body is
`Ch02.LambdaS (originCube d m) s / Ch02.lambdaS (originCube d m) s`, raised to
`s/(1-2s)`; and the depth-one sum
verbatim on `descendantsAtDepth (originCube d m) 1`, which is the set of the
`3^d` children `z+\cu_{m-1}` of `\cu_m`.  Two features differ from the printed
display and are load bearing.

1. *The negative Sobolev factor is replaced by its multiscale upper bound.*
   `3^{-2m}\|\nabla v\|_{\Hminusul}^2` is replaced by the square of
   `centredMultiscaleAverageSum`, the manuscript sum `\sum_{n\le m}
   3^{-(m-n)}(\avsum_z|(\nabla v - c)_{z+\cu_n}|^2)^{1/2}`.  The scale weight
   `3^{-m}` of the printed display is carried inside that sum, by the
   reindexing `n = m-j`, exactly as `Carriers.scaledNegHMinusOne` carries it at
   the use site.  The replacement is in the direction of a weaker estimate: the
   proved bridge
   `MultiscalePoincareBridge.scaledNegHMinusOne_le_multiscaleAverageSum` bounds
   the negative Sobolev object by the multiscale sum and no reverse comparison
   is available, so no statement here is equivalent to the printed one.  The
   bridge's own right-hand side is the Euclidean coordinate aggregate of the
   same circ norms, which lies below the coordinate sum used here; the
   comparison is therefore in the stated direction only up to the `√d`
   coordinate aggregation, and no declaration in this directory compares the
   negative Sobolev object to the multiscale average sum directly.
2. *The centring term is explicit.*  Because the multiscale sum of item 1 is
   the sum of the **centred** gradient, the centring of step 4 leaves the
   summand `|c|`, written `Real.sqrt (vecNormSq (coarseScaleSeparation ...))`.
   Squared, it is exactly the third summand of the consumer display at
   ,
   `C \shom_L \E [ | \s_{L,*}^{-1}(\cu_m)(q+\k_L(\cu_m)p) - p |^2 ]`, so the
   consumer already carries it.
   The manuscript's own copy of that summand comes from squaring the fourth
   printed term of `e.Besov.norms.gradient`, which carries the discount
   `3^{-(m-L_0)}`; the term produced here carries none, matching the
   undiscounted form.  It is therefore a second, independent copy
   of the same summand, which the consumer's constant absorbs.  It is kept
   explicit rather than absorbed.

## Formalization readings

The readings of `Carriers.lean`, `PerScaleDefect.lean` and `BesovNorms.lean`
(the pairing is volume normalized; a vector field's dual seminorm is the
Euclidean `\ell^2` aggregate; the index set `z \in 3^n\Zd \cap \cu_m` is the set
of triadic descendants at depth `m-n` and `\avsum` is `descendantsAverage`; the
bi-infinite sum over `n \le m` is the supremum of its partial sums) are
inherited unchanged.  One further reading is specific to this module.

*The multiscale average sum is the supremum of its partial sums.*
`centredMultiscaleAverageSum` is `⨆ N, \sum_{j < N} 3^{-j}(\ldots)^{1/2}`.  The
supremum is finite: `partialMultiscaleSum_le_fourTerm` bounds every partial sum
by the four printed terms of `e.Besov.norms.gradient`, at the admissible
parameters `L_0 = m`, `s = 1/4` and `r = \infty`, so the defining family is
bounded above and `centredMultiscaleAverageSum_le_fourTerm` transfers the
four-term bound to the supremum itself at every admissible parameter choice.
-/

namespace Algsuperdiff.Section3.Provider.Besov

open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03
open HCPolySupport.Book.Ch05.Section53
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## Scalar helpers -/

private theorem sqrt_add_le_add_sqrt {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  have h1 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have h2 : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
  have hx' : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
  have hy' : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy
  have hsq : x + y ≤ (Real.sqrt x + Real.sqrt y) ^ 2 := by nlinarith [mul_nonneg h1 h2]
  calc
    Real.sqrt (x + y) ≤ Real.sqrt ((Real.sqrt x + Real.sqrt y) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt x + Real.sqrt y := Real.sqrt_sq (by positivity)

omit [NeZero d] in
private theorem sum_le_sqrt_dim_mul_sqrt_sum_sq (x : Fin d → ℝ) :
    ∑ i : Fin d, x i ≤ Real.sqrt (d : ℝ) * Real.sqrt (∑ i : Fin d, x i ^ 2) := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin d)) (fun _ => (1 : ℝ)) x
  simpa using h

private theorem sum_range_inv_three_pow_eq (K : ℕ) :
    ∑ j ∈ Finset.range K, ((3 : ℝ) ^ j)⁻¹ = 3 / 2 - (3 / 2) * ((3 : ℝ) ^ K)⁻¹ := by
  induction K with
  | zero => norm_num
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    have h : ((3 : ℝ) ^ (K + 1))⁻¹ = ((3 : ℝ) ^ K)⁻¹ / 3 := by
      rw [pow_succ]
      have h3 : ((3 : ℝ) ^ K) ≠ 0 := by positivity
      field_simp
    rw [h]
    ring

private theorem sum_range_inv_three_pow_le (K : ℕ) :
    ∑ j ∈ Finset.range K, ((3 : ℝ) ^ j)⁻¹ ≤ 3 / 2 := by
  rw [sum_range_inv_three_pow_eq K]
  have h : (0 : ℝ) ≤ ((3 : ℝ) ^ K)⁻¹ := by positivity
  linarith

/-! ## The circ entry at `(s,p,q) = (1,2,1)` -/

omit [NeZero d] in
private theorem circNormEntry_one_two_one (Q : TriadicCube d) (u : Vec d → ℝ) (N : ℕ) :
    cubeBesovCircNormEntry Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N u =
      ∑ j ∈ Finset.range (N + 2),
        cubeBesovCircDepthWeight Q 1 j *
          Real.sqrt (cubeBesovCircDepthAverage Q (2 : ℝ≥0∞) u j) := by
  have hterm : ∀ j : ℕ,
      cubeBesovCircDepthSeminorm Q 1 (2 : ℝ≥0∞) u j ^ (1 : ℝ≥0∞).toReal =
        cubeBesovCircDepthWeight Q 1 j *
          Real.sqrt (cubeBesovCircDepthAverage Q (2 : ℝ≥0∞) u j) := by
    intro j
    rw [ENNReal.toReal_one, Real.rpow_one, cubeBesovCircDepthSeminorm, Real.sqrt_eq_rpow]
    norm_num
  rw [cubeBesovCircNormEntry, ite_eq_right (by simp : (1 : ℝ≥0∞) ≠ ∞), cubeBesovCircPartialNorm,
    cubeBesovCircPartialSeminorm, Finset.sum_congr rfl (fun j _ => hterm j), ENNReal.toReal_one]
  norm_num

omit [NeZero d] in
private theorem circNormEntry_nonneg (Q : TriadicCube d) (u : Vec d → ℝ) (N : ℕ) :
    0 ≤ cubeBesovCircNormEntry Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N u := by
  rw [circNormEntry_one_two_one]
  exact Finset.sum_nonneg fun j _ =>
    mul_nonneg (cubeBesovCircDepthWeight_nonneg Q 1 j) (Real.sqrt_nonneg _)

omit [NeZero d] in
private theorem scale_mul_depthWeight (m : ℤ) (j : ℕ) :
    (3 : ℝ) ^ (-m) * cubeBesovCircDepthWeight (originCube d m) 1 j = ((3 : ℝ) ^ j)⁻¹ := by
  have h1 : ((3 : ℝ) ^ m) ≠ 0 := zpow_ne_zero m (by norm_num : (3 : ℝ) ≠ 0)
  have h2 : ((3 : ℝ) ^ j : ℝ) ≠ 0 := by positivity
  have hscale : (originCube d m).scale = m := rfl
  rw [cubeBesovCircDepthWeight_one, hscale, zpow_neg]
  field_simp

omit [NeZero d] in
/-- The abstract form of the centring step: a weighted depth sum of coordinate
`\ell^1` aggregates of square roots, whose summands are controlled by a centred
square plus a constant square, is bounded by the same weighted sum of the
`\ell^2`-aggregated centred squares plus the constant, at the cost of `\sqrt 2`
and `\sqrt d`. -/
private theorem weighted_sum_sqrt_le (A B : Fin d → ℕ → ℝ) (cc : Fin d → ℝ) (S : ℕ → ℝ)
    (w : ℕ → ℝ) (K : ℕ) (hw : ∀ j, 0 ≤ w j) (hB : ∀ i j, 0 ≤ B i j)
    (hA : ∀ i j, A i j ≤ 2 * B i j + 2 * cc i ^ 2)
    (hS : ∀ j, ∑ i : Fin d, B i j = S j) :
    ∑ i : Fin d, ∑ j ∈ Finset.range K, w j * Real.sqrt (A i j) ≤
      Real.sqrt 2 * Real.sqrt (d : ℝ) * (∑ j ∈ Finset.range K, w j * Real.sqrt (S j)) +
        Real.sqrt 2 * Real.sqrt (d : ℝ) * Real.sqrt (∑ i : Fin d, cc i ^ 2) *
          ∑ j ∈ Finset.range K, w j := by
  have hsqrt2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsqrtd : (0 : ℝ) ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
  have hperij : ∀ (i : Fin d) (j : ℕ),
      Real.sqrt (A i j) ≤ Real.sqrt 2 * Real.sqrt (B i j) + Real.sqrt 2 * |cc i| := by
    intro i j
    have h1 : Real.sqrt (A i j) ≤ Real.sqrt (2 * B i j + 2 * cc i ^ 2) :=
      Real.sqrt_le_sqrt (hA i j)
    have h2 : Real.sqrt (2 * B i j + 2 * cc i ^ 2) ≤
        Real.sqrt (2 * B i j) + Real.sqrt (2 * cc i ^ 2) :=
      sqrt_add_le_add_sqrt (by linarith [hB i j]) (by positivity)
    have h3 : Real.sqrt (2 * B i j) = Real.sqrt 2 * Real.sqrt (B i j) :=
      Real.sqrt_mul (by norm_num) _
    have h4 : Real.sqrt (2 * cc i ^ 2) = Real.sqrt 2 * |cc i| := by
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq_eq_abs]
    linarith
  have hperj : ∀ j : ℕ,
      ∑ i : Fin d, Real.sqrt (A i j) ≤
        Real.sqrt 2 * Real.sqrt (d : ℝ) * Real.sqrt (S j) +
          Real.sqrt 2 * Real.sqrt (d : ℝ) * Real.sqrt (∑ i : Fin d, cc i ^ 2) := by
    intro j
    have hstep1 :
        ∑ i : Fin d, Real.sqrt (A i j) ≤
          Real.sqrt 2 * ∑ i : Fin d, Real.sqrt (B i j) +
            Real.sqrt 2 * ∑ i : Fin d, |cc i| := by
      have := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) => hperij i j)
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at this
      exact this
    have hstep2 :
        ∑ i : Fin d, Real.sqrt (B i j) ≤ Real.sqrt (d : ℝ) * Real.sqrt (S j) := by
      have h := sum_le_sqrt_dim_mul_sqrt_sum_sq (fun i => Real.sqrt (B i j))
      have hsq : ∑ i : Fin d, Real.sqrt (B i j) ^ 2 = S j := by
        rw [← hS j]
        exact Finset.sum_congr rfl fun i _ => Real.sq_sqrt (hB i j)
      rwa [hsq] at h
    have hstep3 :
        ∑ i : Fin d, |cc i| ≤ Real.sqrt (d : ℝ) * Real.sqrt (∑ i : Fin d, cc i ^ 2) := by
      have h := sum_le_sqrt_dim_mul_sqrt_sum_sq (fun i => |cc i|)
      have hsq : ∑ i : Fin d, |cc i| ^ 2 = ∑ i : Fin d, cc i ^ 2 :=
        Finset.sum_congr rfl fun i _ => sq_abs _
      rwa [hsq] at h
    nlinarith [hsqrt2, hsqrtd, hstep1, hstep2, hstep3]
  calc
    ∑ i : Fin d, ∑ j ∈ Finset.range K, w j * Real.sqrt (A i j)
        = ∑ j ∈ Finset.range K, w j * ∑ i : Fin d, Real.sqrt (A i j) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => (Finset.mul_sum _ _ _).symm
    _ ≤ ∑ j ∈ Finset.range K,
          w j * (Real.sqrt 2 * Real.sqrt (d : ℝ) * Real.sqrt (S j) +
            Real.sqrt 2 * Real.sqrt (d : ℝ) * Real.sqrt (∑ i : Fin d, cc i ^ 2)) :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hperj j) (hw j)
    _ = Real.sqrt 2 * Real.sqrt (d : ℝ) * (∑ j ∈ Finset.range K, w j * Real.sqrt (S j)) +
          Real.sqrt 2 * Real.sqrt (d : ℝ) * Real.sqrt (∑ i : Fin d, cc i ^ 2) *
            ∑ j ∈ Finset.range K, w j := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun j _ => by ring

/-! ## The centred multiscale average sum -/

/-- The manuscript multiscale average sum
`\sum_{n \le m} 3^{-(m-n)} ( \avsum_{z} | (\nabla v - c)_{z+\cu_n} |^2 )^{1/2}`
, for the canonical maximizer gradient defect on `\cu_m` and
the comparison vector `c = \s_*^{-1}(\cu_m)(q+\k(\cu_m)p) - p`.

The reindexing `n = m - j` turns the printed discount `3^{-(m-n)}` into `3^{-j}`
and the printed index set `z \in 3^n\Zd \cap \cu_m` into the triadic descendants
at depth `j`; the bi-infinite sum over `n \le m` is the supremum of the partial
sums, exactly as in `BesovNorms.lean`. -/
noncomputable def centredMultiscaleAverageSum (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) (m : ℤ) (p q : Vec d) : ℝ :=
  ⨆ N : ℕ,
    ∑ j ∈ Finset.range N,
      ((3 : ℝ) ^ j)⁻¹ *
        Real.sqrt (descendantsAverage (originCube d m) j
          (parentCoarseScaleSeparationDeviationSq a ha (originCube d m) p q))

/-- Every partial multiscale sum is bounded by the four printed right-hand terms of
`e.Besov.norms.gradient`.  This is the proved four-term display of
`BesovNorms.lean`, restated at an arbitrary truncation of the depth range. -/
theorem partialMultiscaleSum_le_fourTerm (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) {m L₀ : ℤ} (hLm : L₀ ≤ m)
    {s : ℝ} (hs : 0 < s) (hs2 : s ≤ 1 / 2)
    {r : Ch02.MultiscaleExponent} (hr : r.IsAdmissible) (p q : Vec d) (K : ℕ) :
    ∑ j ∈ Finset.range K,
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
  have hsub : Finset.range K ⊆ Finset.range (K + 2) := by
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub ?_) ?_
  · intro j _ _
    positivity
  · exact sum_range_multiscaleTerm_le_fourTerm a ha hLm hs hs2 hr p q K

private theorem bddAbove_partialMultiscaleSums (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) (m : ℤ) (p q : Vec d) :
    BddAbove (Set.range fun N : ℕ =>
      ∑ j ∈ Finset.range N,
        ((3 : ℝ) ^ j)⁻¹ *
          Real.sqrt (descendantsAverage (originCube d m) j
            (parentCoarseScaleSeparationDeviationSq a ha (originCube d m) p q))) := by
  obtain ⟨C, hC⟩ :
      ∃ C : ℝ, ∀ N : ℕ,
        (∑ j ∈ Finset.range N,
          ((3 : ℝ) ^ j)⁻¹ *
            Real.sqrt (descendantsAverage (originCube d m) j
              (parentCoarseScaleSeparationDeviationSq a ha (originCube d m) p q))) ≤ C :=
    ⟨_, fun N =>
      partialMultiscaleSum_le_fourTerm a ha (le_refl m) (by norm_num : (0 : ℝ) < 1 / 4)
        (by norm_num : (1 : ℝ) / 4 ≤ 1 / 2)
        (r := Ch02.MultiscaleExponent.infinity) trivial p q N⟩
  refine ⟨C, ?_⟩
  rintro y ⟨N, rfl⟩
  exact hC N

/-- Every partial multiscale sum is below the multiscale average sum. -/
theorem partialMultiscaleSum_le_centredMultiscaleAverageSum (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) (m : ℤ) (p q : Vec d) (K : ℕ) :
    ∑ j ∈ Finset.range K,
        ((3 : ℝ) ^ j)⁻¹ *
          Real.sqrt (descendantsAverage (originCube d m) j
            (parentCoarseScaleSeparationDeviationSq a ha (originCube d m) p q)) ≤
      centredMultiscaleAverageSum a ha m p q :=
  le_ciSup (bddAbove_partialMultiscaleSums a ha m p q) K

theorem centredMultiscaleAverageSum_nonneg (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) (m : ℤ) (p q : Vec d) :
    0 ≤ centredMultiscaleAverageSum a ha m p q := by
  have h := partialMultiscaleSum_le_centredMultiscaleAverageSum a ha m p q 0
  simpa using h

/-- **The multiscale average sum obeys the four-term display of `l.Besov.norms`.**
This is the form in which the composite below meets the proved
`e.Besov.norms.gradient` estimate. -/
theorem centredMultiscaleAverageSum_le_fourTerm (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) {m L₀ : ℤ} (hLm : L₀ ≤ m)
    {s : ℝ} (hs : 0 < s) (hs2 : s ≤ 1 / 2)
    {r : Ch02.MultiscaleExponent} (hr : r.IsAdmissible) (p q : Vec d) :
    centredMultiscaleAverageSum a ha m p q ≤
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
              Real.sqrt (vecNormSq (coarseScaleSeparation a ha (originCube d m) p q))) :=
  ciSup_le fun N => partialMultiscaleSum_le_fourTerm a ha hLm hs hs2 hr p q N

/-! ## The centring step -/

omit [NeZero d] in
private theorem vecNormSq_eq_sum_sq (x : Vec d) : vecNormSq x = ∑ i : Fin d, x i ^ 2 := by
  simp [vecNormSq, vecDot, pow_two]

omit [NeZero d] in
/-- The descendant average of the maximizer gradient is the descendant average of
its defect, shifted by the parent comparison vector. -/
private theorem cubeAverage_maximizerGradient_eq_add (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) (Q : TriadicCube d) (p q : Vec d)
    {R : TriadicCube d} {j : ℕ} (hR : R ∈ descendantsAtDepth Q j) (i : Fin d) :
    cubeAverage R (fun x => (canonicalCubeMaximizerSolution a ha Q p q).toH1.grad x i) =
      cubeAverage R (fun x => maximizerGradientDefect a ha Q p q x i) +
        coarseScaleSeparation a ha Q p q i := by
  have hmem :
      MemLp (fun x => (canonicalCubeMaximizerSolution a ha Q p q).toH1.grad x i)
        (2 : ℝ≥0∞) (normalizedCubeMeasure R) :=
    memLp_component_of_memLp _ i
      (JUpperBoundWeakNorms.canonicalMaximizerGradientOnCube_memLp_descendant Q R
        ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q) hR p q)
  have hdefect :
      (fun x => maximizerGradientDefect a ha Q p q x i) =
        fun x =>
          (canonicalCubeMaximizerSolution a ha Q p q).toH1.grad x i -
            coarseScaleSeparation a ha Q p q i := rfl
  rw [hdefect, cubeAverage_sub_const_of_memLp_two R hmem]
  ring

omit [NeZero d] in
/-- The depth-`j` circ average of a maximizer gradient coordinate is bounded by
twice the depth-`j` circ average of the corresponding defect coordinate plus
twice the squared coordinate of the comparison vector. -/
private theorem circDepthAverage_maximizerGradient_le (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) (Q : TriadicCube d) (p q : Vec d)
    (i : Fin d) (j : ℕ) :
    cubeBesovCircDepthAverage Q (2 : ℝ≥0∞)
        (fun x => (canonicalCubeMaximizerSolution a ha Q p q).toH1.grad x i) j ≤
      2 * cubeBesovCircDepthAverage Q (2 : ℝ≥0∞)
          (fun x => maximizerGradientDefect a ha Q p q x i) j +
        2 * coarseScaleSeparation a ha Q p q i ^ 2 := by
  have hnorm : ∀ x : ℝ, ‖x‖ ^ (2 : ℝ≥0∞).toReal = x ^ 2 := by
    intro x
    rw [show ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      Real.norm_eq_abs, sq_abs]
  have halg : ∀ (F : TriadicCube d → ℝ) (k : ℝ),
      descendantsAverage Q j (fun R => 2 * F R + 2 * k) =
        2 * descendantsAverage Q j F + 2 * k := by
    intro F k
    rw [descendantsAverage_add Q j (fun R => 2 * F R) (fun _ => 2 * k),
      descendantsAverage_smul Q j 2 F, descendantsAverage_const]
  have hpt : ∀ R ∈ descendantsAtDepth Q j,
      ‖cubeAverage R (fun x => (canonicalCubeMaximizerSolution a ha Q p q).toH1.grad x i)‖ ^
          (2 : ℝ≥0∞).toReal ≤
        2 * ‖cubeAverage R (fun x => maximizerGradientDefect a ha Q p q x i)‖ ^
            (2 : ℝ≥0∞).toReal + 2 * coarseScaleSeparation a ha Q p q i ^ 2 := by
    intro R hR
    rw [hnorm, hnorm, cubeAverage_maximizerGradient_eq_add a ha Q p q hR i]
    nlinarith [sq_nonneg (cubeAverage R (fun x => maximizerGradientDefect a ha Q p q x i) -
      coarseScaleSeparation a ha Q p q i)]
  simp only [cubeBesovCircDepthAverage]
  exact (descendantsAverage_le_descendantsAverage Q j hpt).trans_eq (halg _ _)

/-- **The centring step.**  The scaled coordinate sum of the negative circ norms of
the maximizer gradient is bounded by the multiscale average sum of the
*centred* gradient plus the length of the comparison vector, with a
dimension-only constant.  The second summand is the term the manuscript already
carries, squared. -/
theorem sum_cubeBesovCircNorm_maximizerGradient_le (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) (m : ℤ) (p q : Vec d) :
    (3 : ℝ) ^ (-m) *
        ∑ i : Fin d,
          cubeBesovCircNorm (originCube d m) 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (fun x =>
              (canonicalCubeMaximizerSolution a ha (originCube d m) p q).toH1.grad x i) ≤
      3 / 2 * Real.sqrt 2 * (d : ℝ) * Real.sqrt (d : ℝ) *
        (centredMultiscaleAverageSum a ha m p q +
          Real.sqrt (vecNormSq (coarseScaleSeparation a ha (originCube d m) p q))) := by
  have hsqrt2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsqrtd : (0 : ℝ) ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
  have hMS : 0 ≤ centredMultiscaleAverageSum a ha m p q :=
    centredMultiscaleAverageSum_nonneg a ha m p q
  have hc : 0 ≤ Real.sqrt (vecNormSq (coarseScaleSeparation a ha (originCube d m) p q)) :=
    Real.sqrt_nonneg _
  have hpow : (0 : ℝ) < (3 : ℝ) ^ (-m) := by positivity
  obtain ⟨target, htarget⟩ :
      ∃ t : ℝ, t =
        3 / 2 * Real.sqrt 2 * Real.sqrt (d : ℝ) *
          (centredMultiscaleAverageSum a ha m p q +
            Real.sqrt (vecNormSq (coarseScaleSeparation a ha (originCube d m) p q))) :=
    ⟨_, rfl⟩
  -- the scaled coordinate sum of the depth-`N` entries
  have hsum : ∀ N : ℕ,
      (3 : ℝ) ^ (-m) *
          ∑ i : Fin d,
            cubeBesovCircNormEntry (originCube d m) 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
              (fun x =>
                (canonicalCubeMaximizerSolution a ha (originCube d m) p q).toH1.grad x i) ≤
        Real.sqrt 2 * Real.sqrt (d : ℝ) * centredMultiscaleAverageSum a ha m p q +
          Real.sqrt 2 * Real.sqrt (d : ℝ) *
            Real.sqrt (vecNormSq (coarseScaleSeparation a ha (originCube d m) p q)) *
            (3 / 2) := by
    intro N
    have hexp :
        (3 : ℝ) ^ (-m) *
            ∑ i : Fin d,
              cubeBesovCircNormEntry (originCube d m) 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
                (fun x =>
                  (canonicalCubeMaximizerSolution a ha (originCube d m) p q).toH1.grad x i) =
          ∑ i : Fin d,
            ∑ j ∈ Finset.range (N + 2),
              ((3 : ℝ) ^ j)⁻¹ *
                Real.sqrt (cubeBesovCircDepthAverage (originCube d m) (2 : ℝ≥0∞)
                  (fun x =>
                    (canonicalCubeMaximizerSolution a ha (originCube d m) p q).toH1.grad x i)
                  j) := by
      simp only [circNormEntry_one_two_one]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← mul_assoc, scale_mul_depthWeight]
    rw [hexp]
    have hmain :=
      weighted_sum_sqrt_le
        (A := fun (i : Fin d) (j : ℕ) =>
          cubeBesovCircDepthAverage (originCube d m) (2 : ℝ≥0∞)
            (fun x =>
              (canonicalCubeMaximizerSolution a ha (originCube d m) p q).toH1.grad x i) j)
        (B := fun (i : Fin d) (j : ℕ) =>
          cubeBesovCircDepthAverage (originCube d m) (2 : ℝ≥0∞)
            (fun x => maximizerGradientDefect a ha (originCube d m) p q x i) j)
        (cc := fun i : Fin d => coarseScaleSeparation a ha (originCube d m) p q i)
        (S := fun j : ℕ =>
          descendantsAverage (originCube d m) j
            (parentCoarseScaleSeparationDeviationSq a ha (originCube d m) p q))
        (w := fun j : ℕ => ((3 : ℝ) ^ j)⁻¹) (K := N + 2)
        (fun j => by positivity)
        (fun i j => cubeBesovCircDepthAverage_nonneg (originCube d m) (2 : ℝ≥0∞) _ j)
        (fun i j =>
          circDepthAverage_maximizerGradient_le a ha (originCube d m) p q i j)
        (fun j =>
          sum_cubeBesovCircDepthAverage_maximizerGradientDefect a ha (originCube d m) p q j)
    rw [← vecNormSq_eq_sum_sq] at hmain
    refine hmain.trans (add_le_add ?_ ?_)
    · exact mul_le_mul_of_nonneg_left
        (partialMultiscaleSum_le_centredMultiscaleAverageSum a ha m p q (N + 2))
        (by positivity)
    · exact mul_le_mul_of_nonneg_left (sum_range_inv_three_pow_le (N + 2)) (by positivity)
  -- every entry is below the target, uniformly in the depth cutoff
  have hentry : ∀ (i : Fin d) (N : ℕ),
      cubeBesovCircNormEntry (originCube d m) 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
          (fun x =>
            (canonicalCubeMaximizerSolution a ha (originCube d m) p q).toH1.grad x i) ≤
        (3 : ℝ) ^ m * target := by
    intro i N
    have hsingle :
        cubeBesovCircNormEntry (originCube d m) 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
            (fun x =>
              (canonicalCubeMaximizerSolution a ha (originCube d m) p q).toH1.grad x i) ≤
          ∑ i' : Fin d,
            cubeBesovCircNormEntry (originCube d m) 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
              (fun x =>
                (canonicalCubeMaximizerSolution a ha (originCube d m) p q).toH1.grad x i') :=
      Finset.single_le_sum (f := fun i' : Fin d =>
        cubeBesovCircNormEntry (originCube d m) 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
          (fun x =>
            (canonicalCubeMaximizerSolution a ha (originCube d m) p q).toH1.grad x i'))
        (fun i' _ => circNormEntry_nonneg _ _ _) (Finset.mem_univ i)
    have hscaled := hsum N
    have hbound :
        Real.sqrt 2 * Real.sqrt (d : ℝ) * centredMultiscaleAverageSum a ha m p q +
            Real.sqrt 2 * Real.sqrt (d : ℝ) *
              Real.sqrt (vecNormSq (coarseScaleSeparation a ha (originCube d m) p q)) *
              (3 / 2) ≤ target := by
      have hexpand :
          target =
            3 / 2 * (Real.sqrt 2 * Real.sqrt (d : ℝ) *
                centredMultiscaleAverageSum a ha m p q) +
              3 / 2 * (Real.sqrt 2 * Real.sqrt (d : ℝ) *
                Real.sqrt (vecNormSq (coarseScaleSeparation a ha (originCube d m) p q))) := by
        rw [htarget]; ring
      have hnonneg : 0 ≤ Real.sqrt 2 * Real.sqrt (d : ℝ) *
          centredMultiscaleAverageSum a ha m p q :=
        mul_nonneg (mul_nonneg hsqrt2 hsqrtd) hMS
      rw [hexpand]
      linarith
    have hfinal :
        (3 : ℝ) ^ (-m) *
            ∑ i' : Fin d,
              cubeBesovCircNormEntry (originCube d m) 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
                (fun x =>
                  (canonicalCubeMaximizerSolution a ha (originCube d m) p q).toH1.grad x i') ≤
          target := hscaled.trans hbound
    have hmul := mul_le_mul_of_nonneg_left hfinal (le_of_lt (show (0:ℝ) < (3:ℝ)^m by positivity))
    rw [← mul_assoc] at hmul
    have hcancel : (3 : ℝ) ^ m * (3 : ℝ) ^ (-m) = 1 := by
      rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      simp
    rw [hcancel, one_mul] at hmul
    exact hsingle.trans hmul
  have hcirc : ∀ i : Fin d,
      cubeBesovCircNorm (originCube d m) 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
          (fun x =>
            (canonicalCubeMaximizerSolution a ha (originCube d m) p q).toH1.grad x i) ≤
        (3 : ℝ) ^ m * target := fun i =>
    cubeBesovCircNorm_le_of_forall_entry_le (originCube d m) 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) _
      (hentry i)
  have hsumcirc :
      ∑ i : Fin d,
          cubeBesovCircNorm (originCube d m) 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (fun x =>
              (canonicalCubeMaximizerSolution a ha (originCube d m) p q).toH1.grad x i) ≤
        (d : ℝ) * ((3 : ℝ) ^ m * target) := by
    have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) => hcirc i)
    simpa using h
  have hcancel : (3 : ℝ) ^ (-m) * (3 : ℝ) ^ m = 1 := by
    rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    simp
  calc
    (3 : ℝ) ^ (-m) *
        ∑ i : Fin d,
          cubeBesovCircNorm (originCube d m) 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (fun x =>
              (canonicalCubeMaximizerSolution a ha (originCube d m) p q).toH1.grad x i)
        ≤ (3 : ℝ) ^ (-m) * ((d : ℝ) * ((3 : ℝ) ^ m * target)) :=
          mul_le_mul_of_nonneg_left hsumcirc hpow.le
    _ = ((3 : ℝ) ^ (-m) * (3 : ℝ) ^ m) * ((d : ℝ) * target) := by ring
    _ = (d : ℝ) * target := by rw [hcancel, one_mul]
    _ = 3 / 2 * Real.sqrt 2 * (d : ℝ) * Real.sqrt (d : ℝ) *
          (centredMultiscaleAverageSum a ha m p q +
            Real.sqrt (vecNormSq (coarseScaleSeparation a ha (originCube d m) p q))) := by
          rw [htarget]; ring

/-! ## The subadditivity digging room -/

omit [NeZero d] in
/-- Pointwise polarization at a single elliptic matrix: half the child energy is
below the parent energy plus the parent-minus-child energy. -/
private theorem half_symm_energy_le_energy_add_diff {lam Lam : ℝ} (A : Mat d)
    (hA : IsEllipticMatrix lam Lam A) (top child : Vec d) :
    (1 / 2 : ℝ) * vecDot child (matVecMul (symmPart A) child) ≤
      vecDot top (matVecMul (symmPart A) top) +
        vecDot (top - child) (matVecMul (symmPart A) (top - child)) := by
  have hlower := lowerBound_symmPart_of_isEllipticMatrix hA (top - (1 / 2 : ℝ) • child)
  have hnorm : 0 ≤ vecNormSq (top - (1 / 2 : ℝ) • child) :=
    vecNormSq_nonneg (top - (1 / 2 : ℝ) • child)
  have hw_nonneg :
      0 ≤ vecDot (top - (1 / 2 : ℝ) • child)
        (matVecMul (symmPart A) (top - (1 / 2 : ℝ) • child)) := by
    nlinarith [hA.1]
  have hcomm :
      vecDot child (matVecMul (symmPart A) top) =
        vecDot top (matVecMul (symmPart A) child) := by
    simpa using vecDot_matVecMul_symmPart_comm A child top
  have hid :
      vecDot top (matVecMul (symmPart A) top) +
            vecDot (top - child) (matVecMul (symmPart A) (top - child)) -
          (1 / 2 : ℝ) * vecDot child (matVecMul (symmPart A) child) =
        2 * vecDot (top - (1 / 2 : ℝ) • child)
          (matVecMul (symmPart A) (top - (1 / 2 : ℝ) • child)) := by
    simp [sub_eq_add_neg, matVecMul_add, matVecMul_neg, matVecMul_smul,
      vecDot_add_left, vecDot_add_right, vecDot_neg_left, vecDot_neg_right,
      vecDot_smul_left, vecDot_smul_right, hcomm]
    ring
  linarith

/-- The canonical child response is controlled by the parent energy on that child
plus the parent-minus-child difference energy.  This is the second line. -/
private theorem responseJ_le_two_topHalfEnergy_add_two_diffHalfEnergy (F : CoeffFamily d)
    (Q : TriadicCube d) {R : TriadicCube d} (hR : R ∈ descendantsAtDepth Q 1) (p q : Vec d)
    (hCoeff : (F.coeffOn Q).toCoeffField = (F.coeffOn R).toCoeffField) :
    Ch02.responseJ (Ch02.cubeDomain R) (F.coeffOn R) p q ≤
      2 * cubeAverage R
          (JUpperBoundWeakNorms.topHalfEnergyDensityOnCube Q (F.coeffOn Q) p q) +
        2 * cubeAverage R
          (JUpperBoundWeakNorms.additivityDiffHalfEnergyDensityOnFamilyOnCube F Q R p q) := by
  have hchild_int :
      IntegrableOn (JUpperBoundWeakNorms.topHalfEnergyDensityOnCube R (F.coeffOn R) p q)
        (cubeSet R) volume :=
    JUpperBoundWeakNorms.topHalfEnergyDensityOnCube_integrableOn_cubeSet R (F.coeffOn R) p q
  have hparent_int :
      IntegrableOn (JUpperBoundWeakNorms.topHalfEnergyDensityOnCube Q (F.coeffOn Q) p q)
        (cubeSet R) volume :=
    (JUpperBoundWeakNorms.topHalfEnergyDensityOnCube_integrableOn_cubeSet Q
      (F.coeffOn Q) p q).mono_set (cubeSet_subset_of_mem_descendantsAtDepth hR)
  have hdiff_int :
      IntegrableOn
        (JUpperBoundWeakNorms.additivityDiffHalfEnergyDensityOnFamilyOnCube F Q R p q)
        (cubeSet R) volume :=
    JUpperBoundWeakNorms.additivityDiffHalfEnergyDensityOnFamilyOnCube_integrableOn F Q hR p q
  have hrhs_int :
      IntegrableOn
        (fun x =>
          2 * JUpperBoundWeakNorms.topHalfEnergyDensityOnCube Q (F.coeffOn Q) p q x +
            2 * JUpperBoundWeakNorms.additivityDiffHalfEnergyDensityOnFamilyOnCube F Q R p q x)
        (cubeSet R) volume :=
    (hparent_int.const_mul 2).add (hdiff_int.const_mul 2)
  have hEllOpen :
      IsAEEllipticFieldOn (F.coeffOn R).lam (F.coeffOn R).Lam (openCubeSet R)
        (F.coeffOn R).toCoeffField := by
    simpa [Ch02.cubeDomain_coe] using
      JUpperBoundWeakNorms.ch02_coeffOn_isAEEllipticFieldOn (F.coeffOn R)
  have hEll :
      IsAEEllipticFieldOn (F.coeffOn R).lam (F.coeffOn R).Lam (cubeSet R)
        (F.coeffOn R).toCoeffField :=
    hEllOpen.cubeSet_of_openCubeSet
  have hpoint :
      JUpperBoundWeakNorms.topHalfEnergyDensityOnCube R (F.coeffOn R) p q ≤ᵐ[
          volumeMeasureOn (cubeSet R)]
        fun x =>
          2 * JUpperBoundWeakNorms.topHalfEnergyDensityOnCube Q (F.coeffOn Q) p q x +
            2 * JUpperBoundWeakNorms.additivityDiffHalfEnergyDensityOnFamilyOnCube
              F Q R p q x := by
    filter_upwards [hEll.ae_isEllipticMatrix] with x hx
    have hpol :=
      half_symm_energy_le_energy_add_diff ((F.coeffOn R).toCoeffField x) hx
        (JUpperBoundWeakNorms.canonicalMaximizerGradientOnCube Q (F.coeffOn Q) p q x)
        (JUpperBoundWeakNorms.canonicalMaximizerGradientOnCube R (F.coeffOn R) p q x)
    simpa [JUpperBoundWeakNorms.topHalfEnergyDensityOnCube, Ch02.variationEnergyIntegrand,
      JUpperBoundWeakNorms.additivityDiffHalfEnergyDensityOnFamilyOnCube,
      JUpperBoundWeakNorms.canonicalMaximizerGradientOnCube, hCoeff] using hpol
  have hintegral :
      ∫ x in cubeSet R, JUpperBoundWeakNorms.topHalfEnergyDensityOnCube R (F.coeffOn R) p q x
          ∂volume ≤
        ∫ x in cubeSet R,
          (2 * JUpperBoundWeakNorms.topHalfEnergyDensityOnCube Q (F.coeffOn Q) p q x +
            2 * JUpperBoundWeakNorms.additivityDiffHalfEnergyDensityOnFamilyOnCube F Q R p q x)
          ∂volume :=
    setIntegral_mono_ae_restrict hchild_int hrhs_int hpoint
  have havg :
      cubeAverage R (JUpperBoundWeakNorms.topHalfEnergyDensityOnCube R (F.coeffOn R) p q) ≤
        cubeAverage R
          (fun x =>
            2 * JUpperBoundWeakNorms.topHalfEnergyDensityOnCube Q (F.coeffOn Q) p q x +
              2 * JUpperBoundWeakNorms.additivityDiffHalfEnergyDensityOnFamilyOnCube
                F Q R p q x) := by
    unfold cubeAverage
    exact mul_le_mul_of_nonneg_left hintegral (inv_nonneg.mpr (cubeVolume_nonneg R))
  have hsplit :
      cubeAverage R
          (fun x =>
            2 * JUpperBoundWeakNorms.topHalfEnergyDensityOnCube Q (F.coeffOn Q) p q x +
              2 * JUpperBoundWeakNorms.additivityDiffHalfEnergyDensityOnFamilyOnCube
                F Q R p q x) =
        2 * cubeAverage R
            (JUpperBoundWeakNorms.topHalfEnergyDensityOnCube Q (F.coeffOn Q) p q) +
          2 * cubeAverage R
            (JUpperBoundWeakNorms.additivityDiffHalfEnergyDensityOnFamilyOnCube F Q R p q) := by
    rw [JUpperBoundWeakNorms.cubeAverage_add_of_integrableOn R
        (fun x => 2 * JUpperBoundWeakNorms.topHalfEnergyDensityOnCube Q (F.coeffOn Q) p q x)
        (fun x =>
          2 * JUpperBoundWeakNorms.additivityDiffHalfEnergyDensityOnFamilyOnCube F Q R p q x)
        (hparent_int.const_mul 2) (hdiff_int.const_mul 2),
      cubeAverage_const_mul, cubeAverage_const_mul]
  calc
    Ch02.responseJ (Ch02.cubeDomain R) (F.coeffOn R) p q =
        cubeAverage R (JUpperBoundWeakNorms.topHalfEnergyDensityOnCube R (F.coeffOn R) p q) :=
      JUpperBoundWeakNorms.responseJOnCube_eq_cubeAverage_topHalfEnergy R (F.coeffOn R) p q
    _ ≤ _ := havg.trans_eq hsplit

omit [NeZero d] in
/-- The full parent energy on the ordinary central child is exactly twice the
central-child average of the parent half-energy density. -/
private theorem centralChildCaccioppoliEnergy_eq_two_cubeAverage_topHalfEnergy
    (F : CoeffFamily d) (Q : TriadicCube d) (p q : Vec d) :
    centralChildCaccioppoliEnergy Q F
        (JUpperBoundWeakNorms.canonicalMaximizerSolutionOnCube Q (F.coeffOn Q) p q) =
      2 * cubeAverage (CubeCalderonZygmund.centralChild Q)
        (JUpperBoundWeakNorms.topHalfEnergyDensityOnCube Q (F.coeffOn Q) p q) := by
  have hdensity :
      JUpperBoundWeakNorms.topHalfEnergyDensityOnCube Q (F.coeffOn Q) p q =
        fun x =>
          (1 / 2 : ℝ) *
            Ch02.variationEnergyIntegrand (Ch02.cubeDomain Q) (F.coeffOn Q)
              (JUpperBoundWeakNorms.canonicalMaximizerSolutionOnCube Q (F.coeffOn Q) p q) x :=
    rfl
  have hbridge :
      centralChildCaccioppoliEnergy Q F
          (JUpperBoundWeakNorms.canonicalMaximizerSolutionOnCube Q (F.coeffOn Q) p q) =
        cubeAverage (CubeCalderonZygmund.centralChild Q)
          (Ch02.variationEnergyIntegrand (Ch02.cubeDomain Q) (F.coeffOn Q)
            (JUpperBoundWeakNorms.canonicalMaximizerSolutionOnCube Q (F.coeffOn Q) p q)) := by
    unfold centralChildCaccioppoliEnergy localizedCoeffEnergyValue normalizedSetAverage
      volumeAverage cubeAverage
    rw [volume_openCubeSet_toReal, ← setIntegral_cubeSet_eq_setIntegral_openCubeSet]
    rfl
  rw [hbridge, hdensity, cubeAverage_const_mul]
  ring

omit [NeZero d] in
/-- The summed difference energy over the depth-one children is the summed response
defect, with the literal factor `2`. -/
private theorem sum_two_cubeAverage_diffHalfEnergy_eq_sum_two_responseDefect
    (a : RegCoeffField d) (ha : Ch04.AELocallyUniformlyEllipticField a) (Q : TriadicCube d)
    (j : ℕ) (p q : Vec d) :
    ∑ R ∈ descendantsAtDepth Q j,
        2 * cubeAverage R
          (JUpperBoundWeakNorms.additivityDiffHalfEnergyDensityOnFamilyOnCube
            (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) Q R p q) =
      ∑ R ∈ descendantsAtDepth Q j,
        2 * (Ch02.responseJ (Ch02.cubeDomain R)
              ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn R) p q -
            Ch02.responseJ (Ch02.cubeDomain Q)
              ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q) p q) := by
  have hE :
      descendantsAverage Q j
          (fun R =>
            cubeAverage R
              (JUpperBoundWeakNorms.additivityDiffHalfEnergyDensityOnFamilyOnCube
                (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) Q R p q)) =
        JUpperBoundWeakNorms.responseJPartitionDefectOnFamilyAtDepth
          (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) Q j p q :=
    JUpperBoundWeakNorms.descendantMean_additivityHalfEnergy_eq_responseJDefect
      a ha Q j p q
  have hG :
      descendantsAverage Q j
          (fun R =>
            Ch02.responseJ (Ch02.cubeDomain R)
                ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn R) p q -
              Ch02.responseJ (Ch02.cubeDomain Q)
                ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
                p q) =
        JUpperBoundWeakNorms.responseJPartitionDefectOnFamilyAtDepth
          (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) Q j p q := by
    have hrewrite :
        (fun R : TriadicCube d =>
            Ch02.responseJ (Ch02.cubeDomain R)
                ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn R) p q -
              Ch02.responseJ (Ch02.cubeDomain Q)
                ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
                p q) =
          fun R : TriadicCube d =>
            Ch02.responseJ (Ch02.cubeDomain R)
                ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn R)
                p q +
              (-1 : ℝ) *
                Ch02.responseJ (Ch02.cubeDomain Q)
                  ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
                  p q := by
      funext R
      ring
    rw [hrewrite, descendantsAverage_add, descendantsAverage_smul, descendantsAverage_const]
    rw [JUpperBoundWeakNorms.responseJPartitionDefectOnFamilyAtDepth,
      JUpperBoundWeakNorms.childResponseJAverageOnFamilyAtDepth]
    ring
  have hcard : ((descendantsAtDepth Q j).card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr (descendantsAtDepth_nonempty Q j)
  have hsum :
      ∑ R ∈ descendantsAtDepth Q j,
          cubeAverage R
            (JUpperBoundWeakNorms.additivityDiffHalfEnergyDensityOnFamilyOnCube
              (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) Q R p q) =
        ∑ R ∈ descendantsAtDepth Q j,
          (Ch02.responseJ (Ch02.cubeDomain R)
              ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn R) p q -
            Ch02.responseJ (Ch02.cubeDomain Q)
              ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
              p q) := by
    refine mul_left_cancel₀ (inv_ne_zero hcard) ?_
    exact hE.trans hG.symm
  rw [← Finset.mul_sum, hsum, Finset.mul_sum]

/-- **The subadditivity digging room.**  The response of the ordinary central child
`\cu_{m-1}` is bounded by the parent-coefficient energy of the parent maximizer
on that child, plus the literal depth-one sum of twice the response defects. -/
theorem responseJ_centralChild_le_centralChildCaccioppoliEnergy_add_defectSum
    (a : RegCoeffField d) (ha : Ch04.AELocallyUniformlyEllipticField a) (Q : TriadicCube d)
    (p q : Vec d) :
    Ch02.responseJ (Ch02.cubeDomain (CubeCalderonZygmund.centralChild Q))
        ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn
          (CubeCalderonZygmund.centralChild Q)) p q ≤
      centralChildCaccioppoliEnergy Q
          (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)
          (canonicalCubeMaximizerSolution a ha Q p q) +
        ∑ R ∈ descendantsAtDepth Q 1,
          2 * (Ch02.responseJ (Ch02.cubeDomain R)
                ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn R) p q -
              Ch02.responseJ (Ch02.cubeDomain Q)
                ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
                p q) := by
  have hcentral : CubeCalderonZygmund.centralChild Q ∈ descendantsAtDepth Q 1 := by
    simpa [descendantsAtDepth_one] using CubeCalderonZygmund.centralChild_mem_childCubes Q
  have hlocal :=
    responseJ_le_two_topHalfEnergy_add_two_diffHalfEnergy
      (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) Q hcentral p q (by simp)
  have henergy :=
    centralChildCaccioppoliEnergy_eq_two_cubeAverage_topHalfEnergy
      (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) Q p q
  have hnonneg : ∀ R ∈ descendantsAtDepth Q 1,
      0 ≤ 2 * cubeAverage R
        (JUpperBoundWeakNorms.additivityDiffHalfEnergyDensityOnFamilyOnCube
          (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) Q R p q) := by
    intro R _
    exact mul_nonneg (by norm_num)
      (JUpperBoundWeakNorms.cubeAverage_additivityDiffHalfEnergyDensityOnFamilyOnCube_nonneg
        (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) Q R p q)
  have hsingle :
      2 * cubeAverage (CubeCalderonZygmund.centralChild Q)
          (JUpperBoundWeakNorms.additivityDiffHalfEnergyDensityOnFamilyOnCube
            (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) Q
            (CubeCalderonZygmund.centralChild Q) p q) ≤
        ∑ R ∈ descendantsAtDepth Q 1,
          2 * cubeAverage R
            (JUpperBoundWeakNorms.additivityDiffHalfEnergyDensityOnFamilyOnCube
              (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) Q R p q) :=
    Finset.single_le_sum hnonneg hcentral
  have hsum := sum_two_cubeAverage_diffHalfEnergy_eq_sum_two_responseDefect a ha Q 1 p q
  have hsolution :
      canonicalCubeMaximizerSolution a ha Q p q =
        JUpperBoundWeakNorms.canonicalMaximizerSolutionOnCube Q
          ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q) p q := rfl
  rw [hsolution, henergy, ← hsum]
  linarith

/-! ## The composite -/

omit [NeZero d] in
private theorem interiorCaccioppoliParentOscillationL2Sq_nonneg (Q : TriadicCube d)
    (F : CoeffFamily d) (u : CubeSolution Q F) :
    0 ≤ interiorCaccioppoliParentOscillationL2Sq Q F u := by
  unfold interiorCaccioppoliParentOscillationL2Sq normalizedL2SqOnSet normalizedSetAverage
    volumeAverage
  exact mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
    (integral_nonneg fun x => sq_nonneg _)

omit [NeZero d] in
/-- The ordinary central child of `\cu_m` is `\cu_{m-1}`. -/
private theorem centralChild_originCube (m : ℤ) :
    CubeCalderonZygmund.centralChild (originCube d m) = originCube d (m - 1) := by
  apply congrArg₂ TriadicCube.mk
  · rfl
  · funext i
    simp [originCube]

omit [NeZero d] in
private theorem sum_cubeBesovCircNorm_maximizerGradient_nonneg (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) (m : ℤ) (p q : Vec d) :
    0 ≤ ∑ i : Fin d,
      cubeBesovCircNorm (originCube d m) 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
        (fun x => (canonicalCubeMaximizerSolution a ha (originCube d m) p q).toH1.grad x i) := by
  let : IsProbabilityMeasure (normalizedCubeMeasure (originCube d m)) :=
    ⟨normalizedCubeMeasure_apply_univ (originCube d m)⟩
  refine Finset.sum_nonneg fun i _ => ?_
  refine cubeBesovCircNorm_nonneg (originCube d m) 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) _ ?_
  exact cubeBesovCircNormValueSet_bddAbove_of_memLp (originCube d m) 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) _
    (by norm_num)
    (H1Function.grad_memL2_normalizedCubeMeasure
      (canonicalCubeMaximizerSolution a ha (originCube d m) p q).toH1 i)
    (by norm_num) (by norm_num) le_rfl

omit [NeZero d] in
private theorem rpow_three_neg_two_scale (m : ℤ) :
    Real.rpow (3 : ℝ) (-2 * ((((originCube d m).scale : ℤ)) : ℝ)) = ((3 : ℝ) ^ (-m)) ^ 2 := by
  have hscale : ((originCube d m).scale : ℤ) = m := rfl
  rw [hscale, show (-2 * ((m : ℤ) : ℝ)) = (((-2 * m : ℤ)) : ℝ) by push_cast; ring]
  change (3 : ℝ) ^ ((((-2 * m : ℤ)) : ℝ)) = ((3 : ℝ) ^ (-m)) ^ 2
  rw [Real.rpow_intCast, show (-2 * m : ℤ) = -m + -m by ring,
    zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
  ring

/-- **The composite, with the negative Sobolev factor replaced by its proved
multiscale upper bound.**  For the canonical maximizer on `\cu_m`, the response
of the ordinary central child `\cu_{m-1}` is bounded by a dimension-only
constant times the coarse upper ellipticity `\Lambda_{s,1}`, times the coarse
ellipticity ratio raised to `s/(1-2s)`, times the square of the multiscale
average sum of the centred gradient plus the length of the comparison vector,
plus the literal depth-one sum of twice the response defects. -/
theorem exists_responseJ_centralChild_le_jBoundByBesovDisplay (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : RegCoeffField d) (ha : Ch04.AELocallyUniformlyEllipticField a) (m : ℤ)
        (p q : Vec d) {s : ℝ}, 0 < s → s ≤ 1 / 4 →
        Ch02.responseJ (Ch02.cubeDomain (originCube d (m - 1)))
            ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn
              (originCube d (m - 1))) p q ≤
          C *
                Ch02.LambdaS (originCube d m) s
                  (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) *
                Real.rpow (Ch02.ThetaRatio (originCube d m) s s
                    (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha))
                  (s / (1 - 2 * s)) *
                (centredMultiscaleAverageSum a ha m p q +
                    Real.sqrt (vecNormSq (coarseScaleSeparation a ha (originCube d m) p q))) ^ 2 +
            ∑ R ∈ descendantsAtDepth (originCube d m) 1,
              2 * (Ch02.responseJ (Ch02.cubeDomain R)
                      ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn R)
                      p q -
                    Ch02.responseJ (Ch02.cubeDomain (originCube d m))
                      ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn
                        (originCube d m)) p q) := by
  obtain ⟨C₆, hC₆pos, hcacc⟩ := centralChildCaccioppoli_canonicalMaximizer d
  have hd : (0 : ℝ) < (d : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hsqrt2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsqrtd : (0 : ℝ) < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hd
  have hEpos : 0 < jBesovCaccioppoliEnvelope C₆ := jBesovCaccioppoliEnvelope_pos C₆
  have hKpos : 0 < 3 / 2 * Real.sqrt 2 * (d : ℝ) * Real.sqrt (d : ℝ) := by positivity
  refine ⟨jBesovCaccioppoliEnvelope C₆ * (oscillationMultiscalePoincareConstant d ^ 2 + 1) *
    (3 / 2 * Real.sqrt 2 * (d : ℝ) * Real.sqrt (d : ℝ)) ^ 2, ?_, ?_⟩
  · have h2 : (0 : ℝ) < oscillationMultiscalePoincareConstant d ^ 2 + 1 := by positivity
    exact mul_pos (mul_pos hEpos h2) (pow_pos hKpos 2)
  intro a ha m p q s hs hs_quarter
  have hst : s + s < 1 := by linarith
  -- the objects of the display
  have hLambdaNonneg :
      0 ≤ Ch02.LambdaS (originCube d m) s
        (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) :=
    Ch02.LambdaSq_finite_nonneg (originCube d m)
      (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) hs le_rfl
  have hThetaNonneg :
      0 ≤ Real.rpow (Ch02.ThetaRatio (originCube d m) s s
          (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha))
        (s / (1 - 2 * s)) :=
    Real.rpow_nonneg (Ch02.ThetaRatio_nonneg (originCube d m)
      (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) hs hs) _
  have hSumNonneg := sum_cubeBesovCircNorm_maximizerGradient_nonneg a ha m p q
  have hcentring := sum_cubeBesovCircNorm_maximizerGradient_le a ha m p q
  have hprefNonneg :
      0 ≤ caccioppoliPrefactor C₆ (originCube d m)
        (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) s s :=
    caccioppoliPrefactor_nonneg hC₆pos.le hs hs hst
  have hoscNonneg :=
    interiorCaccioppoliParentOscillationL2Sq_nonneg (originCube d m)
      (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)
      (canonicalCubeMaximizerSolution a ha (originCube d m) p q)
  have hosc :=
    interiorCaccioppoliParentOscillationL2Sq_le_sq_sum_cubeBesovCircNorm (originCube d m)
      (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)
      (canonicalCubeMaximizerSolution a ha (originCube d m) p q)
  have hpref :=
    caccioppoliPrefactor_diag_le_jBesovEnvelope C₆ hC₆pos.le (originCube d m)
      (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) hs hs_quarter
  rw [rpow_three_neg_two_scale m] at hpref
  have hcaccRHS :=
    hcacc a ha (originCube d m) p q hs hs hst
  rw [interiorCaccioppoliRHS] at hcaccRHS
  -- the energy bound
  have henergy :
      centralChildCaccioppoliEnergy (originCube d m)
          (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)
          (canonicalCubeMaximizerSolution a ha (originCube d m) p q) ≤
        jBesovCaccioppoliEnvelope C₆ * (oscillationMultiscalePoincareConstant d ^ 2 + 1) *
            (3 / 2 * Real.sqrt 2 * (d : ℝ) * Real.sqrt (d : ℝ)) ^ 2 *
            Ch02.LambdaS (originCube d m) s
              (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) *
            Real.rpow (Ch02.ThetaRatio (originCube d m) s s
                (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha))
              (s / (1 - 2 * s)) *
            (centredMultiscaleAverageSum a ha m p q +
              Real.sqrt (vecNormSq (coarseScaleSeparation a ha (originCube d m) p q))) ^ 2 := by
    have hscaled :
        (3 : ℝ) ^ (-m) *
            ∑ i : Fin d,
              cubeBesovCircNorm (originCube d m) 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
                (fun x =>
                  (canonicalCubeMaximizerSolution a ha (originCube d m) p q).toH1.grad x i) ≥ 0 :=
      mul_nonneg (by positivity) hSumNonneg
    have hsq :
        ((3 : ℝ) ^ (-m)) ^ 2 *
            (∑ i : Fin d,
              cubeBesovCircNorm (originCube d m) 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
                (fun x =>
                  (canonicalCubeMaximizerSolution a ha (originCube d m) p q).toH1.grad x i)) ^ 2 ≤
          (3 / 2 * Real.sqrt 2 * (d : ℝ) * Real.sqrt (d : ℝ)) ^ 2 *
            (centredMultiscaleAverageSum a ha m p q +
              Real.sqrt (vecNormSq (coarseScaleSeparation a ha (originCube d m) p q))) ^ 2 := by
      simpa only [mul_pow] using pow_le_pow_left₀ hscaled hcentring 2
    have hstep1 := hcaccRHS
    have hstep2 :
        caccioppoliPrefactor C₆ (originCube d m)
              (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) s s *
            interiorCaccioppoliParentOscillationL2Sq (originCube d m)
              (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)
              (canonicalCubeMaximizerSolution a ha (originCube d m) p q) ≤
          (jBesovCaccioppoliEnvelope C₆ *
              (Real.rpow (Ch02.ThetaRatio (originCube d m) s s
                  (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha))
                (s / (1 - 2 * s)) *
                Ch02.LambdaS (originCube d m) s
                  (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) *
                ((3 : ℝ) ^ (-m)) ^ 2)) *
            (oscillationMultiscalePoincareConstant d *
              ∑ i : Fin d,
                cubeBesovCircNorm (originCube d m) 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
                  (fun x =>
                    (canonicalCubeMaximizerSolution a ha (originCube d m) p q).toH1.grad x i)) ^
              2 :=
      mul_le_mul hpref hosc hoscNonneg
        (by
          refine mul_nonneg hEpos.le (mul_nonneg (mul_nonneg hThetaNonneg hLambdaNonneg) ?_)
          positivity)
    refine hstep1.trans (hstep2.trans ?_)
    have hfactor :
        (jBesovCaccioppoliEnvelope C₆ *
              (Real.rpow (Ch02.ThetaRatio (originCube d m) s s
                  (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha))
                (s / (1 - 2 * s)) *
                Ch02.LambdaS (originCube d m) s
                  (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) *
                ((3 : ℝ) ^ (-m)) ^ 2)) *
            (oscillationMultiscalePoincareConstant d *
              ∑ i : Fin d,
                cubeBesovCircNorm (originCube d m) 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
                  (fun x =>
                    (canonicalCubeMaximizerSolution a ha (originCube d m) p q).toH1.grad x i)) ^
              2 =
          jBesovCaccioppoliEnvelope C₆ * oscillationMultiscalePoincareConstant d ^ 2 *
            Ch02.LambdaS (originCube d m) s
              (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) *
            Real.rpow (Ch02.ThetaRatio (originCube d m) s s
                (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha))
              (s / (1 - 2 * s)) *
            (((3 : ℝ) ^ (-m)) ^ 2 *
              (∑ i : Fin d,
                cubeBesovCircNorm (originCube d m) 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
                  (fun x =>
                    (canonicalCubeMaximizerSolution a ha (originCube d m) p q).toH1.grad x i)) ^
                2) := by ring
    rw [hfactor]
    have hcoef :
        0 ≤ jBesovCaccioppoliEnvelope C₆ * oscillationMultiscalePoincareConstant d ^ 2 *
          Ch02.LambdaS (originCube d m) s
            (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) *
          Real.rpow (Ch02.ThetaRatio (originCube d m) s s
              (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha))
            (s / (1 - 2 * s)) := by
      have h := mul_nonneg (mul_nonneg hEpos.le (sq_nonneg
        (oscillationMultiscalePoincareConstant d))) hLambdaNonneg
      exact mul_nonneg h hThetaNonneg
    have hgrow :
        jBesovCaccioppoliEnvelope C₆ * oscillationMultiscalePoincareConstant d ^ 2 *
              Ch02.LambdaS (originCube d m) s
                (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) *
              Real.rpow (Ch02.ThetaRatio (originCube d m) s s
                  (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha))
                (s / (1 - 2 * s)) *
            ((3 / 2 * Real.sqrt 2 * (d : ℝ) * Real.sqrt (d : ℝ)) ^ 2 *
              (centredMultiscaleAverageSum a ha m p q +
                Real.sqrt (vecNormSq (coarseScaleSeparation a ha (originCube d m) p q))) ^ 2) ≤
          jBesovCaccioppoliEnvelope C₆ * (oscillationMultiscalePoincareConstant d ^ 2 + 1) *
              (3 / 2 * Real.sqrt 2 * (d : ℝ) * Real.sqrt (d : ℝ)) ^ 2 *
              Ch02.LambdaS (originCube d m) s
                (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) *
              Real.rpow (Ch02.ThetaRatio (originCube d m) s s
                  (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha))
                (s / (1 - 2 * s)) *
              (centredMultiscaleAverageSum a ha m p q +
                Real.sqrt (vecNormSq (coarseScaleSeparation a ha (originCube d m) p q))) ^ 2 := by
      have hbase : 0 ≤ jBesovCaccioppoliEnvelope C₆ *
          Ch02.LambdaS (originCube d m) s
            (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) *
          Real.rpow (Ch02.ThetaRatio (originCube d m) s s
              (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha))
            (s / (1 - 2 * s)) :=
        mul_nonneg (mul_nonneg hEpos.le hLambdaNonneg) hThetaNonneg
      rw [show
          jBesovCaccioppoliEnvelope C₆ * (oscillationMultiscalePoincareConstant d ^ 2 + 1) *
              (3 / 2 * Real.sqrt 2 * (d : ℝ) * Real.sqrt (d : ℝ)) ^ 2 *
              Ch02.LambdaS (originCube d m) s
                (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) *
              Real.rpow (Ch02.ThetaRatio (originCube d m) s s
                  (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha))
                (s / (1 - 2 * s)) *
              (centredMultiscaleAverageSum a ha m p q +
                Real.sqrt (vecNormSq (coarseScaleSeparation a ha (originCube d m) p q))) ^ 2 =
            (jBesovCaccioppoliEnvelope C₆ * oscillationMultiscalePoincareConstant d ^ 2 *
                  Ch02.LambdaS (originCube d m) s
                    (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) *
                  Real.rpow (Ch02.ThetaRatio (originCube d m) s s
                      (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha))
                    (s / (1 - 2 * s)) +
                jBesovCaccioppoliEnvelope C₆ *
                  Ch02.LambdaS (originCube d m) s
                    (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) *
                  Real.rpow (Ch02.ThetaRatio (originCube d m) s s
                      (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha))
                    (s / (1 - 2 * s))) *
              ((3 / 2 * Real.sqrt 2 * (d : ℝ) * Real.sqrt (d : ℝ)) ^ 2 *
                (centredMultiscaleAverageSum a ha m p q +
                  Real.sqrt (vecNormSq (coarseScaleSeparation a ha (originCube d m) p q))) ^ 2)
          by ring]
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    exact le_trans (mul_le_mul_of_nonneg_left hsq hcoef) hgrow
  rw [show (originCube d (m - 1)) = CubeCalderonZygmund.centralChild (originCube d m) from
    (centralChild_originCube m).symm]
  have hdig :=
    responseJ_centralChild_le_centralChildCaccioppoliEnergy_add_defectSum a ha
      (originCube d m) p q
  linarith [hdig, henergy]

/-- **The composite on the Chapter 4 restriction response observable.**  This is
the same estimate written on the carrier that the Section 3 response observable
`J(\cu_m, p, q\;\a)` uses, so that a Section 3 consumer meets it after
instantiating the loads. -/
theorem exists_restrictionResponseJ_centralChild_le_jBoundByBesovDisplay (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : RegCoeffField d) (ha : Ch04.AELocallyUniformlyEllipticField a) (m : ℤ)
        (p q : Vec d) {s : ℝ}, 0 < s → s ≤ 1 / 4 →
        Ch04.restrictionResponseJObservableCubeSet (originCube d (m - 1)) p q a ≤
          C *
                Ch02.LambdaS (originCube d m) s
                  (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) *
                Real.rpow (Ch02.ThetaRatio (originCube d m) s s
                    (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha))
                  (s / (1 - 2 * s)) *
                (centredMultiscaleAverageSum a ha m p q +
                    Real.sqrt (vecNormSq (coarseScaleSeparation a ha (originCube d m) p q))) ^ 2 +
            ∑ R ∈ descendantsAtDepth (originCube d m) 1,
              2 * (Ch04.restrictionResponseJObservableCubeSet R p q a -
                    Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q a) := by
  obtain ⟨C, hC, hbound⟩ := exists_responseJ_centralChild_le_jBoundByBesovDisplay d
  refine ⟨C, hC, ?_⟩
  intro a ha m p q s hs hs_quarter
  simpa only
    [JUpperBoundWeakNorms.responseJOnDependentFamily_eq_restrictionResponseJObservableCubeSet
      a ha] using hbound a ha m p q hs hs_quarter

end

end Algsuperdiff.Section3.Provider.Besov
