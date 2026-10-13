/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.CombineExpectation

/-!
# UnionSubadditivity

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Response subadditivity at the union display

The first inequality of the cutoff-union display of ABK26 (proof of
`p.homogenization.step`) is the deterministic statement

```
J(square_m, sigmabar_L^{-1/2} e, sigmabar_L^{1/2} e; a_L)
  <=  avsum_{z in 3^n Z^d cap square_m}
        J(z + square_n, sigmabar_L^{-1/2} e, sigmabar_L^{1/2} e; a_L) ,
```

read at the genuine cutoff sample law and therefore almost surely, since both
sides are the measurable representatives of the two literal quantities.

This module carries that step and the recentred corollary,

```
J(square_m, ...)  <=  | avsum_z ( J(z + square_n, ...) - E[J(square_n, ...)] ) |
                        + E[J(square_n, ...)] ,
```

which is the shape the two-lane grid concentration endpoint
`isTwoTermBigOWith_gridAverage_siteCenteredResponseJ` consumes: the first term
is exactly the averaged *recentred* site response whose two-term weak-Orlicz
relation is proved, and the second is the single number produced by the mean
lane.

## The three ingredients, all proved

1. *Deterministic depth-`k` subadditivity.*  The nonnegativity of the Chapter 5
   defect `WeakNormsMaximizer.responseDefectAverageAtScale m n p q a`, proved
   upstream as
   `responseDefectAverageAtScale_nonneg_of_aelocallyUniformlyEllipticField`,
   *is* the inequality `J(square_m) <= descendantsAverage` at relative depth
   `(m - n).toNat` once the definition is unfolded.

2. *The enumeration of the descendant family by the site family.*  The
   depth-`k` descendants of `square_m` are exactly the site cubes
   `siteCube n u` at `n = m - k` with `u` ranging over `cubeFinset k`, which is
   the manuscript's grid `3^n Z^d cap square_m` in the cube-side units of
   `Provider/Percolation/Coloring.lean`.  This is proved below from the index
   bound of the triadic child recursion plus the two cardinalities
   `3^(d k)`.

3. *The two literal identifications.*  `Observable.cutoffResponseJ M m L e` is
   the literal parent response off one null set
   (`Observable.ae_forall_cutoffResponseJ_eq_literal`), and `siteResponseJ M L n u e`
   is the literal response of `siteCube n u` off one null set per site
   (`ae_siteResponseJ_eq_responseJ`).

## Null-set accounting

The main almost-sure statement spends **two** events: the parent literal event,
and the single event obtained from the finitely many site literal events by
`Filter.eventually_all_finset` over `cubeFinset (m - n).toNat` (a finite set of
cardinality `3^(d (m-n))`).  Both are consumed in one `filter_upwards`.  The
recentred corollary adds no further event: the identity
`gridAverage_siteCenteredResponseJ_eq_sub_integral` is pointwise in `omega`.

## References

* ABK26, proof of `p.homogenization.step`.
* ABK26, (2.4), definition of `J(U, p, q; a)`.
* ABK26, `e.subaddJ.nosymm`, the deterministic response subadditivity.
-/

namespace Algsuperdiff.Section3.Provider.Homogenization

open Filter MeasureTheory
open _root_.HCPolySupport _root_.HCPolySupport.Book
open _root_.HCPolySupport.Book.Ch05.Section53
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Percolation

noncomputable section

variable {d : ℕ}

/-! ## The grid enumeration of the descendant family -/

/-- The triadic half-width recursion `r_{k+1} = 3 r_k + 1` behind the child
index recursion of `childCubes`. -/
private theorem cubeRadius_succ (k : ℕ) :
    Percolation.cubeRadius (k + 1) = 3 * Percolation.cubeRadius k + 1 := by
  have h1 := Percolation.two_mul_cubeRadius_add_one k
  have h2 := Percolation.two_mul_cubeRadius_add_one (k + 1)
  have h3 : (3 : ℕ) ^ (k + 1) = 3 * 3 ^ k := by ring
  omega

/-- Every depth-`k` descendant of `square_m` has all its indices bounded by the
triadic half-width `cubeRadius k`.  This is the containment half of the grid
enumeration; the child index recursion `3 u + digit - 1` with `digit` in
`{0, 1, 2}` is exactly the recursion `r_{k+1} = 3 r_k + 1`. -/
private theorem abs_index_le_cubeRadius_of_mem_descendantsAtDepth {m : ℤ} :
    ∀ {k : ℕ} {R : TriadicCube d},
      R ∈ descendantsAtDepth (originCube d m) k →
        ∀ i : Fin d, |R.index i| ≤ (Percolation.cubeRadius k : ℤ)
  | 0, R, hR, i => by
      rw [descendantsAtDepth_zero, Finset.mem_singleton] at hR
      subst hR
      simp [originCube, Percolation.cubeRadius]
  | k + 1, R, hR, i => by
      rcases mem_descendantsAtDepth_succ_iff.mp hR with ⟨S, hS, hRS⟩
      rcases mem_childCubes_iff.mp hRS with ⟨digits, rfl⟩
      have hS' := abs_index_le_cubeRadius_of_mem_descendantsAtDepth hS i
      have hdlt : ((digits i : ℕ) : ℤ) < 3 := by exact_mod_cast (digits i).isLt
      have hd0 : (0 : ℤ) ≤ ((digits i : ℕ) : ℤ) := Int.natCast_nonneg _
      have hr : (Percolation.cubeRadius (k + 1) : ℤ) =
          3 * (Percolation.cubeRadius k : ℤ) + 1 := by
        exact_mod_cast congrArg (fun t : ℕ => (t : ℤ)) (cubeRadius_succ k)
      rw [abs_le] at hS' ⊢
      show -(Percolation.cubeRadius (k + 1) : ℤ) ≤
            3 * S.index i + ((digits i : ℕ) : ℤ) - 1 ∧
          3 * S.index i + ((digits i : ℕ) : ℤ) - 1 ≤
            (Percolation.cubeRadius (k + 1) : ℤ)
      omega

/-- **The grid enumeration.**  For integer scales `n <= m` the depth-`(m - n)`
descendants of `square_m` are exactly the site cubes `siteCube n u` with `u`
ranging over `cubeFinset (m - n).toNat`; that is, ABK26's grid
`3^n Z^d cap square_m` in the cube-side units of `Provider/Percolation`.  The
containment is the index bound, and the reverse inclusion is forced by the two
equal cardinalities `3^(d (m - n))`. -/
theorem descendantsAtDepth_originCube_eq_image_siteCube (m n : ℤ) (hnm : n ≤ m) :
    descendantsAtDepth (originCube d m) (m - n).toNat =
      (cubeFinset (d := d) (m - n).toNat).image (siteCube n) := by
  classical
  set k : ℕ := (m - n).toNat with hk
  have hkcast : ((k : ℤ)) = m - n := Int.toNat_of_nonneg (by omega)
  have hscale : ∀ R ∈ descendantsAtDepth (originCube d m) k, R.scale = n := by
    intro R hR
    have h := scale_eq_sub_of_mem_descendantsAtDepth hR
    have hOrigin : (originCube d m).scale = m := rfl
    rw [hOrigin, hkcast] at h
    omega
  have hsub : descendantsAtDepth (originCube d m) k ⊆
      (cubeFinset (d := d) k).image (siteCube n) := by
    intro R hR
    refine Finset.mem_image.mpr ⟨R.index, ?_, ?_⟩
    · rw [cubeFinset, Fintype.mem_piFinset]
      intro i
      have hi := abs_index_le_cubeRadius_of_mem_descendantsAtDepth hR i
      rw [abs_le] at hi
      exact Finset.mem_Icc.mpr hi
    · rw [← hscale R hR]
      rfl
  refine Finset.eq_of_subset_of_card_le hsub ?_
  have hcardImage : ((cubeFinset (d := d) k).image (siteCube n)).card ≤
      (cubeFinset (d := d) k).card := Finset.card_image_le
  have hcardCube : (cubeFinset (d := d) k).card = 3 ^ (d * k) := card_cubeFinset k
  have hcardDesc : (descendantsAtDepth (originCube d m) k).card = 3 ^ (d * k) := by
    rw [descendantsAtDepth_card, pow_mul]
  omega

/-- **The descendant average is the grid average.**  Any real functional of
cubes averaged over the depth-`(m - n)` descendants of `square_m` is its own
average over the manuscript grid, indexed by `cubeFinset (m - n).toNat`. -/
theorem descendantsAverage_originCube_eq_gridAverage (m n : ℤ) (hnm : n ≤ m)
    (F : TriadicCube d → ℝ) :
    descendantsAverage (originCube d m) (m - n).toNat F =
      ((cubeFinset (d := d) (m - n).toNat).card : ℝ)⁻¹ *
        ∑ u ∈ cubeFinset (d := d) (m - n).toNat, F (siteCube n u) := by
  classical
  have hinj : Function.Injective (siteCube (d := d) n) := fun u v huv =>
    congrArg TriadicCube.index huv
  rw [descendantsAverage, descendantsAtDepth_originCube_eq_image_siteCube m n hnm,
    Finset.card_image_of_injective _ hinj,
    Finset.sum_image fun u _ v _ huv => hinj huv]

/-! ## The deterministic subadditivity step -/

/-- **Response subadditivity at the union display, deterministically** (ABK26,
proof of `p.homogenization.step`).  For every genuine cutoff realization and
every pair of loads, the literal response of the parent cube `square_m` is at
most the grid average, over `3^n Z^d cap square_m`, of the literal responses of
the site cubes.

This is `WeakNormsMaximizer.responseDefectAverageAtScale_nonneg_of_aelocallyUniformlyEllipticField`
read at the pointwise ellipticity of the cutoff and reindexed by the grid
enumeration; no null set is spent. -/
theorem restrictionResponseJObservableCubeSet_originCube_le_gridAverage
    (M : ABKModel d) (m n L : ℤ) (hnm : n ≤ m) (p q : Vec d)
    (omega : CutoffSample d) :
    Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q
        (coefficientCutoff M.nu L omega) ≤
      ((cubeFinset (d := d) (m - n).toNat).card : ℝ)⁻¹ *
        ∑ u ∈ cubeFinset (d := d) (m - n).toNat,
          Ch04.restrictionResponseJObservableCubeSet (siteCube n u) p q
            (coefficientCutoff M.nu L omega) := by
  let : NeZero d :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
  have hnn := WeakNormsMaximizer.responseDefectAverageAtScale_nonneg_of_aelocallyUniformlyEllipticField
    (coefficientCutoff M.nu L omega)
    (coefficientCutoff_aeLocallyUniformlyEllipticField M L omega) m n p q
  rw [WeakNormsMaximizer.responseDefectAverageAtScale] at hnn
  have hgrid : descendantsAverage (originCube d m) (m - n).toNat
        (fun R => Ch04.restrictionResponseJObservableCubeSet R p q
          (coefficientCutoff M.nu L omega)) =
      ((cubeFinset (d := d) (m - n).toNat).card : ℝ)⁻¹ *
        ∑ u ∈ cubeFinset (d := d) (m - n).toNat,
          Ch04.restrictionResponseJObservableCubeSet (siteCube n u) p q
            (coefficientCutoff M.nu L omega) :=
    descendantsAverage_originCube_eq_gridAverage m n hnm _
  rw [← hgrid]
  linarith

/-! ## The almost-sure statements at the genuine cutoff sample law -/

/-- **Response subadditivity at the union display** (ABK26, proof of
`p.homogenization.step`).  Almost surely under the genuine cutoff sample law,
the measurable parent response at cube scale `m` is at most the grid average of
the proved site responses at cube scale `n`, over the manuscript grid `3^n Z^d
cap square_m` written at relative depth `(m - n).toNat`.

Two events are spent: the parent literal identification
`Observable.ae_forall_cutoffResponseJ_eq_literal`, and the finite intersection
over `cubeFinset (m - n).toNat` of the per-site literal identifications
`ae_siteResponseJ_eq_responseJ`.  This is a Provider result and carries no
source-node status by itself. -/
theorem ae_cutoffResponseJ_le_gridAverage_siteResponseJ (M : ABKModel d)
    (m n L : ℤ) (hnm : n ≤ m) (e : Vec d) :
    ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      Observable.cutoffResponseJ M m L e omega ≤
        ((cubeFinset (d := d) (m - n).toNat).card : ℝ)⁻¹ *
          ∑ u ∈ cubeFinset (d := d) (m - n).toNat,
            siteResponseJ M L n u e omega := by
  have hsites : ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      ∀ u ∈ cubeFinset (d := d) (m - n).toNat,
        siteResponseJ M L n u e omega =
          Ch04.restrictionResponseJObservableCubeSet (siteCube n u)
            (Observable.inverseSqrtLoad (Annealed.sigmaBar M L) e)
            (Observable.sqrtLoad (Annealed.sigmaBar M L) e)
            (coefficientCutoff M.nu L omega) := by
    rw [eventually_all_finset]
    intro u _
    filter_upwards [ae_siteResponseJ_eq_responseJ M L n u e] with omega homega
    exact homega
  filter_upwards [Observable.ae_forall_cutoffResponseJ_eq_literal M m L, hsites]
    with omega hlit hsite
  rw [hlit e, Finset.sum_congr rfl hsite]
  exact restrictionResponseJObservableCubeSet_originCube_le_gridAverage M m n L hnm
    _ _ omega

/-- **The recentred union display** (ABK26, proof of `p.homogenization.step`).
Almost surely under the genuine cutoff sample law, the measurable parent
response at cube scale `m` is at most the absolute value of the grid average of
the *recentred* site responses plus the single number `E[J(square_n,
sigmabar_L^{-1/2} e, sigmabar_L^{1/2} e; a_L)]`.

The first summand is exactly the random variable of the proved two-lane grid
concentration endpoint `isTwoTermBigOWith_gridAverage_siteCenteredResponseJ`,
and the second is the quantity iterated by the mean lane.  The split is the
proved pointwise identity `gridAverage_siteCenteredResponseJ_eq_sub_integral`,
whose mean identification is
`integral_siteResponseJ_eq_integral_cutoffResponseJ`; no further null set is
spent beyond the two of the previous theorem, and no integrability binder is
needed for the inequality.  Disclosure: absent such a binder the Bochner
integral in the statement is the convention `0` whenever
`Observable.cutoffResponseJ M n L e` is not integrable, and the bound then
degenerates to the (still true) bound by the unrecentred grid average; the
integrability that makes this term the genuine expectation `E[J(square_n..)]`
is produced by the proved `integrable_cutoffResponseJ_of_precedingError` and is
bound only in `integral_gridAverage_siteCenteredResponseJ_eq_zero` below. -/
theorem ae_cutoffResponseJ_le_abs_gridAverage_siteCenteredResponseJ_add_integral
    (M : ABKModel d) (m n L : ℤ) (hnm : n ≤ m) (e : Vec d) :
    ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      Observable.cutoffResponseJ M m L e omega ≤
        |((cubeFinset (d := d) (m - n).toNat).card : ℝ)⁻¹ *
            ∑ u ∈ cubeFinset (d := d) (m - n).toNat,
              siteCenteredResponseJ M L n u e omega| +
          ∫ omega', Observable.cutoffResponseJ M n L e omega'
            ∂(cutoffSampleLaw M).toMeasure := by
  filter_upwards [ae_cutoffResponseJ_le_gridAverage_siteResponseJ M m n L hnm e]
    with omega hle
  have hsplit :=
    gridAverage_siteCenteredResponseJ_eq_sub_integral M L n (m - n).toNat e omega
  have habs := le_abs_self (((cubeFinset (d := d) (m - n).toNat).card : ℝ)⁻¹ *
    ∑ u ∈ cubeFinset (d := d) (m - n).toNat, siteCenteredResponseJ M L n u e omega)
  linarith

end

end Algsuperdiff.Section3.Provider.Homogenization
