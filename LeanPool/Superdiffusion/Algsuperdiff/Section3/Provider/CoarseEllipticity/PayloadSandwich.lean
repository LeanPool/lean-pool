/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.BlockPayload
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.GridDomination

/-!
# PayloadSandwich

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The payload sandwich: joining the on-grid domination to the block payload

Two halves of the coarse-ellipticity payload are proved separately and left
uncomposed:

* `Provider/CoarseEllipticity/GridDomination.lean` discharges `hgrid` --- the
  domination of each leg's observable by the weighted series of **Chapter 4
  grid maxima** `Ch04.maxDescendant{SigmaStarInv,B}MatrixNormCoeffFieldAtScale`
  read at the coefficient cutoff --- against an arbitrary majorizing family `G`;
* `Provider/CoarseEllipticity/BlockPayload.lean` turns a per-cube block estimate
  into each leg's payload conjunction, but through the **`gridSupAbs` carrier**
  `blockGridSup`, i.e. through a supremum of a family indexed by triadic cubes.

The two carriers differ: the identification
`maxDescendantBMatrixNormAtScale_eq_gridSupAbs` of `GridWeights.lean` is stated
at the deterministic sample space `Ch02.TriadicCoeffFamily d`, and composing the
halves at a *random* coefficient family is an additional step.  This module
proves that step, adds the missing `sigma_*^{-1}` twin, adds the **top-scale
step** that prices the gap-`0` fold's summand against the scale-`m-1` grid, and
supplies the folded-amplitude arithmetic in which the two halves meet.

## What is joined, in one line

```
Ch04.maxDescendant...CoeffFieldAtScale (cu_m) (m-1-k) a  =  blockGridSup d m k F a
Ch04.maxDescendant...CoeffFieldAtScale (cu_m)  m     a  <=  blockGridSup d m 0 F a
```

with `F` the per-cube Chapter 4 coefficient-field norm defined here.  The first
is an equality (both sides are the same finite supremum, on both branches of the
`AELocallyUniformlyEllipticField` `dite`); the second is the top-scale step,
CoarseGraining's `Ch02.coarse...MatrixNorm_le_maxDescendant...AtScale` at the
singleton `descendantsAtScale Q Q.scale = {Q}`, i.e. the one-cube half of
`e.ellipticities.monotone.ordered` / `e.bound.one.cube.by.lambdas`.  Its
constant is `1`.

## What composes outright, and what remains an explicit obligation

* **Upper leg**: the identifications below discharge `hgrid` outright, at the
  leg's own cutoff index, with NO binder on the grid family.  What is left over
  is the per-cube block estimate `hblock` / `hblockO1` / `hblockOexp`
  (`p.bfA.multiscalebound`, i.e. `e.bL.multiscale`) together with the source's
  own series data --- the shape in which
  `threeTermSplit_cutoffUpperEllipticity_of_finiteQLtTwoPresplit` consumes
  them.
* **Lower leg**: `hgrid` can only be discharged against an `L`-free family
  built from one named binder `hLunif`, the per-cube `L`-uniform majorant.
  This is not a corollary of the identification: the Chapter 4 grid maxima read
  `Cutoff.coefficientCutoff M.nu L omega`, and no `L`-free majorant is
  constructible here.  `hLunif` is exactly the `sup_{L >= m-1}` printed on the
  left of `e.slstar.multiscale`: together with `hblock` at the same `Xc`, the
  pair is that display.  It stays an explicit proof obligation of the lower
  leg's producers
  (`twoTermFamilySplit_cutoffLowerEllipticityInv_of_finiteQPresplit` and its
  `q < 2` twin), not evidence that the source display has been proved.

## What is not proved here and remains an interface obligation

1. `hblock` / `hblockO` / `hblockO1` / `hblockOexp` --- the per-cube block
   estimate `p.bfA.multiscalebound` (`e.slstar.multiscale`;
   `e.bL.multiscale`).
2. `hLunif` --- the lower leg's `L`-uniformity, as above.
3. The small-`m` branch (`p.base.case` / `l.mathcal.E.to.Lambdas`) is
   untouched here; it is a separate producer's.
4. The `q > 2` re-plumb: everything at the observable layer here is at the
   exponent `q = 2` (`hqval`).

## References

* ABK26, `p.cg.ellipticity.bounds` from `p.bfA.multiscalebound` (the
  composite: lower upper; the summed poles; the absorption gate).
* ABK26, `e.slstar.multiscale` and `e.bL.multiscale`.
* ABK26, `e.ellipticities.monotone.ordered` and `e.bound.one.cube.by.lambdas`
  --- the one-cube/grid ordering implemented by the top-scale step.
* ABK26, `l.maximums.Gamma.s` (`e.maxy.bound`).
* `Provider/CoarseEllipticity/GridWeights.lean` (the local seam handled
  here), `.../BlockPayload.lean` and `.../GridDomination.lean` (the two
  halves), `.../GridDominationAllQ.lean` (the `q >= 2` extension),
  `Provider/ErrorComparison/ExponentMonotonicity.lean` (the display
  whose one-cube half the top-scale step uses).
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open MeasureTheory
open HCPolySupport HCPolySupport.IndependentSums
open Algsuperdiff.Section3

noncomputable section

variable {d : ℕ}

/-! ## 1. The per-cube Chapter 4 coefficient-field norms -/

/-- `|sigma_*^{-1}(R; a)|` at the Chapter 4 ambient coefficient field:
CoarseGraining's one-cube norm on the a.e.-locally elliptic support, `0` off it
--- the per-cube datum whose grid maximum is
`Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale`. -/
noncomputable def coarseSigmaStarInvNormCoeffField (R : TriadicCube d)
    (a : RegCoeffField d) : ℝ := by
  classical
  exact
    if h : Book.Ch04.AELocallyUniformlyEllipticField a then
      Book.Ch02.coarseSigmaStarInvMatrixNorm R
        (Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a h)
    else 0

/-- `|b(R; a)|` at the Chapter 4 ambient coefficient field, the upper leg's
per-cube datum. -/
noncomputable def coarseBNormCoeffField (R : TriadicCube d)
    (a : RegCoeffField d) : ℝ := by
  classical
  exact
    if h : Book.Ch04.AELocallyUniformlyEllipticField a then
      Book.Ch02.coarseBMatrixNorm R
        (Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a h)
    else 0

/-- The lower per-cube datum is a matrix norm, hence nonnegative on both
branches. -/
theorem coarseSigmaStarInvNormCoeffField_nonneg (R : TriadicCube d)
    (a : RegCoeffField d) : 0 ≤ coarseSigmaStarInvNormCoeffField R a := by
  classical
  rw [coarseSigmaStarInvNormCoeffField]
  by_cases h : Book.Ch04.AELocallyUniformlyEllipticField a
  · rw [dite_eq_left h]
    exact Book.Ch02.coarseSigmaStarInvMatrixNorm_nonneg _ _
  · rw [dite_eq_right h]

/-- The upper per-cube datum is a matrix norm, hence nonnegative on both
branches. -/
theorem coarseBNormCoeffField_nonneg (R : TriadicCube d) (a : RegCoeffField d) :
    0 ≤ coarseBNormCoeffField R a := by
  classical
  rw [coarseBNormCoeffField]
  by_cases h : Book.Ch04.AELocallyUniformlyEllipticField a
  · rw [dite_eq_left h]
    exact Book.Ch02.coarseBMatrixNorm_nonneg _ _
  · rw [dite_eq_right h]

/-! ## 2. `blockGridSup` A -/

/-- The grid maximum only reads the sample point through the family, so
precomposing every cube's observable with one map is the same as evaluating the
grid maximum at the image point.  This is what carries the identification below
from the coefficient field to the cutoff sample space. -/
theorem blockGridSup_comp {Omega Omega' : Type*} (d : ℕ) (m : ℤ) (k : ℕ)
    (X : TriadicCube d → Omega' → ℝ) (g : Omega → Omega') (omega : Omega) :
    blockGridSup d m k (fun R o => X R (g o)) omega
      = blockGridSup d m k X (g omega) := rfl

/-- A nonnegative constant passes through the grid maximum: the normalizer
`sigmabar_{m-1}^{(-1)}` of the legs can sit inside the per-cube family or
outside the maximum, indifferently. -/
theorem blockGridSup_const_mul {Omega : Type*} (d : ℕ) (m : ℤ) (k : ℕ)
    {c : ℝ} (hc : 0 ≤ c) (X : TriadicCube d → Omega → ℝ) (omega : Omega) :
    blockGridSup d m k (fun R o => c * X R o) omega
      = c * blockGridSup d m k X omega := by
  have hcongr : (fun R : TriadicCube d => |c * X R omega|)
      = fun R : TriadicCube d => c * |X R omega| := by
    funext R
    rw [abs_mul, abs_of_nonneg hc]
  have hsup := Finset.apply_sup'_eq_sup'_comp
    (descendantsAtScale_originCube_nonempty d m k)
    (f := fun R : TriadicCube d => |X R omega|) (g := fun t : ℝ => c * t)
    (fun x y => mul_max_of_nonneg x y hc)
  rw [blockGridSup, blockGridSup, gridSupAbs, gridSupAbs, hcongr]
  exact hsup.symm

/-! ## 3. The Chapter 2 identification, `sigma_*^{-1}` twin -/

/-- CoarseGraining's `sSup`-over-a-finite-image and Mathlib's `Finset.sup'` agree
on a nonempty finite set. -/
private theorem finsetSupReal_eq_sup'_aux {alpha : Type*} (sfin : Finset alpha)
    (hs : sfin.Nonempty) (f : alpha → ℝ) :
    Book.Ch02.finsetSupReal sfin f = sfin.sup' hs f :=
  Book.Ch04.RestrictionLawCarrier.finsetSupReal_eq_sup' sfin hs f

/-- **The on-grid carrier identification, `sigma_*^{-1}` twin.**  The missing
companion of `GridWeights.maxDescendantBMatrixNormAtScale_eq_gridSupAbs`:
CoarseGraining's per-scale grid maximum, the quantity `Ch02.lambdaSqFinite` is
defined from, is exactly `gridSupAbs` at the one-cube norms `|sigma_*^{-1}(R;
a)|`. -/
theorem maxDescendantSigmaStarInvMatrixNormAtScale_eq_gridSupAbs (m : ℤ) (k : ℕ)
    (a : Book.Ch02.TriadicCoeffFamily d) :
    Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale (originCube d m)
        (m - 1 - (k : ℤ)) a
      = gridSupAbs (Omega := Book.Ch02.TriadicCoeffFamily d)
          (descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)))
          (descendantsAtScale_originCube_nonempty d m k)
          (fun R b => Book.Ch02.coarseSigmaStarInvMatrixNorm R b) a := by
  have hfun : (fun R : TriadicCube d =>
      |Book.Ch02.coarseSigmaStarInvMatrixNorm R a|)
      = fun R : TriadicCube d => Book.Ch02.coarseSigmaStarInvMatrixNorm R a := by
    funext R
    exact abs_of_nonneg (Book.Ch02.coarseSigmaStarInvMatrixNorm_nonneg R a)
  rw [Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale, gridSupAbs, hfun,
    finsetSupReal_eq_sup'_aux _ (descendantsAtScale_originCube_nonempty d m k)]

/-! ## 4. The Chapter 4 identification: the -/

/-- **The, lower half.**  The Chapter 4 ambient grid maximum at scale `m-1-k` IS
this repository's `blockGridSup` at the per-cube Chapter 4 norms --- on the
a.e.-locally elliptic branch by the Chapter 2 identification, off it because
both sides are the supremum of the zero family.  This is the equality
`GridWeights.lean` flags as "an additional, unlanded step". -/
theorem maxDescendantSigmaStarInvCoeffField_eq_blockGridSup (m : ℤ)
    (k : ℕ) (a : RegCoeffField d) :
    Book.Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
        (originCube d m) (m - 1 - (k : ℤ)) a
      = blockGridSup (Omega := RegCoeffField d) d m k
          coarseSigmaStarInvNormCoeffField a := by
  classical
  by_cases h : Book.Ch04.AELocallyUniformlyEllipticField a
  · rw [Book.Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale, dite_eq_left h,
      maxDescendantSigmaStarInvMatrixNormAtScale_eq_gridSupAbs, blockGridSup,
      gridSupAbs, gridSupAbs]
    refine Finset.sup'_congr _ rfl fun R _ => ?_
    rw [coarseSigmaStarInvNormCoeffField, dite_eq_left h]
  · rw [Book.Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale, dite_eq_right h,
      blockGridSup, gridSupAbs]
    have hz : (fun R : TriadicCube d => |coarseSigmaStarInvNormCoeffField R a|)
        = fun _ : TriadicCube d => (0 : ℝ) := by
      funext R
      rw [coarseSigmaStarInvNormCoeffField, dite_eq_right h, abs_zero]
    rw [hz, Finset.sup'_const]

/-- **The, upper half**: the `b` twin of
`maxDescendantSigmaStarInvCoeffField_eq_blockGridSup`. -/
theorem maxDescendantBCoeffField_eq_blockGridSup (m : ℤ) (k : ℕ)
    (a : RegCoeffField d) :
    Book.Ch04.maxDescendantBMatrixNormCoeffFieldAtScale
        (originCube d m) (m - 1 - (k : ℤ)) a
      = blockGridSup (Omega := RegCoeffField d) d m k coarseBNormCoeffField a := by
  classical
  by_cases h : Book.Ch04.AELocallyUniformlyEllipticField a
  · rw [Book.Ch04.maxDescendantBMatrixNormCoeffFieldAtScale, dite_eq_left h,
      maxDescendantBMatrixNormAtScale_eq_gridSupAbs, blockGridSup,
      gridSupAbs, gridSupAbs]
    refine Finset.sup'_congr _ rfl fun R _ => ?_
    rw [coarseBNormCoeffField, dite_eq_left h]
  · rw [Book.Ch04.maxDescendantBMatrixNormCoeffFieldAtScale, dite_eq_right h,
      blockGridSup, gridSupAbs]
    have hz : (fun R : TriadicCube d => |coarseBNormCoeffField R a|)
        = fun _ : TriadicCube d => (0 : ℝ) := by
      funext R
      rw [coarseBNormCoeffField, dite_eq_right h, abs_zero]
    rw [hz, Finset.sup'_const]

/-! ## 5. The top-scale step -/

/-- At its own scale a cube's only descendant is itself, so the grid maximum there
is the one-cube norm. -/
theorem maxDescendantSigmaStarInvMatrixNormAtScale_top_eq
    (Q : TriadicCube d) (a : Book.Ch02.TriadicCoeffFamily d) :
    Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q Q.scale a
      = Book.Ch02.coarseSigmaStarInvMatrixNorm Q a := by
  rw [Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale, descendantsAtScale_self,
    finsetSupReal_eq_sup'_aux _ (Finset.singleton_nonempty Q), Finset.sup'_singleton]

/-- The `b` twin of `maxDescendantSigmaStarInvMatrixNormAtScale_top_eq`. -/
theorem maxDescendantBMatrixNormAtScale_top_eq
    (Q : TriadicCube d) (a : Book.Ch02.TriadicCoeffFamily d) :
    Book.Ch02.maxDescendantBMatrixNormAtScale Q Q.scale a
      = Book.Ch02.coarseBMatrixNorm Q a := by
  rw [Book.Ch02.maxDescendantBMatrixNormAtScale, descendantsAtScale_self,
    finsetSupReal_eq_sup'_aux _ (Finset.singleton_nonempty Q), Finset.sup'_singleton]

/-- **The top-scale step** (Chapter 2, lower).  The depth-`0` one-cube quantity is
dominated by the grid maximum at any deeper scale, with constant `1`.  This is
the one-cube half of `e.ellipticities.monotone.ordered` /
`e.bound.one.cube.by.lambdas` (ABK26), already available in CoarseGraining,
and it is what lets the gap-`0` fold be priced against the scale-`m-1` grid
rather than against a separate object. -/
theorem maxDescendantSigmaStarInvMatrixNormAtScale_top_le [NeZero d]
    (Q : TriadicCube d) {l : ℤ} (hl : l ≤ Q.scale)
    (a : Book.Ch02.TriadicCoeffFamily d) :
    Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q Q.scale a
      ≤ Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q l a := by
  rw [maxDescendantSigmaStarInvMatrixNormAtScale_top_eq]
  exact Book.Ch02.coarseSigmaStarInvMatrixNorm_le_maxDescendantSigmaStarInvMatrixNormAtScale
    Q hl a

/-- **The top-scale step** (Chapter 2, upper). -/
theorem maxDescendantBMatrixNormAtScale_top_le [NeZero d]
    (Q : TriadicCube d) {l : ℤ} (hl : l ≤ Q.scale)
    (a : Book.Ch02.TriadicCoeffFamily d) :
    Book.Ch02.maxDescendantBMatrixNormAtScale Q Q.scale a
      ≤ Book.Ch02.maxDescendantBMatrixNormAtScale Q l a := by
  rw [maxDescendantBMatrixNormAtScale_top_eq]
  exact Book.Ch02.coarseBMatrixNorm_le_maxDescendantBMatrixNormAtScale Q hl a

/-- **The top-scale step at the Chapter 4 carrier, lower**: the depth-`0` grid
maximum is dominated by `blockGridSup` at gap `1`. -/
theorem maxDescendantSigmaStarInvCoeffField_top_le_blockGridSup [NeZero d] (m : ℤ)
    (a : RegCoeffField d) :
    Book.Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
        (originCube d m) m a
      ≤ blockGridSup (Omega := RegCoeffField d) d m 0
          coarseSigmaStarInvNormCoeffField a := by
  classical
  have hscale : (originCube d m).scale = m := rfl
  rw [← maxDescendantSigmaStarInvCoeffField_eq_blockGridSup m 0 a]
  by_cases h : Book.Ch04.AELocallyUniformlyEllipticField a
  · rw [Book.Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale, dite_eq_left h,
      Book.Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale, dite_eq_left h]
    have hl : m - 1 - ((0 : ℕ) : ℤ) ≤ (originCube d m).scale := by
      rw [hscale]; omega
    have htop : m = (originCube d m).scale := hscale.symm
    rw [htop]
    exact maxDescendantSigmaStarInvMatrixNormAtScale_top_le (originCube d m) hl _
  · rw [Book.Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale, dite_eq_right h,
      Book.Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale, dite_eq_right h]

/-- **The top-scale step at the Chapter 4 carrier, upper**. -/
theorem maxDescendantBCoeffField_top_le_blockGridSup [NeZero d] (m : ℤ)
    (a : RegCoeffField d) :
    Book.Ch04.maxDescendantBMatrixNormCoeffFieldAtScale (originCube d m) m a
      ≤ blockGridSup (Omega := RegCoeffField d) d m 0 coarseBNormCoeffField a := by
  classical
  have hscale : (originCube d m).scale = m := rfl
  rw [← maxDescendantBCoeffField_eq_blockGridSup m 0 a]
  by_cases h : Book.Ch04.AELocallyUniformlyEllipticField a
  · rw [Book.Ch04.maxDescendantBMatrixNormCoeffFieldAtScale, dite_eq_left h,
      Book.Ch04.maxDescendantBMatrixNormCoeffFieldAtScale, dite_eq_left h]
    have hl : m - 1 - ((0 : ℕ) : ℤ) ≤ (originCube d m).scale := by
      rw [hscale]; omega
    have htop : m = (originCube d m).scale := hscale.symm
    rw [htop]
    exact maxDescendantBMatrixNormAtScale_top_le (originCube d m) hl _
  · rw [Book.Ch04.maxDescendantBMatrixNormCoeffFieldAtScale, dite_eq_right h,
      Book.Ch04.maxDescendantBMatrixNormCoeffFieldAtScale, dite_eq_right h]

/-! ## 6. The sandwich at the observable carrier -/

/-- The lower leg's per-cube normalized grid datum at the cutoff index `L`. -/
noncomputable def cutoffSigmaStarInvBlockFamily (M : ABKModel d) (L : ℤ)
    (scaling : ℝ) (R : TriadicCube d) (omega : Cutoff.CutoffSample d) : ℝ :=
  scaling * coarseSigmaStarInvNormCoeffField R
    (Cutoff.coefficientCutoff M.nu L omega)

/-- The upper leg's per-cube normalized grid datum at the cutoff index `L`. -/
noncomputable def cutoffBBlockFamily (M : ABKModel d) (L : ℤ) (scaling : ℝ)
    (R : TriadicCube d) (omega : Cutoff.CutoffSample d) : ℝ :=
  scaling * coarseBNormCoeffField R (Cutoff.coefficientCutoff M.nu L omega)


/-- **The sandwich, upper leg, one scale.** -/
theorem scaledB_le_blockGridSup [NeZero d] (M : ABKModel d) (m : ℤ)
    (k : ℕ) {scaling T : ℝ} (hscaling : 0 ≤ scaling)
    {Y : TriadicCube d → Cutoff.CutoffSample d → ℝ} {L : ℤ}
    {omega : Cutoff.CutoffSample d}
    (hT : T ≤ Book.Ch04.maxDescendantBMatrixNormCoeffFieldAtScale
      (originCube d m) (m - 1 - (k : ℤ)) (Cutoff.coefficientCutoff M.nu L omega))
    (hdom : ∀ R ∈ descendantsAtScale (originCube d m) (m - 1 - (k : ℤ)),
      scaling * coarseBNormCoeffField R
          (Cutoff.coefficientCutoff M.nu L omega) ≤ Y R omega) :
    scaling * T ≤ blockGridSup d m k Y omega := by
  refine le_trans (mul_le_mul_of_nonneg_left hT hscaling) ?_
  rw [maxDescendantBCoeffField_eq_blockGridSup m k
      (Cutoff.coefficientCutoff M.nu L omega),
    ← blockGridSup_comp (Omega := Cutoff.CutoffSample d) d m k
      coarseBNormCoeffField (fun o => Cutoff.coefficientCutoff M.nu L o) omega,
    ← blockGridSup_const_mul d m k hscaling]
  refine blockGridSup_le fun R hR => ?_
  have h0 : 0 ≤ scaling * coarseBNormCoeffField R
      (Cutoff.coefficientCutoff M.nu L omega) :=
    mul_nonneg hscaling (coarseBNormCoeffField_nonneg _ _)
  have hY : |Y R omega| ≤ blockGridSup d m k Y omega := le_blockGridSup hR omega
  have hle := (hdom R hR).trans (le_abs_self (Y R omega))
  rw [abs_of_nonneg h0]
  linarith

/-- The top-scale step, stated between the two grid maxima the fold compares. -/
theorem maxDescendantSigmaStarInvCoeffField_top_le [NeZero d] (m : ℤ) (a : RegCoeffField d) :
    Book.Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
        (originCube d m) m a
      ≤ Book.Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
        (originCube d m) (m - 1 - ((0 : ℕ) : ℤ)) a :=
  (maxDescendantSigmaStarInvCoeffField_top_le_blockGridSup m a).trans_eq
    (maxDescendantSigmaStarInvCoeffField_eq_blockGridSup m 0 a).symm

/-- The top-scale step, upper, between the two grid maxima the fold compares. -/
theorem maxDescendantBCoeffField_top_le [NeZero d] (m : ℤ) (a : RegCoeffField d) :
    Book.Ch04.maxDescendantBMatrixNormCoeffFieldAtScale (originCube d m) m a
      ≤ Book.Ch04.maxDescendantBMatrixNormCoeffFieldAtScale
        (originCube d m) (m - 1 - ((0 : ℕ) : ℤ)) a :=
  (maxDescendantBCoeffField_top_le_blockGridSup m a).trans_eq
    (maxDescendantBCoeffField_eq_blockGridSup m 0 a).symm


/-! ## 7. The folded split and the folded amplitude -/


/-- The amplitude of a folded lane `ctop * U_0 + U_k`, at the two-term
`l.Gamma.sigma.triangle` constant. -/
noncomputable def foldedAmp (sigma ctop : ℝ) (a : ℕ → ℝ) (k : ℕ) : ℝ :=
  gammaTriangleConst sigma * (ctop * a 0 + a k)

/-- The folded amplitude is positive whenever the unfolded one is. -/
theorem foldedAmp_pos {sigma ctop : ℝ} {a : ℕ → ℝ} (hctop : 0 ≤ ctop)
    (ha : ∀ k, 0 < a k) (k : ℕ) : 0 < foldedAmp sigma ctop a k :=
  mul_pos gammaTriangleConst_pos
    (by have := mul_nonneg hctop (ha 0).le; have := ha k; linarith)

/-- Folding adds one constant series to the amplitude series, so summability is
inherited. -/
theorem summable_foldedAmp {mass rho sigma ctop : ℝ} {a : ℕ → ℝ} (hrho : 0 < rho)
    (hasum : Summable fun k : ℕ => mass * gridWeight rho k * a k) :
    Summable fun k : ℕ => mass * gridWeight rho k * foldedAmp sigma ctop a k := by
  have hw : Summable fun k : ℕ => mass * gridWeight rho k :=
    (gridWeight_summable hrho).mul_left mass
  refine (((hw.mul_left (gammaTriangleConst sigma * (ctop * a 0))).add
    (hasum.mul_left (gammaTriangleConst sigma))).congr fun k => ?_)
  rw [foldedAmp]
  ring

/-- The folded scale sum: the gap-`0` fold costs one extra `rho^{-1}` slot at the
top-scale amplitude, nothing else. -/
theorem tsum_foldedAmp_le {mass rho sigma ctop S : ℝ} {a : ℕ → ℝ}
    (hmass : 0 ≤ mass) (hrho : 0 < rho) (hctop : 0 ≤ ctop) (ha : ∀ k, 0 ≤ a k)
    (hasum : Summable fun k : ℕ => mass * gridWeight rho k * a k)
    (hS : ∑' k : ℕ, mass * gridWeight rho k * a k ≤ S) :
    ∑' k : ℕ, mass * gridWeight rho k * foldedAmp sigma ctop a k
      ≤ gammaTriangleConst sigma * (ctop * a 0 * (mass * rho⁻¹) + S) := by
  have hw : Summable fun k : ℕ => mass * gridWeight rho k :=
    (gridWeight_summable hrho).mul_left mass
  have hwtot : ∑' k : ℕ, mass * gridWeight rho k ≤ mass * rho⁻¹ := by
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (gridWeight_tsum_le hrho) hmass
  have hsplit : ∀ k : ℕ, mass * gridWeight rho k * foldedAmp sigma ctop a k
      = gammaTriangleConst sigma * (ctop * a 0) * (mass * gridWeight rho k)
        + gammaTriangleConst sigma * (mass * gridWeight rho k * a k) := by
    intro k
    rw [foldedAmp]
    ring
  have heq : ∑' k : ℕ, mass * gridWeight rho k * foldedAmp sigma ctop a k
      = gammaTriangleConst sigma * (ctop * a 0) * ∑' k : ℕ, mass * gridWeight rho k
        + gammaTriangleConst sigma * ∑' k : ℕ, mass * gridWeight rho k * a k := by
    rw [← tsum_mul_left, ← tsum_mul_left,
      ← (hw.mul_left (gammaTriangleConst sigma * (ctop * a 0))).tsum_add
        (hasum.mul_left (gammaTriangleConst sigma))]
    exact tsum_congr hsplit
  have hc : 0 ≤ gammaTriangleConst sigma * (ctop * a 0) :=
    mul_nonneg gammaTriangleConst_pos.le (mul_nonneg hctop (ha 0))
  have h1 : gammaTriangleConst sigma * (ctop * a 0) * ∑' k : ℕ, mass * gridWeight rho k
      ≤ gammaTriangleConst sigma * (ctop * a 0) * (mass * rho⁻¹) :=
    mul_le_mul_of_nonneg_left hwtot hc
  have h2 : gammaTriangleConst sigma * ∑' k : ℕ, mass * gridWeight rho k * a k
      ≤ gammaTriangleConst sigma * S :=
    mul_le_mul_of_nonneg_left hS gammaTriangleConst_pos.le
  rw [heq]
  have hexp : gammaTriangleConst sigma * (ctop * a 0 * (mass * rho⁻¹) + S)
      = gammaTriangleConst sigma * (ctop * a 0) * (mass * rho⁻¹)
        + gammaTriangleConst sigma * S := by ring
  rw [hexp]
  linarith

/-- The explicit folded pole: the constant the exceptional lane's amplitude sums
to after the gap-`0` fold and the rounded-up `e.maxy.bound` polynomial. -/
noncomputable def foldedBlockPole (d : ℕ) (sigma A mass rho ctop : ℝ) (p : ℕ) : ℝ :=
  gammaTriangleConst sigma *
    (gammaTriangleConst sigma *
      (ctop * gridBlockAmp d sigma A 0 * (mass * rho⁻¹)
        + mass * (gridNetConst d sigma * A) * blockPoleConst p rho))

/-- The consumers' `hBexp` input, at the folded `e.maxy.bound` amplitude and the
explicit pole. -/
theorem gammaTriangleConst_mul_tsum_foldedGridBlockAmp_le {d : ℕ}
    {mass rho sigma A ctop : ℝ} (hmass : 0 ≤ mass) (hrho : 0 < rho)
    (hctop : 0 ≤ ctop) (hA : 0 ≤ A) (p : ℕ) (hp : sigma⁻¹ ≤ (p : ℝ)) :
    gammaTriangleConst sigma *
        ∑' k : ℕ, mass * gridWeight rho k *
          foldedAmp sigma ctop (fun j => gridBlockAmp d sigma A j) k
      ≤ foldedBlockPole d sigma A mass rho ctop p := by
  refine mul_le_mul_of_nonneg_left ?_ gammaTriangleConst_pos.le
  exact tsum_foldedAmp_le hmass hrho hctop
    (fun k => gridBlockAmp_nonneg d sigma hA k)
    (summable_gridWeight_mul_gridBlockAmp hmass hrho hA p hp)
    (tsum_gridWeight_mul_gridBlockAmp_le hmass hrho hA p hp)

/-! ## 8. The composed payload producers -/


/-! ## 9. The elementary `ell^{q/2}` pre-split -/

/-- **The elementary `ell^{q/2}` pre-split**, at an abstract exponent:
`(x + y)^t <= 2^{t-1} (x^t + y^t)` for `1 <= t` and nonnegative `x`, `y`.  This
is the real-valued form of Mathlib's `NNReal.rpow_add_le_mul_rpow_add_rpow`,
which Mathlib does not export over `ℝ`. -/
theorem rpow_add_le_mul_rpow_add_rpow {x y t : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (ht : 1 ≤ t) :
    (x + y) ^ t ≤ (2 : ℝ) ^ (t - 1) * (x ^ t + y ^ t) := by
  lift x to NNReal using hx
  lift y to NNReal using hy
  exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow x y ht

/-- The pre-split at the exponent the coarse-grained ellipticity aggregate
carries: `(x + y)^{q/2} <= 2^{q/2 - 1} (x^{q/2} + y^{q/2})` for `2 <= q`. -/
theorem rpow_half_add_le_mul_rpow_half_add_rpow_half {x y q : ℝ} (hx : 0 ≤ x)
    (hy : 0 ≤ y) (hq : 2 ≤ q) :
    (x + y) ^ (q / 2) ≤ (2 : ℝ) ^ (q / 2 - 1) * (x ^ (q / 2) + y ^ (q / 2)) :=
  rpow_add_le_mul_rpow_add_rpow hx hy (by linarith)

/-- The companion root step: `(a + b)^{1/t} <= a^{1/t} + b^{1/t}` for `1 <= t`,
i.e. `(a+b)^{2/q} <= a^{2/q} + b^{2/q}` at `t = q/2`. -/
theorem rpow_inv_add_le_add_rpow_inv {a b t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ht : 1 ≤ t) : (a + b) ^ (1 / t) ≤ a ^ (1 / t) + b ^ (1 / t) := by
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
  refine Real.rpow_add_le_add_rpow ha hb (by positivity) ?_
  rw [div_le_one ht0]
  exact ht

/-- The pre-split, applied termwise inside a weighted `ell^t` aggregate. -/
theorem tsum_rpow_presplit_le {w X Y : ℕ → ℝ} {t : ℝ} (hw : ∀ n, 0 ≤ w n)
    (hX : ∀ n, 0 ≤ X n) (hY : ∀ n, 0 ≤ Y n) (ht : 1 ≤ t)
    (hXs : Summable fun n : ℕ => w n * X n ^ t)
    (hYs : Summable fun n : ℕ => w n * Y n ^ t)
    (hsum : Summable fun n : ℕ => w n * (X n + Y n) ^ t) :
    ∑' n : ℕ, w n * (X n + Y n) ^ t
      ≤ (2 : ℝ) ^ (t - 1) *
        ((∑' n : ℕ, w n * X n ^ t) + ∑' n : ℕ, w n * Y n ^ t) := by
  have hmaj : Summable fun n : ℕ =>
      (2 : ℝ) ^ (t - 1) * (w n * X n ^ t + w n * Y n ^ t) := (hXs.add hYs).mul_left _
  have hle : ∀ n : ℕ, w n * (X n + Y n) ^ t
      ≤ (2 : ℝ) ^ (t - 1) * (w n * X n ^ t + w n * Y n ^ t) := by
    intro n
    have h := rpow_add_le_mul_rpow_add_rpow (hX n) (hY n) ht
    calc w n * (X n + Y n) ^ t
        ≤ w n * ((2 : ℝ) ^ (t - 1) * (X n ^ t + Y n ^ t)) :=
          mul_le_mul_of_nonneg_left h (hw n)
      _ = (2 : ℝ) ^ (t - 1) * (w n * X n ^ t + w n * Y n ^ t) := by ring
  have hstep := hsum.tsum_le_tsum hle hmaj
  rwa [tsum_mul_left, hXs.tsum_add hYs] at hstep

/-- **The application shape at the aggregate.**  Splitting the deterministic and
the random part INSIDE the `ell^{q/2}` aggregate, before taking the `2/q` root,
costs a dimension-free factor `2` and no pole. -/
theorem rpow_inv_tsum_presplit_le {w X Y : ℕ → ℝ} {t : ℝ} (hw : ∀ n, 0 ≤ w n)
    (hX : ∀ n, 0 ≤ X n) (hY : ∀ n, 0 ≤ Y n) (ht : 1 ≤ t)
    (hXs : Summable fun n : ℕ => w n * X n ^ t)
    (hYs : Summable fun n : ℕ => w n * Y n ^ t)
    (hsum : Summable fun n : ℕ => w n * (X n + Y n) ^ t) :
    (∑' n : ℕ, w n * (X n + Y n) ^ t) ^ (1 / t)
      ≤ 2 * ((∑' n : ℕ, w n * X n ^ t) ^ (1 / t)
          + (∑' n : ℕ, w n * Y n ^ t) ^ (1 / t)) := by
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
  have hSX : 0 ≤ ∑' n : ℕ, w n * X n ^ t :=
    tsum_nonneg fun n => mul_nonneg (hw n) (Real.rpow_nonneg (hX n) t)
  have hSY : 0 ≤ ∑' n : ℕ, w n * Y n ^ t :=
    tsum_nonneg fun n => mul_nonneg (hw n) (Real.rpow_nonneg (hY n) t)
  have hT : 0 ≤ ∑' n : ℕ, w n * (X n + Y n) ^ t :=
    tsum_nonneg fun n =>
      mul_nonneg (hw n) (Real.rpow_nonneg (add_nonneg (hX n) (hY n)) t)
  have hbase := tsum_rpow_presplit_le hw hX hY ht hXs hYs hsum
  have hmono : (∑' n : ℕ, w n * (X n + Y n) ^ t) ^ (1 / t)
      ≤ ((2 : ℝ) ^ (t - 1) *
        ((∑' n : ℕ, w n * X n ^ t) + ∑' n : ℕ, w n * Y n ^ t)) ^ (1 / t) :=
    Real.rpow_le_rpow hT hbase (by positivity)
  have hsplitmul : ((2 : ℝ) ^ (t - 1) *
        ((∑' n : ℕ, w n * X n ^ t) + ∑' n : ℕ, w n * Y n ^ t)) ^ (1 / t)
      = ((2 : ℝ) ^ (t - 1)) ^ (1 / t) *
        (((∑' n : ℕ, w n * X n ^ t) + ∑' n : ℕ, w n * Y n ^ t)) ^ (1 / t) :=
    Real.mul_rpow (Real.rpow_nonneg (by norm_num) _) (add_nonneg hSX hSY)
  have hconst : ((2 : ℝ) ^ (t - 1)) ^ (1 / t) ≤ 2 := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    calc (2 : ℝ) ^ ((t - 1) * (1 / t)) ≤ (2 : ℝ) ^ (1 : ℝ) := by
          refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
          rw [mul_one_div, div_le_one ht0]
          linarith
      _ = 2 := Real.rpow_one 2
  have hsub : (((∑' n : ℕ, w n * X n ^ t) + ∑' n : ℕ, w n * Y n ^ t)) ^ (1 / t)
      ≤ (∑' n : ℕ, w n * X n ^ t) ^ (1 / t)
        + (∑' n : ℕ, w n * Y n ^ t) ^ (1 / t) :=
    rpow_inv_add_le_add_rpow_inv hSX hSY ht
  have hnn : (0 : ℝ) ≤ (((∑' n : ℕ, w n * X n ^ t)
      + ∑' n : ℕ, w n * Y n ^ t)) ^ (1 / t) :=
    Real.rpow_nonneg (add_nonneg hSX hSY) _
  calc (∑' n : ℕ, w n * (X n + Y n) ^ t) ^ (1 / t)
      ≤ ((2 : ℝ) ^ (t - 1)) ^ (1 / t) *
        (((∑' n : ℕ, w n * X n ^ t) + ∑' n : ℕ, w n * Y n ^ t)) ^ (1 / t) := by
        rw [← hsplitmul]; exact hmono
    _ ≤ 2 * (((∑' n : ℕ, w n * X n ^ t)
          + ∑' n : ℕ, w n * Y n ^ t)) ^ (1 / t) :=
        mul_le_mul_of_nonneg_right hconst hnn
    _ ≤ 2 * ((∑' n : ℕ, w n * X n ^ t) ^ (1 / t)
          + (∑' n : ℕ, w n * Y n ^ t) ^ (1 / t)) :=
        mul_le_mul_of_nonneg_left hsub (by norm_num)

end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
