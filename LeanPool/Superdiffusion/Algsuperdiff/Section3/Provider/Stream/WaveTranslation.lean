/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.IncrementTranslation
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.TranslatedLargeCubeW1Inf

/-!
# WaveTranslation

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The uniform large-cube supremum gauge at an arbitrary triadic cube

`Provider/Stream/IncrementTranslation.lean` moved the *cube-averaged* `L^p`
chain of ABK26's Step 2 from the centered cube `cu_l` to an arbitrary triadic
cube `Q`.  The `L^infty` chain did not move with it, and this is what blocked
the wave terms of Step 2: `largeCubeSupBound l n m` is not a cube average but a
uniform supremum gauge, represented by a maximum of small-cube gauges over an explicit
covering grid *inside* `cu_l` (`Provider/Stream/LargeCubeLinfty.lean`).
Transporting it to `Q` therefore requires re-indexing the covering grid, which
no proved statement did: `TranslatedLargeCubeW1Inf.lean` and
`TranslatedTransport.lean` carry the one-shell half of that machinery only (a
single translated base point `z`, and the covering maximum only for the
own-scale derivative gauge of a single shell).

This module supplies the missing deterministic half and its immediate
probabilistic consequence.

## The grid re-indexing

The covering family of the origin cube `cu_l` at scale `n` is indexed by the
finite set `subcubeShifts d n l` of lattice points of `3^{n-1} Z^d`, the grid
point of index `p` sitting at `subcubeCenter n p`.  The covering family of `Q`
is the SAME index set at `l = Q.scale`, with every grid point pushed forward by
the base point `z_Q = triadicCubeShift Q` of `Q`:

```
  cubeSubcubeCenter Q n p  =  subcubeCenter n p + z_Q .
```

`exists_cubeSubcubeCenter_mem` is the resulting covering property at `Q` (every
point of the open cube `Q` lies in one of the translated open small cubes),
obtained from CoarseGraining's
`openCubeSet_eq_translateSet_originCube_of_triadicCube` and the proved origin
covering property `exists_subcubeShift_mem`.

## The generator

`cubeSupBound_eq_largeCubeSupBound_translate`:

```
  cubeSupBound Q n m omega  =  largeCubeSupBound Q.scale n m (tau_{z_Q} omega) ,
```

with `tau_z = ShellField.translateSequence z` the joint translation action on
the whole shell sequence.  This is an equality of functions of the sample, not
an equality in law: the per-cube gauge is the origin-cube gauge read at the
translated sample.  Its one-cube
step is `translatedIncrementSupBound_cubeSubcubeCenter`, which is exactly the
re-indexing: the small-cube gauge at the pushed-forward grid point of the
original sample is the small-cube gauge at the original grid point of the
translated sample.

Everything else here is a corollary of the generator together with the proved
abstract transport `isBigOWith_comp_translateSequence` /
`isBigOWith_comp_translateCutoffSample`.  In particular every transported
amplitude is the O amplitude read at `l = Q.scale`, V: translation is an exact
isometry of the law, so there is no union bound, no covering penalty beyond the
one the origin display already pays, and no new dimension-only constant
anywhere in this module.

## Main definitions

* `Algsuperdiff.Section3.Provider.Stream.cubeSubcubeCenter`
* `Algsuperdiff.Section3.Provider.Stream.cubeSupBound`

## Main results

* `Algsuperdiff.Section3.Provider.Stream.exists_cubeSubcubeCenter_mem`
* `Algsuperdiff.Section3.Provider.Stream.cubeSupBound_eq_largeCubeSupBound_translate`
* `Algsuperdiff.Section3.Provider.Stream.matrixOperatorNorm_finiteShellIncrement_le_cubeSupBound`
* `Algsuperdiff.Section3.Provider.Stream.isBigOWith_gammaSigma_cubeSupBound`
* `Algsuperdiff.Section3.Provider.Stream.isBigOWith_gammaSigma_cubeSupBound_cutoffLaw`

## References

* ABK26, `e.km.kn.Linfty`, proof (the origin display whose covering grid is
  re-indexed here).
* ABK26, `e.kmn.bounds`, ("by the assumption of `R^d`-stationarity"), and
  `l.bad.event.lemma`, in particular the reduction "by stationarity, it
  suffices to prove the case `z = 0`" with `z in R^d`.
* `Provider/Stream/LargeCubeLinfty.lean` (the origin covering grid),
  `Provider/Stream/IncrementTranslation.lean` (the abstract transport),
  `Homogenization/Geometry/TriadicCubeTranslation.lean` (the cube geometry).
-/

namespace Algsuperdiff.Section3.Provider.Stream

open MeasureTheory
open HCPolySupport
open HCPolySupport.Book.Ch02
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## The covering grid of an arbitrary triadic cube -/

/-- The base point of the scale-`n` covering cube of index `p` inside the
triadic cube `Q`: the origin grid point `subcubeCenter n p` pushed forward by
the base point `triadicCubeShift Q` of `Q`.

This is the re-indexing of the covering family under the translation: the index
set is unchanged, only the grid points move. -/
def cubeSubcubeCenter (Q : TriadicCube d) (n : ℤ) (p : Fin d → ℤ) : Vec d :=
  subcubeCenter n p + triadicCubeShift Q

/-- **The covering property at an arbitrary cube.**  Every point of the open
cube `Q` lies in one of the translated open small cubes of the re-indexed
family, whose index set is the origin index set at the scale of `Q`. -/
theorem exists_cubeSubcubeCenter_mem (Q : TriadicCube d) (n : ℤ) {x : Vec d}
    (hx : x ∈ openCubeSet Q) :
    ∃ p ∈ subcubeShifts d n Q.scale,
      x ∈ translateSet (cubeSubcubeCenter Q n p) (openCubeSet (originCube d n)) := by
  have hx0 : x - triadicCubeShift Q ∈ openCubeSet (originCube d Q.scale) := by
    rw [openCubeSet_eq_translateSet_originCube_of_triadicCube Q,
      mem_translateSet_iff_sub_mem] at hx
    exact hx
  obtain ⟨p, hp, hmem⟩ := exists_subcubeShift_mem (d := d) n Q.scale hx0
  refine ⟨p, hp, ?_⟩
  rw [mem_translateSet_iff_sub_mem] at hmem ⊢
  have hsub : x - cubeSubcubeCenter Q n p =
      x - triadicCubeShift Q - subcubeCenter n p := by
    rw [cubeSubcubeCenter]
    abel
  rw [hsub]
  exact hmem

/-! ## The per-cube uniform supremum gauge -/

/-- The single random variable dominating `‖k_m - k_n‖_{L∞(Q)}` at an A triadic
cube `Q`: the maximum of the small-cube gauges over the re-indexed covering
family of `Q`. -/
def cubeSupBound (Q : TriadicCube d) (n m : ℤ) (omega : ShellSeq d) : ℝ :=
  (subcubeShifts d n Q.scale).sup' (subcubeShifts_nonempty d n Q.scale)
    fun p => translatedIncrementSupBound (cubeSubcubeCenter Q n p) n m omega

/-- **The one-cube re-indexing step.**  The small-cube gauge at the pushed-forward
grid point, read at the original sample, is the small-cube gauge at the
original grid point, read at the T sample. -/
theorem translatedIncrementSupBound_cubeSubcubeCenter (Q : TriadicCube d) (n m : ℤ)
    (p : Fin d → ℤ) (omega : ShellSeq d) :
    translatedIncrementSupBound (cubeSubcubeCenter Q n p) n m omega =
      translatedIncrementSupBound (subcubeCenter n p) n m
        (ShellField.translateSequence (triadicCubeShift Q) omega) := by
  rw [translatedIncrementSupBound, translatedIncrementSupBound]
  congr 1
  funext k
  simp only [translateShellSeq, ShellField.translateSequence_apply, cubeSubcubeCenter]
  exact (translate_translate (subcubeCenter n p) (triadicCubeShift Q) (omega k)).symm

/-- **The grid re-indexing identity.**  The uniform supremum gauge of the
finite stream increment on an arbitrary triadic cube `Q` is the origin-cube
gauge at the scale of `Q`, read at the sample translated by the base point of
`Q`.

This is an exact identity of functions of the sample — not an identity in law —
and it is the deterministic half of the transport of the Step-2 wave terms. -/
theorem cubeSupBound_eq_largeCubeSupBound_translate (Q : TriadicCube d) (n m : ℤ)
    (omega : ShellSeq d) :
    cubeSupBound Q n m omega =
      largeCubeSupBound Q.scale n m
        (ShellField.translateSequence (triadicCubeShift Q) omega) := by
  rw [cubeSupBound, largeCubeSupBound]
  refine le_antisymm (Finset.sup'_le _ _ fun p hp => ?_) (Finset.sup'_le _ _ fun p hp => ?_)
  · rw [translatedIncrementSupBound_cubeSubcubeCenter]
    exact Finset.le_sup'
      (fun q : Fin d → ℤ => translatedIncrementSupBound (subcubeCenter n q) n m
        (ShellField.translateSequence (triadicCubeShift Q) omega)) hp
  · rw [← translatedIncrementSupBound_cubeSubcubeCenter]
    exact Finset.le_sup'
      (fun q : Fin d → ℤ =>
        translatedIncrementSupBound (cubeSubcubeCenter Q n q) n m omega) hp

theorem cubeSupBound_nonneg (Q : TriadicCube d) (n m : ℤ) (omega : ShellSeq d) :
    0 ≤ cubeSupBound Q n m omega := by
  rw [cubeSupBound_eq_largeCubeSupBound_translate]
  exact largeCubeSupBound_nonneg _ _ _ _

/-- **The deterministic half of `e.km.kn.Linfty` at an arbitrary cube**: at
every point of the open cube `Q` the finite stream increment is dominated by
the single random variable `cubeSupBound Q n m`. -/
theorem matrixOperatorNorm_finiteShellIncrement_le_cubeSupBound
    (omega : ShellSeq d) (Q : TriadicCube d) (n m : ℤ) {x : Vec d}
    (hx : x ∈ openCubeSet Q) :
    matrixOperatorNorm (finiteShellIncrement omega n m x) ≤ cubeSupBound Q n m omega := by
  obtain ⟨p, hp, hmem⟩ := exists_cubeSubcubeCenter_mem Q n hx
  refine le_trans
    (matrixOperatorNorm_finiteShellIncrement_le_translatedIncrementSupBound
      (cubeSubcubeCenter Q n p) omega n m hmem) ?_
  exact Finset.le_sup'
    (fun q : Fin d → ℤ =>
      translatedIncrementSupBound (cubeSubcubeCenter Q n q) n m omega) hp

/-! ## Measurability -/

/-- The translated small-cube gauge is a random variable. -/
theorem measurable_translatedIncrementSupBound (z : Vec d) (n m : ℤ) :
    Measurable (translatedIncrementSupBound (d := d) z n m) := by
  have hrw : translatedIncrementSupBound (d := d) z n m = fun omega : ShellSeq d =>
      matrixOperatorNorm (finiteShellIncrement omega n m z) +
        (d : ℝ) ^ 2 * Real.sqrt d * ((3 : ℝ) ^ n / 2) *
          ∑ k ∈ Finset.Ioc n m,
            localCubeDerivNorm n (ShellField.translate z (omega k)) :=
    funext fun omega => translatedIncrementSupBound_eq z n m omega
  rw [hrw]
  refine (measurable_matrixOperatorNorm_finiteShellIncrement n m z).add ?_
  refine measurable_const.mul ?_
  exact Finset.measurable_sum _ fun k _ =>
    (measurable_localCubeDerivNorm n).comp
      ((ShellField.measurable_translate z).comp (measurable_pi_apply k))

/-- The origin-cube uniform gauge is a random variable. -/
theorem measurable_largeCubeSupBound (l n m : ℤ) :
    Measurable (largeCubeSupBound (d := d) l n m) := by
  have hrw : largeCubeSupBound (d := d) l n m =
      (subcubeShifts d n l).sup' (subcubeShifts_nonempty d n l)
        fun p => translatedIncrementSupBound (subcubeCenter n p) n m := by
    funext omega
    rw [largeCubeSupBound, Finset.sup'_apply]
  rw [hrw]
  exact Finset.measurable_sup' (subcubeShifts_nonempty d n l) fun p _ =>
    measurable_translatedIncrementSupBound (subcubeCenter n p) n m

/-- The per-cube uniform gauge is a random variable. -/
theorem measurable_cubeSupBound (Q : TriadicCube d) (n m : ℤ) :
    Measurable (cubeSupBound Q n m) := by
  have hrw : cubeSupBound Q n m = fun omega : ShellSeq d =>
      largeCubeSupBound Q.scale n m
        (ShellField.translateSequence (triadicCubeShift Q) omega) :=
    funext fun omega => cubeSupBound_eq_largeCubeSupBound_translate Q n m omega
  rw [hrw]
  exact (measurable_largeCubeSupBound Q.scale n m).comp
    (ShellField.measurable_translateSequence (triadicCubeShift Q))

/-! ## `e.km.kn.Linfty` at an arbitrary triadic cube -/

theorem isBigOWith_gammaSigma_cubeSupBound (M : ABKModel d) {n m : ℤ} (hnm : n < m)
    (Q : TriadicCube d) :
    IndependentSums.IsBigOWith M.P.toMeasure (IndependentSums.gammaSigma 2)
      (cubeSupBound Q n m)
      ((3 * max 1 (Real.log (((subcubeShifts d n Q.scale).card : ℕ) : ℝ))) ^ (2 : ℝ)⁻¹ *
        (streamLinftyConst d *
          min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) *
          (3 : ℝ) ^ (M.gamma * (m : ℝ)))) := by
  have hfun : cubeSupBound Q n m = fun omega : ShellSeq d =>
      largeCubeSupBound Q.scale n m
        (ShellField.translateSequence (triadicCubeShift Q) omega) :=
    funext fun omega => cubeSupBound_eq_largeCubeSupBound_translate Q n m omega
  rw [hfun]
  exact isBigOWith_comp_translateSequence M (triadicCubeShift Q)
    (measurable_largeCubeSupBound Q.scale n m)
    (isBigOWith_gammaSigma_largeCubeSupBound M (l := Q.scale) hnm)

/-! ## The estimates on the lower-tail cutoff carrier -/

/-- The per-cube covering maximum, read on the lower-tail cutoff carrier. -/
theorem isBigOWith_gammaSigma_cubeSupBound_cutoffLaw (M : ABKModel d) {n m : ℤ}
    (hnm : n < m) (Q : TriadicCube d) :
    IndependentSums.IsBigOWith (cutoffSampleLaw M).toMeasure
      (IndependentSums.gammaSigma 2)
      (fun omega : CutoffSample d => cubeSupBound Q n m omega.1)
      ((3 * max 1 (Real.log (((subcubeShifts d n Q.scale).card : ℕ) : ℝ))) ^ (2 : ℝ)⁻¹ *
        (streamLinftyConst d *
          min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (n : ℝ))) *
          (3 : ℝ) ^ (M.gamma * (m : ℝ)))) :=
  isBigOWith_cutoffSampleLaw_comp_val (isBigOWith_gammaSigma_cubeSupBound M hnm Q)

end

end Algsuperdiff.Section3.Provider.Stream
