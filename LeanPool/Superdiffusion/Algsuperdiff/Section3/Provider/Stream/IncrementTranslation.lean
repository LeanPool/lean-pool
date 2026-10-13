/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.IncrementLpLarge
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.CutoffLawTransport
public import LeanPool.HighContrastHomogenization.Support.Geometry.TriadicCubeTranslation
public import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# IncrementTranslation

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The stream-increment `L^p` chain at an arbitrary triadic cube

ABK26 states every stream-increment estimate at the *centered* cube `cu_l` and
then moves it to an off-centre cube by the single phrase "by
`R^d`-stationarity" (for `e.kmn.bounds`;, for the bad-event lemma).  The
whole proved Step-2 chain of this repository — `streamIncrementLpMass`,
`streamIncrementLpNorm`, `streamIncrementLpTail` and the `Gamma` estimates
built on them — is likewise defined on the origin cubes only.  This module
supplies the passage, at the level of the *observable*, from the origin cube to
every triadic cube `Q`.

## The two halves, and what was already available

The manuscript's step has a deterministic half and a probabilistic half, and
BOTH halves were already proved in this repository before this module:

* the **joint multi-shell covariance** of the increment,
  `Stream.translateReg_finiteShellIncrement` (`IncrementLaw.lean`):
  `translateReg z (k_m - k_n)(omega) = (k_m - k_n)(tau_z omega)` with
  `tau_z = ShellField.translateSequence z` acting on *every* shell at once; and
* the **joint law invariance** `Cutoff.sequenceLaw_stationary`
  (`Cutoff/Symmetry.lean`): `(tau_z)_* P = P` for every `z : Vec d`, derived
  from the frozen shell independence, the frozen marginal scaling law and (J1)
  through `Measure.infinitePi`.

What was missing is the composite: no statement anywhere carried a
stream-increment `L^p` quantity at a cube other than `cu_l`.

## The generator

`cubeAverage_streamIncrementLpDensity_eq_streamIncrementLpMass_translate`:

```
  ⨍_{Q} |(k_m - k_n)(x)|^p dx  =  ⨍_{cu_{Q.scale}} |(k_m - k_n)(tau_{z_Q} omega)(x)|^p dx ,
```

`z_Q = triadicCubeShift Q` the base point of `Q`.  This is an equality of
functions of the sample, not an equality in law: the per-cube mass is the
origin-cube mass read at the
translated sample.  It is assembled from CoarseGraining's
`cubeSet_eq_translateSet_originCube_of_triadicCube`, the proved
`regFieldLpMass_translateSet` and `translateReg_finiteShellIncrement`.

Everything else in the module is a corollary of the generator together with the
one abstract transport principle `isBigOWith_comp_of_map_eq`: a weak-Orlicz
upper-tail bound sees only the law of its random variable, so it survives
composition with any measure-preserving self-map, for Orlicz profile `Psi` (not
only `gammaSigma sigma`).

## What is delivered

* **the generator** and its norm form
  (`cubeStreamIncrementLpNorm_eq_streamIncrementLpNorm_translate`);
* **`e.kmn.bounds` at every cube** — `Gamma_{2/p}` for the per-cube mass,
  `Gamma_2` for the per-cube norm, `Gamma_1` for its square.  The
  `Gamma_2`-per-cube norm estimate is the "translated `Gamma_2` wave estimate
  applied cube by cube" that the corrected `e.bL` Step-3 aggregation (with
  the exponent bookkeeping) requires, and that
  `Provider/Multiscale/ConclusionSeam2.lean` recorded as its missing Step-2
  input.  Nothing in this module changed; `ConclusionSeam2`'s own root-collapse
  route also remains proved;
* **`e.kl.bounds.large` at every cube** — the head-plus-decaying-tail form of
  `streamIncrementLpMass_head_tail_gain` / `streamIncrementLpNorm_head_tail_gain`
  transported to `Q`, with the gain read at `Q.scale`;
* **the abstract translate transport on the cutoff carrier**,
  `isBigOWith_comp_translateCutoffSample` and
  `measureReal_preimage_translateCutoffSample`: any law-level bound, and any
  event probability, proved at the origin holds verbatim at every real
  translate of the cutoff sample.  This is the shape of the manuscript's own
  reduction "by stationarity, it suffices to prove the case `z = 0`", and the
  shape a translate family for `e.bL.multiscale` would be consumed through.
  NOTE: `e.bL.multiscale` itself has no realization in this repository, and
  none is asserted here.

## Conventions

* `cubeAverage Q` is CoarseGraining's average over the HALF-O cube `cubeSet Q`,
  which is what CoarseGraining's partition identity and
  `Provider/Stream/IncrementConcentration.lean` use; `streamIncrementLpMass` is
  the average over the O origin cube.  The two agree
  (`streamIncrementLpMass_eq_cubeAverage`), the boundary being null.
* `Q.scale` replaces the origin-cube index `l` everywhere: a per-cube statement
  at `Q` is the origin statement at `l = Q.scale`.

## Main definitions

* `cubeStreamIncrementLpNorm`, `cubeStreamIncrementLpTail`.

## Main results

* `cubeAverage_streamIncrementLpDensity_eq_streamIncrementLpMass_translate`.
* `isBigOWith_comp_of_map_eq`, `isBigOWith_comp_translateSequence`,
  `isBigOWith_comp_translateCutoffSample`,
  `measureReal_preimage_translateCutoffSample`.
* `isBigOWith_gammaSigma_cubeAverage_streamIncrementLpDensity`,
  `isBigOWith_gammaSigma_cubeStreamIncrementLpNorm`,
  `isBigOWith_gammaSigma_cubeAverage_streamIncrementLpDensity_cutoffLaw`.
* `cubeStreamIncrementLpNorm_head_tail_gain`.

## References

* ABK26, `e.kmn.bounds`, (its "`R^d`-stationarity" is the step proved locally
  here); `e.kl.bounds.large`; `e.km.kn.Lp`; `l.bad.event.lemma`, (the "by
  stationarity" reduction, with `z in R^d`).
* `Provider/Stream/IncrementLaw.lean`, `Cutoff/Symmetry.lean` — the two halves
  of the stationarity step that this module composes.
-/

namespace Algsuperdiff.Section3.Provider.Stream

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## The generator: the per-cube mass as a translated origin-cube mass -/

/-- **The stationarity reduction, at the level of the observable.**  The
volume-normalized `L^p` mass of a stream increment on an A triadic cube `Q` is
the origin-cube mass at the scale of `Q`, read at the sample translated by the
base point `triadicCubeShift Q` of `Q`.

This is an exact identity of functions of the sample — not an identity in law —
and it is what makes every proved origin-cube estimate transport verbatim to
every cube. -/
theorem cubeAverage_streamIncrementLpDensity_eq_streamIncrementLpMass_translate
    {p : ℝ} (hp : 0 < p) (Q : TriadicCube d) (n m : ℤ) (omega : ShellSeq d) :
    cubeAverage Q (streamIncrementLpDensity p n m omega) =
      streamIncrementLpMass p Q.scale n m
        (ShellField.translateSequence (triadicCubeShift Q) omega) := by
  rw [cubeAverage_streamIncrementLpDensity,
    cubeSet_eq_translateSet_originCube_of_triadicCube Q, regFieldLpMass_translateSet,
    translateReg_finiteShellIncrement, ← cubeAverage_streamIncrementLpDensity,
    ← streamIncrementLpMass_eq_cubeAverage hp]

/-- The volume-normalized `L^p` norm `‖k_m - k_n‖_{L^p(Q)}` of a stream
increment on an arbitrary triadic cube `Q`. -/
def cubeStreamIncrementLpNorm (p : ℝ) (Q : TriadicCube d) (n m : ℤ)
    (omega : ShellSeq d) : ℝ :=
  cubeAverage Q (streamIncrementLpDensity p n m omega) ^ p⁻¹

/-- The norm form of the generator. -/
theorem cubeStreamIncrementLpNorm_eq_streamIncrementLpNorm_translate {p : ℝ}
    (hp : 0 < p) (Q : TriadicCube d) (n m : ℤ) (omega : ShellSeq d) :
    cubeStreamIncrementLpNorm p Q n m omega =
      streamIncrementLpNorm p Q.scale n m
        (ShellField.translateSequence (triadicCubeShift Q) omega) := by
  rw [cubeStreamIncrementLpNorm,
    cubeAverage_streamIncrementLpDensity_eq_streamIncrementLpMass_translate hp,
    streamIncrementLpNorm]

theorem cubeStreamIncrementLpNorm_nonneg {p : ℝ} (hp : 0 < p) (Q : TriadicCube d)
    (n m : ℤ) (omega : ShellSeq d) :
    0 ≤ cubeStreamIncrementLpNorm p Q n m omega := by
  rw [cubeStreamIncrementLpNorm_eq_streamIncrementLpNorm_translate hp]
  exact streamIncrementLpNorm_nonneg p Q.scale n m _

/-! ## Transport of a weak-Orlicz bound along a measure-preserving self-map -/

/-- **The abstract transport principle.**  A weak-Orlicz upper-tail bound sees
only the law of its random variable, so it survives composition with any
measure-preserving self-map of the sample space — for every Orlicz profile
`Psi`, not only for `gammaSigma sigma`. -/
theorem isBigOWith_comp_of_map_eq {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {T : Omega → Omega} (hT : Measurable T)
    (hmap : Measure.map T mu = mu) {Psi : ℝ → ℝ} {X : Omega → ℝ}
    (hX : Measurable X) {A : ℝ}
    (h : IndependentSums.IsBigOWith mu Psi X A) :
    IndependentSums.IsBigOWith mu Psi (fun omega => X (T omega)) A := by
  intro t ht
  have hset : MeasurableSet (IndependentSums.upperTailEvent X (A * t)) :=
    measurableSet_lt measurable_const hX
  have hpre : mu (T ⁻¹' IndependentSums.upperTailEvent X (A * t)) =
      mu (IndependentSums.upperTailEvent X (A * t)) := by
    rw [← Measure.map_apply hT hset, hmap]
  calc mu.real (IndependentSums.upperTailEvent (fun omega => X (T omega)) (A * t))
      = mu.real (IndependentSums.upperTailEvent X (A * t)) := by
        rw [measureReal_def, measureReal_def]
        exact congrArg ENNReal.toReal hpre
    _ ≤ (Psi t)⁻¹ := h ht

/-- Every weak-Orlicz bound on a measurable shell-sequence observable holds
verbatim for the observable read at the jointly translated sample. -/
theorem isBigOWith_comp_translateSequence (M : ABKModel d) (z : Vec d)
    {Psi : ℝ → ℝ} {X : ShellSeq d → ℝ} (hX : Measurable X) {A : ℝ}
    (h : IndependentSums.IsBigOWith M.P.toMeasure Psi X A) :
    IndependentSums.IsBigOWith M.P.toMeasure Psi
      (fun omega : ShellSeq d => X (ShellField.translateSequence z omega)) A :=
  isBigOWith_comp_of_map_eq (ShellField.measurable_translateSequence z)
    (sequenceLaw_stationary M z) hX h

/-- **The translate transport on the cutoff carrier.**  Every weak-Orlicz bound
proved for a measurable observable of the cutoff sample holds verbatim for the
observable read at every translate of the sample.

This is the shape in which a translate family for an origin-only display is
consumed: whatever bound is available at the origin-centred cube is available,
with the same amplitude and the same Orlicz profile, at `z + cu_n` for every
`z : Vec d`.  Nothing here asserts any particular origin bound. -/
theorem isBigOWith_comp_translateCutoffSample (M : ABKModel d) (z : Vec d)
    {Psi : ℝ → ℝ} {X : CutoffSample d → ℝ} (hX : Measurable X) {A : ℝ}
    (h : IndependentSums.IsBigOWith (cutoffSampleLaw M).toMeasure Psi X A) :
    IndependentSums.IsBigOWith (cutoffSampleLaw M).toMeasure Psi
      (fun omega : CutoffSample d => X (translateCutoffSample z omega)) A :=
  isBigOWith_comp_of_map_eq (measurable_translateCutoffSample z)
    (map_translateCutoffSample_cutoffSampleLaw M z) hX h

/-- **The event form of the manuscript's "by stationarity" reduction**: a
translated event has exactly the probability of the original one, for every
real translation vector. -/
theorem measureReal_preimage_translateCutoffSample (M : ABKModel d) (z : Vec d)
    {E : Set (CutoffSample d)} (hE : MeasurableSet E) :
    (cutoffSampleLaw M).toMeasure.real (translateCutoffSample z ⁻¹' E) =
      (cutoffSampleLaw M).toMeasure.real E := by
  rw [measureReal_def, measureReal_def,
    ← Measure.map_apply (measurable_translateCutoffSample z) hE,
    map_translateCutoffSample_cutoffSampleLaw M z]

/-! ## Measurability of the transported observables -/

private theorem measurable_mass {p : ℝ} (hp : 0 < p) (l n m : ℤ) :
    Measurable (streamIncrementLpMass (d := d) p l n m) := by
  have hswap : (fun q : ShellSeq d × Vec d => streamIncrementLpDensity p n m q.1 q.2) =
      Function.uncurry (fun (x : Vec d) (w : ShellSeq d) =>
        streamIncrementLpDensity p n m w x) ∘ Prod.swap := rfl
  have hjoint : Measurable fun q : ShellSeq d × Vec d =>
      streamIncrementLpDensity p n m q.1 q.2 := by
    rw [hswap]
    exact (measurable_uncurry_streamIncrementLpDensity hp n m).comp measurable_swap
  have hSM := MeasureTheory.StronglyMeasurable.integral_prod_right
      (ν := volume.restrict (openCubeSet (originCube d l)))
      (f := fun (w : ShellSeq d) (x : Vec d) => streamIncrementLpDensity p n m w x)
      hjoint.stronglyMeasurable
  have hrw : streamIncrementLpMass (d := d) p l n m = fun omega : ShellSeq d =>
      (volume (openCubeSet (originCube d l))).toReal⁻¹ *
        ∫ x in openCubeSet (originCube d l), streamIncrementLpDensity p n m omega x := by
    funext omega
    rw [streamIncrementLpMass, Book.Ch02.average, Book.Ch02.cubeDomain_coe]
  rw [hrw]
  exact measurable_const.mul hSM.measurable

private theorem measurable_norm {p : ℝ} (hp : 0 < p) (l n m : ℤ) :
    Measurable (streamIncrementLpNorm (d := d) p l n m) :=
  (measurable_mass hp l n m).pow_const _

private theorem measurable_tail (M : ABKModel d) {p : ℝ} (hp : 0 < p) (l n m : ℤ) :
    Measurable (streamIncrementLpTail M p l n m) := by
  by_cases hc : m + (incrementPartitionShift d : ℤ) ≤ l
  · have hrw : streamIncrementLpTail M p l n m = fun omega : ShellSeq d =>
        |streamIncrementLpMass p l n m omega -
          ∫ w, streamIncrementLpMass p (m + (incrementPartitionShift d : ℤ)) n m w
            ∂M.P.toMeasure| := by
      funext omega
      rw [streamIncrementLpTail, ite_eq_left hc]
    rw [hrw]
    have hsub : Measurable fun omega : ShellSeq d =>
        streamIncrementLpMass p l n m omega -
          ∫ w, streamIncrementLpMass p (m + (incrementPartitionShift d : ℤ)) n m w
            ∂M.P.toMeasure :=
      (measurable_mass hp l n m).sub measurable_const
    exact hsub.abs
  · have hrw : streamIncrementLpTail M p l n m = streamIncrementLpMass p l n m := by
      funext omega
      rw [streamIncrementLpTail, ite_eq_right hc]
    rw [hrw]
    exact measurable_mass hp l n m

/-! ## `e.kmn.bounds` at every triadic cube -/

/-- **`e.kmn.bounds` at every cube.**  The `Gamma_{2/p}` estimate of ABK26's
`e.kmn.bounds` holds at every triadic cube `Q`, with the SAME amplitude as at
the origin cube of the same scale. -/
theorem isBigOWith_gammaSigma_cubeAverage_streamIncrementLpDensity (M : ABKModel d)
    {p : ℝ} (hp : 1 ≤ p) {n m : ℤ} (hnm : n < m) (Q : TriadicCube d) :
    IndependentSums.IsBigOWith M.P.toMeasure (IndependentSums.gammaSigma (2 / p))
      (fun omega : ShellSeq d => cubeAverage Q (streamIncrementLpDensity p n m omega))
      (streamIncrementLpMassScale M p n m) := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  have hfun : (fun omega : ShellSeq d =>
      cubeAverage Q (streamIncrementLpDensity p n m omega)) =
      fun omega : ShellSeq d => streamIncrementLpMass p Q.scale n m
        (ShellField.translateSequence (triadicCubeShift Q) omega) :=
    funext fun omega =>
      cubeAverage_streamIncrementLpDensity_eq_streamIncrementLpMass_translate hp0 Q n m omega
  rw [hfun]
  exact isBigOWith_comp_translateSequence M (triadicCubeShift Q)
    (measurable_mass hp0 Q.scale n m)
    (isBigOWith_gammaSigma_streamIncrementLpMass M hp hnm Q.scale)

/-- **The per-cube `Gamma_2` `L^p`-norm estimate.**  This is the "translated
`Gamma_2` wave estimate applied cube by cube" of the corrected `e.bL` Step-3
aggregation (exponents), and the Step-2 input recorded as missing by
`Provider/Multiscale/ConclusionSeam2.lean`; the per-cube route is consumed
there through
`isBigOWith_gammaSigma_cubeAverage_streamIncrementLpDensity_cutoffLaw` (in
`LayerPerCubePricing.lean` and `ConclusionSeam2PerCube.lean`; attribution
corrected).

No large-scale gain is claimed here: this is the `Q`-uniform envelope of
`e.kmn.bounds`.  The gain is `cubeStreamIncrementLpNorm_head_tail_gain`. -/
theorem isBigOWith_gammaSigma_cubeStreamIncrementLpNorm (M : ABKModel d) {p : ℝ}
    (hp : 1 ≤ p) {n m : ℤ} (hnm : n < m) (Q : TriadicCube d) :
    IndependentSums.IsBigOWith M.P.toMeasure (IndependentSums.gammaSigma 2)
      (cubeStreamIncrementLpNorm p Q n m) (streamIncrementLpNormScale M p n m) := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  have hfun : cubeStreamIncrementLpNorm p Q n m =
      fun omega : ShellSeq d => streamIncrementLpNorm p Q.scale n m
        (ShellField.translateSequence (triadicCubeShift Q) omega) :=
    funext fun omega =>
      cubeStreamIncrementLpNorm_eq_streamIncrementLpNorm_translate hp0 Q n m omega
  rw [hfun]
  exact isBigOWith_comp_translateSequence M (triadicCubeShift Q)
    (measurable_norm hp0 Q.scale n m)
    (isBigOWith_gammaSigma_streamIncrementLpNorm M hp hnm Q.scale)

/-! ## The estimates on the cutoff carrier -/

/-- The per-cube `Gamma_{2/p}` mass estimate, read on the lower-tail cutoff
carrier. -/
theorem isBigOWith_gammaSigma_cubeAverage_streamIncrementLpDensity_cutoffLaw
    (M : ABKModel d) {p : ℝ} (hp : 1 ≤ p) {n m : ℤ} (hnm : n < m)
    (Q : TriadicCube d) :
    IndependentSums.IsBigOWith (cutoffSampleLaw M).toMeasure
      (IndependentSums.gammaSigma (2 / p))
      (fun omega : CutoffSample d =>
        cubeAverage Q (streamIncrementLpDensity p n m omega.1))
      (streamIncrementLpMassScale M p n m) :=
  isBigOWith_cutoffSampleLaw_comp_val
    (isBigOWith_gammaSigma_cubeAverage_streamIncrementLpDensity M hp hnm Q)

/-! ## `e.kl.bounds.large` at every triadic cube -/

/-- The per-cube tail of the head-plus-gain decomposition: the proved origin-cube
tail `streamIncrementLpTail` at scale `Q.scale`, read at the sample translated
by the base point of `Q`. -/
def cubeStreamIncrementLpTail (M : ABKModel d) (p : ℝ) (Q : TriadicCube d)
    (n m : ℤ) (omega : ShellSeq d) : ℝ :=
  streamIncrementLpTail M p Q.scale n m
    (ShellField.translateSequence (triadicCubeShift Q) omega)

theorem cubeStreamIncrementLpTail_nonneg (M : ABKModel d) (p : ℝ)
    (Q : TriadicCube d) (n m : ℤ) (omega : ShellSeq d) :
    0 ≤ cubeStreamIncrementLpTail M p Q n m omega :=
  streamIncrementLpTail_nonneg M p Q.scale n m _

/-- The norm form of the previous display: the per-cube `L^p` norm is a deterministic
head plus a tail obeying a `Gamma_2` bound whose scale carries the gain with
its exponent divided by `p`.  At `p = 4` this is the `3^{-(d/8)(Q.scale - m)}`
gain of the third term of `e.wave.influence.bound`, now available at every cube
rather than only at `cu_l`. -/
theorem cubeStreamIncrementLpNorm_head_tail_gain (M : ABKModel d) {p : ℝ}
    (hp : 1 ≤ p) {n m : ℤ} (hnm : n < m) (Q : TriadicCube d) :
    (∀ omega : ShellSeq d,
        cubeStreamIncrementLpNorm p Q n m omega ≤
          streamIncrementLpMassHead M p n m ^ p⁻¹ +
            cubeStreamIncrementLpTail M p Q n m omega ^ p⁻¹) ∧
      IndependentSums.IsBigOWith M.P.toMeasure (IndependentSums.gammaSigma 2)
        (fun omega : ShellSeq d => cubeStreamIncrementLpTail M p Q n m omega ^ p⁻¹)
        (streamIncrementLpGainScale M p Q.scale n m ^ p⁻¹) := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  obtain ⟨hnorm, htail⟩ := streamIncrementLpNorm_head_tail_gain M hp hnm Q.scale
  refine ⟨fun omega => ?_, ?_⟩
  · rw [cubeStreamIncrementLpNorm_eq_streamIncrementLpNorm_translate hp0]
    exact hnorm _
  · exact isBigOWith_comp_translateSequence M (triadicCubeShift Q)
      ((measurable_tail M hp0 Q.scale n m).pow_const _) htail

end

end Algsuperdiff.Section3.Provider.Stream
