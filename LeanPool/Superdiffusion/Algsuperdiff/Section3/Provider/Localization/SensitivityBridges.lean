/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.LambdaTransfer
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Localization.ResponseTransport
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.JCarrierRescale
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.CutoffLawTransport
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.IncrementLinftyNorm
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.WaveTranslation

/-!
# SensitivityBridges

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The bridge layer of the Section 3.6 sensitivity injection

It contains no estimate of the manuscript: every declaration below is either an
exact identity, an exact normalization, a carrier transport, or a monotone
comparison already proved elsewhere in the repository and re-read at the shape
the injection needs.

## The seams

** The zeroth-order unit-cube bridge.**  `IncrementBridge.lean` supplies
`gradientW1Infinity_shellFieldUnitCube_le`, the *first*-order half of the
frozen Section 2.4 gate.  The zeroth-order half -- the one the frozen
remainder's `h.w1Infinity` term needs -- existed only as a `private`
declaration,
`Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.w1Infinity_shellFieldUnitCube_le`
at `Provider/Diffusivity/ApproximateRecurrence/PrincipalResponseCentre.lean`,
and `private` in Lean 4 is file-scoped: the name is genuinely unreachable from
any other module (machine-checked: importing that module and referring to the
name fails with `unknown identifier`).  It is therefore re-proved here, in
public form, by exactly the route the private uses -- both components of
`UnitCubeSkewW2Infinity.w1Infinity` are `eLpNorm ... ∞` on the literal open
unit cube, so pointwise bounds transfer -- together with the raw-norm corollary
that mirrors `gradientW1Infinity_shellFieldUnitCube_le`.

** The zeroth-order twin of the two-index bridge.**  ABK26's
`e.good.local.events` gauge is measured on the rescaled unit cube; the proved
`gradientW1Infinity_incrementUnitCube₂_le`
(`Provider/BadEvents/IncrementGaugeTwoIndex.lean`) reads the *first*-order gate
through `cubeOscGauge`.  Its zeroth-order twin is supplied here.  The rescale
weights are exact and are the ones the manuscript's volume-normalized norms
carry (ABK26): for the map `y |-> z + 3^l y`,

```
  ‖rescaled‖_{L∞(square_0)}       =  ‖·‖_{L∞(z+square_l)}          (weight 1),
  ‖∇ rescaled‖_{L∞(square_0)}     =  3^l ‖∇·‖_{L∞(z+square_l)}     (weight 3^l),
```

so `w1Infinity` of the rescaled increment is `max { 3^l
‖∇(k_L-k_n)‖_{L∞(z+square_l)}, ‖k_L-k_n‖_{L∞(z+square_l)} }`.  Both sides are
carried here at the proved stream-level norms `Stream.localCubeDerivNorm` and
`Cutoff.localCubeControl`, and then at the two carriers the wave chain uses,
`Stream.streamIncrementLinftyNorm` and `Stream.cubeSupBound`.

** The rescale and gauge companions.**  The response at the localization cube
is the response at the *unit* cube of the rescaled and translated data.  The
translate half is the proved `ResponseTransport.lean` seam
(`responseJ_cutoffFamily_eq_originCube_translate`); the dilation half is
`Ch02.responseJ_dilate` at `Ch02.TriadicCoeffFamily.isDilation_dilate`.  Their
composition proves exactly on `BadEvents.unitRescaledCutoffCoeff`, the carrier
at which the frozen `responseJ_sensitivity` and the proved `lambda`-transfer
are both stated.  The `3^{4l}` is the *fingerprint* of these weights and is
exhibited here: with the volume-normalized norm

```
  ‖f‖_{W^{2,∞}(z+square_l)} = max { ‖∇²f‖_∞, 3^{-l}‖∇f‖_∞, 3^{-2l}‖f‖_∞ },
```

both frozen gate quantities of the rescaled increment are below
`3^{2l} ‖k_L-k_n‖_{W^{2,∞}(z+square_l)}`, hence both *squares* -- the two terms
of the frozen remainder -- are below
`3^{4l} ‖k_L-k_n‖²_{W^{2,∞}(z+square_l)}`.

A qualification on the norm.  ABK26 does **not** print a `W^{2,p}` definition:
the symbol `‖·‖_{W^{2,∞}}` is used but never defined.  The convention adopted
here is the one the wave lane states, in the equivalent `3^{2l}`-normalized
form `max{‖f‖_∞, 3^l‖∇f‖_∞, 3^{2l}‖∇²f‖_∞}`; see the fidelity-convention block
of `Provider/MultiscaleEstimate/WaveSizesZeroth.lean`.

(b) The `1/8 -> 3/8` gauge conversion.  The good event's ellipticity clause is
`lambda_{1/8,2}(z+square_l; a_n)` (`GoodLocalEvents.lean` carries it as the
binder `hlam`); the frozen sensitivity engine gates and prices at
`lambda_{3/8,2}` of the rescaled unit-cube field.  The *forward* comparison is
proved as `BadEvents.lambdaSq_le_unitCubeLambda_unitRescaledCutoffCoeff`
(`Provider/BadEvents/LambdaTransfer.lean`), proved from
`e.ellipticities.monotone.ordered` (ABK26) in the Section-3 face
`Provider/ErrorComparison/ExponentMonotonicity.lean` (`lambdaSq_mono_of_lt`).
What the *pricing* step consumes is the reciprocal direction: the frozen
remainder's weights `lambda_{3/8,2}^{-1}` and `lambda_{3/8,2}^{-2}` must be
replaced by the event's own `lambda_{1/8,2}^{-1}`.  That is supplied here, at
the literal observable and in the squared form the second remainder term
carries.

## Main definitions

* `Algsuperdiff.Section3.Provider.Localization.underlineW2Gauge`

## Main results

* `w1Infinity_shellFieldUnitCube_le`, `w1Infinity_shellFieldUnitCube_le_max`.
* `max_unitCubeValueNorm_cube`, `w1Infinity_cubeUnitCube_le`,
  `w1Infinity_incrementUnitCube₂_le`.
* (fingerprint) `underlineW2Gauge_nonneg`,
  `gradientW1Infinity_cubeUnitCube_le_underlineW2Gauge`,
  `w1Infinity_cubeUnitCube_le_underlineW2Gauge`,
  `gradientW1Infinity_sq_incrementUnitCube₂_le`,
  `w1Infinity_sq_incrementUnitCube₂_le`.
* `responseJ_cutoffFamily_eq_unitRescaledCutoffCoeff` (an orientation face of
  the proved `Multiscale.responseJ_unitRescaledCutoffCoeff`).
* `inv_unitCubeLambda_unitRescaledCutoffCoeff_le_inv_lambdaSq`,
  `inv_unitCubeLambda_le_inv_lambdaSq_oneEighth`,
  `inv_unitCubeLambda_sq_le_inv_lambdaSq_sq_oneEighth`.

## Name collisions

* `w1Infinity_incrementUnitCube₂_le` collides on the short name with
  `Algsuperdiff.Section3.Provider.Multiscale.w1Infinity_incrementUnitCube₂_le`.
  Same short name, same left-hand side
  `(incrementUnitCube₂ Q n L omega).w1Infinity`, different right-hand sides:
  that one bounds by `max (incrementOscGauge₂ Q n L omega)
  (cubeSupBound Q n L omega.1)`, the one here by the pair of raw scale-weighted
  cube norms.  The two namespaces are disjoint, so nothing is ambiguous as
  things stand; a consumer that opens both `...Provider.Localization` and
  `...Provider.Multiscale` will have to disambiguate.
* `dilateCube` is genuinely ambiguous in this file's scope --
  `Homogenization.Book.Ch02.dilateCube` versus
  `Algsuperdiff.Section3.Provider.Stream.dilateCube` -- and is therefore written
  `Ch02.dilateCube` throughout.  So is `MultiscaleExponent`
  (`Homogenization.MultiscaleExponent` versus `Ch02.MultiscaleExponent`).

## The wave lane's carrier, and how it relates to this one

* The wave lane's extended carrier `MultiscaleEstimate.waveGaugeW2` and this
  file's `underlineW2Gauge` are NOT the same normalization of the same object:
  - `waveGaugeW2 m h R` is a SUM,
    `cubeSupBound R (l-h) m + waveGauge l m h (cubeCenter R)`, at the `3^{2l}`
    normalization `‖f‖_∞ + 3^l‖∇f‖_∞ + 3^{2l}‖∇²f‖_∞`;
  - `underlineW2Gauge Q` is a MAX, at the reciprocal normalization
    `max{‖∇²f‖_∞, 3^{-l}‖∇f‖_∞, 3^{-2l}‖f‖_∞}`, and is at the suprema
    throughout.
  The bridge that the injection will eventually need,
  `3 ^ (2 * Q.scale) * underlineW2Gauge Q (shellIncrement omega n L)
     ≤ waveGaugeW2 L h Q omega`,
  is not carried out in this module.  It is proved, at the constant `1`, as
  `LambdaGateChain.three_zpow_mul_underlineW2Gauge_le_waveGaugeW2` (with its
  squared form `three_zpow_mul_underlineW2Gauge_sq_le_waveGaugeW2_sq`, which is
  the shape the injection remainder meets).
  No passage from a pointwise fidelity statement to the three suprema is
  needed: `waveGauge`'s own summands are already at the suprema.  They are
  `Stream.localCubeDerivNorm` and `Stream.localCubeSecondDerivNorm`, which are
  by definition the exact `L∞` norms on the open cube.  The route is layer
  subadditivity of those exact gauges (`Stream.localCubeDerivNorm_sum_le`,
  `Stream.localCubeSecondDerivNorm_sum_le`) applied to
  `shellIncrement = ShellField.sum (Ioc (l-h) m)`, and it costs the constant
  exactly `1`.

## References

* ABK26: the only volume-normalized Sobolev norm the manuscript defines is
  `W^{1,p}`, as `(‖∇f‖^p_{L^p} + |U|^{-p/d}‖f‖^p_{L^p})^{1/p}`, i.e.
  `max{‖∇f‖, |U|^{-1/d}‖f‖}` at `p = ∞`.  That display is what fixes the
  weights used here; the `W^{2,∞}` symbol is used but never defined.
* ABK26, `e.ellipticities.monotone.ordered`.
* ABK26, `l.J.sensitivity`, stated at `square_0`.
* ABK26, `e.good.local.events`.
* ABK26, the gauge pricing `e.J.sensitivity.apppp` at `delta = 1`, with the
  `3^{4l}`.
-/

namespace Algsuperdiff.Section3.Provider.Localization

-- `_root_` is here, not presently load-bearing.
-- `Algsuperdiff.Section3.Provider.Homogenization` is a live sibling namespace, and a
-- bare `open Homogenization` resolves to it as soon as any `Provider.Homogenization`
-- module enters this file's import closure.  Measured both ways: the current closure
-- has Z such modules and the bare open elaborates; with `import Algsuperdiff.Section3`
-- in front of this same body it fails at once (`Unknown identifier Vec`.).
-- See the "Namespace hazards" block of the module docstring.
open _root_.MeasureTheory
open _root_.HCPolySupport _root_.HCPolySupport.Book _root_.HCPolySupport.Book.Ch02
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Frozen.Section24
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section3.Provider.Stream
open scoped BigOperators ENNReal Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-! ## The zeroth-order unit-cube bridge -/

/-- A pointwise bound on the literal open unit cube bounds the `L∞` seminorm
that the frozen Section 2.4 carriers read. -/
private theorem toReal_eLpNorm_unitCube_le {f : Vec d → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x ∈ openCubeSet (originCube d 0), ‖f x‖ ≤ C) :
    (eLpNorm f ∞
      (volumeMeasureOn
        ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))).toReal ≤ C := by
  exact Algsuperdiff.Section3.Provider.BadEvents.toReal_eLpNorm_unitCube_le hC hbound

/-- **Pointwise bounds on the literal open unit cube bound the frozen
zeroth-order gate `UnitCubeSkewW2Infinity.w1Infinity`.**

Both components of `w1Infinity` are essential suprema on the open unit cube, so
a pointwise bound `A` on the stored derivative and a pointwise bound `B` on the
value transfer to `max A B`.

This is the public re-proof of the unreachable `private`
`w1Infinity_shellFieldUnitCube_le` of
`Provider/Diffusivity/ApproximateRecurrence/PrincipalResponseCentre.lean`, by
that private's own route.

: the statement holds only under the propositions supplied by its binders `hA`,
`hB`, `hderiv` and `hval`.  It is a provider A, not a source-facing frozen
declaration. -/
theorem w1Infinity_shellFieldUnitCube_le (g : ShellField d) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hderiv : ∀ y ∈ openCubeSet (originCube d 0),
      ShellField.matrixDerivativeNorm (ShellField.deriv g y) ≤ A)
    (hval : ∀ y ∈ openCubeSet (originCube d 0), matrixNorm (g y) ≤ B) :
    (shellFieldUnitCube g).w1Infinity ≤ max A B := by
  rw [UnitCubeSkewW2Infinity.w1Infinity]
  refine max_le_max ?_ ?_
  · refine toReal_eLpNorm_unitCube_le hA fun y hy => ?_
    have hfrozen : Algsuperdiff.Frozen.Section24.matrixDerivativeNorm
        ((shellFieldUnitCube g).firstDeriv y) =
        ShellField.matrixDerivativeNorm (ShellField.deriv g y) := by
      rw [shellFieldUnitCube_firstDeriv, frozen_matrixDerivativeNorm_eq]
    rw [Real.norm_eq_abs, hfrozen,
      abs_of_nonneg (ShellField.matrixDerivativeNorm_nonneg _)]
    exact hderiv y hy
  · refine toReal_eLpNorm_unitCube_le hB fun y hy => ?_
    rw [Real.norm_eq_abs, shellFieldUnitCube_value,
      abs_of_nonneg (matrixNorm_nonneg _)]
    exact hval y hy

/-- **The zeroth-order gate of a shell field's unit-cube package is below the
raw unit-cube gauges of the shell field.**  This is the exact zeroth-order twin
of `BadEvents.gradientW1Infinity_shellFieldUnitCube_le`: the derivative gauge
replaces the second-derivative gauge and the value gauge replaces the derivative
gauge. -/
theorem w1Infinity_shellFieldUnitCube_le_max (g : ShellField d) :
    (shellFieldUnitCube g).w1Infinity ≤
      max (ShellField.unitCubeDerivNorm g) (ShellField.unitCubeValueNorm g) :=
  w1Infinity_shellFieldUnitCube_le g (ShellField.unitCubeDerivNorm_nonneg g)
    (ShellField.unitCubeValueNorm_nonneg g)
    (fun _ hy => matrixDerivativeNorm_deriv_le_unitCubeDerivNorm g hy)
    (fun y hy => by
      rw [matrixNorm_eq_matrixOperatorNorm]
      exact ShellField.matrixOperatorNorm_apply_le_unitCubeValueNorm g ⟨y, hy⟩)

/-! ## The zeroth-order twin of the two-index unit-cube bridge -/

/-- **The exact zeroth-order normalization.**  The unit-cube derivative and
value gauges of the field rescaled by `y |-> z + 3^l y` are the `3^l`- and
`1`-weighted cube gauges of the field on `z + square_l`.

This is the zeroth-order twin of `BadEvents.max_unitCubeDerivNorm_cube`; the
weights are the ones ABK26's volume-normalized norms carry. -/
theorem max_unitCubeValueNorm_cube (Q : TriadicCube d) (h : ShellField d) :
    max
        (ShellField.unitCubeDerivNorm
          (ShellField.spatialScale ((3 : ℝ) ^ Q.scale)
            (ShellField.translate (cubeBasePoint Q) h)))
        (ShellField.unitCubeValueNorm
          (ShellField.spatialScale ((3 : ℝ) ^ Q.scale)
            (ShellField.translate (cubeBasePoint Q) h))) =
      max
        ((3 : ℝ) ^ Q.scale *
          localCubeDerivNorm Q.scale (ShellField.translate (cubeBasePoint Q) h))
        (localCubeControl Q.scale (ShellField.translate (cubeBasePoint Q) h)) := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ Q.scale := zpow_pos (by norm_num) _
  have hfirst : ShellField.unitCubeDerivNorm
      (ShellField.spatialScale ((3 : ℝ) ^ Q.scale)
        (ShellField.translate (cubeBasePoint Q) h)) =
      (3 : ℝ) ^ Q.scale *
        localCubeDerivNorm Q.scale (ShellField.translate (cubeBasePoint Q) h) := by
    rw [localCubeDerivNorm, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt h3), one_mul]
  have hvalue : ShellField.unitCubeValueNorm
      (ShellField.spatialScale ((3 : ℝ) ^ Q.scale)
        (ShellField.translate (cubeBasePoint Q) h)) =
      localCubeControl Q.scale (ShellField.translate (cubeBasePoint Q) h) := by
    rw [localCubeControl, cubeScaleFactor_originCube]
  rw [hfirst, hvalue]

/-- **The zeroth-order bridge at an arbitrary shell field.**  The frozen
zeroth-order gate of the field rescaled from `z + square_l` to the unit cube is
below the scale-weighted cube norms `max { 3^l ‖∇h‖_{L∞(z+square_l)},
‖h‖_{L∞(z+square_l)} }`. -/
theorem w1Infinity_cubeUnitCube_le (Q : TriadicCube d) (h : ShellField d) :
    (cubeUnitCube Q h).w1Infinity ≤
      max
        ((3 : ℝ) ^ Q.scale *
          localCubeDerivNorm Q.scale (ShellField.translate (cubeBasePoint Q) h))
        (localCubeControl Q.scale (ShellField.translate (cubeBasePoint Q) h)) := by
  rw [cubeUnitCube, ← max_unitCubeValueNorm_cube Q h]
  exact w1Infinity_shellFieldUnitCube_le_max _

/-! ## (fingerprint) The `3^{4l}` weight -/

/-- The manuscript's volume-normalized `W^{2,∞}` gauge of a shell field on the
localization cube `z + square_l` (ABK26, read at `p = ∞` and `|U|^{1/d} =
3^l`):

```
  ‖h‖_{W^{2,∞}(z+square_l)} = max { ‖∇²h‖_∞, 3^{-l}‖∇h‖_∞, 3^{-2l}‖h‖_∞ } .
```
-/
def underlineW2Gauge (Q : TriadicCube d) (h : ShellField d) : ℝ :=
  max
    (localCubeSecondDerivNorm Q.scale (ShellField.translate (cubeBasePoint Q) h))
    (max
      (((3 : ℝ) ^ Q.scale)⁻¹ *
        localCubeDerivNorm Q.scale (ShellField.translate (cubeBasePoint Q) h))
      ((((3 : ℝ) ^ Q.scale)⁻¹) ^ 2 *
        localCubeControl Q.scale (ShellField.translate (cubeBasePoint Q) h)))

theorem underlineW2Gauge_nonneg (Q : TriadicCube d) (h : ShellField d) :
    0 ≤ underlineW2Gauge Q h := by
  refine le_max_of_le_left ?_
  exact localCubeSecondDerivNorm_nonneg _ _

/-- The first-order gate of the rescaled field is `3^{2l}` times the
manuscript's `W^{2,∞}` gauge, at worst. -/
theorem gradientW1Infinity_cubeUnitCube_le_underlineW2Gauge (Q : TriadicCube d)
    (h : ShellField d) :
    (cubeUnitCube Q h).gradientW1Infinity ≤
      (3 : ℝ) ^ (2 * Q.scale) * underlineW2Gauge Q h := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ Q.scale := zpow_pos (by norm_num) _
  have hsq : (3 : ℝ) ^ (2 * Q.scale) = ((3 : ℝ) ^ Q.scale) ^ 2 := by
    rw [two_mul, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), sq]
  refine (gradientW1Infinity_cubeUnitCube_le Q h).trans ?_
  rw [cubeOscGauge]
  refine max_le ?_ ?_
  · refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact le_max_left _ _
  · have hstep : (3 : ℝ) ^ Q.scale *
        localCubeDerivNorm Q.scale (ShellField.translate (cubeBasePoint Q) h) =
        (3 : ℝ) ^ (2 * Q.scale) *
          (((3 : ℝ) ^ Q.scale)⁻¹ *
            localCubeDerivNorm Q.scale
              (ShellField.translate (cubeBasePoint Q) h)) := by
      rw [hsq]
      field_simp
    rw [hstep]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact le_max_of_le_right (le_max_left _ _)

/-- The zeroth-order gate of the rescaled field is `3^{2l}` times the manuscript's
`W^{2,∞}` gauge, at worst.  Together with the first-order twin this is the
source of the `3^{4l}`: the frozen remainder carries the *squares* of these two
quantities. -/
theorem w1Infinity_cubeUnitCube_le_underlineW2Gauge (Q : TriadicCube d)
    (h : ShellField d) :
    (cubeUnitCube Q h).w1Infinity ≤
      (3 : ℝ) ^ (2 * Q.scale) * underlineW2Gauge Q h := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ Q.scale := zpow_pos (by norm_num) _
  have hsq : (3 : ℝ) ^ (2 * Q.scale) = ((3 : ℝ) ^ Q.scale) ^ 2 := by
    rw [two_mul, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), sq]
  refine (w1Infinity_cubeUnitCube_le Q h).trans ?_
  refine max_le ?_ ?_
  · have hstep : (3 : ℝ) ^ Q.scale *
        localCubeDerivNorm Q.scale (ShellField.translate (cubeBasePoint Q) h) =
        (3 : ℝ) ^ (2 * Q.scale) *
          (((3 : ℝ) ^ Q.scale)⁻¹ *
            localCubeDerivNorm Q.scale
              (ShellField.translate (cubeBasePoint Q) h)) := by
      rw [hsq]
      field_simp
    rw [hstep]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact le_max_of_le_right (le_max_left _ _)
  · have hstep : localCubeControl Q.scale
        (ShellField.translate (cubeBasePoint Q) h) =
        (3 : ℝ) ^ (2 * Q.scale) *
          ((((3 : ℝ) ^ Q.scale)⁻¹) ^ 2 *
            localCubeControl Q.scale (ShellField.translate (cubeBasePoint Q) h)) := by
      rw [hsq]
      field_simp
    rw [hstep]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact le_max_of_le_right (le_max_right _ _)

/-- **The `3^{4l}` fingerprint, first-order term.**  The square of the frozen
first-order gate quantity of the rescaled increment -- the quantity multiplying
`|p . q|` in the frozen remainder -- is below
`3^{4l} ‖k_L - k_n‖²_{W^{2,∞}(z+square_l)}`. -/
theorem gradientW1Infinity_sq_incrementUnitCube₂_le (Q : TriadicCube d) (n L : ℤ)
    (omega : CutoffSample d) :
    (incrementUnitCube₂ Q n L omega).gradientW1Infinity ^ 2 ≤
      (3 : ℝ) ^ (4 * Q.scale) *
        underlineW2Gauge Q (shellIncrement omega.1 n L) ^ 2 := by
  have hbase := gradientW1Infinity_cubeUnitCube_le_underlineW2Gauge Q
    (shellIncrement omega.1 n L)
  have hnn : (0 : ℝ) ≤ (incrementUnitCube₂ Q n L omega).gradientW1Infinity :=
    Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Lipschitz.gradientW1Infinity_nonneg _
  have hsq : (3 : ℝ) ^ (4 * Q.scale) = ((3 : ℝ) ^ (2 * Q.scale)) ^ 2 := by
    rw [show (4 : ℤ) * Q.scale = 2 * Q.scale + 2 * Q.scale by ring,
      zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), sq]
  rw [hsq, ← mul_pow]
  exact pow_le_pow_left₀ hnn hbase 2

/-- **The `3^{4l}` fingerprint, zeroth-order term.**  The square of the frozen
zeroth-order gate quantity of the rescaled increment -- the quantity multiplying
`|p|²` in the frozen remainder -- is below
`3^{4l} ‖k_L - k_n‖²_{W^{2,∞}(z+square_l)}`. -/
theorem w1Infinity_sq_incrementUnitCube₂_le (Q : TriadicCube d) (n L : ℤ)
    (omega : CutoffSample d) :
    (incrementUnitCube₂ Q n L omega).w1Infinity ^ 2 ≤
      (3 : ℝ) ^ (4 * Q.scale) *
        underlineW2Gauge Q (shellIncrement omega.1 n L) ^ 2 := by
  have hbase := w1Infinity_cubeUnitCube_le_underlineW2Gauge Q
    (shellIncrement omega.1 n L)
  have hnn : (0 : ℝ) ≤ (incrementUnitCube₂ Q n L omega).w1Infinity :=
    Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Lipschitz.w1Infinity_nonneg _
  have hsq : (3 : ℝ) ^ (4 * Q.scale) = ((3 : ℝ) ^ (2 * Q.scale)) ^ 2 := by
    rw [show (4 : ℤ) * Q.scale = 2 * Q.scale + 2 * Q.scale by ring,
      zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), sq]
  rw [hsq, ← mul_pow]
  exact pow_le_pow_left₀ hnn hbase 2

/-! ## The rescale companion: from `z + square_l` to the unit cube -/

/-- ** The composed rescale companion.**  The demanded response of the cutoff
family at an arbitrary triadic cube `R = z + square_l`, at an arbitrary
coefficient scale `L` and arbitrary loads `p`, `q`, is the response at the
*unit* cube of the rescaled and translated data --
`BadEvents.unitRescaledCutoffCoeff`, which is exactly the carrier at which the
frozen `responseJ_sensitivity` and the proved `lambda`-transfer are both
stated.

Both halves are exact identities, so no constant is created: the manuscript's
dimension-only `C` is untouched by the transport, and the whole scale
bookkeeping sits in the `3^{4l}` fingerprint proved above, not here. -/
theorem responseJ_cutoffFamily_eq_unitRescaledCutoffCoeff (M : ABKModel d)
    (L : ℤ) (R : TriadicCube d) (p q : Vec d) (omega : CutoffSample d) :
    responseJ (cubeDomain R)
        ((coefficientCutoffTriadicCoeffFamily M L omega).coeffOn R) p q =
      responseJ (cubeDomain (originCube d 0))
        (unitRescaledCutoffCoeff M R L omega) p q :=
  (Multiscale.responseJ_unitRescaledCutoffCoeff M R L p q omega).symm

/-! ## The `1/8 -> 3/8` gauge conversion -/

/-- **The reciprocal gauge conversion, in general form.**  For `0 < t < s` and
admissible `q`, the frozen unit-cube weight `lambda_{s,q}^{-1}` of the rescaled
coefficient object is below the manuscript's own
`lambda_{t,q}^{-1}(z + square_l; a_n)`.

This is the reciprocal of the proved forward comparison
`BadEvents.lambdaSq_le_unitCubeLambda_unitRescaledCutoffCoeff`
(`e.ellipticities.monotone.ordered`, ABK26, composed with the
translation-and-dilation covariance of `lambda_{s,q}`); the reciprocal
direction is legitimate because `Ch02.lambdaSq` is strictly positive for every
coefficient family. -/
theorem inv_unitCubeLambda_unitRescaledCutoffCoeff_le_inv_lambdaSq (M : ABKModel d)
    (Q : TriadicCube d) (n : ℤ) {t s : ℝ} {q : Ch02.MultiscaleExponent}
    (ht : 0 < t) (hts : t < s) (hq : q.IsAdmissible) (omega : CutoffSample d) :
    (unitCubeLambda s q (unitRescaledCutoffCoeff M Q n omega))⁻¹ ≤
      (lambdaSq Q t q (coefficientCutoffTriadicCoeffFamily M n omega))⁻¹ := by
  let : NeZero d := neZero_of_abkModel M
  exact inv_anti₀ (lambdaSq_pos Q (coefficientCutoffTriadicCoeffFamily M n omega) ht hq)
    (lambdaSq_le_unitCubeLambda_unitRescaledCutoffCoeff M Q n ht hts hq omega)

/-- **The gauge conversion at the manuscript's own exponents.**  The frozen
engine's weight `lambda_{3/8,2}^{-1}` is below the good event's own
`lambda_{1/8,2}^{-1}(z + square_l; a_n)`, at the literal multiscale
observable. -/
theorem inv_unitCubeLambda_le_inv_lambdaSq_oneEighth (M : ABKModel d)
    (Q : TriadicCube d) (n : ℤ) (omega : CutoffSample d) :
    (unitCubeLambda (3 / 8) (.finite 2) (unitRescaledCutoffCoeff M Q n omega))⁻¹ ≤
      (lambdaSq Q (1 / 8) (.finite 2)
        (coefficientCutoffTriadicCoeffFamily M n omega))⁻¹ :=
  inv_unitCubeLambda_unitRescaledCutoffCoeff_le_inv_lambdaSq M Q n
    (t := 1 / 8) (s := 3 / 8) (q := .finite 2) (by norm_num) (by norm_num)
    (by norm_num) omega

/-- The squared form of the gauge conversion, which is what the second term of
the frozen remainder (`|p . q| * gradientW1Infinity² * lambda^{-2}`) carries. -/
theorem inv_unitCubeLambda_sq_le_inv_lambdaSq_sq_oneEighth (M : ABKModel d)
    (Q : TriadicCube d) (n : ℤ) (omega : CutoffSample d) :
    (unitCubeLambda (3 / 8) (.finite 2)
        (unitRescaledCutoffCoeff M Q n omega))⁻¹ ^ 2 ≤
      (lambdaSq Q (1 / 8) (.finite 2)
        (coefficientCutoffTriadicCoeffFamily M n omega))⁻¹ ^ 2 := by
  let : NeZero d := neZero_of_abkModel M
  refine pow_le_pow_left₀ ?_ (inv_unitCubeLambda_le_inv_lambdaSq_oneEighth M Q n omega) 2
  refine inv_nonneg.2 ?_
  rw [unitCubeLambda_unitRescaledCutoffCoeff]
  exact (lambdaSq_pos Q (coefficientCutoffTriadicCoeffFamily M n omega)
    (by norm_num) (by norm_num)).le

end

end Algsuperdiff.Section3.Provider.Localization
