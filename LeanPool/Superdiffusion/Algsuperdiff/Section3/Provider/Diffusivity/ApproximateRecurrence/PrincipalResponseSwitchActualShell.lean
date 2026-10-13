/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseSwitchTransport
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseShellAverage

/-!
# PrincipalResponseSwitchActualShell

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Provider: the centered fresh shell `h - (h)_{z+cu_n}` at the frozen `W^{2,∞}` carrier

Source displays in ABK26:

* `l.approximate.recurrence.formula` (label), Step 3;
* the gauge-switch chain of Step 3, whose first line conjugates by the doubled
  shear of `e.Gh.def` and replaces `a_m` by `a_m - (h)_{z+cu_n}`;
* `e.good.local.events` (label; display);
* the fresh shell `h := k_m - k_{m-h}` named.

## What this module supplies

`ApproximateRecurrence.PrincipalResponseSwitchTransport` transports the
gauge-switch chain to the manuscript's cube `z + cu_n`, but every one of its
statements carries the *centered* shell `h - (h)_{z+cu_n}` as an abstract
`Algsuperdiff.Frozen.Section24.UnitCubeSkewW2Infinity d` argument `hfield`
together with two binders about it:

* `hshift`, the pointwise field decomposition at the rescaled unit cube;
* `hgrad`, the discounted gradient gate.

No constructor for that centered object existed in this repository: the proved
`Provider.BadEvents.incrementUnitCube₂` is the *uncentered* rescaled increment,
and the proved identification of the rescaled coefficient fields
(`Provider.BadEvents.unitRescaledCutoffCoeff_toCoeffField_ae_eq`) is an
almost-everywhere statement, while `hshift` is quantified over every point.

This module builds the constructor and produces both binders.

### The construction

The frozen carrier `UnitCubeSkewW2Infinity d` stores a value field together
with *separately stored* first and second derivative fields, and every
structural obligation on the value field (`MemLp ∞`, skewness, and
`HasWeakPartialDerivOn`) is an almost-everywhere or distributional statement on
the open unit cube.  Consequently the value field may be replaced by any
almost-everywhere equal field without touching the derivative data.  That is
`unitCubeSkewW2InfinityOfAEEq`.

The centered shell is then built in two steps.

1. `subConstShell` subtracts a constant antisymmetric matrix from a shell
   field.  A shell field is a triple (value, first derivative, second
   derivative) with the two `HasFDerivAt` links and pointwise antisymmetry; subtracting
   a constant changes only the value, so the derivative data -- and therefore
   `cubeOscGauge`, `unitCubeDerivNorm`, `unitCubeSecondDerivNorm` and
   `UnitCubeSkewW2Infinity.gradientW1Infinity` -- are unchanged
   *definitionally*.
2. `centeredShellUnitCube` replaces the value field of
   `cubeUnitCube Q (subConstShell hbar _ (shellIncrement omega lowScale highScale))`
   by the literal difference
   ```
   x  |->  a_hi^resc(x) - a_lo^resc(x) - hbar
   ```
   of the two rescaled coefficient objects.  The replacement is legitimate
   because the two fields agree almost everywhere on the open unit cube, by the
   proved `unitRescaledCutoffCoeff_toCoeffField_ae_eq` at both scales together
   with `shellIncrement_apply_eq_cutoff_sub`.

Because the value field is now *literally* that difference, the binder `hshift`
becomes finite algebra on the coefficient carrier: `perturbCoeffOn` adds
`t • h` to the base field pointwise, so at `t = 1` the required identity is
`a_lo + (a_hi - a_lo - hbar) = a_hi - hbar`.

## What is produced here, and what is not

Produced, unconditionally:

* `centeredShellUnitCube_shift` -- the binder `hshift` of every statement of
  `PrincipalResponseSwitchTransport`, for every point;
* `centeredShellUnitCube_gradientW1Infinity` -- the binder `hgrad`'s carrier
  identification: the centered shell's gradient gauge *is* the uncentered
  rescaled increment's, by `rfl`.

Produced, almost surely on the cutoff sample law:

* `responseSensitivityConst_mul_gradientW1Infinity_centeredShell_le_ae` -- the
  binder `hgrad` itself, at `Delta = 3^{-(1/4)(m-h-n)_+}`, from membership in
  `Provider.BadEvents.goodLocalEvent` alone.  It is the proved
  `responseSensitivityConst_mul_gradientW1Infinity_le_of_mem_goodLocalEvent_ae`
  with its `hcentered` binder discharged by the `rfl` identification above.

NOT produced here: the shell-size binder `hshell`, which is the subject of
`PrincipalResponseSwitchActualShellSize`.

## Carriers

* The localization cube is a free `TriadicCube d`; the manuscript's `n = m - h
  - 16 ceil|log_3 gamma|` (`e.recurrence.params`, label) is never hard-coded.
* The two scales are free integers `lowScale <= highScale`; in Step 3 they are
  `m - h` and `m`.
* The constant `hbar` is a free antisymmetric `Mat d`.  The manuscript's own
  `(h)_{z+cu_n}` is `ApproximateRecurrence.freshShellCubeAverage`, whose
  antisymmetry is the proved `freshShellCubeAverage_skew`; the specialization
  is `centeredFreshShellUnitCube`.
* `cstar` does not occur in this module.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Frozen.Section24
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section3.Provider.Stream
open scoped Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-! ## Weak partial derivatives are insensitive to the representative

`Homogenization.HasWeakPartialDerivOn U i u g` is a family of integral
identities in `u`, so it only sees `u` through its class modulo null sets of
`volume.restrict U`.  CoarseGraining exports the `EqOn` version of this fact
privately in two files; the almost-everywhere version is proved here, in
portable style. -/

/-- Weak partial derivatives are unchanged when the function is modified on a
null set of the restricted volume measure.

Unconditional: no caller-supplied proposition enters. -/
theorem hasWeakPartialDerivOn_congr_ae {U : Set (Vec d)} {i : Fin d}
    {u v g : Vec d → ℝ} (huv : u =ᵐ[volumeMeasureOn U] v)
    (hu : HasWeakPartialDerivOn U i u g) : HasWeakPartialDerivOn U i v g := by
  intro φ hφ hcs hsub
  rw [← hu φ hφ hcs hsub]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [huv] with x hx
  rw [hx]

/-! ## Replacing the value field of a frozen unit-cube `W^{2,∞}` object -/

/-- **Representative change at the frozen `W^{2,∞}` carrier.**  Given a frozen
unit-cube object `h` and any coefficient field `w` that agrees with the value
field of `h` almost everywhere on the open unit cube, this is the frozen object
whose value field is *literally* `w` and whose first and second derivative
fields are those of `h`.

Every structural field of `UnitCubeSkewW2Infinity` that mentions the value is
an almost-everywhere or distributional statement on the open unit cube
(`MemLp ∞`, the skewness of the symmetric part, and `HasWeakPartialDerivOn`),
so all of them transfer.

: this statement holds only under the proposition supplied by its binder `hw`,
the almost-everywhere agreement of the two value fields.  It is a provider A,
not a source-facing frozen declaration. -/
def unitCubeSkewW2InfinityOfAEEq (h : UnitCubeSkewW2Infinity d) (w : CoeffField d)
    (hw : w =ᵐ[volumeMeasureOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d))]
      h.toLInfSkewMatrixFieldOn.1.1) :
    UnitCubeSkewW2Infinity d where
  toLInfSkewMatrixFieldOn :=
    ⟨⟨w, fun i j => (h.toLInfSkewMatrixFieldOn.1.2 i j).ae_eq
        (by filter_upwards [hw] with x hx; rw [hx])⟩, by
      filter_upwards [hw, h.toLInfSkewMatrixFieldOn.2] with x hx hskew
      rw [hx]
      exact hskew⟩
  firstDeriv := h.firstDeriv
  secondDeriv := h.secondDeriv
  firstDeriv_memLp := h.firstDeriv_memLp
  secondDeriv_memLp := h.secondDeriv_memLp
  hasWeakPartialDeriv_value := fun k i j =>
    hasWeakPartialDerivOn_congr_ae
      (u := fun x => h.toLInfSkewMatrixFieldOn.1.1 x i j)
      (by filter_upwards [hw] with x hx; rw [hx])
      (h.hasWeakPartialDeriv_value k i j)
  hasWeakPartialDeriv_firstDeriv := h.hasWeakPartialDeriv_firstDeriv

/-- The representative change does not move the value gauge either: the frozen
`w1Infinity` reads the value field only through an essential supremum. -/
theorem unitCubeSkewW2InfinityOfAEEq_w1Infinity (h : UnitCubeSkewW2Infinity d)
    (w : CoeffField d)
    (hw : w =ᵐ[volumeMeasureOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d))]
      h.toLInfSkewMatrixFieldOn.1.1) :
    (unitCubeSkewW2InfinityOfAEEq h w hw).w1Infinity = h.w1Infinity := by
  simp only [UnitCubeSkewW2Infinity.w1Infinity]
  refine congrArg₂ max rfl (congrArg ENNReal.toReal ?_)
  refine MeasureTheory.eLpNorm_congr_ae ?_
  filter_upwards [hw] with x hx
  change matrixNorm (w x) = matrixNorm (h.toLInfSkewMatrixFieldOn.1.1 x)
  rw [hx]

/-! ## Subtracting a constant antisymmetric matrix from a shell field -/

/-- **The constant shift of a shell field.**  A shell field is a triple (value,
first derivative, second derivative) subject to two `HasFDerivAt` links and pointwise
antisymmetry; subtracting a constant antisymmetric matrix changes only the
value, and preserves all three conditions.

: this statement holds only under the proposition supplied by its binder `hc`,
the antisymmetry of the constant.  It is a provider A, not a source-facing
frozen declaration. -/
def subConstShell (c : Mat d) (hc : matTranspose c = -c) (g : ShellField d) :
    ShellField d :=
  ⟨(g.1.1 - ContinuousMap.const (Vec d) c, g.1.2), by
    refine ⟨?_, g.2.2.1, ?_⟩
    · intro x
      have hfun : (⇑(g.1.1 - ContinuousMap.const (Vec d) c) : Vec d → Mat d) =
          fun y => g y - c := by
        funext y
        simp
      rw [hfun]
      exact (g.hasFDerivAt x).sub_const c
    · intro x i j
      have hg := g.skew_entry x i j
      have hcij : c i j = -c j i := by
        have h := congrFun (congrFun hc j) i
        simpa [matTranspose] using h
      change g x i j - c i j = -(g x j i - c j i)
      rw [hg, hcij]
      ring⟩

@[simp]
theorem subConstShell_apply (c : Mat d) (hc : matTranspose c = -c) (g : ShellField d)
    (x : Vec d) : subConstShell c hc g x = g x - c :=
  rfl

@[simp]
theorem subConstShell_deriv (c : Mat d) (hc : matTranspose c = -c) (g : ShellField d)
    (x : Vec d) :
    ShellField.deriv (subConstShell c hc g) x = ShellField.deriv g x :=
  rfl

/-- The constant shift is invisible to the manuscript's oscillation gauge
`3^{2j} ||grad h||_{W^{1,infinity}(z+square_j)}`, which reads derivatives only. -/
@[simp]
theorem cubeOscGauge_subConstShell (Q : TriadicCube d) (c : Mat d)
    (hc : matTranspose c = -c) (g : ShellField d) :
    cubeOscGauge Q (subConstShell c hc g) = cubeOscGauge Q g :=
  rfl

/-! ## The centered fresh shell at the rescaled unit cube -/

/-- The rescaled centered shell as a *shell field*: `h - hbar` transported to
the unit cube by the manuscript's map `y |-> z + 3^j y`. -/
def centeredShellField (Q : TriadicCube d) (lowScale highScale : ℤ)
    (omega : CutoffSample d) (hbar : Mat d) (hskew : matTranspose hbar = -hbar) :
    UnitCubeSkewW2Infinity d :=
  cubeUnitCube Q (subConstShell hbar hskew (shellIncrement omega.1 lowScale highScale))

@[simp]
theorem centeredShellField_value (Q : TriadicCube d) (lowScale highScale : ℤ)
    (omega : CutoffSample d) (hbar : Mat d) (hskew : matTranspose hbar = -hbar)
    (y : Vec d) :
    (centeredShellField Q lowScale highScale omega hbar
      hskew).toLInfSkewMatrixFieldOn.1.1 y =
      shellIncrement omega.1 lowScale highScale
          (((3 : ℝ) ^ Q.scale) • y + cubeBasePoint Q) - hbar :=
  rfl

/-- The almost-everywhere identification of the rescaled coefficient-field
difference with the rescaled centered shell, on the open unit cube.

This is the two-scale form of the proved
`Provider.BadEvents.unitRescaledCutoffCoeff_toCoeffField_ae_eq`: the constant
`nu I` of `a_m = nu I + k_m` cancels in the difference, leaving the literal
increment `k_{highScale} - k_{lowScale}`.

: this statement holds only under the proposition supplied by its binder `hle`,
the manuscript's `m - h <= m`.  It is a provider A, not a source-facing frozen
declaration. -/
theorem centeredShellField_toCoeffField_sub_ae_eq (M : ABKModel d)
    (Q : TriadicCube d) {lowScale highScale : ℤ} (hle : lowScale ≤ highScale)
    (omega : CutoffSample d) (hbar : Mat d) (hskew : matTranspose hbar = -hbar) :
    (fun x : Vec d =>
        (unitRescaledCutoffCoeff M Q highScale omega).toCoeffField x -
          (unitRescaledCutoffCoeff M Q lowScale omega).toCoeffField x - hbar)
      =ᵐ[volumeMeasureOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d))]
    (centeredShellField Q lowScale highScale omega hbar
      hskew).toLInfSkewMatrixFieldOn.1.1 := by
  filter_upwards [unitRescaledCutoffCoeff_toCoeffField_ae_eq M Q highScale omega,
    unitRescaledCutoffCoeff_toCoeffField_ae_eq M Q lowScale omega] with x hhi hlo
  rw [centeredShellField_value, hhi, hlo,
    shellIncrement_apply_eq_cutoff_sub omega hle, cubeBasePoint_eq_triadicCubeShift,
    coefficientCutoff_apply, coefficientCutoff_apply]
  abel

/-- **The centered fresh shell `h - hbar` at the frozen `W^{2,∞}` carrier.**

Its value field is *literally* the difference of the two rescaled coefficient
objects of `PrincipalResponseSwitchTransport`, shifted by `hbar`; its stored
derivative fields are those of the rescaled literal increment.  The first
property makes `hshift` a pointwise identity; the second makes the frozen
gradient gauge equal to that of the uncentered increment.

: this statement holds only under the propositions supplied by its binders --
`hskew` (antisymmetry of the centering constant) and `hle` (`m - h <= m`).  It
is a provider A, not a source-facing frozen declaration. -/
def centeredShellUnitCube (M : ABKModel d) (Q : TriadicCube d)
    {lowScale highScale : ℤ} (hle : lowScale ≤ highScale) (omega : CutoffSample d)
    (hbar : Mat d) (hskew : matTranspose hbar = -hbar) :
    UnitCubeSkewW2Infinity d :=
  unitCubeSkewW2InfinityOfAEEq
    (centeredShellField Q lowScale highScale omega hbar hskew)
    (fun x => (unitRescaledCutoffCoeff M Q highScale omega).toCoeffField x -
      (unitRescaledCutoffCoeff M Q lowScale omega).toCoeffField x - hbar)
    (centeredShellField_toCoeffField_sub_ae_eq M Q hle omega hbar hskew)

/-! ## The first caller binder: `hshift` -/

/-- **The binder `hshift` of `PrincipalResponseSwitchTransport`, produced.**

The manuscript's own field decomposition at the rescaled unit-cube carrier,

```
a_{m-h}(z + 3^n .) + (h - (h)_{z+cu_n})  =  a_m(z + 3^n .) - (h)_{z+cu_n} ,
```

holds at *every* point, not merely almost everywhere: `perturbCoeffOn` adds
`t . h` to the base coefficient field pointwise, and the centered shell's value
field is by construction the literal difference of the two rescaled coefficient
objects.

Unconditional beyond the binders of `centeredShellUnitCube`: no further
caller-supplied proposition enters. -/
theorem centeredShellUnitCube_shift (M : ABKModel d) (Q : TriadicCube d)
    {lowScale highScale : ℤ} (hle : lowScale ≤ highScale) (omega : CutoffSample d)
    (hbar : Mat d) (hskew : matTranspose hbar = -hbar) (x : Vec d) :
    (perturbCoeffOn (cubeDomain (originCube d 0))
        (unitRescaledCutoffCoeff M Q lowScale omega)
        (centeredShellUnitCube M Q hle omega hbar hskew).toLInfSkewMatrixFieldOn
        1).toCoeffField x =
      (unitRescaledCutoffCoeff M Q highScale omega).toCoeffField x - hbar := by
  change (unitRescaledCutoffCoeff M Q lowScale omega).toCoeffField x +
      (1 : ℝ) • ((unitRescaledCutoffCoeff M Q highScale omega).toCoeffField x -
        (unitRescaledCutoffCoeff M Q lowScale omega).toCoeffField x - hbar) =
    (unitRescaledCutoffCoeff M Q highScale omega).toCoeffField x - hbar
  rw [one_smul]
  abel

/-! ## The second caller binder: `hgrad` -/

/-- **Centering by a constant preserves the gradient gauge.**  The centered
shell's frozen `gradientW1Infinity` *is* that of the uncentered rescaled
increment `k_{highScale} - k_{lowScale}`.

Both the constant shift and the representative change leave the stored first
and second derivative fields untouched, and `gradientW1Infinity` reads nothing
else, so the identification is definitional.

Unconditional beyond the binders of `centeredShellUnitCube`. -/
@[simp]
theorem centeredShellUnitCube_gradientW1Infinity (M : ABKModel d) (Q : TriadicCube d)
    {lowScale highScale : ℤ} (hle : lowScale ≤ highScale) (omega : CutoffSample d)
    (hbar : Mat d) (hskew : matTranspose hbar = -hbar) :
    (centeredShellUnitCube M Q hle omega hbar hskew).gradientW1Infinity =
      (incrementUnitCube₂ Q lowScale highScale omega).gradientW1Infinity :=
  rfl

/-- **The binder `hgrad` of `PrincipalResponseSwitchTransport`, produced.**

Almost surely on the cutoff sample law, membership in the manuscript's own
event `cQ(n, m-h, z)` -- here `goodLocalEvent M Ccg Q lowScale` at the
localization cube `Q` of scale `n` and the coarse scale `lowScale = m-h` --
already gives the discounted gradient gate for the **centered** shell:

```
C_sens ||grad (h - (h)_{z+cu_n})||  <=  3^{-(1/4)(m-h-n)_+} lambda_{3/8,2}(z+cu_n; a_{m-h}) .
```

This is the proved
`responseSensitivityConst_mul_gradientW1Infinity_le_of_mem_goodLocalEvent_ae`
of `PrincipalResponseSwitchTransport` with its remaining binder `hcentered`
discharged by `centeredShellUnitCube_gradientW1Infinity`.

: this statement holds only under the propositions supplied by its binders --
`hle` (`m - h <= m`) and `hskew` -- and the membership hypothesis carried
inside the almost-sure conclusion. -/
theorem responseSensitivityConst_mul_gradientW1Infinity_centeredShell_le_ae
    [NeZero d] (M : ABKModel d) (Ccg : ℝ) (Q : TriadicCube d)
    {lowScale highScale : ℤ} (hle : lowScale ≤ highScale)
    (hbar : CutoffSample d → Mat d)
    (hskew : ∀ omega : CutoffSample d, matTranspose (hbar omega) = -hbar omega) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      omega ∈ goodLocalEvent M Ccg Q lowScale →
        responseSensitivityConst d *
            (centeredShellUnitCube M Q hle omega (hbar omega)
              (hskew omega)).gradientW1Infinity ≤
          (3 : ℝ) ^ (-(1 / 4 : ℝ) * scaleGapPos Q.scale lowScale) *
            Ch02.lambdaSq Q (3 / 8) (.finite 2)
              (coefficientCutoffTriadicCoeffFamily M lowScale omega) := by
  filter_upwards [responseSensitivityConst_mul_gradientW1Infinity_le_of_mem_goodLocalEvent_ae
    M Ccg Q hle
    (fun omega => centeredShellUnitCube M Q hle omega (hbar omega) (hskew omega))]
    with omega hgate homega
  exact hgate homega (le_of_eq (centeredShellUnitCube_gradientW1Infinity M Q hle omega
    (hbar omega) (hskew omega)))

/-! ## The manuscript's own centering constant -/

/-- The centered fresh shell at the manuscript's own constant `(h)_{z+cu_n} =
freshShellCubeAverage`, whose antisymmetry is the proved
`freshShellCubeAverage_skew`.

: this statement holds only under the proposition supplied by its binder `hle`.
It is a provider A, not a source-facing frozen declaration. -/
def centeredFreshShellUnitCube (M : ABKModel d) (Q : TriadicCube d)
    {lowScale highScale : ℤ} (hle : lowScale ≤ highScale)
    (omega : CutoffSample d) : UnitCubeSkewW2Infinity d :=
  centeredShellUnitCube M Q hle omega
    (freshShellCubeAverage Q omega.1 lowScale highScale)
    (freshShellCubeAverage_skew Q omega.1 lowScale highScale)

/-- The binder `hshift` at the manuscript's own centering constant. -/
theorem centeredFreshShellUnitCube_shift (M : ABKModel d) (Q : TriadicCube d)
    {lowScale highScale : ℤ} (hle : lowScale ≤ highScale)
    (omega : CutoffSample d) (x : Vec d) :
    (perturbCoeffOn (cubeDomain (originCube d 0))
        (unitRescaledCutoffCoeff M Q lowScale omega)
        (centeredFreshShellUnitCube M Q hle omega).toLInfSkewMatrixFieldOn
        1).toCoeffField x =
      (unitRescaledCutoffCoeff M Q highScale omega).toCoeffField x -
        freshShellCubeAverage Q omega.1 lowScale highScale :=
  centeredShellUnitCube_shift M Q hle omega _ _ x

/-- The binder `hgrad` at the manuscript's own centering constant. -/
theorem responseSensitivityConst_mul_gradientW1Infinity_centeredFreshShell_le_ae
    [NeZero d] (M : ABKModel d) (Ccg : ℝ) (Q : TriadicCube d)
    {lowScale highScale : ℤ} (hle : lowScale ≤ highScale) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      omega ∈ goodLocalEvent M Ccg Q lowScale →
        responseSensitivityConst d *
            (centeredFreshShellUnitCube M Q hle omega).gradientW1Infinity ≤
          (3 : ℝ) ^ (-(1 / 4 : ℝ) * scaleGapPos Q.scale lowScale) *
            Ch02.lambdaSq Q (3 / 8) (.finite 2)
              (coefficientCutoffTriadicCoeffFamily M lowScale omega) :=
  responseSensitivityConst_mul_gradientW1Infinity_centeredShell_le_ae M Ccg Q hle
    (fun omega => freshShellCubeAverage Q omega.1 lowScale highScale)
    (fun omega => freshShellCubeAverage_skew Q omega.1 lowScale highScale)

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
