/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.IncrementBridge
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# IncrementGaugeTwoIndex

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The two-index increment oscillation gauge, its measurability, and its bridge

`Algsuperdiff.Section3.Provider.BadEvents.incrementOscGauge` measures the stream
increment whose base index is the cube scale, which is what `e.Bosc.def` (ABK26)
needs.  The good event `e.good.local.events` (ABK26) gauges an increment `k_L -
k_n` whose base `n` need not equal the cube scale.  This module supplies that
two-index version, together with the measurability that the corresponding event
needs and the two-index unit-cube bridge into the frozen Section 2.4 sensitivity
gate (ABK26).

Everything is factored through a single-shell-field gauge `cubeOscGauge Q h`,
namely the manuscript's `3^{2j} ||grad h||_{W^{1,infinity}(z + square_j)}` for
an arbitrary shell field `h` at the cube `Q` with `j = Q.scale`; the proved
one-index objects are literally the case `h = k_L - k_{Q.scale}`
(`incrementOscGauge₂_self`, `incrementUnitCube₂_self`, both `rfl`).

## Main definitions

* `cubeOscGauge`: `3^{2j} ||grad h||_{W^{1,infinity}(z + square_j)}`.
* `cubeUnitCube`: the rescaled unit-cube `W^{2,infinity}` package of `h`.
* `incrementOscGauge₂`, `incrementUnitCube₂`: the two-index specializations.

## Main results

* `continuous_shellFieldSum`, `measurable_shellFieldSum`,
  `measurable_shellIncrement`: the additive layer of
  `Algsuperdiff.Section3.Provider.Stream.ShellSum` is continuous, hence
  measurable, in the shell sequence.
* `measurable_cubeOscGauge`, `measurable_incrementOscGauge₂`: the measurability
  needed to realize `e.good.local.events` as a measurable event.
* `incrementOscGauge₂_le_sum_shellOscGauge`: the `W^{1,infinity}` triangle
  inequality at the two-index gauge.
* `gradientW1Infinity_cubeUnitCube_le`,
  `gradientW1Infinity_incrementUnitCube₂_le`: the two-index bridge.

## References

* ABK26 (volume-normalized Sobolev norms).
* ABK26, `e.Bosc.def`, `e.Bosc.decomp`.
* ABK26, `e.good.local.events`.
-/

namespace Algsuperdiff.Section3.Provider.BadEvents

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Frozen.Section24
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Stream
open scoped BigOperators Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-! ## Local instances

Mathlib's default instance search reaches neither of these inside its heartbeat
budget, so the file installs them locally.  The first is the second-countability
of the frozen compact-open carrier, which is what turns continuity in the shell
sequence into measurability; the second is the second-derivative fibre's
continuous addition, needed for finite sums. -/

private theorem secondCountableTopology_shellField (d : ℕ) :
    SecondCountableTopology (ShellField d) := by
  have hMat : SecondCountableTopology (Mat d) := by
    change SecondCountableTopology (Fin d → Fin d → ℝ)
    infer_instance
  have hDeriv : SecondCountableTopology (Vec d →L[ℝ] Mat d) :=
    @secondCountable_of_proper (Vec d →L[ℝ] Mat d)
      (@SeminormedAddCommGroup.toPseudoMetricSpace (Vec d →L[ℝ] Mat d)
        (@NormedAddCommGroup.toSeminormedAddCommGroup (Vec d →L[ℝ] Mat d) inferInstance))
      (@FiniteDimensional.proper ℝ inferInstance (Vec d →L[ℝ] Mat d)
        inferInstance inferInstance inferInstance ContinuousLinearMap.finiteDimensional)
  have hFinDim1 : FiniteDimensional ℝ (Vec d →L[ℝ] Mat d) :=
    ContinuousLinearMap.finiteDimensional
  have hCSMul1 : ContinuousConstSMul ℝ (Vec d →L[ℝ] Mat d) := inferInstance
  have hFinDim2 : FiniteDimensional ℝ (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) :=
    @ContinuousLinearMap.finiteDimensional ℝ (Vec d) (Vec d →L[ℝ] Mat d)
      _ _ _ _ _ _ _ _ _ hFinDim1 hCSMul1
  have hSecondDeriv : SecondCountableTopology (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) :=
    @secondCountable_of_proper (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d))
      (@SeminormedAddCommGroup.toPseudoMetricSpace (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d))
        (@NormedAddCommGroup.toSeminormedAddCommGroup (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d))
          inferInstance))
      (@FiniteDimensional.proper ℝ inferInstance (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d))
        inferInstance inferInstance inferInstance hFinDim2)
  have hC1 : SecondCountableTopology C(Vec d, Mat d) := by
    have := hMat
    infer_instance
  have hC2 : SecondCountableTopology C(Vec d, Vec d →L[ℝ] Mat d) := by
    have := hDeriv
    infer_instance
  have hC3 : SecondCountableTopology
      C(Vec d, Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) := by
    have := hSecondDeriv
    infer_instance
  have hAmbient : SecondCountableTopology (ShellAmbient d) := by
    change SecondCountableTopology
      (C(Vec d, Mat d) ×
        (C(Vec d, Vec d →L[ℝ] Mat d) × C(Vec d, Vec d →L[ℝ] (Vec d →L[ℝ] Mat d))))
    have := hC1
    have := hC2
    have := hC3
    infer_instance
  exact TopologicalSpace.secondCountableTopology_induced
    (ShellField d) (ShellAmbient d) Subtype.val

attribute [local instance] secondCountableTopology_shellField

private theorem continuousAdd_matrixSecondDerivative (d : ℕ) :
    ContinuousAdd (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) := by
  have h : IsTopologicalAddGroup (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) := inferInstance
  exact h.toContinuousAdd

attribute [local instance] continuousAdd_matrixSecondDerivative

/-- `Vec d` is locally compact, so it is the first component of a locally
compact pair with every target.  Mathlib's search for this reaches the
priority-900 instance only past its heartbeat budget at the second-derivative
fibre, so the file installs it locally. -/
private theorem locallyCompactPair_vec (d : ℕ) (Y : Type*) [TopologicalSpace Y] :
    LocallyCompactPair (Vec d) Y where
  exists_mem_nhds_isCompact_mapsTo hf hs :=
    let ⟨K, hKx, hKs, hKc⟩ := local_compact_nhds (hf.continuousAt hs)
    ⟨K, hKx, hKc, hKs⟩

attribute [local instance] locallyCompactPair_vec

/-! ## Continuity and measurability of the additive layer -/

private theorem continuous_eval_pair :
    Continuous fun q : ShellField d × Vec d => q.1 q.2 := by
  have _ : ContinuousEval C(Vec d, Mat d) (Vec d) (Mat d) := inferInstance
  exact ContinuousEval.continuous_eval.comp
    (((continuous_subtype_val.comp continuous_fst).fst).prodMk continuous_snd)

private theorem continuous_eval_pair_deriv :
    Continuous fun q : ShellField d × Vec d => ShellField.deriv q.1 q.2 := by
  have _ : ContinuousEval C(Vec d, Vec d →L[ℝ] Mat d) (Vec d)
      (Vec d →L[ℝ] Mat d) := inferInstance
  exact ContinuousEval.continuous_eval.comp
    (((continuous_subtype_val.comp continuous_fst).snd.fst).prodMk continuous_snd)

private theorem continuous_eval_pair_secondDeriv :
    Continuous fun q : ShellField d × Vec d => ShellField.secondDeriv q.1 q.2 := by
  have _ : ContinuousEval C(Vec d, Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) (Vec d)
      (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) := inferInstance
  exact ContinuousEval.continuous_eval.comp
    (((continuous_subtype_val.comp continuous_fst).snd.snd).prodMk continuous_snd)

private theorem continuous_coord_pair (i : ℤ) :
    Continuous fun p : ShellSeq d × Vec d => ((p.1 i, p.2) : ShellField d × Vec d) :=
  ((continuous_apply i).comp continuous_fst).prodMk continuous_snd

private theorem continuous_coord_eval (i : ℤ) :
    Continuous fun p : ShellSeq d × Vec d => p.1 i p.2 :=
  continuous_eval_pair.comp (continuous_coord_pair i)

private theorem continuous_coord_eval_deriv (i : ℤ) :
    Continuous fun p : ShellSeq d × Vec d => ShellField.deriv (p.1 i) p.2 :=
  continuous_eval_pair_deriv.comp (continuous_coord_pair i)

private theorem continuous_coord_eval_secondDeriv (i : ℤ) :
    Continuous fun p : ShellSeq d × Vec d => ShellField.secondDeriv (p.1 i) p.2 :=
  continuous_eval_pair_secondDeriv.comp (continuous_coord_pair i)

private theorem continuous_uncurry_value (s : Finset ℤ) :
    Continuous fun p : ShellSeq d × Vec d => ∑ i ∈ s, p.1 i p.2 :=
  continuous_finsetSum s fun i _ => continuous_coord_eval i

private theorem continuous_uncurry_deriv (s : Finset ℤ) :
    Continuous fun p : ShellSeq d × Vec d =>
      ∑ i ∈ s, ShellField.deriv (p.1 i) p.2 :=
  continuous_finsetSum s fun i _ => continuous_coord_eval_deriv i

private theorem continuous_uncurry_secondDeriv (s : Finset ℤ) :
    Continuous fun p : ShellSeq d × Vec d =>
      ∑ i ∈ s, ShellField.secondDeriv (p.1 i) p.2 :=
  @continuous_finsetSum ℤ (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) (ShellSeq d × Vec d) _ _ _
    (continuousAdd_matrixSecondDerivative d) _ s fun i _ => continuous_coord_eval_secondDeriv i

private theorem continuous_sum_value (s : Finset ℤ) :
    Continuous fun omega : ShellSeq d =>
      ((ShellField.sum s omega).1.1 : C(Vec d, Mat d)) := by
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  exact continuous_uncurry_value s

private theorem continuous_sum_deriv (s : Finset ℤ) :
    Continuous fun omega : ShellSeq d =>
      ((ShellField.sum s omega).1.2.1 : C(Vec d, Vec d →L[ℝ] Mat d)) := by
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  exact continuous_uncurry_deriv s

private theorem continuous_sum_secondDeriv (s : Finset ℤ) :
    Continuous fun omega : ShellSeq d =>
      ((ShellField.sum s omega).1.2.2 :
        C(Vec d, Vec d →L[ℝ] (Vec d →L[ℝ] Mat d))) := by
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  exact continuous_uncurry_secondDeriv s

/-- Finite shell-field sums are continuous in the shell sequence. -/
theorem continuous_shellFieldSum (s : Finset ℤ) :
    Continuous fun omega : ShellSeq d => ShellField.sum s omega :=
  Continuous.subtype_mk
    ((continuous_sum_value s).prodMk
      ((continuous_sum_deriv s).prodMk (continuous_sum_secondDeriv s)))
    fun omega => (ShellField.sum s omega).2

/-- Finite shell-field sums are measurable in the shell sequence. -/
theorem measurable_shellFieldSum (s : Finset ℤ) :
    Measurable fun omega : ShellSeq d => ShellField.sum s omega :=
  (continuous_shellFieldSum s).measurable

/-- The literal stream increment is measurable in the shell sequence. -/
theorem measurable_shellIncrement (n L : ℤ) :
    Measurable fun omega : ShellSeq d => shellIncrement omega n L :=
  measurable_shellFieldSum (Finset.Ioc n L)

/-- The literal stream increment is measurable on the cutoff sample carrier. -/
theorem measurable_shellIncrement_cutoffSample (n L : ℤ) :
    Measurable fun omega : CutoffSample d => shellIncrement omega.1 n L :=
  (measurable_shellIncrement n L).comp measurable_subtype_coe

/-! ## The single-shell-field cube gauge -/

/-- The manuscript's `3^{2j} ||grad h||_{W^{1,infinity}(z + square_j)}` for an
arbitrary shell field `h`, at the cube `Q` with `j = Q.scale` and base point `z
= cubeBasePoint Q`.  At `p = infinity` the volume-normalized Sobolev norm of
ABK26 is `max { ||grad² h||_{L∞}, 3^{-j} ||grad h||_{L∞} }`. -/
def cubeOscGauge (Q : TriadicCube d) (h : ShellField d) : ℝ :=
  max
    ((3 : ℝ) ^ (2 * Q.scale) *
      localCubeSecondDerivNorm Q.scale (ShellField.translate (cubeBasePoint Q) h))
    ((3 : ℝ) ^ Q.scale *
      localCubeDerivNorm Q.scale (ShellField.translate (cubeBasePoint Q) h))

theorem cubeOscGauge_nonneg (Q : TriadicCube d) (h : ShellField d) :
    0 ≤ cubeOscGauge Q h := by
  refine le_max_of_le_right (mul_nonneg ?_ (localCubeDerivNorm_nonneg _ _))
  exact (zpow_pos (by norm_num : (0 : ℝ) < 3) _).le

theorem measurable_cubeOscGauge (Q : TriadicCube d) :
    Measurable (cubeOscGauge (d := d) Q) := by
  have hbase : Measurable
      (fun h : ShellField d => ShellField.translate (cubeBasePoint Q) h) :=
    ShellField.measurable_translate (cubeBasePoint Q)
  exact
    (((measurable_localCubeSecondDerivNorm Q.scale).comp hbase).const_mul _).max
      (((measurable_localCubeDerivNorm Q.scale).comp hbase).const_mul _)

/-- The single-shell-field gauge is subadditive along finite shell-field sums,
which is the `W^{1,infinity}` triangle inequality of `e.Bosc.decomp`. -/
theorem cubeOscGauge_sum_le {ι : Type*} (Q : TriadicCube d) (s : Finset ι)
    (f : ι → ShellField d) :
    cubeOscGauge Q (ShellField.sum s f) ≤ ∑ i ∈ s, cubeOscGauge Q (f i) := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ Q.scale := zpow_pos (by norm_num) _
  have h32 : (0 : ℝ) < (3 : ℝ) ^ (2 * Q.scale) := zpow_pos (by norm_num) _
  refine max_le ?_ ?_
  · calc
      (3 : ℝ) ^ (2 * Q.scale) *
          localCubeSecondDerivNorm Q.scale
            (ShellField.translate (cubeBasePoint Q) (ShellField.sum s f))
          ≤ (3 : ℝ) ^ (2 * Q.scale) *
            ∑ i ∈ s, localCubeSecondDerivNorm Q.scale
              (ShellField.translate (cubeBasePoint Q) (f i)) := by
        refine mul_le_mul_of_nonneg_left ?_ h32.le
        rw [ShellField.translate_sum]
        exact localCubeSecondDerivNorm_sum_le Q.scale s
          fun i => ShellField.translate (cubeBasePoint Q) (f i)
      _ = ∑ i ∈ s, (3 : ℝ) ^ (2 * Q.scale) *
            localCubeSecondDerivNorm Q.scale
              (ShellField.translate (cubeBasePoint Q) (f i)) :=
        Finset.mul_sum _ _ _
      _ ≤ ∑ i ∈ s, cubeOscGauge Q (f i) :=
        Finset.sum_le_sum fun i _ => le_max_left _ _
  · calc
      (3 : ℝ) ^ Q.scale *
          localCubeDerivNorm Q.scale
            (ShellField.translate (cubeBasePoint Q) (ShellField.sum s f))
          ≤ (3 : ℝ) ^ Q.scale *
            ∑ i ∈ s, localCubeDerivNorm Q.scale
              (ShellField.translate (cubeBasePoint Q) (f i)) := by
        refine mul_le_mul_of_nonneg_left ?_ h3.le
        rw [ShellField.translate_sum]
        exact localCubeDerivNorm_sum_le Q.scale s
          fun i => ShellField.translate (cubeBasePoint Q) (f i)
      _ = ∑ i ∈ s, (3 : ℝ) ^ Q.scale *
            localCubeDerivNorm Q.scale
              (ShellField.translate (cubeBasePoint Q) (f i)) :=
        Finset.mul_sum _ _ _
      _ ≤ ∑ i ∈ s, cubeOscGauge Q (f i) :=
        Finset.sum_le_sum fun i _ => le_max_right _ _

/-! ## The two-index increment gauge -/

/-- The manuscript's `3^{2j} ||grad (k_L - k_n)||_{W^{1,infinity}(z+square_j)}`
with an increment base `n` that need not be the cube scale `j = Q.scale`.  This
is the gauge of `e.good.local.events` (ABK26). -/
def incrementOscGauge₂ (Q : TriadicCube d) (n L : ℤ) : CutoffSample d → ℝ :=
  fun omega => cubeOscGauge Q (shellIncrement omega.1 n L)

theorem incrementOscGauge₂_nonneg (Q : TriadicCube d) (n L : ℤ)
    (omega : CutoffSample d) : 0 ≤ incrementOscGauge₂ Q n L omega :=
  cubeOscGauge_nonneg Q _

/-- Measurability of the two-index gauge, used by the local implementation of
`e.good.local.events` as a measurable event. -/
theorem measurable_incrementOscGauge₂ (Q : TriadicCube d) (n L : ℤ) :
    Measurable (incrementOscGauge₂ (d := d) Q n L) :=
  (measurable_cubeOscGauge Q).comp (measurable_shellIncrement_cutoffSample n L)

/-- The `W^{1,infinity}` triangle inequality at the two-index gauge. -/
theorem incrementOscGauge₂_le_sum_shellOscGauge (Q : TriadicCube d) (n L : ℤ)
    (omega : CutoffSample d) :
    incrementOscGauge₂ Q n L omega ≤
      ∑ k ∈ Finset.Ioc n L, shellOscGauge Q k omega :=
  cubeOscGauge_sum_le Q (Finset.Ioc n L) omega.1

/-! ## The two-index unit-cube bridge -/

/-- The shell field `h` on `z + square_j`, rescaled to the unit cube by
`y |-> z + 3^j y`, as a Section 2.4 unit-cube object. -/
def cubeUnitCube (Q : TriadicCube d) (h : ShellField d) :
    UnitCubeSkewW2Infinity d :=
  shellFieldUnitCube
    (ShellField.spatialScale ((3 : ℝ) ^ Q.scale)
      (ShellField.translate (cubeBasePoint Q) h))

@[simp]
theorem cubeUnitCube_value (Q : TriadicCube d) (h : ShellField d) (y : Vec d) :
    (cubeUnitCube Q h).toLInfSkewMatrixFieldOn.1.1 y =
      h (((3 : ℝ) ^ Q.scale) • y + cubeBasePoint Q) :=
  rfl

/-- The exact normalization: the unit-cube derivative gauges of the rescaled
field are the `3^{2j}`- and `3^{j}`-scaled cube gauges of the field. -/
theorem max_unitCubeDerivNorm_cube (Q : TriadicCube d) (h : ShellField d) :
    max
        (ShellField.unitCubeSecondDerivNorm
          (ShellField.spatialScale ((3 : ℝ) ^ Q.scale)
            (ShellField.translate (cubeBasePoint Q) h)))
        (ShellField.unitCubeDerivNorm
          (ShellField.spatialScale ((3 : ℝ) ^ Q.scale)
            (ShellField.translate (cubeBasePoint Q) h))) =
      cubeOscGauge Q h := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ Q.scale := zpow_pos (by norm_num) _
  have hfirst : ShellField.unitCubeDerivNorm
      (ShellField.spatialScale ((3 : ℝ) ^ Q.scale)
        (ShellField.translate (cubeBasePoint Q) h)) =
      (3 : ℝ) ^ Q.scale *
        localCubeDerivNorm Q.scale
          (ShellField.translate (cubeBasePoint Q) h) := by
    rw [localCubeDerivNorm, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt h3), one_mul]
  have hsecond : ShellField.unitCubeSecondDerivNorm
      (ShellField.spatialScale ((3 : ℝ) ^ Q.scale)
        (ShellField.translate (cubeBasePoint Q) h)) =
      (3 : ℝ) ^ (2 * Q.scale) *
        localCubeSecondDerivNorm Q.scale
          (ShellField.translate (cubeBasePoint Q) h) := by
    have hsq : (3 : ℝ) ^ (2 * Q.scale) = ((3 : ℝ) ^ Q.scale) ^ 2 := by
      rw [two_mul, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), sq]
    rw [localCubeSecondDerivNorm, hsq, inv_pow, ← mul_assoc,
      mul_inv_cancel₀ (by positivity), one_mul]
  rw [hfirst, hsecond]
  rfl

/-- The bridge at an arbitrary shell field. -/
theorem gradientW1Infinity_cubeUnitCube_le (Q : TriadicCube d) (h : ShellField d) :
    (cubeUnitCube Q h).gradientW1Infinity ≤ cubeOscGauge Q h := by
  rw [cubeUnitCube, ← max_unitCubeDerivNorm_cube Q h]
  exact gradientW1Infinity_shellFieldUnitCube_le _

/-- The two-index rescaled literal increment. -/
def incrementUnitCube₂ (Q : TriadicCube d) (n L : ℤ) (omega : CutoffSample d) :
    UnitCubeSkewW2Infinity d :=
  cubeUnitCube Q (shellIncrement omega.1 n L)

/-- The two-index rescaled increment has the manuscript's values
`(k_L - k_n)(z + 3^j y)`. -/
theorem incrementUnitCube₂_value (Q : TriadicCube d) {n L : ℤ} (hnL : n ≤ L)
    (omega : CutoffSample d) (y : Vec d) :
    (incrementUnitCube₂ Q n L omega).toLInfSkewMatrixFieldOn.1.1 y =
      cutoff L omega (((3 : ℝ) ^ Q.scale) • y + cubeBasePoint Q) -
        cutoff n omega (((3 : ℝ) ^ Q.scale) • y + cubeBasePoint Q) := by
  rw [incrementUnitCube₂, cubeUnitCube_value]
  exact shellIncrement_apply_eq_cutoff_sub omega hnL _

/-- The two-index bridge: the Section 2.4 sensitivity gate quantity of the
rescaled literal increment `k_L - k_n` is bounded by the two-index gauge
`3^{2j} ||grad (k_L - k_n)||_{W^{1,infinity}(z + square_j)}`. -/
theorem gradientW1Infinity_incrementUnitCube₂_le (Q : TriadicCube d) (n L : ℤ)
    (omega : CutoffSample d) :
    (incrementUnitCube₂ Q n L omega).gradientW1Infinity ≤
      incrementOscGauge₂ Q n L omega :=
  gradientW1Infinity_cubeUnitCube_le Q _

end

end Algsuperdiff.Section3.Provider.BadEvents
