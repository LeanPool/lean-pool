/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.Step5InputOscillation

/-!
# Step5InputSideConditions

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The Step-5 typing side conditions at the closure's families

ABK26, Step 5 of `l.approximate.recurrence.formula`.

Besides the four mathematical legs (`hshell`, `hgradM`, `hmemOsc`, `hosc`), the
basket
`Closure.Step5Basket.step5GaugeEndpoint_closureFamilies_of_momentLegs` carries
four *typing* binders: two sample measurabilities `hmeasX`, `hmeasS`, one
spatial integrability `hintP` and one sample integrability `hsampDef`.  This
module discharges the first three at the closure's own families.

* `hmeasX`, `hmeasS` are products of the two measurable factors: the averaged
  fresh shell (`ApproximateRecurrence.measurable_freshShellCubeAverage`) and the
  potential average (`ApproximateRecurrence.measurable_cubeAverageVec_freshShellDirichletGrad`),
  both read at the full sigma-algebra.
* `hintP` is a spatial statement at a *fixed* sample: the fresh shell is
  continuous, hence bounded on the localization cube, and the corrector gradient
  is `L^1` there, so the pairing is integrable.

`hsampDef` is **not** discharged *here*; it is discharged downstream, in
`Closure.Step5SampDefMeasurable` (its measurability half) and
`Closure.Step5SampDef` (the whole binder).  See the disclosure.

## References

* ABK26, `l.approximate.recurrence.formula`, Step 5.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open Algsuperdiff.Section3.Provider.Diffusivity.Corrector
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Generic measurability of the two pairings -/

theorem measurable_matVecMul_of_measurable {Omega : Type*} [MeasurableSpace Omega]
    {A : Omega → Mat d} {v : Omega → Vec d} (hA : Measurable A) (hv : Measurable v) :
    Measurable fun omega => matVecMul (A omega) (v omega) := by
  classical
  refine Measurable.of_eval fun i => ?_
  have hEq : (fun omega => matVecMul (A omega) (v omega) i) =
      fun omega => ∑ j, A omega i j * v omega j := rfl
  rw [hEq]
  exact Finset.measurable_sum _ fun j _ =>
    (((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hA)).mul
      ((measurable_pi_apply j).comp hv))

theorem measurable_vecDot_const {Omega : Type*} [MeasurableSpace Omega] (e : Vec d)
    {w : Omega → Vec d} (hw : Measurable w) : Measurable fun omega => vecDot e (w omega) := by
  classical
  have hEq : (fun omega => vecDot e (w omega)) = fun omega => ∑ i, e i * w omega i := rfl
  rw [hEq]
  exact Finset.measurable_sum _ fun i _ =>
    ((measurable_pi_apply i).comp hw).const_mul (e i)

theorem measurable_vecNormSq_of_measurable {Omega : Type*} [MeasurableSpace Omega]
    {w : Omega → Vec d} (hw : Measurable w) : Measurable fun omega => vecNormSq (w omega) := by
  classical
  have hEq : (fun omega => vecNormSq (w omega)) =
      fun omega => ∑ i, w omega i * w omega i := rfl
  rw [hEq]
  exact Finset.measurable_sum _ fun i _ =>
    (((measurable_pi_apply i).comp hw).mul ((measurable_pi_apply i).comp hw))

/-! ## `hmeasX` and `hmeasS` at the closure's Dirichlet family -/

/-- The measurable pair of the Step-5 per-cube quadratic: the averaged fresh
shell applied to the potential average. -/
theorem measurable_matVecMul_freshShellCubeAverage_cubeAverageVec [NeZero d]
    {Q R : TriadicCube d} {jd : ℕ} (hR : R ∈ descendantsAtDepth Q jd) (sigmaInv : ℝ)
    (n m : ℤ) (e : Vec d) (wD : ShellSeq d → H10Function (openCubeSet Q))
    (hwD : ∀ omega : ShellSeq d,
      IsZeroTraceDirichletRhsWeakSolution
        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ)) (openCubeSet Q) (wD omega)
        (fun x => -streamForcing sigmaInv omega n m e x)) :
    Measurable fun omega : CutoffSample d =>
      matVecMul (freshShellCubeAverage R omega.val n m)
        (cubeAverageVec R (fun x => (wD omega.val).toH1Function.grad x)) :=
  measurable_matVecMul_of_measurable
    ((measurable_freshShellCubeAverage hR n m).comp measurable_subtype_coe)
    ((measurable_cubeAverageVec_freshShellDirichletGrad hR sigmaInv n m e wD hwD).comp
      measurable_subtype_coe)

/-- **`hmeasX` at the closure's Dirichlet family.** -/
theorem aestronglyMeasurable_step5PairingX [NeZero d] (M : ABKModel d) (n : ℤ) (h : ℕ)
    (K : ℕ) (e : Vec d) {R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth (originCube d (K : ℤ)) j) :
    AEStronglyMeasurable
      (fun omega : CutoffSample d =>
        vecDot e (matVecMul (freshShellCubeAverage R omega.val n (n + (h : ℤ)))
          (cubeAverageVec R
            (fun x => (alongIncrementPath n h
              (closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K)
                omega.val).toH1Function.grad x))))
      (cutoffSampleLaw M).toMeasure :=
  (measurable_vecDot_const e
    (measurable_matVecMul_freshShellCubeAverage_cubeAverageVec hR
      ((Annealed.sigmaBar M n : ℝ))⁻¹ n (n + (h : ℤ)) e
      (fun omega => alongIncrementPath n h
        (closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K) omega)
      (fun omega => isZeroTraceDirichletRhsWeakSolution_alongIncrementPath
        ((Annealed.sigmaBar M n : ℝ))⁻¹ e K n h omega))).aestronglyMeasurable

/-- **`hmeasS` at the closure's Dirichlet family.** -/
theorem aestronglyMeasurable_step5PairingS [NeZero d] (M : ABKModel d) (n : ℤ) (h : ℕ)
    (K : ℕ) (e : Vec d) {R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth (originCube d (K : ℤ)) j) :
    AEStronglyMeasurable
      (fun omega : CutoffSample d =>
        vecNormSq (matVecMul (freshShellCubeAverage R omega.val n (n + (h : ℤ)))
          (cubeAverageVec R
            (fun x => (alongIncrementPath n h
              (closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K)
                omega.val).toH1Function.grad x))))
      (cutoffSampleLaw M).toMeasure :=
  (measurable_vecNormSq_of_measurable
    (measurable_matVecMul_freshShellCubeAverage_cubeAverageVec hR
      ((Annealed.sigmaBar M n : ℝ))⁻¹ n (n + (h : ℤ)) e
      (fun omega => alongIncrementPath n h
        (closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K) omega)
      (fun omega => isZeroTraceDirichletRhsWeakSolution_alongIncrementPath
        ((Annealed.sigmaBar M n : ℝ))⁻¹ e K n h omega))).aestronglyMeasurable

/-! ## `hintP`: the spatial pairing on the localization cube -/

/-- **`hintP`, at a fixed sample.**  The fresh shell is continuous, hence
bounded on the closed localization cube; the corrector gradient is `L^1` there,
because it is `L^8`; so their pairing against a fixed direction is integrable. -/
theorem integrableOn_cubeSet_vecDot_matVecMul_finiteShellIncrement (Q : TriadicCube d)
    (omega : ShellSeq d) (n m : ℤ) (e : Vec d) {u : Vec d → Vec d}
    (hu : MemLp u (8 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    IntegrableOn (fun x => vecDot e (matVecMul (finiteShellIncrement omega n m x) (u x)))
      (cubeSet Q) volume := by
  classical
  -- the corrector gradient is integrable on the closed cube
  have hu1 : MemLp u (1 : ℝ≥0∞) (normalizedCubeMeasure Q) := hu.mono_exponent (by norm_num)
  have hintN : Integrable u (normalizedCubeMeasure Q) := memLp_one_iff_integrable.1 hu1
  have huC : IntegrableOn u (cubeSet Q) volume := by
    have hne : ENNReal.ofReal ((cubeVolume Q)⁻¹) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (inv_pos.mpr (cubeVolume_pos Q))).ne'
    rw [normalizedCubeMeasure] at hintN
    exact (integrable_smul_measure hne ENNReal.ofReal_ne_top).1 hintN
  -- the fresh shell is bounded on the closed cube
  have hcont : Continuous fun x : Vec d =>
      matrixOperatorNorm (finiteShellIncrement omega n m x) :=
    (Algsuperdiff.Frozen.Assumptions.ShellField.continuous_matrixOperatorNorm (d := d)).comp
      (Corrector.continuous_finiteShellIncrement omega n m)
  obtain ⟨C, hC⟩ := (isCompact_closedBall (cubeCenter Q) (cubeRadius
    Q)).exists_bound_of_continuousOn
    hcont.continuousOn
  have hCball : ∀ x ∈ cubeSet Q,
      matrixOperatorNorm (finiteShellIncrement omega n m x) ≤ C := by
    intro x hx
    have := hC x (cubeSet_subset_closedBall Q hx)
    rwa [Real.norm_eq_abs,
      abs_of_nonneg (matrixOperatorNorm_nonneg _)] at this
  have hmeasu : AEStronglyMeasurable u (volume.restrict (cubeSet Q)) :=
    huC.aestronglyMeasurable
  have hmeas : AEStronglyMeasurable
      (fun x => vecDot e (matVecMul (finiteShellIncrement omega n m x) (u x)))
      (volume.restrict (cubeSet Q)) := by
    have hEq : (fun x => vecDot e (matVecMul (finiteShellIncrement omega n m x) (u x))) =
        fun x => ∑ i : Fin d, ∑ j : Fin d,
          e i * (finiteShellIncrement omega n m x i j * u x j) := by
      funext x
      change (∑ i, e i * (∑ j, finiteShellIncrement omega n m x i j * u x j)) = _
      exact Finset.sum_congr rfl fun i _ => Finset.mul_sum _ _ _
    rw [hEq]
    refine Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
      Finset.aestronglyMeasurable_fun_sum _ fun j _ => ?_
    exact (((continuous_finiteShellIncrement_entry omega n m i
      j).aestronglyMeasurable).mul
      ((continuous_apply j).comp_aestronglyMeasurable hmeasu)).const_mul (e i)
  have hmaj : IntegrableOn (fun x => (vecNorm e * C * Real.sqrt d) * ‖u x‖)
      (cubeSet Q) volume := huC.norm.const_mul _
  refine hmaj.mono' hmeas ?_
  filter_upwards [ae_restrict_mem (measurableSet_cubeSet Q)] with x hx
  have h1 : |vecDot e (matVecMul (finiteShellIncrement omega n m x) (u x))| ≤
      vecNorm e * vecNorm (matVecMul (finiteShellIncrement omega n m x) (u x)) :=
    abs_vecDot_le_vecNorm_mul_vecNorm _ _
  have h2 : vecNorm (matVecMul (finiteShellIncrement omega n m x) (u x)) ≤
      matrixOperatorNorm (finiteShellIncrement omega n m x) * vecNorm (u x) :=
    vecNorm_matVecMul_le_matrixOperatorNorm_mul_vecNorm _ _
  have h3 : matrixOperatorNorm (finiteShellIncrement omega n m x) ≤ C := hCball x hx
  have h4 : vecNorm (u x) ≤ Real.sqrt d * ‖u x‖ := vecNorm_le_sqrt_dim_mul_norm (u x)
  have he0 : (0 : ℝ) ≤ vecNorm e := vecNorm_nonneg e
  have hu0 : (0 : ℝ) ≤ vecNorm (u x) := vecNorm_nonneg _
  have hC0 : (0 : ℝ) ≤ C := le_trans (matrixOperatorNorm_nonneg _) h3
  rw [Real.norm_eq_abs]
  calc |vecDot e (matVecMul (finiteShellIncrement omega n m x) (u x))|
      ≤ vecNorm e * vecNorm (matVecMul (finiteShellIncrement omega n m x) (u x)) := h1
    _ ≤ vecNorm e * (matrixOperatorNorm (finiteShellIncrement omega n m x) * vecNorm (u x)) :=
        mul_le_mul_of_nonneg_left h2 he0
    _ ≤ vecNorm e * (C * (Real.sqrt d * ‖u x‖)) := by
        refine mul_le_mul_of_nonneg_left ?_ he0
        exact mul_le_mul h3 h4 hu0 hC0
    _ = (vecNorm e * C * Real.sqrt d) * ‖u x‖ := by ring

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
