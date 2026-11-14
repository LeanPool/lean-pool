/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.CoefficientFamily
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.CutoffL2Expectation

/-!
# CutoffFrobeniusMass

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Per-cube Frobenius masses of finite and genuine cutoffs

This module packages the volume-normalized squared Frobenius mass of a finite
lower truncation and of the genuine lower-infinite cutoff on an arbitrary
triadic cube.  Both observables use the public `CutoffSample` carrier.  The
finite observable reads its underlying shell sequence through `omega.1`, so
finite and limiting random variables have literally the same carrier.

For a fixed sample, the finite masses converge to the genuine mass.  The
canonical origin cover `cubeOriginCoverScale Q` puts every arbitrary cube in an
origin-centred cube on which the proved lower-tail control applies.  That
control bounds every truncation, so spatial dominated convergence requires no
extra containment or boundedness hypothesis.

## Source and correction

* ABK26, obtains estimates for the genuine stream by sending the finite lower
  cutoff to minus infinity.
* ABK26, expands the volume-normalized squared Frobenius mass of finite
  stream increments.
* No disorder normalization constant occurs in the definitions or the
  deterministic convergence theorem below.

## Main results

* `finiteLowerCutoffFrobeniusMass` and `cutoffFrobeniusMass` are the two
  per-cube observables on `CutoffSample`.
* `cutoffFrobeniusMass_nonneg` records the sign of the second.
* `measurable_cutoffFrobeniusMass` and
  `stronglyMeasurable_setIntegral_cutoffFrobeniusMass` make it available to the
  probabilistic consumers.
* `tendsto_finiteLowerCutoffFrobeniusMass` is pointwise convergence on every
  triadic cube.
-/

namespace Algsuperdiff.Section3.Provider.Stream

open Filter MeasureTheory
open HCPolySupport HCPolySupport.Book.Ch02
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-- The volume-normalized squared Frobenius mass of a finite lower cutoff on
an arbitrary triadic cube. -/
noncomputable def finiteLowerCutoffFrobeniusMass
    (Q : TriadicCube d) (m : ℤ) (q : ℕ) (omega : CutoffSample d) : ℝ :=
  Book.Ch02.average (Book.Ch02.cubeDomain Q)
    (fun x => matrixFrobeniusNormSq (finiteLowerCutoff m q omega.1 x))

/-- The volume-normalized squared Frobenius mass of the genuine lower-infinite
cutoff on an arbitrary triadic cube. -/
noncomputable def cutoffFrobeniusMass
    (Q : TriadicCube d) (m : ℤ) (omega : CutoffSample d) : ℝ :=
  Book.Ch02.average (Book.Ch02.cubeDomain Q)
    (fun x => matrixFrobeniusNormSq (cutoff m omega x))

/-- The genuine cutoff has nonnegative per-cube Frobenius mass. -/
theorem cutoffFrobeniusMass_nonneg
    (Q : TriadicCube d) (m : ℤ) (omega : CutoffSample d) :
    0 ≤ cutoffFrobeniusMass Q m omega := by
  unfold cutoffFrobeniusMass Book.Ch02.average
  simp only [Book.Ch02.cubeDomain_coe]
  refine mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg) ?_
  exact setIntegral_nonneg (measurableSet_openCubeSet Q)
    (fun x _ => matrixFrobeniusNormSq_nonneg (cutoff m omega x))

private theorem measurable_uncurry_frobeniusMass_cutoff_swap (m : ℤ) :
    Measurable (Function.uncurry
      (fun (omega : CutoffSample d) (x : Vec d) =>
        matrixFrobeniusNormSq (cutoff m omega x))) := by
  have hcomp : Function.uncurry
      (fun (omega : CutoffSample d) (x : Vec d) =>
        matrixFrobeniusNormSq (cutoff m omega x)) =
      Function.uncurry
        (fun (x : Vec d) (omega : CutoffSample d) =>
          matrixFrobeniusNormSq (cutoff m omega x)) ∘ Prod.swap := by
    funext p
    obtain ⟨omega, x⟩ := p
    rfl
  rw [hcomp]
  exact (measurable_uncurry_frobeniusMass_cutoff (d := d) m).comp measurable_swap

private theorem stronglyMeasurable_setIntegral_cutoffFrobeniusMass
    (Q : TriadicCube d) (m : ℤ) :
    StronglyMeasurable (fun omega : CutoffSample d =>
      ∫ x in openCubeSet Q,
        matrixFrobeniusNormSq (cutoff m omega x) ∂volume) :=
  (measurable_uncurry_frobeniusMass_cutoff_swap
    (d := d) m).stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (openCubeSet Q))

/-- The genuine per-cube Frobenius mass is measurable on the public cutoff
sample carrier. -/
theorem measurable_cutoffFrobeniusMass (Q : TriadicCube d) (m : ℤ) :
    Measurable (fun omega : CutoffSample d => cutoffFrobeniusMass Q m omega) := by
  unfold cutoffFrobeniusMass Book.Ch02.average
  simp only [Book.Ch02.cubeDomain_coe]
  exact ((stronglyMeasurable_setIntegral_cutoffFrobeniusMass Q m).const_mul _).measurable

private theorem abs_finiteLowerCutoff_entry_le_cutoffLocalControl_on_cube
    (Q : TriadicCube d) (m : ℤ) (q : ℕ) (omega : CutoffSample d)
    {x : Vec d} (hx : x ∈ openCubeSet Q) (i j : Fin d) :
    |finiteLowerCutoff m q omega.1 x i j| ≤
      cutoffLocalControl (cubeOriginCoverScale Q) m omega := by
  rw [finiteLowerCutoff_apply_entry_eq_sum_range_desc]
  calc
    |∑ r ∈ Finset.range q, omega.1 (m - (r : ℤ)) x i j| ≤
        ∑ r ∈ Finset.range q, |omega.1 (m - (r : ℤ)) x i j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ Finset.range q,
        localCubeControl (cubeOriginCoverScale Q) (omega.1 (m - (r : ℤ))) :=
      Finset.sum_le_sum fun r _ =>
        abs_entry_le_localCubeControl (cubeOriginCoverScale Q)
          (omega.1 (m - (r : ℤ))) (openCubeSet_subset_originCover Q hx) i j
    _ ≤ ∑' r : ℕ,
        localCubeControl (cubeOriginCoverScale Q) (omega.1 (m - (r : ℤ))) :=
      (summable_cutoffLocalControl (cubeOriginCoverScale Q) m omega).sum_le_tsum _
        (fun r _ => localCubeControl_nonneg
          (cubeOriginCoverScale Q) (omega.1 (m - (r : ℤ))))
    _ = cutoffLocalControl (cubeOriginCoverScale Q) m omega := rfl

private theorem tendsto_finiteLowerCutoff_entry_on_cube
    (Q : TriadicCube d) (m : ℤ) (omega : CutoffSample d)
    {x : Vec d} (hx : x ∈ openCubeSet Q) (i j : Fin d) :
    Tendsto (fun q : ℕ => finiteLowerCutoff m q omega.1 x i j) atTop
      (nhds (cutoff m omega x i j)) := by
  simpa only [cutoff_apply_entry] using
    (lowerTailGood_tendstoUniformlyOn_finiteLowerCutoff_entry
      omega.2 (cubeOriginCoverScale Q) m i j).tendsto_at
        (openCubeSet_subset_originCover Q hx)

private theorem tendsto_frobeniusMass_finiteLowerCutoff_on_cube
    (Q : TriadicCube d) (m : ℤ) (omega : CutoffSample d)
    {x : Vec d} (hx : x ∈ openCubeSet Q) :
    Tendsto
      (fun q : ℕ => matrixFrobeniusNormSq (finiteLowerCutoff m q omega.1 x))
      atTop (nhds (matrixFrobeniusNormSq (cutoff m omega x))) := by
  change Tendsto (fun q : ℕ =>
      ∑ i : Fin d, ∑ j : Fin d, finiteLowerCutoff m q omega.1 x i j ^ 2)
    atTop (nhds (∑ i : Fin d, ∑ j : Fin d, cutoff m omega x i j ^ 2))
  exact tendsto_finsetSum _ fun i _ =>
    tendsto_finsetSum _ fun j _ =>
      (tendsto_finiteLowerCutoff_entry_on_cube Q m omega hx i j).pow 2

/-- On every triadic cube and for every cutoff sample, the finite lower
truncation masses converge to the genuine cutoff mass. -/
theorem tendsto_finiteLowerCutoffFrobeniusMass
    (Q : TriadicCube d) (m : ℤ) (omega : CutoffSample d) :
    Tendsto (fun q : ℕ => finiteLowerCutoffFrobeniusMass Q m q omega)
      atTop (nhds (cutoffFrobeniusMass Q m omega)) := by
  let : IsFiniteMeasure (volume.restrict (openCubeSet Q)) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact volume_openCubeSet_lt_top Q⟩
  have hmeas : ∀ q : ℕ, AEStronglyMeasurable
      (fun x : Vec d => matrixFrobeniusNormSq (finiteLowerCutoff m q omega.1 x))
      (volume.restrict (openCubeSet Q)) := by
    intro q
    change AEStronglyMeasurable
      (fun x : Vec d => matrixFrobeniusNormSq
        (finiteShellIncrement omega.1 (m - (q : ℤ)) m x))
      (volume.restrict (openCubeSet Q))
    exact (continuous_frobeniusMass_finiteShellIncrement
      (m - (q : ℤ)) m omega.1).measurable.aestronglyMeasurable
  have hint : Tendsto
      (fun q : ℕ => ∫ x in openCubeSet Q,
        matrixFrobeniusNormSq (finiteLowerCutoff m q omega.1 x) ∂volume)
      atTop
      (nhds (∫ x in openCubeSet Q,
        matrixFrobeniusNormSq (cutoff m omega x) ∂volume)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun _ : Vec d => (d : ℝ) ^ 2 *
        cutoffLocalControl (cubeOriginCoverScale Q) m omega ^ 2)
      hmeas (integrable_const _) (fun q => ?_) ?_
    · filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
      rw [Real.norm_eq_abs,
        abs_of_nonneg (matrixFrobeniusNormSq_nonneg
          (finiteLowerCutoff m q omega.1 x))]
      exact matrixFrobeniusNormSq_le_of_abs_entry_le fun i j =>
        abs_finiteLowerCutoff_entry_le_cutoffLocalControl_on_cube
          Q m q omega hx i j
    · filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
      exact tendsto_frobeniusMass_finiteLowerCutoff_on_cube Q m omega hx
  simpa only [finiteLowerCutoffFrobeniusMass, cutoffFrobeniusMass,
    Book.Ch02.average, Book.Ch02.cubeDomain_coe] using
      hint.const_mul (volume (openCubeSet Q)).toReal⁻¹

end

end Algsuperdiff.Section3.Provider.Stream
