/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.External.CalderonZygmund
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.FreshShellL8

/-!
# LocalizationCorrectorRegularity

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Spatial regularity of the two correctors of `e.def.w`

The coarse-energy envelope of
`LocalizationEnvelopeWire.exists_freshShell_gridFourthMoment_mesoWindowEnergy_le_wired`
asks its caller for four per-sample *spatial* propositions about the corrector
gradient on `cu_K`:

* `MemLp (fun x => vecNorm (grad w x)) 8 (normalizedCubeMeasure cu_K)`;
* `IntegrableOn (fun x => (grad w x k)^2) (openCubeSet cu_K) volume` for each
  coordinate `k`;
* `IntegrableOn (fun x => vecNormSq (grad w x)) (openCubeSet cu_K) volume`;
* `IntegrableOn (fun x => vecNormSq (grad w x)^2) (openCubeSet cu_K) volume`.

None of them is a step of the manuscript's argument: all four are consequences
of the single `L^8` membership that the Calderon--Zygmund estimate produces
alongside its bound, so the caller who already has the weak formulation of
`e.def.w` owes nothing extra.  This module derives them.

## Main results

* `memLp_eight_grad_freshShellDirichlet`, `memLp_eight_grad_freshShellNeumann` --
  the `L^8` membership of the two corrector gradients at the fresh-shell
  forcing, read off the external anchor.
* `memLp_vecNorm_eight_of_memLp_eight`,
  `integrableOn_openCubeSet_vecNormSq_of_memLp_eight`,
  `integrableOn_openCubeSet_vecNormSq_sq_of_memLp_eight`,
  `integrableOn_openCubeSet_coord_sq_of_memLp_eight` -- the four consequences.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport MeasureTheory
open Algsuperdiff.Section3.Provider.Diffusivity.Corrector
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The `L^8` membership from the external anchor -/

/-- **The Dirichlet corrector gradient of `e.def.w` lies in `L^8(cu_K)`.** The
Calderon--Zygmund estimate produces the membership together with its bound;
only the membership is read here.: on `hd` and on the weak formulation `hw` of
`e.def.w`. -/
theorem memLp_eight_grad_freshShellDirichlet (hd : 2 ≤ d) (Q : TriadicCube d)
    (sigmaInv : ℝ) (omega : Cutoff.ShellSeq d) (n m : ℤ) (e : Vec d)
    (w : H10Function (openCubeSet Q))
    (hw : IsZeroTraceDirichletRhsWeakSolution
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ)) (openCubeSet Q) w
      (fun x => -streamForcing sigmaInv omega n m e x)) :
    MemLp w.toH1Function.grad (8 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
  obtain ⟨_, _, hCZ⟩ := Algsuperdiff.Frozen.External.calderon_zygmund (d := d) hd
    (8 : ℝ≥0∞) (by norm_num) (by norm_num)
  exact ((hCZ Q (streamForcing sigmaInv omega n m e)
    (memLp_normalizedCubeMeasure_of_continuous Q _
      (continuous_streamForcing sigmaInv omega n m e))).1 w hw).1

/-- **The Neumann corrector gradient of `e.def.w` lies in `L^8(cu_K)`.**  The
Neumann mirror of the previous statement. -/
theorem memLp_eight_grad_freshShellNeumann (hd : 2 ≤ d) (Q : TriadicCube d)
    (sigmaInv : ℝ) (omega : Cutoff.ShellSeq d) (n m : ℤ) (e : Vec d)
    (w : H1MeanZeroFunction (openCubeSet Q))
    (hw : IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ)) (openCubeSet Q) w
      (fun x => -streamForcing sigmaInv omega n m e x)) :
    MemLp w.toH1Function.grad (8 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
  obtain ⟨_, _, hCZ⟩ := Algsuperdiff.Frozen.External.calderon_zygmund (d := d) hd
    (8 : ℝ≥0∞) (by norm_num) (by norm_num)
  exact ((hCZ Q (streamForcing sigmaInv omega n m e)
    (memLp_normalizedCubeMeasure_of_continuous Q _
      (continuous_streamForcing sigmaInv omega n m e))).2 w hw).1

/-! ## The four consequences of one `L^8` membership -/

/-- The Euclidean gauge of an `L^p` field is `L^p`.  Unconditional apart from
the membership `hu`. -/
theorem memLp_vecNorm_eight_of_memLp_eight (Q : TriadicCube d) {p : ℝ≥0∞}
    {u : Vec d → Vec d} (hu : MemLp u p (normalizedCubeMeasure Q)) :
    MemLp (fun x => Book.Ch02.vecNorm (u x)) p (normalizedCubeMeasure Q) := by
  exact Algsuperdiff.Section3.Provider.Diffusivity.Corrector.memLp_vecNorm_of_memLp hu

/-- **`|grad w|^2` is integrable on `cu_K`.**: on `hu`. -/
theorem integrableOn_openCubeSet_vecNormSq_of_memLp_eight (Q : TriadicCube d)
    {u : Vec d → Vec d} (hu : MemLp u (8 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    IntegrableOn (fun x => vecNormSq (u x)) (openCubeSet Q) volume := by
  have huE2 : MemLp (fun x => Book.Ch02.vecNorm (u x)) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) :=
    (memLp_vecNorm_eight_of_memLp_eight Q hu).mono_exponent (by norm_num)
  have hint : Integrable (fun x => vecNormSq (u x)) (normalizedCubeMeasure Q) := by
    simpa only [Book.Ch02.vecNorm_sq_eq_vecNormSq] using huE2.integrable_sq
  exact (integrableOn_cubeSet_of_integrable_normalized Q hint).mono_set
    (openCubeSet_subset_cubeSet Q)

/-- **`|grad w|^4` is integrable on `cu_K`.**: on `hu`. -/
theorem integrableOn_openCubeSet_vecNormSq_sq_of_memLp_eight (Q : TriadicCube d)
    {u : Vec d → Vec d} (hu : MemLp u (8 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    IntegrableOn (fun x => vecNormSq (u x) ^ 2) (openCubeSet Q) volume := by
  exact (integrableOn_cubeSet_vecNormSq_sq_of_memLp_four Q
    (hu.mono_exponent (by norm_num))).mono_set (openCubeSet_subset_cubeSet Q)

/-- **Each coordinate square of `grad w` is integrable on `cu_K`.**: on `hu`. -/
theorem integrableOn_openCubeSet_coord_sq_of_memLp_eight (Q : TriadicCube d)
    {u : Vec d → Vec d} (hu : MemLp u (8 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (k : Fin d) :
    IntegrableOn (fun x => (u x k) ^ 2) (openCubeSet Q) volume := by
  have hdom : IntegrableOn (fun x => vecNormSq (u x)) (openCubeSet Q) volume :=
    integrableOn_openCubeSet_vecNormSq_of_memLp_eight Q hu
  have hu1 : MemLp u (1 : ℝ≥0∞) (normalizedCubeMeasure Q) := hu.mono_exponent (by norm_num)
  have hintN : Integrable u (normalizedCubeMeasure Q) := memLp_one_iff_integrable.1 hu1
  have huC : IntegrableOn u (cubeSet Q) volume :=
    integrableOn_cubeSet_of_integrable_normalized Q hintN
  have hmeasO : AEStronglyMeasurable u (volume.restrict (openCubeSet Q)) :=
    huC.aestronglyMeasurable.mono_measure
      (Measure.restrict_mono (openCubeSet_subset_cubeSet Q) le_rfl)
  have hmeas : AEStronglyMeasurable (fun x => (u x k) ^ 2)
      (volume.restrict (openCubeSet Q)) :=
    (((continuous_apply k).comp_aestronglyMeasurable hmeasO)).pow 2
  refine Integrable.mono hdom hmeas ?_
  filter_upwards with x
  have hle : (u x k) ^ 2 ≤ vecNormSq (u x) := by
    have hsum : vecNormSq (u x) = ∑ j, u x j * u x j := rfl
    rw [hsum, pow_two]
    exact Finset.single_le_sum (f := fun j => u x j * u x j)
      (fun j _ => mul_self_nonneg _) (Finset.mem_univ k)
  have hnn : (0 : ℝ) ≤ vecNormSq (u x) := le_trans (sq_nonneg (u x k)) hle
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (u x k)),
    abs_of_nonneg hnn]
  exact hle

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
