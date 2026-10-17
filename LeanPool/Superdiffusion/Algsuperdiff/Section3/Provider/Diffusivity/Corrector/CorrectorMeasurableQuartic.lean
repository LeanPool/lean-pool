/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.CorrectorMeasurableMoments

/-!
# Quartic corrector observables

Compatibility specializations of the shared positive-moment measurability argument.
Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
-/

@[expose] public section

namespace Algsuperdiff.Section3.Provider.Diffusivity.Corrector

open HCPolySupport MeasureTheory
open Algsuperdiff.Section3

noncomputable section

variable {d : ℕ} {U : Set (Vec d)}

/-- The quartic norm clamped at height `n`. -/
def hilbertVecQuarticTrunc (n : ℕ) (v : HilbertVec d) : ℝ :=
  hilbertVecMomentTrunc 4 n v

theorem hilbertVecQuarticTrunc_zero (n : ℕ) :
    hilbertVecQuarticTrunc (d := d) n 0 = 0 :=
  hilbertVecMomentTrunc_zero 4 (by norm_num) n

theorem lipschitzWith_hilbertVecQuarticTrunc (n : ℕ) :
    LipschitzWith (4 * (n : NNReal) ^ 3) (hilbertVecQuarticTrunc (d := d) n) :=
  lipschitzWith_hilbertVecMomentTrunc 4 n

/-- The truncated quartic window integral as a continuous `L²` functional. -/
def windowQuarticTrunc [IsFiniteMeasure (volumeMeasureOn U)]
    (S : Set (Vec d)) (hS : MeasurableSet S) (n : ℕ) (F : HilbertVectorL2 U) : ℝ :=
  windowMomentTrunc 4 (by norm_num) S hS n F

/-- Unconditional: **the normalized fourth energy of the Dirichlet corrector
gradient over any measurable window of the cube is a measurable function of the
sample.**

`wD` is an arbitrary family of zero-trace weak solutions of the fresh-shell
Dirichlet problem `e.def.w`; no measurability, continuity or selection property
of the family is assumed.  This is the quartic observable the oscillation grid
display reads, and it is exactly what `CorrectorMeasurableGradient` left
open. -/
theorem measurable_volumeAverage_vecNormSq_sq_freshShellDirichletGrad [NeZero d]
    (Q : TriadicCube d) (sigmaInv : ℝ) (n m : ℤ) (e : Vec d)
    {S : Set (Vec d)} (hS : MeasurableSet S) (hSU : S ⊆ openCubeSet Q)
    (wD : Cutoff.ShellSeq d → H10Function (openCubeSet Q))
    (hwD : ∀ omega : Cutoff.ShellSeq d,
      IsZeroTraceDirichletRhsWeakSolution
        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
        (openCubeSet Q) (wD omega)
        (fun x => -streamForcing sigmaInv omega n m e x)) :
    Measurable fun omega =>
      volumeAverage S
        (fun x => vecNormSq ((wD omega).toH1Function.grad x) ^ 2) := by
  have : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  exact measurable_volumeAverage_vecNormSq_pow 2 (by norm_num) hS hSU
    (measurable_freshShellDirichletGradL2 Q sigmaInv n m e wD hwD)
    (w := fun omega => (wD omega).toH1Function) fun _ => rfl

/-- Unconditional: the Neumann mirror of the previous statement. -/
theorem measurable_volumeAverage_vecNormSq_sq_freshShellNeumannGrad
    (Q : TriadicCube d) (sigmaInv : ℝ) (n m : ℤ) (e : Vec d)
    {S : Set (Vec d)} (hS : MeasurableSet S) (hSU : S ⊆ openCubeSet Q)
    (wN : Cutoff.ShellSeq d → H1MeanZeroFunction (openCubeSet Q))
    (hwN : ∀ omega : Cutoff.ShellSeq d,
      IsMeanZeroNeumannRhsWeakSolution
        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
        (openCubeSet Q) (wN omega)
        (fun x => -streamForcing sigmaInv omega n m e x)) :
    Measurable fun omega =>
      volumeAverage S
        (fun x => vecNormSq ((wN omega).toH1Function.grad x) ^ 2) := by
  have : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  exact measurable_volumeAverage_vecNormSq_pow 2 (by norm_num) hS hSU
    (measurable_freshShellNeumannGradL2 Q sigmaInv n m e wN hwN)
    (w := fun omega => (wN omega).toH1Function) fun _ => rfl

end

end Algsuperdiff.Section3.Provider.Diffusivity.Corrector
