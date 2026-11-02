/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootClauseBArith
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenCaccFinalChain
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepFourSeminormComparisons
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenSigmaBar

/-!
# RootClauseBInputs

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


namespace Algsuperdiff.Section4.Provider.Regularity

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03 MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 3.  at the full cube: the `hgradE` identity -/

/-- proved the `ν`-identification at the Caccioppoli core `□_{j-2}`
(`sqrt_localizedCoeffEnergyValue_core_eq_nuGradNorm`); the chain's `hgradE`
slot needs it at `openCubeSet □_j`, which is the same three-line identity — the
symmetric part of the flux-corrected family IS `ν I`, the frame moves by the
translation transport, and the window IS the translate on the interior branch. -/
theorem forcedSolutionEnergyNorm_fluxCorrected_eq_nuGradNorm (M : ABKModel d)
    (L mf m j : ℤ) (Qf : TriadicCube d) {z : Vec d} (omega : Cutoff.CutoffSample d)
    {g : Vec d → Vec d}
    (u : ForcedCubeSolution (originCube d j)
      (Support.fluxCorrectedCoeffFamily M L mf Qf
        (Cutoff.translateCutoffSample z omega)) g)
    (G : Vec d → Vec d) (hg : ∀ y, u.toH1.grad y = G (y + z))
    (hz : z ∈ openCubeSet (originCube d (m - 1))) (hj : j ≤ m - 1) :
    forcedSolutionEnergyNorm (originCube d j)
        (Support.fluxCorrectedCoeffFamily M L mf Qf
          (Cutoff.translateCutoffSample z omega)) u =
      stepSevenNuGradNorm (M.nu : ℝ) (truncatedWindow z m j) G := by
  rw [forcedSolutionEnergyNorm, h1EnergyNormOnCube, stepSevenNuGradNorm]
  congr 1
  rw [localizedCoeffEnergyValue_fluxCorrectedCoeffFamily_eq]
  have hfun : (fun x => vecNormSq (u.toH1.grad x)) = fun x => vecNormSq (G (x + z)) := by
    funext x
    rw [hg x]
  have h1 := normalizedSetAverage_vecNormSq_translateSet z
    (openCubeSet (originCube d j)) G
  rw [truncatedWindow_eq_translateSet_of_mem_inner hz hj, hfun]
  exact congrArg (fun t : ℝ => (M.nu : ℝ) * t) h1.symm

/-! ## 4. The five `IntegrableOn` binders -/

/-- The root's `H¹(□_m)` datum is integrable on every finite-volume subset. -/
theorem integrableOn_toFun_subset {m : ℤ} (u : H1Function (openCubeSet (originCube d m)))
    {A : Set (Vec d)} (hA : A ⊆ openCubeSet (originCube d m)) (hAtop : volume A ≠ ⊤) :
    IntegrableOn u.toFun A volume :=
  integrableOn_of_memLp_two hAtop (memLp_toFun_of_subset u hA)

/-- Its square is integrable there too. -/
theorem integrableOn_sq_toFun_subset {m : ℤ}
    (u : H1Function (openCubeSet (originCube d m)))
    {A : Set (Vec d)} (hA : A ⊆ openCubeSet (originCube d m)) (hAtop : volume A ≠ ⊤) :
    IntegrableOn (fun x => u.toFun x ^ 2) A volume := by
  have h := integrableOn_sub_const_sq hAtop (memLp_toFun_of_subset u hA) 0
  simpa only [sub_zero] using h

/-- And so is its mean-subtracted square. -/
theorem integrableOn_sub_sq_toFun_subset {m : ℤ}
    (u : H1Function (openCubeSet (originCube d m)))
    {A : Set (Vec d)} (hA : A ⊆ openCubeSet (originCube d m)) (hAtop : volume A ≠ ⊤)
    (b : ℝ) :
    IntegrableOn (fun x => (u.toFun x - b) ^ 2) A volume :=
  integrableOn_sub_const_sq hAtop (memLp_toFun_of_subset u hA) b

end

end Algsuperdiff.Section4.Provider.Regularity
