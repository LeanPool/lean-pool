/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSeamFluxHalfBundle
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSeamFluxIdentification
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSeamSpineBase
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.ClassicalGradient

/-!
# HomSeamGradSpine

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The clause supplier and the spine endpoint, re-threaded at the gradient binder

## What this file supplies

The display's classical-gradient binder is threaded through
the supply and the twelve-conjunct core.  This file carries it the rest of the
way to the spine's clause supplier:

```text
  HomSpineClauseSupplierAtGrad                     -- the supplier, gated
```

Each is the strict re-threading of its original: the binder list of the
per-`omega` body gains

```text
  HasGradientOn (openCubeSet (originCube d m)) h.toFun h.grad ->
```

after the `KhInf` sup binder, and the proof passes it straight through.  The
`E_B` witness, the two moment clauses and the `sigmaBar` clause of the endpoint
are BINDER-FREE and are re-used, not re-proved.
-/

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03
open HCPolySupport.Book.Ch03.ABK26 MeasureTheory
open Algsuperdiff.Section3
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The clause supplier, gated -/

/-- The spine's clause supplier with the display's
classical-gradient binder threaded through. -/
def HomSpineClauseSupplierAtGrad (M : ABKModel d) (Cgap : ℝ)
    (Y : Cutoff.CutoffSample d → ℝ≥0∞) (m : ℤ) (sb : {s : ℝ // 0 < s})
    (sigmaBarM Kabs : ℝ) (omega : Cutoff.CutoffSample d) : Prop :=
  ∀ L : ℤ, m ≤ L →
    ∀ (u v h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d)
      (Kg Kh KhInf : ℝ),
      IsDirichletSolutionOn (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
        (originCube d m) u h g →
      IsDirichletSolutionOn (fun _ => sigmaBarM • (1 : Mat d)) (originCube d m) v h g →
      HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kg g →
      HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kh h.grad →
      (∀ x ∈ openCubeSet (originCube d m), ‖h.grad x‖ ≤ KhInf) →
      HasGradientOn (openCubeSet (originCube d m)) h.toFun h.grad →
      ∃ D : ℝ, 0 ≤ D ∧
        ENNReal.ofReal D ≤ ethmB M Cgap Y m (homN M m) sb omega ∧
        (∀ᵐ x ∂(volume.restrict (openCubeSet (originCube d m))),
          Real.rpow 3 (-(m : ℝ)) * |u.toFun x - v.toFun x| ≤
            Kabs * D *
              dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh) ∧
        |volumeAverage (openCubeSet (originCube d m))
              (fun y => M.nu * vecNormSq (u.grad y)) -
            volumeAverage (openCubeSet (originCube d m))
              (fun y => sigmaBarM * vecNormSq (v.grad y))| ≤
          Kabs * D *
            energyBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh ^ (2 : ℕ)

end

end Algsuperdiff.Section4.Provider.Homogenization
