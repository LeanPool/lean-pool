/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponsePz
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseSwitchActualPerCube

/-!
# PrincipalEnergyAverage

The common descendant average used by the principal-response closure and the
localization endpoint. Its lower imports keep those two consumer lanes separate.
-/

@[expose] public section

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The descendant average of the annealed localized principal energy at `(n, n+h)`. -/
def principalEnergyAverage (M : ABKModel d) (n : ℤ) (h : ℕ) (Kc : ℤ) (j : ℕ)
    (e e' : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d Kc)))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d Kc))) : ℝ :=
  descendantsAverage (originCube d Kc) j
    (fun R => ∫ omega : CutoffSample d,
      switchCubeEnergy M (n + (h : ℤ)) R
        (principalPz (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e e' R
          (wD omega.val) (wN omega.val)) omega
      ∂(cutoffSampleLaw M).toMeasure)

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
