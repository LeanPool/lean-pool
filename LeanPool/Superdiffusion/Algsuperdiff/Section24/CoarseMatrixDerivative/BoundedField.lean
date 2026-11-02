/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section24.LInfMatrixFieldOn
public import LeanPool.HighContrastHomogenization.Support.Sobolev.PotentialSolenoidalL2

/-!
# BoundedField

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Bounded perturbations for the coarse-matrix derivative

The source carrier is frozen in `LInfMatrixFieldOn`.  This module records the
two analytic consequences needed by the construction of `D_h`: an `L∞` matrix
field maps vector `L²` fields to vector `L²`, and hence the exact displayed
pairing in `e.def.Dh` is integrable for arbitrary solutions.
-/

namespace Algsuperdiff.Section24

open HCPolySupport HCPolySupport.Book.Ch02 MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

theorem memVectorL2_matVecMul_of_lInfMatrixFieldOn
    (U : Domain d) (h : Algsuperdiff.Frozen.Section24.LInfMatrixFieldOn U)
    {f : Vec d → Vec d} (hf : MemVectorL2 (U : Set (Vec d)) f) :
    MemVectorL2 (U : Set (Vec d)) (fun x => matVecMul (h.1 x) (f x)) := by
  rw [MemVectorL2] at hf ⊢
  refine (memLp_pi_iff).2 ?_
  intro i
  have hsum :
      MemLp (fun x : Vec d => ∑ j : Fin d, h.1 x i j * f x j) 2
        (volumeMeasureOn (U : Set (Vec d))) := by
    refine memLp_finsetSum (s := Finset.univ)
      (f := fun j => fun x : Vec d => h.1 x i j * f x j) ?_
    intro j _
    exact (h.2 i j).fun_mul (r := 2) ((memLp_pi_iff.mp hf) j)
  simpa [matVecMul] using hsum

end

end Algsuperdiff.Section24
