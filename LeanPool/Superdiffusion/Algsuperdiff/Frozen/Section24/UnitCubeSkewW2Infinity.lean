/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section24.LInfSkewMatrixFieldOn
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MultiscaleEllipticity.Public
public import LeanPool.HighContrastHomogenization.Support.Sobolev.WeakDerivatives

/-!
# UnitCubeSkewW2Infinity

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

open HCPolySupport HCPolySupport.Book.Ch02 MeasureTheory
open scoped ENNReal

-- FROZEN-STATEMENT-BEGIN
structure Algsuperdiff.Frozen.Section24.UnitCubeSkewW2Infinity (d : ℕ) where
  toLInfSkewMatrixFieldOn :
    Algsuperdiff.Frozen.Section24.LInfSkewMatrixFieldOn
      (cubeDomain (originCube d 0))
  firstDeriv : Vec d → Vec d →L[ℝ] Mat d
  secondDeriv : Vec d → Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)
  firstDeriv_memLp : ∀ k i j : Fin d,
    MemLp (fun x => firstDeriv x (basisVec k) i j) ∞
      (volumeMeasureOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))
  secondDeriv_memLp : ∀ l k i j : Fin d,
    MemLp (fun x => secondDeriv x (basisVec l) (basisVec k) i j) ∞
      (volumeMeasureOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))
  hasWeakPartialDeriv_value : ∀ k i j : Fin d,
    HasWeakPartialDerivOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)) k
      (fun x => toLInfSkewMatrixFieldOn.1.1 x i j)
      (fun x => firstDeriv x (basisVec k) i j)
  hasWeakPartialDeriv_firstDeriv : ∀ l k i j : Fin d,
    HasWeakPartialDerivOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)) l
      (fun x => firstDeriv x (basisVec k) i j)
      (fun x => secondDeriv x (basisVec l) (basisVec k) i j)
-- FROZEN-STATEMENT-END
