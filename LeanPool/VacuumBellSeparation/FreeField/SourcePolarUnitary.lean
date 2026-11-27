/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SourcePolarUnitaryDefs
public import LeanPool.VacuumBellSeparation.FreeField.PolarUnitary
public import LeanPool.VacuumBellSeparation.FreeField.StandardSourceSpace

/-!
# Polar decomposition of the actual completed local source map

The constructed unitary is obtained from the proved source-map injectivity
and dense range. The factorization uses the literal physical source Gram
operator and its CFC square root, including spectra accumulating at zero.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory

variable {m : ℝ} (hm : 0 < m) (U : Set (EuclideanSpace ℝ (Fin 3)))

theorem sourcePolarUnitary_sqrt_gram (hU : Bornology.IsBounded U)
    (hopen : IsOpen U) (hne : U.Nonempty) (z : ComplexSourceHilbert hm U) :
    sourcePolarUnitary hm U hU hopen hne (CFC.sqrt (sourceGram hm U) z) =
      complexSourceMap hm U z :=
  polarUnitary_polarGramRoot (complexSourceMap hm U) _ _ z

theorem sourcePolarUnitary_factorization (hU : Bornology.IsBounded U)
    (hopen : IsOpen U) (hne : U.Nonempty) :
    (sourcePolarUnitary hm U hU hopen hne).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (CFC.sqrt (sourceGram hm U)) = complexSourceMap hm U := by
  apply ContinuousLinearMap.ext
  intro z
  exact sourcePolarUnitary_sqrt_gram hm U hU hopen hne z

end VacuumBellSeparation
