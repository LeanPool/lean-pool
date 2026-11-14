/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.ProperBandQuadruple
public import Mathlib.Init


/-!
# BandQuadrupleCyclicRotation

Shared facts adapted from Wesley Pegden's Apache-2.0 Trellis formalization.
-/

@[expose] public section

namespace ApollonianSuperharmonic
namespace BandQuadrupleCyclicRotation

/-- Cyclically reordering the three parents preserves properness. -/
theorem proper : ∀ (q : Fin 4 → CircleCoordinates), ProperBandQuadruple q →
    ∀ (r : Fin 3),
    let qrot : Fin 4 → CircleCoordinates :=
      ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
    ProperBandQuadruple qrot := by
  classical
  intro q hq r qrot
  have hqrotSemi : SemiProperQuadruple qrot := by
    fin_cases r
    · convert hq.1 using 1; funext j; fin_cases j <;> simp [qrot]
    · convert SemiProperQuadruple.rotate hq.1 using 1;
        funext j; fin_cases j <;> simp [qrot]
    · convert SemiProperQuadruple.rotate
          (SemiProperQuadruple.rotate hq.1) using 1;
        funext j; fin_cases j <;> simp [qrot]
  refine ⟨hqrotSemi, ?_⟩
  intro j
  fin_cases r <;> fin_cases j <;> simp [qrot]
  · simpa using hq.2 (0 : Fin 3)
  · simpa using hq.2 (1 : Fin 3)
  · simpa using hq.2 (2 : Fin 3)
  · simpa using hq.2 (1 : Fin 3)
  · simpa using hq.2 (2 : Fin 3)
  · simpa using hq.2 (0 : Fin 3)
  · simpa using hq.2 (2 : Fin 3)
  · simpa using hq.2 (0 : Fin 3)
  · simpa using hq.2 (1 : Fin 3)

end BandQuadrupleCyclicRotation
end ApollonianSuperharmonic

end
