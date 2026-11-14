/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralLayoutCertificate

/-!
# BandOriginalParentContainment

Shared facts adapted from Wesley Pegden's Apache-2.0 Trellis formalization.
-/

@[expose] public section

namespace ApollonianSuperharmonic
namespace BandOriginalParentContainment

/-- Shared positiveParent fact. -/
theorem positiveParent :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := cert.P
        let O := cert.O
        O.cells ⊆ (P 0 true).cells ) := by
  classical
  intro q cfg C₀ T cert P O
  change cert.O.cells ⊆ (cert.P 0 true).cells
  rw [cert.precursor_eq]
  intro x hx
  exact (cert.plus_union x).2 ⟨0, false, hx⟩

/-- Shared negativeParent fact. -/
theorem negativeParent :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := cert.P
        let O := cert.O
        O.cells ⊆ (P 0 false).cells ) := by
  classical
  intro q cfg C₀ T cert P O
  change cert.O.cells ⊆ (cert.P 0 false).cells
  rw [cert.precursor_cells]
  intro x hx
  exact (cert.minus_union x).2 ⟨0, true, hx⟩

end BandOriginalParentContainment
end ApollonianSuperharmonic

end
