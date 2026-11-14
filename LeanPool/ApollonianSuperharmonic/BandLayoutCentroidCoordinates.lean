/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralLayoutCertificate
public import Mathlib.Init


/-!
# BandLayoutCentroidCoordinates

Shared facts adapted from Wesley Pegden's Apache-2.0 Trellis formalization.
-/

@[expose] public section

namespace ApollonianSuperharmonic
namespace BandLayoutCentroidCoordinates

/-- Shared doubledCenter fact. -/
theorem doubledCenter :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (layout : BandOrderedGeneralLayoutCertificate q cfg
            C T), ∀ (u : GaussianInt), (GaussianRealPoint u = ((TileCentroid (layout.P (0 : Fin
            (3 : ℕ)) false)).1 + (TileCentroid (layout.P (0 : Fin (3 : ℕ)) false)).2,
            (TileCentroid (layout.P (0 : Fin (3 : ℕ)) false)).2 - (TileCentroid (layout.P (0 :
            Fin (3 : ℕ)) false)).1)) → (
        let w := BandVectors.1 (q 3) (q 2)
        let t : GaussianInt :=
          ⟨u.re - u.im + w.re + w.im, u.re + u.im + w.im - w.re⟩
        (t.re : Real) = 2 * (TileCentroid T).1 ∧ (t.im : Real) = 2 * (TileCentroid T).2) ) := by
  classical
  intro q cfg C T layout u hu w t
  have hur := congrArg Prod.fst hu
  have hui := congrArg Prod.snd hu
  have hc := (layout.outer_occurrence 0 false).2.2
  have hcr := congrArg Prod.fst hc
  have hci := congrArg Prod.snd hc
  norm_num [GaussianRealPoint] at hur hui hcr hci
  simp only [← GaussianInt.intCast_re, ← GaussianInt.intCast_im] at hur hui hcr hci
  dsimp [t, w]
  push_cast
  constructor <;> linarith





end BandLayoutCentroidCoordinates
end ApollonianSuperharmonic

end
