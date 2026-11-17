/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.ModifiedSubtileOccurrenceInterpretation
public import LeanPool.ApollonianSuperharmonic.SubtileOccurrenceInterpretation
public import LeanPool.ApollonianSuperharmonic.TileCellComplementCovariance
public import Mathlib.Init


/-!
# ModifiedSubtileFacts

Shared facts adapted from Wesley Pegden's Apache-2.0 Trellis formalization.
-/

@[expose] public section

namespace ApollonianSuperharmonic
namespace ModifiedSubtileFacts

/-- The modified A occurrence is the translated cell complement. -/
theorem modifiedA (P : Fin 3 → Bool → ProtoTile) (O : ProtoTile) (u v : GaussianInt)
    (m n : Int) :
    ModifiedSubtileOccurrenceInterpretation P O u v ⟨.A, m, n⟩ =
      TileCellComplement (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩)
        (TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) * v)) := by
  change TileTranslation (TileCellComplement (P 0 true) O)
    ((m : GaussianInt) * u + (n : GaussianInt) * v) = _
  rw [(TileCellComplementCovariance _ _ _).1]
  rfl

end ModifiedSubtileFacts
end ApollonianSuperharmonic

end
