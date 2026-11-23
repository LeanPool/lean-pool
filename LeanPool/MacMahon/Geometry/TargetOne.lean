/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
-- Modified for Lean Pool integration.
module

public import LeanPool.MacMahon.Definitions
import LeanPool.MacMahon.Geometry.FaceMatching

/-!
# Face and corner matching for targets in tableau row 1
-/

@[expose] public section

namespace MacMahon

theorem face_corner_10 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 1 0 k) ↔ ∃ r : Fin 24, FaceFits (1, 0) p k r := by
  as_aux_lemma => exact face_corner_of_ne 1 0 (by decide)

theorem face_corner_12 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 1 2 k) ↔ ∃ r : Fin 24, FaceFits (1, 2) p k r := by
  as_aux_lemma => exact face_corner_of_ne 1 2 (by decide)

theorem face_corner_13 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 1 3 k) ↔ ∃ r : Fin 24, FaceFits (1, 3) p k r := by
  as_aux_lemma => exact face_corner_of_ne 1 3 (by decide)

theorem face_corner_14 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 1 4 k) ↔ ∃ r : Fin 24, FaceFits (1, 4) p k r := by
  as_aux_lemma => exact face_corner_of_ne 1 4 (by decide)

theorem face_corner_15 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 1 5 k) ↔ ∃ r : Fin 24, FaceFits (1, 5) p k r := by
  as_aux_lemma => exact face_corner_of_ne 1 5 (by decide)

end MacMahon
