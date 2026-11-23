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
# Face and corner matching for targets in tableau row 3
-/

@[expose] public section

namespace MacMahon

theorem face_corner_30 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 3 0 k) ↔ ∃ r : Fin 24, FaceFits (3, 0) p k r := by
  as_aux_lemma => exact face_corner_of_ne 3 0 (by decide)

theorem face_corner_31 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 3 1 k) ↔ ∃ r : Fin 24, FaceFits (3, 1) p k r := by
  as_aux_lemma => exact face_corner_of_ne 3 1 (by decide)

theorem face_corner_32 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 3 2 k) ↔ ∃ r : Fin 24, FaceFits (3, 2) p k r := by
  as_aux_lemma => exact face_corner_of_ne 3 2 (by decide)

theorem face_corner_34 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 3 4 k) ↔ ∃ r : Fin 24, FaceFits (3, 4) p k r := by
  as_aux_lemma => exact face_corner_of_ne 3 4 (by decide)

theorem face_corner_35 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 3 5 k) ↔ ∃ r : Fin 24, FaceFits (3, 5) p k r := by
  as_aux_lemma => exact face_corner_of_ne 3 5 (by decide)

end MacMahon
