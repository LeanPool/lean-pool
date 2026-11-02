/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.MacMahon.Definitions

/-!
# Face and corner matching for targets in tableau row 4
-/

@[expose] public section

namespace MacMahon

theorem face_corner_40 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 4 0 k) ↔ ∃ r : Fin 24, FaceFits (4, 0) p k r := by
  decide +kernel

theorem face_corner_41 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 4 1 k) ↔ ∃ r : Fin 24, FaceFits (4, 1) p k r := by
  decide +kernel

theorem face_corner_42 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 4 2 k) ↔ ∃ r : Fin 24, FaceFits (4, 2) p k r := by
  decide +kernel

theorem face_corner_43 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 4 3 k) ↔ ∃ r : Fin 24, FaceFits (4, 3) p k r := by
  decide +kernel

theorem face_corner_45 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 4 5 k) ↔ ∃ r : Fin 24, FaceFits (4, 5) p k r := by
  decide +kernel

end MacMahon
