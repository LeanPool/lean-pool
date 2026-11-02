/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.MacMahon.Definitions

/-!
# Face and corner matching for targets in tableau row 5
-/

@[expose] public section

namespace MacMahon

theorem face_corner_50 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 5 0 k) ↔ ∃ r : Fin 24, FaceFits (5, 0) p k r := by
  decide +kernel

theorem face_corner_51 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 5 1 k) ↔ ∃ r : Fin 24, FaceFits (5, 1) p k r := by
  decide +kernel

theorem face_corner_52 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 5 2 k) ↔ ∃ r : Fin 24, FaceFits (5, 2) p k r := by
  decide +kernel

theorem face_corner_53 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 5 3 k) ↔ ∃ r : Fin 24, FaceFits (5, 3) p k r := by
  decide +kernel

theorem face_corner_54 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 5 4 k) ↔ ∃ r : Fin 24, FaceFits (5, 4) p k r := by
  decide +kernel

end MacMahon
