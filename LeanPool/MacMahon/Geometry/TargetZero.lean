/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
-- Modified for Lean Pool integration.
module

public import LeanPool.MacMahon.Definitions

/-!
# Face and corner matching for targets in tableau row 0
-/

@[expose] public section

namespace MacMahon

theorem face_corner_01 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 0 1 k) ↔ ∃ r : Fin 24, FaceFits (0, 1) p k r := by
  decide +kernel

theorem face_corner_02 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 0 2 k) ↔ ∃ r : Fin 24, FaceFits (0, 2) p k r := by
  decide +kernel

theorem face_corner_03 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 0 3 k) ↔ ∃ r : Fin 24, FaceFits (0, 3) p k r := by
  decide +kernel

theorem face_corner_04 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 0 4 k) ↔ ∃ r : Fin 24, FaceFits (0, 4) p k r := by
  decide +kernel

theorem face_corner_05 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 0 5 k) ↔ ∃ r : Fin 24, FaceFits (0, 5) p k r := by
  decide +kernel

end MacMahon
