/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
-- Modified for Lean Pool integration.
module

public import LeanPool.MacMahon.Definitions

/-!
# Face and corner matching for targets in tableau row 2
-/

@[expose] public section

namespace MacMahon

theorem face_corner_20 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 2 0 k) ↔ ∃ r : Fin 24, FaceFits (2, 0) p k r := by
  decide +kernel

theorem face_corner_21 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 2 1 k) ↔ ∃ r : Fin 24, FaceFits (2, 1) p k r := by
  decide +kernel

theorem face_corner_23 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 2 3 k) ↔ ∃ r : Fin 24, FaceFits (2, 3) p k r := by
  decide +kernel

theorem face_corner_24 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 2 4 k) ↔ ∃ r : Fin 24, FaceFits (2, 4) p k r := by
  decide +kernel

theorem face_corner_25 : ∀ p : Pair, ∀ k : Slot,
    HasCorner p (cornerAt 2 5 k) ↔ ∃ r : Fin 24, FaceFits (2, 5) p k r := by
  decide +kernel

end MacMahon
