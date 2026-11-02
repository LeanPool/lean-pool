/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
-- Modified for Lean Pool integration.
module

public import LeanPool.MacMahon.Definitions

/-!
# Proper rotations and cube varieties
-/

@[expose] public section
namespace MacMahon

/-- Faces are +x, -x, +y, -y, +z, -z. -/
theorem faceOne_bound : 1 < 6 := by decide

/-- The face in the opposite coordinate direction. -/
def opposite (f : Fin 6) : Fin 6 :=
  if f.val % 2 = 0 then f + ⟨1, faceOne_bound⟩ else f - ⟨1, faceOne_bound⟩
/-- The face map determined by the images of the three positive coordinate axes. -/
def fromAxes (a b c : Fin 6) : Fin 6 → Fin 6 :=
  ![a, opposite a, b, opposite b, c, opposite c]

/-- Distinct coordinate axes and determinant +1. -/
def ValidAxes (a b c : Fin 6) : Prop :=
  a.val / 2 ≠ b.val / 2 ∧ a.val / 2 ≠ c.val / 2 ∧ b.val / 2 ≠ c.val / 2 ∧
  (a.val % 2 + b.val % 2 + c.val % 2) % 2 =
    ((if a.val / 2 > b.val / 2 then 1 else 0) +
     (if a.val / 2 > c.val / 2 then 1 else 0) +
     (if b.val / 2 > c.val / 2 then 1 else 0)) % 2
instance (a b c : Fin 6) : Decidable (ValidAxes a b c) := by
  unfold ValidAxes; infer_instance

/-- A face map induced by a determinant-positive signed-axis permutation. -/
def ProperRotation (r : Fin 6 → Fin 6) : Prop :=
  ∃ a b c, ValidAxes a b c ∧ r = fromAxes a b c

theorem rotation_table_valid : ∀ n : Fin 24,
    ValidAxes (rotations n 0) (rotations n 2) (rotations n 4) ∧
    rotations n = fromAxes (rotations n 0) (rotations n 2) (rotations n 4) := by
  decide +kernel

theorem rotation_table_complete : ∀ a b c : Fin 6, ValidAxes a b c →
    ∃ n : Fin 24, fromAxes a b c = rotations n := by decide +kernel

theorem proper_rotation_iff (r : Fin 6 → Fin 6) :
    ProperRotation r ↔ ∃ n : Fin 24, r = rotations n := by
  constructor
  · rintro ⟨a, b, c, h, rfl⟩
    exact rotation_table_complete a b c h
  · rintro ⟨n, rfl⟩
    exact ⟨_, _, _, rotation_table_valid n⟩

theorem rotations_bijective : ∀ n : Fin 24, Function.Bijective (rotations n) := by
  decide +kernel

theorem rotations_distinct : Function.Injective rotations := by decide +kernel

theorem face_colours_valid : ∀ i j : Label, i ≠ j →
    Function.Injective (faceColours i j) ∧ ∀ f : Fin 6, faceColours i j f ≠ 0 := by
  decide +kernel

/-- Different Conway labels represent different rotation classes. -/
theorem varieties_distinct : ∀ i j : Label, i ≠ j → ∀ u v : Label, u ≠ v →
    ∀ r : Fin 24, (∀ f : Fin 6, faceColours i j (rotations r f) = faceColours u v f) →
    i = u ∧ j = v := by decide +kernel

theorem rotation_inverse : ∀ r : Fin 24, ∃ s : Fin 24,
    ∀ f : Fin 6, rotations r (rotations s f) = f := by decide +kernel

theorem rotation_composition : ∀ r s : Fin 24, ∃ t : Fin 24,
    ∀ f : Fin 6, rotations t f = rotations r (rotations s f) := by decide +kernel

/-- The three outward faces at each of the eight binary cube positions. -/
theorem exposed_face_rule : ∀ k : Slot, ∀ d : Fin 3,
    (exposedFaces k d).val = 2 * d.val + (k.val / 2^(2-d.val)) % 2 := by decide +kernel

end MacMahon
