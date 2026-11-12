/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.SubtileOccurrenceInterpretation
public import LeanPool.ApollonianSuperharmonic.TileQuarterTurn
public import LeanPool.ApollonianSuperharmonic.TileReflection

-- [TABLET NODE: SubtileOccurrenceInterpretationCovariance]

/-!
# SubtileOccurrenceInterpretationCovariance

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem SubtileOccurrenceInterpretationCovariance
    (S : Fin 3 → Bool → ProtoTile) (u v a : GaussianInt)
    (o : PeriodicSubtileIndex) :
    TileTranslation (SubtileOccurrenceInterpretation S u v o) a =
        SubtileOccurrenceInterpretation
          (fun i s => TileTranslation (S i s) a) u v o ∧
      TileQuarterTurn (SubtileOccurrenceInterpretation S u v o) =
        SubtileOccurrenceInterpretation
          (fun i s => TileQuarterTurn (S i s))
          (GaussianQuarterTurn u) (GaussianQuarterTurn v) o ∧
      TileReflection (SubtileOccurrenceInterpretation S u v o) =
        SubtileOccurrenceInterpretation
          (fun i s => TileReflection (S i s))
          (GaussianReflection u) (GaussianReflection v) o := by
-- BODY
  have translation_commute : ∀ (T : ProtoTile) (x y : GaussianInt),
      TileTranslation (TileTranslation T x) y =
        TileTranslation (TileTranslation T y) x := by
    intro T x y
    cases T with
    | mk cells anchor =>
      have map : (fun z : GaussianInt => (z + x) + y) =
          (fun z : GaussianInt => (z + y) + x) := by
        funext z
        simp [add_comm, add_left_comm]
      apply congrArg₂ (fun c : FiniteTile => fun d : GaussianInt =>
        ProtoTile.mk c d)
      · simp [TileTranslation, GaussianTranslation, Finset.image_image,
          Function.comp_def, map]
      · simp [TileTranslation, GaussianTranslation, add_comm,
          add_left_comm]
  have quarter_commute : ∀ (T : ProtoTile) (x : GaussianInt),
      TileQuarterTurn (TileTranslation T x) =
        TileTranslation (TileQuarterTurn T) (GaussianQuarterTurn x) := by
    intro T x
    cases T with
    | mk cells anchor =>
      have map : (fun z : GaussianInt => GaussianQuarterTurn (z + x) - 1) =
          (fun z : GaussianInt => (GaussianQuarterTurn z - 1) +
            GaussianQuarterTurn x) := by
        funext z
        ext <;> simp [GaussianQuarterTurn, add_comm]; ring
      apply congrArg₂ (fun c : FiniteTile => fun d : GaussianInt =>
        ProtoTile.mk c d)
      · simp [TileQuarterTurn, TileTranslation, GaussianTranslation,
          Finset.image_image, Function.comp_def, map]
      · simp [TileQuarterTurn, TileTranslation, GaussianTranslation,
          GaussianQuarterTurn, add_comm]
  have reflection_commute : ∀ (T : ProtoTile) (x : GaussianInt),
      TileReflection (TileTranslation T x) =
        TileTranslation (TileReflection T) (GaussianReflection x) := by
    intro T x
    cases T with
    | mk cells anchor =>
      have map : (fun z : GaussianInt => GaussianReflection (z + x) -
          ⟨0, 1⟩) =
          (fun z : GaussianInt => (GaussianReflection z - ⟨0, 1⟩) +
            GaussianReflection x) := by
        funext z
        ext <;> simp [GaussianReflection, add_comm]; ring
      apply congrArg₂ (fun c : FiniteTile => fun d : GaussianInt =>
        ProtoTile.mk c d)
      · simp [TileReflection, TileTranslation, GaussianTranslation,
          Finset.image_image, Function.comp_def, map]
      · simp [TileReflection, TileTranslation, GaussianTranslation,
          GaussianReflection, add_comm]
  have quarter_linear : ∀ (m n : Int) (x y : GaussianInt),
      GaussianQuarterTurn (m * x + n * y) =
        m * GaussianQuarterTurn x + n * GaussianQuarterTurn y := by
    intro m n x y
    ext <;> simp [GaussianQuarterTurn]; ring
  have reflection_linear : ∀ (m n : Int) (x y : GaussianInt),
      GaussianReflection (m * x + n * y) =
        m * GaussianReflection x + n * GaussianReflection y := by
    intro m n x y
    ext <;> simp [GaussianReflection]; ring
  cases o with
  | mk label first second =>
    cases label <;>
      simp only [SubtileOccurrenceInterpretation, Fin.isValue]
      <;> rw [translation_commute]
      <;> rw [quarter_commute]
      <;> rw [reflection_commute]
      <;> simp [quarter_linear, reflection_linear]

end ApollonianSuperharmonic

end
