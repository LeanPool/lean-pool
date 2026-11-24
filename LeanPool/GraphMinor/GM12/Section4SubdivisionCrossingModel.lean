/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4SubdivisionStraightness
public import LeanPool.GraphMinor.GM12.Section4CrossingLineModel
public import LeanPool.GraphMinor.GM12.Section4CrossingPoints

/-!
# The local crossing model of the subdivided source

For XII (4.5), claim (1), page 253, an old crossing lies on two
inner chords and hence in the open unit disc. Select the new
subdivision piece on each old edge that contains the crossing.
Each piece agrees locally with its old supporting line. The
distinct supporting lines give continuous real-linear crossing
coordinates on a common open neighborhood.
-/

public section

namespace GraphMinor.GM12

open Set Surface Metric

/-- Every crossing of the source subdivision has an actual
local straight-line coordinate model, derived from the chord
construction and subdivision equations. This supplies the
local input to the crossing-disc construction in XII (4.5),
claim (1), page 253. -/
theorem exists_subdivision_crossing_model {α : Type*} {n : ℕ}
    (V : α → ℂ) (E : Fin n → Set ℂ) (s : Fin n × Bool → ℝ)
    (hinj : Function.Injective (fun q => (ee (s q) : ℂ)))
    (hchord : ∀ e, E e ∩ closedBall 0 1 =
      segment ℝ (ee (s (e, false)) : ℂ) (ee (s (e, true)) : ℂ))
    (hEinter : ∀ e f, e ≠ f → E e ∩ E f ⊆
      (segment ℝ (ee (s (e, false)) : ℂ) (ee (s (e, true)) : ℂ) ∩
        segment ℝ (ee (s (f, false)) : ℂ) (ee (s (f, true)) : ℂ)) ∪ range V)
    (k : Fin n → ℕ) (w : ∀ e, Fin (k e + 1) → ℂ) (P : ∀ e, Fin (k e) → Set ℂ)
    (hline : ∀ e i, IsLineWithEnds (P e i) (w e i.castSucc) (w e i.succ))
    (hcover : ∀ e, (⋃ i, P e i) = E e)
    (havoid : ∀ e i, w e i ∉ E e ∩ edgeMeetingPoints V E)
    (hinter : ∀ e i j, i ≠ j → P e i ∩ P e j ⊆ range (w e))
    {x : ℂ} (hx : x ∈ edgeMeetingPoints V E) :
    ∃ (e f : Fin n) (i : Fin (k e)) (j : Fin (k f)), e ≠ f ∧ x ∈ P e i ∩ P f j ∧
      ∃ (A : ℂ ≃L[ℝ] ℂ) (U : Set ℂ), IsOpen U ∧ x ∈ U ∧
        P e i ∩ U = (line[ℝ, x, x + A 1] : Set ℂ) ∩ U ∧
        P f j ∩ U = (line[ℝ, x, x + A Complex.I] : Set ℂ) ∩ U := by
  have hxM := hx
  obtain ⟨e, f, hef, hxE, hxV⟩ := hx
  let a := fun q : Fin n × Bool => (ee (s q) : ℂ)
  have hab : a (e, false) ≠ a (e, true) := by
    intro h
    exact Bool.false_ne_true (congrArg Prod.snd (hinj h))
  have hcd : a (f, false) ≠ a (f, true) := by
    intro h
    exact Bool.false_ne_true (congrArg Prod.snd (hinj h))
  have hcross : ∀ b c : Bool, a (e, b) ≠ a (f, c) := by
    intro b c h
    exact hef (congrArg Prod.fst (hinj h))
  have hunit : ∀ q, ‖a q‖ = 1 := by intro q; simp [a]
  have hxchords := (hEinter e f hef hxE).resolve_right hxV
  have hxB : x ∈ ball (0 : ℂ) 1 := unit_chord_inter_subset_openBall
    (hunit (e, false)) (hunit (e, true)) (hunit (f, false)) (hunit (f, true))
    hab hcd (hcross false false) (hcross false true) (hcross true false) (hcross true true) hxchords
  have hxeL : x ∈ line[ℝ, a (e, false), a (e, true)] :=
    (line[ℝ, a (e, false), a (e, true)]).convex.segment_subset
      (left_mem_affineSpan_pair _ _ _) (right_mem_affineSpan_pair _ _ _) hxchords.1
  have hxfL : x ∈ line[ℝ, a (f, false), a (f, true)] :=
    (line[ℝ, a (f, false), a (f, true)]).convex.segment_subset
      (left_mem_affineSpan_pair _ _ _) (right_mem_affineSpan_pair _ _ _) hxchords.2
  obtain ⟨i, hxi⟩ := mem_iUnion.mp ((hcover e).symm ▸ hxE.1)
  obtain ⟨j, hxj⟩ := mem_iUnion.mp ((hcover f).symm ▸ hxE.2)
  obtain ⟨U, hU, hxU, hPU⟩ := exists_open_subdivision_line_agreement
    (E e) (edgeMeetingPoints V E) (w e) (P e) (hline e) (hcover e) (havoid e) (hinter e)
    (hunit (e, false)) (hunit (e, true)) hab (hchord e) ⟨hxi, hxE.1, hxM⟩ hxB
  obtain ⟨W, hW, hxW, hPW⟩ := exists_open_subdivision_line_agreement
    (E f) (edgeMeetingPoints V E) (w f) (P f) (hline f) (hcover f) (havoid f) (hinter f)
    (hunit (f, false)) (hunit (f, true)) hcd (hchord f) ⟨hxj, hxE.2, hxM⟩ hxB
  have hne := lines_ne_of_distinct_unit_ports (a (e, true)) (hunit (e, false))
    (hunit (f, false)) (hunit (f, true)) hcd (hcross false false) (hcross false true)
  obtain ⟨A, hAe, hAf⟩ := exists_cross_coordinates_for_chords
    (hunit (e, false)) (hunit (f, false)) hxB hxeL hxfL hne
  refine ⟨e, f, i, j, hef, ⟨hxi, hxj⟩, A, U ∩ W, hU.inter hW, ⟨hxU, hxW⟩, ?_, ?_⟩
  · rw [← inter_assoc, hPU]
    rw [← hAe, inter_assoc]
  · rw [inter_comm U W, ← inter_assoc, hPW]
    rw [← hAf, inter_assoc]

end GraphMinor.GM12
