/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P5064T3Rectangles
public import LeanPool.ApollonianSuperharmonic.AllowedSubtileIncidence
public import LeanPool.ApollonianSuperharmonic.SubtileOccurrenceInterpretation
public import LeanPool.ApollonianSuperharmonic.FootprintEdges
public import LeanPool.ApollonianSuperharmonic.FootprintVertices
public import LeanPool.ApollonianSuperharmonic.P5098T1SquareIntersection
public import LeanPool.ApollonianSuperharmonic.P5098T1OccurrenceSquares
public import LeanPool.ApollonianSuperharmonic.P5098T1EqualIntervals
public import LeanPool.ApollonianSuperharmonic.P5098T1ABIntervals
public import LeanPool.ApollonianSuperharmonic.P5098T1ACIntervals
public import LeanPool.ApollonianSuperharmonic.P5098T1ADIntervals
public import LeanPool.ApollonianSuperharmonic.P5098T1BCIntervals
public import LeanPool.ApollonianSuperharmonic.P5098T1BDIntervals
public import LeanPool.ApollonianSuperharmonic.P5098T1CDIntervals

-- [TABLET NODE: P5064T3RectangleContacts]

/-!
# P5064T3RectangleContacts

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5064T3RectangleContacts (r s : Nat) (hs : 2 ≤ s) (hrs : s < r) :
    let M := P5064T3Rectangles r s
    let u : GaussianInt := ⟨-(r : Int), ((r + s : Nat) : Int)⟩
    let v : GaussianInt := ⟨-(s : Int), -((r + s : Nat) : Int)⟩
    ∀ a b : PeriodicSubtileIndex, a ≠ b →
      ((FootprintEdges (SubtileOccurrenceInterpretation M u v a) ∩
          FootprintEdges (SubtileOccurrenceInterpretation M u v b)).Nonempty →
        AllowedSubtileIncidence a b) ∧
      (¬ AllowedSubtileIncidence a b →
        FootprintVertices (SubtileOccurrenceInterpretation M u v a) ∩
            FootprintVertices (SubtileOccurrenceInterpretation M u v b) = ∅ ∨
          (FootprintVertices (SubtileOccurrenceInterpretation M u v a) ∩
            FootprintVertices (SubtileOccurrenceInterpretation M u v b)).Subsingleton) := by
-- BODY
  classical
  let M := P5064T3Rectangles r s
  let u : GaussianInt := ⟨-(r : Int), ((r + s : Nat) : Int)⟩
  let v : GaussianInt := ⟨-(s : Int), -((r + s : Nat) : Int)⟩
  let occ := SubtileOccurrenceInterpretation M u v
  let d : SixSubtileLabel → Nat := fun l => match l with
    | .A | .B => r
    | .C | .D => s
    | .E | .F => 0
  let c : SixSubtileLabel → GaussianInt := fun l => match l with
    | .A => 0
    | .B => ⟨(s : Int), (s : Int)⟩
    | .C => ⟨(r : Int), 0⟩
    | .D => ⟨0, (r : Int)⟩
    | .E => ⟨(s : Int), (r + s : Nat)⟩
    | .F => ⟨(r : Int), 0⟩
  let shift (m n : Int) : GaussianInt :=
    ⟨-m * r - n * s, (r + s) * (m - n)⟩
  let corner (o : PeriodicSubtileIndex) := c o.label + shift o.first o.second
  let rank : SixSubtileLabel → Nat := fun l => match l with
    | .A => 0 | .B => 1 | .C => 2 | .D => 3 | .E => 4 | .F => 5
  have hsI : (2 : Int) ≤ s := by exact_mod_cast hs
  have hrsI : (s : Int) < r := by exact_mod_cast hrs
  have normal (o : PeriodicSubtileIndex) :
      occ o = TileTranslation (FordTile (d o.label)) (corner o) := by
    exact P5098T1OccurrenceSquares r s o
  have zero_edges (o : PeriodicSubtileIndex) (hz : d o.label = 0) :
      FootprintEdges (occ o) = ∅ := by
    rw [normal, hz]
    simp [FordTile, FordCellDomain, TileTranslation, FootprintEdges]
  have zero_vertices (o : PeriodicSubtileIndex) (hz : d o.label = 0) :
      (FootprintVertices (occ o)).Subsingleton := by
    rw [normal, hz]
    simp [FordTile, FordCellDomain, TileTranslation, FootprintVertices]
  have ordered (a b : PeriodicSubtileIndex) (hne : a ≠ b)
      (horder : rank a.label ≤ rank b.label)
      (hedge : (FootprintEdges (occ a) ∩ FootprintEdges (occ b)).Nonempty) :
      AllowedSubtileIncidence a b := by
    by_cases hza : d a.label = 0
    · simp [zero_edges a hza] at hedge
    by_cases hzb : d b.label = 0
    · simp [zero_edges b hzb] at hedge
    have hpa : 0 < d a.label := Nat.pos_of_ne_zero hza
    have hpb : 0 < d b.label := Nat.pos_of_ne_zero hzb
    have hrect := (P5098T1SquareIntersection (d a.label) (d b.label)
      hpa hpb (corner a) (corner b)).1.mp
        (by simpa only [normal] using hedge)
    have dx : (corner b - corner a).re =
        (c b.label).re - (c a.label).re -
          (b.first - a.first) * (r + s) +
          ((b.first - a.first) - (b.second - a.second)) * s := by
      dsimp [corner, shift]
      ring
    have dy : (corner b - corner a).im =
        (c b.label).im - (c a.label).im +
          (r + s) * ((b.first - a.first) - (b.second - a.second)) := by
      dsimp [corner, shift]
      ring
    rw [dx, dy] at hrect
    rcases a with ⟨la, m, n⟩
    rcases b with ⟨lb, p, t⟩
    cases la <;> cases lb
    all_goals simp only [d, c, rank, Zsqrtd.re_zero, Zsqrtd.im_zero] at hpa hpb horder hrect
    all_goals try omega
    case A.A =>
      obtain ⟨hi, hk⟩ := P5098T1EqualIntervals r s r (p - m)
        ((p - m) - (t - n)) hsI hrsI (Or.inl rfl)
        (by simpa only [sub_self, zero_sub, zero_add, neg_mul] using hrect)
      apply False.elim
      apply hne
      congr <;> omega
    case B.B =>
      obtain ⟨hi, hk⟩ := P5098T1EqualIntervals r s r (p - m)
        ((p - m) - (t - n)) hsI hrsI (Or.inl rfl)
        (by simpa only [sub_self, zero_sub, zero_add, neg_mul] using hrect)
      apply False.elim
      apply hne
      congr <;> omega
    case C.C =>
      obtain ⟨hi, hk⟩ := P5098T1EqualIntervals r s s (p - m)
        ((p - m) - (t - n)) hsI hrsI (Or.inr rfl)
        (by simpa only [sub_self, zero_sub, zero_add, neg_mul] using hrect)
      apply False.elim
      apply hne
      congr <;> omega
    case D.D =>
      obtain ⟨hi, hk⟩ := P5098T1EqualIntervals r s s (p - m)
        ((p - m) - (t - n)) hsI hrsI (Or.inr rfl)
        (by simpa only [sub_self, zero_sub, zero_add, neg_mul] using hrect)
      apply False.elim
      apply hne
      congr <;> omega
    case A.B =>
      have hrow := P5098T1ABIntervals r s (p - m) ((p - m) - (t - n))
        hsI hrsI (by simpa only [sub_zero] using hrect)
      rcases hrow with ⟨hi, hk⟩ | ⟨hi, hk⟩ | ⟨hi, hk⟩
      · have hp : p = m := by omega
        have ht : t = n := by omega
        subst p; subst t
        exact .AB m n
      · have hp : p = m := by omega
        have ht : t = n + 1 := by omega
        subst p; subst t
        exact .AB01 m n
      · have hp : p = m + 1 := by omega
        have ht : t = n + 1 := by omega
        subst p; subst t
        exact .AB11 m n
    case A.C =>
      have hrow := P5098T1ACIntervals r s (p - m) ((p - m) - (t - n))
        hsI hrsI (by simpa only [sub_zero, zero_add] using hrect)
      rcases hrow with ⟨hi, hk⟩ | ⟨hi, hk⟩
      · have hp : p = m := by omega
        have ht : t = n := by omega
        subst p; subst t
        exact .AC m n
      · have hp : p = m + 1 := by omega
        have ht : t = n + 1 := by omega
        subst p; subst t
        exact .AC11 m n
    case A.D =>
      obtain ⟨hi, hk⟩ := P5098T1ADIntervals r s (p - m) ((p - m) - (t - n))
        hsI hrsI (by simpa only [sub_zero, zero_sub, neg_mul] using hrect)
      have hp : p = m := by omega
      have ht : t = n := by omega
      subst p; subst t
      exact .AD m n
    case B.C =>
      obtain ⟨hi, hk⟩ := P5098T1BCIntervals r s (p - m) ((p - m) - (t - n))
        hsI hrsI (by simpa only [zero_sub] using hrect)
      have hp : p = m := by omega
      have ht : t = n := by omega
      subst p; subst t
      exact .BC m n
    case B.D =>
      have hrow := P5098T1BDIntervals r s (p - m) ((p - m) - (t - n))
        hsI hrsI (by simpa only [zero_sub] using hrect)
      rcases hrow with ⟨hi, hk⟩ | ⟨hi, hk⟩
      · have hp : p = m - 1 := by omega
        have ht : t = n - 1 := by omega
        subst p; subst t
        exact .BDm1m1 m n
      · have hp : p = m := by omega
        have ht : t = n := by omega
        subst p; subst t
        exact .BD m n
    case C.D =>
      obtain ⟨hi, hk⟩ := P5098T1CDIntervals r s (p - m) ((p - m) - (t - n))
        hsI hrsI (by simpa only [zero_sub, sub_zero] using hrect)
      have hp : p = m - 1 := by omega
      have ht : t = n := by omega
      subst p; subst t
      exact .CDm10 m n
  have classify (a b : PeriodicSubtileIndex) (hne : a ≠ b)
      (hedge : (FootprintEdges (occ a) ∩ FootprintEdges (occ b)).Nonempty) :
      AllowedSubtileIncidence a b := by
    rcases le_total (rank a.label) (rank b.label) with hab | hba
    · exact ordered a b hne hab hedge
    · exact .symm (ordered b a hne.symm hba (by rwa [Set.inter_comm]))
  dsimp only
  intro a b hne
  change ((FootprintEdges (occ a) ∩ FootprintEdges (occ b)).Nonempty → _) ∧ _
  refine ⟨classify a b hne, ?_⟩
  intro hnot
  right
  change (FootprintVertices (occ a) ∩ FootprintVertices (occ b)).Subsingleton
  by_cases hza : d a.label = 0
  · intro x hx y hy
    exact zero_vertices a hza hx.1 hy.1
  by_cases hzb : d b.label = 0
  · intro x hx y hy
    exact zero_vertices b hzb hx.2 hy.2
  have hno : ¬ (FootprintEdges (occ a) ∩ FootprintEdges (occ b)).Nonempty :=
    fun he => hnot (classify a b hne he)
  simpa only [normal] using
    (P5098T1SquareIntersection (d a.label) (d b.label)
      (Nat.pos_of_ne_zero hza) (Nat.pos_of_ne_zero hzb) (corner a) (corner b)).2
      (by simpa only [normal] using hno)

end ApollonianSuperharmonic

end
