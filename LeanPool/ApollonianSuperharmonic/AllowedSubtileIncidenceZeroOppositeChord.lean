/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Algebra.Group.Basic

public import LeanPool.ApollonianSuperharmonic.AllowedSubtileIncidence

-- [TABLET NODE: AllowedSubtileIncidenceZeroOppositeChord]

/-!
# AllowedSubtileIncidenceZeroOppositeChord

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem AllowedSubtileIncidenceZeroOppositeChord
    (a b c d : PeriodicSubtileIndex)
    (ha : a.first = 0 ∧ a.second = 0)
    (hc : c.first = 0 ∧ c.second = 0)
    (hab : AllowedSubtileIncidence a b)
    (hbc : AllowedSubtileIncidence b c)
    (hcd : AllowedSubtileIncidence c d)
    (hda : AllowedSubtileIncidence d a)
    (hab_ne : a ≠ b) (hac_ne : a ≠ c) (had_ne : a ≠ d)
    (hbc_ne : b ≠ c) (hbd_ne : b ≠ d) (hcd_ne : c ≠ d) :
    AllowedSubtileIncidence a c ∨ AllowedSubtileIncidence b d := by
-- BODY
  -- Normalize all symmetric reversals to the eighteen displacement families.
  let ledger : SixSubtileLabel → SixSubtileLabel → Int → Int → Prop :=
    fun x y m n => match x, y with
    | .A, .B => (m = 0 ∧ (n = 0 ∨ n = 1)) ∨ (m = 1 ∧ n = 1)
    | .A, .C => (m = 0 ∧ n = 0) ∨ (m = 1 ∧ n = 1)
    | .A, .D => m = 0 ∧ n = 0
    | .A, .E => m = 0 ∧ n = 1
    | .A, .F => m = 0 ∧ n = 0
    | .B, .C => m = 0 ∧ n = 0
    | .B, .D => (m = -1 ∧ n = -1) ∨ (m = 0 ∧ n = 0)
    | .B, .E => m = 0 ∧ n = 0
    | .B, .F => m = 0 ∧ n = -1
    | .C, .D => m = -1 ∧ n = 0
    | .C, .E => m = -1 ∧ n = 0
    | .C, .F => m = 0 ∧ n = 0
    | .D, .E => m = 0 ∧ n = 0
    | .D, .F => m = 1 ∧ n = 0
    | _, _ => False
  let adjacent := fun x y m n => ledger x y m n ∨ ledger y x (-m) (-n)
  have reverse : ∀ x y m n, adjacent x y m n → adjacent y x (-m) (-n) := by
    intro x y m n h
    simpa only [adjacent, neg_neg, or_comm] using h
  have normalize : ∀ {u v : PeriodicSubtileIndex}, AllowedSubtileIncidence u v →
      adjacent u.label v.label (v.first - u.first) (v.second - u.second) := by
    intro u v h
    induction h with
    | symm h ih =>
      simpa only [neg_sub] using reverse _ _ _ _ ih
    | AB m n | AB01 m n | AB11 m n | AC m n | AC11 m n
      | AD m n | AE01 m n | AF m n | BC m n | BDm1m1 m n
      | BD m n | BE m n | BF0m1 m n | CDm10 m n | CEm10 m n
      | CF m n | DE m n | DF10 m n =>
      dsimp [adjacent, ledger]
      omega
  -- The six nonadjacent zero-label pairs have precisely these neighbor bounds.
  have rowAE : ∀ u : PeriodicSubtileIndex,
      adjacent .A u.label u.first u.second →
      adjacent .E u.label u.first u.second →
      u = ⟨.B, 0, 0⟩ ∨ u = ⟨.D, 0, 0⟩ := by
    rintro ⟨l, m, n⟩ hA hE
    cases l <;> simp [adjacent, ledger] at hA hE ⊢ <;> omega
  have rowBF : ∀ u : PeriodicSubtileIndex,
      adjacent .B u.label u.first u.second →
      adjacent .F u.label u.first u.second →
      u = ⟨.A, 0, 0⟩ ∨ u = ⟨.C, 0, 0⟩ := by
    rintro ⟨l, m, n⟩ hB hF
    cases l <;> simp [adjacent, ledger] at hB hF ⊢ <;> omega
  have rowCD : ∀ u : PeriodicSubtileIndex,
      adjacent .C u.label u.first u.second →
      adjacent .D u.label u.first u.second →
      u = ⟨.A, 0, 0⟩ ∨ u = ⟨.B, 0, 0⟩ := by
    rintro ⟨l, m, n⟩ hC hD
    cases l <;> simp [adjacent, ledger] at hC hD ⊢ <;> omega
  have rowCE : ∀ u : PeriodicSubtileIndex,
      adjacent .C u.label u.first u.second →
      adjacent .E u.label u.first u.second →
      u = ⟨.B, 0, 0⟩ := by
    rintro ⟨l, m, n⟩ hC hE
    cases l <;> simp [adjacent, ledger] at hC hE ⊢ <;> omega
  have rowDF : ∀ u : PeriodicSubtileIndex,
      adjacent .D u.label u.first u.second →
      adjacent .F u.label u.first u.second →
      u = ⟨.A, 0, 0⟩ := by
    rintro ⟨l, m, n⟩ hD hF
    cases l <;> simp [adjacent, ledger] at hD hF ⊢ <;> omega
  have rowEF : ∀ u : PeriodicSubtileIndex,
      adjacent .E u.label u.first u.second →
      adjacent .F u.label u.first u.second → False := by
    rintro ⟨l, m, n⟩ hE hF
    cases l <;> simp [adjacent, ledger] at hE hF <;> omega
  have two {x y : PeriodicSubtileIndex} (hxy : AllowedSubtileIncidence x y)
      (hb : b = x ∨ b = y) (hd : d = x ∨ d = y) :
      AllowedSubtileIncidence b d := by
    rcases hb with rfl | rfl
    · rcases hd with rfl | rfl
      · exact (hbd_ne rfl).elim
      · exact hxy
    · rcases hd with rfl | rfl
      · exact AllowedSubtileIncidence.symm hxy
      · exact (hbd_ne rfl).elim
  -- Both opposite indices must be at zero before applying the neighbor rows.
  rcases a with ⟨al, am, an⟩
  rcases c with ⟨cl, cm, cn⟩
  rcases ha with ⟨ham, han⟩
  rcases hc with ⟨hcm, hcn⟩
  dsimp at ham han hcm hcn
  subst am
  subst an
  subst cm
  subst cn
  have hbA := normalize hab
  have hbC := normalize (AllowedSubtileIncidence.symm hbc)
  have hdA := normalize (AllowedSubtileIncidence.symm hda)
  have hdC := normalize hcd
  change adjacent al b.label (b.first - 0) (b.second - 0) at hbA
  change adjacent cl b.label (b.first - 0) (b.second - 0) at hbC
  change adjacent al d.label (d.first - 0) (d.second - 0) at hdA
  change adjacent cl d.label (d.first - 0) (d.second - 0) at hdC
  simp only [Int.sub_zero] at hbA hbC hdA hdC
  cases al <;> cases cl
  · exact (hac_ne rfl).elim
  · exact Or.inl (AllowedSubtileIncidence.AB 0 0)
  · exact Or.inl (AllowedSubtileIncidence.AC 0 0)
  · exact Or.inl (AllowedSubtileIncidence.AD 0 0)
  · exact Or.inr (two (AllowedSubtileIncidence.BD 0 0)
      (rowAE b hbA hbC) (rowAE d hdA hdC))
  · exact Or.inl (AllowedSubtileIncidence.AF 0 0)
  · exact Or.inl (AllowedSubtileIncidence.symm (AllowedSubtileIncidence.AB 0 0))
  · exact (hac_ne rfl).elim
  · exact Or.inl (AllowedSubtileIncidence.BC 0 0)
  · exact Or.inl (AllowedSubtileIncidence.BD 0 0)
  · exact Or.inl (AllowedSubtileIncidence.BE 0 0)
  · exact Or.inr (two (AllowedSubtileIncidence.AC 0 0)
      (rowBF b hbA hbC) (rowBF d hdA hdC))
  · exact Or.inl (AllowedSubtileIncidence.symm (AllowedSubtileIncidence.AC 0 0))
  · exact Or.inl (AllowedSubtileIncidence.symm (AllowedSubtileIncidence.BC 0 0))
  · exact (hac_ne rfl).elim
  · exact Or.inr (two (AllowedSubtileIncidence.AB 0 0)
      (rowCD b hbA hbC) (rowCD d hdA hdC))
  · exact (hbd_ne ((rowCE b hbA hbC).trans (rowCE d hdA hdC).symm)).elim
  · exact Or.inl (AllowedSubtileIncidence.CF 0 0)
  · exact Or.inl (AllowedSubtileIncidence.symm (AllowedSubtileIncidence.AD 0 0))
  · exact Or.inl (AllowedSubtileIncidence.symm (AllowedSubtileIncidence.BD 0 0))
  · exact Or.inr (two (AllowedSubtileIncidence.AB 0 0)
      (rowCD b hbC hbA) (rowCD d hdC hdA))
  · exact (hac_ne rfl).elim
  · exact Or.inl (AllowedSubtileIncidence.DE 0 0)
  · exact (hbd_ne ((rowDF b hbA hbC).trans (rowDF d hdA hdC).symm)).elim
  · exact Or.inr (two (AllowedSubtileIncidence.BD 0 0)
      (rowAE b hbC hbA) (rowAE d hdC hdA))
  · exact Or.inl (AllowedSubtileIncidence.symm (AllowedSubtileIncidence.BE 0 0))
  · exact (hbd_ne ((rowCE b hbC hbA).trans (rowCE d hdC hdA).symm)).elim
  · exact Or.inl (AllowedSubtileIncidence.symm (AllowedSubtileIncidence.DE 0 0))
  · exact (hac_ne rfl).elim
  · exact (rowEF b hbA hbC).elim
  · exact Or.inl (AllowedSubtileIncidence.symm (AllowedSubtileIncidence.AF 0 0))
  · exact Or.inr (two (AllowedSubtileIncidence.AC 0 0)
      (rowBF b hbC hbA) (rowBF d hdC hdA))
  · exact Or.inl (AllowedSubtileIncidence.symm (AllowedSubtileIncidence.CF 0 0))
  · exact (hbd_ne ((rowDF b hbC hbA).trans (rowDF d hdC hdA).symm)).elim
  · exact (rowEF b hbC hbA).elim
  · exact (hac_ne rfl).elim

end ApollonianSuperharmonic

end
