/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P3889T1TwoRaySectorDecomposition
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring

-- [TABLET NODE: P3889T1TwoRaySectors]

/-!
# P3889T1TwoRaySectors

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace TwoRaySectorsProof

private theorem huOrig :
    ∀ (u : Real × Real), (‖u‖ = 1) → (
    let uOrig := u
    ‖uOrig‖ = 1) := by
  classical
  intro u hu uOrig
  exact hu

private theorem hvOrig :
    ∀ (v : Real × Real), (‖v‖ = 1) → (
    let vOrig := v
    ‖vOrig‖ = 1) := by
  classical
  intro v hv vOrig
  exact hv

end TwoRaySectorsProof

namespace TwoRaySectorGeometry

private theorem hscalar :
    ∀ (u : Real × Real), ∀ (v : Real × Real),
    let det : (Real × Real) → (Real × Real) → Real :=
        fun a b => a.1 * b.2 - a.2 * b.1
    let uOrig := u
    let vOrig := v
    let dOrig := det uOrig vOrig
    (dOrig = (0 : ℝ)) → ((u.1 ≠ 0 ∨ u.2 ≠ 0) → (∃ k : Real, v = k • u)) := by
  classical
  intro u v det uOrig vOrig dOrig hd hcoord
  have hdet0 : u.1 * v.2 - u.2 * v.1 = 0 := hd
  rcases hcoord with h1 | h2
  · refine ⟨v.1 / u.1, ?_⟩
    ext
    · simp [div_eq_mul_inv, h1]
    · dsimp
      field_simp
      nlinarith [hdet0]
  · refine ⟨v.2 / u.2, ?_⟩
    ext
    · dsimp
      field_simp
      nlinarith [hdet0, h2]
    · simp [div_eq_mul_inv, h2]

private theorem hLconvAt193 :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real),
    let det : (Real × Real) → (Real ×
        Real) → Real := fun a b => a.1 * b.2 - a.2 * b.1
    let A : (Real × Real) → Real := fun p => det u (p - x)
    let L : Set (Real × Real) := Metric.ball x r ∩ {p | 0 < A p}
    Convex ℝ L := by
  classical
  intro x r u det A L p hp q' hq a b ha hb hab
  rcases hp with ⟨hpball, hpA⟩
  rcases hq with ⟨hqball, hqA⟩
  have hb' : b = 1-a := by linarith
  subst b
  refine ⟨(convex_ball x r) hpball hqball ha (by positivity) (by linarith), ?_⟩
  have hcomb : A (a • p + (1-a) • q') = a*A p + (1-a)*A q' := by
    dsimp [A, det]
    ring
  change 0 < A (a • p + (1-a) • q')
  rw [hcomb]
  by_cases ha0 : a=0
  · subst a
    simpa using hqA
  · have hap : 0<a := lt_of_le_of_ne ha (Ne.symm ha0)
    exact add_pos_of_pos_of_nonneg (mul_pos hap hpA)
      (mul_nonneg (by positivity) (le_of_lt hqA))

private theorem hRconv :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real),
    let det : (Real × Real) → (Real ×
        Real) → Real := fun a b => a.1 * b.2 - a.2 * b.1
    let A : (Real × Real) → Real := fun p => det u (p - x)
    let R : Set (Real × Real) := Metric.ball x r ∩ {p | A p < 0}
    Convex ℝ R := by
  classical
  intro x r u det A R p hp q' hq a b ha hb hab
  rcases hp with ⟨hpball, hpA⟩
  rcases hq with ⟨hqball, hqA⟩
  have hb' : b = 1-a := by linarith
  subst b
  refine ⟨(convex_ball x r) hpball hqball ha (by positivity) (by linarith), ?_⟩
  have hcomb : A (a • p + (1-a) • q') = a*A p + (1-a)*A q' := by
    dsimp [A, det]
    ring
  change A (a • p + (1-a) • q') < 0
  rw [hcomb]
  by_cases hb0 : 1-a=0
  · have haone : a=1 := by linarith
    simpa [haone, hb0] using hpA
  · have hbp : 0<1-a := lt_of_le_of_ne hb (Ne.symm hb0)
    exact add_neg_of_nonpos_of_neg (mul_nonpos_of_nonneg_of_nonpos ha
      (le_of_lt hpA)) (mul_neg_of_pos_of_neg hbp hqA)

private theorem hcol :
    ∀ (u : Real × Real),
    let det : (Real × Real) → (Real × Real) → Real := fun a b => a.1 * b.2 -
        a.2 * b.1
    (u.1 ≠ 0 ∨ u.2 ≠ 0) → (∀ (y : Real × Real), (det u y = 0) → (∃ k : Real, y = k • u)) := by
  classical
  intro u det hcoord y hy
  rcases hcoord with h1 | h2
  · refine ⟨y.1 / u.1, ?_⟩
    ext
    · simp [h1]
    · dsimp
      field_simp
      nlinarith [hy]
  · have hdet : u.1 * y.2 - u.2 * y.1 = 0 := by simpa [det] using hy
    refine ⟨y.2 / u.2, ?_⟩
    ext
    · dsimp
      field_simp [h2]
      nlinarith [hdet]
    · simp [h2]

private theorem hcoverAt299 :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real), ∀ (v : Real × Real),
    let det : (Real
        × Real) → (Real × Real) → Real := fun a b => a.1 * b.2 - a.2 * b.1
    (v = -u) → (
    let A : (Real × Real) → Real := fun p => det u (p - x)
    let L : Set (Real × Real) := Metric.ball x r ∩ {p | 0 < A p}
    let R : Set (Real × Real) := Metric.ball x r ∩ {p | A p < 0}
    (∀ (y : Real × Real), (det u y = 0) → (∃ k : Real, y = k • u)) → ((∀ (t : Real), A (x+t•u)=0)
        → ((∀ (t : Real), A (x+t•v)=0) → (L ∪ R = Metric.ball x r \
      ({p | ∃ t : Real, 0 ≤ t ∧ p=x+t•u} ∪
        {p | ∃ t : Real, 0 ≤ t ∧ p=x+t•v}))))) := by
  classical
  intro x r u v det hvneg A L R hcol hAu hAv
  ext p
  constructor
  · intro hp
    have hpball : p∈Metric.ball x r := by
      rcases hp with hpL | hpR
      · change p∈Metric.ball x r ∧ 0<A p at hpL
        exact hpL.1
      · change p∈Metric.ball x r ∧ A p<0 at hpR
        exact hpR.1
    refine ⟨hpball, ?_⟩
    intro hray
    rcases hray with hru | hrv
    · rcases hru with ⟨t, ht, rfl⟩
      have hz := hAu t
      rcases hp with hpL | hpR
      · change x+t•u∈Metric.ball x r ∧ 0<A (x+t•u) at hpL
        rw [hz] at hpL
        exact (lt_irrefl 0) hpL.2
      · change x+t•u∈Metric.ball x r ∧ A (x+t•u)<0 at hpR
        exact (not_lt_of_ge (le_of_eq hz.symm)) hpR.2
    · rcases hrv with ⟨t, ht, rfl⟩
      have hz := hAv t
      rcases hp with hpL | hpR
      · change x+t•v∈Metric.ball x r ∧ 0<A (x+t•v) at hpL
        rw [hz] at hpL
        exact (lt_irrefl 0) hpL.2
      · change x+t•v∈Metric.ball x r ∧ A (x+t•v)<0 at hpR
        exact (not_lt_of_ge (le_of_eq hz.symm)) hpR.2
  · rintro ⟨hpball, hnotray⟩
    by_cases hneg : A p < 0
    · right
      change p∈Metric.ball x r ∧ A p<0
      exact ⟨hpball,hneg⟩
    · by_cases hzero : A p=0
      · have hy : det u (p-x)=0 := by simpa [A] using hzero
        obtain ⟨k,hk⟩ := hcol (p-x) hy
        have hpEq : p=x+k•u := by
          calc p = x+(p-x) := by simp
            _ = x+k•u := by rw [hk]
        by_cases hkneg : k<0
        · have hvterm : (-k)•v = k•u := by rw [hvneg]; simp
          have hrv : p=x+(-k)•v := by rw [hpEq, ← hvterm]
          exact False.elim (hnotray (Or.inr ⟨-k, (neg_nonneg.mpr (le_of_lt hkneg)), hrv⟩))
        · exact False.elim (hnotray (Or.inl ⟨k, le_of_not_gt hkneg, hpEq⟩))
      · have hpos : 0<A p := lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm hzero)
        left
        change p∈Metric.ball x r ∧ 0<A p
        exact ⟨hpball,hpos⟩

private theorem hleftAt368 :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real),
    let det : (Real × Real) → (Real ×
        Real) → Real := fun a b => a.1 * b.2 - a.2 * b.1
    let A : (Real × Real) → Real := fun p => det u (p - x)
    let L : Set (Real × Real) := Metric.ball x r ∩ {p | 0 < A p}
    ∀ (t : ℝ),
    let z : Real × Real := x+t•u
    ∀ (δ : ℝ), (Metric.ball z δ ⊆ Metric.ball x r) → ((∀ (q : Real × Real), A q =
        u.1*(q.2-z.2)-u.2*(q.1-z.1)) → (L∩Metric.ball z δ =
      {q | q∈Metric.ball z δ ∧ 0<u.1*(q.2-z.2)-u.2*(q.1-z.1)})) := by
  classical
  intro x r u det A L t z δ hδsub hshift
  ext q
  constructor
  · rintro ⟨hqL,hqδ⟩
    change q∈Metric.ball x r ∧ 0<A q at hqL
    exact ⟨hqδ,by rw [← hshift]; exact hqL.2⟩
  · rintro ⟨hqδ,hdet⟩
    refine ⟨?_,hqδ⟩
    change q∈Metric.ball x r ∧ 0<A q
    exact ⟨hδsub hqδ,by rw [hshift]; exact hdet⟩

private theorem hrightAt379 :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real),
    let det : (Real × Real) → (Real ×
        Real) → Real := fun a b => a.1 * b.2 - a.2 * b.1
    let A : (Real × Real) → Real := fun p => det u (p - x)
    let R : Set (Real × Real) := Metric.ball x r ∩ {p | A p < 0}
    ∀ (t : ℝ),
    let z : Real × Real := x+t•u
    ∀ (δ : ℝ), (Metric.ball z δ ⊆ Metric.ball x r) → ((∀ (q : Real × Real), A q =
        u.1*(q.2-z.2)-u.2*(q.1-z.1)) → (R∩Metric.ball z δ =
      {q | q∈Metric.ball z δ ∧ u.1*(q.2-z.2)-u.2*(q.1-z.1)<0})) := by
  classical
  intro x r u det A R t z δ hδsub hshift
  ext q
  constructor
  · rintro ⟨hqR,hqδ⟩
    change q∈Metric.ball x r ∧ A q<0 at hqR
    exact ⟨hqδ,by rw [← hshift]; exact hqR.2⟩
  · rintro ⟨hqδ,hdet⟩
    refine ⟨?_,hqδ⟩
    change q∈Metric.ball x r ∧ A q<0
    exact ⟨hδsub hqδ,by rw [hshift]; exact hdet⟩

private theorem hrightAt407 :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real), ∀ (v : Real × Real),
    let det : (Real
        × Real) → (Real × Real) → Real := fun a b => a.1 * b.2 - a.2 * b.1
    let A : (Real × Real) → Real := fun p => det u (p - x)
    let R : Set (Real × Real) := Metric.ball x r ∩ {p | A p < 0}
    ∀ (t : ℝ),
    let z : Real × Real := x+t•v
    ∀ (δ : ℝ), (Metric.ball z δ ⊆ Metric.ball x r) → ((∀ (q : Real × Real), A q =
        -(v.1*(q.2-z.2)-v.2*(q.1-z.1))) → (R∩Metric.ball z δ =
      {q | q∈Metric.ball z δ ∧ 0<v.1*(q.2-z.2)-v.2*(q.1-z.1)})) := by
  classical
  intro x r u v det A R t z δ hδsub hshift
  ext q
  constructor
  · rintro ⟨hqR,hqδ⟩
    change q∈Metric.ball x r ∧ A q<0 at hqR
    have hval : A q<0 := hqR.2
    exact ⟨hqδ,by rw [hshift] at hval; linarith⟩
  · rintro ⟨hqδ,hdet⟩
    refine ⟨?_,hqδ⟩
    change q∈Metric.ball x r ∧ A q<0
    exact ⟨hδsub hqδ,by rw [hshift]; linarith⟩

private theorem hleftAt419 :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real), ∀ (v : Real × Real),
    let det : (Real
        × Real) → (Real × Real) → Real := fun a b => a.1 * b.2 - a.2 * b.1
    let A : (Real × Real) → Real := fun p => det u (p - x)
    let L : Set (Real × Real) := Metric.ball x r ∩ {p | 0 < A p}
    ∀ (t : ℝ),
    let z : Real × Real := x+t•v
    ∀ (δ : ℝ), (Metric.ball z δ ⊆ Metric.ball x r) → ((∀ (q : Real × Real), A q =
        -(v.1*(q.2-z.2)-v.2*(q.1-z.1))) → (L∩Metric.ball z δ =
      {q | q∈Metric.ball z δ ∧ v.1*(q.2-z.2)-v.2*(q.1-z.1)<0})) := by
  classical
  intro x r u v det A L t z δ hδsub hshift
  ext q
  constructor
  · rintro ⟨hqL,hqδ⟩
    change q∈Metric.ball x r ∧ 0<A q at hqL
    have hval : 0<A q := hqL.2
    exact ⟨hqδ,by rw [hshift] at hval; linarith⟩
  · rintro ⟨hqδ,hdet⟩
    refine ⟨?_,hqδ⟩
    change q∈Metric.ball x r ∧ 0<A q
    exact ⟨hδsub hqδ,by rw [hshift]; linarith⟩

private theorem hdpos :
    ∀ (u : Real × Real), ∀ (v : Real × Real),
    let det : (Real × Real) → (Real × Real) → Real :=
        fun a b => a.1 * b.2 - a.2 * b.1
    let uOrig := u
    let vOrig := v
    let dOrig := det uOrig vOrig
    (¬dOrig = (0 : ℝ)) → (
    let positiveFirstDirection := if 0 < dOrig then uOrig else vOrig
    let positiveSecondDirection := if 0 < dOrig then vOrig else uOrig
    let d := det positiveFirstDirection positiveSecondDirection
    0 < d) := by
  classical
  intro u v det uOrig vOrig dOrig hd positiveFirstDirection positiveSecondDirection d
  change 0 < det (if 0 < dOrig then uOrig else vOrig)
    (if 0 < dOrig then vOrig else uOrig)
  by_cases hpos : 0 < dOrig
  · simp only [ite_eq_left hpos]
    change 0 < dOrig
    exact hpos
  · have hneg : dOrig < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hd
    have hrev : det vOrig uOrig = -dOrig := by dsimp [dOrig, det]; ring
    simp only [ite_eq_right hpos]
    rw [hrev]
    exact neg_pos.mpr hneg

private theorem hLconvAt510 :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real), ∀ (v : Real × Real),
    let det : (Real
        × Real) → (Real × Real) → Real := fun a b => a.1 * b.2 - a.2 * b.1
    let uOrig := u
    let vOrig := v
    let dOrig := det uOrig vOrig
    let positiveFirstDirection := if 0 < dOrig then uOrig else vOrig
    let positiveSecondDirection := if 0 < dOrig then vOrig else uOrig
    let A : (Real × Real) → Real := fun p => det positiveFirstDirection (p - x)
    let B : (Real × Real) → Real := fun p => det (p - x) positiveSecondDirection
    let L : Set (Real × Real) := Metric.ball x r ∩ {p | 0 < A p} ∩ {p | 0 < B p}
    Convex ℝ L := by
  classical
  intro x r u v det uOrig vOrig dOrig positiveFirstDirection positiveSecondDirection A B L p hp
      q' hq' a b ha hb hab
  rcases hp with ⟨⟨hpball, hpA⟩, hpB⟩
  rcases hq' with ⟨⟨hqball', hqA'⟩, hqB'⟩
  have hb' : b = 1 - a := by linarith
  subst b
  refine ⟨⟨(convex_ball x r) hpball hqball' ha (by positivity) (by linarith), ?_⟩, ?_⟩
  · have hcomb : A (a • p + (1-a) • q') = a * A p + (1-a) * A q' := by
      dsimp [A, det]
      ring
    change 0 < A (a • p + (1-a) • q')
    rw [hcomb]
    by_cases ha0 : a = 0
    · subst a
      simpa using hqA'
    · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      exact add_pos_of_pos_of_nonneg (mul_pos hap hpA)
        (mul_nonneg (by positivity) (le_of_lt hqA'))
  · have hcomb : B (a • p + (1-a) • q') = a * B p + (1-a) * B q' := by
      dsimp [B, det]
      ring
    change 0 < B (a • p + (1-a) • q')
    rw [hcomb]
    by_cases ha0 : a = 0
    · subst a
      simpa using hqB'
    · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      exact add_pos_of_pos_of_nonneg (mul_pos hap hpB)
        (mul_nonneg (by positivity) (le_of_lt hqB'))

private theorem hCconv :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real), ∀ (v : Real × Real),
    let det : (Real
        × Real) → (Real × Real) → Real := fun a b => a.1 * b.2 - a.2 * b.1
    let uOrig := u
    let vOrig := v
    let dOrig := det uOrig vOrig
    let positiveFirstDirection := if 0 < dOrig then uOrig else vOrig
    let A : (Real × Real) → Real := fun p => det positiveFirstDirection (p - x)
    let C : Set (Real × Real) := Metric.ball x r ∩ {p | A p < 0}
    Convex ℝ C := by
  classical
  intro x r u v det uOrig vOrig dOrig positiveFirstDirection A C p hp q' hq' a b ha hb hab
  rcases hp with ⟨hpball, hpA⟩
  rcases hq' with ⟨hqball', hqA'⟩
  have hb' : b = 1 - a := by linarith
  subst b
  refine ⟨(convex_ball x r) hpball hqball' ha (by positivity) (by linarith), ?_⟩
  have hcomb : A (a • p + (1-a) • q') = a * A p + (1-a) * A q' := by
    dsimp [A, det]
    ring
  change A (a • p + (1-a) • q') < 0
  rw [hcomb]
  by_cases hb0 : 1 - a = 0
  · have haone : a = 1 := by linarith
    simpa [haone, hb0] using hpA
  · have hbp : 0 < 1 - a := lt_of_le_of_ne hb (Ne.symm hb0)
    exact add_neg_of_nonpos_of_neg (mul_nonpos_of_nonneg_of_nonpos ha
      (le_of_lt hpA)) (mul_neg_of_pos_of_neg hbp hqA')

private theorem hDconv :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real), ∀ (v : Real × Real),
    let det : (Real
        × Real) → (Real × Real) → Real := fun a b => a.1 * b.2 - a.2 * b.1
    let uOrig := u
    let vOrig := v
    let dOrig := det uOrig vOrig
    let positiveSecondDirection := if 0 < dOrig then vOrig else uOrig
    let B : (Real × Real) → Real := fun p => det (p - x) positiveSecondDirection
    let D : Set (Real × Real) := Metric.ball x r ∩ {p | B p < 0}
    Convex ℝ D := by
  classical
  intro x r u v det uOrig vOrig dOrig positiveSecondDirection B D p hp q' hq' a b ha hb hab
  rcases hp with ⟨hpball, hpB⟩
  rcases hq' with ⟨hqball', hqB'⟩
  have hb' : b = 1 - a := by linarith
  subst b
  refine ⟨(convex_ball x r) hpball hqball' ha (by positivity) (by linarith), ?_⟩
  have hcomb : B (a • p + (1-a) • q') = a * B p + (1-a) * B q' := by
    dsimp [B, det]
    ring
  change B (a • p + (1-a) • q') < 0
  rw [hcomb]
  by_cases hb0 : 1 - a = 0
  · have haone : a = 1 := by linarith
    simpa [haone, hb0] using hpB
  · have hbp : 0 < 1 - a := lt_of_le_of_ne hb (Ne.symm hb0)
    exact add_neg_of_nonpos_of_neg (mul_nonpos_of_nonneg_of_nonpos ha
      (le_of_lt hpB)) (mul_neg_of_pos_of_neg hbp hqB')

private theorem hdisAt619 :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real), ∀ (v : Real × Real),
    let det : (Real
        × Real) → (Real × Real) → Real := fun a b => a.1 * b.2 - a.2 * b.1
    let uOrig := u
    let vOrig := v
    let dOrig := det uOrig vOrig
    let positiveFirstDirection := if 0 < dOrig then uOrig else vOrig
    let positiveSecondDirection := if 0 < dOrig then vOrig else uOrig
    let A : (Real × Real) → Real := fun p => det positiveFirstDirection (p - x)
    let B : (Real × Real) → Real := fun p => det (p - x) positiveSecondDirection
    let L : Set (Real × Real) := Metric.ball x r ∩ {p | 0 < A p} ∩ {p | 0 < B p}
    let C : Set (Real × Real) := Metric.ball x r ∩ {p | A p < 0}
    let D : Set (Real × Real) := Metric.ball x r ∩ {p | B p < 0}
    let R : Set (Real × Real) := C ∪ D
    Disjoint L R := by
  classical
  intro x r u v det uOrig vOrig dOrig positiveFirstDirection positiveSecondDirection A B L C D R
  apply Set.disjoint_left.mpr
  intro p hpL hpR
  change p ∈ Metric.ball x r ∩ {p | 0 < A p} ∩ {p | 0 < B p} at hpL
  change p ∈ C ∪ D at hpR
  rcases hpL with ⟨⟨_, hpa⟩, hpb⟩
  rcases hpR with hpC | hpD
  · change p ∈ Metric.ball x r ∧ A p < 0 at hpC
    exact (not_lt_of_ge (le_of_lt hpa)) hpC.2
  · change p ∈ Metric.ball x r ∧ B p < 0 at hpD
    exact (not_lt_of_ge (le_of_lt hpb)) hpD.2

private theorem hcoverAlias :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real), ∀ (v : Real × Real),
    let det : (Real
        × Real) → (Real × Real) → Real := fun a b => a.1 * b.2 - a.2 * b.1
    let uOrig := u
    let vOrig := v
    let dOrig := det uOrig vOrig
    let positiveFirstDirection := if 0 < dOrig then uOrig else vOrig
    let positiveSecondDirection := if 0 < dOrig then vOrig else uOrig
    let d := det positiveFirstDirection positiveSecondDirection
    (0 < d) → (
    let A : (Real × Real) → Real := fun p => det positiveFirstDirection (p - x)
    let B : (Real × Real) → Real := fun p => det (p - x) positiveSecondDirection
    let L : Set (Real × Real) := Metric.ball x r ∩ {p | 0 < A p} ∩ {p | 0 < B p}
    let C : Set (Real × Real) := Metric.ball x r ∩ {p | A p < 0}
    let D : Set (Real × Real) := Metric.ball x r ∩ {p | B p < 0}
    let R : Set (Real × Real) := C ∪ D
    (∀ (y : Real × Real), d • y = det y positiveSecondDirection • positiveFirstDirection + det
        positiveFirstDirection y • positiveSecondDirection) → ((∀ (t : Real), A (x + t •
        positiveFirstDirection) = 0) → ((∀ (t : Real), B (x + t • positiveFirstDirection) = t *
        d) → ((∀ (t : Real), A (x + t • positiveSecondDirection) = t * d) → ((∀ (t : Real), B (x
        + t • positiveSecondDirection) = 0) → (L ∪ R = Metric.ball x r \
      ({p | ∃ t : Real, 0 ≤ t ∧ p = x + t • positiveFirstDirection} ∪
        {p | ∃ t : Real, 0 ≤ t ∧ p = x + t • positiveSecondDirection}))))))) := by
  classical
  intro x r u v det uOrig vOrig dOrig positiveFirstDirection positiveSecondDirection d hdpos A B
      L C D R hdetid hAu hBu hAv hBv
  ext p
  constructor
  · intro hp
    have hpball : p ∈ Metric.ball x r := by
      rcases hp with hpL | hpR
      · change p ∈ Metric.ball x r ∩ {p | 0 < A p} ∩ {p | 0 < B p} at hpL
        exact hpL.1.1
      · change p ∈ C ∪ D at hpR
        rcases hpR with hpC | hpD
        · change p ∈ Metric.ball x r ∧ A p < 0 at hpC
          exact hpC.1
        · change p ∈ Metric.ball x r ∧ B p < 0 at hpD
          exact hpD.1
    refine ⟨hpball, ?_⟩
    intro hray
    rcases hray with huRay | hvRay
    · rcases huRay with ⟨t, ht, rfl⟩
      have hzero := hAu t
      have hnonneg := mul_nonneg ht (le_of_lt hdpos)
      have hdetnonneg : 0 ≤ B (x + t • positiveFirstDirection) := by rw [hBu]; exact hnonneg
      rcases hp with hpL | hpR
      · change x + t • positiveFirstDirection ∈ Metric.ball x r ∩ {p | 0 < A p} ∩ {p | 0 < B p}
          at hpL
        have hpA' : 0 < A (x + t • positiveFirstDirection) := hpL.1.2
        rw [hzero] at hpA'
        exact (lt_irrefl 0) hpA'
      · change x + t • positiveFirstDirection ∈ C ∪ D at hpR
        rcases hpR with hpC | hpD
        · change x + t • positiveFirstDirection ∈ Metric.ball x r ∧ A (x + t •
            positiveFirstDirection) < 0 at hpC
          exact (not_lt_of_ge (le_of_eq hzero.symm)) hpC.2
        · change x + t • positiveFirstDirection ∈ Metric.ball x r ∧ B (x + t •
            positiveFirstDirection) < 0 at hpD
          exact (not_lt_of_ge hdetnonneg) hpD.2
    · rcases hvRay with ⟨t, ht, rfl⟩
      have hzero := hBv t
      have hnonneg := mul_nonneg ht (le_of_lt hdpos)
      have hdetnonneg : 0 ≤ A (x + t • positiveSecondDirection) := by rw [hAv]; exact hnonneg
      rcases hp with hpL | hpR
      · change x + t • positiveSecondDirection ∈ Metric.ball x r ∩ {p | 0 < A p} ∩ {p | 0 < B p}
          at hpL
        have hpB' : 0 < B (x + t • positiveSecondDirection) := hpL.2
        rw [hzero] at hpB'
        exact (lt_irrefl 0) hpB'
      · change x + t • positiveSecondDirection ∈ C ∪ D at hpR
        rcases hpR with hpC | hpD
        · change x + t • positiveSecondDirection ∈ Metric.ball x r ∧ A (x + t •
            positiveSecondDirection) < 0 at hpC
          exact (not_lt_of_ge hdetnonneg) hpC.2
        · change x + t • positiveSecondDirection ∈ Metric.ball x r ∧ B (x + t •
            positiveSecondDirection) < 0 at hpD
          exact (not_lt_of_ge (le_of_eq hzero.symm)) hpD.2
  · rintro ⟨hpball, hnotray⟩
    by_cases hpa : A p < 0
    · right
      left
      exact ⟨hpball, hpa⟩
    · by_cases hpb : B p < 0
      · right
        right
        exact ⟨hpball, hpb⟩
      · have hpa0 : 0 ≤ A p := le_of_not_gt hpa
        have hpb0 : 0 ≤ B p := le_of_not_gt hpb
        have hyid := hdetid (p - x)
        have hrep : p - x = (B p / d) • positiveFirstDirection + (A p / d) •
            positiveSecondDirection := by
          have hdne : d ≠ 0 := ne_of_gt hdpos
          have hmul := congrArg (fun y : Real × Real => d⁻¹ • y) hyid
          calc
            p - x = d⁻¹ • (d • (p - x)) := by simp [smul_smul, hdne]
            _ = d⁻¹ • (B p • positiveFirstDirection + A p • positiveSecondDirection) := hmul
            _ = (B p / d) • positiveFirstDirection + (A p / d) • positiveSecondDirection := by
              simp [smul_add, smul_smul, div_eq_mul_inv, mul_comm]
        by_cases hpaEq : A p = 0
        · have hray : p = x + (B p / d) • positiveFirstDirection := by
            calc
              p = x + (p - x) := by simp
                _ = x + ((B p / d) • positiveFirstDirection + (A p / d) •
                    positiveSecondDirection) := by rw [hrep]
                _ = x + (B p / d) • positiveFirstDirection := by
                  rw [hpaEq]
                  simp only [zero_div, zero_smul, add_zero]
          apply False.elim (hnotray (Or.inl ⟨B p / d, div_nonneg hpb0 (le_of_lt hdpos), hray⟩))
        · by_cases hpbEq : B p = 0
          · have hray : p = x + (A p / d) • positiveSecondDirection := by
              calc
                p = x + (p - x) := by simp
                _ = x + ((B p / d) • positiveFirstDirection + (A p / d) •
                    positiveSecondDirection) := by rw [hrep]
                _ = x + (A p / d) • positiveSecondDirection := by
                  rw [hpbEq]
                  simp only [zero_div, zero_smul, zero_add]
            exact False.elim (hnotray (Or.inr ⟨A p / d, div_nonneg hpa0 (le_of_lt hdpos),
                hray⟩))
          · have hpaPos : 0 < A p := lt_of_le_of_ne hpa0 (Ne.symm hpaEq)
            have hpbPos : 0 < B p := lt_of_le_of_ne hpb0 (Ne.symm hpbEq)
            left
            exact ⟨⟨hpball, hpaPos⟩, hpbPos⟩

private theorem hcoverAt724 :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real), ∀ (v : Real × Real),
    let det : (Real
        × Real) → (Real × Real) → Real := fun a b => a.1 * b.2 - a.2 * b.1
    let uOrig := u
    let vOrig := v
    let dOrig := det uOrig vOrig
    let positiveFirstDirection := if 0 < dOrig then uOrig else vOrig
    let positiveSecondDirection := if 0 < dOrig then vOrig else uOrig
    let A : (Real × Real) → Real := fun p => det positiveFirstDirection (p - x)
    let B : (Real × Real) → Real := fun p => det (p - x) positiveSecondDirection
    let L : Set (Real × Real) := Metric.ball x r ∩ {p | 0 < A p} ∩ {p | 0 < B p}
    let C : Set (Real × Real) := Metric.ball x r ∩ {p | A p < 0}
    let D : Set (Real × Real) := Metric.ball x r ∩ {p | B p < 0}
    let R : Set (Real × Real) := C ∪ D
    (L ∪ R = Metric.ball x r \ ({p | ∃ t : Real, 0 ≤ t ∧ p = x + t • positiveFirstDirection} ∪ {p
        | ∃ t : Real, 0 ≤ t ∧ p = x + t • positiveSecondDirection})) → (L ∪ R = Metric.ball x r \
      ({p | ∃ t : Real, 0 ≤ t ∧ p = x + t • uOrig} ∪
        {p | ∃ t : Real, 0 ≤ t ∧ p = x + t • vOrig})) := by
  classical
  intro x r u v det uOrig vOrig dOrig positiveFirstDirection positiveSecondDirection A B L C D R
      hcoverAlias
  have hrays :
      ({p | ∃ t : Real, 0 ≤ t ∧ p = x + t • positiveFirstDirection} ∪
        {p | ∃ t : Real, 0 ≤ t ∧ p = x + t • positiveSecondDirection}) =
      ({p | ∃ t : Real, 0 ≤ t ∧ p = x + t • uOrig} ∪
        {p | ∃ t : Real, 0 ≤ t ∧ p = x + t • vOrig}) := by
    have horder : (positiveFirstDirection = uOrig ∧ positiveSecondDirection = vOrig) ∨
        (positiveFirstDirection = vOrig ∧ positiveSecondDirection = uOrig) := by
      by_cases hpos : 0 < dOrig
      · left
        constructor <;> dsimp [positiveFirstDirection, positiveSecondDirection] <;> simp [hpos]
      · right
        constructor <;> dsimp [positiveFirstDirection, positiveSecondDirection] <;> simp [hpos]
    rcases horder with ⟨huv1, hvv1⟩ | ⟨huv1, hvv1⟩
    · rw [huv1, hvv1]
    · rw [huv1, hvv1, Set.union_comm]
  rw [hcoverAlias, hrays]

private theorem hwAlias :
    ∀ (u : Real × Real), ∀ (v : Real × Real),
    let det : (Real × Real) → (Real × Real) → Real :=
        fun a b => a.1 * b.2 - a.2 * b.1
    let uOrig := u
    let vOrig := v
    let dOrig := det uOrig vOrig
    let positiveFirstDirection := if 0 < dOrig then uOrig else vOrig
    let positiveSecondDirection := if 0 < dOrig then vOrig else uOrig
    ∀ (w : ℝ × ℝ), (w = u ∨ w = v) → (w = positiveFirstDirection ∨ w = positiveSecondDirection)
        := by
  classical
  intro u v det uOrig vOrig dOrig positiveFirstDirection positiveSecondDirection w hw
  rcases hw with h | h
  · by_cases hpos : 0 < dOrig
    · have huEq : positiveFirstDirection = uOrig := by dsimp [positiveFirstDirection]; simp [hpos]
      have h : w = uOrig := by simpa [uOrig] using h
      left
      rw [huEq]
      exact h
    · have hvEq : positiveSecondDirection = uOrig := by dsimp [positiveSecondDirection]; simp [hpos]
      have h : w = uOrig := by simpa [uOrig] using h
      right
      rw [hvEq]
      exact h
  · by_cases hpos : 0 < dOrig
    · have hvEq : positiveSecondDirection = vOrig := by dsimp [positiveSecondDirection]; simp [hpos]
      have h : w = vOrig := by simpa [vOrig] using h
      right
      rw [hvEq]
      exact h
    · have huEq : positiveFirstDirection = vOrig := by dsimp [positiveFirstDirection]; simp [hpos]
      have h : w = vOrig := by simpa [vOrig] using h
      left
      rw [huEq]
      exact h

private theorem hleftAt789 :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real), ∀ (v : Real × Real),
    let det : (Real
        × Real) → (Real × Real) → Real := fun a b => a.1 * b.2 - a.2 * b.1
    let uOrig := u
    let vOrig := v
    let dOrig := det uOrig vOrig
    let positiveFirstDirection := if 0 < dOrig then uOrig else vOrig
    let positiveSecondDirection := if 0 < dOrig then vOrig else uOrig
    let A : (Real × Real) → Real := fun p => det positiveFirstDirection (p - x)
    let B : (Real × Real) → Real := fun p => det (p - x) positiveSecondDirection
    let L : Set (Real × Real) := Metric.ball x r ∩ {p | 0 < A p} ∩ {p | 0 < B p}
    ∀ (t : ℝ),
    let z : Real × Real := x + t • positiveFirstDirection
    ∀ (δ : ℝ), (Metric.ball z δ ⊆ Metric.ball x r ∩ {p : ℝ × ℝ | (0 : ℝ) < B p}) → ((∀ (q : Real
        × Real), A q = positiveFirstDirection.1 * (q.2 - z.2) - positiveFirstDirection.2 * (q.1 -
        z.1)) → (L ∩ Metric.ball z δ =
      {q | q ∈ Metric.ball z δ ∧
        0 < positiveFirstDirection.1 * (q.2 - z.2) - positiveFirstDirection.2 * (q.1 - z.1)})) := by
  classical
  intro x r u v det uOrig vOrig dOrig positiveFirstDirection positiveSecondDirection A B L t z δ
      hδsub hAshift
  ext q
  constructor
  · rintro ⟨hqL, hqδ⟩
    change q ∈ Metric.ball x r ∩ {p | 0 < A p} ∩ {p | 0 < B p} at hqL
    have hqN := hδsub hqδ
    exact ⟨hqδ, by rw [← hAshift]; exact hqL.1.2⟩
  · rintro ⟨hqδ, hdet⟩
    have hqN := hδsub hqδ
    refine ⟨?_, hqδ⟩
    change q ∈ Metric.ball x r ∩ {p | 0 < A p} ∩ {p | 0 < B p}
    exact ⟨⟨hqN.1, by change 0 < A q; rw [hAshift]; exact hdet⟩, hqN.2⟩

private theorem hrightAt803 :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real), ∀ (v : Real × Real),
    let det : (Real
        × Real) → (Real × Real) → Real := fun a b => a.1 * b.2 - a.2 * b.1
    let uOrig := u
    let vOrig := v
    let dOrig := det uOrig vOrig
    let positiveFirstDirection := if 0 < dOrig then uOrig else vOrig
    let positiveSecondDirection := if 0 < dOrig then vOrig else uOrig
    let A : (Real × Real) → Real := fun p => det positiveFirstDirection (p - x)
    let B : (Real × Real) → Real := fun p => det (p - x) positiveSecondDirection
    let C : Set (Real × Real) := Metric.ball x r ∩ {p | A p < 0}
    let D : Set (Real × Real) := Metric.ball x r ∩ {p | B p < 0}
    let R : Set (Real × Real) := C ∪ D
    ∀ (t : ℝ),
    let z : Real × Real := x + t • positiveFirstDirection
    ∀ (δ : ℝ), (Metric.ball z δ ⊆ Metric.ball x r ∩ {p : ℝ × ℝ | (0 : ℝ) < B p}) → ((∀ (q : Real
        × Real), A q = positiveFirstDirection.1 * (q.2 - z.2) - positiveFirstDirection.2 * (q.1 -
        z.1)) → (R ∩ Metric.ball z δ =
      {q | q ∈ Metric.ball z δ ∧
        positiveFirstDirection.1 * (q.2 - z.2) - positiveFirstDirection.2 * (q.1 - z.1) < 0})) := by
  classical
  intro x r u v det uOrig vOrig dOrig positiveFirstDirection positiveSecondDirection A B C D R t
      z δ hδsub hAshift
  ext q
  constructor
  · rintro ⟨hqR, hqδ⟩
    have hqN := hδsub hqδ
    change q ∈ C ∪ D at hqR
    rcases hqR with hqC | hqD
    · change q ∈ Metric.ball x r ∧ A q < 0 at hqC
      exact ⟨hqδ, by rw [← hAshift]; exact hqC.2⟩
    · change q ∈ Metric.ball x r ∧ B q < 0 at hqD
      exact False.elim ((not_lt_of_ge (le_of_lt hqN.2)) hqD.2)
  · rintro ⟨hqδ, hdet⟩
    have hqN := hδsub hqδ
    refine ⟨?_, hqδ⟩
    change q ∈ C ∪ D
    left
    change q ∈ Metric.ball x r ∧ A q < 0
    exact ⟨hqN.1, by rw [hAshift]; exact hdet⟩

private theorem hrightAt842 :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real), ∀ (v : Real × Real),
    let det : (Real
        × Real) → (Real × Real) → Real := fun a b => a.1 * b.2 - a.2 * b.1
    let uOrig := u
    let vOrig := v
    let dOrig := det uOrig vOrig
    let positiveFirstDirection := if 0 < dOrig then uOrig else vOrig
    let positiveSecondDirection := if 0 < dOrig then vOrig else uOrig
    let A : (Real × Real) → Real := fun p => det positiveFirstDirection (p - x)
    let B : (Real × Real) → Real := fun p => det (p - x) positiveSecondDirection
    let C : Set (Real × Real) := Metric.ball x r ∩ {p | A p < 0}
    let D : Set (Real × Real) := Metric.ball x r ∩ {p | B p < 0}
    let R : Set (Real × Real) := C ∪ D
    ∀ (t : ℝ),
    let z : Real × Real := x + t • positiveSecondDirection
    ∀ (δ : ℝ), (Metric.ball z δ ⊆ Metric.ball x r ∩ {p : ℝ × ℝ | (0 : ℝ) < A p}) → ((∀ (q : Real
        × Real), B q = -(positiveSecondDirection.1 * (q.2 - z.2) - positiveSecondDirection.2 *
        (q.1 - z.1))) → (R ∩ Metric.ball z δ =
      {q | q ∈ Metric.ball z δ ∧
        0 < positiveSecondDirection.1 * (q.2 - z.2) - positiveSecondDirection.2 * (q.1 - z.1)}))
            := by
  classical
  intro x r u v det uOrig vOrig dOrig positiveFirstDirection positiveSecondDirection A B C D R t
      z δ hδsub hBshift
  ext q
  constructor
  · rintro ⟨hqR, hqδ⟩
    have hqN := hδsub hqδ
    change q ∈ C ∪ D at hqR
    rcases hqR with hqC | hqD
    · change q ∈ Metric.ball x r ∧ A q < 0 at hqC
      exact False.elim ((not_lt_of_ge (le_of_lt hqN.2)) hqC.2)
    · change q ∈ Metric.ball x r ∧ B q < 0 at hqD
      refine ⟨hqδ, ?_⟩
      have hDval : B q < 0 := hqD.2
      rw [hBshift] at hDval
      linarith [hDval]
  · rintro ⟨hqδ, hdet⟩
    have hqN := hδsub hqδ
    refine ⟨?_, hqδ⟩
    change q ∈ C ∪ D
    right
    change q ∈ Metric.ball x r ∧ B q < 0
    refine ⟨hqN.1, ?_⟩
    rw [hBshift]
    linarith

private theorem hleftAt868 :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real), ∀ (v : Real × Real),
    let det : (Real
        × Real) → (Real × Real) → Real := fun a b => a.1 * b.2 - a.2 * b.1
    let uOrig := u
    let vOrig := v
    let dOrig := det uOrig vOrig
    let positiveFirstDirection := if 0 < dOrig then uOrig else vOrig
    let positiveSecondDirection := if 0 < dOrig then vOrig else uOrig
    let A : (Real × Real) → Real := fun p => det positiveFirstDirection (p - x)
    let B : (Real × Real) → Real := fun p => det (p - x) positiveSecondDirection
    let L : Set (Real × Real) := Metric.ball x r ∩ {p | 0 < A p} ∩ {p | 0 < B p}
    ∀ (t : ℝ),
    let z : Real × Real := x + t • positiveSecondDirection
    ∀ (δ : ℝ), (Metric.ball z δ ⊆ Metric.ball x r ∩ {p : ℝ × ℝ | (0 : ℝ) < A p}) → ((∀ (q : Real
        × Real), B q = -(positiveSecondDirection.1 * (q.2 - z.2) - positiveSecondDirection.2 *
        (q.1 - z.1))) → (L ∩ Metric.ball z δ =
      {q | q ∈ Metric.ball z δ ∧
        positiveSecondDirection.1 * (q.2 - z.2) - positiveSecondDirection.2 * (q.1 - z.1) < 0}))
            := by
  classical
  intro x r u v det uOrig vOrig dOrig positiveFirstDirection positiveSecondDirection A B L t z δ
      hδsub hBshift
  ext q
  constructor
  · rintro ⟨hqL, hqδ⟩
    have hqN := hδsub hqδ
    change q ∈ Metric.ball x r ∩ {p | 0 < A p} ∩ {p | 0 < B p} at hqL
    refine ⟨hqδ, ?_⟩
    have hLval : 0 < B q := hqL.2
    rw [hBshift] at hLval
    linarith [hLval]
  · rintro ⟨hqδ, hdet⟩
    have hqN := hδsub hqδ
    refine ⟨?_, hqδ⟩
    change q ∈ Metric.ball x r ∩ {p | 0 < A p} ∩ {p | 0 < B p}
    refine ⟨⟨hqN.1, hqN.2⟩, ?_⟩
    change 0 < B q
    rw [hBshift]
    linarith

end TwoRaySectorGeometry

namespace TwoRayCasesProof

private theorem degenerateCase :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real), ∀ (v : Real × Real), (0 < r) → ((‖u‖
        = 1) → ((‖v‖ = 1) → ((u ≠ v) → (
    let det : (Real × Real) → (Real × Real) → Real := fun a b => a.1 * b.2 - a.2 * b.1
    let uOrig := u
    let vOrig := v
    let dOrig := det uOrig vOrig
    (dOrig = 0) → (Nonempty (P3889T1TwoRaySectorDecomposition x r u v)))))) := by
  classical
  intro x r u v hr hu hv huv det uOrig vOrig dOrig hd
  have hdet0 : u.1 * v.2 - u.2 * v.1 = 0 := by
    simpa [dOrig, det, uOrig, vOrig] using hd
  have hu0 : u ≠ (0, 0) := by
    intro h
    rw [h] at hu
    norm_num at hu
  have hcoord : u.1 ≠ 0 ∨ u.2 ≠ 0 := by
    by_contra h
    push Not at h
    apply hu0
    ext
    · exact h.1
    · exact h.2
  have hscalar := TwoRaySectorGeometry.hscalar u v hd hcoord
  obtain ⟨k, hk⟩ := hscalar
  have hkabs : |k| = 1 := by
    have hvnorm := hv
    rw [hk, norm_smul, Real.norm_eq_abs, hu] at hvnorm
    nlinarith
  have hk2 : k^2 = 1 := by nlinarith [sq_abs k]
  have hfactor : (k-1)*(k+1)=0 := by nlinarith [hk2]
  rcases mul_eq_zero.mp hfactor with hkone | hkminus
  · have hkone' : k = 1 := by linarith
    have : v = u := by rw [hk, hkone']; simp
    exact False.elim (huv this.symm)
  · have hkminus' : k = -1 := by linarith
    have hvneg : v = -u := by rw [hk, hkminus']; simp
    let A : (Real × Real) → Real := fun p => det u (p - x)
    let L : Set (Real × Real) := Metric.ball x r ∩ {p | 0 < A p}
    let R : Set (Real × Real) := Metric.ball x r ∩ {p | A p < 0}
    have hAcont : Continuous A := by
      dsimp [A, det]
      fun_prop
    have hLopen : IsOpen L := by
      dsimp [L]
      exact Metric.isOpen_ball.inter (isOpen_Ioi.preimage hAcont)
    have hRopen : IsOpen R := by
      dsimp [R]
      exact Metric.isOpen_ball.inter (isOpen_Iio.preimage hAcont)
    have hLconv := TwoRaySectorGeometry.hLconvAt193 x r u
    have hRconv := TwoRaySectorGeometry.hRconv x r u
    let j : Real × Real := (-u.2, u.1)
    have hsqpos : 0 < u.1^2 + u.2^2 := by
      by_contra h
      have hle : u.1^2 + u.2^2 ≤ 0 := le_of_not_gt h
      have h1 : u.1 = 0 := by nlinarith [sq_nonneg u.1, sq_nonneg u.2]
      have h2 : u.2 = 0 := by nlinarith [sq_nonneg u.1, sq_nonneg u.2]
      apply hu0
      ext <;> simp [h1, h2]
    have hjdet : det u j = u.1^2 + u.2^2 := by dsimp [j, det]; ring
    have hjnorm : ‖j‖ = 1 := by
      dsimp [j]
      simpa [Prod.norm_def, Real.norm_eq_abs, max_comm] using hu
    let qpos : Real × Real := x + (r/4) • j
    let qneg : Real × Real := x - (r/4) • j
    have hqposball : qpos ∈ Metric.ball x r := by
      change dist qpos x < r
      rw [dist_eq_norm]
      have heq : qpos-x=(r/4)•j := by simp [qpos]
      rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0<r/4), hjnorm]
      nlinarith [hr]
    have hqnegball : qneg ∈ Metric.ball x r := by
      change dist qneg x < r
      rw [dist_eq_norm]
      have heq : qneg-x=-((r/4)•j) := by simp [qneg, sub_eq_add_neg]
      rw [heq, norm_neg, norm_smul, Real.norm_eq_abs,
        abs_of_pos (by positivity : 0<r/4), hjnorm]
      nlinarith [hr]
    have hqposA : 0 < A qpos := by
      dsimp [A, qpos, det]
      simp [j]
      nlinarith [hsqpos, hr]
    have hqnegA : A qneg < 0 := by
      dsimp [A, qneg, det]
      simp [j]
      nlinarith [hsqpos, hr]
    have hLne : L.Nonempty := ⟨qpos, hqposball, hqposA⟩
    have hRne : R.Nonempty := ⟨qneg, hqnegball, hqnegA⟩
    have hLconn : IsConnected L := hLconv.isConnected hLne
    have hRconn : IsConnected R := hRconv.isConnected hRne
    have hdis : Disjoint L R := by
      apply Set.disjoint_left.mpr
      intro p hpL hpR
      change p ∈ Metric.ball x r ∧ 0<A p at hpL
      change p ∈ Metric.ball x r ∧ A p<0 at hpR
      exact (not_lt_of_ge (le_of_lt hpL.2)) hpR.2
    have hcol (y : Real × Real) (hy : det u y = 0) :
    ∃ k : Real, y = k • u := TwoRaySectorGeometry.hcol u hcoord y hy
    have hAu (t : Real) : A (x+t•u)=0 := by
      dsimp [A, det]
      simp
      ring
    have hAv (t : Real) : A (x+t•v)=0 := by
      rw [hvneg]
      dsimp [A, det]
      simp
      ring
    have hcover : L ∪ R = Metric.ball x r \
    ({p | ∃ t : Real, 0 ≤ t ∧ p=x+t•u} ∪
      {p | ∃ t : Real, 0 ≤ t ∧ p=x+t•v}) := TwoRaySectorGeometry.hcoverAt299 x r u v hvneg hcol
          hAu hAv
    refine ⟨⟨L,R,hLopen,hRopen,hLconn,hRconn,hdis,hcover,?_⟩⟩
    intro w hw t ht htr
    dsimp
    rcases hw with hwu | hwv
    · subst w
      let z : Real × Real := x+t•u
      have hztball : z∈Metric.ball x r := by
        change dist z x < r
        rw [dist_eq_norm]
        have heq : z-x=t•u := by simp [z]
        rw [heq,norm_smul,Real.norm_eq_abs,abs_of_pos ht,hu]
        nlinarith
      obtain ⟨δ,hδ,hδsub⟩ := Metric.mem_nhds_iff.mp
        (Metric.isOpen_ball.mem_nhds hztball)
      have hshift (q : Real × Real) : A q =
          u.1*(q.2-z.2)-u.2*(q.1-z.1) := by
        dsimp [A,det,z]
        ring
      have hleft : L∩Metric.ball z δ =
    {q | q∈Metric.ball z δ ∧ 0<u.1*(q.2-z.2)-u.2*(q.1-z.1)} := TwoRaySectorGeometry.hleftAt368
        x r u t δ hδsub hshift
      have hright : R∩Metric.ball z δ =
    {q | q∈Metric.ball z δ ∧ u.1*(q.2-z.2)-u.2*(q.1-z.1)<0} := TwoRaySectorGeometry.hrightAt379
        x r u t δ hδsub hshift
      exact ⟨δ,hδ,hδsub,Or.inl ⟨hleft,hright⟩⟩
    · subst w
      let z : Real × Real := x+t•v
      have hztball : z∈Metric.ball x r := by
        change dist z x < r
        rw [dist_eq_norm]
        have heq : z-x=t•v := by simp [z]
        rw [heq,norm_smul,Real.norm_eq_abs,abs_of_pos ht,hv]
        nlinarith
      obtain ⟨δ,hδ,hδsub⟩ := Metric.mem_nhds_iff.mp
        (Metric.isOpen_ball.mem_nhds hztball)
      have hshift (q : Real × Real) : A q =
          -(v.1*(q.2-z.2)-v.2*(q.1-z.1)) := by
        dsimp [A,det,z]
        rw [hvneg]
        simp only [Prod.fst_neg, Prod.snd_neg]
        ring
      have hright : R∩Metric.ball z δ =
    {q | q∈Metric.ball z δ ∧ 0<v.1*(q.2-z.2)-v.2*(q.1-z.1)} := TwoRaySectorGeometry.hrightAt407
        x r u v t δ hδsub hshift
      have hleft : L∩Metric.ball z δ =
    {q | q∈Metric.ball z δ ∧ v.1*(q.2-z.2)-v.2*(q.1-z.1)<0} := TwoRaySectorGeometry.hleftAt419
        x r u v t δ hδsub hshift
      exact ⟨δ,hδ,hδsub,Or.inr ⟨hright,hleft⟩⟩

private theorem nondegenerateCase :
    ∀ (x : Real × Real), ∀ (r : Real), ∀ (u : Real × Real), ∀ (v : Real × Real), (0 < r) → (
    let det : (Real × Real) → (Real × Real) → Real := fun a b => a.1 * b.2 - a.2 * b.1
    let uOrig := u
    let vOrig := v
    (‖uOrig‖ = 1) → ((‖vOrig‖ = 1) → (
    let dOrig := det uOrig vOrig
    (dOrig ≠ 0) → (Nonempty (P3889T1TwoRaySectorDecomposition x r u v))))) := by
  classical
  intro x r u v hr det uOrig vOrig huOrig hvOrig dOrig hd
  let positiveFirstDirection := if 0 < dOrig then uOrig else vOrig
  let positiveSecondDirection := if 0 < dOrig then vOrig else uOrig
  let d := det positiveFirstDirection positiveSecondDirection
  have hu : ‖positiveFirstDirection‖ = 1 := by
    dsimp [positiveFirstDirection]
    split_ifs with h
    · exact huOrig
    · exact hvOrig
  have hv : ‖positiveSecondDirection‖ = 1 := by
    dsimp [positiveSecondDirection]
    split_ifs with h
    · exact hvOrig
    · exact huOrig
  have hdpos := TwoRaySectorGeometry.hdpos u v hd
  let A : (Real × Real) → Real := fun p => det positiveFirstDirection (p - x)
  let B : (Real × Real) → Real := fun p => det (p - x) positiveSecondDirection
  let L : Set (Real × Real) := Metric.ball x r ∩ {p | 0 < A p} ∩ {p | 0 < B p}
  let C : Set (Real × Real) := Metric.ball x r ∩ {p | A p < 0}
  let D : Set (Real × Real) := Metric.ball x r ∩ {p | B p < 0}
  let R : Set (Real × Real) := C ∪ D
  have hdetid (y : Real × Real) : d • y = det y positiveSecondDirection •
      positiveFirstDirection + det positiveFirstDirection y • positiveSecondDirection := by
    apply Prod.ext <;> simp [d, det, smul_eq_mul] <;> ring
  have hAcont : Continuous A := by
    dsimp [A, det]
    fun_prop
  have hBcont : Continuous B := by
    dsimp [B, det]
    fun_prop
  have hballAopen : IsOpen (Metric.ball x r ∩ {p | 0 < A p}) :=
    Metric.isOpen_ball.inter (isOpen_Ioi.preimage hAcont)
  have hballBopen : IsOpen (Metric.ball x r ∩ {p | 0 < B p}) :=
    Metric.isOpen_ball.inter (isOpen_Ioi.preimage hBcont)
  have hLopen : IsOpen L := by
    dsimp [L]
    exact hballAopen.inter (isOpen_Ioi.preimage hBcont)
  have hCopen : IsOpen C := by
    dsimp [C]
    exact Metric.isOpen_ball.inter (isOpen_Iio.preimage hAcont)
  have hDopen : IsOpen D := by
    dsimp [D]
    exact Metric.isOpen_ball.inter (isOpen_Iio.preimage hBcont)
  have hRopen : IsOpen R := by
    dsimp [R]
    exact hCopen.union hDopen
  have huplusnorm : ‖positiveFirstDirection + positiveSecondDirection‖ ≤ 2 := by
    calc ‖positiveFirstDirection + positiveSecondDirection‖ ≤ ‖positiveFirstDirection‖ +
        ‖positiveSecondDirection‖ := norm_add_le _ _
      _ = 2 := by rw [hu, hv]; norm_num
  have hr4 : 0 < r / 4 := by positivity
  let q : Real × Real := x + (r / 4) • (positiveFirstDirection + positiveSecondDirection)
  have hqball : q ∈ Metric.ball x r := by
    change dist q x < r
    rw [dist_eq_norm]
    have hbound : ‖(r / 4) • (positiveFirstDirection + positiveSecondDirection)‖ ≤ r / 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < r / 4)]
      nlinarith [huplusnorm]
    have hxq : q - x = (r / 4) • (positiveFirstDirection + positiveSecondDirection) := by simp [q]
    rw [hxq]
    exact lt_of_le_of_lt hbound (by linarith)
  have hqA : 0 < A q := by
    dsimp [A, q, det]
    simp []
    nlinarith [hdpos, hu]
  have hqB : 0 < B q := by
    dsimp [B, q, det]
    simp []
    nlinarith [hdpos, hv]
  have hLne : L.Nonempty := ⟨q, ⟨⟨hqball, hqA⟩, hqB⟩⟩
  have hLconv := TwoRaySectorGeometry.hLconvAt510 x r u v
  have hLconn : IsConnected L := hLconv.isConnected hLne
  have hCconv := TwoRaySectorGeometry.hCconv x r u v
  have hDconv := TwoRaySectorGeometry.hDconv x r u v
  let qneg : Real × Real := x - (r / 4) • (positiveFirstDirection + positiveSecondDirection)
  have hqnegball : qneg ∈ Metric.ball x r := by
    change dist qneg x < r
    rw [dist_eq_norm]
    have hbound : ‖(r / 4) • (positiveFirstDirection + positiveSecondDirection)‖ ≤ r / 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < r / 4)]
      nlinarith [huplusnorm]
    have hxq : qneg - x = -((r / 4) • (positiveFirstDirection + positiveSecondDirection)) := by
        simp [qneg, sub_eq_add_neg]
    rw [hxq, norm_neg]
    exact lt_of_le_of_lt hbound (by linarith)
  have hqnegA : A qneg < 0 := by
    dsimp [A, qneg, det]
    simp []
    nlinarith [hdpos]
  have hqnegB : B qneg < 0 := by
    dsimp [B, qneg, det]
    simp []
    nlinarith [hdpos]
  have hCne : C.Nonempty := ⟨qneg, ⟨hqnegball, hqnegA⟩⟩
  have hDne : D.Nonempty := ⟨qneg, ⟨hqnegball, hqnegB⟩⟩
  have hCconn : IsConnected C := hCconv.isConnected hCne
  have hDconn : IsConnected D := hDconv.isConnected hDne
  have hCD : (C ∩ D).Nonempty := ⟨qneg,
    ⟨⟨hqnegball, hqnegA⟩, ⟨hqnegball, hqnegB⟩⟩⟩
  have hRconn : IsConnected R := by
    dsimp [R]
    exact IsConnected.union hCD hCconn hDconn
  have hAu (t : Real) : A (x + t • positiveFirstDirection) = 0 := by
    dsimp [A, det]
    simp []
    ring
  have hBu (t : Real) : B (x + t • positiveFirstDirection) = t * d := by
    dsimp [B, det, d]
    simp []
    ring
  have hAv (t : Real) : A (x + t • positiveSecondDirection) = t * d := by
    dsimp [A, det, d]
    simp []
    ring
  have hBv (t : Real) : B (x + t • positiveSecondDirection) = 0 := by
    dsimp [B, det]
    simp []
    ring
  have hdis := TwoRaySectorGeometry.hdisAt619 x r u v
  have hcoverAlias := TwoRaySectorGeometry.hcoverAlias x r u v hdpos hdetid hAu hBu hAv hBv
  have hcover := TwoRaySectorGeometry.hcoverAt724 x r u v
          hcoverAlias
  refine ⟨⟨L, R, hLopen, hRopen, hLconn, hRconn, hdis, hcover, ?_⟩⟩
  intro w hw t ht htr
  dsimp
  have hwAlias := TwoRaySectorGeometry.hwAlias u v w hw
  rcases hwAlias with hwu | hwv
  · rw [hwu]
    let z : Real × Real := x + t • positiveFirstDirection
    have hztball : z ∈ Metric.ball x r := by
      change dist z x < r
      rw [dist_eq_norm]
      have heq : z - x = t • positiveFirstDirection := by simp [z]
      rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos ht, hu]
      nlinarith
    have hBz : 0 < B z := by
      dsimp [z]
      rw [hBu]
      exact mul_pos ht hdpos
    have hNopen : IsOpen (Metric.ball x r ∩ {p | 0 < B p}) := hballBopen
    obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp
      (hNopen.mem_nhds ⟨hztball, hBz⟩)
    have hAshift (q : Real × Real) : A q =
        positiveFirstDirection.1 * (q.2 - z.2) - positiveFirstDirection.2 * (q.1 - z.1) := by
      dsimp [A, det, z]
      ring
    have hleft : L ∩ Metric.ball z δ =
    {q | q ∈ Metric.ball z δ ∧
      0 < positiveFirstDirection.1 * (q.2 - z.2) - positiveFirstDirection.2 * (q.1 - z.1)} :=
          TwoRaySectorGeometry.hleftAt789 x r u v t δ hδsub hAshift
    have hright : R ∩ Metric.ball z δ =
    {q | q ∈ Metric.ball z δ ∧
      positiveFirstDirection.1 * (q.2 - z.2) - positiveFirstDirection.2 * (q.1 - z.1) < 0} :=
          TwoRaySectorGeometry.hrightAt803 x r u v t δ hδsub hAshift
    exact ⟨δ, hδ, fun q hq => (hδsub hq).1, Or.inl ⟨hleft, hright⟩⟩
  · rw [hwv]
    let z : Real × Real := x + t • positiveSecondDirection
    have hztball : z ∈ Metric.ball x r := by
      change dist z x < r
      rw [dist_eq_norm]
      have heq : z - x = t • positiveSecondDirection := by simp [z]
      rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos ht, hv]
      simpa only [mul_one] using htr
    have hAz : 0 < A z := by
      dsimp [z]
      rw [hAv]
      exact mul_pos ht hdpos
    have hNopen : IsOpen (Metric.ball x r ∩ {p | 0 < A p}) := hballAopen
    obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp
      (hNopen.mem_nhds ⟨hztball, hAz⟩)
    have hBshift (q : Real × Real) : B q = -(positiveSecondDirection.1 * (q.2 - z.2) -
        positiveSecondDirection.2 * (q.1 - z.1)) := by
      dsimp [B, det, z]
      ring
    have hright : R ∩ Metric.ball z δ =
    {q | q ∈ Metric.ball z δ ∧
      0 < positiveSecondDirection.1 * (q.2 - z.2) - positiveSecondDirection.2 * (q.1 - z.1)} :=
          TwoRaySectorGeometry.hrightAt842 x r u v t δ hδsub hBshift
    have hleft : L ∩ Metric.ball z δ =
    {q | q ∈ Metric.ball z δ ∧
      positiveSecondDirection.1 * (q.2 - z.2) - positiveSecondDirection.2 * (q.1 - z.1) < 0} :=
          TwoRaySectorGeometry.hleftAt868 x r u v t δ hδsub hBshift
    exact ⟨δ, hδ, fun q hq => (hδsub hq).1, Or.inr ⟨hright, hleft⟩⟩

end TwoRayCasesProof

theorem P3889T1TwoRaySectors (x : Real × Real) (r : Real)
    (u v : Real × Real) (hr : 0 < r) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : u ≠ v) : Nonempty (P3889T1TwoRaySectorDecomposition x r u v) := by
-- BODY
  let det : (Real × Real) → (Real × Real) → Real := fun a b => a.1 * b.2 - a.2 * b.1
  let uOrig := u
  let vOrig := v
  have huOrig : ‖uOrig‖ = 1 := TwoRaySectorsProof.huOrig u hu
  have hvOrig : ‖vOrig‖ = 1 := TwoRaySectorsProof.hvOrig v hv
  let dOrig := det uOrig vOrig
  have degenerateCase (hd : dOrig = 0) : Nonempty (P3889T1TwoRaySectorDecomposition x r u v) :=
      TwoRayCasesProof.degenerateCase x r u v hr hu hv huv hd
  have nondegenerateCase (hd : dOrig ≠ 0) : Nonempty (P3889T1TwoRaySectorDecomposition x r u v)
      := TwoRayCasesProof.nondegenerateCase x r u v hr huOrig hvOrig hd
  by_cases hd : dOrig = 0
  · exact degenerateCase hd
  · exact nondegenerateCase hd

end ApollonianSuperharmonic

end
