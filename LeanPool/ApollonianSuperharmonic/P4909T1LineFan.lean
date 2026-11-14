/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4909T1ParentEdges
public import LeanPool.ApollonianSuperharmonic.P4828T1Rotate
public import LeanPool.ApollonianSuperharmonic.P4828T1Step
public import LeanPool.ApollonianSuperharmonic.P4953T1LiteralHulls
public import LeanPool.ApollonianSuperharmonic.P4953T1HullHeight
public import LeanPool.ApollonianSuperharmonic.P4953T1QuadrilateralSections
public import LeanPool.ApollonianSuperharmonic.P4953T1TriangleSections

-- [TABLET NODE: P4909T1LineFan]

/-!
# P4909T1LineFan

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace LineFanConstruction

private noncomputable abbrev p (q : Fin 4 → CircleCoordinates) (i : Fin 4) : ℂ := by
  classical
  exact (q i).2 / ((q i).1 : ℝ)

private noncomputable abbrev s (q : Fin 4 → CircleCoordinates) (c : Fin 3) := by
  classical
  exact P4828T1Step (P4828T1Rotate q c)

private noncomputable abbrev P (L : ℝ) (q : Fin 4 → CircleCoordinates) := by
  classical
  exact P4909T1ParentPolygon L q

private noncomputable abbrev F (L : ℝ) (q : Fin 4 → CircleCoordinates) (c : Fin 3) := by
  classical
  let s (c : Fin 3) := P4828T1Step (P4828T1Rotate q c)
  exact P4909T1ParentPolygon L (s c)

private noncomputable abbrev h (L : ℝ) (q : Fin 4 → CircleCoordinates) (l : Fin 3) := by
  classical
  exact if (q l.succ).2 = -1 then L else L + 2

private noncomputable abbrev σ (q : Fin 4 → CircleCoordinates) (l : Fin 3) : ℝ := by
  classical
  exact if (q l.succ).2 = -1 then 1 else -1

private noncomputable abbrev foot (L : ℝ) (q : Fin 4 → CircleCoordinates) (l : Fin 3) (z : ℂ) : ℂ
    := by
  classical
  let h := if (q l.succ).2 = -1 then L else L + 2
  exact ⟨h, z.im⟩

private noncomputable abbrev x (q : Fin 4 → CircleCoordinates) := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  exact p 0

private theorem hσ (q : Fin 4 → CircleCoordinates) (l : Fin 3) : (σ q l) ^ 2 = 1 := by
  classical
  let σ : ℝ := if (q l.succ).2 = -1 then 1 else -1
  change (σ ^ 2 = 1)
  dsimp [σ]; split_ifs <;> norm_num

private theorem side (L : ℝ) (q : Fin 4 → CircleCoordinates) (l : Fin 3) (hside : ∀ i : Fin 4, 0
    < (q i).1 → if (q l.succ).2 = -1 then L < (((q i).2 : ℂ) / ((q i).1 : ℝ)).re else (((q i).2 :
    ℂ) / ((q i).1 : ℝ)).re < L + 2) (i : Fin 4) (hi : 0 < (q i).1) : 0 < (σ q l) * (((p q) i).re
    - (h L q l)) := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let h := if (q l.succ).2 = -1 then L else L + 2
  let σ : ℝ := if (q l.succ).2 = -1 then 1 else -1
  change (0 < σ * ((p i).re - h))
  have hh := hside i hi
  by_cases hs : (q l.succ).2 = -1
  · simp only [hs, ite_true] at hh
    dsimp [σ, h]
    simp only [hs, ite_true, one_mul]
    exact sub_pos.mpr hh
  · simp only [hs, ite_false] at hh
    dsimp [σ, h]
    simp only [hs, ite_false, neg_one_mul]
    change 0 < -((p i).re - (L + 2))
    linarith

private noncomputable abbrev a₀ (l : Fin 3) : Fin 3 := by
  classical
  exact if l = 0 then 1 else 0

private noncomputable abbrev b₀ (l : Fin 3) : Fin 3 := by
  classical
  exact if l = 2 then 1 else 2

private theorem ha₀ (L : ℝ) (q : Fin 4 → CircleCoordinates) (l : Fin 3) (hl : (q l.succ).1 = 0)
    (hpos : ∀ i : Fin 3, i ≠ l → 0 < (q i.succ).1) (hnormal : (q l.succ).2 = -1 ∨ (q l.succ).2 =
    1) (hside : ∀ i : Fin 4, 0 < (q i).1 → if (q l.succ).2 = -1 then L < (((q i).2 : ℂ) / ((q
    i).1 : ℝ)).re else (((q i).2 : ℂ) / ((q i).1 : ℝ)).re < L + 2) : (a₀ l) ≠ l := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let h := if (q l.succ).2 = -1 then L else L + 2
  let σ : ℝ := if (q l.succ).2 = -1 then 1 else -1
  have hσ : σ ^ 2 = 1 := hσ q l
  have side (i : Fin 4) (hi : 0 < (q i).1) : 0 < σ * ((p i).re - h) := side L q l hside i hi
  let a₀ : Fin 3 := if l = 0 then 1 else 0
  change (a₀ ≠ l)
  fin_cases l <;> simp [a₀]

private theorem hb₀ (L : ℝ) (q : Fin 4 → CircleCoordinates) (l : Fin 3) (hl : (q l.succ).1 = 0)
    (hpos : ∀ i : Fin 3, i ≠ l → 0 < (q i.succ).1) (hnormal : (q l.succ).2 = -1 ∨ (q l.succ).2 =
    1) (hside : ∀ i : Fin 4, 0 < (q i).1 → if (q l.succ).2 = -1 then L < (((q i).2 : ℂ) / ((q
    i).1 : ℝ)).re else (((q i).2 : ℂ) / ((q i).1 : ℝ)).re < L + 2) : (b₀ l) ≠ l := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let h := if (q l.succ).2 = -1 then L else L + 2
  let σ : ℝ := if (q l.succ).2 = -1 then 1 else -1
  have hσ : σ ^ 2 = 1 := hσ q l
  have side (i : Fin 4) (hi : 0 < (q i).1) : 0 < σ * ((p i).re - h) := side L q l hside i hi
  let a₀ : Fin 3 := if l = 0 then 1 else 0
  let b₀ : Fin 3 := if l = 2 then 1 else 2
  have ha₀ : a₀ ≠ l := ha₀ L q l hl hpos hnormal hside
  change (b₀ ≠ l)
  fin_cases l <;> simp [b₀]

private theorem hab₀ (L : ℝ) (q : Fin 4 → CircleCoordinates) (l : Fin 3) (hl : (q l.succ).1 = 0)
    (hpos : ∀ i : Fin 3, i ≠ l → 0 < (q i.succ).1) (hnormal : (q l.succ).2 = -1 ∨ (q l.succ).2 =
    1) (hside : ∀ i : Fin 4, 0 < (q i).1 → if (q l.succ).2 = -1 then L < (((q i).2 : ℂ) / ((q
    i).1 : ℝ)).re else (((q i).2 : ℂ) / ((q i).1 : ℝ)).re < L + 2) : (a₀ l) ≠ (b₀ l) := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let h := if (q l.succ).2 = -1 then L else L + 2
  let σ : ℝ := if (q l.succ).2 = -1 then 1 else -1
  have hσ : σ ^ 2 = 1 := hσ q l
  have side (i : Fin 4) (hi : 0 < (q i).1) : 0 < σ * ((p i).re - h) := side L q l hside i hi
  let a₀ : Fin 3 := if l = 0 then 1 else 0
  let b₀ : Fin 3 := if l = 2 then 1 else 2
  have ha₀ : a₀ ≠ l := ha₀ L q l hl hpos hnormal hside
  have hb₀ : b₀ ≠ l := hb₀ L q l hl hpos hnormal hside
  change (a₀ ≠ b₀)
  fin_cases l <;> simp [a₀, b₀]

private theorem hne (L : ℝ) (q : Fin 4 → CircleCoordinates) (l : Fin 3) (hl : (q l.succ).1 = 0)
    (hpos : ∀ i : Fin 3, i ≠ l → 0 < (q i.succ).1) (hzero : 0 < (q 0).1) (hnormal : (q l.succ).2
    = -1 ∨ (q l.succ).2 = 1) (hside : ∀ i : Fin 4, 0 < (q i).1 → if (q l.succ).2 = -1 then L <
    (((q i).2 : ℂ) / ((q i).1 : ℝ)).re else (((q i).2 : ℂ) / ((q i).1 : ℝ)).re < L + 2) (hinside
    : ((q 0).2 : ℂ) / ((q 0).1 : ℝ) ∈ interior (P4909T1ParentPolygon L q)) : ((p q) (a₀
    l).succ).im ≠ ((p q) (b₀ l).succ).im := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let h := if (q l.succ).2 = -1 then L else L + 2
  let x := p 0
  let a₀ : Fin 3 := if l = 0 then 1 else 0
  let b₀ : Fin 3 := if l = 2 then 1 else 2
  have ha₀ : a₀ ≠ l := ha₀ L q l hl hpos hnormal hside
  have hb₀ : b₀ ≠ l := hb₀ L q l hl hpos hnormal hside
  have hab₀ : a₀ ≠ b₀ := hab₀ L q l hl hpos hnormal hside
  have hp₀ := (P4953T1LiteralHulls L q l a₀ b₀ ha₀ hb₀ hab₀ hl
    (hpos a₀ ha₀) (hpos b₀ hb₀) hzero).1
  have hheight := P4953T1HullHeight h (p a₀.succ) (p b₀.succ) x (by
    rw [← hp₀]; exact hinside)
  change ((p a₀.succ).im ≠ (p b₀.succ).im)
  intro he
  simp only [he, min_self, max_self] at hheight
  linarith [hheight.1, hheight.2]

private noncomputable abbrev A (q : Fin 4 → CircleCoordinates) (a : Fin 3) := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  exact p a.succ

private noncomputable abbrev B (q : Fin 4 → CircleCoordinates) (b : Fin 3) := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  exact p b.succ

private theorem classes (l : Fin 3) (a : Fin 3) (b : Fin 3) (hal : a ≠ l) (hbl : b ≠ l) (hab : a
    ≠ b) (c : Fin 3) : c = l ∨ c = a ∨ c = b := by
  classical
  omega

private theorem hvertices (L : ℝ) (q : Fin 4 → CircleCoordinates) (l : Fin 3) (a : Fin 3) (b :
    Fin 3) (hP : (P L q) = convexHull ℝ ({(A q a), (B q b), ⟨(h L q l), (A q a).im⟩, ⟨(h L q l),
    (B q b).im⟩} : Set ℂ)) : (A q a) ∈ (P L q) ∧ (B q b) ∈ (P L q) ∧ (foot L q l) (A q a) ∈ (P L
    q) ∧ (foot L q l) (B q b) ∈ (P L q) := by
  classical
  rw [hP]
  exact ⟨subset_convexHull ℝ _ (by simp), subset_convexHull ℝ _ (by simp),
    subset_convexHull ℝ _ (by simp), subset_convexHull ℝ _ (by simp)⟩

private theorem hxP (L : ℝ) (q : Fin 4 → CircleCoordinates) (hinside : ((q 0).2 : ℂ) / ((q 0).1 :
    ℝ) ∈ interior (P4909T1ParentPolygon L q)) : (x q) ∈ (P L q) := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let P := P4909T1ParentPolygon L q
  let x := p 0
  change (x ∈ P)
  exact interior_subset hinside

private theorem hfxP (L : ℝ) (q : Fin 4 → CircleCoordinates) (l : Fin 3) (hinside : ((q 0).2 : ℂ)
    / ((q 0).1 : ℝ) ∈ interior (P4909T1ParentPolygon L q)) (a : Fin 3) (b : Fin 3) (qmem : ∀ (z
    : ℂ), z ∈ ((P L q)) ↔ (A q a).im ≤ z.im ∧ z.im ≤ (B q b).im ∧ 0 ≤ (σ q l) * (z.re - (h L q
    l)) ∧ 0 ≤ (σ q l) * ((fun y => (A q a).re + ((B q b).re - (A q a).re) * (y - (A q a).im) /
    ((B q b).im - (A q a).im)) z.im - z.re)) (qint : ∀ (z : ℂ), z ∈ interior (((P L q))) ↔ (A q
    a).im < z.im ∧ z.im < (B q b).im ∧ 0 < (σ q l) * (z.re - (h L q l)) ∧ 0 < (σ q l) * ((fun y
    => (A q a).re + ((B q b).re - (A q a).re) * (y - (A q a).im) / ((B q b).im - (A q a).im))
    z.im - z.re)) (hAx : ((p q) a.succ).im < (x q).im) (hxB : (x q).im < ((p q) b.succ).im) :
    (foot L q l) (x q) ∈ (P L q) := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let P := P4909T1ParentPolygon L q
  let h := if (q l.succ).2 = -1 then L else L + 2
  let σ : ℝ := if (q l.succ).2 = -1 then 1 else -1
  let foot (z : ℂ) : ℂ := ⟨h, z.im⟩
  let x := p 0
  let A := p a.succ
  let B := p b.succ
  have hxi := (qint x).mp hinside
  change (foot x ∈ P)
  apply (qmem (foot x)).mpr
  refine ⟨hAx.le, hxB.le, ?_, ?_⟩
  · change 0 ≤ σ * (h - h)
    simp
  · change 0 ≤ σ * (A.re + (B.re - A.re) *
      (x.im - A.im) / (B.im - A.im) - h)
    nlinarith only [hxi.2.2.1, hxi.2.2.2]

private theorem convexP (L : ℝ) (q : Fin 4 → CircleCoordinates) : Convex ℝ (P L q) := by
  classical
  let P := P4909T1ParentPolygon L q
  change (Convex ℝ P)
  exact convex_convexHull ℝ _

private theorem subC (L : ℝ) (q : Fin 4 → CircleCoordinates) (l : Fin 3) (hinside : ((q 0).2 : ℂ)
    / ((q 0).1 : ℝ) ∈ interior (P4909T1ParentPolygon L q)) (a : Fin 3) (b : Fin 3) (hP : (P L
    q) = convexHull ℝ ({(A q a), (B q b), ⟨(h L q l), (A q a).im⟩, ⟨(h L q l), (B q b).im⟩} : Set
    ℂ)) (hC : (F L q) l = convexHull ℝ ({(x q), (A q a), (B q b)} : Set ℂ)) : (F L q) l ⊆ (P L q)
    := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let P := P4909T1ParentPolygon L q
  let h := if (q l.succ).2 = -1 then L else L + 2
  let foot (z : ℂ) : ℂ := ⟨h, z.im⟩
  let x := p 0
  let A := p a.succ
  let B := p b.succ
  have hvertices : A ∈ P ∧ B ∈ P ∧ foot A ∈ P ∧ foot B ∈ P := hvertices L q l a b hP
  have hxP : x ∈ P := hxP L q hinside
  have convexP : Convex ℝ P := convexP L q
  rw [hC]
  apply convexHull_min _ convexP
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl
  · exact hxP
  · exact hvertices.1
  · exact hvertices.2.1

private theorem subU (L : ℝ) (q : Fin 4 → CircleCoordinates) (l : Fin 3) (hinside : ((q 0).2 : ℂ)
    / ((q 0).1 : ℝ) ∈ interior (P4909T1ParentPolygon L q)) (a : Fin 3) (b : Fin 3) (qmem : ∀ (z
    : ℂ), z ∈ ((P L q)) ↔ (A q a).im ≤ z.im ∧ z.im ≤ (B q b).im ∧ 0 ≤ (σ q l) * (z.re - (h L q
    l)) ∧ 0 ≤ (σ q l) * ((fun y => (A q a).re + ((B q b).re - (A q a).re) * (y - (A q a).im) /
    ((B q b).im - (A q a).im)) z.im - z.re)) (qint : ∀ (z : ℂ), z ∈ interior (((P L q))) ↔ (A q
    a).im < z.im ∧ z.im < (B q b).im ∧ 0 < (σ q l) * (z.re - (h L q l)) ∧ 0 < (σ q l) * ((fun y
    => (A q a).re + ((B q b).re - (A q a).re) * (y - (A q a).im) / ((B q b).im - (A q a).im))
    z.im - z.re)) (hP : (P L q) = convexHull ℝ ({(A q a), (B q b), ⟨(h L q l), (A q a).im⟩, ⟨(h L
    q l), (B q b).im⟩} : Set ℂ)) (hU : (F L q) a = convexHull ℝ ({(x q), (B q b), ⟨(h L q l), (x
    q).im⟩, ⟨(h L q l), (B q b).im⟩} : Set ℂ)) (hAx : ((p q) a.succ).im < (x q).im) (hxB : (x
    q).im < ((p q) b.succ).im) : (F L q) a ⊆ (P L q) := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let P := P4909T1ParentPolygon L q
  let h := if (q l.succ).2 = -1 then L else L + 2
  let foot (z : ℂ) : ℂ := ⟨h, z.im⟩
  let x := p 0
  let A := p a.succ
  let B := p b.succ
  have hvertices : A ∈ P ∧ B ∈ P ∧ foot A ∈ P ∧ foot B ∈ P := hvertices L q l a b hP
  have hxP : x ∈ P := hxP L q hinside
  have hfxP : foot x ∈ P := hfxP L q l hinside a b qmem qint hAx hxB
  have convexP : Convex ℝ P := convexP L q
  rw [hU]
  apply convexHull_min _ convexP
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact hxP
  · exact hvertices.2.1
  · exact hfxP
  · exact hvertices.2.2.2

private theorem subD (L : ℝ) (q : Fin 4 → CircleCoordinates) (l : Fin 3) (hinside : ((q 0).2 : ℂ)
    / ((q 0).1 : ℝ) ∈ interior (P4909T1ParentPolygon L q)) (a : Fin 3) (b : Fin 3) (qmem : ∀ (z
    : ℂ), z ∈ ((P L q)) ↔ (A q a).im ≤ z.im ∧ z.im ≤ (B q b).im ∧ 0 ≤ (σ q l) * (z.re - (h L q
    l)) ∧ 0 ≤ (σ q l) * ((fun y => (A q a).re + ((B q b).re - (A q a).re) * (y - (A q a).im) /
    ((B q b).im - (A q a).im)) z.im - z.re)) (qint : ∀ (z : ℂ), z ∈ interior (((P L q))) ↔ (A q
    a).im < z.im ∧ z.im < (B q b).im ∧ 0 < (σ q l) * (z.re - (h L q l)) ∧ 0 < (σ q l) * ((fun y
    => (A q a).re + ((B q b).re - (A q a).re) * (y - (A q a).im) / ((B q b).im - (A q a).im))
    z.im - z.re)) (hP : (P L q) = convexHull ℝ ({(A q a), (B q b), ⟨(h L q l), (A q a).im⟩, ⟨(h L
    q l), (B q b).im⟩} : Set ℂ)) (hD : (F L q) b = convexHull ℝ ({(A q a), (x q), ⟨(h L q l), (A
    q a).im⟩, ⟨(h L q l), (x q).im⟩} : Set ℂ)) (hAx : ((p q) a.succ).im < (x q).im) (hxB : (x
    q).im < ((p q) b.succ).im) : (F L q) b ⊆ (P L q) := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let P := P4909T1ParentPolygon L q
  let h := if (q l.succ).2 = -1 then L else L + 2
  let foot (z : ℂ) : ℂ := ⟨h, z.im⟩
  let x := p 0
  let A := p a.succ
  let B := p b.succ
  have hvertices : A ∈ P ∧ B ∈ P ∧ foot A ∈ P ∧ foot B ∈ P := hvertices L q l a b hP
  have hxP : x ∈ P := hxP L q hinside
  have hfxP : foot x ∈ P := hfxP L q l hinside a b qmem qint hAx hxB
  have convexP : Convex ℝ P := convexP L q
  rw [hD]
  apply convexHull_min _ convexP
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact hvertices.1
  · exact hxP
  · exact hvertices.2.2.1
  · exact hfxP

private theorem root (q : Fin 4 → CircleCoordinates) (slots : ∀ (c j : Fin 3), (fun c =>
    ApollonianSuperharmonic.P4828T1Step (ApollonianSuperharmonic.P4828T1Rotate q c)) c j.succ
    = if j = 0 then q 0 else q (j + c).succ) (c : Fin 3) : (s q) c (0 : Fin 3).succ = q 0 := by
  classical
  let s (c : Fin 3) := P4828T1Step (P4828T1Rotate q c)
  change (s c (0 : Fin 3).succ = q 0)
  exact (slots c 0).trans (ite_eq_left rfl)

private theorem keep (q : Fin 4 → CircleCoordinates) (slots : ∀ (c j : Fin 3), (fun c =>
    ApollonianSuperharmonic.P4828T1Step (ApollonianSuperharmonic.P4828T1Rotate q c)) c j.succ
    = if j = 0 then q 0 else q (j + c).succ) (c i : Fin 3) (hi : i ≠ c) : (s q) c (i - c).succ =
    q i.succ := by
  classical
  let s (c : Fin 3) := P4828T1Step (P4828T1Rotate q c)
  change (s c (i - c).succ = q i.succ)
  simpa only [ite_eq_right (sub_ne_zero.mpr hi), sub_add_cancel] using slots c (i - c)

private theorem radial (L : ℝ) (q : Fin 4 → CircleCoordinates) (hzero : 0 < (q 0).1) (slots : ∀
    (c j : Fin 3), (fun c => ApollonianSuperharmonic.P4828T1Step
    (ApollonianSuperharmonic.P4828T1Rotate q c)) c j.succ = if j = 0 then q 0 else q (j +
    c).succ) (c i : Fin 3) (hi : i ≠ c) (hpi : 0 < (q i.succ).1) : segment ℝ (x q) ((p q) i.succ)
    ⊆ P4909T1ParentEdges L ((s q) c) := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let s (c : Fin 3) := P4828T1Step (P4828T1Rotate q c)
  let x := p 0
  have root (c : Fin 3) : s c (0 : Fin 3).succ = q 0 := root q slots c
  have keep (c i : Fin 3) (hi : i ≠ c) : s c (i - c).succ = q i.succ := keep q slots c i hi
  change (segment ℝ x (p i.succ) ⊆ P4909T1ParentEdges L (s c))
  intro z hz
  apply Or.inl
  refine ⟨0, i - c, (sub_ne_zero.mpr hi).symm, ?_, ?_, ?_⟩
  · rw [root]; exact hzero
  · rw [keep c i hi]; exact hpi
  · simpa only [root, keep c i hi] using hz

private theorem retained (L : ℝ) (q : Fin 4 → CircleCoordinates) (slots : ∀ (c j : Fin 3), (fun c
    => ApollonianSuperharmonic.P4828T1Step (ApollonianSuperharmonic.P4828T1Rotate q c)) c
    j.succ = if j = 0 then q 0 else q (j + c).succ) (c i j : Fin 3) (hi : i ≠ c) (hj : j ≠ c)
    (hij : i ≠ j) (hpi : 0 < (q i.succ).1) (hpj : 0 < (q j.succ).1) : segment ℝ ((p q) i.succ)
    ((p q) j.succ) ⊆ P4909T1ParentEdges L ((s q) c) := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let s (c : Fin 3) := P4828T1Step (P4828T1Rotate q c)
  have keep (c i : Fin 3) (hi : i ≠ c) : s c (i - c).succ = q i.succ := keep q slots c i hi
  change (segment ℝ (p i.succ) (p j.succ) ⊆ P4909T1ParentEdges L (s c))
  intro z hz
  apply Or.inl
  refine ⟨i - c, j - c, fun he => hij (sub_left_inj.mp he), ?_, ?_, ?_⟩
  · rw [keep c i hi]; exact hpi
  · rw [keep c j hj]; exact hpj
  · simpa only [keep c i hi, keep c j hj] using hz

private theorem rootFoot (L : ℝ) (q : Fin 4 → CircleCoordinates) (l : Fin 3) (hl : (q l.succ).1 =
    0) (hzero : 0 < (q 0).1) (slots : ∀ (c j : Fin 3), (fun c =>
    ApollonianSuperharmonic.P4828T1Step (ApollonianSuperharmonic.P4828T1Rotate q c)) c j.succ
    = if j = 0 then q 0 else q (j + c).succ) (c : Fin 3) (hc : l ≠ c) : segment ℝ (x q) ((foot L
    q l) (x q)) ⊆ P4909T1ParentEdges L ((s q) c) := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let s (c : Fin 3) := P4828T1Step (P4828T1Rotate q c)
  let h := if (q l.succ).2 = -1 then L else L + 2
  let foot (z : ℂ) : ℂ := ⟨h, z.im⟩
  let x := p 0
  have root (c : Fin 3) : s c (0 : Fin 3).succ = q 0 := root q slots c
  have keep (c i : Fin 3) (hi : i ≠ c) : s c (i - c).succ = q i.succ := keep q slots c i hi
  change (segment ℝ x (foot x) ⊆ P4909T1ParentEdges L (s c))
  intro z hz
  apply Or.inr ∘ Or.inl
  refine ⟨0, l - c, ?_, ?_, ?_⟩
  · rw [root]; exact hzero
  · rw [keep c l hc]; exact hl
  · simpa only [root, keep c l hc] using hz

private theorem retainedFoot (L : ℝ) (q : Fin 4 → CircleCoordinates) (l : Fin 3) (hl : (q
    l.succ).1 = 0) (slots : ∀ (c j : Fin 3), (fun c => ApollonianSuperharmonic.P4828T1Step
    (ApollonianSuperharmonic.P4828T1Rotate q c)) c j.succ = if j = 0 then q 0 else q (j +
    c).succ) (c i : Fin 3) (hc : l ≠ c) (hi : i ≠ c) (hpi : 0 < (q i.succ).1) : segment ℝ ((p q)
    i.succ) ((foot L q l) ((p q) i.succ)) ⊆ P4909T1ParentEdges L ((s q) c) := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let s (c : Fin 3) := P4828T1Step (P4828T1Rotate q c)
  let h := if (q l.succ).2 = -1 then L else L + 2
  let foot (z : ℂ) : ℂ := ⟨h, z.im⟩
  have keep (c i : Fin 3) (hi : i ≠ c) : s c (i - c).succ = q i.succ := keep q slots c i hi
  change (segment ℝ (p i.succ) (foot (p i.succ)) ⊆ P4909T1ParentEdges L (s c))
  intro z hz
  apply Or.inr ∘ Or.inl
  refine ⟨i - c, l - c, ?_, ?_, ?_⟩
  · rw [keep c i hi]; exact hpi
  · rw [keep c l hc]; exact hl
  · simpa only [keep c i hi, keep c l hc] using hz

private theorem lineCarrier (L : ℝ) (q : Fin 4 → CircleCoordinates) (l : Fin 3) (hl : (q
    l.succ).1 = 0) (slots : ∀ (c j : Fin 3), (fun c => ApollonianSuperharmonic.P4828T1Step
    (ApollonianSuperharmonic.P4828T1Rotate q c)) c j.succ = if j = 0 then q 0 else q (j +
    c).succ) (c : Fin 3) (hc : l ≠ c) : {z : ℂ | z.re = (h L q l)} ⊆ P4909T1ParentEdges L ((s
    q) c) := by
  classical
  let s (c : Fin 3) := P4828T1Step (P4828T1Rotate q c)
  let h := if (q l.succ).2 = -1 then L else L + 2
  have keep (c i : Fin 3) (hi : i ≠ c) : s c (i - c).succ = q i.succ := keep q slots c i hi
  change ({z : ℂ | z.re = h} ⊆ P4909T1ParentEdges L (s c))
  intro z hz
  apply Or.inr ∘ Or.inr
  refine ⟨l - c, ?_, ?_⟩
  · rw [keep c l hc]; exact hl
  · rw [keep c l hc]
    exact hz

private theorem footLine (L : ℝ) (q : Fin 4 → CircleCoordinates) (l : Fin 3) (u v : ℂ) : segment
    ℝ ((foot L q l) u) ((foot L q l) v) ⊆ {z : ℂ | z.re = (h L q l)} := by
  classical
  let h := if (q l.succ).2 = -1 then L else L + 2
  let foot (z : ℂ) : ℂ := ⟨h, z.im⟩
  change (segment ℝ (foot u) (foot v) ⊆ {z : ℂ | z.re = h})
  rintro z ⟨r, t, _, _, hrt, rfl⟩
  change (r • foot u + t • foot v).re = h
  simp only [Complex.add_re, Complex.smul_re]
  change r * h + t * h = h
  rw [← add_mul, hrt, one_mul]

private theorem frontC (L : ℝ) (q : Fin 4 → CircleCoordinates) (l : Fin 3) (hpos : ∀ i : Fin 3, i
    ≠ l → 0 < (q i.succ).1) (hzero : 0 < (q 0).1) (a : Fin 3) (b : Fin 3) (tfront : frontier (((F
    L q) l)) = segment ℝ (x q) (A q a) ∪ segment ℝ (x q) (B q b) ∪ segment ℝ (A q a) (B q b))
    (slots : ∀ (c j : Fin 3), (fun c => ApollonianSuperharmonic.P4828T1Step
    (ApollonianSuperharmonic.P4828T1Rotate q c)) c j.succ = if j = 0 then q 0 else q (j +
    c).succ) (hal : a ≠ l) (hbl : b ≠ l) (hab : a ≠ b) : frontier ((F L q) l) ⊆
    P4909T1ParentEdges L ((s q) l) := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let s (c : Fin 3) := P4828T1Step (P4828T1Rotate q c)
  let x := p 0
  have ha := hpos a hal
  have hb := hpos b hbl
  have radial (c i : Fin 3) (hi : i ≠ c) (hpi : 0 < (q i.succ).1) :
      segment ℝ x (p i.succ) ⊆ P4909T1ParentEdges L (s c) := radial L q hzero slots c i hi hpi
  have retained (c i j : Fin 3) (hi : i ≠ c) (hj : j ≠ c)
      (hij : i ≠ j) (hpi : 0 < (q i.succ).1) (hpj : 0 < (q j.succ).1) :
      segment ℝ (p i.succ) (p j.succ) ⊆ P4909T1ParentEdges L (s c) := retained L q slots c i j
          hi hj hij hpi hpj
  rw [tfront]
  exact Set.union_subset (Set.union_subset (radial l a hal ha) (radial l b hbl hb))
    (retained l a b hal hbl hab ha hb)

private theorem frontU (L : ℝ) (q : Fin 4 → CircleCoordinates) (l : Fin 3) (hl : (q l.succ).1 =
    0) (hpos : ∀ i : Fin 3, i ≠ l → 0 < (q i.succ).1) (hzero : 0 < (q 0).1) (a : Fin 3) (b : Fin
    3) (ufront : frontier (((F L q) a)) = segment ℝ (x q) (B q b) ∪ segment ℝ (x q) ⟨(h L q l),
    (x q).im⟩ ∪ segment ℝ (B q b) ⟨(h L q l), (B q b).im⟩ ∪ segment ℝ ⟨(h L q l), (x q).im⟩ ⟨(h L
    q l), (B q b).im⟩) (slots : ∀ (c j : Fin 3), (fun c => ApollonianSuperharmonic.P4828T1Step
    (ApollonianSuperharmonic.P4828T1Rotate q c)) c j.succ = if j = 0 then q 0 else q (j +
    c).succ) (hal : a ≠ l) (hbl : b ≠ l) (hab : a ≠ b) : frontier ((F L q) a) ⊆
    P4909T1ParentEdges L ((s q) a) := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let s (c : Fin 3) := P4828T1Step (P4828T1Rotate q c)
  let h := if (q l.succ).2 = -1 then L else L + 2
  let foot (z : ℂ) : ℂ := ⟨h, z.im⟩
  let x := p 0
  let B := p b.succ
  have hb := hpos b hbl
  have radial (c i : Fin 3) (hi : i ≠ c) (hpi : 0 < (q i.succ).1) :
      segment ℝ x (p i.succ) ⊆ P4909T1ParentEdges L (s c) := radial L q hzero slots c i hi hpi
  have rootFoot (c : Fin 3) (hc : l ≠ c) :
      segment ℝ x (foot x) ⊆ P4909T1ParentEdges L (s c) := rootFoot L q l hl hzero slots c hc
  have retainedFoot (c i : Fin 3) (hc : l ≠ c) (hi : i ≠ c)
      (hpi : 0 < (q i.succ).1) :
      segment ℝ (p i.succ) (foot (p i.succ)) ⊆ P4909T1ParentEdges L (s c) := retainedFoot L q l
          hl slots c i hc hi hpi
  have lineCarrier (c : Fin 3) (hc : l ≠ c) :
      {z : ℂ | z.re = h} ⊆ P4909T1ParentEdges L (s c) := lineCarrier L q l hl slots c hc
  have footLine (u v : ℂ) : segment ℝ (foot u) (foot v) ⊆ {z : ℂ | z.re = h} := footLine L q l u v
  rw [ufront]
  exact Set.union_subset (Set.union_subset (Set.union_subset (radial a b hab.symm hb)
    (rootFoot a hal.symm)) (retainedFoot a b hal.symm hab.symm hb))
    ((footLine x B).trans (lineCarrier a hal.symm))

private theorem frontD (L : ℝ) (q : Fin 4 → CircleCoordinates) (l : Fin 3) (hl : (q l.succ).1 =
    0) (hpos : ∀ i : Fin 3, i ≠ l → 0 < (q i.succ).1) (hzero : 0 < (q 0).1) (a : Fin 3) (b : Fin
    3) (dfront : frontier (((F L q) b)) = segment ℝ (A q a) (x q) ∪ segment ℝ (A q a) ⟨(h L q l),
    (A q a).im⟩ ∪ segment ℝ (x q) ⟨(h L q l), (x q).im⟩ ∪ segment ℝ ⟨(h L q l), (A q a).im⟩ ⟨(h L
    q l), (x q).im⟩) (slots : ∀ (c j : Fin 3), (fun c => ApollonianSuperharmonic.P4828T1Step
    (ApollonianSuperharmonic.P4828T1Rotate q c)) c j.succ = if j = 0 then q 0 else q (j +
    c).succ) (hal : a ≠ l) (hbl : b ≠ l) (hab : a ≠ b) : frontier ((F L q) b) ⊆
    P4909T1ParentEdges L ((s q) b) := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let s (c : Fin 3) := P4828T1Step (P4828T1Rotate q c)
  let F (c : Fin 3) := P4909T1ParentPolygon L (s c)
  let h := if (q l.succ).2 = -1 then L else L + 2
  let foot (z : ℂ) : ℂ := ⟨h, z.im⟩
  let x := p 0
  let A := p a.succ
  have ha := hpos a hal
  have radial (c i : Fin 3) (hi : i ≠ c) (hpi : 0 < (q i.succ).1) :
      segment ℝ x (p i.succ) ⊆ P4909T1ParentEdges L (s c) := radial L q hzero slots c i hi hpi
  have rootFoot (c : Fin 3) (hc : l ≠ c) :
      segment ℝ x (foot x) ⊆ P4909T1ParentEdges L (s c) := rootFoot L q l hl hzero slots c hc
  have retainedFoot (c i : Fin 3) (hc : l ≠ c) (hi : i ≠ c)
      (hpi : 0 < (q i.succ).1) :
      segment ℝ (p i.succ) (foot (p i.succ)) ⊆ P4909T1ParentEdges L (s c) := retainedFoot L q l
          hl slots c i hc hi hpi
  have lineCarrier (c : Fin 3) (hc : l ≠ c) :
      {z : ℂ | z.re = h} ⊆ P4909T1ParentEdges L (s c) := lineCarrier L q l hl slots c hc
  have footLine (u v : ℂ) : segment ℝ (foot u) (foot v) ⊆ {z : ℂ | z.re = h} := footLine L q l u v
  change (frontier (F b) ⊆ P4909T1ParentEdges L (s b))
  rw [dfront, segment_symm ℝ A x]
  exact Set.union_subset (Set.union_subset (Set.union_subset (radial b a hab ha)
    (retainedFoot b a hbl.symm hab ha)) (rootFoot b hbl.symm))
    ((footLine A x).trans (lineCarrier b hbl.symm))

private theorem sepCU (L : ℝ) (q : Fin 4 → CircleCoordinates) (l : Fin 3) (a : Fin 3) (b : Fin 3)
    (uint : ∀ (z : ℂ), z ∈ interior (((F L q) a)) ↔ (x q).im < z.im ∧ z.im < (B q b).im ∧ 0 < (σ
    q l) * (z.re - (h L q l)) ∧ 0 < (σ q l) * ((fun y => (x q).re + ((B q b).re - (x q).re) * (y
    - (x q).im) / ((B q b).im - (x q).im)) z.im - z.re)) (tint : ∀ (z : ℂ), z ∈ interior (((F L
    q) l)) ↔ 0 < (σ q l) * ((fun y => (A q a).re + ((B q b).re - (A q a).re) * (y - (A q a).im) /
    ((B q b).im - (A q a).im)) z.im - z.re) ∧ 0 < (σ q l) * (z.re - (fun y => (A q a).re + ((x
    q).re - (A q a).re) * (y - (A q a).im) / ((x q).im - (A q a).im)) z.im) ∧ 0 < (σ q l) * (z.re
    - (fun y => (x q).re + ((B q b).re - (x q).re) * (y - (x q).im) / ((B q b).im - (x q).im))
    z.im)) : Disjoint (interior ((F L q) l)) (interior ((F L q) a)) := by
  classical
  let s (c : Fin 3) := P4828T1Step (P4828T1Rotate q c)
  let F (c : Fin 3) := P4909T1ParentPolygon L (s c)
  change (Disjoint (interior (F l)) (interior (F a)))
  apply Set.disjoint_left.mpr
  intro z ht hu
  have ht' := ((tint z).mp ht).2.2
  have hu' := ((uint z).mp hu).2.2.2
  nlinarith only [ht', hu']

private theorem sepCD (L : ℝ) (q : Fin 4 → CircleCoordinates) (l : Fin 3) (a : Fin 3) (b : Fin 3)
    (dint : ∀ (z : ℂ), z ∈ interior (((F L q) b)) ↔ (A q a).im < z.im ∧ z.im < (x q).im ∧ 0 < (σ
    q l) * (z.re - (h L q l)) ∧ 0 < (σ q l) * ((fun y => (A q a).re + ((x q).re - (A q a).re) *
    (y - (A q a).im) / ((x q).im - (A q a).im)) z.im - z.re)) (tint : ∀ (z : ℂ), z ∈ interior
    (((F L q) l)) ↔ 0 < (σ q l) * ((fun y => (A q a).re + ((B q b).re - (A q a).re) * (y - (A q
    a).im) / ((B q b).im - (A q a).im)) z.im - z.re) ∧ 0 < (σ q l) * (z.re - (fun y => (A q a).re
    + ((x q).re - (A q a).re) * (y - (A q a).im) / ((x q).im - (A q a).im)) z.im) ∧ 0 < (σ q l) *
    (z.re - (fun y => (x q).re + ((B q b).re - (x q).re) * (y - (x q).im) / ((B q b).im - (x
    q).im)) z.im)) : Disjoint (interior ((F L q) l)) (interior ((F L q) b)) := by
  classical
  let s (c : Fin 3) := P4828T1Step (P4828T1Rotate q c)
  let F (c : Fin 3) := P4909T1ParentPolygon L (s c)
  change (Disjoint (interior (F l)) (interior (F b)))
  apply Set.disjoint_left.mpr
  intro z ht hd
  have ht' := ((tint z).mp ht).2.1
  have hd' := ((dint z).mp hd).2.2.2
  nlinarith only [ht', hd']

private theorem sepUD (L : ℝ) (q : Fin 4 → CircleCoordinates) (l : Fin 3) (a : Fin 3) (b : Fin 3)
    (dint : ∀ (z : ℂ), z ∈ interior (((F L q) b)) ↔ (A q a).im < z.im ∧ z.im < (x q).im ∧ 0 < (σ
    q l) * (z.re - (h L q l)) ∧ 0 < (σ q l) * ((fun y => (A q a).re + ((x q).re - (A q a).re) *
    (y - (A q a).im) / ((x q).im - (A q a).im)) z.im - z.re)) (uint : ∀ (z : ℂ), z ∈ interior
    (((F L q) a)) ↔ (x q).im < z.im ∧ z.im < (B q b).im ∧ 0 < (σ q l) * (z.re - (h L q l)) ∧ 0 <
    (σ q l) * ((fun y => (x q).re + ((B q b).re - (x q).re) * (y - (x q).im) / ((B q b).im - (x
    q).im)) z.im - z.re)) : Disjoint (interior ((F L q) a)) (interior ((F L q) b)) := by
  classical
  let s (c : Fin 3) := P4828T1Step (P4828T1Rotate q c)
  let F (c : Fin 3) := P4909T1ParentPolygon L (s c)
  change (Disjoint (interior (F a)) (interior (F b)))
  apply Set.disjoint_left.mpr
  intro z hu hd
  exact (not_lt_of_gt ((uint z).mp hu).1) ((dint z).mp hd).2.1

private theorem cover (L : ℝ) (q : Fin 4 → CircleCoordinates) (l : Fin 3) (a : Fin 3) (b : Fin 3)
    (qmem : ∀ (z : ℂ), z ∈ ((P L q)) ↔ (A q a).im ≤ z.im ∧ z.im ≤ (B q b).im ∧ 0 ≤ (σ q l) *
    (z.re - (h L q l)) ∧ 0 ≤ (σ q l) * ((fun y => (A q a).re + ((B q b).re - (A q a).re) * (y -
    (A q a).im) / ((B q b).im - (A q a).im)) z.im - z.re)) (dmem : ∀ (z : ℂ), z ∈ ((F L q) b) ↔
    (A q a).im ≤ z.im ∧ z.im ≤ (x q).im ∧ 0 ≤ (σ q l) * (z.re - (h L q l)) ∧ 0 ≤ (σ q l) * ((fun
    y => (A q a).re + ((x q).re - (A q a).re) * (y - (A q a).im) / ((x q).im - (A q a).im)) z.im
    - z.re)) (tlower : ∀ (z : ℂ), (A q a).im ≤ z.im → z.im ≤ (x q).im → (z ∈ ((F L q) l) ↔ 0 ≤ (σ
    q l) * (z.re - (fun y => (A q a).re + ((x q).re - (A q a).re) * (y - (A q a).im) / ((x q).im
    - (A q a).im)) z.im) ∧ 0 ≤ (σ q l) * ((fun y => (A q a).re + ((B q b).re - (A q a).re) * (y -
    (A q a).im) / ((B q b).im - (A q a).im)) z.im - z.re))) (umem : ∀ (z : ℂ), z ∈ ((F L q) a) ↔
    (x q).im ≤ z.im ∧ z.im ≤ (B q b).im ∧ 0 ≤ (σ q l) * (z.re - (h L q l)) ∧ 0 ≤ (σ q l) * ((fun
    y => (x q).re + ((B q b).re - (x q).re) * (y - (x q).im) / ((B q b).im - (x q).im)) z.im -
    z.re)) (tupper : ∀ (z : ℂ), (x q).im ≤ z.im → z.im ≤ (B q b).im → (z ∈ ((F L q) l) ↔ 0 ≤ (σ q
    l) * (z.re - (fun y => (x q).re + ((B q b).re - (x q).re) * (y - (x q).im) / ((B q b).im - (x
    q).im)) z.im) ∧ 0 ≤ (σ q l) * ((fun y => (A q a).re + ((B q b).re - (A q a).re) * (y - (A q
    a).im) / ((B q b).im - (A q a).im)) z.im - z.re))) (z : ℂ) (hz : z ∈ (P L q)) : ∃ c, z ∈ (F L
    q) c := by
  classical
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let s (c : Fin 3) := P4828T1Step (P4828T1Rotate q c)
  let F (c : Fin 3) := P4909T1ParentPolygon L (s c)
  let σ : ℝ := if (q l.succ).2 = -1 then 1 else -1
  let x := p 0
  let A := p a.succ
  let B := p b.succ
  change (∃ c, z ∈ F c)
  have hz' := (qmem z).mp hz
  by_cases hm : z.im ≤ x.im
  · by_cases he : 0 ≤ σ * (A.re + (x.re - A.re) *
        (z.im - A.im) / (x.im - A.im) - z.re)
    · exact ⟨b, (dmem z).mpr ⟨hz'.1, hm, hz'.2.2.1, he⟩⟩
    · refine ⟨l, (tlower z hz'.1 hm).mpr ⟨?_, hz'.2.2.2⟩⟩
      nlinarith only [he]
  · have hm' : x.im ≤ z.im := (not_le.mp hm).le
    by_cases he : 0 ≤ σ * (x.re + (B.re - x.re) *
        (z.im - x.im) / (B.im - x.im) - z.re)
    · exact ⟨a, (umem z).mpr ⟨hm', hz'.2.1, hz'.2.2.1, he⟩⟩
    · refine ⟨l, (tupper z hm' hz'.2.1).mpr ⟨?_, hz'.2.2.2⟩⟩
      nlinarith only [he]

end LineFanConstruction

theorem P4909T1LineFan (L : ℝ) (q : Fin 4 → CircleCoordinates)
    (l : Fin 3) (hl : (q l.succ).1 = 0)
    (hpos : ∀ i : Fin 3, i ≠ l → 0 < (q i.succ).1)
    (hzero : 0 < (q 0).1)
    (hnormal : (q l.succ).2 = -1 ∨ (q l.succ).2 = 1)
    (hside : ∀ i : Fin 4, 0 < (q i).1 →
      if (q l.succ).2 = -1 then L < (((q i).2 : ℂ) / ((q i).1 : ℝ)).re
      else (((q i).2 : ℂ) / ((q i).1 : ℝ)).re < L + 2)
    (hinside : ((q 0).2 : ℂ) / ((q 0).1 : ℝ) ∈ interior (P4909T1ParentPolygon L q)) :
    let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
    let s (b : Fin 3) := P4828T1Step (P4828T1Rotate q b)
    let P := P4909T1ParentPolygon L q
    let F (b : Fin 3) := P4909T1ParentPolygon L (s b)
    (∀ b, F b ⊆ P ∧ (0 < (q b.succ).1 → p b.succ ∉ F b) ∧
      frontier (F b) ⊆ P4909T1ParentEdges L (s b)) ∧
    (∀ b c, b ≠ c → Disjoint (interior (F b)) (interior (F c))) ∧
    P = ⋃ b, F b ∧
    (∀ z ∈ interior P,
      (∀ i : Fin 4, 0 < (q i).1 → z ∉ segment ℝ (p 0) (p i)) →
      (∀ k : Fin 3, (q k.succ).1 = 0 →
        z ∉ segment ℝ (p 0)
          ⟨if (q k.succ).2 = -1 then L else L + 2, (p 0).im⟩) →
      ∃ b, z ∈ interior (F b)) := by
-- BODY
  classical
  dsimp only
  let p (i : Fin 4) : ℂ := (q i).2 / ((q i).1 : ℝ)
  let s (c : Fin 3) := P4828T1Step (P4828T1Rotate q c)
  let P := P4909T1ParentPolygon L q
  let F (c : Fin 3) := P4909T1ParentPolygon L (s c)
  let h := if (q l.succ).2 = -1 then L else L + 2
  let σ : ℝ := if (q l.succ).2 = -1 then 1 else -1
  let foot (z : ℂ) : ℂ := ⟨h, z.im⟩
  let x := p 0
  have hσ : σ ^ 2 = 1 := LineFanConstruction.hσ q l
  have side (i : Fin 4) (hi : 0 < (q i).1) : 0 < σ * ((p i).re - h) := LineFanConstruction.side L
      q l hside i hi
  -- The interior assumption, not an extra hypothesis, orders the parent heights.
  let a₀ : Fin 3 := if l = 0 then 1 else 0
  let b₀ : Fin 3 := if l = 2 then 1 else 2
  have ha₀ : a₀ ≠ l := LineFanConstruction.ha₀ L q l hl hpos hnormal hside
  have hb₀ : b₀ ≠ l := LineFanConstruction.hb₀ L q l hl hpos hnormal hside
  have hab₀ : a₀ ≠ b₀ := LineFanConstruction.hab₀ L q l hl hpos hnormal hside
  have hp₀ := (P4953T1LiteralHulls L q l a₀ b₀ ha₀ hb₀ hab₀ hl
    (hpos a₀ ha₀) (hpos b₀ hb₀) hzero).1
  change P = convexHull ℝ
    ({p a₀.succ, p b₀.succ, ⟨h, (p a₀.succ).im⟩, ⟨h, (p b₀.succ).im⟩} : Set ℂ) at hp₀
  have hheight := P4953T1HullHeight h (p a₀.succ) (p b₀.succ) x (by
    rw [← hp₀]; exact hinside)
  have hne : (p a₀.succ).im ≠ (p b₀.succ).im := LineFanConstruction.hne L q l hl hpos hzero
      hnormal hside hinside
  obtain ⟨a, b, hal, hbl, hab, hAx, hxB⟩ : ∃ a b : Fin 3,
      a ≠ l ∧ b ≠ l ∧ a ≠ b ∧ (p a.succ).im < x.im ∧ x.im < (p b.succ).im := by
    rcases lt_or_gt_of_ne hne with hh | hh
    · exact ⟨a₀, b₀, ha₀, hb₀, hab₀, by
        simpa only [min_eq_left hh.le] using hheight.1, by
        simpa only [max_eq_right hh.le] using hheight.2⟩
    · exact ⟨b₀, a₀, hb₀, ha₀, hab₀.symm, by
        simpa only [min_eq_right hh.le] using hheight.1, by
        simpa only [max_eq_left hh.le] using hheight.2⟩
  let A := p a.succ
  let B := p b.succ
  have ha := hpos a hal
  have hb := hpos b hbl
  have classes (c : Fin 3) : c = l ∨ c = a ∨ c = b := LineFanConstruction.classes l a b hal hbl
      hab c
  obtain ⟨hP, hC, hU, hD, slots⟩ :=
    P4953T1LiteralHulls L q l a b hal hbl hab hl ha hb hzero
  change P = convexHull ℝ ({A, B, foot A, foot B} : Set ℂ) at hP
  change F l = convexHull ℝ ({x, A, B} : Set ℂ) at hC
  change F a = convexHull ℝ ({x, B, foot x, foot B} : Set ℂ) at hU
  change F b = convexHull ℝ ({A, x, foot A, foot x} : Set ℂ) at hD
  have hA := side a.succ ha
  have hB := side b.succ hb
  have hx := side 0 hzero
  obtain ⟨qmem, qint, qfront⟩ :=
    P4953T1QuadrilateralSections h σ A B hσ hA hB (hAx.trans hxB)
  obtain ⟨dmem, dint, dfront⟩ :=
    P4953T1QuadrilateralSections h σ A x hσ hA hx hAx
  obtain ⟨umem, uint, ufront⟩ :=
    P4953T1QuadrilateralSections h σ x B hσ hx hB hxB
  rw [← hP] at qmem qint qfront
  rw [← hD] at dmem dint dfront
  rw [← hU] at umem uint ufront
  have hxi := (qint x).mp hinside
  obtain ⟨tint, tlower, tupper, tfront⟩ :=
    P4953T1TriangleSections σ A x B hAx hxB hxi.2.2.2
  rw [← hC] at tint tlower tupper tfront
  -- Containment uses only convexity and the inserted foot's actual height.
  have subC : F l ⊆ P := LineFanConstruction.subC L q l hinside a b hP hC
  have subU : F a ⊆ P := LineFanConstruction.subU L q l hinside a b qmem qint hP hU hAx hxB
  have subD : F b ⊆ P := LineFanConstruction.subD L q l hinside a b qmem qint hP hD hAx hxB
  have sub (c : Fin 3) : F c ⊆ P := by
    rcases classes c with rfl | rfl | rfl
    · exact subC
    · exact subU
    · exact subD
  have omitted (c : Fin 3) (hc : 0 < (q c.succ).1) : p c.succ ∉ F c := by
    rcases classes c with rfl | rfl | rfl
    · omega
    · intro hz
      exact (not_le_of_gt hAx) ((umem A).mp hz).1
    · intro hz
      exact (not_le_of_gt hxB) ((dmem B).mp hz).2.1
  -- Build the literal edge witnesses without identifying same-center records.
  have footLine (u v : ℂ) : segment ℝ (foot u) (foot v) ⊆ {z : ℂ | z.re = h} :=
      LineFanConstruction.footLine L q l u v
  have frontC : frontier (F l) ⊆ P4909T1ParentEdges L (s l) := LineFanConstruction.frontC L q l
      hpos hzero a b tfront slots hal hbl hab
  have frontU : frontier (F a) ⊆ P4909T1ParentEdges L (s a) := LineFanConstruction.frontU L q l
      hl hpos hzero a b ufront slots hal hbl hab
  have frontD : frontier (F b) ⊆ P4909T1ParentEdges L (s b) := LineFanConstruction.frontD L q l
      hl hpos hzero a b dfront slots hal hbl hab
  have front (c : Fin 3) : frontier (F c) ⊆ P4909T1ParentEdges L (s c) := by
    rcases classes c with rfl | rfl | rfl
    · exact frontC
    · exact frontU
    · exact frontD
  -- Strict affine inequalities separate the central and lateral interiors.
  have sepCU : Disjoint (interior (F l)) (interior (F a)) := LineFanConstruction.sepCU L q l a b
      uint tint
  have sepCD : Disjoint (interior (F l)) (interior (F b)) := LineFanConstruction.sepCD L q l a b
      dint tint
  have sepUD : Disjoint (interior (F a)) (interior (F b)) := LineFanConstruction.sepUD L q l a b
      dint uint
  have sep (c d : Fin 3) (hcd : c ≠ d) : Disjoint (interior (F c)) (interior (F d)) := by
    rcases classes c with rfl | rfl | rfl
    · rcases classes d with rfl | rfl | rfl
      · exact (hcd rfl).elim
      · exact sepCU
      · exact sepCD
    · rcases classes d with rfl | rfl | rfl
      · exact sepCU.symm
      · exact (hcd rfl).elim
      · exact sepUD
    · rcases classes d with rfl | rfl | rfl
      · exact sepCD.symm
      · exact sepUD.symm
      · exact (hcd rfl).elim
  have cover (z : ℂ) (hz : z ∈ P) : ∃ c, z ∈ F c := LineFanConstruction.cover L q l a b qmem dmem
      tlower umem tupper z hz
  refine ⟨fun c => ⟨sub c, omitted c, front c⟩, sep, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · intro z hz
      exact Set.mem_iUnion.mpr (cover z hz)
    · intro z hz
      obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hz
      exact sub c hc
  · intro z hz hseams hfeet
    have noA : z ∉ segment ℝ x A := hseams a.succ ha
    have noB : z ∉ segment ℝ x B := hseams b.succ hb
    have noFoot : z ∉ segment ℝ x (foot x) := hfeet l hl
    have noLine (he : z.re = h) : False := by
      have hp := ((qint z).mp hz).2.2.1
      rw [he, sub_self, mul_zero] at hp
      exact (lt_irrefl 0) hp
    have noOuter (he : z ∈ segment ℝ A B ∪ segment ℝ A (foot A) ∪
        segment ℝ B (foot B)) : False := by
      have hf : z ∈ frontier P := by rw [qfront]; exact Or.inl he
      exact hf.2 hz
    obtain ⟨c, hc⟩ := cover z (interior_subset hz)
    refine ⟨c, ?_⟩
    by_contra hn
    have hf : z ∈ frontier (F c) := ⟨subset_closure hc, hn⟩
    rcases classes c with rfl | rfl | rfl
    · rw [tfront] at hf
      rcases hf with (hf | hf) | hf
      · exact noA hf
      · exact noB hf
      · exact noOuter (Or.inl (Or.inl hf))
    · rw [ufront] at hf
      rcases hf with ((hf | hf) | hf) | hf
      · exact noB hf
      · exact noFoot hf
      · exact noOuter (Or.inr hf)
      · exact noLine (footLine x B hf)
    · rw [dfront] at hf
      rcases hf with ((hf | hf) | hf) | hf
      · exact noA (by rwa [segment_symm] at hf)
      · exact noOuter (Or.inl (Or.inr hf))
      · exact noFoot hf
      · exact noLine (footLine A x hf)

end ApollonianSuperharmonic

end
