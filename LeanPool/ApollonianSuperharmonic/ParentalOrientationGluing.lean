/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.AcyclicIndegreeOrientation

-- [TABLET NODE: ParentalOrientationGluing]

/-!
# ParentalOrientationGluing

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace ParentalOrientationLemmas

private theorem incoming_one :
    ∀ (D₁ : Finset GaussianInt), ∀ (D₂ : Finset GaussianInt), ∀ (σ : GaussianInt → ℤ), ∀ (o₁ :
        AcyclicIndegreeOrientation D₁ σ), (∀ x ∈ D₁ ∩ D₂, ∀ y ∈ D₁, o₁.edge y x → y ∈ D₂) →
    let I := D₁ ∩ D₂
    ∀ x ∈ I,
      (D₁.filter (fun y => @decide (o₁.edge y x) (o₁.edgeDecidable y x))) =
        (I.filter (fun y => @decide (o₁.edge y x) (o₁.edgeDecidable y x))) := by
  classical
  intro D₁ D₂ σ o₁ hclosed₁ I x hx
  change x ∈ D₁ ∩ D₂ at hx
  ext y
  simp only [Finset.mem_filter]
  constructor
  · intro h
    refine ⟨Finset.mem_inter.mpr ⟨h.1, ?_⟩, h.2⟩
    exact hclosed₁ x hx y
      h.1
      (@of_decide_eq_true (o₁.edge y x) (o₁.edgeDecidable y x) h.2)
  · intro h
    exact ⟨(Finset.mem_inter.mp (show y ∈ D₁ ∩ D₂ from h.1)).1, h.2⟩

private theorem incoming_two :
    ∀ (D₁ : Finset GaussianInt), ∀ (D₂ : Finset GaussianInt), ∀ (σ : GaussianInt → ℤ), ∀ (o₂ :
        AcyclicIndegreeOrientation D₂ σ), (∀ x ∈ D₁ ∩ D₂, ∀ y ∈ D₂, o₂.edge y x → y ∈ D₁) →
    let I := D₁ ∩ D₂
    ∀ x ∈ I,
      (D₂.filter (fun y => @decide (o₂.edge y x) (o₂.edgeDecidable y x))) =
        (I.filter (fun y => @decide (o₂.edge y x) (o₂.edgeDecidable y x))) := by
  classical
  intro D₁ D₂ σ o₂ hclosed₂ I x hx
  change x ∈ D₁ ∩ D₂ at hx
  ext y
  simp only [Finset.mem_filter]
  constructor
  · intro h
    refine ⟨Finset.mem_inter.mpr ⟨?_, h.1⟩, h.2⟩
    exact hclosed₂ x hx y
      h.1
      (@of_decide_eq_true (o₂.edge y x) (o₂.edgeDecidable y x) h.2)
  · intro h
    exact ⟨(Finset.mem_inter.mp (show y ∈ D₁ ∩ D₂ from h.1)).2, h.2⟩

private theorem incoming_card :
    ∀ (D₁ : Finset GaussianInt), ∀ (D₂ : Finset GaussianInt), ∀ (σ : GaussianInt → ℤ), ∀ (o₁ :
        AcyclicIndegreeOrientation D₁ σ), ∀ (o₂ : AcyclicIndegreeOrientation D₂ σ),
    let I := D₁ ∩ D₂
    (∀ x ∈ I, (D₁.filter (fun y => @decide (o₁.edge y x) (o₁.edgeDecidable y x))) = (I.filter
        (fun y => @decide (o₁.edge y x) (o₁.edgeDecidable y x)))) → (∀ x ∈ I, (D₂.filter (fun y
        => @decide (o₂.edge y x) (o₂.edgeDecidable y x))) = (I.filter (fun y => @decide (o₂.edge
        y x) (o₂.edgeDecidable y x)))) → ∀ x ∈ I,
      (I.filter (fun y => @decide (o₁.edge y x) (o₁.edgeDecidable y x))).card =
        (I.filter (fun y => @decide (o₂.edge y x) (o₂.edgeDecidable y x))).card := by
  classical
  intro D₁ D₂ σ o₁ o₂ I incoming_one incoming_two x hx
  change x ∈ D₁ ∩ D₂ at hx
  have hx' := Finset.mem_inter.mp (show x ∈ D₁ ∩ D₂ from hx)
  have h₁ := o₁.indegree x hx'.1
  have h₂ := o₂.indegree x hx'.2
  rw [incoming_one x hx] at h₁
  rw [incoming_two x hx] at h₂
  exact_mod_cast h₁.trans h₂.symm

private theorem agreement :
    ∀ (D₁ : Finset GaussianInt), ∀ (D₂ : Finset GaussianInt), ∀ (σ : GaussianInt → ℤ), ∀ (o₁ :
        AcyclicIndegreeOrientation D₁ σ), ∀ (o₂ : AcyclicIndegreeOrientation D₂ σ),
    let I := D₁ ∩ D₂
    (∀ x ∈ I, (I.filter (fun y => @decide (o₁.edge y x) (o₁.edgeDecidable y x))).card =
        (I.filter (fun y => @decide (o₂.edge y x) (o₂.edgeDecidable y x))).card) →
    ∀ x ∈ I, ∀ y ∈ I, o₁.edge x y ↔ o₂.edge x y := by
  classical
  intro D₁ D₂ σ o₁ o₂ I incoming_card
  let B := I.filter (fun x => ∃ y ∈ I, o₁.edge x y ≠ o₂.edge x y)
  intro x hx y hy
  by_contra hxy
  have hb : x ∈ B := by
    simp only [B, Finset.mem_filter]
    exact ⟨hx, y, hy, by
      by_cases a : o₁.edge x y <;> by_cases b : o₂.edge x y <;> simp_all⟩
  obtain ⟨z, hz, hmin⟩ := Finset.exists_min_image B o₁.rank
    (by exact ⟨x, hb⟩)
  have hin : ∀ w ∈ I, o₁.edge w z → o₂.edge w z := by
    intro w hw hwz
    by_contra hn
    have hwb : w ∈ B := by
      simp only [B, Finset.mem_filter]
      exact ⟨hw, ⟨z, (Finset.mem_filter.mp hz).1, by
        intro he
        exact hn (he ▸ hwz)⟩⟩
    exact (Nat.not_lt_of_ge (hmin w hwb)) (o₁.increasing w z hwz)
  have hsub : I.filter (fun w => @decide (o₁.edge w z) (o₁.edgeDecidable w z)) ⊆
      I.filter (fun w => @decide (o₂.edge w z) (o₂.edgeDecidable w z)) := by
    intro w hw
    have hwI := (Finset.mem_filter.mp hw).1
    have he := (Finset.mem_filter.mp hw).2
    have he' : o₁.edge w z := @of_decide_eq_true (o₁.edge w z)
      (o₁.edgeDecidable w z) he
    have ho := hin w hwI he'
    have hot : @decide (o₂.edge w z) (o₂.edgeDecidable w z) = true := by
      exact (show @decide (o₂.edge w z) (o₂.edgeDecidable w z) = true from
        (@decide_eq_true_eq (o₂.edge w z) (o₂.edgeDecidable w z)).mpr ho)
    exact Finset.mem_filter.mpr ⟨hwI, hot⟩
  have heq := Finset.eq_of_subset_of_card_le hsub
    (by rw [incoming_card z (Finset.mem_filter.mp hz).1])
  have hback : ∀ w ∈ I, o₂.edge w z → o₁.edge w z := by
    intro w hw hwz
    have hm : w ∈ I.filter (fun q => @decide (o₂.edge q z) (o₂.edgeDecidable q z)) :=
      Finset.mem_filter.mpr ⟨hw, by simp [hwz]⟩
    have hm' := heq ▸ hm
    exact @of_decide_eq_true (o₁.edge w z) (o₁.edgeDecidable w z)
      (Finset.mem_filter.mp hm').2
  have hzall : ∀ w ∈ I, o₁.edge w z ↔ o₂.edge w z := by
    intro w hw
    exact ⟨hin w hw, hback w hw⟩
  have hznot : z ∉ B := by
    intro hzb
    rcases (Finset.mem_filter.mp hzb) with ⟨hzI, w, hwI, hdiff⟩
    by_cases hadj : FourNeighborAdjacent z w
    · rcases o₁.oriented z (Finset.mem_inter.mp (show z ∈ D₁ ∩ D₂ from hzI)).1
        w (Finset.mem_inter.mp (show w ∈ D₁ ∩ D₂ from hwI)).1 hadj with h | h
      · have hzout : ¬ o₁.edge w z := h.2
        rcases o₂.oriented z (Finset.mem_inter.mp (show z ∈ D₁ ∩ D₂ from hzI)).2
          w (Finset.mem_inter.mp (show w ∈ D₁ ∩ D₂ from hwI)).2 hadj with k | k
        · exact hdiff (propext ⟨fun q => k.1, fun q => h.1⟩)
        · exact hzout ((hzall w hwI).2 k.1)
      · have hzout : ¬ o₁.edge z w := h.2
        rcases o₂.oriented z (Finset.mem_inter.mp (show z ∈ D₁ ∩ D₂ from hzI)).2
          w (Finset.mem_inter.mp (show w ∈ D₁ ∩ D₂ from hwI)).2 hadj with k | k
        · exact k.2 ((hzall w hwI).1 h.1)
        · exact hdiff (propext ⟨False.elim ∘ hzout, False.elim ∘ k.2⟩)
    · have h₁ : ¬ o₁.edge z w := by
        intro q
        exact hadj (o₁.supported z w q).2.2
      have h₂ : ¬ o₂.edge z w := by
        intro q
        exact hadj (o₂.supported z w q).2.2
      exact hdiff (propext (by simp [h₁, h₂]))
  exact hznot hz

private theorem edge_one :
    ∀ (D₁ : Finset GaussianInt), ∀ (D₂ : Finset GaussianInt), ∀ (σ : GaussianInt → ℤ), ∀ (o₁ :
        AcyclicIndegreeOrientation D₁ σ), ∀ (o₂ : AcyclicIndegreeOrientation D₂ σ),
    let edge : GaussianInt → GaussianInt → Prop := fun x y =>
      if x ∈ D₁ ∧ y ∈ D₁ then o₁.edge x y
      else if x ∈ D₂ ∧ y ∈ D₂ then o₂.edge x y else False
    ∀ x ∈ D₁, ∀ y ∈ D₁, edge x y ↔ o₁.edge x y := by
  classical
  intro D₁ D₂ σ o₁ o₂ edge x hx y hy
  simp [edge, hx, hy]

private theorem edge_two :
    ∀ (D₁ : Finset GaussianInt), ∀ (D₂ : Finset GaussianInt), ∀ (σ : GaussianInt → ℤ), ∀ (o₁ :
        AcyclicIndegreeOrientation D₁ σ), ∀ (o₂ : AcyclicIndegreeOrientation D₂ σ),
    let I := D₁ ∩ D₂
    (∀ x ∈ I, ∀ y ∈ I, o₁.edge x y ↔ o₂.edge x y) →
    let edge : GaussianInt → GaussianInt → Prop := fun x y =>
      if x ∈ D₁ ∧ y ∈ D₁ then o₁.edge x y
      else if x ∈ D₂ ∧ y ∈ D₂ then o₂.edge x y else False
    ∀ x ∈ D₂, ∀ y ∈ D₂, edge x y ↔ o₂.edge x y := by
  classical
  intro D₁ D₂ σ o₁ o₂ I agreement edge x hx y hy
  by_cases hxy : x ∈ D₁ ∧ y ∈ D₁
  · have hxi : x ∈ I := Finset.mem_inter.mpr ⟨hxy.1, hx⟩
    have hyi : y ∈ I := Finset.mem_inter.mpr ⟨hxy.2, hy⟩
    simp [edge, hxy, agreement x hxi y hyi]
  · simp [edge, hxy, hx, hy]

private theorem edge_support :
    ∀ (D₁ : Finset GaussianInt), ∀ (D₂ : Finset GaussianInt), ∀ (σ : GaussianInt → ℤ), ∀ (o₁ :
        AcyclicIndegreeOrientation D₁ σ), ∀ (o₂ : AcyclicIndegreeOrientation D₂ σ),
    let U := D₁ ∪ D₂
    let edge : GaussianInt → GaussianInt → Prop := fun x y =>
      if x ∈ D₁ ∧ y ∈ D₁ then o₁.edge x y
      else if x ∈ D₂ ∧ y ∈ D₂ then o₂.edge x y else False
    ∀ x y, edge x y → x ∈ U ∧ y ∈ U ∧ FourNeighborAdjacent x y := by
  classical
  intro D₁ D₂ σ o₁ o₂ U edge x y h
  by_cases h1 : x ∈ D₁ ∧ y ∈ D₁
  · have he : o₁.edge x y := by simpa [edge, h1] using h
    exact ⟨Finset.mem_union.mpr (Or.inl h1.1),
      Finset.mem_union.mpr (Or.inl h1.2), (o₁.supported x y he).2.2⟩
  · by_cases h2 : x ∈ D₂ ∧ y ∈ D₂
    · have he : o₂.edge x y := by simpa [edge, h1, h2] using h
      exact ⟨Finset.mem_union.mpr (Or.inr h2.1),
        Finset.mem_union.mpr (Or.inr h2.2), (o₂.supported x y he).2.2⟩
    · simp [edge, h1, h2] at h

private theorem edge_oriented :
    ∀ (D₁ : Finset GaussianInt), ∀ (D₂ : Finset GaussianInt), ∀ (σ : GaussianInt → ℤ), ∀ (o₁ :
        AcyclicIndegreeOrientation D₁ σ), ∀ (o₂ : AcyclicIndegreeOrientation D₂ σ), (∀ x ∈ D₁, x
        ∉ D₂ → ∀ y ∈ D₂, y ∉ D₁ → ¬ FourNeighborAdjacent x y) →
    let U := D₁ ∪ D₂
    let edge : GaussianInt → GaussianInt → Prop := fun x y =>
      if x ∈ D₁ ∧ y ∈ D₁ then o₁.edge x y
      else if x ∈ D₂ ∧ y ∈ D₂ then o₂.edge x y else False
    ∀ x ∈ U, ∀ y ∈ U, FourNeighborAdjacent x y →
      (edge x y ∧ ¬ edge y x) ∨ (edge y x ∧ ¬ edge x y) := by
  classical
  intro D₁ D₂ σ o₁ o₂ hcross U edge x hx y hy hxy
  rcases Finset.mem_union.mp hx with hx1 | hx2
  · rcases Finset.mem_union.mp hy with hy1 | hy2
    · rcases o₁.oriented x hx1 y hy1 hxy with h | h
      · simpa [edge, hx1, hy1] using (Or.inl h)
      · simpa [edge, hx1, hy1] using (Or.inr h)
    · by_cases hx2' : x ∈ D₂
      · by_cases hy1 : y ∈ D₁
        · rcases o₁.oriented x hx1 y hy1 hxy with h | h
          · simpa [edge, hx1, hy1] using (Or.inl h)
          · simpa [edge, hx1, hy1] using (Or.inr h)
        · rcases o₂.oriented x hx2' y hy2 hxy with h | h
          · simpa [edge, hx1, hy1, hy2, hx2'] using (Or.inl h)
          · simpa [edge, hx1, hy1, hy2, hx2'] using (Or.inr h)
      · by_cases hy1 : y ∈ D₁
        · rcases o₁.oriented x hx1 y hy1 hxy with h | h
          · simpa [edge, hx1, hy1] using (Or.inl h)
          · simpa [edge, hx1, hy1] using (Or.inr h)
        · exfalso
          exact hcross x hx1 hx2' y hy2 hy1 hxy
  · rcases Finset.mem_union.mp hy with hy1 | hy2
    · by_cases hy2' : y ∈ D₂
      · by_cases hx1 : x ∈ D₁
        · rcases o₁.oriented x hx1 y hy1 hxy with h | h
          · simpa [edge, hx1, hy1] using (Or.inl h)
          · simpa [edge, hx1, hy1] using (Or.inr h)
        · rcases o₂.oriented x hx2 y hy2' hxy with h | h
          · simpa [edge, hx1, hy1, hx2, hy2'] using (Or.inl h)
          · simpa [edge, hx1, hy1, hx2, hy2'] using (Or.inr h)
      · by_cases hx1 : x ∈ D₁
        · rcases o₁.oriented x hx1 y hy1 hxy with h | h
          · simpa [edge, hx1, hy1] using (Or.inl h)
          · simpa [edge, hx1, hy1] using (Or.inr h)
        · exfalso
          have hsymm : FourNeighborAdjacent y x := by
            rcases hxy with h | h | h | h <;> subst y <;>
              simp [FourNeighborAdjacent]
          exact hcross y hy1 hy2' x hx2 hx1 hsymm
    · by_cases hboth : x ∈ D₁ ∧ y ∈ D₁
      · rcases o₁.oriented x hboth.1 y hboth.2 hxy with h | h
        · simpa [edge, hboth] using (Or.inl h)
        · simpa [edge, hboth] using (Or.inr h)
      · rcases o₂.oriented x hx2 y hy2 hxy with h | h
        · have hboth' : ¬(y ∈ D₁ ∧ x ∈ D₁) := by
            intro q; exact hboth ⟨q.2, q.1⟩
          simpa [edge, hboth, hboth', hx2, hy2] using (Or.inl h)
        · have hboth' : ¬(y ∈ D₁ ∧ x ∈ D₁) := by
            intro q; exact hboth ⟨q.2, q.1⟩
          simpa [edge, hboth, hboth', hx2, hy2] using (Or.inr h)

private theorem rank_one_bound :
    ∀ (D₁ : Finset GaussianInt), ∀ (σ : GaussianInt → ℤ), ∀ (o₁ : AcyclicIndegreeOrientation D₁
        σ), ∀ x ∈ D₁, o₁.rank x ≤ D₁.sup o₁.rank := by
  classical
  intro D₁ σ o₁ x hx
  exact Finset.le_sup hx

private theorem rank_two_bound :
    ∀ (D₂ : Finset GaussianInt), ∀ (σ : GaussianInt → ℤ), ∀ (o₂ : AcyclicIndegreeOrientation D₂
        σ), ∀ x ∈ D₂, o₂.rank x ≤ D₂.sup o₂.rank := by
  classical
  intro D₂ σ o₂ x hx
  exact Finset.le_sup hx

private theorem rank_increasing :
    ∀ (D₁ : Finset GaussianInt), ∀ (D₂ : Finset GaussianInt), ∀ (σ : GaussianInt → ℤ), ∀ (o₁ :
        AcyclicIndegreeOrientation D₁ σ), ∀ (o₂ : AcyclicIndegreeOrientation D₂ σ), (∀ x ∈ D₁ ∩
        D₂, ∀ y ∈ D₁, o₁.edge y x → y ∈ D₂) → (∀ x ∈ D₁ ∩ D₂, ∀ y ∈ D₂, o₂.edge y x → y ∈ D₁) →
    let I := D₁ ∩ D₂
    (∀ x ∈ I, ∀ y ∈ I, o₁.edge x y ↔ o₂.edge x y) →
    let edge : GaussianInt → GaussianInt → Prop := fun x y =>
      if x ∈ D₁ ∧ y ∈ D₁ then o₁.edge x y
      else if x ∈ D₂ ∧ y ∈ D₂ then o₂.edge x y else False
    let M : ℕ := D₁.sup o₁.rank + D₂.sup o₂.rank + 1
    let rank : GaussianInt → ℕ := fun x =>
      if x ∈ I then o₁.rank x else
      if x ∈ D₁ then o₁.rank x + M else o₂.rank x + M
    (∀ x ∈ D₁, o₁.rank x ≤ D₁.sup o₁.rank) → ∀ x y, edge x y → rank x < rank y := by
  classical
  intro D₁ D₂ σ o₁ o₂ hclosed₁ hclosed₂ I agreement edge M rank rank_one_bound x y hxy
  by_cases h1 : x ∈ D₁ ∧ y ∈ D₁
  · have he := (by simpa [edge, h1] using hxy : o₁.edge x y)
    have hxI : x ∈ I ↔ x ∈ D₂ := by simp [I, h1.1]
    have hyI : y ∈ I ↔ y ∈ D₂ := by simp [I, h1.2]
    by_cases hx' : x ∈ I
    · by_cases hy' : y ∈ I
      · simp only [hx', ↓reduceIte, hy', gt_iff_lt, rank]
        exact o₁.increasing x y he
      · simp [rank, hx', hy', h1.2]
        have hm : 0 < M := by simp [M]
        have hr := rank_one_bound y h1.2
        have hp := rank_one_bound x h1.1
        simp [M] at *
        omega
    · by_cases hy' : y ∈ I
      · have hbad : x ∈ D₂ := hclosed₁ y hy' x h1.1 he
        exact (hx' (Finset.mem_inter.mpr ⟨h1.1, hbad⟩)).elim
      · simp only [hx', ↓reduceIte, h1.1, hy', h1.2, add_lt_add_iff_right, gt_iff_lt, rank]
        exact o₁.increasing x y he
  · by_cases h2 : x ∈ D₂ ∧ y ∈ D₂
    · have he := (by simpa [edge, h1, h2] using hxy : o₂.edge x y)
      by_cases hx' : x ∈ I
      · by_cases hy' : y ∈ I
        · simp only [hx', ↓reduceIte, hy', gt_iff_lt, rank]
          exact o₁.increasing x y ((agreement x hx' y hy').2 he)
        · simp only [hx', ↓reduceIte, hy', gt_iff_lt, rank]
          by_cases hyD1 : y ∈ D₁
          · simp [hyD1]
            have hp := rank_one_bound x (Finset.mem_inter.mp (show x ∈ D₁ ∩ D₂ from hx')).1
            have hm : 0 < M := by simp [M]
            simp [M] at *
            omega
          · simp only [hyD1, ↓reduceIte]
            have hp := rank_one_bound x (Finset.mem_inter.mp (show x ∈ D₁ ∩ D₂ from hx')).1
            have hm : 0 < M := by simp [M]
            simp [M] at *
            omega
      · by_cases hy' : y ∈ I
        · have hbad : x ∈ D₁ := hclosed₂ y hy' x h2.1 he
          exact (hx' (Finset.mem_inter.mpr ⟨hbad, h2.1⟩)).elim
        · have hyD1 : ¬ y ∈ D₁ := by
            intro q; exact hy' (Finset.mem_inter.mpr ⟨q, h2.2⟩)
          have hxD1 : ¬ x ∈ D₁ := by
            intro q; exact hx' (Finset.mem_inter.mpr ⟨q, h2.1⟩)
          simp only [hx', ↓reduceIte, hxD1, hy', hyD1, add_lt_add_iff_right, gt_iff_lt, rank]
          exact o₂.increasing x y he
    · simp [edge, h1, h2] at hxy

end ParentalOrientationLemmas

theorem ParentalOrientationGluing
    (D₁ D₂ : Finset GaussianInt) (σ : GaussianInt → ℤ)
    (o₁ : AcyclicIndegreeOrientation D₁ σ)
    (o₂ : AcyclicIndegreeOrientation D₂ σ)
    (hcross : ∀ x ∈ D₁, x ∉ D₂ → ∀ y ∈ D₂, y ∉ D₁ →
      ¬ FourNeighborAdjacent x y)
    (hclosed₁ : ∀ x ∈ D₁ ∩ D₂, ∀ y ∈ D₁,
      o₁.edge y x → y ∈ D₂)
    (hclosed₂ : ∀ x ∈ D₁ ∩ D₂, ∀ y ∈ D₂,
      o₂.edge y x → y ∈ D₁) :
    ∃ o : AcyclicIndegreeOrientation (D₁ ∪ D₂) σ,
      (∀ x ∈ D₁, ∀ y ∈ D₁, o.edge x y ↔ o₁.edge x y) ∧
      ∀ x ∈ D₂, ∀ y ∈ D₂, o.edge x y ↔ o₂.edge x y := by
-- BODY
  classical
  let I := D₁ ∩ D₂
  let U := D₁ ∪ D₂
  have incoming_one : ∀ x ∈ I,
      (D₁.filter (fun y => @decide (o₁.edge y x) (o₁.edgeDecidable y x))) =
        (I.filter (fun y => @decide (o₁.edge y x) (o₁.edgeDecidable y x))) :=
            ParentalOrientationLemmas.incoming_one D₁ D₂ σ o₁ hclosed₁
  have incoming_two : ∀ x ∈ I,
      (D₂.filter (fun y => @decide (o₂.edge y x) (o₂.edgeDecidable y x))) =
        (I.filter (fun y => @decide (o₂.edge y x) (o₂.edgeDecidable y x))) :=
            ParentalOrientationLemmas.incoming_two D₁ D₂ σ o₂ hclosed₂
  have incoming_card : ∀ x ∈ I,
      (I.filter (fun y => @decide (o₁.edge y x) (o₁.edgeDecidable y x))).card =
        (I.filter (fun y => @decide (o₂.edge y x) (o₂.edgeDecidable y x))).card :=
            ParentalOrientationLemmas.incoming_card D₁ D₂ σ o₁ o₂ incoming_one incoming_two
  let B := I.filter (fun x => ∃ y ∈ I, o₁.edge x y ≠ o₂.edge x y)
  have agreement : ∀ x ∈ I, ∀ y ∈ I, o₁.edge x y ↔ o₂.edge x y :=
      ParentalOrientationLemmas.agreement D₁ D₂ σ o₁ o₂ incoming_card
  let edge : GaussianInt → GaussianInt → Prop := fun x y =>
    if x ∈ D₁ ∧ y ∈ D₁ then o₁.edge x y
    else if x ∈ D₂ ∧ y ∈ D₂ then o₂.edge x y else False
  let M : ℕ := D₁.sup o₁.rank + D₂.sup o₂.rank + 1
  let rank : GaussianInt → ℕ := fun x =>
    if x ∈ I then o₁.rank x else
    if x ∈ D₁ then o₁.rank x + M else o₂.rank x + M
  have edge_one : ∀ x ∈ D₁, ∀ y ∈ D₁, edge x y ↔ o₁.edge x y :=
      ParentalOrientationLemmas.edge_one D₁ D₂ σ o₁ o₂
  have edge_two : ∀ x ∈ D₂, ∀ y ∈ D₂, edge x y ↔ o₂.edge x y :=
      ParentalOrientationLemmas.edge_two D₁ D₂ σ o₁ o₂ agreement
  have edge_support : ∀ x y, edge x y → x ∈ U ∧ y ∈ U ∧ FourNeighborAdjacent x y :=
      ParentalOrientationLemmas.edge_support D₁ D₂ σ o₁ o₂
  have edge_oriented : ∀ x ∈ U, ∀ y ∈ U, FourNeighborAdjacent x y →
      (edge x y ∧ ¬ edge y x) ∨ (edge y x ∧ ¬ edge x y) :=
          ParentalOrientationLemmas.edge_oriented D₁ D₂ σ o₁ o₂ hcross
  have rank_one_bound : ∀ x ∈ D₁, o₁.rank x ≤ D₁.sup o₁.rank :=
      ParentalOrientationLemmas.rank_one_bound D₁ σ o₁
  have rank_two_bound : ∀ x ∈ D₂, o₂.rank x ≤ D₂.sup o₂.rank :=
      ParentalOrientationLemmas.rank_two_bound D₂ σ o₂
  have rank_increasing : ∀ x y, edge x y → rank x < rank y :=
      ParentalOrientationLemmas.rank_increasing D₁ D₂ σ o₁ o₂ hclosed₁ hclosed₂ agreement
      rank_one_bound
  let o : AcyclicIndegreeOrientation U σ :=
    { edge := edge
      edgeDecidable := fun x y => Classical.propDecidable _
      rank := rank
      supported := edge_support
      oriented := edge_oriented
      increasing := rank_increasing
      indegree := by
        intro x hx
        by_cases hx1 : x ∈ D₁
        · have hi := o₁.indegree x hx1
          have hf : U.filter (fun y => @decide (edge y x) (Classical.propDecidable _)) =
              D₁.filter (fun y => @decide (o₁.edge y x) (o₁.edgeDecidable y x)) := by
            ext y
            simp only [Finset.mem_filter]
            constructor
            · intro h
              rcases Finset.mem_union.mp h.1 with hy1 | hy2
              · exact ⟨hy1, by simpa [edge, hx1, hy1] using h.2⟩
              · by_cases hy1' : y ∈ D₁
                · exact ⟨hy1', by simpa [edge, hx1, hy1'] using h.2⟩
                · by_cases hx2 : x ∈ D₂
                  · exfalso
                    have q : o₂.edge y x := by
                      simpa [edge, hx1, hy1', hy2, hx2] using h.2
                    exact hy1' (hclosed₂ x (Finset.mem_inter.mpr ⟨hx1, hx2⟩) y hy2 q)
                  · exfalso
                    simpa [edge, hx1, hy1', hy2, hx2] using h.2
            · intro h
              exact ⟨Finset.mem_union.mpr (Or.inl h.1), by
                simpa [edge, hx1, h.1] using h.2⟩
          rw [hf]
          exact hi
        · have hx2 : x ∈ D₂ := Finset.mem_union.mp hx |>.resolve_left hx1
          have hi := o₂.indegree x hx2
          have hf : U.filter (fun y => @decide (edge y x) (Classical.propDecidable _)) =
              D₂.filter (fun y => @decide (o₂.edge y x) (o₂.edgeDecidable y x)) := by
            ext y
            simp only [Finset.mem_filter]
            constructor
            · intro h
              rcases Finset.mem_union.mp h.1 with hy1 | hy2
              · by_cases hy2' : y ∈ D₂
                · exact ⟨hy2', by simpa [edge, hx1, hy2', hx2] using h.2⟩
                · exact (hy2' (o₂.supported y x (by simpa [edge, hx1, hy1, hy2'] using h.2)).1).elim
              · exact ⟨hy2, by simpa [edge, hx1, hy2, hx2] using h.2⟩
            · intro h
              exact ⟨Finset.mem_union.mpr (Or.inr h.1), by
                simpa [edge, hx1, h.1, hx2] using h.2⟩
          rw [hf]
          exact hi }
  refine ⟨o, ?_, ?_⟩
  · intro x hx y hy
    exact edge_one x hx y hy
  · intro x hx y hy
    exact edge_two x hx y hy

end ApollonianSuperharmonic

end
