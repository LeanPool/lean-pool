/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.CutChain

/-!
# Lifting arcs to the cut surface

Let `ψ` be a map that has two preimages over each point of an arc. If the arc is a chain of edges,
the two lifts of the
edges fit together to two disjoint lifts of the arc (`LiftPair.join`). For an `O`-arc, we close the
chain
(`LiftPair.close`): either we get two `O`-arcs over `F`, or one `O`-arc that runs twice around `F`.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric

universe u

local notation "𝕀" => unitInterval

variable {S S' : Type u} [TopologicalSpace S] [TopologicalSpace S'] [T2Space S'] {ψ : S' → S}

/-- Two disjoint lifts `X`, `Y` of the line `Z` from `u` to `v`, that fill the preimage of `Z`. -/
def LiftPair (ψ : S' → S) (Z : Set S) (u v : S) (X Y : Set S') : Prop :=
  ∃ x0 x1 y0 y1, IsLineWithEnds X x0 x1 ∧ IsLineWithEnds Y y0 y1 ∧ Disjoint X Y ∧ X ∪ Y = ψ ⁻¹' Z
    ∧ BijOn ψ X Z ∧
    BijOn ψ Y Z ∧ ψ x0 = u ∧ ψ y0 = u ∧ ψ x1 = v ∧ ψ y1 = v

omit [TopologicalSpace S] [T2Space S'] in
theorem LiftPair.symm {Z : Set S} {u v : S} {X Y : Set S'} (h : LiftPair ψ Z u v X Y) : LiftPair ψ
  Z u v Y X := by
  obtain ⟨x0, x1, y0, y1, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  exact ⟨y0, y1, x0, x1, h2, h1, h3.symm, by rw [union_comm, h4], h6, h5, h8, h7, h10, h9⟩

theorem eq_or_of_encard_le_two {α : Type*} {T : Set α} (hT : T.encard ≤ 2) {a b c : α} (ha : a ∈ T)
  (hb : b ∈ T) (hc : c ∈ T)
    (hab : a ≠ b) : c = a ∨ c = b := by
  by_contra hcon
  push Not at hcon
  have h1 : ({a, b, c} : Set α) ⊆ T := by
    rintro x (rfl | rfl | rfl) <;> assumption
  have h2 : ({a, b, c} : Set α).encard = 3 := Set.encard_eq_three.mpr ⟨a, b, c, hab, hcon.1.symm,
    hcon.2.symm, rfl⟩
  have h3 := encard_le_encard h1
  rw [h2] at h3
  exact absurd (h3.trans hT) (by norm_num)

omit [TopologicalSpace S] in
theorem LiftPair.join_aux {Z₁ Z₂ : Set S} {u c v : S} {X₁ Y₁ X₂ Y₂ : Set S'} {x0 x1 y0 y1 y₂ y₂' :
  S'}
    (h1 : IsLineWithEnds X₁ x0 x1) (h2 : IsLineWithEnds Y₁ y0 y1) (h3 : Disjoint X₁ Y₁)
      (h4 : X₁ ∪ Y₁ = ψ ⁻¹' Z₁)
    (h5 : BijOn ψ X₁ Z₁) (h6 : BijOn ψ Y₁ Z₁) (h7 : ψ x0 = u) (h8 : ψ y0 = u) (h9 : ψ x1 = c)
      (h10 : ψ y1 = c)
    (h1' : IsLineWithEnds X₂ x1 y₂) (h2' : IsLineWithEnds Y₂ y1 y₂') (h3' : Disjoint X₂ Y₂)
      (h4' : X₂ ∪ Y₂ = ψ ⁻¹' Z₂)
    (h5' : BijOn ψ X₂ Z₂) (h6' : BijOn ψ Y₂ Z₂) (h9' : ψ y₂ = v) (h10' : ψ y₂' = v) (hi : Z₁ ∩ Z₂
      = {c}) :
    LiftPair ψ (Z₁ ∪ Z₂) u v (X₁ ∪ X₂) (Y₁ ∪ Y₂) := by
  have hX : X₁ ∩ X₂ = {x1} := by
    ext z
    constructor
    · rintro ⟨hz, hz'⟩
      have h11 : ψ z ∈ Z₁ ∩ Z₂ := ⟨h5.mapsTo hz, h5'.mapsTo hz'⟩
      rw [hi] at h11
      exact h5.injOn hz h1.right_mem (h11.trans h9.symm)
    · rintro rfl
      exact ⟨h1.right_mem, h1'.left_mem⟩
  have hY : Y₁ ∩ Y₂ = {y1} := by
    ext z
    constructor
    · rintro ⟨hz, hz'⟩
      have h11 : ψ z ∈ Z₁ ∩ Z₂ := ⟨h6.mapsTo hz, h6'.mapsTo hz'⟩
      rw [hi] at h11
      exact h6.injOn hz h2.right_mem (h11.trans h10.symm)
    · rintro rfl
      exact ⟨h2.right_mem, h2'.left_mem⟩
  have hc1 : ∀ z ∈ X₁, z ∈ Y₂ → False := fun z hz hz' => by
    have h11 : ψ z ∈ Z₁ ∩ Z₂ := ⟨h5.mapsTo hz, h6'.mapsTo hz'⟩
    rw [hi] at h11
    have e1 : z = x1 := h5.injOn hz h1.right_mem (h11.trans h9.symm)
    have e2 : z = y1 := h6'.injOn hz' h2'.left_mem (h11.trans h10.symm)
    exact Set.disjoint_left.mp h3 h1.right_mem (show x1 ∈ Y₁ by rw [← e1, e2]; exact h2.right_mem)
  have hc2 : ∀ z ∈ X₂, z ∈ Y₁ → False := fun z hz hz' => by
    have h11 : ψ z ∈ Z₁ ∩ Z₂ := ⟨h6.mapsTo hz', h5'.mapsTo hz⟩
    rw [hi] at h11
    have e1 : z = x1 := h5'.injOn hz h1'.left_mem (h11.trans h9.symm)
    have e2 : z = y1 := h6.injOn hz' h2.right_mem (h11.trans h10.symm)
    exact Set.disjoint_left.mp h3 (show z ∈ X₁ by rw [e1]; exact h1.right_mem) hz'
  refine ⟨x0, y₂, y0, y₂', h1.union h1' hX, h2.union h2' hY, ?_, ?_, ?_, ?_, h7, h8, h9', h10'⟩
  · rw [Set.disjoint_left]
    rintro z (hz | hz) (hz' | hz')
    · exact Set.disjoint_left.mp h3 hz hz'
    · exact hc1 z hz hz'
    · exact hc2 z hz hz'
    · exact Set.disjoint_left.mp h3' hz hz'
  · rw [preimage_union, ← h4, ← h4']
    ac_rfl
  · refine ⟨fun z hz => hz.imp (fun h => h5.mapsTo h) (fun h => h5'.mapsTo h), ?_, ?_⟩
    · rintro z (hz | hz) z' (hz' | hz') he
      · exact h5.injOn hz hz' he
      · have h11 : ψ z ∈ Z₁ ∩ Z₂ := ⟨h5.mapsTo hz, he ▸ h5'.mapsTo hz'⟩
        rw [hi] at h11
        rw [h5.injOn hz h1.right_mem (h11.trans h9.symm), h5'.injOn hz' h1'.left_mem
          ((he.symm.trans h11).trans h9.symm)]
      · have h11 : ψ z ∈ Z₁ ∩ Z₂ := ⟨he ▸ h5.mapsTo hz', h5'.mapsTo hz⟩
        rw [hi] at h11
        rw [h5'.injOn hz h1'.left_mem (h11.trans h9.symm), h5.injOn hz' h1.right_mem
          ((he.symm.trans h11).trans h9.symm)]
      · exact h5'.injOn hz hz' he
    · rintro z (hz | hz)
      · obtain ⟨w, hw, rfl⟩ := h5.surjOn hz
        exact ⟨w, .inl hw, rfl⟩
      · obtain ⟨w, hw, rfl⟩ := h5'.surjOn hz
        exact ⟨w, .inr hw, rfl⟩
  · refine ⟨fun z hz => hz.imp (fun h => h6.mapsTo h) (fun h => h6'.mapsTo h), ?_, ?_⟩
    · rintro z (hz | hz) z' (hz' | hz') he
      · exact h6.injOn hz hz' he
      · have h11 : ψ z ∈ Z₁ ∩ Z₂ := ⟨h6.mapsTo hz, he ▸ h6'.mapsTo hz'⟩
        rw [hi] at h11
        rw [h6.injOn hz h2.right_mem (h11.trans h10.symm), h6'.injOn hz' h2'.left_mem
          ((he.symm.trans h11).trans h10.symm)]
      · have h11 : ψ z ∈ Z₁ ∩ Z₂ := ⟨he ▸ h6.mapsTo hz', h6'.mapsTo hz⟩
        rw [hi] at h11
        rw [h6'.injOn hz h2'.left_mem (h11.trans h10.symm), h6.injOn hz' h2.right_mem
          ((he.symm.trans h11).trans h10.symm)]
      · exact h6'.injOn hz hz' he
    · rintro z (hz | hz)
      · obtain ⟨w, hw, rfl⟩ := h6.surjOn hz
        exact ⟨w, .inl hw, rfl⟩
      · obtain ⟨w, hw, rfl⟩ := h6'.surjOn hz
        exact ⟨w, .inr hw, rfl⟩

omit [TopologicalSpace S] in
/-- Two lifts of two lines that meet in one point, over which there are at most two points, fit
together. -/
theorem LiftPair.join {Z₁ Z₂ : Set S} {u c v : S} {X₁ Y₁ X₂ Y₂ : Set S'}
  (h : LiftPair ψ Z₁ u c X₁ Y₁)
    (h' : LiftPair ψ Z₂ c v X₂ Y₂) (hi : Z₁ ∩ Z₂ = {c}) (hc : (ψ ⁻¹' {c}).encard ≤ 2) :
    ∃ X Y, LiftPair ψ (Z₁ ∪ Z₂) u v X Y := by
  obtain ⟨x0, x1, y0, y1, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  obtain ⟨x0', x1', y0', y1', h1', h2', h3', h4', h5', h6', h7', h8', h9', h10'⟩ := h'
  have hne : x1 ≠ y1 := fun he => Set.disjoint_left.mp h3 h1.right_mem (he ▸ h2.right_mem)
  have hne' : x0' ≠ y0' := fun he => Set.disjoint_left.mp h3' h1'.left_mem (he ▸ h2'.left_mem)
  rcases eq_or_of_encard_le_two hc h9 h10 (c := x0') h7' hne with e | e
  · have e' : y0' = y1 := by
      rcases eq_or_of_encard_le_two hc h9 h10 (c := y0') h8' hne with e' | e'
      · exact absurd (e.trans e'.symm) hne'
      · exact e'
    subst e e'
    exact ⟨_, _, LiftPair.join_aux h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h1' h2' h3' h4' h5' h6' h9' h10'
      hi⟩
  · have e' : y0' = x1 := by
      rcases eq_or_of_encard_le_two hc h9 h10 (c := y0') h8' hne with e' | e'
      · exact e'
      · exact absurd (e.trans e'.symm) hne'
    subst e e'
    exact ⟨_, _, LiftPair.join_aux h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h2' h1' h3'.symm
      (by rw [union_comm, h4']) h6' h5' h10' h9' hi⟩

theorem oArc_of_lines {X : Type*} [TopologicalSpace X] [T2Space X] {A B : Set X} {u v : X}
  (hA : IsLineWithEnds A u v)
    (hB : IsLineWithEnds B u v) (hi : A ∩ B = {u, v}) : IsOArc (A ∪ B) := by
  obtain ⟨a, ha, rfl, rfl, rfl⟩ := hA.exists_arc
  obtain ⟨b, hb, rfl, h0, h1⟩ := hB.exists_arc
  refine oArc_of_two_arcs ha hb h0.symm h1.symm fun s t he => ?_
  have hm : a s ∈ range a ∩ range b := ⟨⟨s, rfl⟩, ⟨t, he.symm⟩⟩
  rw [hi] at hm
  rcases hm with hm | hm
  · left
    have e1 : s = 0 := ha.2 hm
    subst e1
    exact ⟨rfl, hb.2 (he.symm.trans h0.symm)⟩
  · right
    have e1 : s = 1 := ha.2 hm
    subst e1
    exact ⟨rfl, hb.2 (he.symm.trans h1.symm)⟩

theorem IsOArc.lines {X : Type*} [TopologicalSpace X] [T2Space X] {F : Set X}
  (hF : IsOArc F) {x y : X} (hx : x ∈ F) (hy : y ∈ F)
    (hxy : x ≠ y) : ∃ A B, IsLineWithEnds A x y ∧ IsLineWithEnds B x y ∧ A ∪ B = F ∧ A ∩ B = {x, y}
      := by
  obtain ⟨a, b, h1, rfl, rfl, rfl⟩ := hF.exists_arcs hx hy hxy
  refine ⟨range a, range b, h1.arc_left.isLineWithEnds, ?_, rfl, h1.inter⟩
  have := h1.arc_right.isLineWithEnds
  rwa [h1.zero, h1.one] at this

omit [TopologicalSpace S] in
theorem LiftPair.close_aux {Z₁ Z₂ : Set S} {u c : S} {X₁ Y₁ X₂ Y₂ : Set S'} {x0 x1 y0 y1 p q : S'}
    (h1 : IsLineWithEnds X₁ x0 x1) (h2 : IsLineWithEnds Y₁ y0 y1) (h3 : Disjoint X₁ Y₁)
      (h4 : X₁ ∪ Y₁ = ψ ⁻¹' Z₁)
    (h5 : BijOn ψ X₁ Z₁) (h6 : BijOn ψ Y₁ Z₁) (h7 : ψ x0 = u) (h8 : ψ y0 = u) (h9 : ψ x1 = c)
      (h10 : ψ y1 = c)
    (h1' : IsLineWithEnds X₂ x1 p) (h2' : IsLineWithEnds Y₂ y1 q) (h3' : Disjoint X₂ Y₂)
      (h4' : X₂ ∪ Y₂ = ψ ⁻¹' Z₂)
    (h5' : BijOn ψ X₂ Z₂) (h6' : BijOn ψ Y₂ Z₂) (hi : Z₁ ∩ Z₂ = {u, c}) (huc : u ≠ c)
    (hpq : (p = x0 ∧ q = y0) ∨ (p = y0 ∧ q = x0)) :
    (∃ X Y, Disjoint X Y ∧ X ∪ Y = ψ ⁻¹' (Z₁ ∪ Z₂) ∧ IsOArc X ∧ IsOArc Y ∧ BijOn ψ X (Z₁ ∪ Z₂)
      ∧ BijOn ψ Y (Z₁ ∪ Z₂)) ∨
      IsOArc (ψ ⁻¹' (Z₁ ∪ Z₂)) := by
  have hxy0 : x0 ≠ y0 := fun he => Set.disjoint_left.mp h3 h1.left_mem (he ▸ h2.left_mem)
  have hxy1 : x1 ≠ y1 := fun he => Set.disjoint_left.mp h3 h1.right_mem (he ▸ h2.right_mem)
  have hun : ψ ⁻¹' (Z₁ ∪ Z₂) = (X₁ ∪ X₂) ∪ (Y₁ ∪ Y₂) := by
    rw [preimage_union, ← h4, ← h4']
    ac_rfl
  /- The points over `u` and `c` in each of the four arcs. -/
  have hX1 : ∀ z ∈ X₁, ∀ w ∈ X₂ ∪ Y₂, ψ z = ψ w → z = x0 ∨ z = x1 := fun z hz w hw he => by
    have hw' : ψ w ∈ Z₂ := by
      rcases hw with hw | hw
      · exact h5'.mapsTo hw
      · exact h6'.mapsTo hw
    have h11 : ψ z ∈ Z₁ ∩ Z₂ := ⟨h5.mapsTo hz, he ▸ hw'⟩
    rw [hi] at h11
    rcases h11 with h11 | h11
    · exact .inl (h5.injOn hz h1.left_mem (h11.trans h7.symm))
    · exact .inr (h5.injOn hz h1.right_mem (h11.trans h9.symm))
  have hY1 : ∀ z ∈ Y₁, ∀ w ∈ X₂ ∪ Y₂, ψ z = ψ w → z = y0 ∨ z = y1 := fun z hz w hw he => by
    have hw' : ψ w ∈ Z₂ := by
      rcases hw with hw | hw
      · exact h5'.mapsTo hw
      · exact h6'.mapsTo hw
    have h11 : ψ z ∈ Z₁ ∩ Z₂ := ⟨h6.mapsTo hz, he ▸ hw'⟩
    rw [hi] at h11
    rcases h11 with h11 | h11
    · exact .inl (h6.injOn hz h2.left_mem (h11.trans h8.symm))
    · exact .inr (h6.injOn hz h2.right_mem (h11.trans h10.symm))
  have hψp : ψ p = u := by
    rcases hpq with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> assumption
  have hψq : ψ q = u := by
    rcases hpq with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> assumption
  have hX2 : ∀ z ∈ X₂, ∀ w ∈ X₁ ∪ Y₁, ψ z = ψ w → z = p ∨ z = x1 := fun z hz w hw he => by
    have hw' : ψ w ∈ Z₁ := by
      rcases hw with hw | hw
      · exact h5.mapsTo hw
      · exact h6.mapsTo hw
    have h11 : ψ z ∈ Z₁ ∩ Z₂ := ⟨he ▸ hw', h5'.mapsTo hz⟩
    rw [hi] at h11
    rcases h11 with h11 | h11
    · exact .inl (h5'.injOn hz h1'.right_mem (h11.trans hψp.symm))
    · exact .inr (h5'.injOn hz h1'.left_mem (h11.trans h9.symm))
  have hY2 : ∀ z ∈ Y₂, ∀ w ∈ X₁ ∪ Y₁, ψ z = ψ w → z = q ∨ z = y1 := fun z hz w hw he => by
    have hw' : ψ w ∈ Z₁ := by
      rcases hw with hw | hw
      · exact h5.mapsTo hw
      · exact h6.mapsTo hw
    have h11 : ψ z ∈ Z₁ ∩ Z₂ := ⟨he ▸ hw', h6'.mapsTo hz⟩
    rw [hi] at h11
    rcases h11 with h11 | h11
    · exact .inl (h6'.injOn hz h2'.right_mem (h11.trans hψq.symm))
    · exact .inr (h6'.injOn hz h2'.left_mem (h11.trans h10.symm))
  have hx0Y : x0 ∉ Y₁ := fun h => Set.disjoint_left.mp h3 h1.left_mem h
  have hx1Y : x1 ∉ Y₁ := fun h => Set.disjoint_left.mp h3 h1.right_mem h
  have hy0X : y0 ∉ X₁ := fun h => Set.disjoint_left.mp h3 h h2.left_mem
  have hy1X : y1 ∉ X₁ := fun h => Set.disjoint_left.mp h3 h h2.right_mem
  have hx1Y2 : x1 ∉ Y₂ := fun h => by
    rcases hY2 x1 h y1 (.inr h2.right_mem) (h9.trans h10.symm) with e | e
    · exact huc ((hψq.symm.trans (congrArg ψ e.symm)).trans h9)
    · exact hxy1 e
  have hy1X2 : y1 ∉ X₂ := fun h => by
    rcases hX2 y1 h x1 (.inl h1.right_mem) (h10.trans h9.symm) with e | e
    · exact huc ((hψp.symm.trans (congrArg ψ e.symm)).trans h10)
    · exact hxy1 e.symm
  have hbij : ∀ {A B : Set S'}, BijOn ψ A Z₁ → BijOn ψ B Z₂ → (∀ z ∈ A, ∀ w ∈ B, ψ z = ψ w → z = w)
    →
      BijOn ψ (A ∪ B) (Z₁ ∪ Z₂) := by
    intro A B hA hB hAB
    refine ⟨fun z hz => hz.imp (fun h => hA.mapsTo h) (fun h => hB.mapsTo h), ?_, ?_⟩
    · rintro z (hz | hz) z' (hz' | hz') he
      · exact hA.injOn hz hz' he
      · exact hAB z hz z' hz' he
      · exact (hAB z' hz' z hz he.symm).symm
      · exact hB.injOn hz hz' he
    · rintro z (hz | hz)
      · obtain ⟨w, hw, rfl⟩ := hA.surjOn hz
        exact ⟨w, .inl hw, rfl⟩
      · obtain ⟨w, hw, rfl⟩ := hB.surjOn hz
        exact ⟨w, .inr hw, rfl⟩
  rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · left
    have hXi : X₁ ∩ X₂ = {p, x1} := by
      ext z
      constructor
      · rintro ⟨hz, hz'⟩
        exact hX1 z hz z (.inl hz') rfl
      · rintro (rfl | rfl)
        · exact ⟨h1.left_mem, h1'.right_mem⟩
        · exact ⟨h1.right_mem, h1'.left_mem⟩
    have hYi : Y₁ ∩ Y₂ = {q, y1} := by
      ext z
      constructor
      · rintro ⟨hz, hz'⟩
        exact hY1 z hz z (.inr hz') rfl
      · rintro (rfl | rfl)
        · exact ⟨h2.left_mem, h2'.right_mem⟩
        · exact ⟨h2.right_mem, h2'.left_mem⟩
    refine ⟨X₁ ∪ X₂, Y₁ ∪ Y₂, ?_, hun.symm, oArc_of_lines h1 h1'.symm hXi,
      oArc_of_lines h2 h2'.symm hYi, ?_, ?_⟩
    · rw [Set.disjoint_left]
      rintro z (hz | hz) (hz' | hz')
      · exact Set.disjoint_left.mp h3 hz hz'
      · rcases hX1 z hz z (.inr hz') rfl with e | e
        · rcases hY2 z hz' z (.inl hz) rfl with e' | e'
          · exact hxy0 (e.symm.trans e')
          · exact hx0Y (by rw [← e, e']; exact h2.right_mem)
        · exact hx1Y2 (e ▸ hz')
      · rcases hY1 z hz' z (.inl hz) rfl with e | e
        · rcases hX2 z hz z (.inr hz') rfl with e' | e'
          · exact hxy0 (e'.symm.trans e)
          · exact hx1Y (by rw [← e']; exact hz')
        · exact hy1X2 (e ▸ hz)
      · exact Set.disjoint_left.mp h3' hz hz'
    · refine hbij h5 h5' fun z hz w hw he => ?_
      rcases hX1 z hz w (.inl hw) he with e | e <;> rcases hX2 w hw z (.inl hz) he.symm with e' | e'
      · rw [e, e']
      · exact absurd (by rw [← h7, ← h9, ← e, ← e']; exact he) huc
      · exact absurd (by rw [← h7, ← h9, ← e, ← e']; exact he) huc.symm
      · rw [e, e']
    · refine hbij h6 h6' fun z hz w hw he => ?_
      rcases hY1 z hz w (.inr hw) he with e | e <;> rcases hY2 w hw z (.inr hz) he.symm with e' | e'
      · rw [e, e']
      · exact absurd (by rw [← h8, ← h10, ← e, ← e']; exact he) huc
      · exact absurd (by rw [← h8, ← h10, ← e, ← e']; exact he) huc.symm
      · rw [e, e']
  · right
    have hXi : X₁ ∩ X₂ = {x1} := by
      ext z
      constructor
      · rintro ⟨hz, hz'⟩
        rcases hX1 z hz z (.inl hz') rfl with e | e
        · rcases hX2 z hz' z (.inl hz) rfl with e' | e'
          · exact absurd (e.symm.trans e') hxy0
          · exact e'
        · exact e
      · rintro rfl
        exact ⟨h1.right_mem, h1'.left_mem⟩
    have hYi : Y₁ ∩ Y₂ = {y1} := by
      ext z
      constructor
      · rintro ⟨hz, hz'⟩
        rcases hY1 z hz z (.inr hz') rfl with e | e
        · rcases hY2 z hz' z (.inr hz) rfl with e' | e'
          · exact absurd (e'.symm.trans e) hxy0
          · exact e'
        · exact e
      · rintro rfl
        exact ⟨h2.right_mem, h2'.left_mem⟩
    have hL1 := h1.union h1' hXi
    have hL2 := h2.union h2' hYi
    have hLi : (X₁ ∪ X₂) ∩ (Y₁ ∪ Y₂) = {q, p} := by
      ext z
      constructor
      · rintro ⟨hz | hz, hz' | hz'⟩
        · exact absurd hz' (Set.disjoint_left.mp h3 hz)
        · rcases hX1 z hz z (.inr hz') rfl with e | e
          · exact .inl e
          · exact absurd (e ▸ hz') hx1Y2
        · rcases hY1 z hz' z (.inl hz) rfl with e | e
          · exact .inr e
          · exact absurd (e ▸ hz) hy1X2
        · exact absurd hz' (Set.disjoint_left.mp h3' hz)
      · rintro (rfl | rfl)
        · exact ⟨.inl h1.left_mem, .inr h2'.right_mem⟩
        · exact ⟨.inr h1'.right_mem, .inl h2.left_mem⟩
    rw [hun]
    exact oArc_of_lines hL1 hL2.symm hLi

omit [TopologicalSpace S] in
/-- Closing a chain around an `O`-arc. -/
theorem LiftPair.close {Z₁ Z₂ : Set S} {u c : S} {X₁ Y₁ X₂ Y₂ : Set S'}
  (h : LiftPair ψ Z₁ u c X₁ Y₁)
    (h' : LiftPair ψ Z₂ c u X₂ Y₂) (hi : Z₁ ∩ Z₂ = {u, c}) (huc : u ≠ c) (hu : (ψ ⁻¹' {u}).encard
      ≤ 2)
    (hc : (ψ ⁻¹' {c}).encard ≤ 2) :
    (∃ X Y, Disjoint X Y ∧ X ∪ Y = ψ ⁻¹' (Z₁ ∪ Z₂) ∧ IsOArc X ∧ IsOArc Y ∧ BijOn ψ X (Z₁ ∪ Z₂)
      ∧ BijOn ψ Y (Z₁ ∪ Z₂)) ∨
      IsOArc (ψ ⁻¹' (Z₁ ∪ Z₂)) := by
  obtain ⟨x0, x1, y0, y1, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  obtain ⟨x0', x1', y0', y1', h1', h2', h3', h4', h5', h6', h7', h8', h9', h10'⟩ := h'
  have hne : x1 ≠ y1 := fun he => Set.disjoint_left.mp h3 h1.right_mem (he ▸ h2.right_mem)
  have hne0 : x0 ≠ y0 := fun he => Set.disjoint_left.mp h3 h1.left_mem (he ▸ h2.left_mem)
  have hne' : x0' ≠ y0' := fun he => Set.disjoint_left.mp h3' h1'.left_mem (he ▸ h2'.left_mem)
  have hne1' : x1' ≠ y1' := fun he => Set.disjoint_left.mp h3' h1'.right_mem (he ▸ h2'.right_mem)
  have hu' : ∀ w, ψ w = u → ∀ w', ψ w' = u → w ≠ w' → (x1' = x0 ∧ y1' = y0) ∨ (x1' = y0 ∧ y1' = x0)
    := by
    intro _ _ _ _ _
    rcases eq_or_of_encard_le_two hu h7 h8 (c := x1') h9' hne0 with e | e <;>
      rcases eq_or_of_encard_le_two hu h7 h8 (c := y1') h10' hne0 with e' | e'
    · exact absurd (e.trans e'.symm) hne1'
    · exact .inl ⟨e, e'⟩
    · exact .inr ⟨e, e'⟩
    · exact absurd (e.trans e'.symm) hne1'
  have hpq := hu' _ h7 _ h8 hne0
  rcases eq_or_of_encard_le_two hc h9 h10 (c := x0') h7' hne with e | e
  · have e' : y0' = y1 := by
      rcases eq_or_of_encard_le_two hc h9 h10 (c := y0') h8' hne with e' | e'
      · exact absurd (e.trans e'.symm) hne'
      · exact e'
    subst e e'
    exact LiftPair.close_aux h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h1' h2' h3' h4' h5' h6' hi huc hpq
  · have e' : y0' = x1 := by
      rcases eq_or_of_encard_le_two hc h9 h10 (c := y0') h8' hne with e' | e'
      · exact e'
      · exact absurd (e.trans e'.symm) hne'
    subst e e'
    have hpq' : (y1' = x0 ∧ x1' = y0) ∨ (y1' = y0 ∧ x1' = x0) := by
      rcases hpq with h | h
      · exact .inr ⟨h.2, h.1⟩
      · exact .inl ⟨h.2, h.1⟩
    exact LiftPair.close_aux h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h2' h1' h3'.symm (by rw [union_comm,
      h4']) h6' h5' hi huc hpq'

omit [TopologicalSpace S] in
/-- Two continuous lifts of a path, that differ at each point and fill the preimage of its image. -/
theorem liftPair_of_maps {a : ℝ → S} {r r' : ℝ → S'} (hr : ContinuousOn r (Icc 0 1))
  (hr' : ContinuousOn r' (Icc 0 1))
    (hψ : ∀ t ∈ Icc (0 : ℝ) 1, ψ (r t) = a t) (hψ' : ∀ t ∈ Icc (0 : ℝ) 1, ψ (r' t) = a t)
      (ha : InjOn a (Icc 0 1))
    (hne : ∀ t ∈ Icc (0 : ℝ) 1, r t ≠ r' t) (hfill : ∀ z, ψ z ∈ a '' Icc 0 1
      → z ∈ r '' Icc 0 1 ∪ r' '' Icc 0 1) :
    LiftPair ψ (a '' Icc 0 1) (a 0) (a 1) (r '' Icc 0 1) (r' '' Icc 0 1) := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have line : ∀ q : ℝ → S', ContinuousOn q (Icc 0 1) → (∀ t ∈ Icc (0 : ℝ) 1, ψ (q t) = a t) →
      IsLineWithEnds (q '' Icc 0 1) (q 0) (q 1) := by
    intro q hq hψq
    have harc : IsArcMap fun t : 𝕀 => q t := by
      refine ⟨continuousOn_iff_continuous_domRestrict.mp hq, fun s t he => ?_⟩
      have h2 : a s = a t := by
        rw [← hψq s s.2, ← hψq t t.2]
        exact congrArg ψ he
      exact Subtype.ext (ha s.2 t.2 h2)
    have := harc.isLineWithEnds
    have e : range (fun t : 𝕀 => q t) = q '' Icc 0 1 := by
      ext z
      constructor
      · rintro ⟨t, rfl⟩
        exact ⟨t, t.2, rfl⟩
      · rintro ⟨t, ht, rfl⟩
        exact ⟨⟨t, ht⟩, rfl⟩
    rw [e] at this
    exact this
  have bij : ∀ q : ℝ → S', (∀ t ∈ Icc (0 : ℝ) 1, ψ (q t) = a t) → BijOn ψ (q '' Icc 0 1)
    (a '' Icc 0 1) := by
    intro q hψq
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨t, ht, rfl⟩
      exact ⟨t, ht, (hψq t ht).symm⟩
    · rintro _ ⟨t, ht, rfl⟩ _ ⟨t', ht', rfl⟩ he
      rw [hψq t ht, hψq t' ht'] at he
      rw [ha ht ht' he]
    · rintro _ ⟨t, ht, rfl⟩
      exact ⟨q t, ⟨t, ht, rfl⟩, hψq t ht⟩
  refine ⟨r 0, r 1, r' 0, r' 1, line r hr hψ, line r' hr' hψ', ?_, ?_, bij r hψ, bij r' hψ',
    hψ 0 h0, hψ' 0 h0, hψ 1 h1,
    hψ' 1 h1⟩
  · rw [Set.disjoint_left]
    rintro _ ⟨t, ht, rfl⟩ ⟨t', ht', he⟩
    have h2 : a t' = a t := by rw [← hψ t ht, ← hψ' t' ht', he]
    rw [ha ht' ht h2] at he
    exact hne t ht he.symm
  · ext z
    constructor
    · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
      · exact ⟨t, ht, (hψ t ht).symm⟩
      · exact ⟨t, ht, (hψ' t ht).symm⟩
    · exact hfill z

end GraphMinor.Surface
