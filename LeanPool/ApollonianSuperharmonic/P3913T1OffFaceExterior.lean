/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P3723T1AllContactRouting
public import LeanPool.ApollonianSuperharmonic.P3767T1VertexEdgeIncidence
public import LeanPool.ApollonianSuperharmonic.P3776T1FixedGeometry
public import LeanPool.ApollonianSuperharmonic.P3913T1PeriodicPositionUnbounded

-- [TABLET NODE: P3913T1OffFaceExterior]

/-!
# P3913T1OffFaceExterior

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3913T1OffFaceExterior {ι : Type} (P : PeriodicTileComplex ι)
    (D : P3723T1AllContactRouting P) (f : P.plane.Face)
    (U V : Set (Real × Real)) (hU : IsOpen U) (hV : IsOpen V)
    (hb : Bornology.IsBounded U) (hd : Disjoint U V)
    (hp : U ∪ V = (D.edgeArc (P.plane.faceVertex f 0) (P.plane.faceVertex f 1) ∪
      D.edgeArc (P.plane.faceVertex f 1) (P.plane.faceVertex f 2) ∪
      D.edgeArc (P.plane.faceVertex f 2) (P.plane.faceVertex f 0))ᶜ)
    (hdelete : ∀ a b : ι,
      a ∉ Set.range (P.plane.faceVertex f) →
      b ∉ Set.range (P.plane.faceVertex f) →
      ∃ p : List ι,
        p.head? = some a ∧ p.getLast? = some b ∧
        (∀ x ∈ p, x ∉ Set.range (P.plane.faceVertex f)) ∧
        ∀ x y : ι, ∀ l₁ l₂ : List ι,
          p = l₁ ++ x :: y :: l₂ → P.plane.adjacent x y) :
    (¬ Bornology.IsBounded
      (D.position '' (Set.range (P.plane.faceVertex f))ᶜ)) ∧
    ∀ a, a ∉ Set.range (P.plane.faceVertex f) → D.position a ∈ V := by
-- BODY
  classical
  let : Nontrivial ι := (P3776T1FixedGeometry P.toPeriodicTileCore).1
  let A := Set.range (P.plane.faceVertex f)
  let J := D.edgeArc (P.plane.faceVertex f 0) (P.plane.faceVertex f 1) ∪
    D.edgeArc (P.plane.faceVertex f 1) (P.plane.faceVertex f 2) ∪
    D.edgeArc (P.plane.faceVertex f 2) (P.plane.faceVertex f 0)
  have contact (a b : ι) (h : P.plane.adjacent a b) :
      P3723T1EdgeContact P a b :=
    ⟨(fun e => P.plane.adjacent_irreflexive a (e.symm ▸ h)),
      P.adjacent_has_common_edge a b h⟩
  have vertex_on_edge (x a b : ι) (hab : P.plane.adjacent a b)
      (hx : D.position x ∈ D.edgeArc a b) : x = a ∨ x = b := by
    obtain ⟨y, hxy⟩ := (P3767T1VertexEdgeIncidence P.plane x).1
    obtain ⟨g, h0, _⟩ := D.edgeArc_homeomorph x y (contact x y hxy)
    have hxpos : D.position x ∈ D.edgeArc x y := by
      rw [← h0]
      exact (g ⟨0, by norm_num⟩).property
    by_cases heq : ({x, y} : Set ι) = {a, b}
    · have hm : x ∈ ({a, b} : Set ι) := heq ▸ (by simp)
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hm
    · have hm : D.position x ∈ D.position '' (({x, y} : Set ι) ∩ {a, b}) := by
        rw [← D.edgeArc_intersections x y a b (contact x y hxy)
          (contact a b hab) heq]
        exact ⟨hxpos, hx⟩
      obtain ⟨z, hz, hzx⟩ := hm
      have hzx' : z = x := D.position_injective hzx
      subst z
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hz.2
  have vertex_miss (x : ι) (hx : x ∉ A) : D.position x ∉ J := by
    intro hxJ
    rcases hxJ with (hxJ | hxJ) | hxJ
    · rcases vertex_on_edge x _ _ (P.plane.face_edges f 0 1 (by decide)) hxJ with h | h
      · exact hx ⟨0, h.symm⟩
      · exact hx ⟨1, h.symm⟩
    · rcases vertex_on_edge x _ _ (P.plane.face_edges f 1 2 (by decide)) hxJ with h | h
      · exact hx ⟨1, h.symm⟩
      · exact hx ⟨2, h.symm⟩
    · rcases vertex_on_edge x _ _ (P.plane.face_edges f 2 0 (by decide)) hxJ with h | h
      · exact hx ⟨2, h.symm⟩
      · exact hx ⟨0, h.symm⟩
  have edge_miss (a b : ι) (hab : P.plane.adjacent a b) (ha : a ∉ A) (hb : b ∉ A) :
      Disjoint (D.edgeArc a b) J := by
    have pair_miss (i j : Fin 3) :
        Disjoint ({a, b} : Set ι)
          ({P.plane.faceVertex f i, P.plane.faceVertex f j} : Set ι) := by
      apply Set.disjoint_left.mpr
      intro z hz hz'
      have hzA : z ∈ A := by
        rcases Set.mem_insert_iff.mp hz' with h | h
        · exact ⟨i, h.symm⟩
        · exact ⟨j, (Set.mem_singleton_iff.mp h).symm⟩
      rcases Set.mem_insert_iff.mp hz with h | h
      · exact ha (h ▸ hzA)
      · exact hb ((Set.mem_singleton_iff.mp h) ▸ hzA)
    have misses (i j : Fin 3) (hij : i ≠ j) :
        Disjoint (D.edgeArc a b)
          (D.edgeArc (P.plane.faceVertex f i) (P.plane.faceVertex f j)) := by
      have hne : ({a, b} : Set ι) ≠
          {P.plane.faceVertex f i, P.plane.faceVertex f j} := by
        intro heq
        have hleft : a ∈ ({a, b} : Set ι) := by simp
        have hright : a ∈
            ({P.plane.faceVertex f i, P.plane.faceVertex f j} : Set ι) := heq ▸ hleft
        exact Set.disjoint_left.mp (pair_miss i j) hleft hright
      apply Set.disjoint_left.mpr
      intro z hz hz'
      have hm : z ∈ D.position '' (({a, b} : Set ι) ∩
          {P.plane.faceVertex f i, P.plane.faceVertex f j}) := by
        rw [← D.edgeArc_intersections a b _ _ (contact a b hab)
          (contact _ _ (P.plane.face_edges f i j hij)) hne]
        exact ⟨hz, hz'⟩
      obtain ⟨w, hw, _⟩ := hm
      exact Set.disjoint_left.mp (pair_miss i j) hw.1 hw.2
    apply Set.disjoint_left.mpr
    intro z hz hzJ
    rcases hzJ with (hzJ | hzJ) | hzJ
    · exact Set.disjoint_left.mp (misses 0 1 (by decide)) hz hzJ
    · exact Set.disjoint_left.mp (misses 1 2 (by decide)) hz hzJ
    · exact Set.disjoint_left.mp (misses 2 0 (by decide)) hz hzJ
  have adjacent_same (a b : ι) (ha : a ∉ A) (hb : b ∉ A)
      (hab : P.plane.adjacent a b) : D.position a ∈ U ↔ D.position b ∈ U := by
    obtain ⟨g, hg, _, hr, h0, h1, _⟩ := D.edgeArc_parameterization a b (contact a b hab)
    let : ConnectedSpace (Set.Icc (0 : Real) 1) :=
      isConnected_iff_connectedSpace.mp (isConnected_Icc (by norm_num))
    have hpre : IsPreconnected (D.edgeArc a b) := hr ▸ isPreconnected_range hg
    have hsub : D.edgeArc a b ⊆ U ∪ V := by
      intro z hz
      rw [hp]
      exact fun hzJ => Set.disjoint_left.mp (edge_miss a b hab ha hb) hz hzJ
    have hposa : D.position a ∈ D.edgeArc a b := h0 ▸ hr ▸ Set.mem_range_self _
    have hposb : D.position b ∈ D.edgeArc a b := h1 ▸ hr ▸ Set.mem_range_self _
    rcases hpre.subset_or_subset hU hV hd hsub with h | h
    · exact ⟨fun _ => h hposb, fun _ => h hposa⟩
    · constructor
      · intro hu
        exact (Set.disjoint_left.mp hd hu (h hposa)).elim
      · intro hu
        exact (Set.disjoint_left.mp hd hu (h hposb)).elim
  have walk_same (l : List ι)
      (hv : ∀ x ∈ l, x ∉ A)
      (he : ∀ x y : ι, ∀ l₁ l₂ : List ι,
        l = l₁ ++ x :: y :: l₂ → P.plane.adjacent x y) :
      ∀ a b, l.head? = some a → l.getLast? = some b →
        (D.position a ∈ U ↔ D.position b ∈ U) := by
    induction l with
    | nil => intro a b h; simp at h
    | cons x xs ih =>
      intro a b hhead hlast
      have hxa : x = a := by simpa using hhead
      subst a
      cases xs with
      | nil =>
        have hxb : x = b := by simpa using hlast
        subst b
        rfl
      | cons y ys =>
        have htail := ih (fun z hz => hv z (by simp [hz]))
          (fun u v l₁ l₂ h => he u v (x :: l₁) l₂ (by simp [h]))
          y b rfl (by simpa using hlast)
        exact (adjacent_same x y (hv x (by simp)) (hv y (by simp))
          (he x y [] ys rfl)).trans htail
  have same (a b : ι) (ha : a ∉ A) (hb : b ∉ A) :
      D.position a ∈ U ↔ D.position b ∈ U := by
    obtain ⟨l, hhead, hlast, hv, he⟩ := hdelete a b ha hb
    exact walk_same l hv he a b hhead hlast
  have hnb : ¬ Bornology.IsBounded (D.position '' Aᶜ) :=
    P3913T1PeriodicPositionUnbounded P D A (Set.finite_range _)
  refine ⟨hnb, ?_⟩
  intro a ha
  have hnU : D.position a ∉ U := by
    intro haU
    apply hnb
    apply hb.subset
    rintro z ⟨b, hbA, rfl⟩
    exact (same a b ha hbA).mp haU
  have hUV : D.position a ∈ U ∪ V := by
    rw [hp]
    exact vertex_miss a ha
  exact hUV.resolve_left hnU

end ApollonianSuperharmonic

end
