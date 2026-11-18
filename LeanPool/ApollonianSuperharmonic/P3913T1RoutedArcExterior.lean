/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Order.DenselyOrdered

public import LeanPool.ApollonianSuperharmonic.P3723T1AllContactRouting

-- [TABLET NODE: P3913T1RoutedArcExterior]

/-!
# P3913T1RoutedArcExterior

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3913T1RoutedArcExterior {ι : Type} (P : PeriodicTileComplex ι)
    (D : P3723T1AllContactRouting P) (f : P.plane.Face)
    (U V : Set (Real × Real)) (hU : IsOpen U) (hV : IsOpen V)
    (hd : Disjoint U V)
    (hp : U ∪ V = (D.edgeArc (P.plane.faceVertex f 0) (P.plane.faceVertex f 1) ∪
      D.edgeArc (P.plane.faceVertex f 1) (P.plane.faceVertex f 2) ∪
      D.edgeArc (P.plane.faceVertex f 2) (P.plane.faceVertex f 0))ᶜ)
    (hout : ∀ a, a ∉ Set.range (P.plane.faceVertex f) → D.position a ∈ V) :
    let J := D.edgeArc (P.plane.faceVertex f 0) (P.plane.faceVertex f 1) ∪
      D.edgeArc (P.plane.faceVertex f 1) (P.plane.faceVertex f 2) ∪
      D.edgeArc (P.plane.faceVertex f 2) (P.plane.faceVertex f 0)
    (Set.range D.position ⊆ J ∪ V) ∧
    (∀ a b, P.plane.adjacent a b →
      (a ∉ Set.range (P.plane.faceVertex f) ∨
        b ∉ Set.range (P.plane.faceVertex f)) →
      D.edgeArc a b \ {D.position a, D.position b} ⊆ V) ∧
    ∀ a b, P.plane.adjacent a b → D.edgeArc a b ⊆ J ∪ V := by
-- BODY
  classical
  dsimp only
  let J := D.edgeArc (P.plane.faceVertex f 0) (P.plane.faceVertex f 1) ∪
    D.edgeArc (P.plane.faceVertex f 1) (P.plane.faceVertex f 2) ∪
    D.edgeArc (P.plane.faceVertex f 2) (P.plane.faceVertex f 0)
  have contact (a b : ι) (hab : P.plane.adjacent a b) :
      P3723T1EdgeContact P a b :=
    ⟨(fun e => P.plane.adjacent_irreflexive a (e.symm ▸ hab)),
      P.adjacent_has_common_edge a b hab⟩
  have faceArc_sub (i j : Fin 3) (hij : i ≠ j) :
      D.edgeArc (P.plane.faceVertex f i) (P.plane.faceVertex f j) ⊆ J := by
    intro x hx
    fin_cases i <;> fin_cases j <;> dsimp [J] at *
    all_goals try exact (hij rfl).elim
    all_goals first
      | exact Or.inl (Or.inl hx)
      | exact Or.inl (Or.inr hx)
      | exact Or.inr hx
      | rw [D.edgeArc_symmetric] at hx
        first
          | exact Or.inl (Or.inl hx)
          | exact Or.inl (Or.inr hx)
          | exact Or.inr hx
  have facePos (i : Fin 3) : D.position (P.plane.faceVertex f i) ∈ J := by
    have hi : i ≠ i + 1 := by fin_cases i <;> decide
    obtain ⟨e, he, _⟩ := D.edgeArc_homeomorph _ _
      (contact _ _ (P.plane.face_edges f i (i + 1) hi))
    apply faceArc_sub i (i + 1) hi
    rw [← he]
    exact (e ⟨0, by norm_num⟩).property
  have pos : Set.range D.position ⊆ J ∪ V := by
    rintro x ⟨a, rfl⟩
    by_cases ha : a ∈ Set.range (P.plane.faceVertex f)
    · obtain ⟨i, rfl⟩ := ha
      exact Or.inl (facePos i)
    · exact Or.inr (hout a ha)
  have pair_mem (x : ι) (i j : Fin 3)
      (hx : x ∈ ({P.plane.faceVertex f i, P.plane.faceVertex f j} : Set ι)) :
      x ∈ Set.range (P.plane.faceVertex f) := by
    rcases Set.mem_insert_iff.mp hx with h | h
    · exact ⟨i, h.symm⟩
    · exact ⟨j, (Set.mem_singleton_iff.mp h).symm⟩
  have openArc (a b : ι) (hab : P.plane.adjacent a b)
      (ha : a ∉ Set.range (P.plane.faceVertex f) ∨
        b ∉ Set.range (P.plane.faceVertex f)) :
      D.edgeArc a b \ {D.position a, D.position b} ⊆ V := by
    let H := D.edgeArc a b \ {D.position a, D.position b}
    have hmiss : Disjoint H J := by
      have misses (i j : Fin 3) (hij : i ≠ j) :
          Disjoint H (D.edgeArc (P.plane.faceVertex f i) (P.plane.faceVertex f j)) := by
        have hne : ({a, b} : Set ι) ≠
            {P.plane.faceVertex f i, P.plane.faceVertex f j} := by
          intro heq
          rcases ha with ha | hb
          · apply ha
            exact pair_mem a i j (heq ▸ (by simp))
          · apply hb
            exact pair_mem b i j (heq ▸ (by simp))
        apply Set.disjoint_left.mpr
        intro x hx hy
        have hxint : x ∈ D.position '' (({a, b} : Set ι) ∩
            {P.plane.faceVertex f i, P.plane.faceVertex f j}) := by
          rw [← D.edgeArc_intersections a b _ _ (contact a b hab)
            (contact _ _ (P.plane.face_edges f i j hij)) hne]
          exact ⟨hx.1, hy⟩
        obtain ⟨w, hw, hwx⟩ := hxint
        apply hx.2
        rcases Set.mem_insert_iff.mp hw.1 with hw | hw
        · simp [← hwx, hw]
        · simp [← hwx, Set.mem_singleton_iff.mp hw]
      apply Set.disjoint_left.mpr
      intro x hx hxJ
      rcases hxJ with (hxJ | hxJ) | hxJ
      · exact Set.disjoint_left.mp (misses 0 1 (by decide)) hx hxJ
      · exact Set.disjoint_left.mp (misses 1 2 (by decide)) hx hxJ
      · exact Set.disjoint_left.mp (misses 2 0 (by decide)) hx hxJ
    obtain ⟨g, hg, hgi, hgr, hg0, hg1, _⟩ :=
      D.edgeArc_parameterization a b (contact a b hab)
    let t0 : Set.Icc (0 : Real) 1 := ⟨0, by norm_num⟩
    let t1 : Set.Icc (0 : Real) 1 := ⟨1, by norm_num⟩
    have hne : t0 ≠ t1 := by
      intro h
      have hh := congrArg Subtype.val h
      norm_num [t0, t1] at hh
    have hrange : g '' Set.Ioo t0 t1 = H := by
      ext x
      constructor
      · rintro ⟨t, ht, rfl⟩
        refine ⟨hgr ▸ Set.mem_range_self t, ?_⟩
        intro hx
        rcases Set.mem_insert_iff.mp hx with hx | hx
        · have heq : t = t0 := hgi (hx.trans hg0.symm)
          exact (ne_of_gt ht.1) heq
        · have heq : t = t1 := hgi ((Set.mem_singleton_iff.mp hx).trans hg1.symm)
          exact (ne_of_lt ht.2) heq
      · intro hx
        obtain ⟨t, rfl⟩ := hgr.symm ▸ hx.1
        refine ⟨t, ⟨?_, ?_⟩, rfl⟩
        · apply lt_of_le_of_ne t.property.1
          intro heq
          have heq' : t0 = t := Subtype.ext heq
          exact hx.2 (by simp [← heq', t0, hg0])
        · apply lt_of_le_of_ne t.property.2
          intro heq
          have heq' : t = t1 := Subtype.ext heq
          exact hx.2 (by simp [heq', t1, hg1])
    have hpre : IsPreconnected H := by
      rw [← hrange]
      exact isPreconnected_Ioo.image g hg.continuousOn
    have hsub : H ⊆ U ∪ V := by
      intro x hx
      rw [hp]
      exact fun hxJ => Set.disjoint_left.mp hmiss hx hxJ
    have hcl (t : Set.Icc (0 : Real) 1) : g t ∈ closure H := by
      rw [← hrange]
      apply mem_closure_image hg.continuousAt
      rw [closure_Ioo hne]
      exact t.property
    have hmeet : (H ∩ V).Nonempty := by
      have he : g t0 ∈ V ∨ g t1 ∈ V := by
        rcases ha with ha | hb
        · exact Or.inl (hg0.symm ▸ hout a ha)
        · exact Or.inr (hg1.symm ▸ hout b hb)
      rcases he with he | he
      · obtain ⟨x, hxV, hxH⟩ := (mem_closure_iff.mp (hcl t0)) V hV he
        exact ⟨x, hxH, hxV⟩
      · obtain ⟨x, hxV, hxH⟩ := (mem_closure_iff.mp (hcl t1)) V hV he
        exact ⟨x, hxH, hxV⟩
    exact hpre.subset_right_of_subset_union hU hV hd hsub hmeet
  refine ⟨pos, openArc, ?_⟩
  intro a b hab x hx
  by_cases ha : a ∈ Set.range (P.plane.faceVertex f)
  · by_cases hb : b ∈ Set.range (P.plane.faceVertex f)
    · obtain ⟨i, rfl⟩ := ha
      obtain ⟨j, rfl⟩ := hb
      have hij : i ≠ j := by
        intro heq
        subst j
        exact P.plane.adjacent_irreflexive _ hab
      exact Or.inl (faceArc_sub i j hij hx)
    · by_cases hend : x ∈ ({D.position a, D.position b} : Set (Real × Real))
      · rcases Set.mem_insert_iff.mp hend with h | h
        · exact pos ⟨a, h.symm⟩
        · exact pos ⟨b, (Set.mem_singleton_iff.mp h).symm⟩
      · exact Or.inr (openArc a b hab (Or.inr hb) ⟨hx, hend⟩)
  · by_cases hend : x ∈ ({D.position a, D.position b} : Set (Real × Real))
    · rcases Set.mem_insert_iff.mp hend with h | h
      · exact pos ⟨a, h.symm⟩
      · exact pos ⟨b, (Set.mem_singleton_iff.mp h).symm⟩
    · exact Or.inr (openArc a b hab (Or.inl ha) ⟨hx, hend⟩)

end ApollonianSuperharmonic

end
