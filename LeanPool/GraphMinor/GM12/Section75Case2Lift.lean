/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM10.Section8
public import LeanPool.GraphMinor.GM10.TangleLemmas

/-!
# Two small sides and an edge cover a graph

A hypergraph fact for the order 2 step of Case 2 of XII (7.5). Let `T` be a tangle of order 3 in a
graph
`G`, and let `T'` be the tangle of order 2 in `G \ v` that it gives. Suppose `(A₁, B₁)` and `(A₂,
B₂)` are
in `T'`, and that `A₁`, `A₂` and one edge `g` of `G \ v` make up `G \ v`. Then `A₁`, `A₂`, each with
the
edges at `v` that go to it, and `g` are three small sides that cover `G`. This cannot happen
(`false_of_cover_of_edge`).
-/

@[expose] public section

namespace GraphMinor.GM12

open Set Hypergraph GraphMinor.GM10

variable {α β : Type*}

/-- `A` with `v` and with the edges at `v` all of whose other ends lie in `A`. -/
def starLeft (G A : Hypergraph α β) (v : α) (hA : A ≤ G.deleteVertices {v}) (hv : v ∈ G.vertexSet) :
    Hypergraph α β where
  vertexSet := A.vertexSet ∪ {v}
  edgeSet := A.edgeSet ∪ {f ∈ G.edgeSet | G.Inc f v ∧ ∀ w, G.Inc f w → w = v ∨ w ∈ A.vertexSet}
  Inc f w := G.Inc f w ∧
    (f ∈ A.edgeSet ∨ f ∈ G.edgeSet ∧ G.Inc f v ∧ ∀ w, G.Inc f w → w = v ∨ w ∈ A.vertexSet)
  vertex_mem_of_inc f w h := by
    obtain ⟨h₁, hf | hf⟩ := h
    · have hd : w ∈ (G.deleteVertices {v}).ends f := by
        have hf' := hA.edgeSet_subset hf
        exact ⟨h₁, fun u hu => hu ▸ hf'.2 v rfl⟩
      rw [hA.ends_eq f hf] at hd
      exact Or.inl (A.vertex_mem_of_inc hd)
    · rcases hf.2.2 w h₁ with rfl | h'
      · exact Or.inr rfl
      · exact Or.inl h'
  edge_mem_of_inc f w h := by
    obtain ⟨_, hf | hf⟩ := h
    · exact Or.inl hf
    · exact Or.inr hf
  vertexSet_finite := A.vertexSet_finite.union (finite_singleton v)
  edgeSet_finite := A.edgeSet_finite.union (G.edgeSet_finite.subset fun _ h => h.1)

/-- The other side of `starLeft`. -/
def starRight (G A B : Hypergraph α β) (v : α) (hG : G.IsGraph)
    (hAB : (G.deleteVertices {v}).IsSeparation A B) (hv : v ∈ G.vertexSet) :
    Hypergraph α β where
  vertexSet := B.vertexSet ∪ {v}
  edgeSet := G.edgeSet \ (starLeft G A v hAB.left_le hv).edgeSet
  Inc f w := G.Inc f w ∧ f ∉ (starLeft G A v hAB.left_le hv).edgeSet
  vertex_mem_of_inc f w h := by
    obtain ⟨h₁, hf⟩ := h
    have hfG := G.edge_mem_of_inc h₁
    have hwG := G.vertex_mem_of_inc h₁
    by_cases hw : w = v
    · exact Or.inr hw
    by_cases hfv : G.Inc f v
    · have : ∃ y, G.Inc f y ∧ y ≠ v ∧ y ∉ A.vertexSet := by
        by_contra hn
        push Not at hn
        exact hf (Or.inr ⟨hfG, hfv, fun y hy => by
          by_cases hyv : y = v
          · exact Or.inl hyv
          · exact Or.inr (hn y hy hyv)⟩)
      obtain ⟨y, hy, hyv, hyA⟩ := this
      have hwy : w = y := by
        by_contra hne
        have hsub : ({v, w, y} : Set α) ⊆ G.ends f := by
          rintro z (rfl | rfl | rfl)
          · exact hfv
          · exact h₁
          · exact hy
        have hcard : ({v, w, y} : Set α).ncard = 3 := by
          rw [ncard_insert_of_notMem (by simp [Ne.symm hw, Ne.symm hyv]) (by simp),
            ncard_pair hne]
        have := ncard_le_ncard hsub (G.vertexSet_finite.subset fun _ h => G.vertex_mem_of_inc h)
        have := (hG f hfG).2
        omega
      have hmem : y ∈ A.vertexSet ∪ B.vertexSet := by
        have h' : (A ∪ B).vertexSet = _ := congrArg vertexSet hAB.union_eq
        change _ = G.vertexSet \ {v} at h'
        change y ∈ (A ∪ B).vertexSet
        rw [h']
        exact ⟨G.vertex_mem_of_inc hy, hyv⟩
      exact Or.inl (hwy ▸ hmem.resolve_left hyA)
    · have hfd : f ∈ (G.deleteVertices {v}).edgeSet := ⟨hfG, fun u hu => hu ▸ hfv⟩
      have hfB : f ∈ B.edgeSet := by
        have h' : (A ∪ B).edgeSet = _ := congrArg edgeSet hAB.union_eq
        have : f ∈ (A ∪ B).edgeSet := h' ▸ hfd
        exact this.resolve_left fun h'' => hf (Or.inl h'')
      have hd : w ∈ (G.deleteVertices {v}).ends f := ⟨h₁, fun u hu => hu ▸ hfv⟩
      rw [hAB.right_le.ends_eq f hfB] at hd
      exact Or.inl (B.vertex_mem_of_inc hd)
  edge_mem_of_inc f w h := ⟨G.edge_mem_of_inc h.1, h.2⟩
  vertexSet_finite := B.vertexSet_finite.union (finite_singleton v)
  edgeSet_finite := G.edgeSet_finite.subset sdiff_subset

variable {G A B : Hypergraph α β} {v : α}

theorem notMem_of_le_delete (hA : A ≤ G.deleteVertices {v}) : v ∉ A.vertexSet := fun h =>
  (hA.vertexSet_subset h).2 rfl

theorem star_isSeparation (hG : G.IsGraph) (hAB : (G.deleteVertices {v}).IsSeparation A B)
    (hv : v ∈ G.vertexSet) :
    G.IsSeparation (starLeft G A v hAB.left_le hv) (starRight G A B v hG hAB hv) := by
  have hUV : ∀ w, w ∈ G.vertexSet → w = v ∨ w ∈ A.vertexSet ∨ w ∈ B.vertexSet := by
    intro w hw
    by_cases hwv : w = v
    · exact Or.inl hwv
    · right
      have h' : (A ∪ B).vertexSet = _ := congrArg vertexSet hAB.union_eq
      change w ∈ (A ∪ B).vertexSet
      rw [h']
      exact ⟨hw, hwv⟩
  have hAE : A.edgeSet ⊆ G.edgeSet := fun f hf => (hAB.left_le.edgeSet_subset hf).1
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · rintro w (h | h)
    · exact (hAB.left_le.vertexSet_subset h).1
    · exact (mem_singleton_iff.mp h) ▸ hv
  · rintro f (h | h)
    · exact hAE h
    · exact h.1
  · intro f hf
    ext w
    exact ⟨fun h => ⟨h, hf.imp id id⟩, fun h => h.1⟩
  · rintro w (h | h)
    · exact (hAB.right_le.vertexSet_subset h).1
    · exact (mem_singleton_iff.mp h) ▸ hv
  · exact fun f h => h.1
  · intro f hf
    ext w
    exact ⟨fun h => ⟨h, hf.2⟩, fun h => h.1⟩
  · refine Hypergraph.ext ?_ ?_ ?_
    · ext w
      constructor
      · rintro ((h | h) | (h | h))
        · exact (hAB.left_le.vertexSet_subset h).1
        · exact (mem_singleton_iff.mp h) ▸ hv
        · exact (hAB.right_le.vertexSet_subset h).1
        · exact (mem_singleton_iff.mp h) ▸ hv
      · intro hw
        rcases hUV w hw with h | h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inl (Or.inl h)
        · exact Or.inr (Or.inl h)
    · ext f
      constructor
      · rintro (h | h)
        · rcases h with h | h
          · exact hAE h
          · exact h.1
        · exact h.1
      · intro hf
        by_cases h : f ∈ (starLeft G A v hAB.left_le hv).edgeSet
        · exact Or.inl h
        · exact Or.inr ⟨hf, h⟩
    · funext f w
      apply propext
      constructor
      · rintro (h | h)
        · exact h.1
        · exact h.1
      · intro h
        by_cases hf : f ∈ (starLeft G A v hAB.left_le hv).edgeSet
        · exact Or.inl ⟨h, hf.imp id id⟩
        · exact Or.inr ⟨h, hf⟩
  · ext f
    simp only [mem_empty_iff_false, iff_false]
    exact fun h => h.2.2 h.1

theorem star_order_le (hG : G.IsGraph) (hAB : (G.deleteVertices {v}).IsSeparation A B)
    (hv : v ∈ G.vertexSet) :
    separationOrder (starLeft G A v hAB.left_le hv) (starRight G A B v hG hAB hv) ≤
      separationOrder A B + 1 := by
  have hsub : (starLeft G A v hAB.left_le hv ∩ starRight G A B v hG hAB hv).vertexSet ⊆
      insert v (A ∩ B).vertexSet := by
    rintro w ⟨h₁ | h₁, h₂ | h₂⟩
    · exact Or.inr ⟨h₁, h₂⟩
    · exact Or.inl h₂
    · exact Or.inl h₁
    · exact Or.inl h₁
  have hfin : (insert v (A ∩ B).vertexSet).Finite := (A ∩ B).vertexSet_finite.insert v
  exact (ncard_le_ncard hsub hfin).trans (ncard_insert_le _ _)

theorem starLeft_delete (hAB : (G.deleteVertices {v}).IsSeparation A B) (hv : v ∈ G.vertexSet) :
    (starLeft G A v hAB.left_le hv).deleteVertices {v} = A := by
  have hvA := notMem_of_le_delete hAB.left_le
  have hno : ∀ f ∈ A.edgeSet, ¬ G.Inc f v := fun f hf =>
    (hAB.left_le.edgeSet_subset hf).2 v rfl
  have hmem : ∀ f, (starLeft G A v hAB.left_le hv).Inc f v → f ∉ A.edgeSet := fun f h hf =>
    hno f hf h.1
  refine Hypergraph.ext ?_ ?_ ?_
  · ext w
    constructor
    · rintro ⟨h | h, h'⟩
      · exact h
      · exact absurd h h'
    · exact fun h => ⟨Or.inl h, fun h' => hvA (mem_singleton_iff.mp h' ▸ h)⟩
  · ext f
    constructor
    · rintro ⟨h | h, h'⟩
      · exact h
      · exact absurd ⟨h.2.1, Or.inr h⟩ (h' v rfl)
    · exact fun h => ⟨Or.inl h, fun u hu h' => hno f h (mem_singleton_iff.mp hu ▸ h'.1)⟩
  · funext f w
    apply propext
    constructor
    · rintro ⟨⟨h₁, h | h⟩, h₂⟩
      · have hd : w ∈ (G.deleteVertices {v}).ends f :=
          ⟨h₁, fun u hu => (mem_singleton_iff.mp hu) ▸ hno f h⟩
        rw [hAB.left_le.ends_eq f h] at hd
        exact hd
      · exact absurd ⟨h.2.1, Or.inr h⟩ (h₂ v rfl)
    · intro h
      have hf := A.edge_mem_of_inc h
      have hd : w ∈ (G.deleteVertices {v}).ends f := by
        rw [hAB.left_le.ends_eq f hf]
        exact h
      exact ⟨⟨hd.1, Or.inl hf⟩, fun u hu h' => hno f hf (mem_singleton_iff.mp hu ▸ h'.1)⟩

theorem starRight_delete (hG : G.IsGraph) (hAB : (G.deleteVertices {v}).IsSeparation A B)
    (hv : v ∈ G.vertexSet) :
    (starRight G A B v hG hAB hv).deleteVertices {v} = B := by
  have hvB := notMem_of_le_delete hAB.right_le
  have hno : ∀ f ∈ B.edgeSet, ¬ G.Inc f v := fun f hf =>
    (hAB.right_le.edgeSet_subset hf).2 v rfl
  have hBout : ∀ f ∈ B.edgeSet, f ∉ (starLeft G A v hAB.left_le hv).edgeSet := by
    rintro f hf (h | h)
    · have : f ∈ (A ∩ B).edgeSet := ⟨h, hf⟩
      rw [hAB.edgeSet_inter_eq] at this
      exact this
    · exact hno f hf h.2.1
  have hBE : ∀ f, f ∈ G.edgeSet → f ∉ (starLeft G A v hAB.left_le hv).edgeSet → ¬ G.Inc f v →
      f ∈ B.edgeSet := by
    intro f hf hn hfv
    have hfd : f ∈ (G.deleteVertices {v}).edgeSet := ⟨hf, fun u hu => hu ▸ hfv⟩
    have h' : (A ∪ B).edgeSet = _ := congrArg edgeSet hAB.union_eq
    have : f ∈ (A ∪ B).edgeSet := h' ▸ hfd
    exact this.resolve_left fun h'' => hn (Or.inl h'')
  refine Hypergraph.ext ?_ ?_ ?_
  · ext w
    constructor
    · rintro ⟨h | h, h'⟩
      · exact h
      · exact absurd h h'
    · exact fun h => ⟨Or.inl h, fun h' => hvB (mem_singleton_iff.mp h' ▸ h)⟩
  · ext f
    constructor
    · rintro ⟨h, h'⟩
      exact hBE f h.1 h.2 fun hi => h' v rfl ⟨hi, h.2⟩
    · intro h
      exact ⟨⟨(hAB.right_le.edgeSet_subset h).1, hBout f h⟩,
        fun u hu h' => hno f h (mem_singleton_iff.mp hu ▸ h'.1)⟩
  · funext f w
    apply propext
    constructor
    · rintro ⟨⟨h₁, h⟩, h₂⟩
      have hfB := hBE f (G.edge_mem_of_inc h₁) h fun hi => h₂ v rfl ⟨hi, h⟩
      have hd : w ∈ (G.deleteVertices {v}).ends f :=
        ⟨h₁, fun u hu => (mem_singleton_iff.mp hu) ▸ hno f hfB⟩
      rw [hAB.right_le.ends_eq f hfB] at hd
      exact hd
    · intro h
      have hf := B.edge_mem_of_inc h
      have hd : w ∈ (G.deleteVertices {v}).ends f := by
        rw [hAB.right_le.ends_eq f hf]
        exact h
      exact ⟨⟨hd.1, hBout f hf⟩, fun u hu h' => hno f hf (mem_singleton_iff.mp hu ▸ h'.1)⟩

/-- A separation in `T'` lifts to `T` with the edges at `v` placed as in `starLeft`. -/
theorem star_mem {T : Set (Hypergraph α β × Hypergraph α β)} (hG : G.IsGraph)
    (hT : IsTangle G 3 T) (hv : v ∈ G.vertexSet)
    (hT' : IsTangle (G.deleteVertices {v}) 2 (deleteVerticesTangle G {v} T 3))
    (hAB : (A, B) ∈ deleteVerticesTangle G {v} T 3) :
    ∃ (hs : (G.deleteVertices {v}).IsSeparation A B) ,
      (starLeft G A v hs.left_le hv, starRight G A B v hG hs hv) ∈ T := by
  have hs : (G.deleteVertices {v}).IsSeparation A B := hAB.1
  refine ⟨hs, ?_⟩
  have hsep := star_isSeparation hG hs hv
  have hord : separationOrder (starLeft G A v hs.left_le hv) (starRight G A B v hG hs hv) < 3 := by
    have h₁ := star_order_le hG hs hv
    have h₂ : separationOrder A B < 2 := hT'.order_lt hAB
    omega
  refine (hT.axiom1 hsep hord).resolve_right fun hn => ?_
  have hsymm : (G.deleteVertices {v}).IsSeparation B A := by
    refine ⟨hs.right_le, hs.left_le, ?_, ?_⟩
    · rw [← hs.union_eq]
      exact Hypergraph.ext (union_comm _ _) (union_comm _ _) (by
        funext f w; exact propext or_comm)
    · have : (B ∩ A).edgeSet = (A ∩ B).edgeSet := inter_comm _ _
      rw [this]
      exact hs.edgeSet_inter_eq
  have hordBA : separationOrder B A < 2 := by
    have h₂ : separationOrder A B < 2 := hT'.order_lt hAB
    have : separationOrder B A = separationOrder A B := by
      unfold separationOrder
      exact congrArg ncard (inter_comm _ _)
    omega
  have hBA : (B, A) ∈ deleteVerticesTangle G {v} T 3 := by
    refine ⟨hsymm, by simpa using hordBA, _, hn, ?_, starRight_delete hG hs hv,
      starLeft_delete hs hv⟩
    rintro w hw
    obtain rfl : w = v := hw
    exact ⟨Or.inr rfl, Or.inr rfl⟩
  refine hT'.axiom2 hAB hBA hBA ?_
  rw [← hs.union_eq]
  refine Hypergraph.ext (by ext w; exact or_iff_left_of_imp fun h => Or.inr h) (by
    ext w; exact or_iff_left_of_imp fun h => Or.inr h) ?_
  funext f w
  exact propext (or_iff_left_of_imp fun h => Or.inr h)

/-- The union of the left sides of some separations of `G` that all meet at most in `h`, as a
separation of `G` that meets in `h`. -/
def joinLeft (G : Hypergraph α β) (P : Set (Hypergraph α β × Hypergraph α β)) (h : α)
    (hP : ∀ p ∈ P, G.IsSeparation p.1 p.2) (_hh : h ∈ G.vertexSet) : Hypergraph α β where
  vertexSet := insert h (⋃ p ∈ P, p.1.vertexSet)
  edgeSet := ⋃ p ∈ P, p.1.edgeSet
  Inc f w := G.Inc f w ∧ f ∈ ⋃ p ∈ P, p.1.edgeSet
  vertex_mem_of_inc f w hi := by
    obtain ⟨p, hp, hf⟩ := mem_iUnion₂.mp hi.2
    have hw : w ∈ p.1.ends f := by
      rw [← (hP p hp).left_le.ends_eq f hf]
      exact hi.1
    exact Or.inr (mem_biUnion hp (p.1.vertex_mem_of_inc hw))
  edge_mem_of_inc _ _ hi := hi.2
  vertexSet_finite := (G.vertexSet_finite.subset fun w hw => by
    obtain ⟨p, hp, hw⟩ := mem_iUnion₂.mp hw
    exact (hP p hp).left_le.vertexSet_subset hw).insert h
  edgeSet_finite := G.edgeSet_finite.subset fun f hf => by
    obtain ⟨p, hp, hf⟩ := mem_iUnion₂.mp hf
    exact (hP p hp).left_le.edgeSet_subset hf

/-- The other side of `joinLeft`. -/
def joinRight (G : Hypergraph α β) (P : Set (Hypergraph α β × Hypergraph α β)) (h : α)
    (hP : ∀ p ∈ P, G.IsSeparation p.1 p.2) (_hh : h ∈ G.vertexSet)
    (hm : ∀ p ∈ P, (p.1 ∩ p.2).vertexSet ⊆ {h}) : Hypergraph α β where
  vertexSet := insert h (G.vertexSet \ ⋃ p ∈ P, p.1.vertexSet)
  edgeSet := G.edgeSet \ ⋃ p ∈ P, p.1.edgeSet
  Inc f w := G.Inc f w ∧ f ∉ ⋃ p ∈ P, p.1.edgeSet
  vertex_mem_of_inc f w hi := by
    by_cases hw : w = h
    · exact Or.inl hw
    refine Or.inr ⟨G.vertex_mem_of_inc hi.1, fun hc => ?_⟩
    obtain ⟨p, hp, hwp⟩ := mem_iUnion₂.mp hc
    have hs := hP p hp
    have hfG := G.edge_mem_of_inc hi.1
    have hfQ : f ∈ p.2.edgeSet := by
      have hu : (p.1 ∪ p.2).edgeSet = G.edgeSet := congrArg edgeSet hs.union_eq
      have : f ∈ (p.1 ∪ p.2).edgeSet := hu ▸ hfG
      exact this.resolve_left fun h' => hi.2 (mem_biUnion hp h')
    have hwQ : w ∈ p.2.ends f := by
      rw [← hs.right_le.ends_eq f hfQ]
      exact hi.1
    exact hw (hm p hp ⟨hwp, p.2.vertex_mem_of_inc hwQ⟩)
  edge_mem_of_inc f _ hi := ⟨G.edge_mem_of_inc hi.1, hi.2⟩
  vertexSet_finite := (G.vertexSet_finite.subset sdiff_subset).insert h
  edgeSet_finite := G.edgeSet_finite.subset sdiff_subset

theorem join_isSeparation {P : Set (Hypergraph α β × Hypergraph α β)} {h : α}
    (hP : ∀ p ∈ P, G.IsSeparation p.1 p.2) (hh : h ∈ G.vertexSet)
    (hm : ∀ p ∈ P, (p.1 ∩ p.2).vertexSet ⊆ {h}) :
    G.IsSeparation (joinLeft G P h hP hh) (joinRight G P h hP hh hm) := by
  have hVL : ∀ w ∈ ⋃ p ∈ P, p.1.vertexSet, w ∈ G.vertexSet := fun w hw => by
    obtain ⟨p, hp, hw⟩ := mem_iUnion₂.mp hw
    exact (hP p hp).left_le.vertexSet_subset hw
  have hEL : ∀ f ∈ ⋃ p ∈ P, p.1.edgeSet, f ∈ G.edgeSet := fun f hf => by
    obtain ⟨p, hp, hf⟩ := mem_iUnion₂.mp hf
    exact (hP p hp).left_le.edgeSet_subset hf
  refine ⟨⟨?_, hEL, ?_⟩, ⟨?_, sdiff_subset, ?_⟩, ?_, ?_⟩
  · rintro w (rfl | hw)
    · exact hh
    · exact hVL w hw
  · intro f hf
    ext w
    exact ⟨fun hi => ⟨hi, hf⟩, fun hi => hi.1⟩
  · rintro w (rfl | hw)
    · exact hh
    · exact hw.1
  · intro f hf
    ext w
    exact ⟨fun hi => ⟨hi, hf.2⟩, fun hi => hi.1⟩
  · refine Hypergraph.ext ?_ ?_ ?_
    · ext w
      constructor
      · rintro ((rfl | hw) | (rfl | hw))
        · exact hh
        · exact hVL w hw
        · exact hh
        · exact hw.1
      · intro hw
        by_cases hc : w ∈ ⋃ p ∈ P, p.1.vertexSet
        · exact Or.inl (Or.inr hc)
        · exact Or.inr (Or.inr ⟨hw, hc⟩)
    · ext f
      constructor
      · rintro (hf | hf)
        · exact hEL f hf
        · exact hf.1
      · intro hf
        by_cases hc : f ∈ ⋃ p ∈ P, p.1.edgeSet
        · exact Or.inl hc
        · exact Or.inr ⟨hf, hc⟩
    · funext f w
      apply propext
      constructor
      · rintro (hi | hi)
        · exact hi.1
        · exact hi.1
      · intro hi
        by_cases hc : f ∈ ⋃ p ∈ P, p.1.edgeSet
        · exact Or.inl ⟨hi, hc⟩
        · exact Or.inr ⟨hi, hc⟩
  · ext f
    simp only [mem_empty_iff_false, iff_false]
    exact fun hf => hf.2.2 hf.1

theorem join_inter_subset {P : Set (Hypergraph α β × Hypergraph α β)} {h : α}
    (hP : ∀ p ∈ P, G.IsSeparation p.1 p.2) (hh : h ∈ G.vertexSet)
    (hm : ∀ p ∈ P, (p.1 ∩ p.2).vertexSet ⊆ {h}) :
    (joinLeft G P h hP hh ∩ joinRight G P h hP hh hm).vertexSet = {h} := by
  ext w
  constructor
  · rintro ⟨h₁ | h₁, h₂ | h₂⟩
    · exact h₁
    · exact h₁
    · exact h₂
    · exact absurd h₁ h₂.2
  · intro hw
    exact ⟨Or.inl hw, Or.inl hw⟩

/-- See the module docstring. The hypotheses `hV` and `hE` say that `A₁`, `A₂` and `g` make up `G \
v`. -/
theorem false_of_cover_of_edge {A₁ B₁ A₂ B₂ : Hypergraph α β}
    {T : Set (Hypergraph α β × Hypergraph α β)} (hG : G.IsGraph)
    (hT : IsTangle G 3 T) (hv : v ∈ G.vertexSet)
    (hT' : IsTangle (G.deleteVertices {v}) 2 (deleteVerticesTangle G {v} T 3))
    (h₁ : (A₁, B₁) ∈ deleteVerticesTangle G {v} T 3)
    (h₂ : (A₂, B₂) ∈ deleteVerticesTangle G {v} T 3)
    {g : β} (hg : g ∈ G.edgeSet)
    (hV : ∀ w ∈ G.vertexSet, w ≠ v → w ∈ A₁.vertexSet ∨ w ∈ A₂.vertexSet)
    (hE : ∀ f ∈ G.edgeSet, ¬ G.Inc f v → f ≠ g → f ∈ A₁.edgeSet ∨ f ∈ A₂.edgeSet) : False := by
  obtain ⟨hs₁, hm₁⟩ := star_mem hG hT hv hT' h₁
  obtain ⟨hs₂, hm₂⟩ := star_mem hG hT hv hT' h₂
  have hsize : edgeSize G g < 3 := by
    have := (hG g hg).2
    unfold edgeSize
    omega
  have hm₃ := (GraphMinor.GM10.theorem_2_7_proof hT.one_le hT.isSeparation hT.order_lt hT.axiom1
    hT.axiom2).mp hT g hg hsize
  have hle₁ := (star_isSeparation hG hs₁ hv).left_le
  have hle₂ := (star_isSeparation hG hs₂ hv).left_le
  have hedge : ∀ f ∈ G.edgeSet, f ∈ (starLeft G A₁ v hs₁.left_le hv).edgeSet ∨
      f ∈ (starLeft G A₂ v hs₂.left_le hv).edgeSet ∨ f = g := by
    intro f hf
    by_cases hfv : G.Inc f v
    · by_cases hc : ∃ y, G.Inc f y ∧ y ≠ v
      · obtain ⟨y, hy, hyv⟩ := hc
        have honly : ∀ w, G.Inc f w → w = v ∨ w = y := by
          intro w hw
          by_contra hn
          push Not at hn
          have hsub : ({v, w, y} : Set α) ⊆ G.ends f := by
            rintro z (rfl | rfl | rfl)
            · exact hfv
            · exact hw
            · exact hy
          have hcard : ({v, w, y} : Set α).ncard = 3 := by
            rw [ncard_insert_of_notMem (by simp [Ne.symm hn.1, Ne.symm hyv]) (by simp),
              ncard_pair hn.2]
          have := ncard_le_ncard hsub (G.vertexSet_finite.subset fun _ h => G.vertex_mem_of_inc h)
          have := (hG f hf).2
          omega
        rcases hV y (G.vertex_mem_of_inc hy) hyv with h | h
        · exact Or.inl (Or.inr ⟨hf, hfv, fun w hw => (honly w hw).imp id (fun (e : w = y)
          => e ▸ h)⟩)
        · exact Or.inr (Or.inl (Or.inr ⟨hf, hfv, fun w hw => (honly w hw).imp id (fun (e : w = y)
          => e ▸ h)⟩))
      · push Not at hc
        exact Or.inl (Or.inr ⟨hf, hfv, fun w hw => Or.inl (hc w hw)⟩)
    · by_cases hfg : f = g
      · exact Or.inr (Or.inr hfg)
      · rcases hE f hf hfv hfg with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr (Or.inl (Or.inl h))
  refine hT.axiom2 hm₁ hm₂ hm₃ ?_
  refine Hypergraph.ext ?_ ?_ ?_
  · ext w
    constructor
    · rintro ((h | h) | h)
      · exact hle₁.vertexSet_subset h
      · exact hle₂.vertexSet_subset h
      · exact G.vertex_mem_of_inc h
    · intro hw
      by_cases hwv : w = v
      · exact Or.inl (Or.inl (Or.inr hwv))
      · rcases hV w hw hwv with h | h
        · exact Or.inl (Or.inl (Or.inl h))
        · exact Or.inl (Or.inr (Or.inl h))
  · ext f
    constructor
    · rintro ((h | h) | h)
      · exact hle₁.edgeSet_subset h
      · exact hle₂.edgeSet_subset h
      · exact (mem_singleton_iff.mp h) ▸ hg
    · intro hf
      rcases hedge f hf with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  · funext f w
    apply propext
    constructor
    · rintro ((h | h) | h)
      · exact h.1
      · exact h.1
      · exact h.1 ▸ h.2
    · intro h
      rcases hedge f (G.edge_mem_of_inc h) with hf | hf | hf
      · exact Or.inl (Or.inl ⟨h, hf.imp id id⟩)
      · exact Or.inl (Or.inr ⟨h, hf.imp id id⟩)
      · exact Or.inr ⟨hf, hf ▸ h⟩

end GraphMinor.GM12
