/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.CylinderCut
public import LeanPool.GraphMinor.GM14.NaturalOrderArc
public import LeanPool.GraphMinor.GM14.PieceFacts
public import LeanPool.GraphMinor.GM14.Section5

/-!
# Small steps of the proof of (8.4)

The main results: `path_in_side` says that a path that starts on one side of a separation and meets
the common vertices only at its end stays on that side. `exists_nest_between` gives the `π + 5`
nested circuits of (8.4), which come from the regional distance by (5.5).
-/


@[expose] public section

namespace GraphMinor.GM14

open Set Topology Graph GraphMinor GraphMinor.GM09 GraphMinor.Surface GraphMinor.GM11

universe u v w

variable {α : Type u} {β : Type v}

theorem start_mem_support {P : Graph α β} {a b : α} (W : GraphWalk P a b) : a ∈ W.support := by
  cases W <;> simp [GraphWalk.support]

theorem last_mem_support {P : Graph α β} {a b : α} (W : GraphWalk P a b) : b ∈ W.support := by
  induction W with
  | nil hv => simp [GraphWalk.support]
  | cons hlink rest ih => simp [GraphWalk.support, ih]

theorem walk_in_side {G P I O : Graph α β} (hP : P ≤ G) (hO : O ≤ G) (hI : I ≤ G)
    (hE : E(G) ⊆ E(I) ∪ E(O)) {Z : Set α} (hZ : V(I) ∩ V(O) ⊆ Z) {a b : α} (W : GraphWalk P a b)
    (ha : a ∈ V(I)) (hs : W.support.Nodup) (hoff : ∀ v ∈ W.support, v ∈ Z → v = b) :
    (∀ v ∈ W.support, v ∈ V(I)) ∧ ∀ e ∈ W.edges, e ∈ E(I) := by
  induction W with
  | nil hv =>
    refine ⟨?_, by simp [GraphWalk.edges]⟩
    intro v hv'
    simp only [GraphWalk.support, List.mem_singleton] at hv'
    exact hv' ▸ ha
  | @cons u x w e hlink rest ih =>
    simp only [GraphWalk.support, List.nodup_cons] at hs
    have hne : u ≠ w := fun h => hs.1 (h ▸ last_mem_support rest)
    have huZ : u ∉ Z := fun h => hne (hoff u (by simp [GraphWalk.support]) h)
    have hlG : G.IsLink e u x := hlink.mono hP
    have heI : e ∈ E(I) := by
      rcases hE hlG.edge_mem with h | h
      · exact h
      · exact absurd (hZ ⟨ha, (hlG.of_compatible (Compatible.of_le_le le_rfl hO) h).left_mem⟩) huZ
    have hxI : x ∈ V(I) := (hlG.of_compatible (Compatible.of_le_le le_rfl hI) heI).right_mem
    obtain ⟨h₁, h₂⟩ := ih hxI hs.2 fun v hv hvZ =>
      hoff v (by simp [GraphWalk.support, hv]) hvZ
    constructor
    · intro v hv
      simp only [GraphWalk.support, List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact ha
      · exact h₁ v hv
    · intro f hf
      simp only [GraphWalk.edges, List.mem_cons] at hf
      rcases hf with rfl | hf
      · exact heI
      · exact h₂ f hf

/-- See the module docstring. -/
theorem path_in_side {G P I O : Graph α β} (hO : O ≤ G) (hI : I ≤ G) (hE : E(G) ⊆ E(I) ∪ E(O))
    {Z : Set α} (hZ : V(I) ∩ V(O) ⊆ Z) {a b : α} (hP : IsGraphPathWithEnds G P a b)
    (ha : a ∈ V(I)) (hoff : V(P) ∩ Z ⊆ {b}) : P ≤ I := by
  obtain ⟨hle, W, hs, hV, hEP⟩ := hP
  obtain ⟨h₁, h₂⟩ := walk_in_side hle hO hI hE hZ W ha hs fun v hv hvZ =>
    hoff ⟨hV.superset hv, hvZ⟩
  exact le_of_subset_of_subset hle hI (fun v hv => h₁ v (hV.subset hv))
    fun e he => h₂ e (hEP.subset he)

theorem walk_no_loop {P : Graph α β} {a b : α} (W : GraphWalk P a b) (hs : W.support.Nodup) {e : β}
    (he : e ∈ W.edges) {z : α} (hz : P.IsLink e z z) : False := by
  induction W with
  | nil hv => simp [GraphWalk.edges] at he
  | @cons u x w f hlink rest ih =>
    simp only [GraphWalk.support, List.nodup_cons] at hs
    simp only [GraphWalk.edges, List.mem_cons] at he
    rcases he with rfl | he
    · rcases hlink.eq_and_eq_or_eq_and_eq hz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hs.1 (start_mem_support rest)
      · exact hs.1 (start_mem_support rest)
    · exact ih hs.2 he

/-- A path has no loop. -/
theorem IsGraphPathWithEnds.no_loop {G P : Graph α β} {a b : α} (hP : IsGraphPathWithEnds G P a b)
    {e : β} {z : α} (hz : P.IsLink e z z) : False := by
  obtain ⟨-, W, hs, -, hEP⟩ := hP
  exact walk_no_loop W hs (hEP.subset hz.edge_mem) hz

variable {S : Type w} [TopologicalSpace S] [T2Space S]

omit [T2Space S] in
theorem edge_subset_U {R : Drawing S} {e : Set S} (he : e ∈ R.E) : e ⊆ R.U := by
  rw [R.U_eq]
  exact subset_closure.trans (subset_union_right.trans' (subset_biUnion_of_mem
    (u := fun e => closure e) he))

omit [T2Space S] in
/-- The image of a subdrawing `R` under `η` has the same set of points as `R`. -/
theorem subgraphU_image {H R : Drawing S} (hR : R.IsSubdrawing H) {G A : Graph α β}
    (η : SpanEmbedding H G) (Y : GraphDrawing A S) {ν : α → S}
    (hν : ∀ v : V(A), (Y.iso.vertexEquiv v).1 = ν v.1) (hle : η.imageGraph ≤ A)
    (hη : ∀ v ∈ H.V, ν (η.vMap v) = v)
    (hηe : ∀ e ∈ H.E, graphDrawingEdgeSet Y (η.eMap e) = e) (hRG : R.toGraph ≤ H.toGraph) :
    graphDrawingSubgraphU Y (η.gmap.sub R.toGraph) = R.U := by
  have hV : ∀ v ∈ R.V, η.vMap v ∈ V(A) := fun v hv =>
    hle.vertexSet_mono (η.gmap.bijV.mapsTo (hR.1 hv))
  rw [R.U_eq]
  refine Subset.antisymm (union_subset (iUnion₂_subset ?_) (iUnion₂_subset ?_))
    (union_subset ?_ (iUnion₂_subset ?_))
  · rintro _ ⟨v, hv, rfl⟩
    rw [graphDrawingVertexSet_eq_singleton Y (hV v hv), hν ⟨_, hV v hv⟩, hη v (hR.1 hv)]
    exact singleton_subset_iff.mpr (Or.inl hv)
  · intro a ha
    rw [η.gmap.edgeSet_sub hRG] at ha
    obtain ⟨e, he, rfl⟩ := ha
    rw [hηe e (hR.2 he)]
    exact subset_biUnion_of_mem (u := fun e => closure e) he |>.trans subset_union_right
  · intro v hv
    refine Or.inl (mem_iUnion₂.mpr ⟨η.vMap v, mem_image_of_mem _ hv, ?_⟩)
    rw [graphDrawingVertexSet_eq_singleton Y (hV v hv), hν ⟨_, hV v hv⟩, hη v (hR.1 hv)]
    rfl
  · intro e he
    have h : η.eMap e ∈ E(η.gmap.sub R.toGraph) := by
      rw [η.gmap.edgeSet_sub hRG]
      exact mem_image_of_mem _ he
    refine Subset.trans ?_ (subset_union_right (s := _))
    refine subset_biUnion_of_mem (u := fun e => closure (graphDrawingEdgeSet Y e)) h |>.trans' ?_
    rw [show graphDrawingEdgeSet Y (η.eMap e) = e from hηe e (hR.2 he)]

omit [T2Space S] in
theorem mem_discBd_of_subset (hman : ∀ x : S, IsManifoldPoint x) {A D : Set S} (hA : IsClosedDisc A)
    (hAD : A ⊆ D) {x : S} (hx : x ∈ A) (hb : x ∈ discBd D) : x ∈ discBd A := by
  by_contra hn
  exact (discInt_mono hman hA hAD ⟨hx, hn⟩).2 hb

omit [T2Space S] in
/-- A disc whose boundary misses the boundary of a larger disc misses it altogether. -/
theorem subset_sdiff_discBd (hman : ∀ x : S, IsManifoldPoint x) {A Q : Set S}
    (hA : IsClosedDisc A) (hAQ : A ⊆ Q) (hb : discBd A ⊆ Q \ discBd Q) :
    A ⊆ Q \ discBd Q := by
  intro x hx
  by_cases h : x ∈ discBd A
  · exact hb h
  · exact discInt_mono hman hA hAQ ⟨hx, h⟩

variable [ConnectedSpace S]

omit [T2Space S] in
/-- See the module docstring. -/
theorem exists_nest_between (hS : IsClosedSurface S) (H : Drawing S) {C₁ C₂ : Drawing S}
    {E₁ E₂ : Set S} (hE₁ : IsClosedDisc E₁) (hE₂ : IsClosedDisc E₂)
    (hC₁ : C₁.IsCircuit ∧ C₁.IsSubdrawing H) (hC₂ : C₂.IsCircuit ∧ C₂.IsSubdrawing H)
    (hbd₁ : discBd E₁ = C₁.U) (hbd₂ : discBd E₂ = C₂.U) (hE₂E₁ : E₂ ⊆ E₁ \ C₁.U) {m : ℕ}
    (hd : m + 1 ≤ regionalDistance H C₂.U C₁.U) :
    ∃ (R : Fin (m + 2) → Drawing S) (A : Fin (m + 2) → Set S),
      (∀ i, (R i).IsCircuit ∧ (R i).IsSubdrawing H ∧ IsClosedDisc (A i) ∧ discBd (A i) = (R i).U ∧
        E₂ ⊆ A i ∧ A i ⊆ E₁) ∧
      (R 0 = C₂ ∧ A 0 = E₂) ∧ ∀ i j, i < j → A i ⊆ A j \ (R j).U := by
  classical
  have hman : ∀ x : S, IsManifoldPoint x := (IsClosedSurface.isSurface hS).2.2
  have hsb₁ : subBd E₁ = C₁.U := by
    rw [← hbd₁]
    exact IsClosedDisc.subBd_eq_discBd hS hE₁
  have hZ : C₂.U ⊆ E₁ \ subBd E₁ := by
    rw [hsb₁, ← hbd₂]
    exact (GraphMinor.Surface.discBd_subset E₂).trans hE₂E₁
  obtain ⟨φ⟩ := hE₂.isOArc_discBd
  have hconn : IsPreconnected C₂.U := by
    rw [← hbd₂]
    have := (isPreconnected_range (f := fun z : Circle => (φ z).1)
      (continuous_subtype_val.comp φ.continuous))
    rwa [show range (fun z : Circle => (φ z).1) = discBd E₂ by
      ext x
      constructor
      · rintro ⟨z, rfl⟩
        exact (φ z).2
      · intro hx
        exact ⟨φ.symm ⟨x, hx⟩, by simp⟩] at this
  have hne : C₂.U.Nonempty := by
    rw [← hbd₂]
    exact ⟨_, (φ 1).2⟩
  obtain ⟨CC, Λ, hprops, hnest⟩ := theorem_5_5_aux hS H hE₁ m hZ hne hconn (hsb₁ ▸ hd)
  let seq : ℕ → Drawing S × Set S := fun k =>
    if k = 0 then (C₂, E₂) else
      if h : k - 1 < m then (CC ⟨k - 1, h⟩, closure (Λ ⟨k - 1, h⟩)) else (C₁, E₁)
  have h0 : seq 0 = (C₂, E₂) := rfl
  have hmid : ∀ i : Fin m, seq (i.1 + 1) = (CC i, closure (Λ i)) := by
    intro i
    simp only [seq, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel,
      i.2, ↓reduceDIte]
  have hlast : seq (m + 1) = (C₁, E₁) := by
    simp [seq]
  have hE₂sub : E₂ ⊆ E₁ := hE₂E₁.trans sdiff_subset
  -- The facts on one circuit of the middle.
  have hmidfacts : ∀ i : Fin m, E₂ ⊆ closure (Λ i) ∧ closure (Λ i) ⊆ E₁ \ C₁.U := by
    intro i
    obtain ⟨-, -, -, -, hcl, hdisc, -, -, -, hZΛ⟩ := hprops i
    have hcl' : closure (Λ i) ⊆ E₁ \ C₁.U := hsb₁ ▸ hcl
    refine ⟨?_, hcl'⟩
    refine GraphMinor.GM16.closedDisc_subset_of_boundary_subset hE₁ hdisc hE₂
      (hcl'.trans sdiff_subset) hE₂sub ?_
    rw [hbd₂]
    exact hZΛ.trans subset_closure
  have hgood : ∀ k, k ≤ m + 1 → (seq k).1.IsCircuit ∧ (seq k).1.IsSubdrawing H ∧
      IsClosedDisc (seq k).2 ∧ discBd (seq k).2 = (seq k).1.U ∧ E₂ ⊆ (seq k).2 ∧ (seq k).2 ⊆ E₁
        := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [h0]
      exact ⟨hC₂.1, hC₂.2, hE₂, hbd₂, Subset.rfl, hE₂sub⟩
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      by_cases hj : j < m
      · rw [hmid ⟨j, hj⟩]
        obtain ⟨h₁, h₂, -, -, -, hdisc, -, hb, -, -⟩ := hprops ⟨j, hj⟩
        obtain ⟨h₃, h₄⟩ := hmidfacts ⟨j, hj⟩
        exact ⟨h₂, h₁, hdisc, (IsClosedDisc.subBd_eq_discBd hS hdisc).symm.trans hb, h₃,
          h₄.trans sdiff_subset⟩
      · have : j = m := by omega
        subst this
        rw [hlast]
        exact ⟨hC₁.1, hC₁.2, hE₁, hbd₁, hE₂sub, Subset.rfl⟩
  have hstep : ∀ k, k ≤ m → (seq k).2 ⊆ (seq (k + 1)).2 \ (seq (k + 1)).1.U := by
    intro k hk
    have hcase0 : ∀ i : Fin m, E₂ ⊆ closure (Λ i) \ (CC i).U := by
      intro i
      obtain ⟨-, -, -, -, -, hdisc, -, hb, hdiff, hZΛ⟩ := hprops i
      have hbq : discBd (closure (Λ i)) = (CC i).U := (IsClosedDisc.subBd_eq_discBd hS
        hdisc).symm.trans hb
      rw [← hbq]
      refine subset_sdiff_discBd hman hE₂ (hmidfacts i).1 ?_
      rw [hbq, hdiff, hbd₂]
      exact hZΛ
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · by_cases hm : 0 < m
      · rw [h0, hmid ⟨0, hm⟩]
        exact hcase0 ⟨0, hm⟩
      · have : m = 0 := by omega
        subst this
        rw [h0, hlast]
        exact hE₂E₁
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hj : j < m := by omega
      rw [hmid ⟨j, hj⟩]
      by_cases hj' : j + 1 < m
      · rw [hmid ⟨j + 1, hj'⟩]
        obtain ⟨-, -, -, -, -, -, -, -, hdiff, -⟩ := hprops ⟨j + 1, hj'⟩
        change closure (Λ ⟨j, hj⟩) ⊆ closure (Λ ⟨j + 1, hj'⟩) \ (CC ⟨j + 1, hj'⟩).U
        rw [hdiff]
        exact hnest ⟨j, hj⟩ ⟨j + 1, hj'⟩ (Nat.lt_succ_self j)
      · have : j + 1 = m := by omega
        subst this
        rw [hlast]
        exact (hmidfacts ⟨j, hj⟩).2
  have hchain : ∀ i j, i < j → j ≤ m + 1 → (seq i).2 ⊆ (seq j).2 \ (seq j).1.U := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => exact fun h => hstep i (by omega)
    | succ j hj ih =>
      intro h
      exact (ih (by omega)).trans (sdiff_subset.trans (hstep j (by omega)))
  refine ⟨fun i => (seq i.1).1, fun i => (seq i.1).2, fun i => hgood i.1 (by omega), ?_,
    fun i j hij => hchain i.1 j.1 hij (by omega)⟩
  exact ⟨congrArg Prod.fst h0, congrArg Prod.snd h0⟩

end GraphMinor.GM14
