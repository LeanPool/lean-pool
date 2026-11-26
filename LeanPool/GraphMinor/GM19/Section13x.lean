/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section13w

import LeanPool.GraphMinor.GM07.Bridge

/-!
# Graph Minors XIX, Section 13: the end of the proof of (13.6)

Steps (8) to (11) leave two arcs of `F` outside `Δ_v`, and steps (12) to (14) use them to bound `F`
from above and below. Here we put these together. First comes the set that ties each
arc away from the hub, in both forms of the sector. Then comes the count that gives the
contradiction, and (13.6) itself.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

omit [T2Space Shat] in
/-- If every vertex of an edge of a simple walk is an end of the walk, then this edge is the only
edge of the walk. -/
theorem GraphWalk.edges_eq_of_ends {G : Drawing Shat} {a b : Shat} (K : GraphWalk G.toGraph a b)
  (hs : K.IsSimple) {e : Set Shat} (he : e ∈ K.edges)
    (hV : ∀ x y, G.toGraph.IsLink e x y → (x = a ∨ x = b) ∧ (y = a ∨ y = b)) : ∀ e' ∈ K.edges, e'
      = e := by
  obtain ⟨x, y, hl, L, M, rfl⟩ := GraphWalk.exists_split_edge K he
  obtain ⟨hL, hc⟩ := isSimple_of_append hs
  obtain ⟨hxM, hM⟩ := List.nodup_cons.mp hc
  obtain ⟨h₁, h₂⟩ := hV x y hl
  have hxb : x ≠ b := fun h' ↦ hxM (h' ▸ M.end_mem_support)
  have hxa := h₁.resolve_right hxb
  subst hxa
  have hya : y ≠ x := fun h' ↦ hxM (h' ▸ M.start_mem_support)
  have hyb := h₂.resolve_left hya
  subst hyb
  intro e' he'
  rw [GraphWalk.edges_append, GraphWalk.edges_cons, GraphWalk.edges_of_closed L hL,
    GraphWalk.edges_of_closed M hM] at he'
  simpa using he'

/-- The image of a line is connected. -/
theorem IsLineWithEnds.isPreconnected' {T : Type} [TopologicalSpace T] {L : Set T} {u v : T}
  (h : IsLineWithEnds L u v) : IsPreconnected L :=
  GraphMinor.Surface.IsLineWithEnds.isPreconnected h

namespace TangleDatum

variable {D : TangleDatum cap χ} {W : Set Shat} {H : Drawing Shat} {ρ : ℕ} {r : Shat} {Δv : Set
  Shat} {Dv F : Drawing Shat}
  {ord' : ℕ} {𝒯' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {Δ₀ Δ : Set Shat} {C :
    Drawing Shat} {h : Shat}
  {v₁ v₂ c₁ c₂ h₁ h₂ : Shat} {f₁ f₂ : Set Shat} {A₁ : GraphWalk D.rad.G.toGraph v₁ c₁} {A₂ :
    GraphWalk D.rad.G.toGraph v₂ c₂} {T₁ : GraphWalk D.rad.G.toGraph c₁ h₁}
  {T₂ : GraphWalk D.rad.G.toGraph c₂ h₂}

omit [T2Space S] in
/-- A point of a walk in the drawing of the walk that is a vertex of `Γ*` is on the walk. -/
theorem support_of_mem_U {a b y : Shat} (L : GraphWalk D.rad.G.toGraph a b) (hy : y ∈
  (walkDrawing D.rad.G L).U) (hV : y ∈ D.rad.G.V) : y ∈ L.support := by
  rcases (mem_walkDrawing_U _ _).mp hy with h' | ⟨e, he, hye⟩
  · exact h'
  · obtain ⟨x, z, -, hx, hz, hcap⟩ := D.exists_ends_of_mem_edges L he
    have hm : y ∈ closure e ∩ D.rad.G.V := ⟨hye, hV⟩
    rw [hcap] at hm
    rcases hm with rfl | rfl
    · exact hx
    · exact hz

omit [T2Space S] in
/-- Two walks meet only at common vertices and in common edges. -/
theorem walkU_inter {a b a' b' y : Shat} (L : GraphWalk D.rad.G.toGraph a b)
  (M : GraphWalk D.rad.G.toGraph a' b') (h₁' : y ∈ (walkDrawing D.rad.G L).U)
    (h₂' : y ∈ (walkDrawing D.rad.G M).U) : (y ∈ L.support ∧ y ∈ M.support) ∨ ∃ e, e ∈ L.edges
      ∧ e ∈ M.edges := by
  by_cases hV : y ∈ D.rad.G.V
  · exact .inl ⟨support_of_mem_U L h₁' hV, support_of_mem_U M h₂' hV⟩
  · right
    rcases (mem_walkDrawing_U _ _).mp h₂' with h' | ⟨e, he, hye⟩
    · exact absurd (M.mem_vertexSet_of_mem_support h') hV
    · have heG : e ∈ D.rad.G.E := TieBreaker.mem_edges_E M he
      have hye' : y ∈ e := (closure_edge_subset heG hye).resolve_right hV
      refine ⟨e, ?_, he⟩
      by_contra hn
      exact disjoint_left.mp (edge_disjoint_U (walkDrawing_isSubdrawing _ _) heG
        (by rwa [walkDrawing_E])) hye' h₁'

omit [T2Space S] in
/-- A walk with no vertex on a subdrawing is disjoint from it. -/
theorem walkU_disjoint {a b : Shat} {F : Drawing Shat} (hFs : F.IsSubdrawing D.rad.G)
  (T : GraphWalk D.rad.G.toGraph a b) (hT : ∀ x ∈ T.support, x ∉ F.V) :
    Disjoint (walkDrawing D.rad.G T).U F.U := disjoint_left.mpr fun y hy hyF ↦ by
  by_cases hV : y ∈ D.rad.G.V
  · exact hT y (support_of_mem_U T hy hV) (mem_V_of_mem_U hFs hyF hV)
  · rcases (mem_walkDrawing_U _ _).mp hy with h' | ⟨e, he, hye⟩
    · exact hV (T.mem_vertexSet_of_mem_support h')
    · have heG : e ∈ D.rad.G.E := TieBreaker.mem_edges_E T he
      have hye' : y ∈ e := (closure_edge_subset heG hye).resolve_right hV
      have heF : e ∈ F.E := by
        by_contra hn
        exact disjoint_left.mp (edge_disjoint_U hFs heG hn) hye' hyF
      obtain ⟨x, z, -, hx, -, hcap⟩ := D.exists_ends_of_mem_edges T he
      have hm : x ∈ closure e ∩ D.rad.G.V := by rw [hcap]; exact .inl rfl
      exact hT x hx (mem_V_of_mem_U hFs (F.closure_subset_U heF hm.1) hm.2)

theorem IsArcOn.U_subset_F {G Dv F : Drawing Shat} {a b : Shat} {P : GraphWalk G.toGraph a b}
  (hP : IsArcOn G Dv F P) (hF : F.IsSubdrawing G) : (walkDrawing G P).U ⊆ F.U := fun y hy ↦ by
  rcases (mem_walkDrawing_U _ _).mp hy with h' | ⟨e, he, hye⟩
  · exact F.V_subset_U (hP.mem_F hF y h')
  · exact F.closure_subset_U (hP.inF e he) hye

/-- The walk drawing of a simple walk is connected. -/
theorem walkU_isPreconnected {G : Drawing Shat} {a b : Shat} (T : GraphWalk G.toGraph a b)
  (hs : T.IsSimple) : IsPreconnected (walkDrawing G T).U := by
  by_cases hab : a = b
  · subst hab
    have hE := GraphWalk.edges_of_closed T hs
    have hU : (walkDrawing G T).U = {a} := by
      ext y
      rw [mem_singleton_iff, mem_walkDrawing_U]
      constructor
      · rintro (h' | ⟨e, he, -⟩)
        · by_contra hne
          obtain ⟨L, M, hLM⟩ := T.exists_append_of_mem h'
          obtain ⟨e, he, -⟩ := GraphWalk.exists_edge_at_end L (Ne.symm hne)
          rw [hLM, GraphWalk.edges_append] at hE
          simp only [List.append_eq_nil_iff] at hE
          simp [hE.1] at he
        · simp [hE] at he
      · rintro rfl
        exact .inl T.start_mem_support
    rw [hU]
    exact isPreconnected_singleton
  · exact IsLineWithEnds.isPreconnected' (isLine_of_isPathBetween (walkDrawing_isPathBetween G hs)
      hab)

namespace IsFar

variable {u h' : Shat} {A₁' : GraphWalk D.rad.G.toGraph v₁ u} {A₂' : GraphWalk D.rad.G.toGraph v₂
  u} {T : GraphWalk D.rad.G.toGraph u h'}

/-- In the first form of the sector, the rest of the two spokes is an anchor, as soon as `F` has no
vertex on it. -/
theorem fan_anchor (hf : D.IsFar W H ρ r Δv Dv ord' 𝒯' F Δ₀ C Δ h) (s : D.IsShape W H r Δv Dv F f₁
  f₂ A₁' A₂' T T) (hfan : D.IsFan W H ρ r f₁ f₂ A₁' A₂' T)
    (hTF : ∀ x ∈ T.support, x ∉ F.V) : D.IsAnchor H ρ Δv Dv F h f₁ f₂ A₁' A₂'
      (walkDrawing D.rad.G T).U := by
  have hT' := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hx := hf.enc
  have hW := hx.wheel
  have hFs := hx.isInsOf_F.1.1
  have hbv := hx.sector.Dv_U.symm
  have hsub₁ : (walkDrawing D.rad.G T).U ⊆ (walkDrawing D.rad.G (A₁'.append T)).U := walkU_subset
    (fun x hx' ↦ (GraphWalk.mem_support_append _ _).mpr (.inr hx'))
    (fun e he ↦ by rw [GraphWalk.edges_append]; exact List.mem_append_right _ he)
  have hsub₂ : (walkDrawing D.rad.G T).U ⊆ (walkDrawing D.rad.G (A₂'.append T)).U := walkU_subset
    (fun x hx' ↦ (GraphWalk.mem_support_append _ _).mpr (.inr hx'))
    (fun e he ↦ by rw [GraphWalk.edges_append]; exact List.mem_append_right _ he)
  have hcl : IsClosed (discBd W) := by
    rw [← IsClosedDisc.frontier_eq_discBd hT' hW.is_disc]
    exact isClosed_frontier
  have hoffB : Disjoint (walkDrawing D.rad.G T).U (discBd W) := disjoint_left.mpr fun y hy hb ↦
    s.ne ((IsSpokeWalk.meet_bd hW hx.hbdS hx.hin s.spoke₁ (hsub₁ hy) hb).symm.trans
      (IsSpokeWalk.meet_bd hW hx.hbdS hx.hin s.spoke₂ (hsub₂ hy) hb))
  have hmeetA : ∀ {v : Shat} {A : GraphWalk D.rad.G.toGraph v u}, (∀ e ∈ A.edges, e ∉ T.edges) →
    (A.append T).IsSimple → ∀ y ∈ (walkDrawing D.rad.G T).U, y ∈ (walkDrawing D.rad.G A).U → y = u
      := by
    intro v A hd hsA y hy hy'
    rcases walkU_inter A T hy' hy with ⟨h₃, h₄⟩ | ⟨e, h₃, h₄⟩
    · exact Splits.append_meet hsA h₃ h₄
    · exact absurd h₄ (hd e h₃)
  have hu : u ∈ (walkDrawing D.rad.G T).U := (mem_walkDrawing_U _ _).mpr (.inl T.start_mem_support)
  refine ⟨walkU_isPreconnected T (isSimple_of_append s.spoke₁.1).2, ⟨u, hu, Surface.discBd_subset _
    (hbv ▸ Dv.V_subset_U (s.mem₁ u A₁'.end_mem_support))⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hend : h' ∈ (walkDrawing D.rad.G T).U := (mem_walkDrawing_U _ _).mpr
      (.inl T.end_mem_support)
    rcases hf.hub with ⟨hV, -⟩ | ⟨h₁', h₂', h₃'⟩
    · have hm := s.spoke₁.2.h_mem
      rw [hV] at hm
      exact ⟨h', hend, .inl hm⟩
    · exact ⟨h', hend, .inr ⟨H.V_subset_U s.spoke₁.2.h_mem, h₁', h₂', h₃'⟩⟩
  · intro a b Q hQ
    exact (walkU_disjoint hFs T hTF).mono_right (IsArcOn.U_subset_F hQ hFs)
  · exact hoffB.mono_right (closure_minimal s.bd₁ hcl)
  · exact hoffB.mono_right (closure_minimal s.bd₂ hcl)
  · exact hmeetA hfan.edges_disjoint_T s.spoke₁.1
  · exact hmeetA hfan.swap.edges_disjoint_T s.spoke₂.1

omit [T2Space S] in
/-- In the second form of the sector, a point of an edge of the path of `H` on `D_v` is an anchor.
-/
theorem path_anchor (hf : D.IsFar W H ρ r Δv Dv ord' 𝒯' F Δ₀ C Δ h) (s : D.IsShape W H r Δv Dv F f₁
  f₂ A₁ A₂ T₁ T₂) {p q : Shat} {P : Drawing Shat} (hpq : p ≠ q) (hP : Drawing.IsPathOf P H p q)
    (hsub : P.U ⊆ Dv.U) : ∃ Y,
      D.IsAnchor H ρ Δv Dv F h f₁ f₂ A₁ A₂ Y := by
  have hT' := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hx := hf.enc
  have hW := hx.wheel
  have hbv := hx.sector.Dv_U.symm
  obtain ⟨K, -, -, hKE⟩ := hP.exists_simple_walk
  obtain ⟨g, hgK, -⟩ := GraphWalk.exists_edge_at_end K hpq
  have hgP := (hKE g).mpr hgK
  have hgH := hP.1.2 hgP
  have hgG := hW.H_sub.2 hgH
  obtain ⟨y, hy⟩ := hgG.1
  have hyV : y ∉ D.rad.G.V := (hgG.2.1 hy).2
  have hyP : y ∈ P.U := P.closure_subset_U hgP (subset_closure hy)
  have hyH : y ∈ H.U := H.closure_subset_U hgH (subset_closure hy)
  have hgD : g ∈ Dv.E := by
    by_contra hn
    exact disjoint_left.mp (edge_disjoint_U hx.sector.Dv_circuit.1 hgG hn) hy (hsub hyP)
  have hyW : y ∉ discBd W := fun h' ↦ (hW.H_in_int hyH).2 h'
  have hcl : IsClosed (discBd W) := by
    rw [← IsClosedDisc.frontier_eq_discBd hT' hW.is_disc]
    exact isClosed_frontier
  have hhub : ∃ z ∈ ({y} : Set Shat), z = h ∨ (z ∈ H.U ∧ IsEnclave D.tb D.ord D.𝒯 H ∧ H.E.ncard
    ≤ 4 * ρ + 4 ∧ h ∈ discInt (D.ins H)) := by
    rcases hf.hub with ⟨hV, -⟩ | ⟨h₁', h₂', h₃'⟩
    · exfalso
      have hp : p ∈ H.V := K.mem_vertexSet_of_mem_support K.start_mem_support
      have hq : q ∈ H.V := K.mem_vertexSet_of_mem_support K.end_mem_support
      rw [hV] at hp hq
      exact hpq (hp.trans hq.symm)
    · exact ⟨y, rfl, .inr ⟨hyH, h₁', h₂', h₃'⟩⟩
  refine ⟨{y}, isPreconnected_singleton, ⟨y, rfl, Surface.discBd_subset _ (hbv ▸ hsub hyP)⟩,
    hhub, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b Q hQ
    refine disjoint_singleton_left.mpr fun hyQ ↦ ?_
    rcases (mem_walkDrawing_U _ _).mp hyQ with h' | ⟨e, he, hye⟩
    · exact hyV (Q.mem_vertexSet_of_mem_support h')
    · have heG : e ∈ D.rad.G.E := TieBreaker.mem_edges_E Q he
      have hye' : y ∈ e := (closure_edge_subset heG hye).resolve_right hyV
      refine hQ.off e he ?_
      by_contra hn
      exact disjoint_left.mp (edge_disjoint_U hx.sector.Dv_circuit.1 heG hn) hye' (hsub hyP)
  · exact disjoint_singleton_left.mpr fun h' ↦ hyW (closure_minimal s.bd₁ hcl h')
  · exact disjoint_singleton_left.mpr fun h' ↦ hyW (closure_minimal s.bd₂ hcl h')
  · rintro z rfl hz
    have hz' : z ∈ (walkDrawing D.rad.G (A₁.append T₁)).U := walkU_subset (fun x hx' ↦
      (GraphWalk.mem_support_append _ _).mpr (.inl hx'))
      (fun e he ↦ by rw [GraphWalk.edges_append]; exact List.mem_append_left _ he) hz
    have := IsSpokeWalk.U_inter_hub hW s.spoke₁ hz' hyH
    exact absurd (this ▸ (A₁.append T₁).mem_vertexSet_of_mem_support (A₁.append
      T₁).end_mem_support) hyV
  · rintro z rfl hz
    have hz' : z ∈ (walkDrawing D.rad.G (A₂.append T₂)).U := walkU_subset (fun x hx' ↦
      (GraphWalk.mem_support_append _ _).mpr (.inl hx'))
      (fun e he ↦ by rw [GraphWalk.edges_append]; exact List.mem_append_left _ he) hz
    have := IsSpokeWalk.U_inter_hub hW s.spoke₂ hz' hyH
    exact absurd (this ▸ (A₂.append T₂).mem_vertexSet_of_mem_support (A₂.append
      T₂).end_mem_support) hyV

/-- The end of the proof of (13.6) when the second arc goes across: `Q₀` goes from `A₁` to `A₂`.
Then `F` has a third arc `F₂`, which is a chord of `D_v`, and counting gives the
contradiction. -/
theorem false_of_cross (hf : D.IsFar W H ρ r Δv Dv ord' 𝒯' F Δ₀ C Δ h)
  (s : D.IsShape W H r Δv Dv F f₁ f₂ A₁ A₂ T₁ T₂) {Y : Set Shat} (ha : D.IsAnchor H ρ Δv Dv F h f₁
    f₂ A₁ A₂ Y)
    (hten : ∀ x ∈ A₁.support, x ∈ A₂.support → x ∉ F.V) {b₁ a₀ b₀ : Shat} {Q₁ : GraphWalk
      D.rad.G.toGraph r b₁} {Q₀ : GraphWalk D.rad.G.toGraph a₀ b₀} (h₁' : IsArcOn D.rad.G Dv F Q₁)
    (h₀ : IsArcOn D.rad.G Dv F Q₀) (o₁ : ∀ e ∈ Q₁.edges, Disjoint e Δv)
      (o₀ : ∀ e ∈ Q₀.edges, Disjoint e Δv) (hd : ∀ e ∈ Q₀.edges, e ∉ Q₁.edges)
        (hb₁ : b₁ ∈ A₁.support) (ha₀ : a₀ ∈ A₁.support)
    (hb₀ : b₀ ∈ A₂.support) (hnp : ¬ PushesInto (Δ₀ \ {h}) (Δv \ {h})
      (walkDrawing D.rad.G Q₁).U r b₁) : False := by
  classical
  have : ConnectedSpace Shat := cap.connected
  have hx := hf.enc
  have hW := hx.wheel
  have hDv := hx.sector.Dv_circuit
  have hΔv := hx.sector.is_disc
  have hbv := hx.sector.Dv_U.symm
  have hrep := hx.hrep
  have hρ := hW.pos_ρ
  have hr := hf.toIsRound
  have hcC := hr.C_card
  obtain ⟨X₁, Z₁, hA₁⟩ := A₁.exists_append_of_mem hb₁
  obtain ⟨b₂, F₂, hb₂, hF₂s, hF₂E, hF₂A₂, hF₂A₁, ⟨e', he', hin'⟩, hcov⟩
    := hf.exists_third s hten h₁' h₀ o₁ o₀ hd hb₁ ha₀ hb₀
  have hC := hf.outer_circuit s ha h₁' o₁ hA₁ hnp
  have hins : IsInsOf D.rad D.ord D.𝒯 C Δ := by
    have h' := D.ins_spec hf.circuit (by have h₆ : 6 * ρ + 14 ≤ D.rep := hrep; omega)
    rwa [hr.ins_C] at h'
  have hNC : F.E.ncard ≤ C.E.ncard := hx.card_le_of_cover hins fun y _ hy ↦ hf.F_sub
    (discInt_subset _ hy)
  have hCle : C.E.ncard ≤ Q₁.length + (X₁.length + 1) := by
    have h' := ncard_le_length_of_edges (P := C) (Q₁.append (GraphWalk.cons s.link₁ X₁).reverse)
      (fun e he ↦ by
      rw [GraphWalk.edges_append, List.mem_append, GraphWalk.edges_reverse, List.mem_reverse]
      exact (hC e).mp he)
    rw [GraphWalk.length_append, GraphWalk.length_reverse] at h'
    exact h'
  have hp₁ : X₁.length + 1 ≤ Q₁.length := IsShape.parity_bound hf s Q₁ hA₁
  have hXρ : X₁.length ≤ ρ := by
    have h' := (hW.spoke_length s.spoke₁).1
    rw [GraphWalk.length_append, hA₁, GraphWalk.length_append] at h'
    omega
  have hf₀ : 1 ≤ Q₀.length := by
    obtain ⟨e, he, -⟩ := GraphWalk.exists_edge_at_start Q₀ h₀.ne
    have h' := List.length_pos_of_mem he
    rw [edges_length] at h'
    exact h'
  have hcount : Q₀.length + Q₁.length + F₂.length ≤ F.E.ncard := by
    have hn : (Q₀.edges ++ Q₁.edges ++ F₂.edges).Nodup := by
      refine List.Nodup.append (List.Nodup.append h₀.simple.edges_nodup h₁'.simple.edges_nodup fun
        e h₃ h₄ ↦ hd e h₃ h₄) hF₂s.edges_nodup fun e h₃ h₄ ↦ ?_
      rcases List.mem_append.mp h₃ with h₃ | h₃
      · exact (hF₂E e h₄).2.2 h₃
      · exact (hF₂E e h₄).2.1 h₃
    have h' := length_le_of_nodup F hn fun e he ↦ by
      rcases List.mem_append.mp he with he | he
      · rcases List.mem_append.mp he with he | he
        · exact h₀.inF e he
        · exact h₁'.inF e he
      · exact (hF₂E e he).1
    rw [List.length_append, List.length_append, edges_length, edges_length, edges_length] at h'
    exact h'
  have hrA₂ : r ∉ A₂.support := s.swap.r_notMem₁ hf
  by_cases hmid : ∃ x ∈ F₂.support, x ∈ Dv.V ∧ x ≠ r ∧ x ≠ b₂
  · -- A vertex of `D_v` inside `F₂` is on the hub, so `F₂` is too long.
    obtain ⟨x, hxF, hxD, hxr, hxb⟩ := hmid
    have hxH := s.rest x hxD hxr (hF₂A₁ x hxF) fun h' ↦ hxb (hF₂A₂ x hxF h')
    obtain ⟨L, M, hLM⟩ := F₂.exists_append_of_mem hxF
    have hL := IsWheelHubOfRadius.walk_from_rstar hW hx.hbdS hx.hin hx.sector.rstar_mem hxH L
    have hM : 1 ≤ M.length := by
      obtain ⟨e, he, -⟩ := GraphWalk.exists_edge_at_start M hxb
      have h' := List.length_pos_of_mem he
      rw [edges_length] at h'
      exact h'
    have hl : F₂.length = L.length + M.length := by rw [hLM, GraphWalk.length_append]
    omega
  have hinner : ∀ x ∈ F₂.support, x ∈ Dv.V → x = r ∨ x = b₂ := fun x hxF hxD ↦ by
    by_contra hn
    push Not at hn
    exact hmid ⟨x, hxF, hxD, hn.1, hn.2⟩
  have hoff : ∀ e ∈ F₂.edges, e ∉ Dv.E := fun e he heD ↦ by
    have h₃ := GraphWalk.edges_eq_of_ends F₂ hF₂s he (fun x y hl ↦ by
      obtain ⟨h₄, h₅⟩ := Drawing.IsLink.mem_V_of_sub hDv.1 hl heD
      obtain ⟨h₆, h₇⟩ := D.ends_mem_support F₂ he hl.2.2.2
      exact ⟨hinner x h₆ h₄, hinner y h₇ h₅⟩)
    obtain ⟨p, hp⟩ := (hDv.1.2 heD).1
    have heq := h₃ e' he'
    exact (hin' (heq ▸ hp)).2 (hbv ▸ Dv.closure_subset_U heD (subset_closure hp))
  have harc : IsArcOn D.rad.G Dv F F₂ := ⟨fun h' ↦ hrA₂ (h' ▸ hb₂), hF₂s, h₁'.left, s.mem₂ _ hb₂,
    hinner, hoff, fun e he ↦ (hF₂E e he).1⟩
  have hin : ∀ e ∈ F₂.edges, e ⊆ discInt Δv := by
    refine (IsArcOn.side (D := D) harc hDv.1 hΔv hbv).resolve_right fun h₃ ↦ ?_
    obtain ⟨p, hp⟩ := (TieBreaker.mem_edges_E F₂ he').1
    exact disjoint_left.mp (h₃ e' he') hp (discInt_subset _ (hin' hp))
  obtain ⟨X₂, Z₂, hA₂⟩ := A₂.exists_append_of_mem hb₂
  have hb := hf.chord_bound s harc hin hA₁ hA₂ hC (fun e he ↦ h₁'.inF e he) fun e he ↦ by
    rcases hcov e he with h₃ | h₃ | h₃ | h₃
    · exact .inl h₃
    · exact .inr (.inl (o₁ e h₃))
    · exact .inr (.inl (o₀ e h₃))
    · exact .inr (.inr h₃)
  have hp₂ : X₂.length + 1 ≤ F₂.length := IsShape.parity_bound hf s.swap F₂ hA₂
  omega

/-- The rest of the proof of (13.6): one arc `Q` ends at `r*`, and the other arc is one of the
remaining possibilities. -/
theorem false_of_rstar (hf : D.IsFar W H ρ r Δv Dv ord' 𝒯' F Δ₀ C Δ h)
  (s : D.IsShape W H r Δv Dv F f₁ f₂ A₁ A₂ T₁ T₂) {Y : Set Shat} (ha : D.IsAnchor H ρ Δv Dv F h f₁
    f₂ A₁ A₂ Y)
    (hten : ∀ x ∈ A₁.support, x ∈ A₂.support → x ∉ F.V) {b a' b' : Shat} {Q : GraphWalk
      D.rad.G.toGraph r b} {Q' : GraphWalk D.rad.G.toGraph a' b'} (hQ : IsArcOn D.rad.G Dv F Q)
    (hQ' : IsArcOn D.rad.G Dv F Q') (o : ∀ e ∈ Q.edges, Disjoint e Δv)
      (o' : ∀ e ∈ Q'.edges, Disjoint e Δv) (hd : ∀ e ∈ Q'.edges, e ∉ Q.edges) (hb : b ∈ A₁.support)
    (hnp : ¬ PushesInto (Δ₀ \ {h}) (Δv \ {h}) (walkDrawing D.rad.G Q).U r b) (hnp' : ¬ PushesInto
      (Δ₀ \ {h}) (Δv \ {h}) (walkDrawing D.rad.G Q').U a' b')
    (n : (a' = r ∧ b' ∈ A₁.support) ∨ (a' = r ∧ b' ∈ A₂.support) ∨ (a' ∈ A₁.support
      ∧ b' ∈ A₂.support) ∨ (a' ∈ A₂.support ∧ b' ∈ A₁.support)) : False := by
  have hx := hf.enc
  have hFs := hx.isInsOf_F.1.1
  rcases n with ⟨rfl, hb'⟩ | ⟨rfl, hb'⟩ | ⟨h₃, h₄⟩ | ⟨h₃, h₄⟩
  · -- Two arcs from `r*` to `A₁` would close up with `A₁`.
    obtain ⟨Sg, -, hSg, -⟩ := s.exists_seg hx.isEnclave hb hb' (hQ.mem_F hFs _ Q.end_mem_support)
      (hQ'.mem_F hFs _ Q'.end_mem_support)
    have hJ : ∀ e, e ∈ (Sg.append Q'.reverse).edges ↔ e ∈ Sg.edges ∨ e ∈ Q'.edges := fun e ↦ by
      rw [GraphWalk.edges_append, List.mem_append, GraphWalk.edges_reverse, List.mem_reverse]
    refine hf.closing (P := Q) (J := Sg.append Q'.reverse) hQ.ne hQ.simple hQ.inF (fun e he ↦ ?_)
      (fun e he ↦ ?_) fun e he ↦ ?_
    · rcases (hJ e).mp he with h' | h'
      · exact (hSg e h').2
      · exact hQ'.inF e h'
    · rcases (hJ e).mp he with h' | h'
      · exact fun h₃ ↦ hQ.off e h₃ (s.edge₁ e (hSg e h').1)
      · exact hd e h'
    · rcases he with he | he
      · exact .inr (o e he)
      · rcases (hJ e).mp he with h' | h'
        · exact .inl (s.edge₁ e (hSg e h').1)
        · exact .inr (o' e h')
  · -- Step (12): two arcs from `r*` to different spokes cannot both be part of `C`.
    obtain ⟨X, Z, hA⟩ := A₁.exists_append_of_mem hb
    obtain ⟨X', Z', hA'⟩ := A₂.exists_append_of_mem hb'
    have hC₁ := hf.outer_circuit s ha hQ o hA hnp
    have hC₂ := hf.outer_circuit s.swap ha.swap hQ' o' hA' hnp'
    obtain ⟨e, he, -⟩ := GraphWalk.exists_edge_at_start Q' hQ'.ne
    rcases (hC₁ e).mp ((hC₂ e).mpr (.inl he)) with h' | h'
    · exact hd e he h'
    · rw [GraphWalk.edges_cons, List.mem_cons] at h'
      rcases h' with rfl | h'
      · exact hQ'.off _ he s.f₁_mem
      · exact hQ'.off e he (s.edge₁ e (by
          rw [hA, GraphWalk.edges_append]
          exact List.mem_append_left _ h'))
  · exact hf.false_of_cross s ha hten hQ hQ' o o' hd hb h₃ h₄ hnp
  · refine hf.false_of_cross s ha hten hQ (IsArcOn.reverse hQ') o (fun e he ↦ o' e ?_)
      (fun e he ↦ hd e ?_) hb h₄ h₃ hnp
    · rwa [GraphWalk.edges_reverse, List.mem_reverse] at he
    · rwa [GraphWalk.edges_reverse, List.mem_reverse] at he

/-- The two arcs of step (8), brought to normal form. -/
theorem exists_normal_arcs (hf : D.IsFar W H ρ r Δv Dv ord' 𝒯' F Δ₀ C Δ h)
  (s : D.IsShape W H r Δv Dv F f₁ f₂ A₁ A₂ T₁ T₂) :
    ∃ (a₀ b₀ a₁ b₁ : Shat) (Q₀ : GraphWalk D.rad.G.toGraph a₀ b₀) (Q₁ : GraphWalk D.rad.G.toGraph
      a₁ b₁), IsArcOn D.rad.G Dv F Q₀ ∧ IsArcOn D.rad.G Dv F Q₁ ∧
      (∀ e ∈ Q₀.edges, Disjoint e Δv) ∧ (∀ e ∈ Q₁.edges, Disjoint e Δv) ∧
        (∀ e ∈ Q₁.edges, e ∉ Q₀.edges) ∧
      ((a₀ = r ∧ (b₀ ∈ A₁.support ∨ b₀ ∈ A₂.support)) ∨ (a₀ ∈ A₁.support ∧ b₀ ∈ A₂.support)) ∧ ((a₁
        = r ∧ (b₁ ∈ A₁.support ∨ b₁ ∈ A₂.support)) ∨ (a₁ ∈ A₁.support ∧ b₁ ∈ A₂.support)) ∧
      ¬ PushesInto (Δ₀ \ {h}) (Δv \ {h}) (walkDrawing D.rad.G Q₀).U a₀ b₀ ∧ ¬ PushesInto (Δ₀ \ {h})
        (Δv \ {h}) (walkDrawing D.rad.G Q₁).U a₁ b₁ := by
  have : ConnectedSpace Shat := cap.connected
  have hx := hf.enc
  have hFi := hx.isInsOf_F
  have hFc := hFi.1
  have hDv := hx.sector.Dv_circuit
  have hΔv := hx.sector.is_disc
  have hbv := hx.sector.Dv_U.symm
  have hhF : h ∉ F.U := fun hm ↦ hf.notMem_ins_F (Surface.discBd_subset _ (hFi.2.2.2.1 ▸ hm))
  obtain ⟨a₀, b₀, a₁, b₁, P₀, P₁, hP₀, hP₁, np₀, np₁, hne⟩ := exists_two_arcs (D
    := D) hDv hFc hf.circuit hf.amb.disc hf.disc hf.sub hf.bd hf.mem_Δ hf.not_C hFi.2.2.1
      hf.amb.ins_F
    hFi.2.2.2.1 hf.notMem_ins_F hΔv (hf.v_sub.trans hf.sub) hbv hf.mem_Dv_of_mem hf.edges
  have outer : ∀ {a b : Shat} {P : GraphWalk D.rad.G.toGraph a b}, IsArcOn D.rad.G Dv F P
    → ¬ PushesInto (Δ₀ \ {h}) (Δv \ {h}) (walkDrawing D.rad.G P).U a b
      → ∀ e ∈ P.edges, Disjoint e Δv := by
    intro a b P hP hn
    refine (IsArcOn.side (D := D) hP hDv.1 hΔv hbv).resolve_left fun hin ↦ hn
      (PushesInto.of_subset fun y hy ↦ ?_)
    refine ⟨?_, fun h' ↦ hhF (h' ▸ IsArcOn.U_subset_F hP hFc.1 hy)⟩
    have hc : ∃ e ∈ P.edges, y ∈ closure e := by
      rcases (mem_walkDrawing_U _ _).mp hy with h' | h'
      · exact GraphWalk.exists_edge_of_support P hP.ne h'
      · exact h'
    obtain ⟨e, he, hye⟩ := hc
    rw [← closure_discInt hΔv]
    exact closure_mono (hin e he) hye
  have hd₀ := IsArcOn.edges_disjoint hFc hP₀ hP₁ hne
  have ho₀ := outer hP₀ np₀
  have ho₁ := outer hP₁ np₁
  obtain ⟨a₀', b₀', Q₀, hQ₀, hE₀, hS₀, hk₀, n₀⟩ := hf.normal_form s hP₀ ho₀
  obtain ⟨a₁', b₁', Q₁, hQ₁, hE₁, hS₁, hk₁, n₁⟩ := hf.normal_form s hP₁ ho₁
  have hU : ∀ {a b a' b' : Shat} {P : GraphWalk D.rad.G.toGraph a b} {Q : GraphWalk D.rad.G.toGraph
    a' b'}, (∀ e, e ∈ Q.edges ↔ e ∈ P.edges) → (∀ x, x ∈ Q.support ↔ x ∈ P.support) →
      (walkDrawing D.rad.G Q).U = (walkDrawing D.rad.G P).U := fun hE hS ↦ Subset.antisymm
        (walkU_subset (fun x ↦ (hS x).mp) fun e ↦ (hE e).mp) (walkU_subset (fun x ↦
          (hS x).mpr) fun e ↦ (hE e).mpr)
  refine ⟨a₀', b₀', a₁', b₁', Q₀, Q₁, hQ₀, hQ₁, fun e he ↦ ho₀ e ((hE₀ e).mp he), fun e he ↦ ho₁ e
    ((hE₁ e).mp he), fun e he he' ↦ hd₀ e ((hE₁ e).mp he) ((hE₀ e).mp he'), n₀, n₁, ?_, ?_⟩
  · rw [hU hE₀ hS₀]
    exact hk₀ _ np₀
  · rw [hU hE₁ hS₁]
    exact hk₁ _ np₁

/-- One of the two arcs ends at `r*`, by step (9), and then `false_of_rstar` applies. -/
theorem false_of_normal (hf : D.IsFar W H ρ r Δv Dv ord' 𝒯' F Δ₀ C Δ h)
  (s : D.IsShape W H r Δv Dv F f₁ f₂ A₁ A₂ T₁ T₂) {Y : Set Shat} (ha : D.IsAnchor H ρ Δv Dv F h f₁
    f₂ A₁ A₂ Y)
    (hten : ∀ x ∈ A₁.support, x ∈ A₂.support → x ∉ F.V) {a₀ b₀ a₁ b₁ : Shat} {Q₀ : GraphWalk
      D.rad.G.toGraph a₀ b₀} {Q₁ : GraphWalk D.rad.G.toGraph a₁ b₁} (h₀ : IsArcOn D.rad.G Dv F Q₀)
    (h₁' : IsArcOn D.rad.G Dv F Q₁) (o₀ : ∀ e ∈ Q₀.edges, Disjoint e Δv)
      (o₁ : ∀ e ∈ Q₁.edges, Disjoint e Δv) (hd : ∀ e ∈ Q₁.edges, e ∉ Q₀.edges)
    (n₀ : (a₀ = r ∧ (b₀ ∈ A₁.support ∨ b₀ ∈ A₂.support)) ∨ (a₀ ∈ A₁.support ∧ b₀ ∈ A₂.support))
      (n₁ : (a₁ = r ∧ (b₁ ∈ A₁.support ∨ b₁ ∈ A₂.support)) ∨ (a₁ ∈ A₁.support ∧ b₁ ∈ A₂.support))
    (np₀ : ¬ PushesInto (Δ₀ \ {h}) (Δv \ {h}) (walkDrawing D.rad.G Q₀).U a₀ b₀) (np₁ : ¬ PushesInto
      (Δ₀ \ {h}) (Δv \ {h}) (walkDrawing D.rad.G Q₁).U a₁ b₁) : False := by
  have key : ∀ {a b a' b' : Shat} {Q : GraphWalk D.rad.G.toGraph a b} {Q' : GraphWalk
    D.rad.G.toGraph a' b'}, IsArcOn D.rad.G Dv F Q → IsArcOn D.rad.G Dv F Q' →
      (∀ e ∈ Q.edges, Disjoint e Δv) →
      (∀ e ∈ Q'.edges, Disjoint e Δv) → (∀ e ∈ Q'.edges, e ∉ Q.edges) → a = r → (b ∈ A₁.support
        ∨ b ∈ A₂.support) → ((a' = r ∧ (b' ∈ A₁.support ∨ b' ∈ A₂.support)) ∨ (a' ∈ A₁.support
          ∧ b' ∈ A₂.support)) →
      ¬ PushesInto (Δ₀ \ {h}) (Δv \ {h}) (walkDrawing D.rad.G Q).U a b → ¬ PushesInto (Δ₀ \ {h})
        (Δv \ {h}) (walkDrawing D.rad.G Q').U a' b' → False := by
    intro a b a' b' Q Q' hQ hQ' o o' hdd ear hb n hn hn'
    subst ear
    rcases hb with hb | hb
    · refine hf.false_of_rstar s ha hten hQ hQ' o o' hdd hb hn hn' ?_
      rcases n with ⟨h₃, h₄ | h₄⟩ | h₃
      · exact .inl ⟨h₃, h₄⟩
      · exact .inr (.inl ⟨h₃, h₄⟩)
      · exact .inr (.inr (.inl h₃))
    · refine hf.false_of_rstar s.swap ha.swap (fun x h₃ h₄ ↦ hten x h₄ h₃) hQ hQ' o o' hdd hb hn
        hn' ?_
      rcases n with ⟨h₃, h₄ | h₄⟩ | h₃
      · exact .inr (.inl ⟨h₃, h₄⟩)
      · exact .inl ⟨h₃, h₄⟩
      · exact .inr (.inr (.inr h₃))
  rcases n₁ with ⟨e₁, hb₁⟩ | hc₁
  · exact key h₁' h₀ o₁ o₀ (fun e he he' ↦ hd e he' he) e₁ hb₁ n₀ np₁ np₀
  · rcases n₀ with ⟨e₀, hb₀⟩ | hc₀
    · exact key h₀ h₁' o₀ o₁ hd e₀ hb₀ (.inr hc₁) np₀ np₁
    · exact hf.not_cross s h₀ h₁' o₀ o₁ hd hc₀.1 hc₁.1 hc₀.2 hc₁.2

/-- Steps (7) to (14) of the proof of (13.6): `h` cannot lie far inside `Δ`. -/
theorem false_of_far (hf : D.IsFar W H ρ r Δv Dv ord' 𝒯' F Δ₀ C Δ h) : False := by
  rcases hf.shape_cases with ⟨v₁, v₂, u, h', f₁, f₂, A₁, A₂, T, s, hfan, -⟩ | ⟨v₁, v₂, h₁, h₂, f₁,
    f₂, K₁, K₂, P, s, hdis, hP, hE, hc, hsub⟩
  · obtain ⟨a₀, b₀, a₁, b₁, Q₀, Q₁, h₀, h₁', o₀, o₁, hd, n₀, n₁, np₀, np₁⟩
      := hf.exists_normal_arcs s
    have hTF : ∀ x ∈ T.support, x ∉ F.V := fun x hx ↦ hf.off_tail s hfan h₀ h₁' o₀ o₁ hd n₀ n₁ hx
    refine hf.false_of_normal s (hf.fan_anchor s hfan hTF) (fun x h₃ h₄ ↦ ?_) h₀ h₁' o₀ o₁ hd n₀ n₁
      np₀ np₁
    have hxu := (s.meet x h₃ h₄).1
    exact hTF x (hxu ▸ T.start_mem_support)
  · obtain ⟨a₀, b₀, a₁, b₁, Q₀, Q₁, h₀, h₁', o₀, o₁, hd, n₀, n₁, np₀, np₁⟩
      := hf.exists_normal_arcs s
    have hne : h₁ ≠ h₂ := fun h₃ ↦ hdis h₁ K₁.end_mem_support (h₃ ▸ K₂.end_mem_support)
    obtain ⟨Y, ha⟩ := hf.path_anchor s hne hP hsub
    exact hf.false_of_normal s ha (fun x h₃ h₄ ↦ absurd h₄ (hdis x h₃)) h₀ h₁' o₀ o₁ hd n₀ n₁ np₀
      np₁

end IsFar

/-- `Δ_v` lies in the ambient disc, because its boundary does. -/
theorem IsSectorEnclave.Δv_subset (hx : D.IsSectorEnclave W H ρ r Δv Dv ord' 𝒯' F)
  (ham : D.IsAmbientDisc W H ρ F Δ₀) : Δv ⊆ Δ₀ := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hW := hx.wheel
  have hcl : IsClosed Δ₀ := ham.disc.isClosed
  have hclB : ∀ {f : Set Shat}, f ⊆ discBd W → closure f ⊆ Δ₀ := fun hf ↦ closure_minimal
    (hf.trans ham.bd_W) hcl
  have hU : Dv.U ⊆ Δ₀ := by
    rcases hx.sector.cases hW hx.hbdS hx.hin with ⟨v₁, v₂, u, h, f₁, f₂, A₁, A₂, T, hf, hC, hb₁,
      hb₂⟩ |
      ⟨v₁, v₂, h₁, h₂, f₁, f₂, K₁, K₂, P, hne, hl₁, hl₂, hb₁, hb₂, h1, h2, hdis, hP, hbd, -⟩
    · rw [hf.U_eq hC]
      refine union_subset (union_subset (union_subset ?_ ?_) (hclB hb₁)) (hclB hb₂)
      · refine Subset.trans ?_ (ham.spoke _ _ _ hf.spoke₁)
        refine walkU_subset (fun x hx' ↦ (GraphWalk.mem_support_append _ _).mpr (.inl hx')) ?_
        intro e he
        rw [GraphWalk.edges_append]
        exact List.mem_append_left _ he
      · refine Subset.trans ?_ (ham.spoke _ _ _ hf.spoke₂)
        refine walkU_subset (fun x hx' ↦ (GraphWalk.mem_support_append _ _).mpr (.inl hx')) ?_
        intro e he
        rw [GraphWalk.edges_append]
        exact List.mem_append_left _ he
    · rw [hx.sector.Dv_U, hbd]
      exact union_subset (union_subset (union_subset (union_subset (ham.spoke _ _ _ h1)
        (ham.spoke _ _ _ h2)) (hP.1.U_subset.trans ham.hub)) (hclB hb₁)) (hclB hb₂)
  have h' := ham.short Dv hx.sector.Dv_circuit hx.Dv_card hU
  rwa [hx.ins_Dv] at h'

/-- (13.6): the choice of the enclave `F` puts its inside in `Δ_v`. -/
theorem theorem_13_6_proof (hx : D.IsSectorEnclave W H ρ r Δv Dv ord' 𝒯' F) : D.ins F ⊆ Δv := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hFi := hx.isInsOf_F
  have hDv := hx.sector.Dv_circuit
  have hΔv := hx.sector.is_disc
  obtain ⟨Δ₀, ham⟩ := hx.exists_ambient
  obtain ⟨c, hc, h₁, h₂⟩ := hx.exists_edge
  obtain ⟨p, hp⟩ := hc.1
  obtain ⟨C, Δ, hC, hE, hΔ, hsub, hbd, hF, hv⟩ := exists_enclosing_circuit hT ham.disc hFi.1 hDv
    hFi.2.2.1 hΔv ham.ins_F (hx.Δv_subset ham) hFi.2.2.2.1 hx.sector.Dv_U.symm
    ⟨cap.emb p, h₁ ⟨p, hp, rfl⟩, h₂ ⟨p, hp, rfl⟩⟩ D.edge_two_ends
  have hr : D.IsRound W H ρ r Δv Dv ord' 𝒯' F Δ₀ C Δ := ⟨hx, ham, hC, hE, hΔ, hsub, hbd, hF, hv⟩
  by_cases hh : H.U ∩ Δ ⊆ C.U
  · exact hr.step_six hh
  · obtain ⟨h, hf⟩ := hr.exists_far hh
    exact hf.false_of_far.elim

end TangleDatum

end GraphMinor.GM19
