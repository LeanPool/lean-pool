/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section13v

/-!
# Graph Minors XIX, Section 13: steps (12) to (14) of (13.6), and (13.6)

The third arc `F₂` is an inner arc, so it is a chord of `D_v`. One of the two discs it cuts from
`Δ_v` misses `ins(F)`. So the other disc still points to `𝒯'`, and its boundary is at
least as long as `F`. Together with the same bound for `C`, and (14), this leaves no room for the
arc `F₀`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

/-- An open subset of a disc misses the boundary of the disc. -/
theorem disjoint_discBd_of_isOpen {T : Type} [TopologicalSpace T]
  (hT : IsClosedSurface T) {Δ O : Set T} (hΔ : IsClosedDisc Δ) (hO : IsOpen O) (hs : O ⊆ Δ) :
    Disjoint O (discBd Δ) := disjoint_left.mpr fun x hx hb ↦ by
  rw [← IsClosedDisc.frontier_eq_discBd hT hΔ, frontier_eq_closure_inter_closure] at hb
  obtain ⟨y, hy₁, hy₂⟩ := mem_closure_iff.mp hb.2 _ hO hx
  exact hy₂ (hs hy₁)

namespace TangleDatum

variable {D : TangleDatum cap χ} {W : Set Shat} {H : Drawing Shat} {ρ : ℕ} {r : Shat} {Δv : Set
  Shat} {Dv F : Drawing Shat}
  {ord' : ℕ} {𝒯' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {Δ₀ Δ : Set Shat} {C :
    Drawing Shat} {h : Shat}
  {v₁ v₂ c₁ c₂ h₁ h₂ : Shat} {f₁ f₂ : Set Shat} {A₁ : GraphWalk D.rad.G.toGraph v₁ c₁} {A₂ :
    GraphWalk D.rad.G.toGraph v₂ c₂} {T₁ : GraphWalk D.rad.G.toGraph c₁ h₁}
  {T₂ : GraphWalk D.rad.G.toGraph c₂ h₂}

namespace IsShape

/-- `r*` is on neither spoke. -/
theorem r_notMem₁ (hf : D.IsFar W H ρ r Δv Dv ord' 𝒯' F Δ₀ C Δ h) (s : D.IsShape W H r Δv Dv F f₁
  f₂ A₁ A₂ T₁ T₂) : r ∉ A₁.support := fun h' ↦
  IsWheelHubOfRadius.r_notMem_spoke hf.enc.wheel hf.enc.hbdS hf.enc.hin hf.enc.sector.rstar_mem
    s.spoke₁ ((GraphWalk.mem_support_append _ _).mpr (.inl h'))

omit [T2Space S] in
/-- No edge is on both `A₁` and `A₂`. -/
theorem edges_ne (s : D.IsShape W H r Δv Dv F f₁ f₂ A₁ A₂ T₁ T₂) : ∀ e ∈ A₁.edges, e ∉ A₂.edges
  := fun e h₁' h₂' ↦ by
  obtain ⟨x, y, hxy, hx, hy, hcap⟩ := D.exists_ends_of_mem_edges A₁ h₁'
  obtain ⟨hx', hy'⟩ := D.ends_mem_support A₂ h₂' hcap
  exact hxy ((s.meet x hx hx').1.trans (s.meet y hy hy').1.symm)

/-- The edges of `D_v` at `r*` differ. -/
theorem f_ne (hf : D.IsFar W H ρ r Δv Dv ord' 𝒯' F Δ₀ C Δ h) (s : D.IsShape W H r Δv Dv F f₁ f₂ A₁
  A₂ T₁ T₂) : f₁ ≠ f₂ := by
  rintro rfl
  have hm : v₁ ∈ closure f₁ ∩ D.rad.G.V := by
    rw [s.link₁.2.2.2]
    exact .inr rfl
  rw [s.link₂.2.2.2] at hm
  rcases hm with h' | h'
  · exact s.r_notMem₁ hf (h' ▸ A₁.start_mem_support)
  · exact s.ne h'

/-- `f₁` is not on `A₂`, as `r*` is not. -/
theorem f₁_notMem (hf : D.IsFar W H ρ r Δv Dv ord' 𝒯' F Δ₀ C Δ h) (s : D.IsShape W H r Δv Dv F f₁
  f₂ A₁ A₂ T₁ T₂) : f₁ ∉ A₂.edges := fun h' ↦
  s.swap.r_notMem₁ hf (D.ends_mem_support A₂ h' s.link₁.2.2.2).1

end IsShape

namespace IsFar

/-- Step (13) for the inner arc: `F₂` with the path of `D_v` from `r*` to `b₂` through `v₂` is at
least as long as `F`. The other disc cut from `Δ_v` by `F₂` misses `ins(F)`, since
otherwise all of `C` would be in `F`. -/
theorem chord_bound (hf : D.IsFar W H ρ r Δv Dv ord' 𝒯' F Δ₀ C Δ h) (s : D.IsShape W H r Δv Dv F f₁
  f₂ A₁ A₂ T₁ T₂) {b₁ b₂ : Shat} {Q₁ : GraphWalk D.rad.G.toGraph r b₁}
    {F₂ : GraphWalk D.rad.G.toGraph r b₂} {X₁ : GraphWalk D.rad.G.toGraph v₁ b₁} {X₂ : GraphWalk
      D.rad.G.toGraph v₂ b₂} {Z₁ : GraphWalk D.rad.G.toGraph b₁ c₁}
    {Z₂ : GraphWalk D.rad.G.toGraph b₂ c₂} (hF₂ : IsArcOn D.rad.G Dv F F₂)
      (hin : ∀ e ∈ F₂.edges, e ⊆ discInt Δv) (hA₁ : A₁ = X₁.append Z₁) (hA₂ : A₂ = X₂.append Z₂)
    (hC : ∀ e, e ∈ C.E ↔ e ∈ Q₁.edges ∨ e ∈ (GraphWalk.cons s.link₁ X₁).edges)
      (hQ₁ : ∀ e ∈ Q₁.edges, e ∈ F.E)
    (hcover : ∀ e ∈ F.E, e ∈ F₂.edges ∨ Disjoint e Δv ∨ e ∈ Dv.E) : F.E.ncard ≤ F₂.length +
      (X₂.length + 1) := by
  classical
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hman : ∀ x : Shat, IsManifoldPoint x := (Surface.IsClosedSurface.isSurface hT).2.2
  have hx := hf.enc
  have hW := hx.wheel
  have hFi := hx.isInsOf_F
  have hFc := hFi.1
  have hFs := hFc.1
  have hDv := hx.sector.Dv_circuit
  have hΔv := hx.sector.is_disc
  have hbv := hx.sector.Dv_U.symm
  have hΔF := hFi.2.2.1
  have hbF := hFi.2.2.2.1
  have hrep := hx.hrep
  have hFcard := hx.F_card
  have hρ := hW.pos_ρ
  have hUvΔ : Dv.U ⊆ Δv := fun x hx' ↦ Surface.discBd_subset _ (hbv ▸ hx')
  have hX₂s : X₂.IsSimple := by
    have := (isSimple_of_append s.spoke₂.1).1
    rw [hA₂] at this
    exact (isSimple_of_append this).1
  have hrX₂ : r ∉ X₂.support := fun h' ↦ s.swap.r_notMem₁ hf (by
    rw [hA₂, GraphWalk.mem_support_append]
    exact .inl h')
  set Pa : GraphWalk D.rad.G.toGraph r b₂ := GraphWalk.cons s.link₂ X₂ with hPa
  have hPas : Pa.IsSimple := List.nodup_cons.mpr ⟨hrX₂, hX₂s⟩
  have hPaE : ∀ e, e ∈ Pa.edges ↔ e = f₂ ∨ e ∈ X₂.edges := fun e ↦ by
    rw [hPa, GraphWalk.edges_cons, List.mem_cons]
  have hPaD : ∀ e ∈ Pa.edges, e ∈ Dv.E := fun e he ↦ by
    rcases (hPaE e).mp he with rfl | he
    · exact s.f₂_mem
    · exact s.edge₂ e (by rw [hA₂, GraphWalk.edges_append]; exact List.mem_append_left _ he)
  obtain ⟨W₁, W₂, h₀⟩ := exists_splits hDv.2 hDv.1 hF₂.left hF₂.right hF₂.ne
  obtain ⟨R, hR⟩ := exists_side_of_walk (D := D) hF₂.ne hPas hPaD h₀
  have ht := Splits.twoPaths hR hF₂.ne hDv.1 hF₂.simple hF₂.inner hF₂.off
  have hUF₂ : (walkDrawing D.rad.G F₂).U ⊆ Δv := fun y hy ↦ by
    have hc : ∃ e ∈ F₂.edges, y ∈ closure e := by
      rcases (mem_walkDrawing_U _ _).mp hy with h' | h'
      · exact GraphWalk.exists_edge_of_support F₂ hF₂.ne h'
      · exact h'
    obtain ⟨e, he, hye⟩ := hc
    rw [← closure_discInt hΔv]
    exact closure_mono (hin e he) hye
  have hsubU : ∀ {a b : Shat} {K : GraphWalk D.rad.G.toGraph a b}, (walkDrawing D.rad.G
    K).IsSubdrawing Dv → (walkDrawing D.rad.G K).U ⊆ Dv.U := fun h' ↦ h'.U_subset
  have hPU : (walkDrawing D.rad.G Pa).U ⊆ Dv.U := ht.left.1.U_subset
  have hRU : (walkDrawing D.rad.G R.reverse).U ⊆ Dv.U := ht.right.1.U_subset
  have hc₁ := ht.swap.left_circuit
  have hc₂ := ht.left_circuit
  have hU₁ := ht.swap.U_right
  have hU₂ := ht.U_right
  obtain ⟨Δp, ⟨hsp, hdp, hbp, -⟩, -⟩ := disc_oArc Δv _ hΔv (by
    rw [hU₁]
    exact union_subset hUF₂ (hPU.trans hUvΔ)) (GM14.isOArc_of_isCircuit hc₁)
  obtain ⟨Δr, ⟨hsr, hdr, hbr, -⟩, -⟩ := disc_oArc Δv _ hΔv (by
    rw [hU₂]
    exact union_subset hUF₂ (hRU.trans hUvΔ)) (GM14.isOArc_of_isCircuit hc₂)
  have hcovT := ht.theta_cover hT (isSide_out hT hΔv hbv) hdp hdr hbp hbr
    (disjoint_left.mpr fun x h₁' h₂' ↦ h₁' (hsp h₂')) (disjoint_left.mpr fun x h₁' h₂' ↦ h₁'
      (hsr h₂'))
  have hsub₁ : (D.rad.G.sup (walkDrawing D.rad.G F₂) (walkDrawing D.rad.G Pa)).IsSubdrawing D.rad.G
    := D.rad.G.sup_isSubdrawing _ _
  have hcard : (D.rad.G.sup (walkDrawing D.rad.G F₂) (walkDrawing D.rad.G Pa)).E.ncard
    = F₂.length + (X₂.length + 1) := by
    rw [Drawing.sup_E (walkDrawing_isSubdrawing _ _) (walkDrawing_isSubdrawing _ _),
      Set.ncard_union_eq (s := (walkDrawing D.rad.G F₂).E) (t := (walkDrawing D.rad.G Pa).E)
        (disjoint_left.mpr fun e h₁' h₂' ↦ by
      rw [walkDrawing_E] at h₁' h₂'
      exact hF₂.off e h₁' (hPaD e h₂')) (walkDrawing D.rad.G F₂).finite_edges
        (walkDrawing D.rad.G Pa).finite_edges, ncard_walk_E _ hF₂.simple, ncard_walk_E _ hPas]
    rfl
  rw [← hcard]
  by_cases hle : F.E.ncard ≤ (D.rad.G.sup (walkDrawing D.rad.G F₂) (walkDrawing D.rad.G Pa)).E.ncard
  · exact hle
  have hle' : (D.rad.G.sup (walkDrawing D.rad.G F₂) (walkDrawing D.rad.G Pa)).E.ncard ≤
      4 * ρ + 4 := by omega
  have hCirc₁ : Drawing.IsCircuitOf (D.rad.G.sup (walkDrawing D.rad.G F₂)
    (walkDrawing D.rad.G Pa)) D.rad.G := ⟨hsub₁, hc₁⟩
  have heq := hW.eq_ins_of_disc hCirc₁ hle' hdp (hsp.trans hx.sector.Δv_sub) hbp
  have hins := D.ins_spec hCirc₁ (by omega)
  rw [← heq] at hins
  -- `F` misses the interior of the other disc.
  have hIntΔ : discInt Δr ⊆ Δv := (discInt_subset _).trans hsr
  have hoffF : Disjoint (discInt Δr) F.U := by
    have hsubc : F.U ⊆ (discInt Δr)ᶜ := U_of_edges hFc.2 (hdr.isOpen_discInt hman).isClosed_compl
      fun e he p hp hpi ↦ by
      rcases hcover e he with h' | h' | h'
      · refine hpi.2 ?_
        rw [hbr, hU₂]
        exact .inl ((mem_walkDrawing_U _ _).mpr (.inr ⟨e, h', subset_closure hp⟩))
      · exact disjoint_left.mp h' hp (hIntΔ hpi)
      · exact disjoint_left.mp (disjoint_discBd_of_isOpen hT hΔv (hdr.isOpen_discInt hman) hIntΔ)
          hpi (hbv ▸ Dv.closure_subset_U h' (subset_closure hp))
    exact disjoint_left.mpr fun x h₁' h₂' ↦ hsubc h₂' h₁'
  have hoffIns : Disjoint (discInt Δr) (D.ins F) := by
    by_contra hn
    obtain ⟨y, hy₁, hy₂⟩ := not_disjoint_iff.mp hn
    have hyb : y ∉ discBd (D.ins F) := fun h' ↦ disjoint_left.mp hoffF hy₁ (hbF ▸ h')
    have hsubI : discInt Δr ⊆ discInt (D.ins F) :=
      subset_discInt_of_connected hman hΔF hdr.isPreconnected_discInt (by
        rw [hbF]
        exact hoffF) ⟨y, hy₁, hy₂, hyb⟩
    have hrI : Δr ⊆ D.ins F := by
      rw [← closure_discInt hdr, ← closure_discInt hΔF]
      exact closure_mono hsubI
    have hIOff : Disjoint (discInt (D.ins F)) (discBd Δ) := disjoint_discBd_of_isOpen hT hf.disc
      (hΔF.isOpen_discInt hman) ((discInt_subset _).trans hf.F_sub)
    refine hf.ne_F fun e he ↦ ?_
    rcases (hC e).mp he with h' | h'
    · exact hQ₁ e h'
    · have heD : e ∈ Dv.E := by
        rw [GraphWalk.edges_cons, List.mem_cons] at h'
        rcases h' with rfl | h'
        · exact s.f₁_mem
        · exact s.edge₁ e (by rw [hA₁, GraphWalk.edges_append]; exact List.mem_append_left _ h')
      have heR : e ∈ R.reverse.edges := by
        have heA : e ∉ Pa.edges := fun hn' ↦ by
          rw [GraphWalk.edges_cons, List.mem_cons] at h'
          rcases (hPaE e).mp hn' with rfl | h₃ <;> rcases h' with h' | h'
          · exact s.f_ne hf h'.symm
          · exact s.swap.f₁_notMem hf (by
              rw [hA₁, GraphWalk.edges_append]
              exact List.mem_append_left _ h')
          · exact s.f₁_notMem hf (by
              rw [hA₂, GraphWalk.edges_append, ← h']
              exact List.mem_append_left _ h₃)
          · exact s.edges_ne e (by
              rw [hA₁, GraphWalk.edges_append]
              exact List.mem_append_left _ h') (by
              rw [hA₂, GraphWalk.edges_append]
              exact List.mem_append_left _ h₃)
        rw [GraphWalk.edges_reverse, List.mem_reverse]
        exact ((hR.E e).mp heD).resolve_left heA
      have heG := hDv.1.2 heD
      by_contra hnF
      obtain ⟨p, hp⟩ := heG.1
      have hpF : p ∉ F.U := disjoint_left.mp (edge_disjoint_U hFs heG hnF) hp
      have hpIns : p ∈ D.ins F := hrI (Surface.discBd_subset _ (by
        rw [hbr, hU₂]
        exact .inr ((mem_walkDrawing_U _ _).mpr (.inr ⟨e, heR, subset_closure hp⟩))))
      have hpBd : p ∈ discBd Δ := by
        rw [hf.bd]
        exact C.closure_subset_U he (subset_closure hp)
      exact disjoint_left.mp hIOff ⟨hpIns, fun h₃ ↦ hpF (hbF ▸ h₃)⟩ hpBd
  refine hx.card_le_of_cover hins fun y hy₁ hy₂ ↦ ?_
  rcases hcovT y with h' | h' | h'
  · exfalso
    obtain ⟨z, hz₁, hz₂⟩ := mem_closure_iff.mp h' _ (hΔv.isOpen_discInt hman) hy₁
    exact hz₂ (discInt_subset _ hz₁)
  · exact h'
  · exfalso
    by_cases hyb : y ∈ discBd Δr
    · rw [hbr, hU₂] at hyb
      rcases hyb with h₃ | h₃
      · refine hy₂.2 ?_
        rw [hbF]
        rcases (mem_walkDrawing_U _ _).mp h₃ with h₄ | ⟨e, he, hye⟩
        · exact F.V_subset_U (hF₂.mem_F hFs y h₄)
        · exact F.closure_subset_U (hF₂.inF e he) hye
      · exact hy₁.2 (hbv ▸ hRU h₃)
    · exact disjoint_left.mp hoffIns ⟨h', hyb⟩ (discInt_subset _ hy₂)

end IsFar

end TangleDatum

end GraphMinor.GM19
