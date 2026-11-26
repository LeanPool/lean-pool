/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section13r

/-!
# Graph Minors XIX, Section 13: the shape of `D_v`, and step (8) of (13.6)

The two forms of the sector are put into one shape: `D_v` is made of the edges `f₁, f₂` at `r*`, of
first parts `A₁, A₂` of the two spokes, and of vertices of `H`.
Step (8) says where the ends of an outer arc can be.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

/-- A pushing of an arc goes in both directions. -/
theorem PushesInto.symm {T : Type} [TopologicalSpace T] {Z Y L : Set T} {a b : T}
  (h : PushesInto Z Y L a b) : PushesInto Z Y L b a := fun hb ha p hp ↦ by
  obtain ⟨q, hq, hpq⟩ := h ha hb p.symm fun t ↦ hp _
  refine ⟨q.symm, fun t ↦ hq _, ?_⟩
  have := hpq.symm₂
  rwa [Path.symm_symm] at this

omit [T2Space Shat] in
/-- In a simple walk from `x`, only the first edge has the end `x`. -/
theorem GraphWalk.edge_at_start {G : Drawing Shat} {x y : Shat} (K : GraphWalk G.toGraph x y)
  (hs : K.IsSimple) {e e' : Set Shat} (he : e ∈ K.edges) (he' : e' ∈ K.edges)
    (hx : x ∈ closure e) (hx' : x ∈ closure e') : e = e' := by
  cases K with
  | nil _ => cases he
  | @cons _ z _ g hg t =>
    have hxV : x ∈ G.V := hg.left_mem
    have hnot : x ∉ t.support := (List.nodup_cons.mp hs).1
    have key : ∀ f ∈ (GraphWalk.cons hg t).edges, x ∈ closure f → f = g := fun f hf hxf ↦ by
      rw [GraphWalk.edges_cons, List.mem_cons] at hf
      rcases hf with rfl | hf
      · rfl
      · exfalso
        obtain ⟨p, q, hl, A, B, rfl⟩ := GraphWalk.exists_split_edge t hf
        have hm : x ∈ closure f ∩ G.V := ⟨hxf, hxV⟩
        rw [hl.2.2.2] at hm
        refine hnot ((GraphWalk.mem_support_append _ _).mpr ?_)
        rcases hm with rfl | rfl
        · exact .inl A.end_mem_support
        · exact .inr (by simp [B.start_mem_support])
    rw [key e he hx, key e' he' hx']

/-- A circuit has at most two edges at a vertex. -/
theorem no_three_edges {G F : Drawing Shat} (hF : F.IsCircuitOf G)
  (hG : ∀ g ∈ G.E, ∃ a b, a ≠ b ∧ closure g ∩ G.V = {a, b}) {x : Shat} (hx : x ∈ F.V)
    {e₁ e₂ e₃ : Set Shat} (h₁ : e₁ ∈ F.E) (h₂ : e₂ ∈ F.E) (h₃ : e₃ ∈ F.E) (x₁ : x ∈ closure e₁)
      (x₂ : x ∈ closure e₂) (x₃ : x ∈ closure e₃) (n₁₂ : e₁ ≠ e₂) (n₁₃ : e₁ ≠ e₃)
    (n₂₃ : e₂ ≠ e₃) : False := by
  obtain ⟨a, b, hab, hcap⟩ := hG e₁ (hF.1.2 h₁)
  have hxV : x ∈ closure e₁ ∩ G.V := ⟨x₁, hF.1.1 hx⟩
  obtain ⟨y, hy, hxy⟩ : ∃ y, y ∈ F.V ∧ x ≠ y := by
    rw [hcap] at hxV
    have hab' : a ∈ F.V ∧ b ∈ F.V := by
      have hl : G.toGraph.IsLink e₁ a b := ⟨hF.1.2 h₁, (by
        have : a ∈ closure e₁ ∩ G.V := by rw [hcap]; exact .inl rfl
        exact this.2), (by
        have : b ∈ closure e₁ ∩ G.V := by rw [hcap]; exact .inr rfl
        exact this.2), hcap⟩
      exact Drawing.IsLink.mem_V_of_sub hF.1 hl h₁
    rcases hxV with rfl | rfl
    · exact ⟨b, hab'.2, hab⟩
    · exact ⟨a, hab'.1, hab.symm⟩
  obtain ⟨W₁, W₂, hs⟩ := exists_splits hF.2 hF.1 hx hy hxy
  have hu₁ : ∀ {e e' : Set Shat}, e ∈ W₁.edges → e' ∈ W₁.edges → x ∈ closure e → x ∈ closure e' → e
    = e' := fun he he' hx₁ hx₂ ↦
    GraphWalk.edge_at_start W₁ hs.s₁ he he' hx₁ hx₂
  have hu₂ : ∀ {e e' : Set Shat}, e ∈ W₂.edges → e' ∈ W₂.edges → x ∈ closure e → x ∈ closure e' → e
    = e' := fun he he' hx₁ hx₂ ↦ by
    refine GraphWalk.edge_at_start W₂.reverse hs.s₂.reverse ?_ ?_ hx₁ hx₂
    · rwa [GraphWalk.edges_reverse, List.mem_reverse]
    · rwa [GraphWalk.edges_reverse, List.mem_reverse]
  rcases (hs.E e₁).mp h₁ with a₁ | a₁ <;>
    rcases (hs.E e₂).mp h₂ with a₂ | a₂ <;> rcases (hs.E e₃).mp h₃ with a₃ | a₃
  · exact n₁₂ (hu₁ a₁ a₂ x₁ x₂)
  · exact n₁₂ (hu₁ a₁ a₂ x₁ x₂)
  · exact n₁₃ (hu₁ a₁ a₃ x₁ x₃)
  · exact n₂₃ (hu₂ a₂ a₃ x₂ x₃)
  · exact n₂₃ (hu₁ a₂ a₃ x₂ x₃)
  · exact n₁₃ (hu₂ a₁ a₃ x₁ x₃)
  · exact n₁₂ (hu₂ a₁ a₂ x₁ x₂)
  · exact n₁₂ (hu₂ a₁ a₂ x₁ x₂)

namespace TangleDatum

variable {D : TangleDatum cap χ} {W : Set Shat} {H : Drawing Shat} {ρ : ℕ} {r : Shat} {Δv : Set
  Shat} {Dv F : Drawing Shat}
  {ord' : ℕ} {𝒯' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {Δ₀ Δ : Set Shat} {C :
    Drawing Shat} {h : Shat}

omit [T2Space S] [T2Space Shat] in
/-- Every edge of the drawing has two distinct ends. -/
theorem edge_two_ends (D : TangleDatum cap χ) : ∀ g ∈ D.rad.G.E, ∃ a b, a ≠ b
  ∧ closure g ∩ D.rad.G.V = {a, b} := fun g hg ↦ by
  obtain ⟨x, hx, y, hy, hcap⟩ := D.rad.isPreRadial.2.2.2.2.1 g hg
  exact ⟨x, y, fun h' ↦ hy.2 (h' ▸ hx), hcap⟩

omit [T2Space S] in
/-- A spoke meets the hub only in its inner end. -/
theorem IsSpokeWalk.U_inter_hub (hW : D.IsWheelHubOfRadius W H ρ) {v h₁ : Shat} {K : GraphWalk
  D.rad.G.toGraph v h₁} (hK : D.IsSpokeWalk W H K) {y : Shat}
    (hy : y ∈ (walkDrawing D.rad.G K).U) (hyH : y ∈ H.U) : y = h₁ := by
  rcases (mem_walkDrawing_U _ _).mp hy with hs | ⟨e, he, hye⟩
  · exact hK.support_hub hs (mem_V_of_mem_U hW.H_sub hyH (K.mem_vertexSet_of_mem_support hs))
  · have heG : e ∈ D.rad.G.E := TieBreaker.mem_edges_E K he
    obtain ⟨p, q, hpq, hp, hq, hcap⟩ := D.exists_ends_of_mem_edges K he
    rcases closure_edge_subset heG hye with hin | hV
    · have heH : e ∈ H.E := by
        by_contra hn
        exact disjoint_left.mp (edge_disjoint_U hW.H_sub heG hn) hin hyH
      have hl : D.rad.G.toGraph.IsLink e p q := ⟨heG, K.mem_vertexSet_of_mem_support hp,
        K.mem_vertexSet_of_mem_support hq, hcap⟩
      obtain ⟨h₁', h₂'⟩ := Drawing.IsLink.mem_V_of_sub hW.H_sub hl heH
      exact absurd ((hK.support_hub hp h₁').trans (hK.support_hub hq h₂').symm) hpq
    · have hm : y ∈ closure e ∩ D.rad.G.V := ⟨hye, hV⟩
      rw [hcap] at hm
      have hs : y ∈ K.support := by
        rcases hm with rfl | rfl
        · exact hp
        · exact hq
      exact hK.support_hub hs (mem_V_of_mem_U hW.H_sub hyH hV)

/-- Step (8), first part, when the spokes do not meet: an outer arc has no end inside the path `D_v
∩ H`, because `Δ_v ∪ ins(H)` is a disc around such an end, so the edge of the
arc there would be in `ins(H) \ H`, against (3). -/
theorem IsFar.outer_end_path (hf : D.IsFar W H ρ r Δv Dv ord' 𝒯' F Δ₀ C Δ h) {v₁ v₂ h₁ h₂ : Shat}
  {f₁ f₂ : Set Shat} {K₁ : GraphWalk D.rad.G.toGraph v₁ h₁}
    {K₂ : GraphWalk D.rad.G.toGraph v₂ h₂} {P : Drawing Shat} (hl₁ : D.rad.G.toGraph.IsLink f₁ r
      v₁) (hl₂ : D.rad.G.toGraph.IsLink f₂ r v₂)
    (hb₁ : f₁ ⊆ discBd W) (hb₂ : f₂ ⊆ discBd W) (h1 : D.IsSpokeWalk W H K₁)
      (h2 : D.IsSpokeWalk W H K₂) (hdis : ∀ x ∈ K₁.support, x ∉ K₂.support)
    (hP : Drawing.IsPathOf P H h₁ h₂) (hbd : discBd Δv = (walkDrawing D.rad.G K₁).U ∪
      (walkDrawing D.rad.G K₂).U ∪ P.U ∪ closure f₁ ∪ closure f₂)
    {a b : Shat} {Q : GraphWalk D.rad.G.toGraph a b} (hQ : IsArcOn D.rad.G Dv F Q)
      (ho : ∀ e ∈ Q.edges, Disjoint e Δv) (hn₀ : a ≠ r) (hn₁ : a ∉ K₁.support)
        (hn₂ : a ∉ K₂.support) :
    False := by
  classical
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hman : ∀ x : Shat, IsManifoldPoint x := (Surface.IsClosedSurface.isSurface hT).2.2
  have hx := hf.enc
  have hW := hx.wheel
  have hDv := hx.sector.Dv_circuit
  have hΔv := hx.sector.is_disc
  have hbv := hx.sector.Dv_U.symm
  have hFi := hx.isInsOf_F
  have hne12 : h₁ ≠ h₂ := fun h' ↦ hdis h₁ K₁.end_mem_support (h' ▸ K₂.end_mem_support)
  have hHV₁ : h₁ ∈ H.V := h1.2.h_mem
  have hHV₂ : h₂ ∈ H.V := h2.2.h_mem
  -- `H` is a circuit, since it has two vertices.
  have hHe : IsEnclave D.tb D.ord D.𝒯 H ∧ H.E.ncard ≤ 4 * ρ + 4 := by
    rcases hf.hub with ⟨hV, -⟩ | ⟨h₀, h₀', -⟩
    · rw [hV] at hHV₁ hHV₂
      exact absurd ((mem_singleton_iff.mp hHV₁).trans (mem_singleton_iff.mp hHV₂).symm) hne12
    · exact ⟨h₀, h₀'⟩
  obtain ⟨hEn, hEc⟩ := hHe
  obtain ⟨-, -, -, hHc, hHlt, -⟩ := id hEn
  have hHi := D.ins_spec hHc (by have := hW.rep_ge; omega)
  have hΔH := hHi.2.2.1
  have hbH := hHi.2.2.2.1
  have hUH : H.U ⊆ D.ins H := fun x hx' ↦ Surface.discBd_subset _ (hbH ▸ hx')
  have hUv : Dv.U ⊆ Δv := fun x hx' ↦ Surface.discBd_subset _ (hbv ▸ hx')
  have hPU : P.U ⊆ discBd Δv := fun x hx' ↦ hbd ▸ .inl (.inl (.inr hx'))
  -- `a` lies on the path `P`, away from its ends.
  have haU : a ∈ discBd Δv := hbv ▸ Dv.V_subset_U hQ.left
  have haV : a ∈ D.rad.G.V := hDv.1.1 hQ.left
  have hclosV : ∀ {f : Set Shat} {y : Shat}, D.rad.G.toGraph.IsLink f r y → a ∈ closure f → a = r
    ∨ a = y := fun {f _} hl hc ↦ by
    have hm : a ∈ closure f ∩ D.rad.G.V := ⟨hc, haV⟩
    rw [hl.2.2.2] at hm
    exact hm
  have hsup : ∀ {u v : Shat} {K : GraphWalk D.rad.G.toGraph u v}, a ∈ (walkDrawing D.rad.G K).U
    → a ∈ K.support := fun {_ _ K} hu ↦ by
    have := mem_V_of_mem_U (walkDrawing_isSubdrawing D.rad.G K) hu haV
    rw [walkDrawing_V] at this
    exact this
  have haP : a ∈ P.U := by
    rw [hbd] at haU
    rcases haU with (((h₀ | h₀) | h₀) | h₀) | h₀
    · exact absurd (hsup h₀) hn₁
    · exact absurd (hsup h₀) hn₂
    · exact h₀
    · rcases hclosV hl₁ h₀ with h' | h'
      · exact absurd h' hn₀
      · exact absurd (h' ▸ K₁.start_mem_support) hn₁
    · rcases hclosV hl₂ h₀ with h' | h'
      · exact absurd h' hn₀
      · exact absurd (h' ▸ K₂.start_mem_support) hn₂
  have hane₁ : a ≠ h₁ := fun h' ↦ hn₁ (h' ▸ K₁.end_mem_support)
  have hane₂ : a ≠ h₂ := fun h' ↦ hn₂ (h' ▸ K₂.end_mem_support)
  -- The first edge of the arc at `a`.
  obtain ⟨y, e, hl, t, hQeq⟩ : ∃ (y : Shat) (e : Set Shat) (hl : D.rad.G.toGraph.IsLink e a y)
    (t : GraphWalk D.rad.G.toGraph y b), Q = .cons hl t := by
    cases Q with
    | nil _ => exact absurd rfl hQ.ne
    | cons hl t => exact ⟨_, _, hl, t, rfl⟩
  have heQ : e ∈ Q.edges := by rw [hQeq]; exact List.mem_cons_self
  have heF : e ∈ F.E := hQ.inF e heQ
  have heG : e ∈ D.rad.G.E := hl.1
  have haclos : a ∈ closure e := IsLink.left_mem_closure hl
  have hdisΔ : Disjoint e Δv := ho e heQ
  have heDv : e ∉ Dv.E := hQ.off e heQ
  -- `e` is not an edge of `H`, as `H` has its two edges at `a` in `P`.
  have hPG : Drawing.IsPathOf P D.rad.G h₁ h₂ := ⟨hP.1.trans hW.H_sub, hP.2⟩
  obtain ⟨K₀, hK₀, hV₀, hE₀⟩ := Drawing.IsPathOf.exists_simple_walk hPG
  have haV₀ : a ∈ P.V := mem_V_of_mem_U hPG.1 haP haV
  have hedgeDv : ∀ {g : Set Shat}, g ∈ P.E → g ∈ Dv.E := fun {g} hg ↦ by
    by_contra hn
    obtain ⟨x, hx'⟩ := (hPG.1.2 hg).1
    have hxU : x ∈ P.U := P.closure_subset_U hg (subset_closure hx')
    exact disjoint_left.mp (edge_disjoint_U hDv.1 (hPG.1.2 hg) hn) hx' (hbv ▸ hPU hxU)
  have heH : e ∉ H.E := by
    intro heH
    obtain ⟨L, M, hLM⟩ := K₀.exists_append_of_mem ((hV₀ a).mp haV₀)
    obtain ⟨z, g₂, hg₂, t₂, hM⟩ : ∃ (z : Shat) (g : Set Shat) (hg : D.rad.G.toGraph.IsLink g a z)
      (t : GraphWalk D.rad.G.toGraph z h₂), M = .cons hg t := by
      cases M with
      | nil _ => exact absurd rfl hane₂
      | cons hl t => exact ⟨_, _, hl, t, rfl⟩
    obtain ⟨z', g₁, hg₁, t₁, hL⟩ : ∃ (z : Shat) (g : Set Shat) (hg : D.rad.G.toGraph.IsLink g a z)
      (t : GraphWalk D.rad.G.toGraph z h₁), L.reverse = .cons hg t := by
      cases hR : L.reverse with
      | nil _ => exact absurd rfl hane₁
      | cons hl t => exact ⟨_, _, hl, t, rfl⟩
    have hg₁L : g₁ ∈ L.edges := by
      have : g₁ ∈ L.reverse.edges := by rw [hL]; exact List.mem_cons_self
      rwa [GraphWalk.edges_reverse, List.mem_reverse] at this
    have hg₂M : g₂ ∈ M.edges := by rw [hM]; exact List.mem_cons_self
    have hP₁ : g₁ ∈ P.E := (hE₀ g₁).mpr (by
      rw [hLM, GraphWalk.edges_append]
      exact List.mem_append_left _ hg₁L)
    have hP₂ : g₂ ∈ P.E := (hE₀ g₂).mpr (by
      rw [hLM, GraphWalk.edges_append]
      exact List.mem_append_right _ hg₂M)
    have hne : g₁ ≠ g₂ := fun h' ↦ Splits.append_edge (hLM ▸ hK₀) hg₁L (h' ▸ hg₂M)
    exact no_three_edges hHc D.edge_two_ends (hP.1.1 haV₀) heH (hP.1.2 hP₁) (hP.1.2 hP₂) haclos
      (IsLink.left_mem_closure hg₁) (IsLink.left_mem_closure hg₂)
      (fun h' ↦ heDv (h' ▸ hedgeDv hP₁)) (fun h' ↦ heDv (h' ▸ hedgeDv hP₂)) hne
  rcases edge_inside_or_off hT hHc.1 hΔH hbH heG heH with hin | hoff
  · obtain ⟨y', hy'⟩ := heG.1
    have hyU : y' ∈ F.U := F.closure_subset_U heF (subset_closure hy')
    have hyF : y' ∈ D.ins F := Surface.discBd_subset _ (hFi.2.2.2.1 ▸ hyU)
    have hm : y' ∈ D.ins F ∩ D.ins H := ⟨hyF, discInt_subset _ (hin hy')⟩
    rw [hx.hub_circuit hEn] at hm
    exact (hin hy').2 (hbH ▸ hm.2)
  · -- The union of `Δ_v` and `ins(H)` is a disc with `a` in its interior.
    have hOff := IsBoundarySector.interior_off_hub hx.hopt hx.hbdS hx.hin hx.sector hEn hEc
    have hmeet : Δv ∩ D.ins H = P.U := by
      apply Subset.antisymm
      · rintro y' ⟨hy₁, hy₂⟩
        by_cases hi₁ : y' ∈ discInt Δv
        · have hc : y' ∈ closure (discInt (D.ins H)) := by rw [closure_discInt hΔH]; exact hy₂
          obtain ⟨z, hz₁, hz₂⟩ := mem_closure_iff.mp hc _ (hΔv.isOpen_discInt hman) hi₁
          exact absurd hz₂ (disjoint_left.mp hOff.symm hz₁)
        by_cases hi₂ : y' ∈ discInt (D.ins H)
        · have hc : y' ∈ closure (discInt Δv) := by rw [closure_discInt hΔv]; exact hy₁
          obtain ⟨z, hz₁, hz₂⟩ := mem_closure_iff.mp hc _ (hΔH.isOpen_discInt hman) hi₂
          exact absurd hz₂ (disjoint_left.mp hOff hz₁)
        have hbdv : y' ∈ discBd Δv := by_contra fun hn ↦ hi₁ ⟨hy₁, hn⟩
        have hbdH : y' ∈ H.U := by
          rw [← hbH]
          exact by_contra fun hn ↦ hi₂ ⟨hy₂, hn⟩
        have hP₁ : h₁ ∈ P.U := P.V_subset_U ((hV₀ h₁).mpr K₀.start_mem_support)
        have hP₂ : h₂ ∈ P.U := P.V_subset_U ((hV₀ h₂).mpr K₀.end_mem_support)
        have hoffbd : ∀ {f : Set Shat}, f ⊆ discBd W → y' ∉ closure f := fun {f} hf' hc ↦ by
          have hclos : closure f ⊆ discBd W := closure_minimal hf' (by
            rw [← IsClosedDisc.frontier_eq_discBd hT hW.is_disc]; exact isClosed_frontier)
          exact (hW.H_in_int hbdH).2 (hclos hc)
        rw [hbd] at hbdv
        rcases hbdv with (((h₀ | h₀) | h₀) | h₀) | h₀
        · rw [IsSpokeWalk.U_inter_hub hW h1 h₀ hbdH]; exact hP₁
        · rw [IsSpokeWalk.U_inter_hub hW h2 h₀ hbdH]; exact hP₂
        · exact h₀
        · exact absurd h₀ (hoffbd hb₁)
        · exact absurd h₀ (hoffbd hb₂)
      · intro x hx'
        exact ⟨Surface.discBd_subset _ (hPU hx'), hUH (hP.1.U_subset hx')⟩
    obtain ⟨hdU, hbU⟩ := disc_union Δv (D.ins H) P.U h₁ h₂ hΔv hΔH (isLine_of_isPathBetween hP.2
      hne12) hmeet hPU (fun x hx' ↦ hbH ▸ hP.1.U_subset hx')
    have hain : a ∈ discInt (Δv ∪ D.ins H) := by
      refine ⟨.inl (Surface.discBd_subset _ (hbv ▸ Dv.V_subset_U hQ.left)), ?_⟩
      rw [hbU]
      rintro ⟨-, h₀⟩
      refine h₀ ⟨haP, ?_⟩
      rintro (h' | h')
      · exact hane₁ h'
      · exact hane₂ h'
    obtain ⟨z, hz₁, hz₂⟩ := mem_closure_iff.mp haclos _ (hdU.isOpen_discInt hman) hain
    rcases discInt_subset _ hz₁ with h' | h'
    · exact disjoint_left.mp hdisΔ hz₂ h'
    · exact disjoint_left.mp hoff hz₂ h'

end TangleDatum

omit [T2Space Shat] in
/-- A simple closed walk has no edges. -/
theorem GraphWalk.edges_of_closed {G : Drawing Shat} {a : Shat} (K : GraphWalk G.toGraph a a)
  (hs : K.IsSimple) : K.edges = [] := by
  cases K with
  | nil _ => rfl
  | cons hg t => exact absurd t.end_mem_support (List.nodup_cons.mp hs).1

namespace TangleDatum

variable {D : TangleDatum cap χ} {W : Set Shat} {H : Drawing Shat} {ρ : ℕ} {r : Shat} {Δv : Set
  Shat} {Dv F : Drawing Shat}
  {ord' : ℕ} {𝒯' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {Δ₀ Δ : Set Shat} {C :
    Drawing Shat} {h : Shat}

/-- The two forms of a sector in one shape. The spokes are `A₁ T₁` and `A₂ T₂`, and `A₁, A₂` are in
`D_v`. Each vertex of `D_v` other than `r*` is on `A₁`, on `A₂` or in `H`,
and step (8) holds: the ends of outer arcs are `r*` or on `A₁ ∪ A₂`. -/
structure IsShape (D : TangleDatum cap χ) (W : Set Shat) (H : Drawing Shat) (r : Shat)
  (Δv : Set Shat) (Dv F : Drawing Shat) {v₁ v₂ c₁ c₂ h₁ h₂ : Shat} (f₁ f₂ : Set Shat)
    (A₁ : GraphWalk D.rad.G.toGraph v₁ c₁) (A₂ : GraphWalk D.rad.G.toGraph v₂ c₂)
      (T₁ : GraphWalk D.rad.G.toGraph c₁ h₁) (T₂ : GraphWalk D.rad.G.toGraph c₂ h₂) : Prop where
  ne : v₁ ≠ v₂
  link₁ : D.rad.G.toGraph.IsLink f₁ r v₁
  link₂ : D.rad.G.toGraph.IsLink f₂ r v₂
  bd₁ : f₁ ⊆ discBd W
  bd₂ : f₂ ⊆ discBd W
  spoke₁ : D.IsSpokeWalk W H (A₁.append T₁)
  spoke₂ : D.IsSpokeWalk W H (A₂.append T₂)
  mem₁ : ∀ x ∈ A₁.support, x ∈ Dv.V
  mem₂ : ∀ x ∈ A₂.support, x ∈ Dv.V
  edge₁ : ∀ e ∈ A₁.edges, e ∈ Dv.E
  edge₂ : ∀ e ∈ A₂.edges, e ∈ Dv.E
  f₁_mem : f₁ ∈ Dv.E
  f₂_mem : f₂ ∈ Dv.E
  meet : ∀ x ∈ A₁.support, x ∈ A₂.support → x = c₁ ∧ x = c₂
  rest : ∀ x ∈ Dv.V, x ≠ r → x ∉ A₁.support → x ∉ A₂.support → x ∈ H.V
  outer_end : ∀ {a b : Shat} {Q : GraphWalk D.rad.G.toGraph a b}, IsArcOn D.rad.G Dv F Q →
    (∀ e ∈ Q.edges, Disjoint e Δv) → a = r ∨ a ∈ A₁.support ∨ a ∈ A₂.support

variable {v₁ v₂ c₁ c₂ h₁ h₂ : Shat} {f₁ f₂ : Set Shat} {A₁ : GraphWalk D.rad.G.toGraph v₁ c₁} {A₂ :
  GraphWalk D.rad.G.toGraph v₂ c₂} {T₁ : GraphWalk D.rad.G.toGraph c₁ h₁}
  {T₂ : GraphWalk D.rad.G.toGraph c₂ h₂}

omit [T2Space S] in
theorem IsShape.swap (s : D.IsShape W H r Δv Dv F f₁ f₂ A₁ A₂ T₁ T₂) : D.IsShape W H r Δv Dv F f₂
  f₁ A₂ A₁ T₂ T₁ where
  ne := s.ne.symm
  link₁ := s.link₂
  link₂ := s.link₁
  bd₁ := s.bd₂
  bd₂ := s.bd₁
  spoke₁ := s.spoke₂
  spoke₂ := s.spoke₁
  mem₁ := s.mem₂
  mem₂ := s.mem₁
  edge₁ := s.edge₂
  edge₂ := s.edge₁
  f₁_mem := s.f₂_mem
  f₂_mem := s.f₁_mem
  meet x h₁ h₂ := (s.meet x h₂ h₁).symm
  rest x hx hr h₁ h₂ := s.rest x hx hr h₂ h₁
  outer_end hQ ho := by
    rcases s.outer_end hQ ho with h' | h' | h'
    · exact .inl h'
    · exact .inr (.inr h')
    · exact .inr (.inl h')

namespace IsFar

/-- After step (7): the sector in its shape. In the fan form the two spokes share their tail. -/
theorem shape_cases (hf : D.IsFar W H ρ r Δv Dv ord' 𝒯' F Δ₀ C Δ h) :
    (∃ (v₁ v₂ u h' : Shat) (f₁ f₂ : Set Shat) (A₁ : GraphWalk D.rad.G.toGraph v₁ u)
      (A₂ : GraphWalk D.rad.G.toGraph v₂ u) (T : GraphWalk D.rad.G.toGraph u h'),
      D.IsShape W H r Δv Dv F f₁ f₂ A₁ A₂ T T ∧ D.IsFan W H ρ r f₁ f₂ A₁ A₂ T
        ∧ D.IsFanCircuit r f₁ f₂ A₁ A₂ Dv) ∨
    (∃ (v₁ v₂ h₁ h₂ : Shat) (f₁ f₂ : Set Shat) (K₁ : GraphWalk D.rad.G.toGraph v₁ h₁)
      (K₂ : GraphWalk D.rad.G.toGraph v₂ h₂) (P : Drawing Shat),
      D.IsShape W H r Δv Dv F f₁ f₂ K₁ K₂ (.nil (K₁.mem_vertexSet_of_mem_support
        K₁.end_mem_support)) (.nil (K₂.mem_vertexSet_of_mem_support K₂.end_mem_support)) ∧
      (∀ x ∈ K₁.support, x ∉ K₂.support) ∧ Drawing.IsPathOf P H h₁ h₂ ∧ IsEnclave D.tb D.ord D.𝒯 H
        ∧ H.E.ncard ≤ 4 * ρ + 4 ∧ P.U ⊆ Dv.U) := by
  have hx := hf.enc
  have hW := hx.wheel
  have hDv := hx.sector.Dv_circuit
  rcases IsBoundarySector.cases hW hx.hbdS hx.hin hx.sector with ⟨v₁, v₂, u, h', f₁, f₂, A₁, A₂, T,
    hfan, hC, hb₁, hb₂⟩ |
    ⟨v₁, v₂, h₁, h₂, f₁, f₂, K₁, K₂, P, hne, hl₁, hl₂, hb₁, hb₂, s₁, s₂, hdis, hP, hbd, -⟩
  · left
    refine ⟨v₁, v₂, u, h', f₁, f₂, A₁, A₂, T, ?_, hfan, hC⟩
    refine ⟨hfan.ne, hfan.link₁, hfan.link₂, hb₁, hb₂, hfan.spoke₁, hfan.spoke₂, fun x hx' ↦
      (hC.mem_V x).mpr (.inr (.inl hx')), fun x hx' ↦ (hC.mem_V x).mpr (.inr (.inr hx')),
      fun e he ↦ (hC.mem_E e).mpr (.inr (.inr (.inl he))), fun e he ↦ (hC.mem_E e).mpr (.inr (.inr
        (.inr he))), (hC.mem_E _).mpr (.inl rfl), (hC.mem_E _).mpr (.inr (.inl rfl)),
      fun x h₁ h₂ ↦ ⟨hfan.meet x h₁ h₂, hfan.meet x h₁ h₂⟩, fun x hx' hr h₁ h₂ ↦ ?_, fun {a b Q} hQ
        _ ↦ (hC.mem_V a).mp hQ.left⟩
    rcases (hC.mem_V x).mp hx' with h₀ | h₀ | h₀
    · exact absurd h₀ hr
    · exact absurd h₀ h₁
    · exact absurd h₀ h₂
  · right
    have hUform : (walkDrawing D.rad.G K₁).U ∪ (walkDrawing D.rad.G K₂).U ∪ P.U ∪ closure f₁ ∪
      closure f₂ = Dv.U := by
      rw [← hbd, hx.sector.Dv_U]
    have hend₁ := K₁.mem_vertexSet_of_mem_support K₁.end_mem_support
    have hend₂ := K₂.mem_vertexSet_of_mem_support K₂.end_mem_support
    have hne12 : h₁ ≠ h₂ := fun h' ↦ hdis h₁ K₁.end_mem_support (h' ▸ K₂.end_mem_support)
    have hHV₁ : h₁ ∈ H.V := s₁.2.h_mem
    have hHV₂ : h₂ ∈ H.V := s₂.2.h_mem
    have hHe : IsEnclave D.tb D.ord D.𝒯 H ∧ H.E.ncard ≤ 4 * ρ + 4 := by
      rcases hf.hub with ⟨hV, -⟩ | ⟨h₀, h₀', -⟩
      · rw [hV] at hHV₁ hHV₂
        exact absurd ((mem_singleton_iff.mp hHV₁).trans (mem_singleton_iff.mp hHV₂).symm) hne12
      · exact ⟨h₀, h₀'⟩
    have hedgeDv : ∀ {e : Set Shat}, e ∈ D.rad.G.E → e ⊆ Dv.U → e ∈ Dv.E := fun {e} heG hs ↦ by
      by_contra hn
      obtain ⟨x, hx'⟩ := heG.1
      exact disjoint_left.mp (edge_disjoint_U hDv.1 heG hn) hx' (hs hx')
    have hU₁ : (walkDrawing D.rad.G K₁).U ⊆ Dv.U := fun x hx' ↦ hUform ▸ .inl (.inl (.inl
      (.inl hx')))
    have hU₂ : (walkDrawing D.rad.G K₂).U ⊆ Dv.U := fun x hx' ↦ hUform ▸ .inl (.inl (.inl
      (.inr hx')))
    have hmemV : ∀ {a b : Shat} {K : GraphWalk D.rad.G.toGraph a b}, (walkDrawing D.rad.G K).U ⊆
      Dv.U → ∀ x ∈ K.support, x ∈ Dv.V := fun {a b K} hU x hx' ↦
      mem_V_of_mem_U hDv.1 (hU ((mem_walkDrawing_U _ _).mpr (.inl hx')))
        (K.mem_vertexSet_of_mem_support hx')
    have hmemE : ∀ {a b : Shat} {K : GraphWalk D.rad.G.toGraph a b}, (walkDrawing D.rad.G K).U ⊆
      Dv.U → ∀ e ∈ K.edges, e ∈ Dv.E := fun {a b K} hU e he ↦
      hedgeDv (TieBreaker.mem_edges_E K he) fun x hx' ↦ hU ((mem_walkDrawing_U _ _).mpr
        (.inr ⟨e, he, subset_closure hx'⟩))
    have hrest : ∀ x ∈ Dv.V, x ≠ r → x ∉ K₁.support → x ∉ K₂.support → x ∈ H.V ∧ x ∈ P.U
      := fun x hxV hr h₁' h₂' ↦ by
      have hxG : x ∈ D.rad.G.V := hDv.1.1 hxV
      have hsup : ∀ {u v : Shat} {K : GraphWalk D.rad.G.toGraph u v}, x ∈ (walkDrawing D.rad.G K).U
        → x ∈ K.support := fun {_ _ K} hu ↦ by
        have := mem_V_of_mem_U (walkDrawing_isSubdrawing D.rad.G K) hu hxG
        rw [walkDrawing_V] at this
        exact this
      have hclosV : ∀ {f : Set Shat} {y : Shat}, D.rad.G.toGraph.IsLink f r y → x ∈ closure f → x
        = r ∨ x = y := fun {f _} hl hc ↦ by
        have hm : x ∈ closure f ∩ D.rad.G.V := ⟨hc, hxG⟩
        rw [hl.2.2.2] at hm
        exact hm
      have hxU : x ∈ Dv.U := Dv.V_subset_U hxV
      rw [← hUform] at hxU
      rcases hxU with (((h₀ | h₀) | h₀) | h₀) | h₀
      · exact absurd (hsup h₀) h₁'
      · exact absurd (hsup h₀) h₂'
      · exact ⟨hP.1.1 (mem_V_of_mem_U (hP.1.trans hW.H_sub) h₀ hxG), h₀⟩
      · rcases hclosV hl₁ h₀ with h' | h'
        · exact absurd h' hr
        · exact absurd (h' ▸ K₁.start_mem_support) h₁'
      · rcases hclosV hl₂ h₀ with h' | h'
        · exact absurd h' hr
        · exact absurd (h' ▸ K₂.start_mem_support) h₂'
    have hs₁' : D.IsSpokeWalk W H (K₁.append (.nil hend₁)) := by
      simpa only [GraphWalk.append_nil'] using s₁
    have hs₂' : D.IsSpokeWalk W H (K₂.append (.nil hend₂)) := by
      simpa only [GraphWalk.append_nil'] using s₂
    refine ⟨v₁, v₂, h₁, h₂, f₁, f₂, K₁, K₂, P, ⟨hne, hl₁, hl₂, hb₁, hb₂, hs₁', hs₂', hmemV hU₁,
      hmemV hU₂, hmemE hU₁, hmemE hU₂,
      hedgeDv hl₁.1 (subset_closure.trans fun x hx' ↦ hUform ▸ .inl (.inr hx')), hedgeDv hl₂.1
        (subset_closure.trans fun x hx' ↦ hUform ▸ .inr hx'),
      fun x h₁' h₂' ↦ absurd h₂' (hdis x h₁'), fun x hx' hr h₁' h₂' ↦
        (hrest x hx' hr h₁' h₂').1, fun {a b Q} hQ ho ↦ ?_⟩, hdis, hP, hHe.1, hHe.2, fun x hx' ↦
          hUform ▸ .inl (.inl (.inr hx'))⟩
    by_contra hn
    push Not at hn
    exact hf.outer_end_path hl₁ hl₂ hb₁ hb₂ s₁ s₂ hdis hP hbd hQ ho hn.1 hn.2.1 hn.2.2

end IsFar

end TangleDatum

end GraphMinor.GM19
