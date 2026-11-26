/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section13p

/-!
# Graph Minors XIX, Section 13: tools for step (7) of (13.6)

A chord of `D_v` gives two circuits, and one of them still points to `𝒯'`. An edge at `r*` that
leaves `Δ_v` also leaves `W`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

section Tangle

variable {Γ : Painting S} {rad : RadialDrawing cap Γ} {ord' : ℕ} {𝒯' : Set (Hypergraph S
  (Set S) × Hypergraph S (Set S))}

/-- If two discs hold a third one, and the third points to `𝒯'`, then one of the two does. -/
theorem exists_small_side (hS : IsSurface S) (h3 : Γ.IsInternallyThreeConnected)
  (h𝒯' : IsTangle Γ.toHypergraph ord' 𝒯') {Dv C₁ C₂ : Drawing Shat} {Δd Δ₁ Δ₂ : Set Shat}
    (hDv : Dv.IsCircuitOf rad.G) (hΔd : IsClosedDisc Δd) (hbd : discBd Δd = Dv.U) (hmem :
      (partIn cap Γ (closure Δdᶜ), partIn cap Γ Δd) ∈ 𝒯')
    (hc₁ : C₁.IsCircuitOf rad.G) (hΔ₁ : IsClosedDisc Δ₁) (hb₁ : discBd Δ₁ = C₁.U)
      (hc₂ : C₂.IsCircuitOf rad.G) (hΔ₂ : IsClosedDisc Δ₂) (hb₂ : discBd Δ₂ = C₂.U)
    (hcov : Δd ⊆ Δ₁ ∪ Δ₂) (ho₁ : C₁.E.ncard < 2 * ord') (ho₂ : C₂.E.ncard < 2 * ord') :
    (partIn cap Γ (closure Δ₁ᶜ), partIn cap Γ Δ₁) ∈ 𝒯' ∨ (partIn cap Γ
      (closure Δ₂ᶜ), partIn cap Γ Δ₂) ∈ 𝒯' := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  by_contra hn
  push Not at hn
  have hs₁ : Γ.toHypergraph.IsSeparation (partIn cap Γ Δ₁) (partIn cap Γ (closure Δ₁ᶜ)) :=
    (disc_facts hS h3 rad hc₁ hΔ₁ hb₁).1
  have hs₂ : Γ.toHypergraph.IsSeparation (partIn cap Γ Δ₂) (partIn cap Γ (closure Δ₂ᶜ)) :=
    (disc_facts hS h3 rad hc₂ hΔ₂ hb₂).1
  have e₁ := disc_order hS h3 rad hc₁ hΔ₁ hb₁
  have e₂ := disc_order hS h3 rad hc₂ hΔ₂ hb₂
  have m₁ := (h𝒯'.axiom1 hs₁ (by omega)).resolve_right hn.1
  have m₂ := (h𝒯'.axiom1 hs₂ (by omega)).resolve_right hn.2
  have hc := part_cover rad hDv.1 hc₁.1 hc₂.1 (isSide_out hT hΔd hbd) (isSide_int hT hΔ₁ hb₁)
    (isSide_int hT hΔ₂ hb₂) fun x ↦ by
    rw [closure_discInt hΔ₁, closure_discInt hΔ₂]
    by_cases hx : x ∈ Δd
    · rcases hcov hx with h₁ | h₁
      · exact .inr (.inl h₁)
      · exact .inr (.inr h₁)
    · exact .inl (subset_closure hx)
  rw [closure_discInt hΔ₁, closure_discInt hΔ₂] at hc
  exact h𝒯'.axiom2 hmem m₁ m₂ hc

end Tangle

omit [T2Space Shat] in
theorem GraphWalk.append_nil' {G : Drawing Shat} {a b : Shat} (M : GraphWalk G.toGraph a b)
  (h : b ∈ G.toGraph.vertexSet) : M.append (.nil h) = M := by
  induction M with
  | nil _ => rfl
  | cons hl r ih => exact congrArg (GraphWalk.cons hl) (ih h)

/-- If two walks cut a circuit, a walk between the same ends that misses the circuit gives a theta.
-/
theorem Splits.twoPaths {G F : Drawing Shat} {a b : Shat} {W₁ : GraphWalk G.toGraph a b} {W₂ :
  GraphWalk G.toGraph b a} (hs : Splits F W₁ W₂) (hab : a ≠ b)
    (hF : F.IsSubdrawing G) {Q : GraphWalk G.toGraph a b} (hQ : Q.IsSimple)
      (hV : ∀ x ∈ Q.support, x ∈ F.V → x = a ∨ x = b) (hE : ∀ e ∈ Q.edges, e ∉ F.E) :
    TwoPaths G F (walkDrawing G W₁) (walkDrawing G W₂.reverse) (walkDrawing G Q) a b := by
  have hrevV : ∀ x, x ∈ (walkDrawing G W₂.reverse).V ↔ x ∈ W₂.support := fun x ↦ by
    rw [walkDrawing_V]
    change x ∈ W₂.reverse.support ↔ _
    rw [GraphWalk.support_reverse, List.mem_reverse]
  have hrevE : ∀ e, e ∈ (walkDrawing G W₂.reverse).E ↔ e ∈ W₂.edges := fun e ↦ by
    rw [walkDrawing_E]
    change e ∈ W₂.reverse.edges ↔ _
    rw [GraphWalk.edges_reverse, List.mem_reverse]
  have hV₁ : ∀ x, x ∈ (walkDrawing G W₁).V ↔ x ∈ W₁.support := fun x ↦ by rw [walkDrawing_V]; rfl
  have hE₁ : ∀ e, e ∈ (walkDrawing G W₁).E ↔ e ∈ W₁.edges := fun e ↦ by rw [walkDrawing_E]; rfl
  refine ⟨hab, hF, ⟨⟨fun x hx ↦ (hs.V x).mpr (.inl ((hV₁ x).mp hx)),
    fun e he ↦ (hs.E e).mpr (.inl ((hE₁ e).mp he))⟩, walkDrawing_isPathBetween G hs.s₁⟩,
    ⟨⟨fun x hx ↦ (hs.V x).mpr (.inr ((hrevV x).mp hx)), fun e he ↦ (hs.E e).mpr (.inr
      ((hrevE e).mp he))⟩, walkDrawing_isPathBetween G hs.s₂.reverse⟩, ?_, ?_, ?_, ?_,
    ⟨walkDrawing_isSubdrawing _ _, walkDrawing_isPathBetween _ hQ⟩, ?_, ?_⟩
  · ext x
    rw [hs.V x, mem_union, hV₁, hrevV]
  · ext e
    rw [hs.E e, mem_union, hE₁, hrevE]
  · rintro x ⟨h₁, h₂⟩
    exact hs.meet x ((hV₁ x).mp h₁) ((hrevV x).mp h₂)
  · exact disjoint_left.mpr fun e h₁ h₂ ↦ hs.edge e ((hE₁ e).mp h₁) ((hrevE e).mp h₂)
  · rintro x ⟨h₁, h₂⟩
    have : x ∈ Q.support := by simpa [walkDrawing_V] using h₁
    exact hV x this h₂
  · refine disjoint_left.mpr fun e h₁ h₂ ↦ hE e ?_ h₂
    simpa [walkDrawing_E] using h₁

namespace TangleDatum

variable {D : TangleDatum cap χ} {W : Set Shat} {H : Drawing Shat} {ρ : ℕ} {r : Shat} {Δv : Set
  Shat} {Dv F : Drawing Shat}
  {ord' : ℕ} {𝒯' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {Δ₀ Δ : Set Shat} {C :
    Drawing Shat} {h : Shat}

/-- A spoke meets `bd(W)` only in its first vertex. -/
theorem IsSpokeWalk.meet_bd (hW : D.IsWheelHubOfRadius W H ρ) (hbdS : discBd W ⊆ cap.emb ''
  (univ \ bd S))
    (hin : ((W \ discBd W) ∩ (cap.emb '' D.Γ.V)).Nonempty) {v h x : Shat} {K : GraphWalk
      D.rad.G.toGraph v h} (hK : D.IsSpokeWalk W H K)
    (hx : x ∈ (walkDrawing D.rad.G K).U) (hxb : x ∈ discBd W) : x = v := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  rw [mem_walkDrawing_U] at hx
  by_contra hne
  have hvert : ∀ y ∈ K.support, y ∈ discBd W → y = v := fun y hy hb ↦ by
    by_contra hn
    exact hK.tail_off_bd hW hbdS hin hy hn hb
  rcases hx with hx | ⟨e, he, hxe⟩
  · exact hne (hvert x hx hxb)
  · obtain ⟨p, q, hl, A, B, rfl⟩ := GraphWalk.exists_split_edge K he
    have hps : p ∈ (A.append (GraphWalk.cons hl B)).support := (GraphWalk.mem_support_append _
      _).mpr (.inl A.end_mem_support)
    have hqs : q ∈ (A.append (GraphWalk.cons hl B)).support := (GraphWalk.mem_support_append _
      _).mpr (.inr (by simp [B.start_mem_support]))
    have hpq : p ≠ q := by
      have hc : (GraphWalk.cons hl B).support.Nodup := (isSimple_of_append hK.1).2
      rw [GraphWalk.support_cons, List.nodup_cons] at hc
      exact fun h' ↦ hc.1 (h' ▸ B.start_mem_support)
    rcases closure_edge_subset hl.1 hxe with hxe' | hxV
    · obtain ⟨B', hBc, hBs, hBU⟩ := exists_circuit_of_oArc hW.is_disc.isOArc_discBd hW.bd_sub
      have heB : e ∈ B'.E := by
        by_contra hn
        exact disjoint_left.mp (edge_disjoint_U hBs hl.1 hn) hxe' (hBU ▸ hxb)
      have hb₁ : p ∈ discBd W := hBU ▸ B'.closure_subset_U heB (IsLink.left_mem_closure hl)
      have hb₂ : q ∈ discBd W := hBU ▸ B'.closure_subset_U heB (IsLink.right_mem_closure hl)
      exact hpq ((hvert p hps hb₁).trans (hvert q hqs hb₂).symm)
    · have hm : x ∈ closure e ∩ D.rad.G.V := ⟨hxe, hxV⟩
      rw [hl.2.2.2] at hm
      rcases hm with rfl | rfl
      · exact hne (hvert _ hps hxb)
      · exact hne (hvert _ hqs hxb)

/-- An edge at `r*` that misses `Δ_v` is not in `W`. The discs `Δ_v ⊆ W` meet along `f₁ ∪ f₂` on
their boundaries, so `closure (W \ Δ_v)` misses `r*`. -/
theorem IsFan.edge_off_W {v₁ v₂ u h : Shat} {f₁ f₂ : Set Shat} {A₁ : GraphWalk D.rad.G.toGraph v₁
  u} {A₂ : GraphWalk D.rad.G.toGraph v₂ u}
    {T : GraphWalk D.rad.G.toGraph u h} (hf : D.IsFan W H ρ r f₁ f₂ A₁ A₂ T)
      (hC : D.IsFanCircuit r f₁ f₂ A₁ A₂ Dv) (hb₁ : f₁ ⊆ discBd W) (hb₂ : f₂ ⊆ discBd W)
    (hΔ : IsClosedDisc Δv) (hbv : discBd Δv = Dv.U) (hsub : Δv ⊆ W) {g : Set Shat}
      (hr : r ∈ closure g) (hd : Disjoint g Δv) : ¬ g ⊆ W := by
  classical
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hW := hf.hub
  have hne := hf.ne
  have hl₁ := hf.link₁
  have hl₂ := hf.link₂
  have hvr₁ : r ≠ v₁ := fun h' ↦ hf.r_mem.2 (h' ▸ hf.spoke₁.2.v_mem.1)
  have hvr₂ : r ≠ v₂ := fun h' ↦ hf.r_mem.2 (h' ▸ hf.spoke₂.2.v_mem.1)
  let N : GraphWalk D.rad.G.toGraph v₁ v₂ := .cons (IsLink.symm' hl₁) (.cons hl₂ (.nil hl₂.2.2.1))
  have hNs : N.IsSimple := by
    change [v₁, r, v₂].Nodup
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true]
    exact ⟨⟨hvr₁.symm, hne⟩, hvr₂, not_false⟩
  have hNU : ∀ x, x ∈ (walkDrawing D.rad.G N).U ↔ x ∈ closure f₁ ∨ x ∈ closure f₂ := fun x ↦ by
    rw [mem_walkDrawing_U]
    constructor
    · rintro (hx | ⟨e, he, hxe⟩)
      · change x ∈ [v₁, r, v₂] at hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact .inl (IsLink.right_mem_closure hl₁)
        · exact .inl (IsLink.left_mem_closure hl₁)
        · exact .inr (IsLink.right_mem_closure hl₂)
      · change e ∈ [f₁, f₂] at he
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl
        · exact .inl hxe
        · exact .inr hxe
    · rintro (hx | hx)
      · exact .inr ⟨f₁, List.mem_cons_self, hx⟩
      · exact .inr ⟨f₂, List.mem_cons_of_mem _ List.mem_cons_self, hx⟩
  have hline := isLine_of_isPathBetween (walkDrawing_isPathBetween D.rad.G hNs) hne
  have hbf : frontier W = discBd W := IsClosedDisc.frontier_eq_discBd hT hW.is_disc
  have hcl : ∀ {f : Set Shat}, f ⊆ discBd W → closure f ⊆ discBd W := fun hf ↦ closure_minimal hf
    (hbf ▸ isClosed_frontier)
  have hU := hf.U_eq hC
  have hmeet : discBd Δv ∩ discBd W = (walkDrawing D.rad.G N).U := by
    apply Subset.antisymm
    · rintro x ⟨hx, hxb⟩
      rw [hbv, hU] at hx
      rw [hNU]
      rcases hx with ((hx | hx) | hx) | hx
      · have hxv := IsSpokeWalk.meet_bd hW hf.bd_off hf.inner hf.spoke₁ (by
          rw [U_append]
          exact .inl hx) hxb
        exact .inl (hxv ▸ IsLink.right_mem_closure hl₁)
      · have hxv := IsSpokeWalk.meet_bd hW hf.bd_off hf.inner hf.spoke₂ (by
          rw [U_append]
          exact .inl hx) hxb
        exact .inr (hxv ▸ IsLink.right_mem_closure hl₂)
      · exact .inl hx
      · exact .inr hx
    · intro x hx
      rcases (hNU x).mp hx with h₁ | h₁
      · exact ⟨by rw [hbv, hU]; exact .inl (.inr h₁), hcl hb₁ h₁⟩
      · exact ⟨by rw [hbv, hU]; exact .inr h₁, hcl hb₂ h₁⟩
  obtain ⟨-, -, hdiff⟩ := disc_difference Δv W _ v₁ v₂ hΔ hW.is_disc hsub hline hmeet
  intro hgW
  have hr₁ : r ∈ closure (W \ Δv) := closure_mono (show g ⊆ W \ Δv from fun x hx ↦ ⟨hgW hx,
    disjoint_left.mp hd hx⟩) hr
  have hrL : r ∈ (walkDrawing D.rad.G N).U := (hNU r).mpr (.inl (IsLink.left_mem_closure hl₁))
  have hrΔ : r ∈ Δv := by
    have : r ∈ discBd Δv := by
      rw [hbv, hU]
      exact .inl (.inr (IsLink.left_mem_closure hl₁))
    exact Surface.discBd_subset _ this
  have hm : r ∈ closure (W \ Δv) ∩ Δv := ⟨hr₁, hrΔ⟩
  rw [hdiff] at hm
  refine hm.2 ⟨hrL, ?_⟩
  rintro (h' | h')
  · exact hvr₁ h'
  · exact hvr₂ h'

/-- A chord of `D_v` that is short enough cannot exist: its two circuits are shorter than `F`, and
one of them points to `𝒯'`, so `F` would not be the distinction. -/
theorem IsSectorEnclave.no_short_chord (hx : D.IsSectorEnclave W H ρ r Δv Dv ord' 𝒯' F) {a b :
  Shat} {W₁ : GraphWalk D.rad.G.toGraph a b}
    {W₂ : GraphWalk D.rad.G.toGraph b a} (hs : Splits Dv W₁ W₂) (hab : a ≠ b) {Q : GraphWalk
      D.rad.G.toGraph a b} (hQ : Q.IsSimple)
    (hV : ∀ x ∈ Q.support, x ∈ Dv.V → x = a ∨ x = b) (hE : ∀ e ∈ Q.edges, e ∉ Dv.E)
      (h₁ : Q.length + W₁.length < F.E.ncard)
    (h₂ : Q.length + W₂.length < F.E.ncard) : False := by
  have : ConnectedSpace Shat := cap.connected
  have hS := χ.isSurface
  have h3 := D.P.fits.internally_three_connected
  have hDv := hx.sector.Dv_circuit
  have ht := Splits.twoPaths hs hab hDv.1 hQ hV hE
  have hFc := hx.F_card
  have hrep := hx.hrep
  have hρ := hx.wheel.pos_ρ
  have hE₁ : (walkDrawing D.rad.G W₁).E.ncard = W₁.length := ncard_walk_E _ hs.s₁
  have hE₂ : (walkDrawing D.rad.G W₂.reverse).E.ncard = W₂.length := by
    rw [ncard_walk_E _ hs.s₂.reverse, GraphWalk.length_reverse]
  have hEQ : (walkDrawing D.rad.G Q).E.ncard = Q.length := ncard_walk_E _ hQ
  have hc : ∀ X : Drawing Shat, Disjoint (walkDrawing D.rad.G Q).E X.E → X.IsSubdrawing D.rad.G →
    (D.rad.G.sup (walkDrawing D.rad.G Q) X).E.ncard = Q.length + X.E.ncard := fun X hd hX ↦ by
    rw [Drawing.sup_E (walkDrawing_isSubdrawing _ _) hX, ncard_union_eq hd
      (walkDrawing _ _).finite_edges X.finite_edges, hEQ]
  have hdis : ∀ {X : Drawing Shat}, X.E ⊆ Dv.E → Disjoint (walkDrawing D.rad.G Q).E X.E := fun hX ↦
    disjoint_of_subset_right hX ht.meet_E
  have c₁ := hc _ (hdis ht.left.1.2) ht.sub₁
  have c₂ := hc _ (hdis ht.right.1.2) ht.sub₂
  have hC₁ : Drawing.IsCircuitOf (D.rad.G.sup (walkDrawing D.rad.G Q)
    (walkDrawing D.rad.G W₁)) D.rad.G := ⟨D.rad.G.sup_isSubdrawing _ _, ht.swap.left_circuit⟩
  have hC₂ : Drawing.IsCircuitOf (D.rad.G.sup (walkDrawing D.rad.G Q)
    (walkDrawing D.rad.G W₂.reverse)) D.rad.G := ⟨D.rad.G.sup_isSubdrawing _ _, ht.left_circuit⟩
  have l₁ : (D.rad.G.sup (walkDrawing D.rad.G Q) (walkDrawing D.rad.G W₁)).E.ncard < F.E.ncard := by
    omega
  have l₂ : (D.rad.G.sup (walkDrawing D.rad.G Q) (walkDrawing D.rad.G W₂.reverse)).E.ncard <
    F.E.ncard := by omega
  have i₁ := D.ins_spec hC₁ (by omega)
  have i₂ := D.ins_spec hC₂ (by omega)
  have hcov := D.ins_theta (by omega) ht hDv (by omega) (by omega) (by omega)
  rw [hx.ins_Dv] at hcov
  have hFi := hx.isInsOf_F
  have hd := hx.distinction
  have hordF : F.E.ncard < 2 * ord' := by
    have h₀ := hx.isTangle'.order_lt hd.1.2
    have e₀ : F.E.ncard = 2 * Hypergraph.separationOrder (partIn cap D.Γ (D.ins F)) (partIn cap D.Γ
      (closure (D.ins F)ᶜ)) := disc_order hS h3 D.rad hFi.1 hFi.2.2.1 hFi.2.2.2.1
    have hcomm : Hypergraph.separationOrder (partIn cap D.Γ (closure (D.ins F)ᶜ)) (partIn cap D.Γ
      (D.ins F)) =
        Hypergraph.separationOrder (partIn cap D.Γ (D.ins F)) (partIn cap D.Γ (closure (D.ins F)ᶜ))
          := by
      simp only [Hypergraph.separationOrder, GM10.inter_comm]
    omega
  rcases exists_small_side hS h3 hx.isTangle' hDv hx.sector.is_disc hx.sector.Dv_U.symm hx.mem hC₁
    i₁.2.2.1 i₁.2.2.2.1 hC₂ i₂.2.2.1 i₂.2.2.2.1 hcov (by omega) (by omega) with h | h
  · have := enclave_card_le hS h3 D.tb hFi hd i₁ h
    omega
  · have := enclave_card_le hS h3 D.tb hFi hd i₂ h
    omega

end TangleDatum

end GraphMinor.GM19
