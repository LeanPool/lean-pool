/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section13u

/-!
# Graph Minors XIX, Section 13: tools for steps (12) to (14) of (13.6)

If a disc holds what `ins(F)` and `Δ_v` have in common, then its boundary is at least as long as
`F`. A walk from `r*` to the spoke that replaces the start of the spoke is longer, by
(13.1) and parity. And `F` has a third arc, from `r*` to the second spoke, that does not meet the
first spoke.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

omit [T2Space Shat] in
theorem GraphWalk.reverse_append' {G : Drawing Shat} {a b c : Shat} (A : GraphWalk G.toGraph a b)
  (B : GraphWalk G.toGraph b c) : (A.append B).reverse = B.reverse.append A.reverse := by
  induction A with
  | nil h => exact (GraphWalk.append_nil' B.reverse h).symm
  | cons h r ih =>
    change (r.append B).reverse.append _ = B.reverse.append (r.reverse.append _)
    rw [ih, GraphWalk.append_assoc']

/-- A point off the interior of a disc is in the closure of the complement. -/
theorem mem_closure_compl_of_notMem_discInt {T : Type} [TopologicalSpace T]
  (hT : IsClosedSurface T) {Δ : Set T} (hΔ : IsClosedDisc Δ) {x : T}
    (hx : x ∉ discInt Δ) : x ∈ closure Δᶜ := by
  by_cases hm : x ∈ Δ
  · have hb : x ∈ discBd Δ := by_contra fun hn ↦ hx ⟨hm, hn⟩
    rw [← IsClosedDisc.frontier_eq_discBd hT hΔ, frontier_eq_closure_inter_closure] at hb
    exact hb.2
  · exact subset_closure hm

namespace TangleDatum

variable {D : TangleDatum cap χ} {W : Set Shat} {H : Drawing Shat} {ρ : ℕ} {r : Shat} {Δv : Set
  Shat} {Dv F : Drawing Shat}
  {ord' : ℕ} {𝒯' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {Δ₀ Δ : Set Shat} {C :
    Drawing Shat} {h : Shat}

/-- `F` is smaller than the order of `𝒯'`, by the bound on its separation. -/
theorem IsSectorEnclave.F_lt_order (hx : D.IsSectorEnclave W H ρ r Δv Dv ord' 𝒯' F) : F.E.ncard < 2
  * ord' := by
  have : ConnectedSpace Shat := cap.connected
  have hS := χ.isSurface
  have h3 := D.P.fits.internally_three_connected
  have hFi := hx.isInsOf_F
  have hd := hx.distinction
  have h₀ := hx.isTangle'.order_lt hd.1.2
  have e₀ : F.E.ncard = 2 * Hypergraph.separationOrder (partIn cap D.Γ (D.ins F)) (partIn cap D.Γ
    (closure (D.ins F)ᶜ)) := disc_order hS h3 D.rad hFi.1 hFi.2.2.1 hFi.2.2.2.1
  have hcomm : Hypergraph.separationOrder (partIn cap D.Γ (closure (D.ins F)ᶜ)) (partIn cap D.Γ
    (D.ins F)) =
      Hypergraph.separationOrder (partIn cap D.Γ (D.ins F)) (partIn cap D.Γ (closure (D.ins F)ᶜ))
        := by
    simp only [Hypergraph.separationOrder, GM10.inter_comm]
  omega

/-- If a disc contains the common interior of `ins(F)` and `Δ_v`, then its boundary is at least as
long as `F`: it points to `𝒯'` by the second tangle axiom, so the choice of `F` applies. -/
theorem IsSectorEnclave.card_le_of_cover (hx : D.IsSectorEnclave W H ρ r Δv Dv ord' 𝒯' F) {C' :
  Drawing Shat} {Δc : Set Shat} (hins : IsInsOf D.rad D.ord D.𝒯 C' Δc)
    (hcov : ∀ y, y ∈ discInt Δv → y ∈ discInt (D.ins F) → y ∈ Δc) : F.E.ncard ≤ C'.E.ncard := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hS := χ.isSurface
  have h3 := D.P.fits.internally_three_connected
  have hFi := hx.isInsOf_F
  have hd := hx.distinction
  have hDv := hx.sector.Dv_circuit
  have hΔv := hx.sector.is_disc
  have hbv := hx.sector.Dv_U.symm
  have hc := hins.1
  have hΔc := hins.2.2.1
  have hbc := hins.2.2.2.1
  by_cases hbig : 2 * ord' ≤ C'.E.ncard
  · have := hx.F_lt_order
    omega
  have hsep : D.Γ.toHypergraph.IsSeparation (partIn cap D.Γ Δc) (partIn cap D.Γ (closure Δcᶜ)) :=
    (disc_facts hS h3 D.rad hc hΔc hbc).1
  have e₀ : C'.E.ncard = 2 * Hypergraph.separationOrder (partIn cap D.Γ Δc) (partIn cap D.Γ
    (closure Δcᶜ)) := disc_order hS h3 D.rad hc hΔc hbc
  rcases hx.isTangle'.axiom1 hsep (by omega) with hm | hm
  · exfalso
    have hcov' := part_cover D.rad hc.1 hDv.1 hFi.1.1 (isSide_int hT hΔc hbc)
      (isSide_out hT hΔv hbv) (isSide_out hT hFi.2.2.1 hFi.2.2.2.1) fun y ↦ by
      rw [closure_discInt hΔc]
      by_cases h₁ : y ∈ discInt Δv
      · by_cases h₂ : y ∈ discInt (D.ins F)
        · exact .inl (hcov y h₁ h₂)
        · exact .inr (.inr (mem_closure_compl_of_notMem_discInt hT hFi.2.2.1 h₂))
      · exact .inr (.inl (mem_closure_compl_of_notMem_discInt hT hΔv h₁))
    rw [closure_discInt hΔc] at hcov'
    exact hx.isTangle'.axiom2 hm hx.mem hd.1.2 hcov'
  · exact enclave_card_le hS h3 D.tb hFi hd hins hm

/-- By (13.1), a walk from `r*` to the hub has at least `ρ` edges. -/
theorem IsWheelHubOfRadius.walk_from_rstar (hW : D.IsWheelHubOfRadius W H ρ)
  (hbdS : discBd W ⊆ cap.emb '' (univ \ bd S)) (hin : ((W \ discBd W) ∩
    (cap.emb '' D.Γ.V)).Nonempty)
    (hr : r ∈ D.rad.Rstar ∩ discBd W) {z : Shat} (hz : z ∈ H.V) (L : GraphWalk D.rad.G.toGraph r z)
      : ρ ≤ L.length := by
  obtain ⟨P, hP, hle⟩ := exists_path_of_walk L
  by_contra hn
  exact theorem_13_1_proof hW hbdS hin hr.1 hr.2 ⟨P, z, hz, hP, by omega⟩

variable {v₁ v₂ c₁ c₂ h₁ h₂ : Shat} {f₁ f₂ : Set Shat} {A₁ : GraphWalk D.rad.G.toGraph v₁ c₁} {A₂ :
  GraphWalk D.rad.G.toGraph v₂ c₂} {T₁ : GraphWalk D.rad.G.toGraph c₁ h₁}
  {T₂ : GraphWalk D.rad.G.toGraph c₂ h₂}

/-- Step (14) of the proof of (13.6): a walk from `r*` to a vertex `b` of `A₁` is longer than the
part of `A₁` before `b`. -/
theorem IsShape.parity_bound (hf : D.IsFar W H ρ r Δv Dv ord' 𝒯' F Δ₀ C Δ h)
  (s : D.IsShape W H r Δv Dv F f₁ f₂ A₁ A₂ T₁ T₂) {b : Shat} (Q : GraphWalk D.rad.G.toGraph r b)
    {X : GraphWalk D.rad.G.toGraph v₁ b} {Z : GraphWalk D.rad.G.toGraph b c₁} (hA : A₁
      = X.append Z) : X.length + 1 ≤ Q.length := by
  have : ConnectedSpace Shat := cap.connected
  have hx := hf.enc
  have hW := hx.wheel
  have hb := IsWheelHubOfRadius.walk_from_rstar hW hx.hbdS hx.hin hx.sector.rstar_mem
    s.spoke₁.2.h_mem (Q.append (Z.append T₁))
  have hl := (hW.spoke_length s.spoke₁).1
  have e₁ := D.even_length_walk (A₁.append T₁)
  have e₂ := D.even_length_walk (Q.append (Z.append T₁))
  have hr : r ∉ D.P.Γ.hatV cap := hx.sector.rstar_mem.1.2
  have hv : v₁ ∈ D.P.Γ.hatV cap := s.spoke₁.2.v_mem.1
  have hne : (A₁.append T₁).length ≠ (Q.append (Z.append T₁)).length := fun h' ↦ by
    rw [h'] at e₁
    have h₃ := e₁.symm.trans e₂
    tauto
  rw [GraphWalk.length_append, hA, GraphWalk.length_append] at hne hl
  rw [GraphWalk.length_append, GraphWalk.length_append] at hb hne
  omega

namespace IsFar

/-- `F` closes up from `r*` along `Q₁`, `A₁` and `Q₀` through a third walk `F₂` from `r*` to `A₂`,
which meets `A₂` only at its end, does not meet `A₁`, has no edge in `Q₀ ∪ Q₁`,
and has an edge inside `Δ_v`. -/
theorem exists_third (hf : D.IsFar W H ρ r Δv Dv ord' 𝒯' F Δ₀ C Δ h) (s : D.IsShape W H r Δv Dv F
  f₁ f₂ A₁ A₂ T₁ T₂) (hten : ∀ x ∈ A₁.support, x ∈ A₂.support → x ∉ F.V) {b₁ a₀ b₀ : Shat}
    {Q₁ : GraphWalk D.rad.G.toGraph r b₁} {Q₀ : GraphWalk D.rad.G.toGraph a₀ b₀}
      (h₁' : IsArcOn D.rad.G Dv F Q₁) (h₀ : IsArcOn D.rad.G Dv F Q₀) (o₁ : ∀ e ∈ Q₁.edges, Disjoint
        e Δv)
    (o₀ : ∀ e ∈ Q₀.edges, Disjoint e Δv) (hd : ∀ e ∈ Q₀.edges, e ∉ Q₁.edges)
      (hb₁ : b₁ ∈ A₁.support) (ha₀ : a₀ ∈ A₁.support) (hb₀ : b₀ ∈ A₂.support) :
    ∃ (b₂ : Shat) (F₂ : GraphWalk D.rad.G.toGraph r b₂), b₂ ∈ A₂.support ∧ F₂.IsSimple ∧
      (∀ e ∈ F₂.edges, e ∈ F.E ∧ e ∉ Q₁.edges ∧ e ∉ Q₀.edges) ∧ (∀ x ∈ F₂.support, x ∈ A₂.support
        → x = b₂) ∧
      (∀ x ∈ F₂.support, x ∉ A₁.support) ∧ (∃ e ∈ F₂.edges, e ⊆ discInt Δv)
        ∧ ∀ e ∈ F.E, e ∈ F₂.edges ∨ e ∈ Q₁.edges ∨ e ∈ Q₀.edges ∨ e ∈ Dv.E := by
  classical
  have : ConnectedSpace Shat := cap.connected
  have hx := hf.enc
  have hW := hx.wheel
  have hFi := hx.isInsOf_F
  have hFc := hFi.1
  have hFs := hFc.1
  have hE := hx.isEnclave
  have hb₁F := h₁'.mem_F hFs _ Q₁.end_mem_support
  have hrF := h₁'.mem_F hFs _ Q₁.start_mem_support
  have ha₀F := h₀.mem_F hFs _ Q₀.start_mem_support
  have hb₀F := h₀.mem_F hFs _ Q₀.end_mem_support
  have hrA₁ : r ∉ A₁.support := fun h' ↦ IsWheelHubOfRadius.r_notMem_spoke hW hx.hbdS hx.hin
    hx.sector.rstar_mem s.spoke₁ ((GraphWalk.mem_support_append _ _).mpr (.inl h'))
  have hrA₂ : r ∉ A₂.support := fun h' ↦ IsWheelHubOfRadius.r_notMem_spoke hW hx.hbdS hx.hin
    hx.sector.rstar_mem s.spoke₂ ((GraphWalk.mem_support_append _ _).mpr (.inl h'))
  have hb₀A₁ : b₀ ∉ A₁.support := fun h' ↦ hten b₀ h' hb₀ hb₀F
  obtain ⟨Y₁, hY₁s, hY₁, hY₁A⟩ := s.exists_seg hE hb₁ ha₀ hb₁F ha₀F
  have hYQ : ∀ y ∈ Y₁.support, y ∈ Q₀.support → y = a₀ := fun y hy hy' ↦
    (h₀.inner y hy' (s.mem₁ y (hY₁A y hy))).resolve_right fun h' ↦ hb₀A₁ (h' ▸ hY₁A y hy)
  have hs₂ : (Y₁.append Q₀).IsSimple := isSimple_append' hY₁s h₀.simple hYQ
  have hmeet : ∀ y ∈ Q₁.support, y ∈ (Y₁.append Q₀).support → y = b₁ := fun y hy hy' ↦ by
    rcases (GraphWalk.mem_support_append _ _).mp hy' with h' | h'
    · exact (h₁'.inner y hy (s.mem₁ y (hY₁A y h'))).resolve_left fun h'' ↦ hrA₁ (h'' ▸ hY₁A y h')
    · by_cases hyD : y ∈ Dv.V
      · refine (h₁'.inner y hy hyD).resolve_left fun h'' ↦ ?_
        rcases h₀.inner y h' hyD with h₃ | h₃
        · exact hrA₁ (h'' ▸ h₃ ▸ ha₀)
        · exact hrA₂ (h'' ▸ h₃ ▸ hb₀)
      · exfalso
        have hne₁ : a₀ ≠ y := fun h₃ ↦ hyD (h₃ ▸ h₀.left)
        have hne₂ : y ≠ b₀ := fun h₃ ↦ hyD (h₃ ▸ h₀.right)
        obtain ⟨L₁, L₂, hL⟩ := Q₀.exists_append_of_mem h'
        obtain ⟨e₁, he₁, hc₁⟩ := GraphWalk.exists_edge_at_end L₁ hne₁
        obtain ⟨e₂, he₂, hc₂⟩ := GraphWalk.exists_edge_at_start L₂ hne₂
        obtain ⟨e₃, he₃, hc₃⟩ := GraphWalk.exists_edge_of_support Q₁ h₁'.ne hy
        have hm₁ : e₁ ∈ Q₀.edges := by
          rw [hL, GraphWalk.edges_append]
          exact List.mem_append_left _ he₁
        have hm₂ : e₂ ∈ Q₀.edges := by
          rw [hL, GraphWalk.edges_append]
          exact List.mem_append_right _ he₂
        exact no_three_edges hFc D.edge_two_ends (h₀.mem_F hFs y h') (h₀.inF _ hm₁) (h₀.inF _ hm₂)
          (h₁'.inF _ he₃) hc₁ hc₂ hc₃ (fun h₄ ↦ Splits.append_edge (hL ▸ h₀.simple) he₁ (h₄ ▸ he₂))
          (fun h₄ ↦ hd _ hm₁ (h₄ ▸ he₃)) (fun h₄ ↦ hd _ hm₂ (h₄ ▸ he₃))
  have hZs : (Q₁.append (Y₁.append Q₀)).IsSimple := isSimple_append' h₁'.simple hs₂ hmeet
  have hZE : ∀ e, e ∈ (Q₁.append (Y₁.append Q₀)).edges ↔ e ∈ Q₁.edges ∨ e ∈ Y₁.edges ∨ e ∈ Q₀.edges
    := fun e ↦ by
    rw [GraphWalk.edges_append, List.mem_append, GraphWalk.edges_append, List.mem_append]
  have hZF : ∀ e ∈ (Q₁.append (Y₁.append Q₀)).edges, e ∈ F.E := fun e he ↦ by
    rcases (hZE e).mp he with h' | h' | h'
    · exact h₁'.inF e h'
    · exact (hY₁ e h').2
    · exact h₀.inF e h'
  have hrb₀ : r ≠ b₀ := fun h' ↦ hrA₂ (h' ▸ hb₀)
  obtain ⟨W₁, W₂, h₀s⟩ := exists_splits hFc.2 hFc.1 hrF hb₀F hrb₀
  obtain ⟨R', hR⟩ := exists_side_of_walk (D := D) hrb₀ hZs hZF h₀s
  have hrev := hR.rev
  obtain ⟨b₂, hb₂, F₂, Zr, hEq, hfirst⟩ := GraphWalk.exists_first_mem R'.reverse (X
    := {y | y ∈ A₂.support}) ⟨b₀, R'.reverse.end_mem_support, hb₀⟩
  rw [hEq] at hrev
  have hb₂r : b₂ ≠ r := fun h' ↦ hrA₂ (h' ▸ hb₂)
  have hF₂s : F₂.IsSimple := (isSimple_of_append hrev.s₁).1
  have hinF : ∀ e ∈ F₂.edges, e ∈ F.E := fun e he ↦ (hrev.E e).mpr (.inl (by
    rw [GraphWalk.edges_append]
    exact List.mem_append_left _ he))
  have hoffZ : ∀ e ∈ F₂.edges, e ∉ (Q₁.append (Y₁.append Q₀)).edges := fun e he he' ↦ by
    refine hrev.edge e (by rw [GraphWalk.edges_append]; exact List.mem_append_left _ he) ?_
    rwa [GraphWalk.edges_reverse, List.mem_reverse]
  have hsupF : ∀ x ∈ F₂.support, x ∈ F.V := support_subset_of_edges hFs F₂ hrF hinF
  -- The walk `Zr` from `b₂` to `b₀` runs along `A₂`.
  have hZrD : ∀ e ∈ Zr.edges, e ∈ Dv.E := by
    by_cases he : b₂ = b₀
    · subst he
      have := GraphWalk.edges_of_closed Zr (isSimple_of_append hrev.s₁).2
      rw [this]
      exact fun _ h' ↦ absurd h' (List.not_mem_nil)
    have hl := Splits.split_left hrev hb₂r he
    have hl' := Splits.split_left hl.swap (Ne.symm he) hrb₀.symm
    obtain ⟨Y₂, hY₂s, hY₂, -⟩ := s.swap.exists_seg hE hb₂ hb₀ (hsupF _ F₂.end_mem_support) hb₀F
    rcases eq_side_of_walk (D := D) he hY₂s (fun e h' ↦ (hY₂ e h').2) hl' with rfl | h'
    · exact fun e h' ↦ s.edge₂ e (hY₂ e h').1
    · exfalso
      obtain ⟨e, heQ, -⟩ := GraphWalk.exists_edge_at_start Q₀ h₀.ne
      have hmem : e ∈ Y₂.edges := by
        rw [h', GraphWalk.edges_reverse, List.mem_reverse, GraphWalk.edges_append,
          List.mem_append, GraphWalk.edges_reverse, List.mem_reverse]
        exact .inl ((hZE e).mpr (.inr (.inr heQ)))
      exact h₀.off e heQ (s.edge₂ e (hY₂ e hmem).1)
  refine ⟨b₂, F₂, hb₂, hF₂s, fun e he ↦ ⟨hinF e he, fun h' ↦ hoffZ e he ((hZE e).mpr (.inl h')),
    fun h' ↦ hoffZ e he ((hZE e).mpr (.inr (.inr h')))⟩,
    fun x hx' hA ↦ hfirst x hx' hA, ?_, ?_, fun e he ↦ ?_⟩
  · -- If `F₂` met `A₁`, the segment from `b₁` to their common vertex would be one of the two
    -- pieces of `F` between those vertices.
    intro x hxF₂ hxA₁
    have hxF := hsupF x hxF₂
    have hxr : x ≠ r := fun h' ↦ hrA₁ (h' ▸ hxA₁)
    have hxb₀ : x ≠ b₀ := fun h' ↦ hb₀A₁ (h' ▸ hxA₁)
    have hxb₂ : x ≠ b₂ := fun h' ↦ hten x hxA₁ (h' ▸ hb₂) hxF
    have hxb₁ : b₁ ≠ x := fun h' ↦ by
      have hm := hrev.meet x ((GraphWalk.mem_support_append _ _).mpr (.inl hxF₂)) (by
        rw [GraphWalk.support_reverse, List.mem_reverse, ← h']
        exact (GraphWalk.mem_support_append _ _).mpr (.inl Q₁.end_mem_support))
      rcases hm with h₃ | h₃
      · exact hxr h₃
      · exact hxb₀ h₃
    obtain ⟨L, M, hLM⟩ := F₂.exists_append_of_mem hxF₂
    rw [hLM, GraphWalk.append_assoc'] at hrev
    have hl := Splits.split_left hrev hxr hxb₀
    rw [GraphWalk.reverse_append', ← GraphWalk.append_assoc'] at hl
    have hl' := (Splits.split_left hl.swap hxb₁ h₁'.ne.symm).swap
    obtain ⟨Yx, hYxs, hYx, -⟩ := s.exists_seg hE hb₁ hxA₁ hb₁F hxF
    rcases eq_side_of_walk (D := D) hxb₁ hYxs (fun e h' ↦ (hYx e h').2) hl' with h' | h'
    · obtain ⟨e, heQ, -⟩ := GraphWalk.exists_edge_at_start Q₁ h₁'.ne
      have hmem : e ∈ Yx.edges := by
        rw [h', GraphWalk.edges_append, List.mem_append, GraphWalk.edges_reverse, List.mem_reverse]
        exact .inl heQ
      exact h₁'.off e heQ (s.edge₁ e (hYx e hmem).1)
    · obtain ⟨e, heQ, -⟩ := GraphWalk.exists_edge_at_start Q₀ h₀.ne
      have hmem : e ∈ Yx.edges := by
        rw [h', GraphWalk.edges_reverse, List.mem_reverse, GraphWalk.edges_append,
          List.mem_append, GraphWalk.edges_reverse, List.mem_reverse]
        exact .inr (by rw [GraphWalk.edges_append]; exact List.mem_append_right _ heQ)
      exact h₀.off e heQ (s.edge₁ e (hYx e hmem).1)
  · obtain ⟨e, he, hin⟩ := hf.exists_edge_in
    refine ⟨e, ?_, hin⟩
    obtain ⟨p, hp⟩ := (hFs.2 he).1
    have hnotD : e ∉ Dv.E := fun h' ↦ (hin hp).2 (by
      rw [← hx.sector.Dv_U]
      exact Dv.closure_subset_U h' (subset_closure hp))
    have hnotO : ∀ {g : Set Shat}, Disjoint g Δv → e ≠ g := fun hg h' ↦ disjoint_left.mp
      (h' ▸ hg) hp (discInt_subset _ (hin hp))
    rcases (hrev.E e).mp he with h' | h'
    · rw [GraphWalk.edges_append, List.mem_append] at h'
      rcases h' with h' | h'
      · exact h'
      · exact absurd (hZrD e h') hnotD
    · rw [GraphWalk.edges_reverse, List.mem_reverse] at h'
      rcases (hZE e).mp h' with h₃ | h₃ | h₃
      · exact absurd rfl (hnotO (o₁ e h₃))
      · exact absurd (s.edge₁ e (hY₁ e h₃).1) hnotD
      · exact absurd rfl (hnotO (o₀ e h₃))
  · rcases (hrev.E e).mp he with h' | h'
    · rw [GraphWalk.edges_append, List.mem_append] at h'
      rcases h' with h' | h'
      · exact .inl h'
      · exact .inr (.inr (.inr (hZrD e h')))
    · rw [GraphWalk.edges_reverse, List.mem_reverse] at h'
      rcases (hZE e).mp h' with h₃ | h₃ | h₃
      · exact .inr (.inl h₃)
      · exact .inr (.inr (.inr (s.edge₁ e (hY₁ e h₃).1)))
      · exact .inr (.inr (.inl h₃))

end IsFar

end TangleDatum

end GraphMinor.GM19
