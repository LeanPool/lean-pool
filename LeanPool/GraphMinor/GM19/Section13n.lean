/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section13m

/-!
# Graph Minors XIX, Section 13: step (5) of (13.6), and the path `M` of step (6)
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

namespace TieBreaker

variable {Γ : Painting S} {rad : RadialDrawing cap Γ}

omit [T2Space S] [T2Space Shat] in
theorem walkWeight_reverse (tb : TieBreaker rad) {u v : Shat} (T : GraphWalk rad.G.toGraph u v) :
  tb.walkWeight T.reverse = tb.walkWeight T := by
  simp only [walkWeight, GraphWalk.edges_reverse, List.map_reverse, List.sum_reverse]

omit [T2Space S] [T2Space Shat] in
/-- The weight of a circuit is the sum of the weights of its two sides. -/
theorem weightSub_eq_of_splits (tb : TieBreaker rad) {C : Drawing Shat} {a b : Shat} {W₁ :
  GraphWalk rad.G.toGraph a b} {W₂ : GraphWalk rad.G.toGraph b a}
    (hs : Splits C W₁ W₂) : tb.weightSub C = tb.walkWeight W₁ + tb.walkWeight W₂ := by
  classical
  have hn : (W₁.edges ++ W₂.edges).Nodup := List.nodup_append.mpr ⟨hs.s₁.edges_nodup,
    hs.s₂.edges_nodup, fun x hx y hy h ↦ hs.edge x hx (h ▸ hy)⟩
  have hE : C.E = ↑(W₁.edges ++ W₂.edges).toFinset := by
    ext e
    simp [hs.E e]
  rw [weightSub, hE, finsum_mem_coe_finset, List.sum_toFinset _ hn]
  simp [walkWeight]

omit [T2Space S] in
theorem weightSub_le_of_edges (tb : TieBreaker rad) {P : Drawing Shat} {u v : Shat}
  (T : GraphWalk rad.G.toGraph u v) (hE : ∀ e ∈ P.E, e ∈ T.edges) :
    tb.weightSub P ≤ tb.walkWeight T := by
  refine (tb.weightSub_mono (X := P) (Y := walkDrawing rad.G T) (fun e he ↦ ?_)
    (walkDrawing_isSubdrawing _ _).2).trans (tb.weightSub_walkDrawing_le T)
  rw [walkDrawing_E]
  exact hE e he

end TieBreaker

omit [T2Space Shat] in
/-- A set of edges inside a walk has at most as many edges as the walk. -/
theorem ncard_le_length_of_edges {G P : Drawing Shat} {u v : Shat} (T : GraphWalk G.toGraph u v)
  (hE : ∀ e ∈ P.E, e ∈ T.edges) : P.E.ncard ≤ T.length := by
  classical
  have h₁ : P.E ⊆ ↑T.edges.toFinset := fun e he ↦ by simpa using hE e he
  have h₂ := ncard_le_ncard h₁ (Finset.finite_toSet _)
  rw [ncard_coe_finset] at h₂
  exact h₂.trans (List.toFinset_card_le _)

namespace TangleDatum

variable {D : TangleDatum cap χ} {W : Set Shat} {H : Drawing Shat} {ρ : ℕ} {r : Shat} {Δv : Set
  Shat} {Dv F : Drawing Shat}
  {ord' : ℕ} {𝒯' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {Δ₀ Δ : Set Shat} {C :
    Drawing Shat}

omit [T2Space Shat] in
/-- A walk of `Γ*` has even length exactly if its ends are on the same side of the bipartition. -/
theorem even_length_walk (D : TangleDatum cap χ) {a b : Shat} (T : GraphWalk D.rad.G.toGraph a b) :
    Even T.length ↔ (a ∈ D.P.Γ.hatV cap ↔ b ∈ D.P.Γ.hatV cap) := by
  obtain ⟨Sk, hSk⟩ := exists_isSkHat χ.isSurface cap D.P.Γ
  have := even_length_iff Sk.V (D.rad.bipartite hSk.hV) T
  rwa [hSk.hV] at this

/-- The bound of the paper's step (6): a walk from a vertex of `bd(W)` to the inner end of a spoke
is at least as long as the spoke, and if it has
the same length then it starts at a vertex of `Γ`. -/
theorem IsSpokeWalk.le_walk_of_bd (hW : D.IsWheelHubOfRadius W H ρ) (hbdS : discBd W ⊆ cap.emb ''
  (univ \ bd S))
    (hin : ((W \ discBd W) ∩ (cap.emb '' D.Γ.V)).Nonempty) {v h a : Shat} {K : GraphWalk
      D.rad.G.toGraph v h} (hK : D.IsSpokeWalk W H K)
    (T : GraphWalk D.rad.G.toGraph a h) (ha : a ∈ D.rad.G.V) (hab : a ∈ discBd W) : K.length
      ≤ T.length ∧ (K.length = T.length → a ∈ D.P.Γ.hatV cap) := by
  have : ConnectedSpace Shat := cap.connected
  have hl := hW.spoke_length hK
  have hh := hK.2.h_mem
  have hv : v ∈ D.P.Γ.hatV cap := hK.2.v_mem.1
  have hK' := D.even_length_walk K
  have hT' := D.even_length_walk T
  by_cases hah : a ∈ D.P.Γ.hatV cap
  · refine ⟨?_, fun _ ↦ hah⟩
    have h₁ := hW.walk_ge ⟨hah, hab⟩ hh T
    by_contra hn
    have h₂ : K.length = T.length + 1 := by omega
    have e₁ : Even K.length ↔ Even T.length := by
      rw [hK', hT']
      simp [hv, hah]
    rw [h₂, Nat.even_add_one] at e₁
    tauto
  · have hlt : K.length ≤ T.length := by
      by_contra hn
      obtain ⟨P, hP, hle⟩ := exists_path_of_walk T
      exact theorem_13_1_proof hW hbdS hin ⟨ha, hah⟩ hab ⟨P, h, hh, hP, by omega⟩
    refine ⟨hlt, fun heq ↦ ?_⟩
    have e₁ : Even K.length ↔ Even T.length := by rw [heq]
    rw [hK', hT'] at e₁
    tauto

/-- The set-up after step (4) and the paragraph that follows it. -/
structure IsRound (D : TangleDatum cap χ) (W : Set Shat) (H : Drawing Shat) (ρ : ℕ) (r : Shat)
  (Δv : Set Shat) (Dv : Drawing Shat) (ord' : ℕ)
    (𝒯' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (F : Drawing Shat) (Δ₀ : Set Shat)
      (C : Drawing Shat) (Δ : Set Shat) : Prop where
  enc : D.IsSectorEnclave W H ρ r Δv Dv ord' 𝒯' F
  amb : D.IsAmbientDisc W H ρ F Δ₀
  circuit : C.IsCircuitOf D.rad.G
  edges : ∀ e ∈ C.E, e ∈ F.E ∨ e ∈ Dv.E
  disc : IsClosedDisc Δ
  sub : Δ ⊆ Δ₀
  bd : discBd Δ = C.U
  F_sub : D.ins F ⊆ Δ
  v_sub : Δv ⊆ Δ

namespace IsRound

variable (hr : D.IsRound W H ρ r Δv Dv ord' 𝒯' F Δ₀ C Δ)
include hr

/-- **Step (5) of the proof of (13.6).** -/
theorem card : C.E.ncard ≤ Dv.E.ncard ∧ (C.E.ncard = Dv.E.ncard → D.tb.weightSub C
  ≤ D.tb.weightSub Dv) :=
  uncross_circuit_le χ.isSurface D.P.fits.internally_three_connected D.tb D.isTangle
    hr.enc.isTangle' hr.enc.isInsOf_F hr.enc.distinction hr.enc.isInsOf_Dv
    hr.enc.mem hr.circuit hr.disc hr.bd hr.F_sub hr.v_sub hr.edges

theorem C_card : C.E.ncard ≤ 4 * ρ + 4 := hr.card.1.trans hr.enc.Dv_card

/-- `Δ` is the inside of `C`. -/
theorem ins_C : D.ins C = Δ := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hle := hr.C_card
  have hrep := hr.enc.hrep
  have hi := D.ins_spec hr.circuit (by omega)
  have hsub := hr.amb.short C hr.circuit hle (hr.bd ▸ (Surface.discBd_subset Δ).trans hr.sub)
  exact disc_eq_of_subset_disc hT hr.amb.disc hi.2.2.1 hr.disc hsub hr.sub
    (hi.2.2.2.1.trans hr.bd.symm)

theorem Δ_sub_W (hU : C.U ⊆ W) : Δ ⊆ W := by
  rw [← hr.ins_C]
  exact hr.enc.wheel.ins_sub C hr.circuit hr.C_card hU

end IsRound

/-- The path `M` of step (6), with `Q` the other side of `C`. -/
structure IsOuterPath (D : TangleDatum cap χ) (W : Set Shat) (C : Drawing Shat) {a b : Shat}
  (M : GraphWalk D.rad.G.toGraph a b)
    (Q : GraphWalk D.rad.G.toGraph b a) : Prop where
  splits : Splits C M Q
  ne : a ≠ b
  a_bd : a ∈ discBd W
  b_bd : b ∈ discBd W
  two : 2 ≤ M.length
  noint : ∀ x ∈ M.support, x ∉ W \ discBd W
  off_int : ∀ e ∈ M.edges, Disjoint e (W \ discBd W)

omit [T2Space S] [T2Space Shat] in
/-- An edge of `Γ*` at a vertex has another end. -/
theorem exists_other_end (D : TangleDatum cap χ) {g : Set Shat} (hg : g ∈ D.rad.G.E) {c : Shat}
  (hc : c ∈ D.rad.G.V) (hcg : c ∈ closure g) :
    ∃ y, y ≠ c ∧ D.rad.G.toGraph.IsLink g c y := by
  obtain ⟨p, hp, q, hq, hcap⟩ := D.rad.isPreRadial.2.2.2.2.1 g hg
  have hm : c ∈ closure g ∩ D.rad.G.V := ⟨hcg, hc⟩
  have hpm : p ∈ closure g ∩ D.rad.G.V := by
    rw [hcap]
    exact .inl rfl
  have hqm : q ∈ closure g ∩ D.rad.G.V := by
    rw [hcap]
    exact .inr rfl
  have hpq : p ≠ q := fun h' ↦ hq.2 (h' ▸ hp)
  rw [hcap] at hm
  rcases hm with rfl | rfl
  · exact ⟨q, hpq.symm, hg, hpm.2, hqm.2, hcap⟩
  · exact ⟨p, hpq, hg, hqm.2, hpm.2, by rw [hcap, pair_comm]⟩

omit [T2Space Shat] in
theorem IsLink.left_mem_closure {G : Drawing Shat} {e : Set Shat} {x y : Shat}
  (hl : G.toGraph.IsLink e x y) : x ∈ closure e := by
  have : x ∈ closure e ∩ G.V := by
    rw [hl.2.2.2]
    exact .inl rfl
  exact this.1

omit [T2Space Shat] in
theorem IsLink.right_mem_closure {G : Drawing Shat} {e : Set Shat} {x y : Shat}
  (hl : G.toGraph.IsLink e x y) : y ∈ closure e := by
  have : y ∈ closure e ∩ G.V := by
    rw [hl.2.2.2]
    exact .inr rfl
  exact this.1

omit [T2Space Shat] in
theorem IsLink.symm' {G : Drawing Shat} {e : Set Shat} {x y : Shat} (hl : G.toGraph.IsLink e x y) :
  G.toGraph.IsLink e y x :=
  ⟨hl.1, hl.2.2.1, hl.2.1, by rw [hl.2.2.2, pair_comm]⟩

/-- **The path `M` of step (6).** If `U(C)` is not in `W` then `M` is a piece of `C` outside `W`,
and we do not need it to be maximal among the paths
with no edge in `W`. If `U(C) ⊆ W` then `M` is `f₁ ∪ f₂`. -/
theorem IsRound.exists_outer (hr : D.IsRound W H ρ r Δv Dv ord' 𝒯' F Δ₀ C Δ) {v₁ v₂ : Shat} {f₁ f₂
  : Set Shat} (hne : v₁ ≠ v₂)
    (hl₁ : D.rad.G.toGraph.IsLink f₁ r v₁) (hl₂ : D.rad.G.toGraph.IsLink f₂ r v₂)
      (hb₁ : f₁ ⊆ discBd W) (hb₂ : f₂ ⊆ discBd W) (hf₁ : f₁ ∈ Dv.E) (hf₂ : f₂ ∈ Dv.E)
    (hvr : r ∉ D.P.Γ.hatV cap) (hv₁ : v₁ ∈ D.P.Γ.hatV cap) (hv₂ : v₂ ∈ D.P.Γ.hatV cap) {c : Shat}
      (hc : c ∈ C.V) (hcW : c ∈ W \ discBd W) :
    (∃ (a b : Shat) (M : GraphWalk D.rad.G.toGraph a b) (Q : GraphWalk D.rad.G.toGraph b a),
      D.IsOuterPath W C M Q ∧ ∀ x ∈ M.support, x ∈ W → x = a ∨ x = b) ∨
    (C.U ⊆ W ∧ ∃ (M : GraphWalk D.rad.G.toGraph v₁ v₂) (Q : GraphWalk D.rad.G.toGraph v₂ v₁),
      D.IsOuterPath W C M Q ∧ M.edges = [f₁, f₂]) := by
  classical
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hman : ∀ x : Shat, IsManifoldPoint x := (Surface.IsClosedSurface.isSurface hT).2.2
  have hW := hr.enc.wheel
  have hC := hr.circuit
  have hstartV : ∀ {a b : Shat} (N : GraphWalk D.rad.G.toGraph a b), a ≠ b →
    (∀ e ∈ N.edges, e ∈ C.E) → a ∈ C.V := by
    intro a b N hab hE
    cases N with
    | nil _ => exact absurd rfl hab
    | @cons _ y _ e hl r => exact (Drawing.IsLink.mem_V_of_sub hC.1 hl (hE e (by simp))).1
  by_cases hU : C.U ⊆ W
  · right
    refine ⟨hU, ?_⟩
    have hΔW := hr.Δ_sub_W hU
    have hbdf : frontier W = discBd W := IsClosedDisc.frontier_eq_discBd hT hW.is_disc
    have hinC : ∀ {f : Set Shat}, f ∈ Dv.E → f ⊆ discBd W → f ∈ C.E := by
      intro f hf hfb
      by_contra hn
      have hfΔ : f ⊆ Δ := fun x hx ↦ hr.v_sub (by
        have : x ∈ discBd Δv := by
          rw [← hr.enc.sector.Dv_U]
          exact Dv.closure_subset_U hf (subset_closure hx)
        exact Surface.discBd_subset _ this)
      have hfG := hr.enc.sector.Dv_circuit.1.2 hf
      obtain ⟨x, hx⟩ := hfG.1
      rcases edge_inside_or_off hT hC.1 hr.disc hr.bd hfG hn with h₁ | h₁
      · have hf' : x ∈ frontier W := hbdf ▸ hfb hx
        exact hf'.2 (mem_interior.mpr ⟨_, (discInt_subset _).trans hΔW,
          hr.disc.isOpen_discInt hman, h₁ hx⟩)
      · exact disjoint_left.mp h₁ hx (hfΔ hx)
    have h₁C := hinC hf₁ hb₁
    have h₂C := hinC hf₂ hb₂
    have hcl : ∀ {f : Set Shat}, f ⊆ discBd W → closure f ⊆ discBd W := fun hf ↦ closure_minimal hf
      (hbdf ▸ isClosed_frontier)
    let M : GraphWalk D.rad.G.toGraph v₁ v₂ := .cons (IsLink.symm' hl₁) (.cons hl₂ (.nil hl₂.2.2.1))
    have hMe : M.edges = [f₁, f₂] := rfl
    have hMs : M.support = [v₁, r, v₂] := rfl
    have hMsim : M.IsSimple := by
      change [v₁, r, v₂].Nodup
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
        List.nodup_nil, and_true]
      exact ⟨⟨fun h' ↦ hvr (h' ▸ hv₁), hne⟩, fun h' ↦ hvr (h' ▸ hv₂), not_false⟩
    have hME : ∀ e ∈ M.edges, e ∈ C.E := fun e he ↦ by
      rw [hMe] at he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · exact h₁C
      · exact h₂C
    have hreverse := hstartV M.reverse hne.symm fun e he ↦
      hME e (by simpa [GraphWalk.edges_reverse] using he)
    obtain ⟨W₁, W₂, hs⟩ := exists_splits hC.2 hC.1 (hstartV M hne hME) hreverse hne
    obtain ⟨Q, hQ⟩ := exists_side_of_walk hne hMsim hME hs
    have hlength : 2 ≤ M.length := by
      change 2 ≤ M.edges.length
      simp [hMe]
    refine ⟨M, Q, ⟨hQ, hne, hcl hb₁ (IsLink.right_mem_closure hl₁), hcl hb₂
      (IsLink.right_mem_closure hl₂), hlength, ?_, ?_⟩, hMe⟩
    · intro x hx hxi
      rw [hMs] at hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact hxi.2 (hcl hb₁ (IsLink.right_mem_closure hl₁))
      · exact hxi.2 (hcl hb₁ (IsLink.left_mem_closure hl₁))
      · exact hxi.2 (hcl hb₂ (IsLink.right_mem_closure hl₂))
    · intro e he
      rw [hMe] at he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · exact disjoint_left.mpr fun x hx hxi ↦ hxi.2 (hb₁ hx)
      · exact disjoint_left.mpr fun x hx hxi ↦ hxi.2 (hb₂ hx)
  left
  obtain ⟨e, heC, hen⟩ : ∃ e ∈ C.E, ¬ e ⊆ W := by
    by_contra hn
    push Not at hn
    exact hU (U_of_edges hC.2 hW.is_disc.isClosed hn)
  have hed : Disjoint e W := (hW.edge_side (hC.1.2 heC)).resolve_left hen
  obtain ⟨g, hg, hcg⟩ := exists_edge_at_vertex hC.2 hc
  have hgW : g ⊆ W := (hW.edge_side (hC.1.2 hg)).resolve_right fun h' ↦ hcW.2
    (hW.mem_bd_of_closure h' hcg hcW.1)
  obtain ⟨y, hyc, hl⟩ := exists_other_end D (hC.1.2 hg) (hC.1.1 hc) hcg
  have hyC := (Drawing.IsLink.mem_V_of_sub hC.1 hl hg).2
  have hyW : y ∈ W := closure_minimal hgW hW.is_disc.isClosed (IsLink.right_mem_closure hl)
  obtain ⟨W₁, W₂, hs⟩ := exists_splits hC.2 hC.1 hc hyC hyc.symm
  obtain ⟨u, v, M, hu, hv, hMs, heM, hME, hinner⟩ : ∃ (u v : Shat) (M : GraphWalk D.rad.G.toGraph u
    v), u ∈ W ∧ v ∈ W ∧ M.IsSimple ∧ e ∈ M.edges ∧
      (∀ e ∈ M.edges, e ∈ C.E) ∧ ∀ x ∈ M.support, x ∈ W → x = u ∨ x = v := by
    rcases (hs.E e).mp heC with h | h
    · obtain ⟨u, v, M, h₁, h₂, h₃, h₄, h₅, h₆⟩ := GraphWalk.exists_piece W₁ hs.s₁ hcW.1 hyW h
      exact ⟨u, v, M, h₁, h₂, h₃, h₄, fun e he ↦ (hs.E e).mpr (.inl (h₅ e he)), h₆⟩
    · obtain ⟨u, v, M, h₁, h₂, h₃, h₄, h₅, h₆⟩ := GraphWalk.exists_piece W₂ hs.s₂ hyW hcW.1 h
      exact ⟨u, v, M, h₁, h₂, h₃, h₄, fun e he ↦ (hs.E e).mpr (.inr (h₅ e he)), h₆⟩
  have huv : u ≠ v := by
    rintro rfl
    rw [(simple_self hMs).1] at heM
    cases heM
  have hMoff : ∀ f ∈ M.edges, Disjoint f W := fun f hf ↦ by
    rcases GraphWalk.edge_has_middle M hMs huv hf with h | ⟨x, hxs, hxc, hxu, hxv⟩
    · rw [h] at heM
      obtain rfl : e = f := by simpa using heM
      exact hed
    · refine (hW.edge_side (hC.1.2 (hME f hf))).resolve_left fun h' ↦ ?_
      rcases hinner x hxs (closure_minimal h' hW.is_disc.isClosed hxc) with h'' | h''
      · exact hxu h''
      · exact hxv h''
  have hfirst : ∀ {a b : Shat} (N : GraphWalk D.rad.G.toGraph a b), a ≠ b →
    (∀ f ∈ N.edges, Disjoint f W) → a ∈ W → a ∈ discBd W := by
    intro a b N hab hE haW
    cases N with
    | nil _ => exact absurd rfl hab
    | @cons _ y _ f hl r =>
      exact hW.mem_bd_of_closure (hE f (by simp)) (IsLink.left_mem_closure hl) haW
  have hub := hfirst M huv hMoff hu
  have hvb := hfirst M.reverse huv.symm (fun f hf ↦ hMoff f (by simpa [GraphWalk.edges_reverse]
    using hf)) hv
  have htwo : 2 ≤ M.length := by
    by_contra hn
    cases hM : M with
    | nil _ => exact huv rfl
    | @cons _ y' _ f hl' r =>
      cases hr' : r with
      | cons _ _ =>
        subst hr' hM
        simp [GraphWalk.length_cons] at hn
      | nil _ =>
        subst hr' hM
        have hfG := hl'.1
        have ht : tilde f ⊆ discBd W := by
          rw [← closure_inter_V_eq_tilde hfG, hl'.2.2.2]
          rintro x (rfl | rfl)
          · exact hub
          · exact hvb
        obtain ⟨x, hx⟩ := hfG.1
        exact disjoint_left.mp (hMoff f (by simp)) hx (hW.chord_in_W f hfG ht hx)
  obtain ⟨W₃, W₄, hs₂⟩ := exists_splits hC.2 hC.1 (hstartV M huv hME)
    (hstartV M.reverse huv.symm fun f hf ↦ hME f (by simpa [GraphWalk.edges_reverse] using hf)) huv
  obtain ⟨Q, hQ⟩ := exists_side_of_walk huv hMs hME hs₂
  refine ⟨u, v, M, Q, ⟨hQ, huv, hub, hvb, htwo, fun x hx hxi ↦ ?_, fun f hf ↦
    (hMoff f hf).mono_right sdiff_subset⟩, hinner⟩
  rcases hinner x hx hxi.1 with rfl | rfl
  · exact hxi.2 hub
  · exact hxi.2 hvb

end TangleDatum

end GraphMinor.GM19
