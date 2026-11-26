/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section10p

/-!
# The third bullet of the distance flaw

Two short circuits with one pole inside each, and a line between them, or a common vertex.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {cap : IsCappedSurface S Shat} {β : Type w} {χ : ColourScheme S β}


namespace TangleDatum

variable {D : TangleDatum cap χ}

omit [T2Space S] in
/-- A closed walk of `Γ*` around a circuit, at any vertex of the circuit. -/
theorem exists_circuit_walk {C : Drawing Shat} (hC : C.IsCircuitOf D.rad.G) {v : Shat}
  (hv : v ∈ C.V) :
    ∃ W : GraphWalk D.rad.G.toGraph v v, W.length = C.E.ncard ∧ 0 < W.length
      ∧ walkDrawing D.rad.G W = C := by
  classical
  have : ConnectedSpace Shat := cap.connected
  obtain ⟨X, hX, hpos, hV, hE⟩ := exists_walk_at hC.2 hv
  obtain ⟨W, hs, he⟩ := hC.1.exists_walk_up X
  have hEeq : C.E = ↑W.edges.toFinset := by
    rw [hE, he]
    ext e
    simp
  have hlen : W.length = C.E.ncard := by
    rw [hEeq, ncard_coe_finset, List.toFinset_card_of_nodup, GraphWalk.length]
    rw [he]
    exact hX.2
  have hpos' : 0 < W.length := by
    rw [GraphWalk.length, he]
    exact hpos
  refine ⟨W, hlen, hpos', Drawing.ext_of_V_E ?_ ?_⟩
  · rw [walkDrawing_V, hs, hV]
  · rw [walkDrawing_E, he, hE]

omit [T2Space S] in
/-- Two circuits with total length at most `2n` that share two vertices lie in a short circuit, so
its inside holds both insides. -/
theorem no_two_common_vertices {n : ℕ} (hn : n < D.rep) {C₁ C₂ : Drawing Shat}
  (hC₁ : C₁.IsCircuitOf D.rad.G) (hC₂ : C₂.IsCircuitOf D.rad.G)
    (hc : C₁.E.ncard + C₂.E.ncard ≤ 2 * n) {x y : Shat} (hxy : x ≠ y) (hx₁ : x ∈ C₁.V)
      (hx₂ : x ∈ C₂.V) (hy₁ : y ∈ C₁.V) (hy₂ : y ∈ C₂.V) :
    ∃ C, C.IsCircuitOf D.rad.G ∧ C.E.ncard ≤ 2 * n ∧ D.ins C₁ ⊆ D.ins C ∧ D.ins C₂ ⊆ D.ins C
      ∧ C.V ⊆ C₁.V ∪ C₂.V := by
  classical
  have : ConnectedSpace Shat := cap.connected
  have hrep : 1 ≤ D.rep := by omega
  have hs := D.isSlope hrep
  obtain ⟨Z₁, hl₁, hp₁, hZ₁⟩ := exists_circuit_walk hC₁ hx₁
  obtain ⟨Z₂, hl₂, hp₂, hZ₂⟩ := exists_circuit_walk hC₂ hx₂
  have hns := isNonSeparable_walk Z₁ Z₂ (hZ₁ ▸ isBlock_of_isCircuit hC₁.2)
    (hZ₂ ▸ isBlock_of_isCircuit hC₂.2)
    (fun z hz ↦ exists_edge_at Z₁ hp₁ hz) (fun z hz ↦ exists_edge_at Z₂ hp₂ hz) hxy
    (hZ₁ ▸ C₁.V_subset_U hx₁) (hZ₂ ▸ C₂.V_subset_U hx₂) (hZ₁ ▸ C₁.V_subset_U hy₁)
      (hZ₂ ▸ C₂.V_subset_U hy₂)
  set E := walkDrawing D.rad.G (Z₁.append Z₂) with hE
  have hs₁ : C₁.IsSubdrawing E := hZ₁ ▸ walkDrawing_mono
    (fun z h ↦ (GraphWalk.mem_support_append _ _).mpr (Or.inl h))
    (fun e h ↦ by rw [GraphWalk.edges_append]; exact List.mem_append.mpr (Or.inl h))
  have hs₂ : C₂.IsSubdrawing E := hZ₂ ▸ walkDrawing_mono
    (fun z h ↦ (GraphWalk.mem_support_append _ _).mpr (Or.inr h))
    (fun e h ↦ by rw [GraphWalk.edges_append]; exact List.mem_append.mpr (Or.inr h))
  have hEΓ : E.IsSubdrawing D.rad.G := walkDrawing_isSubdrawing _ _
  have hEc : E.E.ncard ≤ 2 * n := by
    have h₁ : E.E ⊆ C₁.E ∪ C₂.E := fun e he ↦ by
      rw [hE, walkDrawing_E, mem_ofPred_eq, GraphWalk.edges_append, List.mem_append] at he
      rcases he with h | h
      · exact Or.inl (by rw [← hZ₁, walkDrawing_E]; exact h)
      · exact Or.inr (by rw [← hZ₂, walkDrawing_E]; exact h)
    have h₂ := ncard_le_ncard h₁ (C₁.finite_edges.union C₂.finite_edges)
    have h₃ := ncard_union_le C₁.E C₂.E
    omega
  have hsub : ∀ {C : Drawing Shat}, C.IsSubdrawing E → C.E.ncard ≤ 2 * n := fun {C} h ↦
    (ncard_le_ncard h.2 E.finite_edges).trans hEc
  have hconf : IsConfined (2 * D.rep) E := fun C _ h ↦ by
    have := hsub h
    change C.E.ncard < _
    omega
  obtain ⟨m, hm⟩ := ((finite_circuits E).image D.ins).exists_maximal ⟨D.ins C₁, C₁, ⟨hC₁.2, hs₁⟩,
    rfl⟩
  obtain ⟨C, ⟨hC, hCs⟩, rfl⟩ := hm.1
  have heq := theorem_4_3_iii hs hEΓ hconf hC hCs (fun C' h₁ h₂ h₃ ↦ hm.2 ⟨C', ⟨h₁, h₂⟩, rfl⟩ h₃)
    hns
  have hin : ∀ {X : Drawing Shat}, X.IsCircuit → X.IsSubdrawing E → D.ins X ⊆ D.ins C
    := fun {X} hX hXs z hz ↦ by
    rw [← heq]
    exact Or.inr (mem_iUnion₂.mpr ⟨X, ⟨hX, hXs⟩, hz⟩)
  refine ⟨C, ⟨hCs.trans hEΓ, hC⟩, hsub hCs, hin hC₁.2 hs₁, hin hC₂.2 hs₂, fun z hz ↦ ?_⟩
  have hzE : z ∈ E.V := hCs.1 hz
  rw [hE, walkDrawing_V, mem_ofPred_eq, GraphWalk.mem_support_append] at hzE
  rcases hzE with h | h
  · exact Or.inl (by rw [← hZ₁, walkDrawing_V]; exact h)
  · exact Or.inr (by rw [← hZ₂, walkDrawing_V]; exact h)

omit [T2Space S] in
/-- Two circuits with total length at most `2n` that share two vertices lie in a short circuit. -/
theorem no_two_common {n : ℕ} (hn : n < D.rep) {C₁ C₂ : Drawing Shat}
  (hC₁ : C₁.IsCircuitOf D.rad.G) (hC₂ : C₂.IsCircuitOf D.rad.G)
    (hc : C₁.E.ncard + C₂.E.ncard ≤ 2 * n) {x y : Shat} (hxy : x ≠ y) (hx₁ : x ∈ C₁.V)
      (hx₂ : x ∈ C₂.V) (hy₁ : y ∈ C₁.V) (hy₂ : y ∈ C₂.V) :
    ∃ C, C.IsCircuitOf D.rad.G ∧ C.E.ncard ≤ 2 * n ∧ D.ins C₁ ⊆ D.ins C ∧ D.ins C₂ ⊆ D.ins C := by
  obtain ⟨C, h₁, h₂, h₃, h₄, -⟩ := no_two_common_vertices hn hC₁ hC₂ hc hxy hx₁ hx₂ hy₁ hy₂
  exact ⟨C, h₁, h₂, h₃, h₄⟩

omit [T2Space S] in
/-- Two short circuits whose insides do not include each other's pole: each inside misses the open
disc of the other. -/
theorem int_disjoint (hrep : 1 ≤ D.rep) {C₁ C₂ : Drawing Shat} (hC₁ : C₁.IsCircuitOf D.rad.G)
  (hC₂ : C₂.IsCircuitOf D.rad.G) (hl₁ : C₁.E.ncard < 2 * D.rep)
    (hl₂ : C₂.E.ncard < 2 * D.rep) {w : Shat} (hw : C₁.U ∩ C₂.U ⊆ {w}) {r₁ r₂ : Shat}
      (h₁ : r₁ ∈ D.ins C₁) (h₁' : r₁ ∉ D.ins C₂) (h₂ : r₂ ∈ D.ins C₂) (h₂' : r₂ ∉ D.ins C₁) :
    Disjoint (discInt (D.ins C₂)) (D.ins C₁) := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hsl := D.isSlope hrep
  have hi₁ := D.ins_spec hC₁ hl₁
  have hi₂ := D.ins_spec hC₂ hl₂
  have hfr₂ : frontier (D.ins C₂) = C₂.U := by
    rw [IsClosedDisc.frontier_eq_discBd hT hi₂.2.2.1, hi₂.2.2.2.1]
  have hO := isSide_int hT hi₂.2.2.1 hi₂.2.2.2.1
  have hint : ∀ {x}, x ∈ discInt (D.ins C₂) → x ∉ C₂.U := fun {x} hx hxU ↦ hx.2 (hi₂.2.2.2.1 ▸ hxU)
  refine disjoint_disc hT hO hi₁.2.2.1 hi₁.2.2.2.1 ?_ ?_
  · refine disjoint_left.2 fun y hy hyC ↦ ?_
    have hconn : IsPreconnected (C₁.U \ C₂.U) := by
      by_cases hwm : w ∈ C₁.U ∧ w ∈ C₂.U
      · have : C₁.U \ C₂.U = C₁.U \ {w} := by
          ext z
          refine ⟨fun hz ↦ ⟨hz.1, fun h ↦ hz.2 (mem_singleton_iff.1 h ▸ hwm.2)⟩, fun hz ↦ ⟨hz.1,
            fun h ↦ hz.2 (hw ⟨hz.1, h⟩)⟩⟩
        rw [this]
        exact (isPathConnected_oArc_diff (IsCircuit.isOArc_U hC₁.2)
          hwm.1).isConnected.isPreconnected
      · have : C₁.U \ C₂.U = C₁.U := by
          refine sdiff_eq_left.2 (disjoint_left.2 fun z h₃ h₄ ↦ hwm ?_)
          have := mem_singleton_iff.1 (hw ⟨h₃, h₄⟩)
          exact this ▸ ⟨h₃, h₄⟩
        rw [this]
        exact (IsCircuit.isOArc_U hC₁.2).isPreconnected
    have hall : C₁.U ⊆ D.ins C₂ := by
      intro z hz
      by_contra hzn
      obtain ⟨c, hc, hcf⟩ := inter_frontier_of_preconnected hconn hi₂.2.2.1.isClosed ⟨y, ⟨hyC, hint
        hy⟩, hy.1⟩
        ⟨z, ⟨hz, fun h ↦ hzn (D.U_subset_ins hC₂ hl₂ h)⟩, hzn⟩
      rw [hfr₂] at hcf
      exact hc.2 hcf
    exact h₁' (hsl.monotone C₁ C₂ hC₁.2 hC₁.1 hl₁ hC₂.2 hC₂.1 hl₂ hall h₁)
  · intro h
    have hsub : D.ins C₂ ⊆ D.ins C₁ := by
      rw [← closure_discInt hi₂.2.2.1]
      exact closure_minimal (h.trans (discInt_subset _)) hi₁.2.2.1.isClosed
    exact h₂' (hsub h₂)

omit [T2Space S] in
/-- Two short circuits, each with a pole inside that the other has not: the insides meet only in
common vertices. -/
theorem ins_inter_ins (hrep : 1 ≤ D.rep) {C₁ C₂ : Drawing Shat} (hC₁ : C₁.IsCircuitOf D.rad.G)
  (hC₂ : C₂.IsCircuitOf D.rad.G) (hl₁ : C₁.E.ncard < 2 * D.rep)
    (hl₂ : C₂.E.ncard < 2 * D.rep) (hone : (C₁.V ∩ C₂.V).Subsingleton) {r₁ r₂ : Shat}
      (h₁ : r₁ ∈ D.ins C₁) (h₁' : r₁ ∉ D.ins C₂) (h₂ : r₂ ∈ D.ins C₂) (h₂' : r₂ ∉ D.ins C₁) :
    D.ins C₁ ∩ D.ins C₂ ⊆ C₁.V ∩ C₂.V := by
  have : ConnectedSpace Shat := cap.connected
  have hedge : ∀ {e}, e ∈ C₁.E → e ∉ C₂.E := fun {e} h₃ h₄ ↦ by
    obtain ⟨u, v, huv, hc, -⟩ | ⟨u, hc, -⟩ := D.rad.G.edge_cond e (hC₁.1.2 h₃)
    · have m₁ : ∀ {X : Drawing Shat}, X.IsSubdrawing D.rad.G → e ∈ X.E → u ∈ X.V ∧ v ∈ X.V
        := fun {X} hX he ↦ by
        have : closure e ∩ X.V = {u, v} := by rw [hX.closure_inter_V he, hc]
        exact ⟨(this ▸ mem_insert _ _ : u ∈ closure e ∩ X.V).2, (this ▸ mem_insert_of_mem _ rfl : v
          ∈ closure e ∩ X.V).2⟩
      exact huv (hone ⟨(m₁ hC₁.1 h₃).1, (m₁ hC₂.1 h₄).1⟩ ⟨(m₁ hC₁.1 h₃).2, (m₁ hC₂.1 h₄).2⟩)
    · obtain ⟨v, hv, w, hw, hset⟩ := D.rad.edge_ends (hC₁.1.2 h₃)
      have hne : cap.emb v ≠ w := fun h ↦ hw.2 (h ▸ mem_image_of_mem _ hv)
      have m₁ : cap.emb v ∈ ({u} : Set Shat) := hc ▸ hset ▸ mem_insert _ _
      have m₂ : w ∈ ({u} : Set Shat) := hc ▸ hset ▸ mem_insert_of_mem _ rfl
      exact hne ((mem_singleton_iff.1 m₁).trans (mem_singleton_iff.1 m₂).symm)
  have hUU : ∀ {x}, x ∈ C₁.U → x ∈ C₂.U → x ∈ C₁.V ∩ C₂.V := fun {x} h₃ h₄ ↦ by
    rcases U_inter_cases hC₁.1 hC₂.1 h₃ h₄ with h | ⟨e, he₁, he₂, -⟩
    · exact h
    · exact (hedge he₁ he₂).elim
  have hw : ∃ w, C₁.U ∩ C₂.U ⊆ {w} := by
    by_cases hne : (C₁.V ∩ C₂.V).Nonempty
    · obtain ⟨w, hw⟩ := hne
      exact ⟨w, fun x hx ↦ hone (hUU hx.1 hx.2) hw⟩
    · refine ⟨r₁, fun x hx ↦ (hne ⟨x, hUU hx.1 hx.2⟩).elim⟩
  obtain ⟨w, hw⟩ := hw
  have d₁ := int_disjoint hrep hC₁ hC₂ hl₁ hl₂ hw h₁ h₁' h₂ h₂'
  have d₂ := int_disjoint hrep hC₂ hC₁ hl₂ hl₁ (by rwa [Set.inter_comm]) h₂ h₂' h₁ h₁'
  have hi₁ := D.ins_spec hC₁ hl₁
  have hi₂ := D.ins_spec hC₂ hl₂
  rintro x ⟨hx₁, hx₂⟩
  have hb₁ : x ∈ C₁.U := by
    by_contra hn
    exact disjoint_left.1 d₂ ⟨hx₁, fun h ↦ hn (hi₁.2.2.2.1 ▸ h)⟩ hx₂
  have hb₂ : x ∈ C₂.U := by
    by_contra hn
    exact disjoint_left.1 d₁ ⟨hx₂, fun h ↦ hn (hi₂.2.2.2.1 ▸ h)⟩ hx₁
  exact hUU hb₁ hb₂

variable (hS : IsSurface S) (h3 : D.P.Γ.IsInternallyThreeConnected)
include hS h3

/-- **The third shape**, from a drawing `P` of the two circuits and the line. -/
theorem outer_of_two [Nonempty S] {n : ℕ} (_hn₁ : 1 ≤ n) (hn : n < D.rep) {C₁ C₂ : Drawing Shat}
  (hC₁ : C₁.IsCircuitOf D.rad.G) (hC₂ : C₂.IsCircuitOf D.rad.G)
    (hc₁ : C₁.E.ncard ≤ 2 * n) (hc₂ : C₂.E.ncard ≤ 2 * n)
    (hlink₁ : GM18.IsLambdaLinkedTo D.tb.lambdaOrder D.𝒯 (partIn cap D.P.Γ (D.ins C₁))
      (partIn cap D.P.Γ (closure (D.ins C₁)ᶜ)))
    (hlink₂ : GM18.IsLambdaLinkedTo D.tb.lambdaOrder D.𝒯 (partIn cap D.P.Γ (D.ins C₂))
      (partIn cap D.P.Γ (closure (D.ins C₂)ᶜ)))
    {r₁ r₂ : Shat} (hr₁ : r₁ ∈ D.rad.poles) (hr₂ : r₂ ∈ D.rad.poles) (hne : r₁ ≠ r₂)
      (hi₁ : r₁ ∈ D.ins C₁) (hi₂ : r₂ ∈ D.ins C₂) (hi₁' : r₁ ∉ D.ins C₂)
    (hrange₁ : C₁.U ⊆ range cap.emb) (hrange₂ : C₂.U ⊆ range cap.emb)
    (hO₁ : IsOArc (cap.emb ⁻¹' C₁.U)) {a₁ b₁ : S} (hab₁ : a₁ ≠ b₁) (ha₁ : a₁ ∈ cap.emb ⁻¹' C₁.U ∩
      D.P.Γ.V) (hb₁ : b₁ ∈ cap.emb ⁻¹' C₁.U ∩ D.P.Γ.V)
    (hO₂ : IsOArc (cap.emb ⁻¹' C₂.U)) {a₂ b₂ : S} (hab₂ : a₂ ≠ b₂) (ha₂ : a₂ ∈ cap.emb ⁻¹' C₂.U ∩
      D.P.Γ.V) (hb₂ : b₂ ∈ cap.emb ⁻¹' C₂.U ∩ D.P.Γ.V)
    {L : Set S} {a b : S} (hL : (L = {a} ∧ a = b) ∨ IsLineWithEnds L a b) {P : Drawing Shat}
      (hPs : P.IsSubdrawing D.rad.G) (hPr : P.U ⊆ range cap.emb)
    (hPi : ∀ v ∈ P.V, ∃ e ∈ P.E, v ∈ closure e) (hPU : P.U = C₁.U ∪ C₂.U ∪ cap.emb '' L)
      (hLi₁ : cap.emb '' L ∩ D.ins C₁ = {cap.emb a})
    (hLi₂ : cap.emb '' L ∩ D.ins C₂ = {cap.emb b}) (hbd : Disjoint (cap.emb '' bd S) P.U)
      (hinter : D.ins C₁ ∩ D.ins C₂ ⊆ {cap.emb a})
    (hsize : P.V.ncard + P.E.ncard ≤ 8 * n) (haC : cap.emb a ∈ C₁.U) (hbC : cap.emb b ∈ C₂.U) : ∃ 𝓓
      K, IsOuterData D n 𝓓 K := by
  classical
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hj := cap.isClosedEmbedding hS
  have hlt₁ : C₁.E.ncard < 2 * D.rep := by omega
  have hlt₂ : C₂.E.ncard < 2 * D.rep := by omega
  have hd₁ := D.ins_spec hC₁ hlt₁
  have hd₂ := D.ins_spec hC₂ hlt₂
  have hbd₁ : discBd (D.ins C₁) = C₁.U := hd₁.2.2.2.1
  have hbd₂ : discBd (D.ins C₂) = C₂.U := hd₂.2.2.2.1
  have hfr₁ : frontier (D.ins C₁) = C₁.U := by
    rw [IsClosedDisc.frontier_eq_discBd hT hd₁.2.2.1, hbd₁]
  have hfr₂ : frontier (D.ins C₂) = C₂.U := by
    rw [IsClosedDisc.frontier_eq_discBd hT hd₂.2.2.1, hbd₂]
  have hcl : ∀ {Δ : Set Shat} {x}, x ∈ frontier Δ → x ∈ closure Δᶜ := fun {Δ x} hx ↦ by
    rw [frontier_eq_closure_inter_closure] at hx
    exact hx.2
  have hmem₁ : cap.emb a ∈ cap.emb '' L ∩ D.ins C₁ := by rw [hLi₁]; rfl
  have hmem₂ : cap.emb b ∈ cap.emb '' L ∩ D.ins C₂ := by rw [hLi₂]; rfl
  have hout₁ : D.ins C₁ ⊆ closure (D.ins C₂)ᶜ := fun x hx ↦ by
    by_cases hx₂ : x ∈ D.ins C₂
    · have h₁ : x = cap.emb a := hinter ⟨hx, hx₂⟩
      subst h₁
      have h₂ : cap.emb a ∈ cap.emb '' L ∩ D.ins C₂ := ⟨hmem₁.1, hx₂⟩
      rw [hLi₂] at h₂
      rw [mem_singleton_iff.1 h₂]
      exact hcl (hfr₂ ▸ hbC)
    · exact subset_closure hx₂
  have hout₂ : D.ins C₂ ⊆ closure (D.ins C₁)ᶜ := fun x hx ↦ by
    by_cases hx₁ : x ∈ D.ins C₁
    · have h₁ : x = cap.emb a := hinter ⟨hx₁, hx⟩
      rw [h₁]
      exact hcl (hfr₁ ▸ haC)
    · exact subset_closure hx₁
  obtain ⟨hinterK, hfeat, hlines, hcV, hcE⟩ := comap_facts D.rad D.P.fits hPs hPr hj hPi
  set K : Drawing S := GM19.Drawing.comap P hj hPr with hKdef
  have hKU : cap.emb '' K.U = P.U := image_preimage_eq_of_subset hPr
  have hmemK : ∀ {x}, x ∈ K.U ↔ (cap.emb x ∈ C₁.U ∨ cap.emb x ∈ C₂.U) ∨ x ∈ L := fun {x} ↦ by
    change cap.emb x ∈ P.U ↔ _
    rw [hPU]
    refine or_congr Iff.rfl ⟨?_, mem_image_of_mem _⟩
    rintro ⟨y, hy, hxy⟩
    exact cap.isEmbedding.injective hxy ▸ hy
  obtain ⟨Θ₁, hΘ₁, Θ₂, hΘ₂, hΘne, hrd₁, hrd₂⟩ := D.pole_cuffs_ne hr₁ hr₂ hne
  have hring₁ : ∀ {x w : S}, cap.emb x ∈ C₁.U → x ≠ w → ∃ E ⊆ K.U \ {w}, x ∈ E ∧ IsPreconnected E ∧
    (E ∩ D.P.Γ.V).Nonempty := fun {x w} hx hne ↦ by
    obtain ⟨E, hE, hxE, hconn, hm⟩ := ring_part hO₁ ha₁ hb₁ hab₁ hx hne
    exact ⟨E, hE.trans (sdiff_subset_sdiff_left fun z hz ↦ hmemK.2 (Or.inl (Or.inl hz))), hxE,
      hconn, hm⟩
  have hring₂ : ∀ {x w : S}, cap.emb x ∈ C₂.U → x ≠ w → ∃ E ⊆ K.U \ {w}, x ∈ E ∧ IsPreconnected E ∧
    (E ∩ D.P.Γ.V).Nonempty := fun {x w} hx hne ↦ by
    obtain ⟨E, hE, hxE, hconn, hm⟩ := ring_part hO₂ ha₂ hb₂ hab₂ hx hne
    exact ⟨E, hE.trans (sdiff_subset_sdiff_left fun z hz ↦ hmemK.2 (Or.inl (Or.inr hz))), hxE,
      hconn, hm⟩
  have hΔne : D.ins C₁ ≠ D.ins C₂ := fun h ↦ hi₁' (h ▸ hi₁)
  have hcover : ∀ Δ ∈ ({D.ins C₁, D.ins C₂} : Set (Set Shat)), ∀ v ∈ D.P.Γ.V, cap.emb v ∈ Δ
    → cap.emb v ∈ closure Δᶜ → v ∈ K.U := by
    rintro Δ (rfl | rfl) v - h₁ h₂
    · have : cap.emb v ∈ frontier (D.ins C₁) := by
        rw [frontier_eq_closure_inter_closure]
        exact ⟨subset_closure h₁, h₂⟩
      rw [hfr₁] at this
      exact hmemK.2 (Or.inl (Or.inl this))
    · have : cap.emb v ∈ frontier (D.ins C₂) := by
        rw [frontier_eq_closure_inter_closure]
        exact ⟨subset_closure h₁, h₂⟩
      rw [hfr₂] at this
      exact hmemK.2 (Or.inl (Or.inr this))
  refine ⟨{D.ins C₁, D.ins C₂}, K, Or.inr (Or.inr ⟨D.ins C₁, D.ins C₂, L, a, b, Θ₁, Θ₂, rfl,
    hΔne, hd₁.2.2.1, hd₂.2.2.1, hbd₁.trans_subset hrange₁, hbd₂.trans_subset hrange₂, hL,
    ?_, hLi₁, hLi₂, ?_, ?_, ?_, hΘ₁, hΘ₂, hΘne, ⟨r₁, hrd₁, hi₁⟩, ⟨r₂, hrd₂, hi₂⟩⟩),
      (finite_singleton _).insert _, ?_, ?_, hfeat, hinterK, hlines, ?_, ?_, hcover, ?_, ?_⟩
  · rw [hKU, hPU, hbd₁, hbd₂]
  · refine hbd.mono_right (union_subset ?_ ?_)
    · rw [hbd₁, hPU]
      exact fun x hx ↦ Or.inl (Or.inl hx)
    · rw [hPU]
      exact fun x hx ↦ Or.inr hx
  · intro x hx y hy
    have h₁ : x ∈ P.U := by
      rw [hPU]
      exact Or.inl (Or.inr (hbd₂ ▸ hx.1))
    exact (disjoint_left.1 hbd hx.2 h₁).elim
  · exact hinter
  · rw [ncard_pair hΔne]
  · refine family_of_discs ((finite_singleton _).insert _) ?_ ?_ ?_
    · rintro _ (rfl | rfl)
      · exact hlink₁
      · exact hlink₂
    · rintro _ (rfl | rfl)
      · have := disc_order hS h3 D.rad hC₁ hd₁.2.2.1 hbd₁
        omega
      · have := disc_order hS h3 D.rad hC₂ hd₂.2.2.1 hbd₂
        omega
    · rintro _ (rfl | rfl) _ (rfl | rfl) h
      · exact (h rfl).elim
      · exact hout₁
      · exact hout₂
      · exact (h rfl).elim
  · rw [hcV, hcE]
    exact hsize
  · have hset : ∀ {x}, cap.emb x ∈ C₁.U ∨ cap.emb x ∈ C₂.U ↔ x ∈ ⋃₀ {cap.emb ⁻¹' C₁.U, cap.emb ⁻¹'
      C₂.U} := fun {x} ↦ by simp
    rcases hL with ⟨rfl, rfl⟩ | hl
    · refine ⟨{cap.emb ⁻¹' C₁.U, cap.emb ⁻¹' C₂.U}, ∅, (finite_singleton _).insert _,
        finite_empty, ?_, by simp, ?_⟩
      · rintro _ (rfl | rfl)
        · exact hO₁
        · exact hO₂
      · ext x
        rw [hmemK]
        simp only [sUnion_empty, union_empty]
        refine ⟨?_, fun h ↦ Or.inl (hset.2 h)⟩
        rintro (h | h)
        · exact hset.1 h
        · rw [mem_singleton_iff.1 h]
          exact hset.1 (Or.inl haC)
    · refine ⟨{cap.emb ⁻¹' C₁.U, cap.emb ⁻¹' C₂.U}, {L}, (finite_singleton _).insert _,
        finite_singleton _, ?_, ?_, ?_⟩
      · rintro _ (rfl | rfl)
        · exact hO₁
        · exact hO₂
      · rintro _ rfl
        refine ⟨a, b, ?_, hl, Or.inr (hset.1 (Or.inl haC)), Or.inr (hset.1 (Or.inr hbC))⟩
        intro h
        obtain ⟨f, h₀, h₁⟩ := hl
        have := f.injective (Subtype.ext (h₀.trans (h.trans h₁.symm)))
        exact zero_ne_one this
      · ext x
        rw [hmemK, sUnion_singleton]
        exact or_congr hset Iff.rfl
  · rintro v hv Δ (rfl | rfl)
    · rcases hmemK.1 hv with (h | h) | h
      · exact hcl (hfr₁ ▸ h)
      · exact hout₂ (D.U_subset_ins hC₂ hlt₂ h)
      · by_cases hvi : cap.emb v ∈ D.ins C₁
        · have hvu : cap.emb v ∈ cap.emb '' L ∩ D.ins C₁ := ⟨mem_image_of_mem _ h, hvi⟩
          rw [hLi₁] at hvu
          rw [mem_singleton_iff.1 hvu]
          exact hcl (hfr₁ ▸ haC)
        · exact subset_closure hvi
    · rcases hmemK.1 hv with (h | h) | h
      · exact hout₁ (D.U_subset_ins hC₁ hlt₁ h)
      · exact hcl (hfr₂ ▸ h)
      · by_cases hvi : cap.emb v ∈ D.ins C₂
        · have hvu : cap.emb v ∈ cap.emb '' L ∩ D.ins C₂ := ⟨mem_image_of_mem _ h, hvi⟩
          rw [hLi₂] at hvu
          rw [mem_singleton_iff.1 hvu]
          exact hcl (hfr₂ ▸ hbC)
        · exact subset_closure hvi
  · intro w x hx hne
    rcases hmemK.1 hx with (h | h) | h
    · exact hring₁ h hne
    · exact hring₂ h hne
    · rcases hL with ⟨rfl, -⟩ | hl
      · exact hring₁ (by rw [mem_singleton_iff.1 h]; exact haC) hne
      · exact line_anchor hl (fun z hz ↦ hmemK.2 (Or.inr hz)) (fun w' hne' ↦ hring₁ haC hne')
          (fun w' hne' ↦ hring₂ hbC hne') h hne

end TangleDatum

end GraphMinor.GM19
