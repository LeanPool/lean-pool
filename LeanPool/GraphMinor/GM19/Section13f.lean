/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section13e

/-!
# Graph Minors XIX, Section 13: (13.4)

The proof is the paper's. If the disc `Δ` of the fan holds a point of `U(H)` other than `u`, then
all of `U(H)` lies in `Δ`, every
spoke passes through `u`, no small enclave surrounds `u`, and so `u` is a hub of radius `ρ -
|E(T)|`. Then `H` is not optimal.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

namespace TangleDatum

variable {D : TangleDatum cap χ} {W : Set Shat} {H : Drawing Shat} {ρ : ℕ} {r v₁ v₂ u h : Shat} {f₁
  f₂ : Set Shat}
  {A₁ : GraphWalk D.rad.G.toGraph v₁ u} {A₂ : GraphWalk D.rad.G.toGraph v₂ u} {T : GraphWalk
    D.rad.G.toGraph u h} {C : Drawing Shat}

/-- A line is preconnected. -/
theorem isPreconnected_of_isLineWithEnds {X : Type*} [TopologicalSpace X] {L : Set X} {a b : X}
  (h : IsLineWithEnds L a b) :
    IsPreconnected L :=
  GraphMinor.Surface.IsLineWithEnds.isPreconnected h

omit [T2Space S] in
omit [T2Space Shat] in
/-- A circuit of `Γ*` has at least two vertices. -/
theorem IsCircuit.two_vertices (D : TangleDatum cap χ) {F : Drawing Shat}
  (hF : F.IsCircuitOf D.rad.G) : F.V.ncard ≠ 1 := by
  intro hc
  obtain ⟨u, K, -, hpos, -, hE⟩ := hF.2
  obtain ⟨y, hy⟩ := ncard_eq_one.mp hc
  cases K with
  | nil _ => simp [GraphWalk.length] at hpos
  | @cons _ c _ e hl q =>
    have heF : e ∈ F.E := by rw [hE]; simp
    have heG := hF.1.2 heF
    obtain ⟨a, ha, b, hb, hcap⟩ := D.rad.isPreRadial.2.2.2.2.1 e heG
    have hl' : D.rad.G.toGraph.IsLink e a b := ⟨heG, D.rad.isPreRadial.2.1 ha, hb.1, hcap⟩
    have h₁ := Drawing.IsLink.mem_V_of_sub hF.1 hl' heF
    rw [hy] at h₁
    have e₁ : a = y := h₁.1
    have e₂ : b = y := h₁.2
    exact hb.2 (e₂.trans e₁.symm ▸ ha)

omit [T2Space S] in
/-- Step of (13.4): a point of `U(H)` in `Δ`, not `u`, brings all of `U(H)` into `Δ`. -/
theorem IsFan.hub_inside (hf : D.IsFan W H ρ r f₁ f₂ A₁ A₂ T) (hC : D.IsFanCircuit r f₁ f₂ A₁ A₂ C)
  {x : Shat} (hx : x ∈ H.U)
    (hxi : x ∈ D.ins C) (hxu : x ≠ u) : H.U ⊆ D.ins C := by
  have : ConnectedSpace Shat := cap.connected
  have hlt := (hf.card_lt hC).2
  obtain ⟨hcl, hfr, hU⟩ := ins_facts_of_length (D.isSlope (by omega)) hC.circuit.2 hC.circuit.1 hlt
  have hint : x ∈ interior (D.ins C) := (D.ins_diff_iff hC.circuit hlt).mp ⟨hxi, fun hu ↦ hxu
    (hf.hub_meet hC hx hu).1⟩
  intro y hy
  by_cases hyu : y = u
  · subst hyu
    exact hU (C.V_subset_U ((hC.mem_V _).mpr (.inr (.inl A₁.end_mem_support))))
  by_cases hxy : x = y
  · exact hxy ▸ hxi
  rcases hf.hub.hub_cond with ⟨hc, hE, -⟩ | ⟨hen, -, -⟩
  · have hUV : H.U = H.V := by
      rw [H.U_eq, hE]
      simp
    rw [hUV] at hx hy
    obtain ⟨z, hz⟩ := ncard_eq_one.mp hc
    rw [hz] at hx hy
    exact absurd (hx.trans hy.symm) hxy
  · obtain ⟨-, -, -, hcF, -⟩ := hen
    obtain ⟨A, B, hA, hB, hAB, hAB'⟩ := (IsCircuit.isOArc_U hcF.2).lines hx hy hxy
    have hAU : A ⊆ H.U := hAB ▸ subset_union_left
    have hBU : B ⊆ H.U := hAB ▸ subset_union_right
    have hL : ∃ L : Set Shat, IsLineWithEnds L x y ∧ L ⊆ H.U ∧ u ∉ L := by
      by_cases huA : u ∈ A
      · refine ⟨B, hB, hBU, fun huB ↦ ?_⟩
        have : u ∈ A ∩ B := ⟨huA, huB⟩
        rw [hAB'] at this
        rcases this with h' | h'
        · exact hxu h'.symm
        · exact hyu h'.symm
      · exact ⟨A, hA, hAU, huA⟩
    obtain ⟨L, hLl, hLU, hLu⟩ := hL
    have hcon := isPreconnected_of_isLineWithEnds hLl
    have hxL : x ∈ L := by
      obtain ⟨f, h₀, -⟩ := hLl
      rw [← h₀]
      exact (f 0).2
    have hyL : y ∈ L := by
      obtain ⟨f, -, h₁⟩ := hLl
      rw [← h₁]
      exact (f 1).2
    have hcov : L ⊆ interior (D.ins C) ∪ (D.ins C)ᶜ := by
      intro p hp
      by_cases hpi : p ∈ D.ins C
      · refine .inl ((D.ins_diff_iff hC.circuit hlt).mp ⟨hpi, fun hu ↦ ?_⟩)
        have := (hf.hub_meet hC (hLU hp) hu).1
        exact hLu (this ▸ hp)
      · exact .inr hpi
    have := hcon.subset_left_of_subset_union isOpen_interior hcl.isOpen_compl
      (disjoint_left.mpr fun p h₁ h₂ ↦ h₂ (interior_subset h₁)) hcov ⟨x, hxL, hint⟩
    exact interior_subset (this hyL)

/-- Step of (13.4): if `U(H) ⊆ Δ` then every spoke passes through `u`. The proof: a spoke joins
`V(H) ⊆ Δ` to a vertex of `bd(W)`, so it
meets `bd(Δ)`, and then (13.2) applies. -/
theorem IsFan.spoke_at (hf : D.IsFan W H ρ r f₁ f₂ A₁ A₂ T) (hC : D.IsFanCircuit r f₁ f₂ A₁ A₂ C)
  (hsub : D.ins C ⊆ W)
    (hHC : H.U ⊆ D.ins C) {v : Shat} (hv : v ∈ (cap.emb '' D.Γ.V) ∩ discBd W) :
    ∃ A : GraphWalk D.rad.G.toGraph v u, A.length + T.length ≤ ρ := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hlt := (hf.card_lt hC).2
  obtain ⟨h', K, hK⟩ := hf.hub.exists_spoke hv
  have hout : v ∉ D.ins C \ C.U := by
    intro h₁
    have hi := interior_mono hsub ((D.ins_diff_iff hC.circuit hlt).mp h₁)
    have hvf : v ∈ frontier W := by
      rw [IsClosedDisc.frontier_eq_discBd hT hf.hub.is_disc]
      exact hv.2
    exact hvf.2 hi
  obtain ⟨a, ha, haC⟩ := D.walk_meets_circuit hC.circuit hlt K.reverse (hHC
    (H.V_subset_U hK.2.h_mem)) hout
  have ha' : a ∈ K.support := by simpa [GraphWalk.support_reverse] using ha
  obtain rfl := hf.spoke_end hC hK ha' haC
  obtain ⟨L, R, rfl⟩ := K.exists_append_of_mem ha'
  obtain ⟨X, rfl, -, -⟩ := hf.spoke_tail hC hK haC
  refine ⟨L.append X, ?_⟩
  have := (hf.hub.spoke_length hK).1
  simp only [GraphWalk.length_append] at this ⊢
  omega

/-- Step of (13.4): the edges and vertices of the fan's circuit lie in `ins(F)` if `v₁, v₂, u` lie
there. -/
theorem IsFan.circuit_in_ins (hf : D.IsFan W H ρ r f₁ f₂ A₁ A₂ T) (hC : D.IsFanCircuit r f₁ f₂ A₁
  A₂ C) {F : Drawing Shat}
    (hFe : IsEnclave D.tb D.ord D.𝒯 F) (hv₁ : v₁ ∈ D.ins F \ F.U) (hv₂ : v₂ ∈ D.ins F \ F.U)
      (hu : u ∈ D.ins F) :
    C.U ⊆ D.ins F := by
  have : ConnectedSpace Shat := cap.connected
  obtain ⟨ord', 𝒯', h𝒯', hc, hlt, -⟩ := id hFe
  have hlt' : F.E.ncard < 2 * D.rep := hlt
  obtain ⟨hcl, hfr, hU⟩ := ins_facts_of_length (D.isSlope (by omega)) hc.2 hc.1 hlt'
  have hnil : ∀ {v : Shat} {A : GraphWalk D.rad.G.toGraph v u}, D.IsSpokeWalk W H (A.append T)
    → v ∈ D.ins F \ F.U →
      (∀ z ∈ A.support, z ∈ D.ins F) ∧ ∀ e ∈ A.edges, e ⊆ D.ins F := by
    intro v A hA hv
    have hv' : v ∈ (D.rad.G.V) := A.mem_vertexSet_of_mem_support A.start_mem_support
    have e : A.append T = (GraphWalk.nil hv').append (A.append T) := rfl
    rw [e] at hA
    exact hA.part_in_ins hFe hv.1 hu
  obtain ⟨hs₁, he₁⟩ := hnil hf.spoke₁ hv₁
  obtain ⟨hs₂, he₂⟩ := hnil hf.spoke₂ hv₂
  obtain ⟨hf₁, hr⟩ := D.edge_inside_of_mem hc hlt' hf.link₁.symm hv₁
  obtain ⟨hf₂, -⟩ := D.edge_inside_of_mem hc hlt' hf.link₂.symm hv₂
  rw [C.U_eq]
  refine union_subset (fun x hx ↦ ?_) (iUnion₂_subset fun e he ↦ closure_minimal ?_ hcl)
  · rcases (hC.mem_V x).mp hx with rfl | h₁ | h₂
    · exact hr
    · exact hs₁ x h₁
    · exact hs₂ x h₂
  · rcases (hC.mem_E e).mp he with rfl | rfl | h₁ | h₂
    · exact hf₁
    · exact hf₂
    · exact he₁ e h₁
    · exact he₂ e h₂

/-- Step of (13.4): no small enclave has `u` strictly inside. -/
theorem IsFan.no_enclave (hf : D.IsFan W H ρ r f₁ f₂ A₁ A₂ T) (hC : D.IsFanCircuit r f₁ f₂ A₁ A₂ C)
  {x : Shat} (hx : x ∈ H.U)
    (hxi : x ∈ D.ins C \ C.U) (hHC : H.U ⊆ D.ins C) {F : Drawing Shat}
      (hFe : IsEnclave D.tb D.ord D.𝒯 F)
    (hFle : F.E.ncard ≤ 4 * ρ + 4) : u ∉ D.ins F \ F.U := by
  have : ConnectedSpace Shat := cap.connected
  intro hu
  have hrep := hf.hub.rep_ge
  have hlt := (hf.card_lt hC).2
  obtain ⟨ord', 𝒯', h𝒯', hc, hlt₀, Δ, hins, hd⟩ := id hFe
  have hlt' : F.E.ncard < 2 * D.rep := hlt₀
  have hsl := D.isSlope (by omega)
  obtain ⟨hcl, hfr, hU⟩ := ins_facts_of_length hsl hc.2 hc.1 hlt'
  obtain ⟨hclC, hfrC, hUC⟩ := ins_facts_of_length hsl hC.circuit.2 hC.circuit.1 hlt
  have hh := hf.spoke₁.2.h_mem
  have hlen : ∀ {Y : Drawing Shat}, Y.E.ncard < 2 * D.rep → Y.length < 2 * D.rep := fun h' ↦ h'
  -- `h` is not strictly inside `F`, and if `v₁, v₂` are, then we are done.
  have hstep : h ∉ D.ins F \ F.U → C.U ⊆ D.ins F := by
    intro hhF
    have side : ∀ {v : Shat} {A : GraphWalk D.rad.G.toGraph v u}, D.IsSpokeWalk W H (A.append T)
      → v ∈ D.ins F \ F.U := by
      intro v A hA
      have hmem : u ∈ (walkDrawing D.rad.G (A.append T)).U ∩ D.ins F := by
        refine ⟨(mem_walkDrawing_U _ _).mpr (.inl ?_), hu.1⟩
        exact (GraphWalk.mem_support_append A T).mpr (.inl A.end_mem_support)
      rcases (theorem_13_3_proof hA.2 hFe).2 (fun hs ↦ hu.2 (hs hmem)) with h' | h'
      · exact h'
      · exact absurd h' hhF
    exact hf.circuit_in_ins hC hFe (side hf.spoke₁) (side hf.spoke₂) hu.1
  have hmono : C.U ⊆ D.ins F → D.ins C ⊆ D.ins F := fun h' ↦
    hsl.monotone C F hC.circuit.2 hC.circuit.1 hlt hc.2 hc.1 hlt' h'
  rcases hf.hub.hub_cond with ⟨hcard, hE, hne⟩ | ⟨hen, hHle, hne⟩
  · obtain ⟨z, hz⟩ := ncard_eq_one.mp hcard
    have hhz : h = z := by
      rw [hz] at hh
      exact hh
    subst hhz
    have hUV : H.U = H.V := by
      rw [H.U_eq, hE]
      simp
    have hnot : h ∉ D.ins F \ F.U := fun h' ↦ by
      apply hne F hFe hFle
      rw [hz]
      exact singleton_subset_iff.mpr h'
    have hxh : x = h := by
      rw [hUV, hz] at hx
      exact hx
    subst hxh
    have hi := interior_mono (hmono (hstep hnot)) ((D.ins_diff_iff hC.circuit hlt).mp hxi)
    exact hnot ((D.ins_diff_iff hc hlt').mpr hi)
  · have hHlt : H.E.ncard < 2 * D.rep := by omega
    obtain ⟨ord₂, 𝒯₂, h𝒯₂, hcH, hlt₂, Δ₂, hins₂, hd₂⟩ := id hen
    obtain ⟨hclH, hfrH, hUH⟩ := ins_facts_of_length hsl hcH.2 hcH.1 hHlt
    have hne' : F ≠ H := by
      rintro rfl
      have hm := hsl.monotone F C hc.2 hc.1 hlt' hC.circuit.2 hC.circuit.1 hlt hHC
      have hi := interior_mono hm ((D.ins_diff_iff hc hlt').mp hu)
      exact (D.ins_diff_iff hC.circuit hlt).mpr hi |>.2 (C.V_subset_U ((hC.mem_V u).mpr (.inr
        (.inl A₁.end_mem_support))))
    have hnotsub : ¬ H.U ⊆ D.ins F := hne F hFe hne' hFle
    have hnot : h ∉ D.ins F \ F.U := by
      intro h'
      obtain rfl := D.eq_ins_of_isInsOf hins
      obtain rfl := D.eq_ins_of_isInsOf hins₂
      rcases theorem_8_6_proof χ.isSurface D.P.fits.internally_three_connected D.tb D.isTangle h𝒯₂
        h𝒯' hins₂ hins hd₂ hd with h₁ | h₁ | h₁
      · exact hnotsub (hUH.trans h₁)
      · have hi := interior_mono h₁ ((D.ins_diff_iff hc hlt').mp h')
        exact (D.ins_diff_iff hcH hHlt).mpr hi |>.2 (H.V_subset_U hh)
      · have : h ∈ D.ins H ∩ D.ins F := ⟨hUH (H.V_subset_U hh), h'.1⟩
        rw [h₁] at this
        exact h'.2 this.2
    exact hnotsub (hHC.trans (hmono (hstep hnot)))

/-- **The core of (13.4).** `u` is the only possible point of `U(H)` in `Δ`, and no spoke enters the
interior of `Δ`. -/
theorem IsFan.main (hf : D.IsFan W H ρ r f₁ f₂ A₁ A₂ T) (hC : D.IsFanCircuit r f₁ f₂ A₁ A₂ C)
    (hopt : D.IsOptimalWheelHub W H ρ) {Δ : Set Shat} (hΔ : IsClosedDisc Δ) (hΔW : Δ ⊆ W)
      (hbd : discBd Δ = C.U) :
    (∀ x ∈ Δ ∩ H.U, x = u) ∧
    ∀ (v h' : Shat) (K : GraphWalk D.rad.G.toGraph v h'), D.IsSpokeWalk W H K → Δ ∩
      (walkDrawing D.rad.G K).U ⊆ discBd Δ := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hle := (hf.card_lt hC).1
  have hlt := (hf.card_lt hC).2
  obtain rfl : Δ = D.ins C := hf.hub.eq_ins_of_disc hC.circuit (by omega) hΔ hΔW hbd
  have hc := hC.circuit
  obtain ⟨hcl, hfr, hU⟩ := ins_facts_of_length (D.isSlope (by omega)) hc.2 hc.1 hlt
  have huC : u ∈ C.U := C.V_subset_U ((hC.mem_V u).mpr (.inr (.inl A₁.end_mem_support)))
  have hfirstclaim : ∀ x ∈ D.ins C ∩ H.U, x = u := by
    rintro x ⟨hxi, hx⟩
    by_contra hxu
    have hHC := hf.hub_inside hC hx hxi hxu
    have hxi' : x ∈ D.ins C \ C.U := ⟨hxi, fun hu ↦ hxu (hf.hub_meet hC hx hu).1⟩
    have huW : u ∈ W := hΔW (hU huC)
    have hub := hf.hub.hub_at hf.u_mem_G T hf.spoke₁.2.h_mem hf.T_lt ⟨huW, hf.u_notMem_bd⟩
      (fun v hv ↦ hf.spoke_at hC hΔW hHC hv) (fun F h₁ h₂ ↦ hf.no_enclave hC hx hxi' hHC h₁ h₂)
    have hρ : ρ ≤ ρ - T.length := by
      rw [hopt.ρ_eq_radius, ← hopt.ρ_eq_radius]
      have := Nat.sInf_le (s := {ρ : ℕ | ∃ H : Drawing Shat, D.IsWheelHubOfRadius W H ρ}) ⟨_, hub⟩
      rw [← wheelRadius, ← hopt.ρ_eq_radius] at this
      exact this
    have hT0 : T.length = 0 := by
      have := hf.T_lt
      omega
    have hhu : u = h := GraphWalk.eq_of_length_eq_zero hT0
    rw [hT0, Nat.sub_zero] at hub
    have hcard : H.V.ncard = 1 := by
      rcases hopt.one_vertex_priority with h' | h'
      · exact h'
      · exact absurd ⟨_, hub, by rw [(point_drawing_facts D.rad.G hf.u_mem_G).1,
          ncard_singleton]⟩ h'
    rcases hf.hub.hub_cond with ⟨-, hE, -⟩ | ⟨⟨-, -, -, hcF, -⟩, -, -⟩
    · have hUV : H.U = H.V := by
        rw [H.U_eq, hE]
        simp
      obtain ⟨z, hz⟩ := ncard_eq_one.mp hcard
      have hh := hf.spoke₁.2.h_mem
      rw [hUV, hz] at hx
      rw [hz] at hh
      have e₁ : x = z := hx
      have e₂ : h = z := hh
      exact hxu (e₁.trans (e₂.symm.trans hhu.symm))
    · exact IsCircuit.two_vertices D hcF hcard
  have hd_eq : discBd (D.ins C) = C.U := hbd
  -- The part `T` misses the strict inside.
  have hTout : ∀ {p : Shat}, p ∈ (walkDrawing D.rad.G T.reverse).U → p ∈ D.ins C → p ∈ C.U := by
    intro p hp hpi
    have hTs : T.IsSimple := (GraphWalk.IsSimple.of_append hf.spoke₁.1).2
    have hhout : h ∉ D.ins C \ C.U := by
      intro h₁
      have e := hfirstclaim h ⟨h₁.1, H.V_subset_U hf.spoke₁.2.h_mem⟩
      exact h₁.2 (e ▸ huC)
    refine D.part_outside hc hlt T.reverse hTs.reverse hhout (fun y hy hyC ↦ ?_) hp hpi
    have hy' : y ∈ T.support := by simpa [GraphWalk.support_reverse] using hy
    rcases (hC.mem_V y).mp hyC with rfl | h₁ | h₂
    · exact absurd ((GraphWalk.mem_support_append A₁ T).mpr (.inr hy'))
        (hf.r_notMem_spoke hf.spoke₁)
    · exact GraphWalk.inter_of_simple hf.spoke₁.1 h₁ hy'
    · exact GraphWalk.inter_of_simple hf.spoke₂.1 h₂ hy'
  refine ⟨hfirstclaim, ?_⟩
  rintro v h' K hK p ⟨hpi, hpK⟩
  rw [hd_eq]
  have hout : v ∉ D.ins C \ C.U := by
    intro h₁
    have hi := interior_mono hΔW ((D.ins_diff_iff hc hlt).mp h₁)
    have hvf : v ∈ frontier W := by
      rw [IsClosedDisc.frontier_eq_discBd hT hf.hub.is_disc]
      exact hK.2.v_mem.2
    exact hvf.2 hi
  by_cases hm : ∃ x ∈ K.support, x ∈ C.V
  · obtain ⟨a, haC, L, R, rfl, hfirst⟩ := GraphWalk.exists_first_mem K hm
    obtain rfl := hf.spoke_end hC hK ((GraphWalk.mem_support_append L R).mpr
      (.inl L.end_mem_support)) haC
    obtain ⟨X, rfl, hXE, hXV⟩ := hf.spoke_tail hC hK haC
    have hLs : L.IsSimple := (GraphWalk.IsSimple.of_append hK.1).1
    rcases (mem_walkDrawing_U _ _).mp hpK with hp | ⟨g, hg, hpg⟩
    · rcases (GraphWalk.mem_support_append L _).mp hp with h₁ | h₁
      · exact D.part_outside hc hlt L hLs hout hfirst ((mem_walkDrawing_U _ _).mpr (.inl h₁)) hpi
      · rcases (GraphWalk.mem_support_append X T).mp h₁ with h₂ | h₂
        · exact C.V_subset_U (hXV p h₂)
        · exact hTout ((mem_walkDrawing_U _ _).mpr (.inl (by simpa [GraphWalk.support_reverse]
            using h₂))) hpi
    · simp only [GraphWalk.edges_append, List.mem_append] at hg
      rcases hg with h₁ | h₁ | h₁
      · exact D.part_outside hc hlt L hLs hout hfirst ((mem_walkDrawing_U _ _).mpr (.inr ⟨g, h₁,
          hpg⟩)) hpi
      · exact C.closure_subset_U (hXE g h₁) hpg
      · exact hTout ((mem_walkDrawing_U _ _).mpr (.inr ⟨g, by simpa [GraphWalk.edges_reverse] using
          h₁, hpg⟩)) hpi
  · push Not at hm
    exact D.part_outside hc hlt K hK.1 hout (fun y hy hyC ↦ absurd hyC (hm y hy)) hpK hpi

/-- `U` of a joined walk. -/
theorem U_append (G : Drawing Shat) {a b c : Shat} (A : GraphWalk G.toGraph a b)
  (B : GraphWalk G.toGraph b c) :
    (walkDrawing G (A.append B)).U = (walkDrawing G A).U ∪ (walkDrawing G B).U := by
  ext x
  simp only [mem_walkDrawing_U, mem_union, GraphWalk.mem_support_append, GraphWalk.edges_append,
    List.mem_append]
  constructor
  · rintro ((h | h) | ⟨e, h | h, hx⟩)
    · exact .inl (.inl h)
    · exact .inr (.inl h)
    · exact .inl (.inr ⟨e, h, hx⟩)
    · exact .inr (.inr ⟨e, h, hx⟩)
  · rintro ((h | ⟨e, h, hx⟩) | (h | ⟨e, h, hx⟩))
    · exact .inl (.inl h)
    · exact .inr ⟨e, .inl h, hx⟩
    · exact .inl (.inr h)
    · exact .inr ⟨e, .inr h, hx⟩

/-- The walks of the two parts of a simple walk meet only at the joint. -/
theorem U_inter_of_simple (G : Drawing Shat) {a b c d : Shat} (A : GraphWalk G.toGraph a b)
  (B : GraphWalk G.toGraph c d)
    (hV : ∀ x ∈ A.support, x ∈ B.support → x = b) (hE : ∀ e ∈ A.edges, e ∉ B.edges)
      (hb : b ∈ A.support) (hb' : b ∈ B.support) :
    (walkDrawing G A).U ∩ (walkDrawing G B).U = {b} := by
  have hdis : Disjoint (walkDrawing G A).E (walkDrawing G B).E := by
    rw [walkDrawing_E, walkDrawing_E]
    exact disjoint_left.mpr fun e h₁ h₂ ↦ hE e h₁ h₂
  rw [U_inter_of_disjoint (walkDrawing_isSubdrawing _ _) (walkDrawing_isSubdrawing _ _) hdis,
    walkDrawing_V, walkDrawing_V]
  ext x
  constructor
  · rintro ⟨h₁, h₂⟩
    exact hV x h₁ h₂
  · rintro rfl
    exact ⟨hb, hb'⟩

omit [T2Space S] in
theorem IsFan.edges_disjoint_T (hf : D.IsFan W H ρ r f₁ f₂ A₁ A₂ T) : ∀ e ∈ A₁.edges, e ∉ T.edges
  := by
  intro e h₁ h₂
  have := hf.spoke₁.1.edges_nodup
  rw [GraphWalk.edges_append] at this
  exact (List.nodup_append.mp this).2.2 e h₁ e h₂ rfl

omit [T2Space S] in
theorem IsFan.edges_disjoint (hf : D.IsFan W H ρ r f₁ f₂ A₁ A₂ T) : ∀ e ∈ A₁.edges, e ∉ A₂.edges
  := by
  intro e h₁ h₂
  obtain ⟨x, y, hxy, hx, hy, hcap⟩ := D.exists_ends_of_mem_edges A₁ h₁
  obtain ⟨hx', hy'⟩ := D.ends_mem_support A₂ h₂ hcap
  exact hxy ((hf.meet x hx hx').trans (hf.meet y hy hy').symm)

omit [T2Space S] in
/-- `U` of the circuit of a fan, as in the statement of (13.4). -/
theorem IsFan.U_eq (hf : D.IsFan W H ρ r f₁ f₂ A₁ A₂ T) (hC : D.IsFanCircuit r f₁ f₂ A₁ A₂ C) :
    C.U = (walkDrawing D.rad.G A₁).U ∪ (walkDrawing D.rad.G A₂).U ∪ closure f₁ ∪ closure f₂ := by
  ext x
  rw [C.U_eq]
  simp only [mem_union, mem_iUnion, mem_walkDrawing_U, hC.mem_V, hC.mem_E, exists_prop]
  have hr : x = r → x ∈ closure f₁ := by
    rintro rfl
    have : x ∈ closure f₁ ∩ D.rad.G.V := by
      rw [hf.link₁.2.2.2]
      exact .inl rfl
    exact this.1
  constructor
  · rintro ((h | h | h) | ⟨e, (rfl | rfl | h | h), hx⟩)
    · exact .inl (.inr (hr h))
    · exact .inl (.inl (.inl (.inl h)))
    · exact .inl (.inl (.inr (.inl h)))
    · exact .inl (.inr hx)
    · exact .inr hx
    · exact .inl (.inl (.inl (.inr ⟨e, h, hx⟩)))
    · exact .inl (.inl (.inr (.inr ⟨e, h, hx⟩)))
  · rintro ((((h | ⟨e, h, hx⟩) | (h | ⟨e, h, hx⟩)) | h) | h)
    · exact .inl (.inr (.inl h))
    · exact .inr ⟨e, .inr (.inr (.inl h)), hx⟩
    · exact .inl (.inr (.inr h))
    · exact .inr ⟨e, .inr (.inr (.inr h)), hx⟩
    · exact .inr ⟨_, .inl rfl, h⟩
    · exact .inr ⟨_, .inr (.inl rfl), h⟩

omit [T2Space S] in
/-- The set in the statement of (13.4) is `U` of the circuit of the fan. -/
theorem IsFan.formula_eq (hf : D.IsFan W H ρ r f₁ f₂ A₁ A₂ T) (hC : D.IsFanCircuit r f₁ f₂ A₁ A₂ C)
  :
    ((walkDrawing D.rad.G (A₁.append T)).U ∪ (walkDrawing D.rad.G (A₂.append T)).U) \
      ((walkDrawing D.rad.G (A₁.append T)).U ∩ (walkDrawing D.rad.G (A₂.append T)).U) ∪ {u} ∪
        closure f₁ ∪ closure f₂ = C.U := by
  have hu₁ : u ∈ A₁.support := A₁.end_mem_support
  have hu₂ : u ∈ A₂.support := A₂.end_mem_support
  have hT : u ∈ T.support := T.start_mem_support
  have i₁ := U_inter_of_simple D.rad.G A₁ T (fun x h₁ h₂ ↦ GraphWalk.inter_of_simple hf.spoke₁.1 h₁
    h₂) hf.edges_disjoint_T hu₁ hT
  have i₂ := U_inter_of_simple D.rad.G A₂ T (fun x h₁ h₂ ↦ GraphWalk.inter_of_simple hf.spoke₂.1 h₁
    h₂) hf.swap.edges_disjoint_T hu₂ hT
  have i₃ := U_inter_of_simple D.rad.G A₁ A₂ hf.meet hf.edges_disjoint hu₁ hu₂
  rw [hf.U_eq hC, U_append, U_append]
  set a := (walkDrawing D.rad.G A₁).U
  set b := (walkDrawing D.rad.G A₂).U
  set t := (walkDrawing D.rad.G T).U
  have hua : u ∈ a := (mem_walkDrawing_U _ _).mpr (.inl hu₁)
  congr 2
  ext x
  have e₁ : x ∈ a → x ∈ t → x = u := fun h₁ h₂ ↦ by
    have : x ∈ a ∩ t := ⟨h₁, h₂⟩
    rwa [i₁] at this
  have e₂ : x ∈ b → x ∈ t → x = u := fun h₁ h₂ ↦ by
    have : x ∈ b ∩ t := ⟨h₁, h₂⟩
    rwa [i₂] at this
  have e₃ : x ∈ a → x ∈ b → x = u := fun h₁ h₂ ↦ by
    have : x ∈ a ∩ b := ⟨h₁, h₂⟩
    rwa [i₃] at this
  simp only [mem_union, mem_sdiff, mem_inter_iff, mem_singleton_iff]
  by_cases hxu : x = u
  · subst hxu
    exact ⟨fun _ ↦ .inl hua, fun _ ↦ .inr rfl⟩
  · constructor
    · rintro (⟨(h₁ | h₁) | (h₁ | h₁), h₂⟩ | h₁)
      · exact .inl h₁
      · exact absurd ⟨.inr h₁, .inr h₁⟩ h₂
      · exact .inr h₁
      · exact absurd ⟨.inr h₁, .inr h₁⟩ h₂
      · exact absurd h₁ hxu
    · rintro (h₁ | h₁)
      · refine .inl ⟨.inl (.inl h₁), ?_⟩
        rintro ⟨-, h₂ | h₂⟩
        · exact hxu (e₃ h₁ h₂)
        · exact hxu (e₁ h₁ h₂)
      · refine .inl ⟨.inr (.inl h₁), ?_⟩
        rintro ⟨h₂ | h₂, -⟩
        · exact hxu (e₃ h₂ h₁)
        · exact hxu (e₂ h₁ h₂)

/-- **Graph Minors XIX, (13.4)** (page 367), for an optimal hub `H`: "**13.4.** *Let
$r^* \in R^* \cap bd(W)$ with neighbours $v_1, v_2$ in $\Gamma^* \cap bd(W)$. Let $S_{v_1}$ meet
$S_{v_2}$, and let $S_{v_1} \cap S_{v_2}$ have ends $u, h$ where $h \in V(H)$. Let
$\Delta \subseteq W$ be the disc bounded by*
$$(U(S_{v_1} \cup S_{v_2}) \setminus U(S_{v_1} \cap S_{v_2})) \cup \{u\} \cup \bar{f}_1 \cup
\bar{f}_2,$$
*where $f_i$ is the edge of $\Gamma^* \cap bd(W)$ with ends $r^*, v_i$ ($i = 1, 2$). Then
$\Delta \cap U(H) = \emptyset$ unless $u = h$, in which case $\Delta \cap U(H) = \{h\}$; and
$\Delta \cap U(S_v) \subseteq bd(\Delta)$ for every $v \in V(\Gamma) \cap bd(W)$.*" The hypotheses
on `W` are those of (13.1). -/
theorem theorem_13_4_proof (hopt : D.IsOptimalWheelHub W H ρ) (hbdS : discBd W ⊆ cap.emb ''
  (univ \ bd S))
    (hin : ((W \ discBd W) ∩ (cap.emb '' D.Γ.V)).Nonempty) (hr : r ∈ D.rad.Rstar ∩ discBd W)
      (hne : v₁ ≠ v₂)
    (hf₁ : f₁ ∈ D.rad.G.E) (hf₁' : tilde f₁ = {r, v₁}) (hf₂ : f₂ ∈ D.rad.G.E) (hf₂' : tilde f₂
      = {r, v₂}) {h₁ h₂ : Shat}
    {S₁ S₂ Q : Drawing Shat} (hS₁ : D.IsSpoke W H v₁ h₁ S₁) (hS₂ : D.IsSpoke W H v₂ h₂ S₂)
      (hQ : Drawing.IsPathOf Q D.rad.G u h₁)
    (hQV : Q.V = S₁.V ∩ S₂.V) (hQE : Q.E = S₁.E ∩ S₂.E) (hm : (S₁.V ∩ S₂.V).Nonempty) {Δ : Set
      Shat} (hΔ : IsClosedDisc Δ) (hΔW : Δ ⊆ W)
    (hbd : discBd Δ = (S₁.U ∪ S₂.U) \ (S₁.U ∩ S₂.U) ∪ {u} ∪ closure f₁ ∪ closure f₂) :
    (u ≠ h₁ → Δ ∩ H.U = ∅) ∧ (u = h₁ → Δ ∩ H.U = {h₁}) ∧
      ∀ (v h : Shat) (P : Drawing Shat), D.IsSpoke W H v h P → Δ ∩ P.U ⊆ discBd Δ := by
  classical
  have : ConnectedSpace Shat := cap.connected
  obtain rfl := (theorem_13_2_proof hS₁ hS₂ hm).1
  obtain ⟨K₁, h1, rfl⟩ := hS₁.exists_walk
  obtain ⟨K₂, h2, rfl⟩ := hS₂.exists_walk
  obtain ⟨x, hx₁, hx₂⟩ := hm
  rw [walkDrawing_V] at hx₁ hx₂ hQV
  rw [walkDrawing_E, walkDrawing_E] at hQE
  rw [walkDrawing_V] at hQV
  obtain ⟨u', A₁, A₂, T, rfl, rfl, -, hmeet⟩ := h1.merge h2 hx₁ hx₂
  have hfan : D.IsFan W H ρ r f₁ f₂ A₁ A₂ T := by
    refine ⟨hopt.toIsWheelHubOfRadius, hbdS, hin, hr.1, hr.2, hne, ?_, ?_, h1, h2,
      fun y h₁ h₂ ↦ hmeet y h₁ ?_⟩
    · exact ⟨hf₁, hr.1.1, h1.2.is_path.1.1 (by rw [walkDrawing_V]; exact
        (A₁.append T).start_mem_support),
        by rw [closure_inter_V_eq_tilde hf₁, hf₁']⟩
    · exact ⟨hf₂, hr.1.1, h2.2.is_path.1.1 (by rw [walkDrawing_V]; exact
        (A₂.append T).start_mem_support),
        by rw [closure_inter_V_eq_tilde hf₂, hf₂']⟩
    · exact (GraphWalk.mem_support_append A₂ T).mpr (.inl h₂)
  -- `Q` and `T` have the same edges and the same last vertex, hence the same first vertex.
  have huu : u = u' := by
    obtain ⟨Qw, hQs, -, hQe⟩ := Drawing.IsPathOf.exists_simple_walk hQ
    have hT : T.IsSimple := (GraphWalk.IsSimple.of_append h1.1).2
    have hedges : ∀ e, e ∈ Qw.reverse.edges ↔ e ∈ T.reverse.edges := by
      intro e
      simp only [GraphWalk.edges_reverse, List.mem_reverse]
      rw [← hQe e, hQE]
      constructor
      · rintro ⟨h₁, h₂⟩
        have h₁' : e ∈ (A₁.append T).edges := h₁
        have h₂' : e ∈ (A₂.append T).edges := h₂
        rw [GraphWalk.edges_append, List.mem_append] at h₁' h₂'
        rcases h₁' with h₃ | h₃
        · rcases h₂' with h₄ | h₄
          · exact absurd h₄ (hfan.edges_disjoint e h₃)
          · exact absurd h₄ (hfan.edges_disjoint_T e h₃)
        · exact h₃
      · intro h'
        constructor
        · change e ∈ (A₁.append T).edges
          rw [GraphWalk.edges_append, List.mem_append]
          exact .inr h'
        · change e ∈ (A₂.append T).edges
          rw [GraphWalk.edges_append, List.mem_append]
          exact .inr h'
    exact (simple_walks_eq Qw.reverse T.reverse hQs.reverse hT.reverse hedges).1
  subst huu
  obtain ⟨C, hC⟩ := hfan.exists_circuit
  have hbd' : discBd Δ = C.U := by rw [hbd, hfan.formula_eq hC]
  obtain ⟨hfirst, hsecond⟩ := hfan.main hC hopt hΔ hΔW hbd'
  have huΔ : u ∈ Δ := by
    apply Surface.discBd_subset Δ
    rw [hbd']
    exact C.V_subset_U ((hC.mem_V u).mpr (.inr (.inl A₁.end_mem_support)))
  refine ⟨fun hne' ↦ ?_, fun heq ↦ ?_, fun v h P hP ↦ ?_⟩
  · refine eq_empty_of_forall_notMem fun y hy ↦ ?_
    have hyu := hfirst y hy
    subst hyu
    apply hne'
    have hy₂ : y ∈ C.U := by
      rw [C.U_eq]
      exact .inl ((hC.mem_V y).mpr (.inr (.inl A₁.end_mem_support)))
    exact (hfan.hub_meet hC hy.2 hy₂).2
  · subst heq
    refine Subset.antisymm (fun y hy ↦ hfirst y hy) ?_
    rw [singleton_subset_iff]
    exact ⟨huΔ, H.V_subset_U h1.2.h_mem⟩
  · obtain ⟨K, hK, rfl⟩ := hP.exists_walk
    exact hsecond v h K hK

end TangleDatum

end GraphMinor.GM19
