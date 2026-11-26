/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section13j

/-!
# Graph Minors XIX, Section 13: steps (1), (2), (3) of (13.6)

The hypotheses of (13.6) are collected in `IsSectorEnclave`. Then come the steps of the proof that
speak about the hub:
the inside of `F` meets the inside of `H` only on their boundaries.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

namespace TangleDatum

variable {D : TangleDatum cap χ} {W : Set Shat} {H : Drawing Shat} {ρ : ℕ} {r : Shat} {Δv : Set
  Shat} {Dv F : Drawing Shat}
  {ord' : ℕ} {𝒯' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}

/-- The hypotheses of (13.6), with the standing assumptions of Section 13. `rep(𝒯) ≥ 6ρ + 14` is the
bound used in the paper's step (4). -/
structure IsSectorEnclave (D : TangleDatum cap χ) (W : Set Shat) (H : Drawing Shat) (ρ : ℕ)
  (r : Shat) (Δv : Set Shat) (Dv : Drawing Shat)
    (ord' : ℕ) (𝒯' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (F : Drawing Shat) : Prop where
  hopt : D.IsOptimalWheelHub W H ρ
  hbdS : discBd W ⊆ cap.emb '' (univ \ bd S)
  hin : ((W \ discBd W) ∩ (cap.emb '' D.Γ.V)).Nonempty
  hrep : 6 * ρ + 14 ≤ D.rep
  sector : D.IsBoundarySector W H r Δv Dv
  mem : (partIn cap D.Γ (closure Δvᶜ), partIn cap D.Γ Δv) ∈ 𝒯'
  enclave : IsEnclaveAround D.tb D.ord ord' D.𝒯 𝒯' F

/-- The two forms of a sector: the spokes meet, and `D_v` is the circuit of their fan, or they do
not, and `D_v` runs along a path of `H`. -/
theorem IsBoundarySector.cases (hW : D.IsWheelHubOfRadius W H ρ) (hbdS : discBd W ⊆ cap.emb ''
  (univ \ bd S))
    (hin : ((W \ discBd W) ∩ (cap.emb '' D.Γ.V)).Nonempty) (hs : D.IsBoundarySector W H r Δv Dv) :
    (∃ (v₁ v₂ u h : Shat) (f₁ f₂ : Set Shat) (A₁ : GraphWalk D.rad.G.toGraph v₁ u)
      (A₂ : GraphWalk D.rad.G.toGraph v₂ u)
      (T : GraphWalk D.rad.G.toGraph u h), D.IsFan W H ρ r f₁ f₂ A₁ A₂ T
        ∧ D.IsFanCircuit r f₁ f₂ A₁ A₂ Dv ∧
        f₁ ⊆ discBd W ∧ f₂ ⊆ discBd W) ∨
    (∃ (v₁ v₂ h₁ h₂ : Shat) (f₁ f₂ : Set Shat) (K₁ : GraphWalk D.rad.G.toGraph v₁ h₁)
      (K₂ : GraphWalk D.rad.G.toGraph v₂ h₂) (P : Drawing Shat),
      v₁ ≠ v₂ ∧ D.rad.G.toGraph.IsLink f₁ r v₁ ∧ D.rad.G.toGraph.IsLink f₂ r v₂ ∧ f₁ ⊆ discBd W
        ∧ f₂ ⊆ discBd W ∧
      D.IsSpokeWalk W H K₁ ∧ D.IsSpokeWalk W H K₂ ∧ (∀ x ∈ K₁.support, x ∉ K₂.support)
        ∧ Drawing.IsPathOf P H h₁ h₂ ∧
      discBd Δv = (walkDrawing D.rad.G K₁).U ∪ (walkDrawing D.rad.G K₂).U ∪ P.U ∪ closure f₁ ∪
        closure f₂ ∧ ¬ (D.ins H ⊆ Δv)) := by
  have : ConnectedSpace Shat := cap.connected
  obtain ⟨v₁, v₂, h₁, h₂, f₁, f₂, S₁, S₂, hne, hf₁, hf₁b, hf₁', hf₂, hf₂b, hf₂', hS₁, hS₂, hcase⟩
    := hs.sector_spec
  obtain ⟨K₁, h1, rfl⟩ := hS₁.exists_walk
  obtain ⟨K₂, h2, rfl⟩ := hS₂.exists_walk
  have hv₁G : v₁ ∈ D.rad.G.V := K₁.mem_vertexSet_of_mem_support K₁.start_mem_support
  have hv₂G : v₂ ∈ D.rad.G.V := K₂.mem_vertexSet_of_mem_support K₂.start_mem_support
  have hl₁ : D.rad.G.toGraph.IsLink f₁ r v₁ := ⟨hf₁, hs.rstar_mem.1.1, hv₁G, by rw
    [closure_inter_V_eq_tilde hf₁, hf₁']⟩
  have hl₂ : D.rad.G.toGraph.IsLink f₂ r v₂ := ⟨hf₂, hs.rstar_mem.1.1, hv₂G, by rw
    [closure_inter_V_eq_tilde hf₂, hf₂']⟩
  rcases hcase with ⟨⟨x, hx₁, hx₂⟩, hbd⟩ | ⟨hdisj, P, hP, hbd, hnot⟩
  · left
    rw [walkDrawing_V] at hx₁ hx₂
    obtain rfl := h1.same_end h2 hx₁ hx₂
    obtain ⟨u, A₁, A₂, T, rfl, rfl, -, hmeet⟩ := h1.merge h2 hx₁ hx₂
    have hfan : D.IsFan W H ρ r f₁ f₂ A₁ A₂ T :=
      ⟨hW, hbdS, hin, hs.rstar_mem.1, hs.rstar_mem.2, hne, hl₁, hl₂, h1, h2, fun y h₁ h₂ ↦ hmeet y
        h₁
        ((GraphWalk.mem_support_append A₂ T).mpr (.inl h₂))⟩
    obtain ⟨C, hC⟩ := hfan.exists_circuit
    have heq : Dv = C := eq_of_U_eq hs.Dv_circuit.1 hC.circuit.1 (by rw [hs.Dv_U, hbd,
      hfan.closure_formula hC])
    subst heq
    exact ⟨v₁, v₂, u, _, f₁, f₂, A₁, A₂, T, hfan, hC, hf₁b, hf₂b⟩
  · right
    refine ⟨v₁, v₂, h₁, h₂, f₁, f₂, K₁, K₂, P, hne, hl₁, hl₂, hf₁b, hf₂b, h1, h2,
      fun x h₃ h₄ ↦ ?_, hP, hbd, hnot⟩
    rw [walkDrawing_V, walkDrawing_V] at hdisj
    exact disjoint_left.mp hdisj h₃ h₄

omit [T2Space S] [T2Space Shat] in
/-- The inside of an enclave `H` that is a hub misses `bd(W)`. -/
theorem IsWheelHubOfRadius.ins_off_bd (hW : D.IsWheelHubOfRadius W H ρ)
  (hc : H.IsCircuitOf D.rad.G) (hle : H.E.ncard ≤ 4 * ρ + 4) :
    Disjoint (D.ins H) (discBd W) := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hman : ∀ x : Shat, IsManifoldPoint x := (Surface.IsClosedSurface.isSurface hT).2.2
  have hrep := hW.rep_ge
  have hlt : H.E.ncard < 2 * D.rep := by omega
  have hi := D.ins_spec hc hlt
  have hsub := hW.ins_sub H hc hle (hW.H_in_int.trans sdiff_subset)
  refine disjoint_left.mpr fun x hx hxb ↦ ?_
  by_cases hxU : x ∈ H.U
  · exact (hW.H_in_int hxU).2 hxb
  · have hxi : x ∈ discInt (D.ins H) := ⟨hx, fun hb ↦ hxU (hi.2.2.2.1 ▸ hb)⟩
    have hop := hi.2.2.1.isOpen_discInt hman
    have hint : x ∈ interior W := mem_interior.mpr ⟨_, (discInt_subset _).trans hsub, hop, hxi⟩
    have hf : x ∈ frontier W := by
      rw [IsClosedDisc.frontier_eq_discBd hT hW.is_disc]
      exact hxb
    exact hf.2 hint

/-- A spoke is outside the inside of an enclave `H` that is the hub. -/
theorem IsSpokeWalk.off_ins_hub (hW : D.IsWheelHubOfRadius W H ρ) (hH : IsEnclave D.tb D.ord D.𝒯 H)
  (hle : H.E.ncard ≤ 4 * ρ + 4) {v h : Shat}
    {K : GraphWalk D.rad.G.toGraph v h} (hK : D.IsSpokeWalk W H K) : Disjoint
      (walkDrawing D.rad.G K).U (discInt (D.ins H)) := by
  have : ConnectedSpace Shat := cap.connected
  obtain ⟨-, -, -, hc, hlt, -⟩ := id hH
  have hrep := hW.rep_ge
  have hlt' : H.E.ncard < 2 * D.rep := by omega
  have hi := D.ins_spec hc hlt'
  refine disjoint_left.mpr fun x hx hxi ↦ ?_
  have h₂ := (theorem_13_3_proof hK.2 hH).2 fun hsub ↦ hxi.2 (hi.2.2.2.1 ▸ hsub ⟨hx, hxi.1⟩)
  rcases h₂ with h₃ | h₃
  · exact disjoint_left.mp (hW.ins_off_bd hc hle) h₃.1 hK.2.v_mem.2
  · exact h₃.2 (H.V_subset_U hK.2.h_mem)

/-- The inside of the hub and the inside of the sector have no common point. -/
theorem IsBoundarySector.interior_off_hub (hopt : D.IsOptimalWheelHub W H ρ)
  (hbdS : discBd W ⊆ cap.emb '' (univ \ bd S))
    (hin : ((W \ discBd W) ∩ (cap.emb '' D.Γ.V)).Nonempty) (hs : D.IsBoundarySector W H r Δv Dv)
      (hH : IsEnclave D.tb D.ord D.𝒯 H)
    (hle : H.E.ncard ≤ 4 * ρ + 4) : Disjoint (discInt (D.ins H)) (discInt Δv) := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hW := hopt.toIsWheelHubOfRadius
  obtain ⟨-, -, -, hc, hlt, -⟩ := id hH
  have hrep := hW.rep_ge
  have hlt' : H.E.ncard < 2 * D.rep := by omega
  have hi := D.ins_spec hc hlt'
  have hbdΔ : discBd Δv = Dv.U := hs.Dv_U.symm
  have hO := isSide_int hT hs.is_disc hbdΔ
  have hcfr : ∀ {f : Set Shat}, f ⊆ discBd W → Disjoint (closure f) (discInt (D.ins H))
    := fun hf ↦ by
    have hcl : IsClosed (discBd W) := by
      rw [← IsClosedDisc.frontier_eq_discBd hT hW.is_disc]
      exact isClosed_frontier
    exact (disjoint_of_subset_left (closure_minimal hf hcl) (hW.ins_off_bd hc hle).symm).mono_right
      (discInt_subset _)
  have hHU : H.U ⊆ D.ins H := by
    rw [← hi.2.2.2.1]
    exact Surface.discBd_subset _
  have hUoff : H.U ⊆ (discInt (D.ins H))ᶜ := fun x hx hxi ↦ hxi.2 (hi.2.2.2.1 ▸ hx)
  have hkey : (∀ {x}, x ∈ Dv.U → x ∉ discInt (D.ins H)) → (discInt (D.ins H) ∩ discInt Δv).Nonempty
    → D.ins H ⊆ Δv := by
    intro hd hne
    have := hO.subset hi.2.2.1.isPreconnected_discInt (disjoint_left.mpr fun x hx hxU ↦ hd hxU hx)
      hne
    exact hi.2.2.1.subset_closure_discInt.trans (closure_minimal (this.trans
      (discInt_subset _)) hs.is_disc.isClosed)
  rw [disjoint_iff_inter_eq_empty, ← not_nonempty_iff_eq_empty]
  intro hne
  rcases hs.cases hW hbdS hin with ⟨v₁, v₂, u, h, f₁, f₂, A₁, A₂, T, hf, hC, hb₁, hb₂⟩ | ⟨v₁, v₂,
    h₁, h₂, f₁, f₂, K₁, K₂, P, -, -, -, hb₁, hb₂, h1, h2, -, hP, hbd, hnot⟩
  · have hsub := hkey (fun {x} hx hxi ↦ by
      rw [hf.U_eq hC] at hx
      have hsp : ∀ {y} {A : GraphWalk D.rad.G.toGraph y u}, D.IsSpokeWalk W H (A.append T) → x ∈
        (walkDrawing D.rad.G A).U → False := fun hA hxA ↦ by
        refine disjoint_left.mp (IsSpokeWalk.off_ins_hub hW hH hle hA) ?_ hxi
        rw [U_append]
        exact .inl hxA
      rcases hx with ((hx | hx) | hx) | hx
      · exact hsp hf.spoke₁ hx
      · exact hsp hf.spoke₂ hx
      · exact disjoint_left.mp (hcfr hb₁) hx hxi
      · exact disjoint_left.mp (hcfr hb₂) hx hxi) hne
    have hmain := (hf.main hC hopt hs.is_disc hs.Δv_sub hbdΔ).1
    have hV : H.V = {u} := by
      have hall : ∀ z ∈ H.V, z = u := fun z hz ↦ hmain z ⟨hsub (hHU (H.V_subset_U hz)),
        H.V_subset_U hz⟩
      obtain ⟨u', W', -, -, hVe, -⟩ := hc.2
      have hu' : u' ∈ H.V := by
        rw [hVe]
        exact W'.start_mem_support
      obtain rfl := hall u' hu'
      exact Subset.antisymm (fun z hz ↦ hall z hz) (singleton_subset_iff.mpr hu')
    have := IsCircuit.two_vertices D hc
    rw [hV, ncard_singleton] at this
    exact this rfl
  · refine hnot (hkey (fun {x} hx hxi ↦ ?_) hne)
    rw [← hbdΔ, hbd] at hx
    rcases hx with (((hx | hx) | hx) | hx) | hx
    · exact disjoint_left.mp (IsSpokeWalk.off_ins_hub hW hH hle h1) hx hxi
    · exact disjoint_left.mp (IsSpokeWalk.off_ins_hub hW hH hle h2) hx hxi
    · exact hUoff (hP.1.U_subset hx) hxi
    · exact disjoint_left.mp (hcfr hb₁) hx hxi
    · exact disjoint_left.mp (hcfr hb₂) hx hxi

namespace IsSectorEnclave

variable (hx : D.IsSectorEnclave W H ρ r Δv Dv ord' 𝒯' F)
include hx

omit [T2Space S] in
omit [T2Space Shat] in
theorem wheel : D.IsWheelHubOfRadius W H ρ := hx.hopt.toIsWheelHubOfRadius

theorem Dv_card : Dv.E.ncard ≤ 4 * ρ + 4 := (theorem_13_5_proof hx.wheel hx.hbdS hx.hin hx.sector).1

theorem ins_Dv : D.ins Dv = Δv := (theorem_13_5_proof hx.wheel hx.hbdS hx.hin hx.sector).2

theorem isInsOf_Dv : IsInsOf D.rad D.ord D.𝒯 Dv Δv := by
  have h := D.ins_spec hx.sector.Dv_circuit (by have := hx.Dv_card; have := hx.hrep; omega)
  rwa [hx.ins_Dv] at h

omit [T2Space S] in
omit [T2Space Shat] in
theorem isTangle' : IsTangle D.Γ.toHypergraph ord' 𝒯' := hx.enclave.1

omit [T2Space S] in
theorem isInsOf_F : IsInsOf D.rad D.ord D.𝒯 F (D.ins F) := by
  obtain ⟨-, hc, hlt, Δ, hins, -⟩ := hx.enclave
  rw [← D.eq_ins_of_isInsOf hins]
  exact hins

omit [T2Space S] in
theorem distinction : IsDistinction D.tb.lambdaOrder D.𝒯 𝒯' (partIn cap D.Γ (D.ins F))
  (partIn cap D.Γ (closure (D.ins F)ᶜ)) := by
  obtain ⟨-, hc, hlt, Δ, hins, hd⟩ := hx.enclave
  rw [← D.eq_ins_of_isInsOf hins]
  exact hd

/-- Step (1) of the proof of (13.6). -/
theorem F_card : F.E.ncard ≤ Dv.E.ncard ∧ Dv.E.ncard ≤ 4 * ρ + 4 :=
  ⟨enclave_card_le χ.isSurface D.P.fits.internally_three_connected D.tb hx.isInsOf_F hx.distinction
    hx.isInsOf_Dv hx.mem, hx.Dv_card⟩

omit [T2Space S] in
omit [T2Space Shat] in
theorem isEnclave : IsEnclave D.tb D.ord D.𝒯 F := ⟨ord', 𝒯', hx.enclave⟩

/-- Step (2) of the proof of (13.6). -/
theorem exists_edge : ∃ c ∈ D.Γ.E, cap.emb '' c ⊆ discInt (D.ins F) ∧ cap.emb '' c ⊆ discInt Δv :=
  exists_edge_in_both χ.isSurface D.P.fits.internally_three_connected hx.isTangle' hx.isInsOf_F
    hx.distinction.1.2 hx.isInsOf_Dv hx.mem

/-- Step (3) of the proof of (13.6), when `H` has one vertex. -/
theorem hub_point (hc : H.V.ncard = 1) {h : Shat} (hh : h ∈ H.V) (hm : h ∈ D.ins F) : h ∈ F.U := by
  have : ConnectedSpace Shat := cap.connected
  by_contra hn
  obtain ⟨z, hz⟩ := ncard_eq_one.mp hc
  rcases hx.wheel.hub_cond with ⟨-, -, hcond⟩ | ⟨hen, -, -⟩
  · refine hcond F hx.isEnclave (hx.F_card.1.trans hx.F_card.2) fun y hy ↦ ?_
    rw [hz] at hy hh
    rw [mem_singleton_iff.mp hy, ← mem_singleton_iff.mp hh]
    exact ⟨hm, hn⟩
  · obtain ⟨-, -, -, hcir, -⟩ := id hen
    have := IsCircuit.two_vertices D hcir
    exact this hc

/-- Step (3) of the proof of (13.6), when `H` is a circuit. -/
theorem hub_circuit (hH : IsEnclave D.tb D.ord D.𝒯 H) : D.ins F ∩ D.ins H = F.U ∩ H.U := by
  have : ConnectedSpace Shat := cap.connected
  have hS := χ.isSurface
  have h3 := D.P.fits.internally_three_connected
  have hW := hx.wheel
  have hrep := hx.hrep
  have hFle := hx.F_card
  have hHle : H.E.ncard ≤ 4 * ρ + 4 ∧ ∀ H' : Drawing Shat, IsEnclave D.tb D.ord D.𝒯 H' → H' ≠ H
    → H'.E.ncard ≤ 4 * ρ + 4 → ¬ (H.U ⊆ D.ins H') := by
    rcases hW.hub_cond with ⟨hc, -, -⟩ | ⟨-, h₂, h₃⟩
    · obtain ⟨-, -, -, hcir, -⟩ := id hH
      exact absurd hc (IsCircuit.two_vertices D hcir)
    · exact ⟨h₂, h₃⟩
  obtain ⟨hle, hcond⟩ := hHle
  obtain ⟨ord₂, 𝒯₂, h𝒯₂, hcir, hlt, Δ, hins, hd⟩ := id hH
  obtain rfl : Δ = D.ins H := D.eq_ins_of_isInsOf hins
  have hlt' : H.E.ncard < 2 * D.rep := by omega
  have hdis := hx.sector.interior_off_hub hx.hopt hx.hbdS hx.hin hH hle
  have hnest : ¬ D.ins F ⊆ D.ins H := by
    intro hsub
    obtain ⟨c, hc, hc₁, hc₂⟩ := hx.exists_edge
    obtain ⟨y, hy⟩ := hc.1
    have hyi₁ := hc₁ (mem_image_of_mem _ hy)
    have hyi₂ := hc₂ (mem_image_of_mem _ hy)
    have hFc := hx.isInsOf_F
    have h₁ : cap.emb y ∈ interior (D.ins F) := (ins_diff_iff D hFc.1 hFc.2.1).mp ⟨hyi₁.1, fun hu ↦
      hyi₁.2 (hFc.2.2.2.1 ▸ hu)⟩
    have h₂ := (ins_diff_iff D hcir hlt').mpr (interior_mono hsub h₁)
    exact disjoint_left.mp hdis ⟨h₂.1, fun hb ↦ h₂.2 (hins.2.2.2.1 ▸ hb)⟩ hyi₂
  rcases theorem_8_6_proof hS h3 D.tb D.isTangle hx.isTangle' h𝒯₂ hx.isInsOf_F hins hx.distinction
    hd with h | h | h
  · exact absurd h hnest
  · by_cases heq : F = H
    · subst heq
      exact absurd subset_rfl hnest
    · have hU : H.U ⊆ D.ins H := by
        rw [← hins.2.2.2.1]
        exact Surface.discBd_subset _
      exact absurd (hU.trans h) (hcond F hx.isEnclave heq (hFle.1.trans hFle.2))
  · exact h

end IsSectorEnclave

end TangleDatum

end GraphMinor.GM19
