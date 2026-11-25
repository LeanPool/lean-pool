/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section15j

/-!
# Graph Minors XIX, (15.2): an internal edge has no small separation around it

This is step (6) of the proof of (15.2), read for circuits of `Γ*`. If a short circuit of `Γ*` holds
more than half its length of the ends of an edge, then it has at most two vertices of `Γ`. An edge
far from the
poles keeps this circuit off the cuffs, so internal 3-connectivity applies in `Σ`, and gives a disc
with no vertex of `Γ` inside. That disc cannot be `ins(F)`, and it cannot be the other disc either,
by the third tangle axiom.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10 GraphMinor.GM14 Hypergraph

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {cap : IsCappedSurface S Shat} {β : Type w} {χ : ColourScheme S β} {D : TangleDatum cap χ}

namespace TangleDatum

/-- **Step (6) of the proof of (15.2).** -/
theorem no_circuit_holds_tilde (hS : IsSurface S) {n : ℕ} (hn : 8 ≤ n) (hrep : 4
  ≤ D.rep) {c : Set S} (hc : c ∈ D.P.Γ.E) (h3c : (tilde c).ncard ≤ 3)
    (hfar : ∀ r ∈ D.rad.poles, n < D.edgeVertDist c r)
    {F : Drawing Shat} (hF : F.IsCircuitOf D.rad.G) (hl : F.E.ncard < 2 * D.rep)
      (hlt : F.E.ncard < 2 * ((cap.emb '' tilde c) ∩ D.ins F).ncard) : False := by
  classical
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have h3 := D.P.fits.internally_three_connected
  have hinj := cap.isEmbedding.injective
  have hi := D.ins_spec hF hl
  have htfin : (tilde c).Finite := D.P.Γ.finite_V.subset (D.P.Γ.tilde_subset_V hc)
  have hX3 : ((cap.emb '' tilde c) ∩ D.ins F).ncard ≤ 3 := by
    have := ncard_le_ncard (s := (cap.emb '' tilde c) ∩ D.ins F) inter_subset_left (htfin.image _)
    rw [ncard_image_of_injective _ hinj] at this
    omega
  have hE := D.ncard_E_eq_hat hF
  have hpos : ((cap.emb '' tilde c) ∩ D.ins F).Nonempty := nonempty_of_ncard_ne_zero (by omega)
  obtain ⟨_, ⟨x, hxt, rfl⟩, hxi⟩ := hpos
  have hxV : x ∈ D.P.Γ.V := D.P.Γ.tilde_subset_V hc hxt
  have hxa : ({cap.emb x} : Set Shat) ∈ D.P.Γ.atoms cap := Or.inl (Or.inl ⟨x, hxV, rfl⟩)
  have hcx : D.dist (cap.emb '' c) {cap.emb x} ≤ 3 := by
    have := D.edgeVertDist_self_le hrep hc hxt hxV
    unfold edgeVertDist at this
    rwa [D.atomOf_emb hxV] at this
  have near : ∀ a : Set Shat, (a ∩ D.ins F).Nonempty → D.dist (cap.emb '' c) a ≤ 5 := fun a ha => by
    have h₁ := D.dist_le_of_circuit (by omega) hF hl (a := {cap.emb x}) ⟨_, rfl, hxi⟩ ha
    have h₂ := D.dist_triangle hrep (a := cap.emb '' c) (c := a) hxa
    omega
  have npole : ∀ r ∈ D.rad.poles, r ∉ D.ins F := fun r hr hri => by
    have h₁ := near (D.rad.atomOf r) ⟨r, D.mem_atomOf hr.1.1, hri⟩
    have h₂ := hfar r hr
    unfold edgeVertDist at h₂
    omega
  have hnb : ∀ Θ ∈ cuffs S, ∀ y ∈ Θ, cap.emb y ∉ F.U := fun Θ hΘ y hy hyF => by
    obtain ⟨hyV, hyFV, -⟩ := D.rad.bd_point hF.1 (cuff_subset_bd ⟨Θ, hΘ⟩ hy) hyF
    obtain ⟨p, hp, -, hreg⟩ := D.rad.exists_pole hΘ
    obtain ⟨e, he, hcap⟩ := D.rad.exists_pole_edge hS h3 hp hΘ hreg hyV hy
    have hyG : cap.emb y ∈ D.rad.G.V := hF.1.1 hyFV
    have hl₁ : D.rad.G.toGraph.IsLink e (cap.emb y) p := ⟨he, hyG, hp.1.1, hcap⟩
    have hlen : (GraphWalk.cons hl₁ (GraphWalk.nil hp.1.1)).length = 1 := by
      simp [GraphWalk.length, GraphWalk.edges]
    have h₁ := D.dist_atomOf_le_of_walk (GraphWalk.cons hl₁ (GraphWalk.nil hp.1.1)) (by omega)
    rw [hlen, D.atomOf_emb hyV] at h₁
    have h₂ := near {cap.emb y} ⟨_, rfl, D.U_subset_ins hF hl hyF⟩
    have h₃ := D.dist_triangle hrep (a := cap.emb '' c) (c := D.rad.atomOf p) (Or.inl
      (Or.inl ⟨y, hyV, rfl⟩) : ({cap.emb y} : Set Shat) ∈ D.P.Γ.atoms cap)
    have h₄ := hfar p hp
    unfold edgeVertDist at h₄
    omega
  have hrange : F.U ⊆ range cap.emb := fun z hz => by
    by_contra hzr
    have hmem : z ∈ (range cap.emb)ᶜ := hzr
    rw [cap.compl_eq] at hmem
    obtain ⟨Θ, hΘ, hzd⟩ := mem_iUnion₂.mp hmem
    obtain ⟨p, hp, -, hreg⟩ := D.rad.exists_pole hΘ
    have hpF := pole_mem_of_meet hF.1 hp hΘ hreg hz hzd
    exact npole p hp (D.U_subset_ins hF hl (F.V_subset_U hpF))
  have hnebd : Disjoint (cap.emb ⁻¹' F.U) (bd S) := disjoint_left.mpr fun y hy hyb =>
    hnb _ ⟨y, hyb, rfl⟩ y (mem_connectedComponentIn hyb) hy
  have : Nonempty S := ⟨x⟩
  have hO : IsOArc (cap.emb ⁻¹' F.U) := by
    obtain ⟨f', hf'c, hf'⟩ := exists_inv_of_isEmbedding cap.isEmbedding
    have himg : f' '' F.U = cap.emb ⁻¹' F.U := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        obtain ⟨w, rfl⟩ := hrange hz
        rw [hf' w]
        exact hz
      · intro hy
        exact ⟨cap.emb y, hy, hf' y⟩
    rw [← himg]
    refine IsOArc.image (IsCircuit.isOArc_U hF.2) (hf'c.mono hrange)
      cap.isEmbedding.continuous.continuousOn ?_
    intro z hz
    obtain ⟨w, rfl⟩ := hrange hz
    rw [hf' w]
  have hUV : cap.emb ⁻¹' F.U ∩ D.P.Γ.U ⊆ D.P.Γ.V := fun y hy => by
    have : cap.emb y ∈ D.P.Γ.hatU cap ∩ D.rad.G.U := ⟨mem_image_of_mem _ hy.2, hF.1.U_subset hy.1⟩
    rw [D.rad.isPreRadial.1] at this
    obtain ⟨w, hw, e⟩ := this
    exact hinj e ▸ hw
  have hVsub : cap.emb '' (cap.emb ⁻¹' F.U ∩ D.P.Γ.V) ⊆ F.V ∩ D.P.Γ.hatV cap := by
    rintro _ ⟨y, ⟨hy, hyV⟩, rfl⟩
    exact ⟨mem_V_of_mem_U_sub hF.1 hy (D.rad.isPreRadial.2.1 (mem_image_of_mem _ hyV)),
      mem_image_of_mem _ hyV⟩
  have hcount : (cap.emb ⁻¹' F.U ∩ D.P.Γ.V).ncard ≤ (F.V ∩ D.P.Γ.hatV cap).ncard := by
    have := ncard_le_ncard hVsub (F.finite_V.subset inter_subset_left)
    rwa [ncard_image_of_injective _ hinj] at this
  have hbdE : cap.emb ⁻¹' F.U ∩ bd S = ∅ := disjoint_iff_inter_eq_empty.mp hnebd
  obtain ⟨Δ, hΔ, hΔb, hΔV⟩ :=
    h3.2 _ hO hUV (by simp [hbdE]) (by rw [hbdE, ncard_empty]; omega)
  obtain ⟨hd, hdb⟩ := isClosedDisc_image hΔ cap.isEmbedding
  have hdb' : discBd (cap.emb '' Δ) = F.U := by
    rw [hdb, hΔb, image_preimage_eq_of_subset hrange]
  have hbd₂ : discBd (D.ins F) = F.U := hi.2.2.2.1
  by_cases he : cap.emb '' Δ = D.ins F
  · have hsub : (cap.emb '' tilde c) ∩ D.ins F ⊆ F.V ∩ D.P.Γ.hatV cap := by
      rintro _ ⟨⟨y, hy, rfl⟩, hyi⟩
      have hyV := D.P.Γ.tilde_subset_V hc hy
      have hyΔ : y ∈ Δ := by
        rw [← he] at hyi
        exact hinj.mem_set_image.mp hyi
      exact hVsub ⟨y, ⟨hΔV ⟨hyΔ, hyV⟩, hyV⟩, rfl⟩
    have := ncard_le_ncard hsub (F.finite_V.subset inter_subset_left)
    omega
  have hsph : IsSphere Shat := by
    by_contra hns
    exact he (eq_of_discBd_eq hT.isSurface hns hd hi.2.2.1 (hdb'.trans hbd₂.symm))
  obtain ⟨Δ₁, Δ₂, -, -, -, -, -, hun, -, -, huniq⟩ := sphere_disc Shat hsph F.U
    (IsCircuit.isOArc_U hF.2)
  have hU : cap.emb '' Δ ∪ D.ins F = univ := by
    rcases huniq _ hd hdb' with e₁ | e₁ <;> rcases huniq _ hi.2.2.1 hbd₂ with e₂ | e₂
    · exact absurd (e₁.trans e₂.symm) he
    · rw [e₁, e₂]
      exact hun
    · rw [e₁, e₂, Set.union_comm]
      exact hun
    · exact absurd (e₁.trans e₂.symm) he
  refine D.isTangle.axiom3 hi.2.2.2.2 ?_
  refine Subset.antisymm inter_subset_left fun v hv => ⟨hv, ?_⟩
  rcases (hU.symm ▸ mem_univ _ : cap.emb v ∈ cap.emb '' Δ ∪ D.ins F) with h | h
  · have hvΔ : v ∈ Δ := hinj.mem_set_image.mp h
    exact D.U_subset_ins hF hl (hΔV ⟨hvΔ, hv⟩)
  · exact h

end TangleDatum

end GraphMinor.GM19
