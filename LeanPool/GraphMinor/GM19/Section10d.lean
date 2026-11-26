/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section10c

/-!
# Existence of a representativeness flaw

Graph Minors XIX, page 353: "Let $(\Gamma, \phi, \lambda, \mathscr{T}) \in \mathscr{D}$, such that
$rep(\Gamma), ord(\mathscr{T}) > rep(\mathscr{T})$. Then $\hat{\Sigma}_\chi$ is not a sphere, and
there is
a circuit $F$ of $\Gamma^*$ with $\frac{1}{2}|E(F)| \le rep(\mathscr{T})$ such that $\Sigma_1$ is
not a disc".
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {cap : IsCappedSurface S Shat} {α : Type w} {χ : ColourScheme S α} {D : TangleDatum cap χ}


namespace TangleDatum

/-- The circuits a flaw is chosen from: `½|E(F)| ≤ rep(𝒯)`, with `Σ₁` not a disc. -/
def IsFlawCandidate (D : TangleDatum cap χ) (F : Drawing Shat) : Prop :=
  F.IsCircuitOf D.rad.G ∧ F.E.ncard ≤ 2 * D.rep ∧ ∃ S₁ S₂ : Set Shat, IsSidesOf F S₁ S₂
    ∧ ¬ IsClosedDisc S₁ ∧
    (D.Γ.restrict (cap.emb ⁻¹' S₁), D.Γ.restrict (cap.emb ⁻¹' S₂)) ∈ D.𝒯

omit [T2Space Shat] in
theorem finite_circuits (G : Drawing Shat) : {C : Drawing Shat | C.IsCircuit
  ∧ C.IsSubdrawing G}.Finite := by
  refine Set.Finite.of_finite_image (f := fun C : Drawing Shat ↦ (C.V, C.E)) ?_ ?_
  · refine (G.finite_V.finite_subsets.prod G.finite_edges.finite_subsets).subset ?_
    rintro _ ⟨C, ⟨-, hs'⟩, rfl⟩
    exact ⟨hs'.1, hs'.2⟩
  · intro C _ C' _ h
    exact Drawing.ext_of_V_E (congrArg Prod.fst h) (congrArg Prod.snd h)

variable (hS : IsSurface S) (h3 : D.P.Γ.IsInternallyThreeConnected)
include hS h3

/-- There is a circuit of `Γ*` that is at most `2 rep(𝒯)` long with `Σ₁` not a disc. -/
theorem exists_candidate (h₁ : (D.rep : ℕ∞) < Painting.rep D.rad) (h₂ : D.rep < D.ord) :
    ∃ F, D.IsFlawCandidate F ∧ ¬ IsSphere Shat := by
  classical
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  set A : Set ℕ := {k : ℕ | k ≤ D.ord ∧ ∀ F : Drawing Shat, F.IsCircuitOf D.rad.G
    → F.E.ncard < 2 * k →
    ∃ Δ : Set Shat, IsClosedDisc Δ ∧ discBd Δ = F.U ∧
      (D.P.Γ.restrict (cap.emb ⁻¹' Δ), D.P.Γ.restrict (cap.emb ⁻¹' closure Δᶜ)) ∈ D.𝒯} with hA
  have hbdd : BddAbove A := ⟨D.ord, fun k hk ↦ hk.1⟩
  have hrep : D.rep = sSup A := rfl
  have hnot : D.rep + 1 ∉ A := fun h ↦ by
    have := le_csSup hbdd h
    omega
  have hle : D.rep + 1 ≤ D.ord := h₂
  simp only [hA, mem_ofPred_eq, not_and, not_forall] at hnot
  obtain ⟨F, hF, hlt, hno⟩ := hnot hle
  have hlt₂ : (F.E.ncard : ℕ∞) < 2 * Painting.rep D.rad := by
    have h₃ : ((D.rep + 1 : ℕ) : ℕ∞) ≤ Painting.rep D.rad := by
      have := Order.add_one_le_of_lt h₁
      exact_mod_cast this
    have h₄ : (F.E.ncard : ℕ∞) < ((2 * (D.rep + 1) : ℕ) : ℕ∞) := by exact_mod_cast hlt
    refine h₄.trans_le ?_
    push_cast
    push_cast at h₃
    gcongr
  obtain ⟨Δ, hΔ, hbd⟩ := exists_disc_of_lt_rep hF hlt₂
  have h₁' := (disc_facts hS h3 D.rad hF hΔ hbd).1
  have o := disc_order hS h3 D.rad hF hΔ hbd
  have heven : F.E.ncard ≤ 2 * D.rep := by omega
  have hmem : (partIn cap D.P.Γ Δ, partIn cap D.P.Γ (closure Δᶜ)) ∈ D.𝒯 ∨
      (partIn cap D.P.Γ (closure Δᶜ), partIn cap D.P.Γ Δ) ∈ D.𝒯 := D.isTangle.axiom1 h₁' (by omega)
  have h₀ : Sided F (discInt Δ) Δᶜ := ⟨Δ, hΔ, hbd, Or.inl ⟨rfl, rfl⟩⟩
  have hsides : IsSidesOf F (closure Δᶜ) Δ := by
    have := (Sided.symm h₀).isSidesOf hT
    rwa [closure_discInt hΔ] at this
  rcases hmem with h | h
  · exact absurd ⟨Δ, hΔ, hbd, h⟩ hno
  · have hnd : ¬ IsClosedDisc (closure Δᶜ) := fun hd ↦ by
      refine hno ⟨closure Δᶜ, hd, discBd_closure_compl hT hΔ hbd hd, ?_⟩
      have hO := isSide_out hT hΔ hbd
      have hE : closure Δᶜ = Δᶜ ∪ F.U := by
        rw [closure_eq_self_union_frontier, hO.frontier_eq]
      have hc : (closure Δᶜ)ᶜ = discInt Δ := by
        rw [hE]
        ext x
        simp only [mem_compl_iff, mem_union, not_or, not_not]
        exact ⟨fun h ↦ ⟨h.1, hbd ▸ h.2⟩, fun h ↦ ⟨h.1, hbd ▸ h.2⟩⟩
      rw [hc, closure_discInt hΔ]
      exact h
    refine ⟨F, ⟨hF, heven, closure Δᶜ, Δ, hsides, hnd, h⟩, fun hsph ↦ hnd ?_⟩
    obtain ⟨Δ₁, Δ₂, -, h₁d, h₂d, -, -, hun, hin, -, huniq⟩ := sphere_disc Shat hsph F.U
      (IsCircuit.isOArc_U hF.2)
    have hO := isSide_out hT hΔ hbd
    have hE : closure Δᶜ = Δᶜ ∪ F.U := by
      rw [closure_eq_self_union_frontier, hO.frontier_eq]
    have key : ∀ {A B : Set Shat}, A ∪ B = univ → A ∩ B = F.U → Aᶜ ∪ F.U = B := fun {A B} hu hi ↦ by
      ext x
      constructor
      · rintro (hx | hx)
        · exact (eq_univ_iff_forall.1 hu x).resolve_left hx
        · exact (hi ▸ hx : x ∈ A ∩ B).2
      · intro hx
        by_cases hxA : x ∈ A
        · exact Or.inr (hi ▸ ⟨hxA, hx⟩)
        · exact Or.inl hxA
    rw [hE]
    rcases huniq Δ hΔ hbd with rfl | rfl
    · rwa [key hun hin]
    · rwa [key (by rwa [union_comm]) (by rwa [inter_comm])]

/-- **A representativeness flaw exists.** -/
theorem exists_repFlaw (h₁ : (D.rep : ℕ∞) < Painting.rep D.rad) (h₂ : D.rep < D.ord) : ∃ F,
  D.IsRepFlaw F := by
  classical
  obtain ⟨F₀, hF₀, hns⟩ := exists_candidate hS h3 h₁ h₂
  have hfin : {F | D.IsFlawCandidate F}.Finite :=
    (finite_circuits D.rad.G).subset fun F hF ↦ ⟨hF.1.2, hF.1.1⟩
  obtain ⟨F, hF, hmin⟩ := Set.exists_min_image _ (fun F ↦ D.tb.weightSub F) hfin ⟨F₀, hF₀⟩
  exact ⟨F, h₁, h₂, hns, hF.1, hF.2.1, hF.2.2, fun F' h₃ h₄ h₅ ↦ hmin F' ⟨h₃, h₄, h₅⟩⟩

omit [T2Space S] [T2Space Shat] hS in
/-- A ring of `Σ` holds two vertices of `Γ`, unless it bounds a disc of `Σ̂` in `Σ` with no vertex
of `Γ` off the ring. -/
theorem two_vertices_of_ring {K : Drawing S} (hO : IsOArc K.U) (hinter : D.P.Γ.U ∩ K.U ⊆ D.P.Γ.V ∩
  K.V) (hsing : (K.U ∩ bd S).Subsingleton)
    (hempty : ∀ Δ : Set Shat, IsClosedDisc Δ → Δ ⊆ range cap.emb → discBd Δ = cap.emb '' K.U →
      (∀ v ∈ D.P.Γ.V, cap.emb v ∈ Δ → cap.emb v ∈ cap.emb '' K.U) → False) :
    ∃ a ∈ K.U ∩ D.P.Γ.V, ∃ b ∈ K.U ∩ D.P.Γ.V, a ≠ b := by
  by_contra hno
  push Not at hno
  have hfinU : (K.U ∩ D.P.Γ.V).Finite := D.P.Γ.finite_V.inter_of_right _
  have hfinb : (K.U ∩ bd S).Finite := hsing.finite
  have hle₁ : (K.U ∩ D.P.Γ.V).ncard ≤ 1 := (ncard_le_one hfinU).2 hno
  have hle₂ : (K.U ∩ bd S).ncard ≤ 1 := (ncard_le_one hfinb).2 fun a ha b hb ↦ hsing ha hb
  obtain ⟨Δ, hΔ, hb, hΔV⟩ := h3.2 K.U hO (fun x hx ↦ (hinter ⟨hx.2, hx.1⟩).1) hfinb (by omega)
  refine hempty _ (isClosedDisc_image hΔ cap.isEmbedding).1 (image_subset_range _ _) ?_ ?_
  · rw [(isClosedDisc_image hΔ cap.isEmbedding).2, hb]
  · intro v hv hvΔ
    obtain ⟨u, hu, hvu⟩ := hvΔ
    obtain rfl := cap.isEmbedding.injective hvu
    exact mem_image_of_mem _ (hΔV ⟨hu, hv⟩)

/-- The part in `Σ` of a circuit of the two forms is a feature, and it holds two vertices of `Γ`. -/
theorem exists_part_of_form [Nonempty S] {F : Drawing Shat} (hF : F.IsCircuitOf D.rad.G)
    (hform : ((F.U ∩ cap.emb '' bd S).ncard ≤ 1 ∧ F.U ⊆ range cap.emb) ∨
      ((F.U ∩ cap.emb '' bd S).ncard = 2 ∧ ¬ F.U ⊆ range cap.emb))
    (hempty : ∀ Δ : Set Shat, IsClosedDisc Δ → Δ ⊆ range cap.emb → discBd Δ = F.U →
      (∀ v ∈ D.P.Γ.V, cap.emb v ∈ Δ → cap.emb v ∈ F.U) → False) :
    ∃ K, IsCircuitPart cap χ.Φ D.P.Γ F K ∧ ∃ a ∈ K.U ∩ D.P.Γ.V, ∃ b ∈ K.U ∩ D.P.Γ.V, a ≠ b := by
  classical
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  obtain ⟨hFG, hFc⟩ := hF
  rcases hform with ⟨hc, hr⟩ | ⟨hc, hr⟩
  · have hnp : ∀ z ∈ F.V, z ∉ D.rad.poles := fun z hz hzp ↦ by
      obtain ⟨Θ, hΘ, -, hzd⟩ := D.rad.pole_cases hzp
      exact cap.notMem_range hΘ hzd (hr (F.V_subset_U hz))
    have hfin : (F.U ∩ cap.emb '' bd S).Finite := F.finite_V.subset fun x ⟨hx, v, hv, hvx⟩ ↦ by
      subst hvx
      exact (D.rad.bd_point hFG hv hx).2.1
    obtain ⟨K, h₁, hKU, hO, hsing⟩ := ring_of_circuit hS D.rad D.P.fits hFG hFc hnp
      (fun {x y} hxb hyb hxF hyF ↦ by
      have := (ncard_le_one hfin).1 hc _ ⟨hxF, mem_image_of_mem _ hxb⟩ _ ⟨hyF, mem_image_of_mem _
        hyb⟩
      exact cap.isEmbedding.injective this)
    refine ⟨K, h₁, two_vertices_of_ring h3 hO h₁.inter hsing fun Δ h₁ h₂ h₃ h₄ ↦ ?_⟩
    exact hempty Δ h₁ h₂ (h₃.trans hKU.symm) (by rwa [hKU])
  · have hex : ∃ p ∈ D.rad.poles, p ∈ F.V := by
      by_contra hno
      push Not at hno
      exact hr (subset_range_of_no_pole D.rad hFG fun z hz hzp ↦ hno z hzp hz)
    obtain ⟨p, hp, hpF⟩ := hex
    obtain ⟨Θ, hΘ, hreg, hpd⟩ := D.rad.pole_cases hp
    obtain ⟨e₁, e₂, v₁, v₂, he₁, he₂, hv₁, hv₂, hne, hs₁, hs₂, -⟩ := D.rad.circuit_edges hS h3
      ⟨hFG, hFc⟩ hpF hp.1
    have hfin : (F.U ∩ cap.emb '' bd S).Finite := F.finite_V.subset fun x ⟨hx, v, hv, hvx⟩ ↦ by
      subst hvx
      exact (D.rad.bd_point hFG hv hx).2.1
    have hend : ∀ {e v}, e ∈ F.E → closure e ∩ D.rad.G.V = {cap.emb v, p} → v ∈ Θ ∧ cap.emb v ∈ F.V
      := fun {e v} he hset ↦ by
      refine ⟨(D.rad.pole_edge (hFG.2 he) hp hΘ hreg hset).2, ?_⟩
      have : cap.emb v ∈ closure e ∩ F.V := by
        rw [hFG.closure_inter_V he, hset]
        exact mem_insert _ _
      exact this.2
    have hin : ∀ {v : S}, v ∈ Θ → cap.emb v ∈ F.V → cap.emb v ∈ F.U ∩ cap.emb '' bd S
      := fun {v} h₁ h₂ ↦
      ⟨F.V_subset_U h₂, mem_image_of_mem _ (cuff_subset_bd ⟨Θ, hΘ⟩ h₁)⟩
    obtain ⟨hΘ₁, hF₁⟩ := hend he₁ hs₁
    obtain ⟨hΘ₂, hF₂⟩ := hend he₂ hs₂
    have hsub : ({cap.emb v₁, cap.emb v₂} : Set Shat) ⊆ F.U ∩ cap.emb '' bd S := by
      rintro x (rfl | rfl)
      · exact hin hΘ₁ hF₁
      · exact hin hΘ₂ hF₂
    have hemb : cap.emb v₁ ≠ cap.emb v₂ := fun h ↦ hne (cap.isEmbedding.injective h)
    have heq : F.U ∩ cap.emb '' bd S = {cap.emb v₁, cap.emb v₂} := by
      refine (eq_of_subset_of_ncard_le hsub ?_ hfin).symm
      rw [hc, ncard_pair hemb]
    have hpick : ∀ {v : S}, v ∈ bd S → cap.emb v ∈ F.V → v = v₁ ∨ v = v₂ := fun {v} hb hF ↦ by
      have : cap.emb v ∈ F.U ∩ cap.emb '' bd S := ⟨F.V_subset_U hF, mem_image_of_mem _ hb⟩
      rw [heq] at this
      rcases this with h | h
      · exact Or.inl (cap.isEmbedding.injective h)
      · exact Or.inr (cap.isEmbedding.injective h)
    refine chord_of_circuit hS D.rad h3 D.P.fits hFG hFc hp hpF (fun z hz hzp ↦ ?_) fun {x} hxb _
      hxF ↦ ?_
    · obtain ⟨Θ', hΘ', hreg', hzd⟩ := D.rad.pole_cases hzp
      obtain ⟨f₁, -, u₁, -, hf₁, -, hu₁, -, -, hs₁', -, -⟩ := D.rad.circuit_edges hS h3 ⟨hFG, hFc⟩
        hz hzp.1
      have huΘ := (D.rad.pole_edge (hFG.2 hf₁) hzp hΘ' hreg' hs₁').2
      have huF : cap.emb u₁ ∈ F.V := by
        have : cap.emb u₁ ∈ closure f₁ ∩ F.V := by
          rw [hFG.closure_inter_V hf₁, hs₁']
          exact mem_insert _ _
        exact this.2
      have huΘ₀ : u₁ ∈ Θ := by
        rcases hpick (cuff_subset_bd ⟨Θ', hΘ'⟩ huΘ) huF with rfl | rfl
        · exact hΘ₁
        · exact hΘ₂
      have hee : Θ' = Θ := by
        by_contra hn
        exact disjoint_left.1 (cuffs_disjoint hΘ' hΘ hn) huΘ huΘ₀
      subst hee
      obtain ⟨-, -, hG3, -⟩ := id D.rad.isPreRadial
      exact (hG3 _ (D.rad.regionOf_mem hp.1).1).unique
        ⟨hreg.trans hreg'.symm ▸ (D.rad.regionOf_mem hzp.1).2, hzp.1.1⟩ ⟨(D.rad.regionOf_mem
          hp.1).2, hp.1.1⟩
    · rcases hpick hxb hxF with rfl | rfl
      · exact ⟨e₁, he₁, hs₁⟩
      · exact ⟨e₂, he₂, hs₂⟩

/-- The part of a representativeness flaw in `Σ` is a feature, and it holds two vertices of `Γ`. -/
theorem exists_flaw_part [Nonempty S] {F : Drawing Shat} (hFl : D.IsRepFlaw F) {S₁ S₂ : Set Shat}
  (hs : IsSidesOf F S₁ S₂)
    (hnd : ¬ IsClosedDisc S₁) (hm : (partIn cap D.P.Γ S₁, partIn cap D.P.Γ S₂) ∈ D.𝒯)
    (hd : ((F.E.ncard + 4 : ℕ) : ℕ∞) < Painting.dist D.rad * 4) :
    ∃ K, IsCircuitPart cap χ.Φ D.P.Γ F K ∧ ∃ a ∈ K.U ∩ D.P.Γ.V, ∃ b ∈ K.U ∩ D.P.Γ.V, a ≠ b := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hform : ((F.U ∩ cap.emb '' bd S).ncard ≤ 1 ∧ F.U ⊆ range cap.emb) ∨
    ((F.U ∩ cap.emb '' bd S).ncard = 2 ∧ ¬ F.U ⊆ range cap.emb) := by
    rcases TangleDatum.IsRepFlaw.second hS h3 hFl hs hnd hm with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h (not_le.2 hd)
  refine exists_part_of_form hS h3 hFl.is_circuit hform fun Δ hd' _ hbd' hΔV ↦ ?_
  rcases isSidesOf_cases hT hd' hbd' hs with ⟨rfl, -⟩ | ⟨rfl, rfl⟩
  · exact hnd hd'
  · refine D.isTangle.axiom3 hm ?_
    refine subset_antisymm inter_subset_left fun v hv ↦ ⟨hv, ?_⟩
    by_cases hvΔ : cap.emb v ∈ S₂
    · exact (isSide_out hT hd' hbd').U_subset_closure (hΔV v hv hvΔ)
    · exact subset_closure hvΔ

end TangleDatum

end GraphMinor.GM19
