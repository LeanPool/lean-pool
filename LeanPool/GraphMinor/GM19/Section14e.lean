/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section14d

/-!
# Graph Minors XIX, Section 14: the sectors and the hub cover the wheel
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology Metric GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

namespace TangleDatum

variable {D : TangleDatum cap χ} {W : Set Shat} {H : Drawing Shat} {ρ : ℕ}

omit [T2Space Shat] in
/-- The two ends of an edge of `Γ*`: one is a vertex of `Γ` and one is in `R*`. -/
theorem exists_Rstar_end (D : TangleDatum cap χ) {e : Set Shat} {x y : Shat}
  (hl : D.rad.G.toGraph.IsLink e x y) : x ∈ D.rad.Rstar ∨ y ∈ D.rad.Rstar := by
  have h := D.even_length_walk (GraphWalk.cons hl (.nil hl.2.2.1))
  have hodd : ¬ Even (GraphWalk.cons hl (.nil hl.2.2.1)).length := by
    rw [show (GraphWalk.cons hl (.nil hl.2.2.1)).length = 1 from rfl]
    decide
  rw [h] at hodd
  by_cases hx : x ∈ D.P.Γ.hatV cap
  · exact .inr ⟨hl.2.2.1, fun hy ↦ hodd (by simp [hx, hy])⟩
  · exact .inl ⟨hl.2.1, hx⟩

/-- Each point of `bd(W)` is on an edge of `bd(W)` at a vertex of `R*`. -/
theorem IsWheelHubOfRadius.exists_region_of_bd (h : D.IsWheelHubOfRadius W H ρ) {y : Shat}
  (hy : y ∈ discBd W) :
    ∃ r ∈ D.rad.Rstar ∩ discBd W, ∃ f ∈ D.rad.G.E, f ⊆ discBd W ∧ r ∈ closure f ∧ y ∈ closure f
      := by
  classical
  have : ConnectedSpace Shat := cap.connected
  have hcl : IsClosed (discBd W) := by
    rw [← IsClosedDisc.frontier_eq_discBd cap.isClosedSurface h.is_disc]
    exact isClosed_frontier
  obtain ⟨F, hFc, hFs, hFU⟩ := exists_circuit_of_oArc h.is_disc.isOArc_discBd h.bd_sub
  have hedge : ∀ {e}, e ∈ F.E → ∃ x z, D.rad.G.toGraph.IsLink e x z ∧ e ⊆ discBd W
    := fun {e} he ↦ by
    have heG := hFs.2 he
    obtain ⟨x, hx, z, hz, hcap⟩ := D.rad.isPreRadial.2.2.2.2.1 e heG
    refine ⟨x, z, ⟨heG, D.rad.isPreRadial.2.1 hx, hz.1, hcap⟩, ?_⟩
    rw [← hFU]
    exact fun w hw ↦ F.closure_subset_U he (subset_closure hw)
  have hfinish : ∀ {e}, e ∈ F.E → y ∈ closure e → ∃ r ∈ D.rad.Rstar ∩ discBd W, ∃ f ∈ D.rad.G.E, f
    ⊆ discBd W ∧ r ∈ closure f ∧ y ∈ closure f := fun {e} he hye ↦ by
    obtain ⟨x, z, hl, hsub⟩ := hedge he
    have hends : x ∈ closure e ∧ z ∈ closure e := by
      have hc := hl.2.2.2
      exact ⟨(hc.symm ▸ (Or.inl rfl : x ∈ ({x, z} : Set Shat)) : x ∈ closure e ∩ D.rad.G.V).1,
        (hc.symm ▸ (Or.inr rfl : z ∈ ({x, z} : Set Shat)) : z ∈ closure e ∩ D.rad.G.V).1⟩
    rcases D.exists_Rstar_end hl with hr | hr
    · exact ⟨x, ⟨hr, closure_minimal hsub hcl hends.1⟩, e, hl.1, hsub, hends.1, hye⟩
    · exact ⟨z, ⟨hr, closure_minimal hsub hcl hends.2⟩, e, hl.1, hsub, hends.2, hye⟩
  have hyF : y ∈ F.U := hFU ▸ hy
  rw [Drawing.U_eq] at hyF
  rcases hyF with hyV | hyE
  swap
  · obtain ⟨e, he, hye⟩ : ∃ e ∈ F.E, y ∈ closure e := by simpa using hyE
    exact hfinish he hye
  -- A vertex of a circuit has an edge.
  obtain ⟨u, Z, hZ, hpos, hV, hE⟩ := hFc
  rw [hV] at hyV
  have hyZ : y ∈ Z.support := hyV
  obtain ⟨L, R, hLR⟩ := Z.exists_append_of_mem hyZ
  have hlen : 0 < L.length ∨ 0 < R.length := by
    rw [hLR, GraphWalk.length_append] at hpos
    omega
  rcases hlen with hp | hp
  · cases hc : L.reverse with
    | nil _ =>
      have : L.reverse.length = 0 := by rw [hc]; rfl
      rw [GraphWalk.length_reverse] at this
      omega
    | @cons _ _ _ e hl t =>
      have heF : e ∈ F.E := by
        rw [hE]
        have h₁ : e ∈ L.reverse.edges := by rw [hc]; simp
        rw [GraphWalk.edges_reverse, List.mem_reverse] at h₁
        change e ∈ Z.edges
        rw [hLR, GraphWalk.edges_append]
        exact List.mem_append_left _ h₁
      have hm : y ∈ closure e ∩ F.V := by
        rw [hl.2.2.2]
        exact .inl rfl
      exact hfinish heF hm.1
  · cases R with
    | nil _ => simp [GraphWalk.length] at hp
    | @cons _ _ _ e hl t =>
      have heF : e ∈ F.E := by
        rw [hE]
        change e ∈ Z.edges
        rw [hLR, GraphWalk.edges_append]
        exact List.mem_append_right _ (by simp)
      have hm : y ∈ closure e ∩ F.V := by
        rw [hl.2.2.2]
        exact .inl rfl
      exact hfinish heF hm.1

/-- The vertices of `Γ` on `bd(W)`. -/
def bdVerts (D : TangleDatum cap χ) (W : Set Shat) : Set Shat := (cap.emb '' D.Γ.V) ∩ discBd W

omit [T2Space S] [T2Space Shat] in
theorem finite_bdVerts (D : TangleDatum cap χ) (W : Set Shat) : (bdVerts D W).Finite :=
  (D.Γ.finite_V.image _).subset inter_subset_left

/-- One spoke from each vertex of `Γ` on `bd(W)`. -/
structure SpokeSystem (D : TangleDatum cap χ) (W : Set Shat) (H : Drawing Shat) where
  /-- The endpoint in the hub chosen for each boundary vertex. -/
  hEnd : bdVerts D W → Shat
  /-- The radial walk from each boundary vertex to its chosen endpoint. -/
  K : ∀ v : bdVerts D W, GraphWalk D.rad.G.toGraph v.1 (hEnd v)
  spoke : ∀ v, D.IsSpokeWalk W H (K v)

omit [T2Space S] in
theorem exists_spokeSystem (hW : D.IsWheelHubOfRadius W H ρ) : Nonempty (SpokeSystem D W H) := by
  have h : ∀ v : bdVerts D W, ∃ (h : Shat) (K : GraphWalk D.rad.G.toGraph v.1 h), D.IsSpokeWalk W H
    K := fun v ↦ hW.exists_spoke v.2
  choose e K hK using h
  exact ⟨⟨e, K, hK⟩⟩

/-- The point set of a spoke. -/
def SpokeSystem.U (sp : SpokeSystem D W H) (v : bdVerts D W) : Set Shat := (walkDrawing D.rad.G
  (sp.K v)).U

/-- The hub as a set: the disc `ins(H)`, or the one vertex of `H`. -/
noncomputable def hubSet (D : TangleDatum cap χ) (H : Drawing Shat) : Set Shat := by
  classical exact if H.V.ncard = 1 then H.U else D.ins H

/-- The hub with all the spokes. -/
noncomputable def SpokeSystem.A (sp : SpokeSystem D W H) : Set Shat := hubSet D H ∪ ⋃ v, sp.U v

omit [T2Space S] [T2Space Shat] in
/-- The two cases of a hub. -/
theorem IsWheelHubOfRadius.hub_cases (hW : D.IsWheelHubOfRadius W H ρ) :
    (∃ z, H.V = {z} ∧ H.U = {z} ∧ hubSet D H = {z}) ∨ (IsEnclave D.tb D.ord D.𝒯 H ∧ H.E.ncard
      ≤ 4 * ρ + 4 ∧ H.V.ncard ≠ 1 ∧ hubSet D H = D.ins H) := by
  classical
  rcases hW.hub_cond with ⟨hc, hE, -⟩ | ⟨hH, hle, -⟩
  · obtain ⟨z, hz⟩ := ncard_eq_one.mp hc
    have hU : H.U = {z} := by
      rw [H.U_eq, hz, hE]
      simp
    refine .inl ⟨z, hz, hU, ?_⟩
    rw [hubSet, ite_eq_left hc, hU]
  · obtain ⟨-, -, -, hcirc, -⟩ := id hH
    have hne := IsCircuit.two_vertices D hcirc
    refine .inr ⟨hH, hle, hne, ?_⟩
    rw [hubSet, ite_eq_right hne]

omit [T2Space S] in
theorem IsWheelHubOfRadius.hubSet_facts (hW : D.IsWheelHubOfRadius W H ρ) : IsClosed (hubSet D H)
  ∧ hubSet D H ⊆ W ∧ Disjoint (hubSet D H) (discBd W) ∧ H.U ⊆ hubSet D H := by
  have : ConnectedSpace Shat := cap.connected
  rcases hW.hub_cases with ⟨z, -, hU, hh⟩ | ⟨hH, hle, -, hh⟩
  · rw [hh]
    have hzU : z ∈ H.U := hU ▸ rfl
    have hzi := hW.H_in_int hzU
    exact ⟨isClosed_singleton, singleton_subset_iff.mpr hzi.1, disjoint_singleton_left.mpr hzi.2,
      hU.subset⟩
  · rw [hh]
    obtain ⟨-, -, -, hc, -⟩ := id hH
    have hrep := hW.rep_ge
    have hi := D.ins_spec hc (by omega)
    refine ⟨hi.2.2.1.isClosed, hW.ins_sub H hc hle (hW.H_in_int.trans sdiff_subset), hW.ins_off_bd
      hc hle, ?_⟩
    rw [← hi.2.2.2.1]
    exact Surface.discBd_subset _

/-- The hub meets a spoke in the inner end. -/
theorem IsWheelHubOfRadius.hubSet_inter_spoke (hW : D.IsWheelHubOfRadius W H ρ) {v h : Shat} {K :
  GraphWalk D.rad.G.toGraph v h} (hK : D.IsSpokeWalk W H K) :
    hubSet D H ∩ (walkDrawing D.rad.G K).U = {h} := by
  have hhH : h ∈ H.U := H.V_subset_U hK.2.h_mem
  have hhK : h ∈ (walkDrawing D.rad.G K).U := (mem_walkDrawing_U _ _).mpr (.inl K.end_mem_support)
  apply subset_antisymm
  · rintro y ⟨hy, hyK⟩
    rcases hW.hub_cases with ⟨z, -, hU, hh⟩ | ⟨hH, hle, -, hh⟩
    · rw [hh] at hy
      exact hK.U_inter_hub hW hyK (hU ▸ hy)
    · rw [hh] at hy
      obtain ⟨-, -, -, hc, -⟩ := id hH
      have hrep := hW.rep_ge
      have hi := D.ins_spec hc (by omega)
      by_cases hyb : y ∈ H.U
      · exact hK.U_inter_hub hW hyK hyb
      · exact absurd ⟨hy, fun h' ↦ hyb (hi.2.2.2.1 ▸ h')⟩ (disjoint_left.mp
          (hK.off_ins_hub hW hH hle) hyK)
  · rintro y rfl
    exact ⟨hW.hubSet_facts.2.2.2 hhH, hhK⟩

omit [T2Space S] in
/-- If two spokes meet then what they share is connected and holds the inner end. -/
theorem IsSpokeWalk.inter_facts {v₁ v₂ h₁ h₂ : Shat} {K₁ : GraphWalk D.rad.G.toGraph v₁ h₁} {K₂ :
  GraphWalk D.rad.G.toGraph v₂ h₂}
    (h1 : D.IsSpokeWalk W H K₁) (h2 : D.IsSpokeWalk W H K₂) {y : Shat} (hy₁ : y ∈
      (walkDrawing D.rad.G K₁).U) (hy₂ : y ∈ (walkDrawing D.rad.G K₂).U) :
    IsPreconnected ((walkDrawing D.rad.G K₁).U ∩ (walkDrawing D.rad.G K₂).U) ∧ h₁ ∈
      (walkDrawing D.rad.G K₁).U ∩ (walkDrawing D.rad.G K₂).U := by
  classical
  obtain ⟨x, hx₁, hx₂⟩ : ∃ x, x ∈ K₁.support ∧ x ∈ K₂.support := by
    rcases walkU_inter K₁ K₂ hy₁ hy₂ with ⟨h₃, h₄⟩ | ⟨e, he₁, he₂⟩
    · exact ⟨y, h₃, h₄⟩
    · obtain ⟨a, b, -, ha, -, hcap⟩ := D.exists_ends_of_mem_edges K₁ he₁
      exact ⟨a, ha, (D.ends_mem_support K₂ he₂ hcap).1⟩
  obtain rfl := h1.same_end h2 hx₁ hx₂
  obtain ⟨u, A₁, A₂, T, rfl, rfl, -, hmeet⟩ := h1.merge h2 hx₁ hx₂
  have heq : (walkDrawing D.rad.G (A₁.append T)).U ∩ (walkDrawing D.rad.G (A₂.append T)).U =
    (walkDrawing D.rad.G T).U := by
    apply subset_antisymm
    · rintro y ⟨h₃, h₄⟩
      rw [walkU_append] at h₃
      rcases h₃ with h₃ | h₃
      · rcases walkU_inter A₁ (A₂.append T) h₃ h₄ with ⟨h₅, h₆⟩ | ⟨e, he₁, he₂⟩
        · rw [hmeet y h₅ h₆]
          exact (mem_walkDrawing_U _ _).mpr (.inl T.start_mem_support)
        · obtain ⟨a, b, hab, ha, hb, hcap⟩ := D.exists_ends_of_mem_edges A₁ he₁
          obtain ⟨ha', hb'⟩ := D.ends_mem_support _ he₂ hcap
          exact absurd ((hmeet a ha ha').trans (hmeet b hb hb').symm) hab
      · exact h₃
    · exact subset_inter (walkU_right_subset A₁ T) (walkU_right_subset A₂ T)
  rw [heq]
  exact ⟨walkU_isPreconnected T (GraphWalk.IsSimple.of_append h1.1).2,
    (mem_walkDrawing_U _ _).mpr (.inl T.end_mem_support)⟩

/-- The hub with the spokes is closed, in `W`, and does not separate the plane. -/
theorem SpokeSystem.nonSep (hW : D.IsWheelHubOfRadius W H ρ) (sp : SpokeSystem D W H)
  (hbdS : discBd W ⊆ cap.emb '' (univ \ bd S))
    (hin : ((W \ discBd W) ∩ (cap.emb '' D.Γ.V)).Nonempty) {h : Shat → ℂ} {g : ℂ → Shat}
      (c : IsChart W h g) :
    IsClosed sp.A ∧ sp.A ⊆ W ∧ NonSep (h '' sp.A) := by
  classical
  have hcomp : CompactSpace Shat := cap.isClosedSurface.1
  have hinj : InjOn h W := c.gh.injOn
  have hhub := hW.hubSet_facts
  have hUW : ∀ v, sp.U v ⊆ W := fun v ↦ (sp.spoke v).subset_W hW hbdS hin
  have hUc : ∀ v, IsClosed (sp.U v) := fun v ↦ (walkDrawing _ _).isClosed_U
  have hsubW : ∀ s : Finset (bdVerts D W), hubSet D H ∪ ⋃ v ∈ s, sp.U v ⊆ W := fun s ↦
    union_subset hhub.2.1 (iUnion₂_subset fun v _ ↦ hUW v)
  have hcl : ∀ s : Finset (bdVerts D W), IsClosed (hubSet D H ∪ ⋃ v ∈ s, sp.U v) := fun s ↦
    hhub.1.union (isClosed_biUnion_finset fun v _ ↦ hUc v)
  have himC : ∀ {X : Set Shat}, IsClosed X → X ⊆ W → IsCompact (h '' X) := fun hX hXW ↦
    hX.isCompact.image_of_continuousOn (c.hc.mono hXW)
  have hhubN : NonSep (h '' hubSet D H) := by
    rcases hW.hub_cases with ⟨z, -, -, hh⟩ | ⟨hH, hle, -, hh⟩
    · rw [hh, image_singleton]
      exact nonSep_singleton _
    · obtain ⟨-, -, -, hcirc, -⟩ := id hH
      have hrep := hW.rep_ge
      have hi := D.ins_spec hcirc (by omega)
      rw [hh] at hhub ⊢
      have hsubB : h '' D.ins H ⊆ closedBall 0 1 := image_subset_iff.mpr fun a ha ↦ c.hm
        (hhub.2.1 ha)
      exact nonSep_of_disc (hi.2.2.1.image (c.hc.mono hhub.2.1) (c.gc.mono hsubB)
        (c.gh.mono hhub.2.1)).1 hsubB
  have hlineN : ∀ v, NonSep (h '' sp.U v) := by
    intro v
    have hne : v.1 ≠ sp.hEnd v := fun e ↦ (hW.H_in_int (H.V_subset_U (sp.spoke v).2.h_mem)).2
      (e ▸ v.2.2)
    obtain ⟨φ, -⟩ := isLine_of_isPathBetween (walkDrawing_isPathBetween _ (sp.spoke v).1) hne
    obtain ⟨e, -⟩ := exists_homeomorph_image (Δ := sp.U v) (c.hc.mono (hUW v)) (c.gc.mono
      (image_subset_iff.mpr fun a ha ↦ c.hm (hUW v ha))) (c.gh.mono (hUW v))
    exact nonSep_of_line ⟨φ.trans e, rfl, rfl⟩
  have hind : ∀ s : Finset (bdVerts D W), NonSep (h '' (hubSet D H ∪ ⋃ v ∈ s, sp.U v)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hhubN
    | @insert a s _ ih =>
      have hrw : hubSet D H ∪ ⋃ v ∈ insert a s, sp.U v = (hubSet D H ∪ ⋃ v ∈ s, sp.U v) ∪ sp.U a
        := by
        ext x
        simp only [mem_union, mem_iUnion, Finset.mem_insert, exists_prop]
        constructor
        · rintro (h' | ⟨v, rfl | hv, hx⟩)
          · exact .inl (.inl h')
          · exact .inr hx
          · exact .inl (.inr ⟨v, hv, hx⟩)
        · rintro ((h' | ⟨v, hv, hx⟩) | hx)
          · exact .inl h'
          · exact .inr ⟨v, .inr hv, hx⟩
          · exact .inr ⟨a, .inl rfl, hx⟩
      rw [hrw, image_union]
      refine ih.union (hlineN a) (himC (hcl s) (hsubW s)) (himC (hUc a) (hUW a)) ?_
      rw [← InjOn.image_inter hinj (hsubW s) (hUW a)]
      refine IsPreconnected.image ?_ _ (c.hc.mono (inter_subset_right.trans (hUW a)))
      refine isPreconnected_of_forall (sp.hEnd a) fun y hy ↦ ?_
      rcases hy.1 with hyh | hyU
      · have hyp : y ∈ ({sp.hEnd a} : Set Shat) := hW.hubSet_inter_spoke (sp.spoke a) ▸
          (⟨hyh, hy.2⟩ : y ∈ hubSet D H ∩ (walkDrawing D.rad.G (sp.K a)).U)
        have hpm : sp.hEnd a ∈ (hubSet D H ∪ ⋃ v ∈ s, sp.U v) ∩ sp.U a
          := mem_singleton_iff.mp hyp ▸ hy
        exact ⟨{sp.hEnd a}, singleton_subset_iff.mpr hpm, rfl, hyp, isPreconnected_singleton⟩
      · obtain ⟨w, hw, hyw⟩ : ∃ w ∈ s, y ∈ sp.U w := by simpa using hyU
        obtain ⟨hp, hm⟩ := (sp.spoke a).inter_facts (sp.spoke w) hy.2 hyw
        refine ⟨sp.U a ∩ sp.U w, ?_, hm, ⟨hy.2, hyw⟩, hp⟩
        rintro z ⟨hz₁, hz₂⟩
        exact ⟨.inr (mem_biUnion hw hz₂), hz₁⟩
  have hfin : Finite (bdVerts D W) := (finite_bdVerts D W).to_subtype
  have hfty := Fintype.ofFinite (bdVerts D W)
  have heq : sp.A = hubSet D H ∪ ⋃ v ∈ (Finset.univ : Finset (bdVerts D W)), sp.U v := by
    simp [SpokeSystem.A]
  rw [heq]
  exact ⟨hcl _, hsubW _, hind _⟩

/-- The sector at `r`, for a fixed system of spokes. -/
structure SectorAt (sp : SpokeSystem D W H) (r : Shat) where
  /-- The first boundary vertex of the sector. -/
  v₁ : bdVerts D W
  /-- The second boundary vertex of the sector. -/
  v₂ : bdVerts D W
  /-- The first radial edge adjacent to the sector at its pole. -/
  f₁ : Set Shat
  /-- The second radial edge adjacent to the sector at its pole. -/
  f₂ : Set Shat
  /-- The radial boundary walk between the two boundary vertices. -/
  Z : GraphWalk D.rad.G.toGraph v₁.1 v₂.1
  /-- The closed disc of the sector. -/
  Δ : Set Shat
  /-- The complementary disc in the hub boundary. -/
  Δ' : Set Shat
  /-- The circuit bounding the sector disc. -/
  C : Drawing Shat
  full : D.IsFullSector W H r f₁ f₂ (sp.K v₁) (sp.K v₂) Z Δ Δ' C
  only : ∀ f ∈ D.rad.G.E, f ⊆ discBd W → r ∈ closure f → f = f₁ ∨ f = f₂

theorem exists_sectorAt (hopt : D.IsOptimalWheelHub W H ρ) (hbdS : discBd W ⊆ cap.emb ''
  (univ \ bd S)) (hin : ((W \ discBd W) ∩ (cap.emb '' D.Γ.V)).Nonempty)
    (sp : SpokeSystem D W H) {r : Shat} (hr : r ∈ D.rad.Rstar ∩ discBd W) : Nonempty
      (SectorAt sp r) := by
  have hW := hopt.toIsWheelHubOfRadius
  have hcl : IsClosed (discBd W) := by
    rw [← IsClosedDisc.frontier_eq_discBd cap.isClosedSurface hW.is_disc]
    exact isClosed_frontier
  obtain ⟨f₁, f₂, v₁, v₂, hne, hl₁, hl₂, hf₁, hf₂, honly⟩ := hW.exists_two_bd_edges hbdS hin hr.1
    hr.2
  have hend : ∀ {f : Set Shat} {v : Shat}, D.rad.G.toGraph.IsLink f r v → f ⊆ discBd W
    → v ∈ bdVerts D W := fun {f v} hl hf ↦ by
    have hm : v ∈ closure f ∩ D.rad.G.V := by
      rw [hl.2.2.2]
      exact .inr rfl
    exact ⟨D.hatV_of_link hr.1 hl, closure_minimal hf hcl hm.1⟩
  have m₁ := hend hl₁ hf₁
  have m₂ := hend hl₂ hf₂
  obtain ⟨Z, Δ, Δ', C, hs⟩ := exists_fullSector hopt hbdS hin (sp.spoke ⟨v₁, m₁⟩)
    (sp.spoke ⟨v₂, m₂⟩) hr hl₁ hl₂ hne hf₁ hf₂
  exact ⟨⟨⟨v₁, m₁⟩, ⟨v₂, m₂⟩, f₁, f₂, Z, Δ, Δ', C, hs, honly⟩⟩

variable {sp : SpokeSystem D W H} {r r' : Shat}

omit [T2Space S] in
theorem SectorAt.Δ_subset (s : SectorAt sp r) : s.Δ ⊆ W := by
  have h := s.full.union
  intro x hx
  have h' : x ∈ s.Δ ∪ s.Δ' := .inl hx
  rwa [h] at h'

omit [T2Space S] in
theorem SectorAt.Z_subset_A (s : SectorAt sp r) (hW : D.IsWheelHubOfRadius W H ρ) :
  (walkDrawing D.rad.G s.Z).U ⊆ sp.A := by
  have h := s.full.Z_sub
  rintro y hy
  rcases h hy with (h' | h') | h'
  · exact .inr (mem_iUnion.mpr ⟨s.v₁, h'⟩)
  · exact .inr (mem_iUnion.mpr ⟨s.v₂, h'⟩)
  · exact .inl (hW.hubSet_facts.2.2.2 h')

omit [T2Space S] in
theorem SpokeSystem.start_mem_A (sp : SpokeSystem D W H) (v : bdVerts D W) : v.1 ∈ sp.A :=
  .inr (mem_iUnion.mpr ⟨v, (mem_walkDrawing_U _ _).mpr (.inl (sp.K v).start_mem_support)⟩)

/-- **The sectors cover `W`, apart from the hub and the spokes.** -/
theorem SpokeSystem.cover (hW : D.IsWheelHubOfRadius W H ρ) (sp : SpokeSystem D W H)
  (hbdS : discBd W ⊆ cap.emb '' (univ \ bd S))
    (hin : ((W \ discBd W) ∩ (cap.emb '' D.Γ.V)).Nonempty) {ι : Type*} (reg : ι → Shat)
      (sec : ∀ i, SectorAt sp (reg i)) (hreg : ∀ r ∈ D.rad.Rstar ∩ discBd W, ∃ i, reg i
        = r) {x : Shat} (hx : x ∈ W) (hxA : x ∉ sp.A) :
    ∃ r, x ∈ (sec r).Δ := by
  classical
  have hT := cap.isClosedSurface
  have : CompactSpace Shat := hT.1
  have hcl : IsClosed (discBd W) := by
    rw [← IsClosedDisc.frontier_eq_discBd hT hW.is_disc]
    exact isClosed_frontier
  have hman := (IsClosedSurface.isSurface hT).2.2
  -- A point of `bd(W)` off the spokes lies on the two edges at some `r`, and is not an end of them.
  have hbd : ∀ {y}, y ∈ discBd W → y ∉ sp.A → ∃ r, y ∈ closure (sec r).f₁ ∪ closure (sec r).f₂
    := fun {y} hy _ ↦ by
    obtain ⟨r, hr, f, hf, hfb, hrf, hyf⟩ := hW.exists_region_of_bd hy
    obtain ⟨i, rfl⟩ := hreg r hr
    refine ⟨i, ?_⟩
    rcases (sec i).only f hf hfb hrf with rfl | rfl
    · exact .inl hyf
    · exact .inr hyf
  by_cases hxb : x ∈ discBd W
  · obtain ⟨r, hr⟩ := hbd hxb hxA
    refine ⟨r, Surface.discBd_subset _ ?_⟩
    rw [(sec r).full.bd_eq]
    exact .inl hr
  obtain ⟨hAc, hAW, hAN⟩ := id (sp.nonSep hW hbdS hin (Classical.choose_spec
    (Classical.choose_spec hW.is_disc.exists_isChart)))
  obtain ⟨J, y, hJc, hxJ, hJ, hy, hyc⟩ := exists_plane_exit_of_disc
    (Classical.choose_spec (Classical.choose_spec hW.is_disc.exists_isChart)) hAN hAc.isCompact hAW
      ⟨hx, hxb⟩ hxA
  obtain ⟨r, hr⟩ := hbd hy.1 hy.2
  have hs := (sec r).full
  have hyΔ : y ∈ (sec r).Δ := Surface.discBd_subset _ (hs.bd_eq ▸ .inl hr)
  have hyΔ' : y ∉ (sec r).Δ' := fun h' ↦ hy.2 ((sec r).Z_subset_A hW (hs.inter ▸ ⟨hyΔ, h'⟩))
  have hoff : ∀ z ∈ J, z ∉ discBd (sec r).Δ := by
    intro z hz hzb
    rw [hs.bd_eq] at hzb
    rcases hzb with hzb | hzb
    · have hsub : closure (sec r).f₁ ∪ closure (sec r).f₂ ⊆ discBd W := union_subset
        (closure_minimal hs.f₁_bd hcl) (closure_minimal hs.f₂_bd hcl)
      exact (hJ hz).1.2 (hsub hzb)
    · exact (hJ hz).2 ((sec r).Z_subset_A hW hzb)
  obtain ⟨z, hzo, hzJ⟩ := mem_closure_iff.mp hyc _ hs.disc'.isClosed.isOpen_compl hyΔ'
  have hzΔ : z ∈ (sec r).Δ := by
    have : z ∈ W := (hJ hzJ).1.1
    have hu := hs.union
    rw [← hu] at this
    exact this.resolve_right hzo
  have hop : IsOpen (discInt (sec r).Δ) := hs.disc.isOpen_discInt hman
  have hsplit := hJc.subset_left_of_subset_union hop hs.disc.isClosed.isOpen_compl
    (disjoint_left.mpr fun a ha hb ↦ hb ha.1) (fun a ha ↦ by
      by_cases h' : a ∈ (sec r).Δ
      · exact .inl ⟨h', hoff a ha⟩
      · exact .inr h') ⟨z, hzJ, hzΔ, hoff z hzJ⟩
  exact ⟨r, (hsplit hxJ).1⟩

omit [T2Space S] in
/-- The boundary of a sector misses the inside of each sector. -/
theorem SectorAt.bd_off (hW : D.IsWheelHubOfRadius W H ρ) (s : SectorAt sp r)
  (s' : SectorAt sp r') : Disjoint (discBd s.Δ) (discInt s'.Δ) := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hcl : IsClosed (discBd W) := by
    rw [← IsClosedDisc.frontier_eq_discBd hT hW.is_disc]
    exact isClosed_frontier
  refine disjoint_left.mpr fun y hy hyi ↦ ?_
  rw [s.full.bd_eq] at hy
  rcases hy with hy | hy
  · refine discInt_off_bd hT hW.is_disc s'.full.disc s'.Δ_subset hyi ?_
    exact (union_subset (closure_minimal s.full.f₁_bd hcl) (closure_minimal s.full.f₂_bd hcl)) hy
  · rcases s.full.Z_sub hy with (h' | h') | h'
    · exact disjoint_left.mp (s'.full.spoke_off _ _ _ (sp.spoke s.v₁)) h' hyi
    · exact disjoint_left.mp (s'.full.spoke_off _ _ _ (sp.spoke s.v₂)) h' hyi
    · exact disjoint_left.mp s'.full.hub_off h' hyi

/-- **Two sectors have disjoint insides.** -/
theorem SectorAt.disjoint_int (hW : D.IsWheelHubOfRadius W H ρ) (hbdS : discBd W ⊆ cap.emb ''
  (univ \ bd S)) (hin : ((W \ discBd W) ∩ (cap.emb '' D.Γ.V)).Nonempty)
    (s : SectorAt sp r) (s' : SectorAt sp r') (hne : r ≠ r') : Disjoint (discInt s.Δ)
      (discInt s'.Δ) := by
  classical
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hman := (IsClosedSurface.isSurface hT).2.2
  have hcl : IsClosed (discBd W) := by
    rw [← IsClosedDisc.frontier_eq_discBd hT hW.is_disc]
    exact isClosed_frontier
  have hside : ∀ {r r' : Shat} (s : SectorAt sp r) (s' : SectorAt sp r'), Disjoint (discBd s.Δ)
    (discInt s'.Δ) := fun s s' ↦ SectorAt.bd_off hW s s'
  have hsub : ∀ {r r' : Shat} (s : SectorAt sp r) (s' : SectorAt sp r'),
    (discInt s.Δ ∩ discInt s'.Δ).Nonempty → discInt s'.Δ ⊆ discInt s.Δ := by
    intro r r' s s' ⟨z, hz, hz'⟩
    have hop : IsOpen (discInt s.Δ) := s.full.disc.isOpen_discInt hman
    refine s'.full.disc.isPreconnected_discInt.subset_left_of_subset_union hop
      s.full.disc.isClosed.isOpen_compl
      (disjoint_left.mpr fun a ha hb ↦ hb ha.1) (fun a ha ↦ ?_) ⟨z, hz', hz⟩
    by_cases h' : a ∈ s.Δ
    · exact .inl ⟨h', fun hb ↦ disjoint_left.mp (hside s s') hb ha⟩
    · exact .inr h'
  refine disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp fun hm ↦ ?_)
  have h₁ := hsub s s' hm
  have h₂ := hsub s' s (by rwa [Set.inter_comm])
  have heq : s.Δ = s'.Δ := by
    rw [← closure_discInt s.full.disc, ← closure_discInt s'.full.disc, subset_antisymm h₁ h₂]
  have hrG := s.full.r_mem
  have hrb : r ∈ discBd s'.Δ := by
    rw [← heq, s.full.bd_eq]
    have hm : r ∈ closure s.f₁ ∩ D.rad.G.V := by
      rw [s.full.link₁.2.2.2]
      exact .inl rfl
    exact .inl (.inl hm.1)
  rw [s'.full.bd_eq] at hrb
  have hrne : ∀ {f : Set Shat} {v : Shat}, D.rad.G.toGraph.IsLink f r' v → r ∉ closure f
    := fun {f v} hl hrf ↦ by
    have hm : r ∈ closure f ∩ D.rad.G.V := ⟨hrf, hrG.1.1⟩
    rw [hl.2.2.2] at hm
    rcases hm with rfl | hm
    · exact hne rfl
    · have hv := D.hatV_of_link s'.full.r_mem.1 hl
      exact hrG.1.2 (mem_singleton_iff.mp hm ▸ hv)
  rcases hrb with (hrb | hrb) | hrb
  · exact hrne s'.full.link₁ hrb
  · exact hrne s'.full.link₂ hrb
  · rcases s'.full.Z_sub hrb with (h' | h') | h'
    · exact notMem_spoke_of_Rstar hW hbdS hin hrG (sp.spoke s'.v₁) (support_of_mem_U _ h' hrG.1.1)
    · exact notMem_spoke_of_Rstar hW hbdS hin hrG (sp.spoke s'.v₂) (support_of_mem_U _ h' hrG.1.1)
    · exact (hW.H_in_int h').2 hrG.2

end TangleDatum

end GraphMinor.GM19
