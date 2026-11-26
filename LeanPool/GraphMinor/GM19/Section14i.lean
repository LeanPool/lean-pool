/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section14h

import LeanPool.GraphMinor.GM07.Bridge

/-!
# Graph Minors XIX, Section 14: the location of a wheel cover

The arms of all wheels of a cover form a rooted location, and it isolates `𝒯`. This is the claim (2)
in the proof of (14.1).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

namespace TangleDatum

variable {D : TangleDatum cap χ} {W : Set Shat}

/-- An arm of a wheel is the arm of a disc in `W`, whose inside misses all else that is not in that
disc. -/
structure IsDiscArm (fr : WheelFrame D W) (A : Arm D.Γ) (Δ X : Set Shat) : Prop where
  disc : IsClosedDisc Δ
  sub : Δ ∪ X ⊆ W
  minus : A.minus = D.partPlus Δ X
  compl : A.compl = partIn cap D.Γ (closure Δᶜ)

omit [T2Space S] [T2Space Shat] in
theorem mem_walkMarch {a b : Shat} {K : GraphWalk D.rad.G.toGraph a b} {x : S} : x ∈ D.walkMarch K
  ↔ x ∈ D.Γ.V ∧ cap.emb x ∈ K.support := by
  classical
  simp only [walkMarch, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨y, ⟨hy, z, hz, rfl⟩, rfl⟩
    rw [D.pre_emb]
    exact ⟨hz, hy⟩
  · rintro ⟨hx, hK⟩
    exact ⟨cap.emb x, ⟨hK, x, hx, rfl⟩, D.pre_emb x⟩

omit [T2Space S] in
omit [T2Space Shat] in
theorem walkMarch_length_le {a b : Shat} (K : GraphWalk D.rad.G.toGraph a b) :
  (D.walkMarch K).length ≤ K.length + 1 := by
  classical
  simp only [walkMarch, List.length_map]
  refine (List.length_filter_le _ _).trans ?_
  rw [GraphWalk.length_support']

omit [T2Space S] in
/-- `|V(Γ) ∩ (U(K) ∪ U(K'))|` is at most the sum of the two lengths. -/
theorem ncard_le_of_two_walks {a b a' b' : Shat} (K : GraphWalk D.rad.G.toGraph a b)
  (K' : GraphWalk D.rad.G.toGraph a' b') {T : Set S}
    (hT : ∀ v ∈ T, v ∈ D.Γ.V ∧ cap.emb v ∈ (walkDrawing D.rad.G K).U ∪
      (walkDrawing D.rad.G K').U) : T.ncard ≤ K.length + K'.length + 2 := by
  classical
  have hsub : T ⊆ ↑((D.walkMarch K ++ D.walkMarch K').toFinset) := by
    intro v hv
    obtain ⟨hV, hU⟩ := hT v hv
    have hG : cap.emb v ∈ D.rad.G.V := D.rad.isPreRadial.2.1 ⟨v, hV, rfl⟩
    simp only [Finset.mem_coe, List.mem_toFinset, List.mem_append]
    rcases hU with hU | hU
    · exact .inl (mem_walkMarch.mpr ⟨hV, support_of_mem_U K hU hG⟩)
    · exact .inr (mem_walkMarch.mpr ⟨hV, support_of_mem_U K' hU hG⟩)
  refine (ncard_le_ncard hsub (Finset.finite_toSet _)).trans ?_
  rw [ncard_coe_finset]
  refine (List.toFinset_card_le _).trans ?_
  rw [List.length_append]
  have h₁ := walkMarch_length_le (D := D) K
  have h₂ := walkMarch_length_le (D := D) K'
  omega

namespace WheelFrame

variable (fr : WheelFrame D W)

theorem spoke_subset (i : ℕ) : (walkDrawing D.rad.G (fr.R.spoke fr.sp i)).U ⊆ W :=
  (fr.spoke_spoke i).subset_W fr.hW fr.hbdS fr.hin

theorem sec_Δ_sub (i : ℕ) : (fr.sec i).Δ ⊆ W := (fr.sec i).toSectorAt.Δ_subset

theorem secArm_disc (i : ℕ) : IsDiscArm fr (fr.secArm i) (fr.sec i).Δ (fr.secX i) :=
  ⟨(fr.sec i).full.disc, union_subset (fr.sec_Δ_sub i) fun _ h ↦ fr.spoke_subset i h.1.2, rfl, rfl⟩

theorem hubArm_disc (hc : fr.H.V.ncard ≠ 1) : IsDiscArm fr (fr.hubArm hc) (D.ins fr.H) ∅ := by
  obtain ⟨hH, hle, hi⟩ := fr.hub_data hc
  have hsub := (fr.hW.hubSet_facts).2.1
  rcases fr.hW.hub_cases with ⟨z, hV, -, -⟩ | ⟨-, -, -, hh⟩
  · rw [hV, ncard_singleton] at hc
    exact absurd rfl hc
  · rw [hh] at hsub
    exact ⟨hi.2.2.1, by simpa using hsub, rfl, rfl⟩

/-- The set in an arm misses the inside of each other arm of the wheel: first for two sectors. -/
theorem sec_off_sec {i j : ℕ} (hne : fr.R.reg i ≠ fr.R.reg j) : Disjoint ((fr.sec i).Δ ∪ fr.secX i)
  (discInt (fr.sec j).Δ) := by
  refine disjoint_left.mpr fun y hy hyi ↦ ?_
  rcases hy with hy | hy
  · by_cases hb : y ∈ discBd (fr.sec i).Δ
    · exact disjoint_left.mp (SectorAt.bd_off fr.hW (fr.sec i).toSectorAt
        (fr.sec j).toSectorAt) hb hyi
    · exact disjoint_left.mp (fr.disjoint_int hne) ⟨hy, hb⟩ hyi
  · exact disjoint_left.mp ((fr.sec j).full.spoke_off _ _ _ (fr.spoke_spoke i)) hy.1.2 hyi

theorem sec_off_hub (hc : fr.H.V.ncard ≠ 1) (i : ℕ) : Disjoint ((fr.sec i).Δ ∪ fr.secX i) (discInt
  (D.ins fr.H)) := by
  have hT := cap.isClosedSurface
  obtain ⟨hH, hle, hi⟩ := fr.hub_data hc
  have hbd := hi.2.2.2.1
  have hcl : IsClosed (discBd W) := by
    rw [← IsClosedDisc.frontier_eq_discBd hT fr.hW.is_disc]
    exact isClosed_frontier
  have hsp : ∀ {j}, Disjoint (walkDrawing D.rad.G (fr.R.spoke fr.sp j)).U (discInt (D.ins fr.H))
    := fun {j} ↦
    disjoint_left.mpr fun y hy hyi ↦ disjoint_left.mp ((fr.spoke_spoke j).off_ins_hub fr.hW hH hle)
      hy ⟨hyi.1, fun h' ↦ hyi.2 (hbd ▸ h')⟩
  have hoff := (fr.sec i).full.boundary.interior_off_hub fr.hopt fr.hbdS fr.hin hH hle
  refine disjoint_left.mpr fun y hy hyi ↦ ?_
  rcases hy with hy | hy
  · by_cases hb : y ∈ discBd (fr.sec i).Δ
    · rw [(fr.sec i).full.bd_eq] at hb
      rcases hb with hb | hb
      · refine disjoint_left.mp (fr.hW.ins_off_bd hi.1 hle) hyi.1 ?_
        exact (union_subset (closure_minimal (fr.sec i).full.f₁_bd hcl) (closure_minimal
          (fr.sec i).full.f₂_bd hcl)) hb
      · rcases (fr.sec i).full.Z_sub hb with (h' | h') | h'
        · exact disjoint_left.mp hsp h' hyi
        · exact disjoint_left.mp hsp h' hyi
        · exact hyi.2 (hbd ▸ h')
    · exact disjoint_left.mp hoff hyi ⟨hy, hb⟩
  · exact disjoint_left.mp hsp hy.1.2 hyi

theorem hub_off_sec (hc : fr.H.V.ncard ≠ 1) (i : ℕ) : Disjoint (D.ins fr.H ∪ ∅) (discInt
  (fr.sec i).Δ) := by
  have hT := cap.isClosedSurface
  obtain ⟨hH, hle, hi⟩ := fr.hub_data hc
  have hoff := (fr.sec i).full.boundary.interior_off_hub fr.hopt fr.hbdS fr.hin hH hle
  rw [union_empty]
  refine disjoint_left.mpr fun y hy hyi ↦ ?_
  by_cases hb : y ∈ discBd (D.ins fr.H)
  · exact disjoint_left.mp (fr.sec i).full.hub_off (hi.2.2.2.1 ▸ hb) hyi
  · exact disjoint_left.mp hoff ⟨hy, hb⟩ hyi

omit [T2Space S] [T2Space Shat] in
/-- A hat vertex on the closure of an edge at `r` is the other end. -/
theorem hat_on_edge {r v x : Shat} {f : Set Shat} (hr : r ∈ D.rad.Rstar)
  (hl : D.rad.G.toGraph.IsLink f r v) (hx : x ∈ closure f) (hxV : x ∈ cap.emb '' D.Γ.V) : x = v
    := by
  have hm : x ∈ closure f ∩ D.rad.G.V := ⟨hx, D.rad.isPreRadial.2.1 hxV⟩
  rw [hl.2.2.2] at hm
  rcases hm with rfl | hm
  · exact absurd hxV hr.2
  · exact hm

/-- The vertices of the `r*`-sector on the boundary are on the two spokes, or `H` has a path in it.
-/
theorem sec_order_le (i : ℕ) : (fr.secArm i).order ≤ 2 * fr.ρ + 2 := by
  classical
  have : ConnectedSpace Shat := cap.connected
  have hS := χ.isSurface
  have h3 := D.P.fits.internally_three_connected
  have hs := (fr.sec i).full
  have hb := hs.boundary
  have h5 := theorem_13_5_proof fr.hW fr.hbdS fr.hin hb
  by_cases he : fr.R.inner fr.sp i = fr.R.inner fr.sp (i + 1)
  · have hT : ∀ v ∈ (D.partPlus (fr.sec i).Δ (fr.secX i) ∩ partIn cap D.Γ (closure
      (fr.sec i).Δᶜ)).vertexSet,
        v ∈ D.Γ.V ∧ cap.emb v ∈ (walkDrawing D.rad.G (fr.R.spoke fr.sp i)).U ∪ (walkDrawing D.rad.G
          (fr.R.spoke fr.sp (i + 1))).U := by
      intro v hv
      obtain ⟨hV, hU⟩ := (plus_inter_V hs.disc (fr.secX_off i)).mp hv
      refine ⟨hV, ?_⟩
      have hem : cap.emb v ∈ cap.emb '' D.Γ.V := ⟨v, hV, rfl⟩
      rcases hU with hU | hU
      · rw [hs.bd_eq] at hU
        rcases hU with (hU | hU) | hU
        · rw [hat_on_edge hs.r_mem.1 hs.link₁ hU hem]
          exact .inl ((mem_walkDrawing_U _ _).mpr (.inl (fr.R.spoke fr.sp i).start_mem_support))
        · rw [hat_on_edge hs.r_mem.1 hs.link₂ hU hem]
          exact .inr ((mem_walkDrawing_U _ _).mpr (.inl (fr.R.spoke fr.sp
            (i + 1)).start_mem_support))
        · exact hs.Z_same he hU
      · exact .inl hU.1.2
    have h := ncard_le_of_two_walks _ _ hT
    have h₁ := (fr.hW.spoke_length (fr.spoke_spoke i)).1
    have h₂ := (fr.hW.spoke_length (fr.spoke_spoke (i + 1))).1
    change Hypergraph.separationOrder _ _ ≤ _
    simp only [Hypergraph.separationOrder]
    refine h.trans ?_
    omega
  · have hX : fr.secX i = ∅ := by
      refine eq_empty_of_forall_notMem fun y hy ↦ he ?_
      have hG : y ∈ D.rad.G.V := D.rad.isPreRadial.2.1 hy.1.1
      exact fr.R.inner_eq_of_mem fr.sp (support_of_mem_U _ hy.1.2 hG)
        (support_of_mem_U _ hy.2 hG)
    have hord := disc_order hS h3 D.rad hb.Dv_circuit hb.is_disc hb.Dv_U.symm
    have hE := h5.1
    change Hypergraph.separationOrder (D.partPlus (fr.sec i).Δ (fr.secX i)) _ ≤ _
    rw [hX]
    have hp : D.partPlus (fr.sec i).Δ ∅ = partIn cap D.Γ (fr.sec i).Δ := by
      simp [partPlus, partIn]
    rw [hp]
    have hq : Hypergraph.separationOrder (partIn cap D.P.Γ (fr.sec i).Δ)
      (partIn cap D.P.Γ (closure (fr.sec i).Δᶜ)) ≤ 2 * fr.ρ + 2 := by omega
    exact hq

theorem hub_order_le (hc : fr.H.V.ncard ≠ 1) : (fr.hubArm hc).order ≤ 2 * fr.ρ + 2 := by
  have : ConnectedSpace Shat := cap.connected
  obtain ⟨hH, hle, hi⟩ := fr.hub_data hc
  have hord := disc_order χ.isSurface D.P.fits.internally_three_connected D.rad hi.1 hi.2.2.1
    hi.2.2.2.1
  change Hypergraph.separationOrder (D.partPlus (D.ins fr.H) ∅) _ ≤ _
  have hp : D.partPlus (D.ins fr.H) ∅ = partIn cap D.Γ (D.ins fr.H) := by
    simp [partPlus, partIn]
  rw [hp]
  have hq : Hypergraph.separationOrder (partIn cap D.P.Γ (D.ins fr.H))
      (partIn cap D.P.Γ (closure (D.ins fr.H)ᶜ)) ≤ 2 * fr.ρ + 2 := by omega
  exact hq

/-- The enclaves of the distinctions fall in the sector. -/
theorem sec_ins (i : ℕ) : IsInsOf D.rad D.ord D.𝒯 (fr.sec i).C (fr.sec i).Δ ∧ (fr.sec i).C.E.ncard
  ≤ 4 * fr.ρ + 4 ∧
    ∀ {ord' 𝒯' F'}, IsEnclaveAround D.tb D.ord ord' D.𝒯 𝒯' F' → (partIn cap D.Γ (closure
      (fr.sec i).Δᶜ), partIn cap D.Γ (fr.sec i).Δ) ∈ 𝒯' → D.ins F' ⊆ (fr.sec i).Δ := by
  have hb := (fr.sec i).full.boundary
  have h5 := theorem_13_5_proof fr.hW fr.hbdS fr.hin hb
  have hrep := fr.hrep
  have hi := D.ins_spec hb.Dv_circuit (by omega)
  rw [h5.2] at hi
  refine ⟨hi, h5.1, fun he hm ↦ ?_⟩
  exact theorem_13_6_proof ⟨fr.hopt, fr.hbdS, fr.hin, hrep, hb, hm, he⟩

theorem hub_ins (hc : fr.H.V.ncard ≠ 1) {ord' : ℕ} {𝒯' : Set (Hypergraph S (Set S) × Hypergraph S
  (Set S))} {F' : Drawing Shat} (he : IsEnclaveAround D.tb D.ord ord' D.𝒯 𝒯' F')
    (hle : F'.E.ncard ≤ fr.H.E.ncard) (hm : (partIn cap D.Γ (closure (D.ins fr.H)ᶜ), partIn cap D.Γ
      (D.ins fr.H)) ∈ 𝒯') : D.ins F' ⊆ D.ins fr.H := by
  have : ConnectedSpace Shat := cap.connected
  have hS := χ.isSurface
  have h3 := D.P.fits.internally_three_connected
  obtain ⟨hH, hHle, hi⟩ := fr.hub_data hc
  obtain ⟨ord₂, 𝒯₂, h𝒯₂, hcH, hlt₂, Δ₂, hins₂, hd₂⟩ := id hH
  obtain ⟨h𝒯', hc', hlt', Δ', hins', hd'⟩ := id he
  obtain rfl := D.eq_ins_of_isInsOf hins₂
  obtain rfl := D.eq_ins_of_isInsOf hins'
  rcases theorem_8_6_proof hS h3 D.tb D.isTangle h𝒯' h𝒯₂ hins' hins₂ hd' hd₂ with h₁ | h₁ | h₁
  · exact h₁
  · by_cases hF : F' = fr.H
    · rw [hF]
    · rcases fr.hW.hub_cond with ⟨hcard, -, -⟩ | ⟨-, -, hne⟩
      · exact absurd hcard hc
      · exact absurd ((hi.2.2.2.1 ▸ Surface.discBd_subset _ : fr.H.U ⊆ D.ins fr.H).trans h₁)
          (hne F' ⟨ord', 𝒯', he⟩ hF (by omega))
  · obtain ⟨c, hc₁, hc₂, hc₃⟩ := exists_edge_in_both hS h3 h𝒯' hins' hd'.1.2 hins₂ hm
    obtain ⟨p, hp⟩ := hc₁.1
    have hmem : cap.emb p ∈ D.ins F' ∩ D.ins fr.H := ⟨(hc₂ ⟨p, hp, rfl⟩).1, (hc₃ ⟨p, hp, rfl⟩).1⟩
    rw [h₁] at hmem
    exact absurd (hi.2.2.2.1 ▸ hmem.2 : cap.emb p ∈ discBd (D.ins fr.H)) (hc₃ ⟨p, hp, rfl⟩).2

end WheelFrame

/-- A separation of the form of an arm of a disc is in `𝒯`. -/
theorem IsDiscArm.sep_mem {fr : WheelFrame D W} {A : Arm D.Γ} {Δ X : Set Shat}
  (h : IsDiscArm fr A Δ X) {F : Drawing Shat} (hins : IsInsOf D.rad D.ord D.𝒯 F Δ)
    (hord : A.order < D.ord) : A.sep ∈ D.𝒯 := by
  have hs₀ := (disc_facts χ.isSurface D.P.fits.internally_three_connected D.rad hins.1 hins.2.2.1
    hins.2.2.2.1).1
  have hs := A.isSeparation
  change D.Γ.toHypergraph.IsSeparation A.minus A.compl at hs
  have hc : A.compl = partIn cap D.Γ (closure Δᶜ) := h.compl
  have : (A.minus, A.compl) ∈ D.𝒯 := by
    have hord' : Hypergraph.separationOrder A.minus A.compl < D.ord := hord
    rw [hc] at hs hord' ⊢
    exact plus_mem_of_mem D.isTangle hs hs₀ hord' hins.2.2.2.2
  exact this

theorem IsDiscArm.distinction {fr : WheelFrame D W} {A : Arm D.Γ} {Δ X : Set Shat}
  (h : IsDiscArm fr A Δ X) {F : Drawing Shat} (hins : IsInsOf D.rad D.ord D.𝒯 F Δ)
    {ord' : ℕ} {𝒯' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
      (h𝒯' : IsTangle D.Γ.toHypergraph ord' 𝒯') (hord : Hypergraph.separationOrder
        (partIn cap D.Γ Δ) (partIn cap D.Γ (closure Δᶜ)) < ord')
    (hm : A.sep.swap ∈ 𝒯') (hfin : ∀ {F'}, IsEnclaveAround D.tb D.ord ord' D.𝒯 𝒯' F' → F'.E.ncard
      ≤ F.E.ncard → (partIn cap D.Γ (closure Δᶜ), partIn cap D.Γ Δ) ∈ 𝒯' → D.ins F' ⊆ Δ)
    {C B : Hypergraph S (Set S)} (hd : IsDistinction D.tb.lambdaOrder D.𝒯 𝒯' C B) : C ≤ A.minus
      ∧ A.compl ≤ B := by
  have hs₀ := (disc_facts χ.isSurface D.P.fits.internally_three_connected D.rad hins.1 hins.2.2.1
    hins.2.2.2.1).1
  have hm' : (A.compl, A.minus) ∈ 𝒯' := hm
  rw [h.compl] at hm' ⊢
  have hm₀ := part_mem_of_plus_mem h𝒯' hs₀ hord hm'
  obtain ⟨F', he, hle, rfl, rfl⟩ := exists_enclave_of_distinction h𝒯' hins hm₀ hd
  rw [h.minus]
  exact le_of_ins_subset (hfin he hle hm₀)

theorem IsDiscArm.minus_le {fr : WheelFrame D W} {W' : Set Shat} {fr' : WheelFrame D W'} {A A' :
  Arm D.Γ} {Δ X Δ' X' : Set Shat} (h : IsDiscArm fr A Δ X) (h' : IsDiscArm fr' A' Δ' X')
    (hd : Disjoint (Δ ∪ X) (discInt Δ')) : A.minus ≤ A'.compl := by
  have : ConnectedSpace Shat := cap.connected
  rw [h.minus, h'.compl, closure_compl_disc cap.isClosedSurface h'.disc]
  exact part_mono fun y hy h'' ↦ disjoint_left.mp hd hy h''

theorem WheelFrame.exists_disc (fr : WheelFrame D W) {A : Arm D.Γ} (hA : A ∈ fr.arms) : ∃ Δ X,
  IsDiscArm fr A Δ X := by
  rcases hA with ⟨i, -, rfl⟩ | ⟨hc, rfl⟩
  · exact ⟨_, _, fr.secArm_disc i⟩
  · exact ⟨_, _, fr.hubArm_disc hc⟩

theorem WheelFrame.minus_le (fr : WheelFrame D W) {A A' : Arm D.Γ} (hA : A ∈ fr.arms)
  (hA' : A' ∈ fr.arms) (hne : A ≠ A') : A.minus ≤ A'.compl := by
  rcases hA with ⟨i, hi, rfl⟩ | ⟨hc, rfl⟩ <;> rcases hA' with ⟨j, hj, rfl⟩ | ⟨hc', rfl⟩
  · have hij : i ≠ j := fun e ↦ hne (by rw [e])
    have hr : fr.R.reg i ≠ fr.R.reg j := fun e ↦ hij (fr.R.reg_inj hi hj e)
    exact (fr.secArm_disc i).minus_le (fr.secArm_disc j) (fr.sec_off_sec hr)
  · exact (fr.secArm_disc i).minus_le (fr.hubArm_disc hc') (fr.sec_off_hub hc' i)
  · exact (fr.hubArm_disc hc).minus_le (fr.secArm_disc j) (fr.hub_off_sec hc j)
  · exact absurd rfl hne

/-- The rooted location of a wheel cover. -/
noncomputable def coverLoc (𝒲 : Set (Set Shat)) (hf : 𝒲.Finite) (hd : 𝒲.PairwiseDisjoint id)
  (fr : ∀ W : ↥𝒲, WheelFrame D W.1) : RootedLocation D.Γ where
  arms := ⋃ W, (fr W).arms
  finite_arms := by
    have := hf.to_subtype
    exact finite_iUnion fun W ↦ (fr W).arms_finite
  disjoint_arms := by
    intro A₁ h₁ A₂ h₂ hne
    obtain ⟨W₁, h₁⟩ := mem_iUnion.mp h₁
    obtain ⟨W₂, h₂⟩ := mem_iUnion.mp h₂
    by_cases he : W₁ = W₂
    · subst he
      exact (fr W₁).minus_le h₁ h₂ hne
    · obtain ⟨Δ, X, hc⟩ := (fr W₁).exists_disc h₁
      obtain ⟨Δ', X', hc'⟩ := (fr W₂).exists_disc h₂
      refine hc.minus_le hc' (disjoint_left.mpr fun y hy hy' ↦ ?_)
      have hdis := hd W₁.2 W₂.2 (fun e ↦ he (Subtype.ext e))
      exact disjoint_left.mp hdis (hc.sub hy) (hc'.sub (.inl hy'.1))

/-- **The claim (2) of the proof of (14.1).** -/
theorem coverLoc_isolates (𝒲 : Set (Set Shat)) (hf : 𝒲.Finite) (hd : 𝒲.PairwiseDisjoint id)
  (fr : ∀ W : ↥𝒲, WheelFrame D W.1) {θ : ℕ} (hθ : 0 < θ)
    (hord : ∀ W, 2 * (fr W).ρ + 2 < θ) (hle : θ ≤ D.ord)  : (coverLoc 𝒲 hf hd fr).Isolates D.tb θ
      D.ord D.𝒯 := by
  have : ConnectedSpace Shat := cap.connected
  have hS := χ.isSurface
  have h3 := D.P.fits.internally_three_connected
  have horder : ∀ A ∈ (coverLoc 𝒲 hf hd fr).arms, A.order < θ := by
    intro A hA
    obtain ⟨W, hW⟩ := mem_iUnion.mp hA
    have := hord W
    rcases hW with ⟨i, -, rfl⟩ | ⟨hc, rfl⟩
    · have := (fr W).sec_order_le i
      omega
    · have := (fr W).hub_order_le hc
      omega
  refine ⟨?_, ?_, hle, ?_⟩
  · rintro _ ⟨A, hA, rfl⟩
    obtain ⟨W, hW⟩ := mem_iUnion.mp hA
    have hlt := lt_of_lt_of_le (horder A hA) hle
    rcases hW with ⟨i, -, rfl⟩ | ⟨hc, rfl⟩
    · exact ((fr W).secArm_disc i).sep_mem ((fr W).sec_ins i).1 hlt
    · exact ((fr W).hubArm_disc hc).sep_mem ((fr W).hub_data hc).2.2 hlt
  · change sSup (Arm.order '' (coverLoc 𝒲 hf hd fr).arms) < θ
    by_cases hne : (Arm.order '' (coverLoc 𝒲 hf hd fr).arms).Nonempty
    · obtain ⟨A, hA, hm⟩ := hne.csSup_mem ((coverLoc 𝒲 hf hd fr).finite_arms.image _)
      rw [← hm]
      exact horder A hA
    · rw [not_nonempty_iff_eq_empty.mp hne]
      simpa using hθ
  · intro A hA ord' 𝒯' h𝒯' hθ' hm C B hdist
    obtain ⟨W, hW⟩ := mem_iUnion.mp hA
    have hρ := hord W
    rcases hW with ⟨i, -, rfl⟩ | ⟨hc, rfl⟩
    · obtain ⟨hi, hE, hfin⟩ := (fr W).sec_ins i
      have ho := disc_order hS h3 D.rad hi.1 hi.2.2.1 hi.2.2.2.1
      have hlt : Hypergraph.separationOrder (partIn cap D.Γ (fr W |>.sec i).Δ) (partIn cap D.Γ
        (closure (fr W |>.sec i).Δᶜ)) < ord' := by
        have hq : Hypergraph.separationOrder (partIn cap D.P.Γ (fr W |>.sec i).Δ)
          (partIn cap D.P.Γ (closure (fr W |>.sec i).Δᶜ)) < ord' := by omega
        exact hq
      exact ((fr W).secArm_disc i).distinction hi h𝒯' hlt hm (fun he _ hm' ↦ hfin he hm') hdist
    · obtain ⟨hH, hE, hi⟩ := (fr W).hub_data hc
      have ho := disc_order hS h3 D.rad hi.1 hi.2.2.1 hi.2.2.2.1
      have hlt : Hypergraph.separationOrder (partIn cap D.Γ (D.ins (fr W).H)) (partIn cap D.Γ
        (closure (D.ins (fr W).H)ᶜ)) < ord' := by
        have hq : Hypergraph.separationOrder (partIn cap D.P.Γ (D.ins (fr W).H))
          (partIn cap D.P.Γ (closure (D.ins (fr W).H)ᶜ)) < ord' := by omega
        exact hq
      exact ((fr W).hubArm_disc hc).distinction hi h𝒯' hlt hm (fun he hle' hm' ↦
        (fr W).hub_ins hc he hle' hm') hdist

end TangleDatum

end GraphMinor.GM19
