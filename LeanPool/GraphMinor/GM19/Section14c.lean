/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section14b

/-!
# Graph Minors XIX, Section 14: spokes and the hub stay out of a sector
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology Metric GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

namespace TangleDatum

variable {D : TangleDatum cap χ} {W : Set Shat} {H : Drawing Shat} {ρ : ℕ} {r : Shat} {f₁ f₂ : Set
  Shat} {v₁ v₂ h₁ h₂ : Shat}
  {K₁ : GraphWalk D.rad.G.toGraph v₁ h₁} {K₂ : GraphWalk D.rad.G.toGraph v₂ h₂} {Z : GraphWalk
    D.rad.G.toGraph v₁ v₂}
  {Δ Δ' : Set Shat} {C : Drawing Shat}

omit [T2Space Shat] in
/-- A point of the inside of a disc in `W` is off `bd(W)`. -/
theorem discInt_off_bd {Δ W : Set Shat} (hT : IsClosedSurface Shat) (hW : IsClosedDisc W)
  (hΔ : IsClosedDisc Δ) (hΔW : Δ ⊆ W) {x : Shat} (hx : x ∈ discInt Δ) :
    x ∉ discBd W := by
  have hop : IsOpen (discInt Δ) := hΔ.isOpen_discInt (IsClosedSurface.isSurface hT).2.2
  have hi : x ∈ interior W := interior_mono ((discInt_subset Δ).trans hΔW)
    (mem_interior_iff_mem_nhds.mpr (hop.mem_nhds hx))
  intro hb
  have hf : x ∈ frontier W := by
    rw [IsClosedDisc.frontier_eq_discBd hT hW]
    exact hb
  exact hf.2 hi

/-- A spoke that meets the sector at a vertex of `U(C)` stays on `U(C)` from there, when `Z` goes
through a path of the hub. -/
theorem spoke_off_hub_sector (hW : D.IsWheelHubOfRadius W H ρ) (hbdS : discBd W ⊆ cap.emb ''
  (univ \ bd S)) (hin : ((W \ discBd W) ∩ (cap.emb '' D.Γ.V)).Nonempty)
    (h1 : D.IsSpokeWalk W H K₁) (h2 : D.IsSpokeWalk W H K₂) {P : Drawing Shat}
      (hP : Drawing.IsPathOf P H h₁ h₂)
    (hU : (walkDrawing D.rad.G Z).U = (walkDrawing D.rad.G K₁).U ∪ (walkDrawing D.rad.G K₂).U ∪
      P.U) (hs : D.IsSector W r f₁ f₂ Z Δ Δ' C)
    (hb : D.IsBoundarySector W H r Δ C) {v h : Shat} {K : GraphWalk D.rad.G.toGraph v h}
      (hK : D.IsSpokeWalk W H K) :
    Disjoint (walkDrawing D.rad.G K).U (discInt Δ) := by
  classical
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  obtain ⟨hle, hins⟩ := theorem_13_5_proof hW hbdS hin hb
  have hrep := hW.rep_ge
  have hlt : C.E.ncard < 2 * D.rep := by omega
  have hc := hs.circuit
  have hΔW : Δ ⊆ W := hs.union ▸ subset_union_left
  have hUΔ : ∀ {y}, y ∈ (walkDrawing D.rad.G Z).U → y ∈ C.U := fun hy ↦ hs.C_U ▸ hs.bd_eq ▸ Or.inr
    hy
  have hout : v ∉ D.ins C \ C.U := by
    intro h'
    apply discInt_off_bd hT hW.is_disc hs.disc hΔW (x := v) ?_ hK.2.v_mem.2
    rw [hins, hs.C_U] at h'
    exact h'
  refine disjoint_left.mpr fun p hpK hpi ↦ hpi.2 ?_
  rw [← hs.C_U]
  have hpins : p ∈ D.ins C := hins ▸ hpi.1
  by_cases hm : ∃ x ∈ K.support, x ∈ C.V
  swap
  · push Not at hm
    exact D.part_outside hc hlt K hK.1 hout (fun y hy hyC ↦ absurd hyC (hm y hy)) hpK hpins
  obtain ⟨a, haC, L, R, rfl, hfirst⟩ := GraphWalk.exists_first_mem K hm
  have hLs : L.IsSimple := (GraphWalk.IsSimple.of_append hK.1).1
  have hRs : R.IsSimple := (GraphWalk.IsSimple.of_append hK.1).2
  have haL : a ∈ (L.append R).support := (GraphWalk.mem_support_append L R).mpr
    (.inl L.end_mem_support)
  have haG : a ∈ D.rad.G.V := hc.1.1 haC
  -- The vertex `a` is on one of the two spokes or on the hub.
  have hcase : a ∈ K₁.support ∨ a ∈ K₂.support ∨ a ∈ H.V := by
    have haU : a ∈ discBd Δ := hs.C_U ▸ C.V_subset_U haC
    rw [hs.bd_eq, hU] at haU
    rcases haU with (ha | ha) | ((ha | ha) | ha)
    · have hmem : a ∈ closure f₁ ∩ D.rad.G.V := ⟨ha, haG⟩
      rw [hs.link₁.2.2.2] at hmem
      rcases hmem with rfl | hmem
      · exact absurd haL (notMem_spoke_of_Rstar hW hbdS hin hs.r_mem hK)
      · exact .inl (mem_singleton_iff.mp hmem ▸ K₁.start_mem_support)
    · have hmem : a ∈ closure f₂ ∩ D.rad.G.V := ⟨ha, haG⟩
      rw [hs.link₂.2.2.2] at hmem
      rcases hmem with rfl | hmem
      · exact absurd haL (notMem_spoke_of_Rstar hW hbdS hin hs.r_mem hK)
      · exact .inr (.inl (mem_singleton_iff.mp hmem ▸ K₂.start_mem_support))
    · exact .inl (support_of_mem_U K₁ ha haG)
    · exact .inr (.inl (support_of_mem_U K₂ ha haG))
    · exact .inr (.inr (mem_V_of_mem_U hW.H_sub (hP.1.U_subset ha) haG))
  have hRC : (walkDrawing D.rad.G R).U ⊆ C.U := by
    rcases hcase with ha | ha | ha
    · obtain rfl := hK.same_end h1 haL ha
      obtain ⟨Y, X, rfl⟩ := K₁.exists_append_of_mem ha
      obtain rfl := hK.tail_after h1
      exact fun y hy ↦ hUΔ (hU ▸ .inl (.inl (walkU_right_subset Y R hy)))
    · obtain rfl := hK.same_end h2 haL ha
      obtain ⟨Y, X, rfl⟩ := K₂.exists_append_of_mem ha
      obtain rfl := hK.tail_after h2
      exact fun y hy ↦ hUΔ (hU ▸ .inl (.inr (walkU_right_subset Y R hy)))
    · obtain rfl : a = h := hK.support_hub haL ha
      have hlen : R.length = 0 := hRs.length_eq_zero
      intro y hy
      cases R with
      | nil _ =>
        rcases (mem_walkDrawing_U _ _).mp hy with hy | ⟨e, he, -⟩
        · rw [show y = a by simpa [GraphWalk.support] using hy]
          exact C.V_subset_U haC
        · simp [GraphWalk.edges] at he
      | cons _ _ => simp [GraphWalk.length_cons] at hlen
  rw [walkU_append] at hpK
  rcases hpK with hp | hp
  · exact D.part_outside hc hlt L hLs hout hfirst hp hpins
  · exact hRC hp

/-- A sector with all that we need of it. -/
structure IsFullSector (D : TangleDatum cap χ) (W : Set Shat) (H : Drawing Shat) (r : Shat)
  (f₁ f₂ : Set Shat) (K₁ : GraphWalk D.rad.G.toGraph v₁ h₁)
    (K₂ : GraphWalk D.rad.G.toGraph v₂ h₂) (Z : GraphWalk D.rad.G.toGraph v₁ v₂) (Δ Δ' : Set Shat)
      (C : Drawing Shat) : Prop extends
    D.IsSector W r f₁ f₂ Z Δ Δ' C where
  boundary : D.IsBoundarySector W H r Δ C
  spoke_off : ∀ (v h : Shat) (K : GraphWalk D.rad.G.toGraph v h), D.IsSpokeWalk W H K → Disjoint
    (walkDrawing D.rad.G K).U (discInt Δ)
  hub_off : Disjoint H.U (discInt Δ)
  Z_sub : (walkDrawing D.rad.G Z).U ⊆ (walkDrawing D.rad.G K₁).U ∪ (walkDrawing D.rad.G K₂).U ∪ H.U
  Z_cover : (walkDrawing D.rad.G K₁).U ∪ (walkDrawing D.rad.G K₂).U ⊆ (walkDrawing D.rad.G Z).U ∪
    ((walkDrawing D.rad.G K₁).U ∩ (walkDrawing D.rad.G K₂).U)
  Z_same : h₁ = h₂ → (walkDrawing D.rad.G Z).U ⊆ (walkDrawing D.rad.G K₁).U ∪
    (walkDrawing D.rad.G K₂).U
  Z_fan : (∃ x ∈ K₁.support, x ∈ K₂.support) → ∃ (u : Shat) (A₁ : GraphWalk D.rad.G.toGraph v₁ u)
    (A₂ : GraphWalk D.rad.G.toGraph v₂ u) (T₁ : GraphWalk D.rad.G.toGraph u h₁)
    (T₂ : GraphWalk D.rad.G.toGraph u h₂), K₁ = A₁.append T₁ ∧ K₂ = A₂.append T₂ ∧ HEq T₁ T₂ ∧
      (∀ y ∈ A₁.support, y ∈ A₂.support → y = u) ∧
      (walkDrawing D.rad.G Z).U = (walkDrawing D.rad.G A₁).U ∪ (walkDrawing D.rad.G A₂).U

/-- **The sector at `r`**, for either kind of pair of spokes. The paper takes the existence of `Δ_v`
as seen. -/
theorem exists_fullSector (hopt : D.IsOptimalWheelHub W H ρ) (hbdS : discBd W ⊆ cap.emb ''
  (univ \ bd S)) (hin : ((W \ discBd W) ∩ (cap.emb '' D.Γ.V)).Nonempty)
    (h1 : D.IsSpokeWalk W H K₁) (h2 : D.IsSpokeWalk W H K₂) (hr : r ∈ D.rad.Rstar ∩ discBd W)
    (hl₁ : D.rad.G.toGraph.IsLink f₁ r v₁) (hl₂ : D.rad.G.toGraph.IsLink f₂ r v₂) (hne : v₁ ≠ v₂)
      (hf₁ : f₁ ⊆ discBd W) (hf₂ : f₂ ⊆ discBd W) :
    ∃ Z Δ Δ' C, D.IsFullSector W H r f₁ f₂ K₁ K₂ Z Δ Δ' C := by
  classical
  have hW := hopt.toIsWheelHubOfRadius
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  by_cases hd : ∀ x ∈ K₁.support, x ∉ K₂.support
  · obtain ⟨P, Z, Δ, Δ', C, hP, hU, hs, hb⟩ := exists_hub_sector hW hbdS hin h1 h2 hd hr hl₁ hl₂
      hne hf₁ hf₂
    have hspoke : ∀ (v h : Shat) (K : GraphWalk D.rad.G.toGraph v h), D.IsSpokeWalk W H K
      → Disjoint (walkDrawing D.rad.G K).U (discInt Δ) :=
      fun v h K hK ↦ spoke_off_hub_sector hW hbdS hin h1 h2 hP hU hs hb hK
    have hhne : h₁ ≠ h₂ := by
      rintro rfl
      exact hd h₁ K₁.end_mem_support K₂.end_mem_support
    obtain ⟨hH, hle⟩ : IsEnclave D.tb D.ord D.𝒯 H ∧ H.E.ncard ≤ 4 * ρ + 4 := by
      rcases hW.hub_cond with ⟨hc, -, -⟩ | ⟨hH, hle, -⟩
      · obtain ⟨z, hz⟩ := ncard_eq_one.mp hc
        exact absurd ((hz ▸ h1.2.h_mem : h₁ ∈ ({z} : Set Shat)).trans (hz ▸ h2.2.h_mem : h₂ ∈
          ({z} : Set Shat)).symm) hhne
      · exact ⟨hH, hle⟩
    obtain ⟨-, -, -, hc, hlt, -⟩ := id hH
    have hrep := hW.rep_ge
    have hi := D.ins_spec hc (by omega)
    have hoff := hb.interior_off_hub hopt hbdS hin hH hle
    refine ⟨Z, Δ, Δ', C, { hs with
      boundary := hb
      spoke_off := hspoke
      hub_off := ?_
      Z_sub := ?_
      Z_cover := ?_
      Z_same := fun e ↦ absurd e hhne
      Z_fan := fun ⟨x, hx₁, hx₂⟩ ↦ absurd hx₂ (hd x hx₁) }⟩
    · refine disjoint_left.mpr fun y hy hyi ↦ ?_
      have hyc : y ∈ closure (discInt (D.ins H)) := by
        rw [closure_discInt hi.2.2.1]
        exact Surface.discBd_subset _ (hi.2.2.2.1 ▸ hy)
      obtain ⟨z, hz₁, hz₂⟩ := mem_closure_iff.mp hyc _ (hs.disc.isOpen_discInt
        (IsClosedSurface.isSurface hT).2.2) hyi
      exact disjoint_left.mp hoff hz₂ hz₁
    · rw [hU]
      exact fun y hy ↦ hy.imp_right fun h' ↦ hP.1.U_subset h'
    · rw [hU]
      exact fun y hy ↦ .inl (.inl hy)
  · push Not at hd
    obtain ⟨x, hx₁, hx₂⟩ := hd
    obtain rfl := h1.same_end h2 hx₁ hx₂
    obtain ⟨u, A₁, A₂, T, rfl, rfl, -, hmeet⟩ := h1.merge h2 hx₁ hx₂
    have hfan : D.IsFan W H ρ r f₁ f₂ A₁ A₂ T := by
      refine ⟨hW, hbdS, hin, hr.1, hr.2, hne, hl₁, hl₂, h1, h2, fun y h₁ h₂ ↦ hmeet y h₁ ?_⟩
      exact (GraphWalk.mem_support_append A₂ T).mpr (.inl h₂)
    obtain ⟨Δ, Δ', C, hs, hb⟩ := hfan.exists_sector hf₁ hf₂
    obtain ⟨C', hC'⟩ := hfan.exists_circuit
    have hbd' : discBd Δ = C'.U := by
      rw [hs.bd_eq, hfan.U_eq hC', walkU_append, walkU_reverse]
      ext x
      simp only [mem_union]
      tauto
    have hΔW : Δ ⊆ W := hs.union ▸ subset_union_left
    obtain ⟨hfirst, hsecond⟩ := hfan.main hC' hopt hs.disc hΔW hbd'
    refine ⟨_, Δ, Δ', C, { hs with
      boundary := hb
      spoke_off := ?_
      hub_off := ?_
      Z_sub := ?_
      Z_cover := ?_
      Z_same := ?_
      Z_fan := fun _ ↦ ⟨u, A₁, A₂, T, T, rfl, rfl, HEq.rfl, hfan.meet, by
        rw [walkU_append, walkU_reverse]⟩ }⟩
    · exact fun v h K hK ↦ disjoint_left.mpr fun y hy hyi ↦ hyi.2 (hsecond v h K hK ⟨hyi.1, hy⟩)
    · refine disjoint_left.mpr fun y hy hyi ↦ hyi.2 ?_
      rw [hfirst y ⟨hyi.1, hy⟩, hbd']
      exact C'.V_subset_U ((hC'.mem_V u).mpr (.inr (.inl A₁.end_mem_support)))
    · rw [walkU_append, walkU_reverse]
      rintro y (hy | hy)
      · exact .inl (.inl (walkU_left_subset A₁ T hy))
      · exact .inl (.inr (walkU_left_subset A₂ T hy))
    · rw [walkU_append A₁ A₂.reverse, walkU_reverse]
      rintro y (hy | hy)
      · rw [walkU_append] at hy
        rcases hy with hy | hy
        · exact .inl (.inl hy)
        · exact .inr ⟨walkU_right_subset A₁ T hy, walkU_right_subset A₂ T hy⟩
      · rw [walkU_append] at hy
        rcases hy with hy | hy
        · exact .inl (.inr hy)
        · exact .inr ⟨walkU_right_subset A₁ T hy, walkU_right_subset A₂ T hy⟩
    · intro _
      rw [walkU_append, walkU_reverse]
      rintro y (hy | hy)
      · exact .inl (walkU_left_subset A₁ T hy)
      · exact .inr (walkU_left_subset A₂ T hy)

end TangleDatum

end GraphMinor.GM19
