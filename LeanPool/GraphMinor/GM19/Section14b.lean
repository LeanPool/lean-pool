/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section14a

/-!
# Graph Minors XIX, Section 14: the sector at a vertex of `R* ∩ bd(W)`

The chord of the sector is the part of the two spokes that is not shared. When the two spokes do not
meet, it runs through a path of the hub.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology Metric GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

section Walks

variable {T : Type} [TopologicalSpace T] [T2Space T] {G : Drawing T} {a b c : T}

theorem walkU_append (A : GraphWalk G.toGraph a b) (B : GraphWalk G.toGraph b c) :
    (walkDrawing G (A.append B)).U = (walkDrawing G A).U ∪ (walkDrawing G B).U := by
  apply subset_antisymm
  · intro x hx
    rcases (mem_walkDrawing_U _ _).mp hx with h | ⟨e, he, hxe⟩
    · rcases (GraphWalk.mem_support_append A B).mp h with h | h
      · exact .inl ((mem_walkDrawing_U _ _).mpr (.inl h))
      · exact .inr ((mem_walkDrawing_U _ _).mpr (.inl h))
    · rw [GraphWalk.edges_append, List.mem_append] at he
      rcases he with h | h
      · exact .inl ((mem_walkDrawing_U _ _).mpr (.inr ⟨e, h, hxe⟩))
      · exact .inr ((mem_walkDrawing_U _ _).mpr (.inr ⟨e, h, hxe⟩))
  · exact union_subset (walkU_left_subset A B) (walkU_right_subset A B)

theorem walkU_reverse (A : GraphWalk G.toGraph a b) : (walkDrawing G A.reverse).U =
  (walkDrawing G A).U := by
  ext x
  simp [mem_walkDrawing_U, GraphWalk.support_reverse, GraphWalk.edges_reverse]

/-- The walk of the two edges at `r`. -/
def arcWalk {f₁ f₂ : Set T} {v₁ r v₂ : T} (h₁ : G.toGraph.IsLink f₁ r v₁)
  (h₂ : G.toGraph.IsLink f₂ r v₂) : GraphWalk G.toGraph v₁ v₂ :=
  .cons ⟨h₁.1, h₁.2.2.1, h₁.2.1, by rw [h₁.2.2.2, pair_comm]⟩ (.cons h₂ (.nil h₂.2.2.1))

theorem arcWalk_U {f₁ f₂ : Set T} {v₁ r v₂ : T} (h₁ : G.toGraph.IsLink f₁ r v₁)
  (h₂ : G.toGraph.IsLink f₂ r v₂) :
    (walkDrawing G (arcWalk h₁ h₂)).U = closure f₁ ∪ closure f₂ := by
  have hend : ∀ {f : Set T} {x y : T}, G.toGraph.IsLink f x y → x ∈ closure f ∧ y ∈ closure f
    := fun {f x y} h ↦ by
    have hc : closure f ∩ G.V = {x, y} := h.2.2.2
    exact ⟨(hc.symm ▸ (Or.inl rfl : x ∈ ({x, y} : Set T)) : x ∈ closure f ∩ G.V).1,
      (hc.symm ▸ (Or.inr rfl : y ∈ ({x, y} : Set T)) : y ∈ closure f ∩ G.V).1⟩
  ext x
  simp only [mem_walkDrawing_U, arcWalk,
    GraphWalk.support, GraphWalk.edges]
  simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, mem_union]
  constructor
  · rintro ((rfl | rfl | rfl) | h)
    · exact .inl (hend h₁).2
    · exact .inl (hend h₁).1
    · exact .inr (hend h₂).2
    · exact h
  · rintro (h | h)
    · exact .inr (.inl h)
    · exact .inr (.inr h)

end Walks

namespace TangleDatum

variable {D : TangleDatum cap χ} {W : Set Shat} {H : Drawing Shat} {ρ : ℕ} {r : Shat} {f₁ f₂ : Set
  Shat} {v₁ v₂ : Shat}

/-- The sector at `r`, with chord `Z`: `Δ` is bounded by the two edges at `r` and `Z`, and `Δ'` is
the rest of `W`. -/
structure IsSector (D : TangleDatum cap χ) (W : Set Shat) (r : Shat) (f₁ f₂ : Set Shat)
  (Z : GraphWalk D.rad.G.toGraph v₁ v₂)
    (Δ Δ' : Set Shat) (C : Drawing Shat) : Prop where
  r_mem : r ∈ D.rad.Rstar ∩ discBd W
  link₁ : D.rad.G.toGraph.IsLink f₁ r v₁
  link₂ : D.rad.G.toGraph.IsLink f₂ r v₂
  ne : v₁ ≠ v₂
  f₁_bd : f₁ ⊆ discBd W
  f₂_bd : f₂ ⊆ discBd W
  simple : Z.IsSimple
  disc : IsClosedDisc Δ
  disc' : IsClosedDisc Δ'
  union : Δ ∪ Δ' = W
  inter : Δ ∩ Δ' = (walkDrawing D.rad.G Z).U
  bd_eq : discBd Δ = (closure f₁ ∪ closure f₂) ∪ (walkDrawing D.rad.G Z).U
  bd_eq' : discBd Δ' = (discBd W \ ((closure f₁ ∪ closure f₂) \ {v₁, v₂})) ∪
    (walkDrawing D.rad.G Z).U
  circuit : C.IsCircuitOf D.rad.G
  C_U : C.U = discBd Δ

variable {Z : GraphWalk D.rad.G.toGraph v₁ v₂}

/-- A chord between the two neighbours of `r` gives a sector. -/
theorem exists_sector_of_chord (hW : IsClosedDisc W) (hG : discBd W ⊆ D.rad.G.U)
  (hr : r ∈ D.rad.Rstar ∩ discBd W) (hl₁ : D.rad.G.toGraph.IsLink f₁ r v₁)
    (hl₂ : D.rad.G.toGraph.IsLink f₂ r v₂) (hne : v₁ ≠ v₂) (hf₁ : f₁ ⊆ discBd W)
      (hf₂ : f₂ ⊆ discBd W) (hZ : Z.IsSimple)
    (hZW : (walkDrawing D.rad.G Z).U ⊆ W) (hZb : (walkDrawing D.rad.G Z).U ∩ discBd W = {v₁, v₂}) :
    ∃ Δ Δ' C, D.IsSector W r f₁ f₂ Z Δ Δ' C := by
  have : ConnectedSpace Shat := cap.connected
  have hcl : IsClosed (discBd W) := by
    rw [← IsClosedDisc.frontier_eq_discBd cap.isClosedSurface hW]
    exact isClosed_frontier
  have hrv₁ : r ≠ v₁ := fun e ↦ hr.1.2 (e ▸ D.hatV_of_link hr.1 hl₁)
  have hrv₂ : r ≠ v₂ := fun e ↦ hr.1.2 (e ▸ D.hatV_of_link hr.1 hl₂)
  have hY : (arcWalk hl₁ hl₂).IsSimple := by
    change [v₁, r, v₂].Nodup
    simp [hrv₁.symm, hrv₂, hne]
  have hYb : (walkDrawing D.rad.G (arcWalk hl₁ hl₂)).U ⊆ discBd W := by
    rw [arcWalk_U]
    exact union_subset (closure_minimal hf₁ hcl) (closure_minimal hf₂ hcl)
  obtain ⟨Δ₁, Δ₂, d₁, d₂, hu, hi, b₁, b₂⟩ := exists_chord_discs hW hG hne hY hZ hYb hZW hZb
  rw [arcWalk_U] at b₁ b₂
  have hsubG : discBd Δ₁ ⊆ D.rad.G.U := by
    rw [b₁]
    exact union_subset (by rw [← arcWalk_U hl₁ hl₂]; exact (walkDrawing_isSubdrawing _ _).U_subset)
      (walkDrawing_isSubdrawing _ _).U_subset
  obtain ⟨C, hCc, hCs, hCU⟩ := exists_circuit_of_oArc d₁.isOArc_discBd hsubG
  exact ⟨Δ₁, Δ₂, C, hr, hl₁, hl₂, hne, hf₁, hf₂, hZ, d₁, d₂, hu, hi, b₁, b₂, ⟨hCs, hCc⟩, hCU⟩

variable {u h : Shat} {A₁ : GraphWalk D.rad.G.toGraph v₁ u} {A₂ : GraphWalk D.rad.G.toGraph v₂ u}
  {T : GraphWalk D.rad.G.toGraph u h}

omit [T2Space S] in
theorem IsFan.chord_simple (hf : D.IsFan W H ρ r f₁ f₂ A₁ A₂ T) : (A₁.append A₂.reverse).IsSimple
  := by
  have hA₁ : A₁.IsSimple := (GraphWalk.IsSimple.of_append hf.spoke₁.1).1
  have hA₂ : A₂.IsSimple := (GraphWalk.IsSimple.of_append hf.spoke₂.1).1
  refine isSimple_append' hA₁ hA₂.reverse fun x h₁ h₂ ↦ hf.meet x h₁ ?_
  simpa [GraphWalk.support_reverse] using h₂

/-- The sector of a fan. -/
theorem IsFan.exists_sector (hf : D.IsFan W H ρ r f₁ f₂ A₁ A₂ T) (hf₁ : f₁ ⊆ discBd W)
  (hf₂ : f₂ ⊆ discBd W) :
    ∃ Δ Δ' C, D.IsSector W r f₁ f₂ (A₁.append A₂.reverse) Δ Δ' C ∧ D.IsBoundarySector W H r Δ C
      := by
  have hW := hf.hub
  have hU₁ := walkU_left_subset A₁ T
  have hU₂ := walkU_left_subset A₂ T
  have hsW₁ := hf.spoke₁.subset_W hW hf.bd_off hf.inner
  have hsW₂ := hf.spoke₂.subset_W hW hf.bd_off hf.inner
  have hmem : ∀ {a b : Shat} (A : GraphWalk D.rad.G.toGraph a b), a ∈ (walkDrawing D.rad.G A).U
    ∧ b ∈ (walkDrawing D.rad.G A).U := fun A ↦
    ⟨(mem_walkDrawing_U _ _).mpr (.inl A.start_mem_support), (mem_walkDrawing_U _ _).mpr
      (.inl A.end_mem_support)⟩
  have hZb : (walkDrawing D.rad.G (A₁.append A₂.reverse)).U ∩ discBd W = {v₁, v₂} := by
    rw [walkU_append, walkU_reverse]
    apply subset_antisymm
    · rintro y ⟨hy | hy, hyb⟩
      · exact .inl (hf.spoke₁.meet_bd hW hf.bd_off hf.inner (hU₁ hy) hyb)
      · exact .inr (hf.spoke₂.meet_bd hW hf.bd_off hf.inner (hU₂ hy) hyb)
    · rintro y (rfl | hy)
      · exact ⟨.inl (hmem A₁).1, hf.spoke₁.2.v_mem.2⟩
      · rw [mem_singleton_iff.mp hy]
        exact ⟨.inr (hmem A₂).1, hf.spoke₂.2.v_mem.2⟩
  have hZW : (walkDrawing D.rad.G (A₁.append A₂.reverse)).U ⊆ W := by
    rw [walkU_append, walkU_reverse]
    exact union_subset (hU₁.trans hsW₁) (hU₂.trans hsW₂)
  obtain ⟨Δ, Δ', C, hs⟩ := exists_sector_of_chord hW.is_disc hW.bd_sub ⟨hf.r_mem, hf.r_bd⟩ hf.link₁
    hf.link₂ hf.ne hf₁ hf₂ hf.chord_simple hZW hZb
  obtain ⟨C', hC'⟩ := hf.exists_circuit
  have hbd : discBd Δ = C'.U := by
    rw [hs.bd_eq, hf.U_eq hC', walkU_append, walkU_reverse]
    ext x
    simp only [mem_union]
    tauto
  have hΔW : Δ ⊆ W := hs.union ▸ subset_union_left
  refine ⟨Δ, Δ', C, hs, ⟨hf.r_mem, hf.r_bd⟩, hΔW, hs.disc, hs.circuit, hs.C_U, v₁, v₂, h, h, f₁,
    f₂, _, _, hf.ne, hf.link₁.1, hf₁, ?_, hf.link₂.1, hf₂, ?_, hf.spoke₁.2, hf.spoke₂.2, ?_⟩
  · rw [← closure_inter_V_eq_tilde hf.link₁.1]
    exact hf.link₁.2.2.2
  · rw [← closure_inter_V_eq_tilde hf.link₂.1]
    exact hf.link₂.2.2.2
  · refine .inl ⟨⟨h, ?_⟩, ?_⟩
    · rw [walkDrawing_V, walkDrawing_V]
      exact ⟨(GraphWalk.mem_support_append A₁ T).mpr (.inr T.end_mem_support),
        (GraphWalk.mem_support_append A₂ T).mpr (.inr T.end_mem_support)⟩
    · rw [hbd, hf.closure_formula hC']

variable {h₁ h₂ : Shat} {K₁ : GraphWalk D.rad.G.toGraph v₁ h₁} {K₂ : GraphWalk D.rad.G.toGraph v₂
  h₂}

/-- `r*` is on no spoke, by (13.1). -/
theorem notMem_spoke_of_Rstar (hW : D.IsWheelHubOfRadius W H ρ) (hbdS : discBd W ⊆ cap.emb ''
  (univ \ bd S)) (hin : ((W \ discBd W) ∩ (cap.emb '' D.Γ.V)).Nonempty)
    (hr : r ∈ D.rad.Rstar ∩ discBd W) {v h' : Shat} {K : GraphWalk D.rad.G.toGraph v h'}
      (hK : D.IsSpokeWalk W H K) : r ∉ K.support := by
  intro hm
  obtain ⟨L, R, rfl⟩ := K.exists_append_of_mem hm
  obtain ⟨P, hP, hle⟩ := exists_path_of_walk R
  have h₂ := (hW.spoke_length hK).1
  rw [GraphWalk.length_append] at h₂
  have hpos : 0 < L.length := by
    by_contra hn
    have hz : L.length = 0 := by omega
    cases L with
    | nil _ => exact hr.1.2 hK.2.v_mem.1
    | cons _ _ => simp [GraphWalk.length_cons] at hz
  exact theorem_13_1_proof hW hbdS hin hr.1 hr.2 ⟨P, h', hK.2.h_mem, hP, by omega⟩

/-- The chord through a path of the hub. -/
theorem exists_hub_chord (hW : D.IsWheelHubOfRadius W H ρ) (hbdS : discBd W ⊆ cap.emb ''
  (univ \ bd S)) (hin : ((W \ discBd W) ∩ (cap.emb '' D.Γ.V)).Nonempty)
    (h1 : D.IsSpokeWalk W H K₁) (h2 : D.IsSpokeWalk W H K₂) (hd : ∀ x ∈ K₁.support, x ∉ K₂.support)
      {P : Drawing Shat} (hP : Drawing.IsPathOf P H h₁ h₂) :
    ∃ Z : GraphWalk D.rad.G.toGraph v₁ v₂, Z.IsSimple ∧ (walkDrawing D.rad.G Z).U =
      (walkDrawing D.rad.G K₁).U ∪ (walkDrawing D.rad.G K₂).U ∪ P.U ∧
      (walkDrawing D.rad.G Z).U ⊆ W ∧ (walkDrawing D.rad.G Z).U ∩ discBd W = {v₁, v₂} := by
  have hPG : Drawing.IsPathOf P D.rad.G h₁ h₂ := ⟨hP.1.trans hW.H_sub, hP.2⟩
  obtain ⟨M, hMs, hMV, hME⟩ := hPG.exists_simple_walk
  have hMU : (walkDrawing D.rad.G M).U = P.U := by
    rw [Drawing.U_eq, Drawing.U_eq, walkDrawing_V, walkDrawing_E]
    ext x
    simp [hMV, hME]
  have hPU : P.U ⊆ H.U := hP.1.U_subset
  have hmeet₁ : ∀ x ∈ K₁.support, x ∈ M.support → x = h₁ := fun x hx hxM ↦
    h1.support_hub hx (hP.1.1 ((hMV x).mpr hxM))
  have hmeet₂ : ∀ x ∈ K₂.support, x ∈ M.support → x = h₂ := fun x hx hxM ↦
    h2.support_hub hx (hP.1.1 ((hMV x).mpr hxM))
  have hs₂ : (M.append K₂.reverse).IsSimple := isSimple_append' hMs h2.1.reverse fun x hx hx' ↦
    hmeet₂ x (by simpa [GraphWalk.support_reverse] using hx') hx
  have hs : (K₁.append (M.append K₂.reverse)).IsSimple := isSimple_append' h1.1 hs₂ fun x hx hx' ↦
    by
    rcases (GraphWalk.mem_support_append _ _).mp hx' with hx' | hx'
    · exact hmeet₁ x hx hx'
    · exact absurd (by simpa [GraphWalk.support_reverse] using hx') (hd x hx)
  have hU : (walkDrawing D.rad.G (K₁.append (M.append K₂.reverse))).U =
    (walkDrawing D.rad.G K₁).U ∪ (walkDrawing D.rad.G K₂).U ∪ P.U := by
    rw [walkU_append, walkU_append, walkU_reverse, hMU]
    ext x
    simp only [mem_union]
    tauto
  have hHW : H.U ⊆ W \ discBd W := hW.H_in_int
  have hsW₁ := h1.subset_W hW hbdS hin
  have hsW₂ := h2.subset_W hW hbdS hin
  refine ⟨_, hs, hU, ?_, ?_⟩
  · rw [hU]
    exact union_subset (union_subset hsW₁ hsW₂) (hPU.trans (hHW.trans sdiff_subset))
  · rw [hU]
    apply subset_antisymm
    · rintro y ⟨(hy | hy) | hy, hyb⟩
      · exact .inl (h1.meet_bd hW hbdS hin hy hyb)
      · exact .inr (h2.meet_bd hW hbdS hin hy hyb)
      · exact absurd hyb (hHW (hPU hy)).2
    · rintro y (rfl | hy)
      · exact ⟨.inl (.inl ((mem_walkDrawing_U _ _).mpr (.inl K₁.start_mem_support))), h1.2.v_mem.2⟩
      · rw [mem_singleton_iff.mp hy]
        exact ⟨.inl (.inr ((mem_walkDrawing_U _ _).mpr (.inl K₂.start_mem_support))), h2.2.v_mem.2⟩

/-- The sector of two spokes that do not meet: the hub is a circuit, and of its two paths between
the inner ends one gives a disc that does not hold `ins(H)`. -/
theorem exists_hub_sector (hW : D.IsWheelHubOfRadius W H ρ) (hbdS : discBd W ⊆ cap.emb ''
  (univ \ bd S)) (hin : ((W \ discBd W) ∩ (cap.emb '' D.Γ.V)).Nonempty)
    (h1 : D.IsSpokeWalk W H K₁) (h2 : D.IsSpokeWalk W H K₂) (hd : ∀ x ∈ K₁.support, x ∉ K₂.support)
      (hr : r ∈ D.rad.Rstar ∩ discBd W)
    (hl₁ : D.rad.G.toGraph.IsLink f₁ r v₁) (hl₂ : D.rad.G.toGraph.IsLink f₂ r v₂) (hne : v₁ ≠ v₂)
      (hf₁ : f₁ ⊆ discBd W) (hf₂ : f₂ ⊆ discBd W) :
    ∃ (P : Drawing Shat) (Z : GraphWalk D.rad.G.toGraph v₁ v₂) (Δ Δ' : Set Shat)
      (C : Drawing Shat), Drawing.IsPathOf P H h₁ h₂ ∧
      (walkDrawing D.rad.G Z).U = (walkDrawing D.rad.G K₁).U ∪ (walkDrawing D.rad.G K₂).U ∪ P.U
        ∧ D.IsSector W r f₁ f₂ Z Δ Δ' C ∧
      D.IsBoundarySector W H r Δ C := by
  classical
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hh₁H := h1.2.h_mem
  have hh₂H := h2.2.h_mem
  have hhne : h₁ ≠ h₂ := by
    rintro rfl
    exact hd h₁ K₁.end_mem_support K₂.end_mem_support
  obtain ⟨hH, hle⟩ : IsEnclave D.tb D.ord D.𝒯 H ∧ H.E.ncard ≤ 4 * ρ + 4 := by
    rcases hW.hub_cond with ⟨hc, -, -⟩ | ⟨hH, hle, -⟩
    · obtain ⟨z, hz⟩ := ncard_eq_one.mp hc
      exact absurd ((hz ▸ hh₁H : h₁ ∈ ({z} : Set Shat)).trans (hz ▸ hh₂H : h₂ ∈
        ({z} : Set Shat)).symm) hhne
    · exact ⟨hH, hle⟩
  obtain ⟨-, -, -, hc, hlt, -⟩ := id hH
  have hrep := hW.rep_ge
  have hi := D.ins_spec hc (by omega)
  have hiW : D.ins H ⊆ W := hW.ins_sub H hc hle (hW.H_in_int.trans sdiff_subset)
  obtain ⟨P, Q, hP, hQ, hPs, hQs, -, -, hPQ, hE, hHsup⟩ := Drawing.IsCircuit.exists_two_paths hc.2
    hh₁H hh₂H hhne
  have hlP := isLine_of_isPathBetween hP hhne
  have hlQ := isLine_of_isPathBetween hQ hhne
  have hPQU := paths_U_inter hPs hQs hPQ hE hlP hlQ
  have build : ∀ {R : Drawing Shat}, Drawing.IsPathOf R H h₁ h₂ → ∃ (Z : GraphWalk D.rad.G.toGraph
    v₁ v₂) (Δ Δ' : Set Shat) (C : Drawing Shat),
      (walkDrawing D.rad.G Z).U = (walkDrawing D.rad.G K₁).U ∪ (walkDrawing D.rad.G K₂).U ∪ R.U
        ∧ D.IsSector W r f₁ f₂ Z Δ Δ' C := by
    intro R hR
    obtain ⟨Z, hZ, hU, hZW, hZb⟩ := exists_hub_chord hW hbdS hin h1 h2 hd hR
    obtain ⟨Δ, Δ', C, hs⟩ := exists_sector_of_chord hW.is_disc hW.bd_sub hr hl₁ hl₂ hne hf₁ hf₂ hZ
      hZW hZb
    exact ⟨Z, Δ, Δ', C, hU, hs⟩
  obtain ⟨Z_P, Δ_P, Δ_P', C_P, hU_P, hs_P⟩ := build ⟨hPs, hP⟩
  obtain ⟨Z_Q, Δ_Q, Δ_Q', C_Q, hU_Q, hs_Q⟩ := build ⟨hQs, hQ⟩
  have finish : ∀ {R : Drawing Shat} {Z : GraphWalk D.rad.G.toGraph v₁ v₂} {Δ Δ' : Set Shat} {C :
    Drawing Shat}, Drawing.IsPathOf R H h₁ h₂ →
      (walkDrawing D.rad.G Z).U = (walkDrawing D.rad.G K₁).U ∪ (walkDrawing D.rad.G K₂).U ∪ R.U
        → D.IsSector W r f₁ f₂ Z Δ Δ' C → ¬ D.ins H ⊆ Δ →
      ∃ (P : Drawing Shat) (Z : GraphWalk D.rad.G.toGraph v₁ v₂) (Δ Δ' : Set Shat)
        (C : Drawing Shat), Drawing.IsPathOf P H h₁ h₂ ∧
      (walkDrawing D.rad.G Z).U = (walkDrawing D.rad.G K₁).U ∪ (walkDrawing D.rad.G K₂).U ∪ P.U
        ∧ D.IsSector W r f₁ f₂ Z Δ Δ' C ∧
      D.IsBoundarySector W H r Δ C := by
    intro R Z Δ Δ' C hR hU hs hn
    refine ⟨R, Z, Δ, Δ', C, hR, hU, hs, hr, hs.union ▸ subset_union_left, hs.disc, hs.circuit,
      hs.C_U, v₁, v₂, h₁, h₂, f₁, f₂, _, _, hne, hl₁.1, hf₁, ?_, hl₂.1, hf₂, ?_, h1.2, h2.2, ?_⟩
    · rw [← closure_inter_V_eq_tilde hl₁.1]
      exact hl₁.2.2.2
    · rw [← closure_inter_V_eq_tilde hl₂.1]
      exact hl₂.2.2.2
    · refine .inr ⟨?_, R, hR, ?_, hn⟩
      · rw [walkDrawing_V, walkDrawing_V]
        exact disjoint_left.mpr fun x h₁ h₂ ↦ hd x h₁ h₂
      · rw [hs.bd_eq, hU]
        ext x
        simp only [mem_union]
        tauto
  by_cases hin_P : D.ins H ⊆ Δ_P
  swap
  · exact finish ⟨hPs, hP⟩ hU_P hs_P hin_P
  refine finish ⟨hQs, hQ⟩ hU_Q hs_Q fun hin_Q ↦ ?_
  -- `Q` is a chord of `Δ_P`, and it cuts off `ins(H)` from `Δ_Q`.
  obtain ⟨M_P, hMsP, hMVP, hMEP⟩ := Drawing.IsPathOf.exists_simple_walk
    (⟨hPs.trans hW.H_sub, hP⟩ : Drawing.IsPathOf P D.rad.G h₁ h₂)
  obtain ⟨M_Q, hMsQ, hMVQ, hMEQ⟩ := Drawing.IsPathOf.exists_simple_walk
    (⟨hQs.trans hW.H_sub, hQ⟩ : Drawing.IsPathOf Q D.rad.G h₁ h₂)
  have hUP : (walkDrawing D.rad.G M_P).U = P.U := by
    rw [Drawing.U_eq, Drawing.U_eq, walkDrawing_V, walkDrawing_E]
    ext x
    simp [hMVP, hMEP]
  have hUQ : (walkDrawing D.rad.G M_Q).U = Q.U := by
    rw [Drawing.U_eq, Drawing.U_eq, walkDrawing_V, walkDrawing_E]
    ext x
    simp [hMVQ, hMEQ]
  have hHint := hW.H_in_int
  have hPH : P.U ⊆ H.U := hPs.U_subset
  have hQH : Q.U ⊆ H.U := hQs.U_subset
  have hHU : H.U ⊆ D.ins H := by
    rw [← hi.2.2.2.1]
    exact Surface.discBd_subset _
  have hcl : IsClosed (discBd W) := by
    rw [← IsClosedDisc.frontier_eq_discBd cap.isClosedSurface hW.is_disc]
    exact isClosed_frontier
  have hLbd : closure f₁ ∪ closure f₂ ⊆ discBd W := union_subset (closure_minimal hf₁ hcl)
    (closure_minimal hf₂ hcl)
  have hsp₁ : ∀ {y}, y ∈ (walkDrawing D.rad.G K₁).U → y ∈ H.U → y = h₁
    := fun hy hyH ↦ h1.U_inter_hub hW hy hyH
  have hsp₂ : ∀ {y}, y ∈ (walkDrawing D.rad.G K₂).U → y ∈ H.U → y = h₂
    := fun hy hyH ↦ h2.U_inter_hub hW hy hyH
  have hend₁ : h₁ ∈ (walkDrawing D.rad.G K₁).U := (mem_walkDrawing_U _ _).mpr
    (.inl K₁.end_mem_support)
  have hend₂ : h₂ ∈ (walkDrawing D.rad.G K₂).U := (mem_walkDrawing_U _ _).mpr
    (.inl K₂.end_mem_support)
  have hbdP : discBd Δ_P = (closure f₁ ∪ closure f₂) ∪ ((walkDrawing D.rad.G K₁).U ∪
    (walkDrawing D.rad.G K₂).U ∪ P.U) := by
    rw [hs_P.bd_eq, hU_P]
  have hbdQ : discBd Δ_Q = (closure f₁ ∪ closure f₂) ∪ ((walkDrawing D.rad.G K₁).U ∪
    (walkDrawing D.rad.G K₂).U ∪ Q.U) := by
    rw [hs_Q.bd_eq, hU_Q]
  have hG : discBd Δ_P ⊆ D.rad.G.U := hs_P.C_U ▸ hs_P.circuit.1.U_subset
  have hYb : (walkDrawing D.rad.G M_P).U ⊆ discBd Δ_P := by
    rw [hUP, hbdP]
    exact fun y hy ↦ .inr (.inr hy)
  have hZW : (walkDrawing D.rad.G M_Q).U ⊆ Δ_P := by
    rw [hUQ]
    exact hQH.trans (hHU.trans hin_P)
  have hZb : (walkDrawing D.rad.G M_Q).U ∩ discBd Δ_P = {h₁, h₂} := by
    rw [hUQ, hbdP]
    apply subset_antisymm
    · rintro y ⟨hyQ, hy⟩
      rcases hy with hy | (hy | hy) | hy
      · exact absurd (hLbd hy) (hHint (hQH hyQ)).2
      · exact .inl (hsp₁ hy (hQH hyQ))
      · exact .inr (hsp₂ hy (hQH hyQ))
      · exact hPQU ▸ ⟨hy, hyQ⟩
    · rintro y (rfl | hy)
      · exact ⟨hlQ.left_mem, .inr (.inl (.inl hend₁))⟩
      · rw [mem_singleton_iff.mp hy]
        exact ⟨hlQ.right_mem, .inr (.inl (.inr hend₂))⟩
  obtain ⟨E₁, E₂, d₁, d₂, hu, hint, b₁, b₂⟩ := exists_chord_discs hs_P.disc hG hhne hMsP hMsQ hYb
    hZW hZb
  rw [hUP, hUQ] at b₁ b₂
  rw [hUQ] at hint
  have hΔPW : Δ_P ⊆ W := hs_P.union ▸ subset_union_left
  have hΔQW : Δ_Q ⊆ W := hs_Q.union ▸ subset_union_left
  have hE₁W : E₁ ⊆ W := (hu ▸ subset_union_left : E₁ ⊆ Δ_P).trans hΔPW
  have hE₂W : E₂ ⊆ W := (hu ▸ subset_union_right : E₂ ⊆ Δ_P).trans hΔPW
  have hHeq : H.U = P.U ∪ Q.U := paths_U_union hPs hQs hHsup
  have e₁ : E₁ = D.ins H := disc_eq_of_subset_disc hT hW.is_disc d₁ hi.2.2.1 hE₁W hiW
    (by rw [b₁, hi.2.2.2.1, hHeq])
  have e₂ : E₂ = Δ_Q := by
    refine disc_eq_of_subset_disc hT hW.is_disc d₂ hs_Q.disc hE₂W hΔQW ?_
    rw [b₂, hbdQ, hbdP]
    ext y
    simp only [mem_union, mem_sdiff, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro (⟨h₁' | (h₁' | h₁') | h₁', hn⟩ | h₁')
      · exact .inl h₁'
      · exact .inr (.inl (.inl h₁'))
      · exact .inr (.inl (.inr h₁'))
      · by_cases hy : y = h₁
        · exact .inr (.inl (.inl (hy ▸ hend₁)))
        · by_cases hy' : y = h₂
          · exact .inr (.inl (.inr (hy' ▸ hend₂)))
          · exact absurd ⟨h₁', not_or.mpr ⟨hy, hy'⟩⟩ hn
      · exact .inr (.inr h₁')
    · rintro (h₁' | (h₁' | h₁') | h₁')
      · exact .inl ⟨.inl h₁', fun h ↦ (hHint (hPH h.1)).2 (hLbd h₁')⟩
      · refine .inl ⟨.inr (.inl (.inl h₁')), fun h ↦ h.2 (.inl (hsp₁ h₁' (hPH h.1)))⟩
      · refine .inl ⟨.inr (.inl (.inr h₁')), fun h ↦ h.2 (.inr (hsp₂ h₁' (hPH h.1)))⟩
      · exact .inr h₁'
  obtain ⟨y, hy, hyn⟩ := GraphMinor.GM19.IsLineWithEnds.diff_nonempty hlP
  have hyE₁ : y ∈ E₁ := e₁ ▸ hHU (hPH hy)
  have hyE₂ : y ∈ E₂ := e₂ ▸ hin_Q (hHU (hPH hy))
  have hyQ : y ∈ Q.U := hint ▸ ⟨hyE₁, hyE₂⟩
  exact hyn (hPQU ▸ ⟨hy, hyQ⟩)

end TangleDatum

end GraphMinor.GM19
