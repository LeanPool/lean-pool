/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section13f

/-!
# Graph Minors XIX, Section 13: (13.5)

`D_v` is short. If the two spokes meet then `D_v` is the circuit of their fan. If they do not, then
the paper's proof applies (8.5) to the
theta formed by the two paths of `H` and the outer path through the spokes.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

/-- A simple walk from `a` to `b` with its edges among those of another one is that one. -/
theorem simple_walk_unique {α' β : Type*} {G : Graph α' β} {a b : α'} (A B : GraphWalk G a b)
  (hA : A.IsSimple) (hB : B.IsSimple)
    (hsub : ∀ e ∈ B.edges, e ∈ A.edges) : A = B := by
  induction A with
  | nil h =>
    cases B with
    | nil _ => rfl
    | @cons _ x _ e hl r =>
      have := hsub e (by simp)
      simp at this
  | @cons a x b e hl r ih =>
    have hsA : (GraphWalk.cons hl r).support.Nodup := hA
    simp only [GraphWalk.support_cons, List.nodup_cons] at hsA
    cases B with
    | nil _ => exact absurd r.end_mem_support hsA.1
    | @cons _ x' _ e' hl' r' =>
      have hsB : (GraphWalk.cons hl' r').support.Nodup := hB
      simp only [GraphWalk.support_cons, List.nodup_cons] at hsB
      have hee : e' = e := by
        have := hsub e' (by simp)
        rcases List.mem_cons.mp (by simpa using this) with h | h
        · exact h
        · exact absurd (r.left_mem_support_of_mem_edges h hl') hsA.1
      subst hee
      obtain rfl := hl.right_unique hl'
      have hsub' : ∀ f ∈ r'.edges, f ∈ r.edges := by
        intro f hf
        have h₁ := hsub f (by simp [hf])
        rcases List.mem_cons.mp (by simpa using h₁) with h | h
        · subst h
          exact absurd (r'.left_mem_support_of_mem_edges hf hl) hsB.1
        · exact h
      rw [ih r' hsA.2 hsB.2 hsub']

/-- The last edge of a walk with an edge. -/
theorem GraphWalk.exists_last_edge {α' β : Type*} {G : Graph α' β} {a b : α'} (A : GraphWalk G a b)
  (h : 1 ≤ A.length) :
    ∃ (g : β) (c : α'), g ∈ A.edges ∧ G.IsLink g b c := by
  induction A with
  | nil _ => simp [GraphWalk.length] at h
  | @cons a x b e hl r ih =>
    by_cases hr : 1 ≤ r.length
    · obtain ⟨g, c, h₁, h₂⟩ := ih hr
      exact ⟨g, c, by simp [h₁], h₂⟩
    · have h₀ : x = b := GraphWalk.eq_of_length_eq_zero (show r.length = 0 by omega)
      subst h₀
      exact ⟨e, a, by simp, hl.symm⟩

/-- A path of a circuit between `a` and `b` is one of the two paths of the circuit between them. -/
theorem path_of_circuit {T : Type} [TopologicalSpace T] [T2Space T] {C F₁ F₂ P : Drawing T} {a b :
  T} (hab : a ≠ b)
    (hF₁ : F₁.IsPathBetween a b) (hF₂ : F₂.IsPathBetween a b) (hs₁ : F₁.IsSubdrawing C)
      (hs₂ : F₂.IsSubdrawing C)
    (hV : F₁.V ∩ F₂.V = {a, b}) (hE : Disjoint F₁.E F₂.E) (hU : C.U = F₁.U ∪ F₂.U)
      (hP : Drawing.IsPathOf P C a b) :
    P = F₁ ∨ P = F₂ := by
  classical
  have hline := isLine_of_isPathBetween hP.2 hab
  have hcon : IsPreconnected (P.U \ {a, b}) := hline.isPreconnected_diff
  have hinter : F₁.U ∩ F₂.U = {a, b} := by
    rw [U_inter_of_disjoint hs₁ hs₂ hE, hV]
  obtain ⟨Kp, hKp, hVp, hEp⟩ := Drawing.IsPathOf.exists_simple_walk hP
  -- If the edges of `P` lie in `Fᵢ` then `P = Fᵢ`.
  have key : ∀ {X : Drawing T}, X.IsPathBetween a b → X.IsSubdrawing C → (∀ e ∈ P.E, e ∈ X.E) → P
    = X := by
    intro X hX hXs hsub
    obtain ⟨Kx, hKx, hVx, hEx⟩ := Drawing.IsPathOf.exists_simple_walk
      (show Drawing.IsPathOf X C a b from ⟨hXs, hX⟩)
    obtain rfl := simple_walk_unique Kx Kp hKx hKp fun e he ↦ (hEx e).mp (hsub e ((hEp e).mpr he))
    refine Drawing.ext_of_V_E ?_ ?_
    · ext x
      rw [hVp, hVx]
    · ext e
      rw [hEp, hEx]
  have haC : a ∈ C.V := Kp.mem_vertexSet_of_mem_support Kp.start_mem_support
  have hbC : b ∈ C.V := Kp.mem_vertexSet_of_mem_support Kp.end_mem_support
  -- If `P` off its ends lies in `U(Fᵢ)` then its edges are edges of `Fᵢ`.
  have hedges : ∀ {X : Drawing T}, X.IsSubdrawing C → (P.U \ {a, b} ⊆ X.U) → ∀ e ∈ P.E, e ∈ X.E
    := by
    intro X hXs hsub e he
    have heC := hP.1.2 he
    obtain ⟨z, hz⟩ := heC.2.2.1.nonempty
    have hzV : z ∉ C.V := (heC.2.1 hz).2
    have hzX : z ∈ P.U \ {a, b} := by
      refine ⟨P.closure_subset_U he (subset_closure hz), ?_⟩
      rintro (rfl | rfl)
      · exact hzV haC
      · exact hzV hbC
    obtain ⟨e', he', hze'⟩ := X.exists_edge_of_mem (hsub hzX) fun h' ↦ hzV (hXs.1 h')
    obtain rfl := C.edge_eq_of_mem heC (hXs.2 he') hz hze'
    exact he'
  have hcov : P.U \ {a, b} ⊆ F₁.U ∪ F₂.U := by
    rw [← hU]
    exact fun x hx ↦ hP.1.U_subset hx.1
  by_cases h₁ : ((P.U \ {a, b}) ∩ F₁.U).Nonempty
  · by_cases h₂ : ((P.U \ {a, b}) ∩ F₂.U).Nonempty
    · exfalso
      obtain ⟨x, hx, hxi⟩ := isPreconnected_closed_iff.mp hcon _ _ F₁.isClosed_U F₂.isClosed_U hcov
        h₁ h₂
      rw [hinter] at hxi
      exact hx.2 hxi
    · refine .inl (key hF₁ hs₁ (hedges hs₁ fun x hx ↦ ?_))
      rcases hcov hx with h' | h'
      · exact h'
      · exact absurd ⟨x, hx, h'⟩ h₂
  · refine .inr (key hF₂ hs₂ (hedges hs₂ fun x hx ↦ ?_))
    rcases hcov hx with h' | h'
    · exact absurd ⟨x, hx, h'⟩ h₁
    · exact h'

namespace TangleDatum

variable {D : TangleDatum cap χ} {W : Set Shat} {H : Drawing Shat} {ρ : ℕ} {r v₁ v₂ u h : Shat} {f₁
  f₂ : Set Shat}
  {A₁ : GraphWalk D.rad.G.toGraph v₁ u} {A₂ : GraphWalk D.rad.G.toGraph v₂ u} {T : GraphWalk
    D.rad.G.toGraph u h} {C : Drawing Shat}

omit [T2Space S] in
/-- A vertex of `bd(W)` is not strictly inside a disc in `W`. -/
theorem IsWheelHubOfRadius.bd_not_strict (hW : D.IsWheelHubOfRadius W H ρ) {F : Drawing Shat}
  (hF : F.IsCircuitOf D.rad.G)
    (hlt : F.E.ncard < 2 * D.rep) (hsub : D.ins F ⊆ W) {v : Shat} (hv : v ∈ discBd W) : v ∉ D.ins F
      \ F.U := by
  have hT := cap.isClosedSurface
  intro h₁
  have hi := interior_mono hsub ((D.ins_diff_iff hF hlt).mp h₁)
  have hvf : v ∈ frontier W := by
    rw [IsClosedDisc.frontier_eq_discBd hT hW.is_disc]
    exact hv
  exact hvf.2 hi

omit [T2Space S] in
/-- The closure in the definition of `Δ_v`, when the spokes meet, is `U` of the circuit of the fan.
-/
theorem IsFan.closure_formula (hf : D.IsFan W H ρ r f₁ f₂ A₁ A₂ T) (hC : D.IsFanCircuit r f₁ f₂ A₁
  A₂ C) :
    closure (((walkDrawing D.rad.G (A₁.append T)).U ∪ (walkDrawing D.rad.G (A₂.append T)).U) \
      ((walkDrawing D.rad.G (A₁.append T)).U ∩ (walkDrawing D.rad.G (A₂.append T)).U) ∪ f₁ ∪ f₂)
        = C.U := by
  set X := ((walkDrawing D.rad.G (A₁.append T)).U ∪ (walkDrawing D.rad.G (A₂.append T)).U) \
      ((walkDrawing D.rad.G (A₁.append T)).U ∩ (walkDrawing D.rad.G (A₂.append T)).U) with hX
  have hform := hf.formula_eq hC
  have hsub₁ : X ⊆ C.U := fun x hx ↦ by
    rw [← hform]
    exact .inl (.inl (.inl hx))
  apply Subset.antisymm
  · refine closure_minimal (union_subset (union_subset hsub₁ ?_) ?_) C.isClosed_U
    · rw [← hform]
      exact fun x hx ↦ .inl (.inr (subset_closure hx))
    · rw [← hform]
      exact fun x hx ↦ .inr (subset_closure hx)
  · rw [← hform]
    refine union_subset (union_subset (union_subset ?_ ?_) ?_) ?_
    · exact subset_closure.trans' (subset_union_left.trans subset_union_left) |>.trans subset_rfl
    · rw [singleton_subset_iff]
      obtain ⟨g, c, hg, hl⟩ := GraphWalk.exists_last_edge A₁ hf.A_pos
      have hgE : g ∈ D.rad.G.E := TieBreaker.mem_edges_E A₁ hg
      have hu₁ : u ∈ A₁.support := A₁.end_mem_support
      have hu₂ : u ∈ A₂.support := A₂.end_mem_support
      have hT : u ∈ T.support := T.start_mem_support
      have i₁ := U_inter_of_simple D.rad.G A₁ T (fun x h₁ h₂ ↦ GraphWalk.inter_of_simple
        hf.spoke₁.1 h₁ h₂) hf.edges_disjoint_T hu₁ hT
      have i₃ := U_inter_of_simple D.rad.G A₁ A₂ hf.meet hf.edges_disjoint hu₁ hu₂
      have hgX : g ⊆ X := by
        intro p hp
        have hpA : p ∈ (walkDrawing D.rad.G A₁).U := (mem_walkDrawing_U _ _).mpr
          (.inr ⟨g, hg, subset_closure hp⟩)
        have hpV : p ≠ u := fun h' ↦ (hgE.2.1 hp).2 (h' ▸ hf.u_mem_G)
        refine ⟨.inl ?_, ?_⟩
        · rw [U_append]
          exact .inl hpA
        · rintro ⟨-, h₂⟩
          rw [U_append] at h₂
          rcases h₂ with h₂ | h₂
          · have : p ∈ (walkDrawing D.rad.G A₁).U ∩ (walkDrawing D.rad.G A₂).U := ⟨hpA, h₂⟩
            rw [i₃] at this
            exact hpV this
          · have : p ∈ (walkDrawing D.rad.G A₁).U ∩ (walkDrawing D.rad.G T).U := ⟨hpA, h₂⟩
            rw [i₁] at this
            exact hpV this
      have huc : u ∈ closure g ∩ D.rad.G.V := by
        rw [hl.2.2.2]
        exact .inl rfl
      exact closure_mono (hgX.trans (subset_union_left.trans subset_union_left)) huc.1
    · exact closure_mono (subset_union_right.trans subset_union_left)
    · exact closure_mono subset_union_right

/-- `r*` is on no spoke, by (13.1). -/
theorem IsWheelHubOfRadius.r_notMem_spoke (hW : D.IsWheelHubOfRadius W H ρ)
  (hbdS : discBd W ⊆ cap.emb '' (univ \ bd S))
    (hin : ((W \ discBd W) ∩ (cap.emb '' D.Γ.V)).Nonempty) (hr : r ∈ D.rad.Rstar ∩ discBd W) {v h'
      : Shat}
    {K : GraphWalk D.rad.G.toGraph v h'} (hK : D.IsSpokeWalk W H K) : r ∉ K.support := by
  intro hrK
  obtain ⟨L, R, rfl⟩ := K.exists_append_of_mem hrK
  obtain ⟨P, hP, hle⟩ := exists_path_of_walk R
  have h₂ := (hW.spoke_length hK).1
  rw [GraphWalk.length_append] at h₂
  have hpos : 1 ≤ L.length := by
    cases L with
    | nil _ => exact absurd hK.2.v_mem.1 hr.1.2
    | @cons _ c _ e hl q =>
      rw [GraphWalk.length_cons]
      omega
  exact theorem_13_1_proof hW hbdS hin hr.1 hr.2 ⟨P, h', hK.2.h_mem, hP, by omega⟩

omit [T2Space S] in
/-- A disc in `W` is determined by its boundary. -/
theorem IsWheelHubOfRadius.disc_eq (hW : D.IsWheelHubOfRadius W H ρ) {Δ₁ Δ₂ : Set Shat}
  (h₁ : IsClosedDisc Δ₁) (h₂ : IsClosedDisc Δ₂)
    (hs₁ : Δ₁ ⊆ W) (hs₂ : Δ₂ ⊆ W) (hb : discBd Δ₁ = discBd Δ₂) : Δ₁ = Δ₂ := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  by_contra hne
  have hcov := cover_of_discBd_eq hT h₁ h₂ hb hne
  obtain ⟨p, hp⟩ := hW.isConnected_compl.nonempty
  have : p ∈ Δ₁ ∪ Δ₂ := by
    rw [hcov]
    exact mem_univ p
  rcases this with h' | h'
  · exact hp (hs₁ h')
  · exact hp (hs₂ h')

private theorem outer_path_point_set
    {S Shat : Type} [TopologicalSpace S] [TopologicalSpace Shat] [T2Space Shat]
    {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}
    {D : TangleDatum cap χ}
    {r v₁ v₂ h₁ h₂ : Shat} {f₁ f₂ : Set Shat}
    {K₁ : GraphWalk D.rad.G.toGraph v₁ h₁} {K₂ : GraphWalk D.rad.G.toGraph v₂ h₂}
    (hl₁ : D.rad.G.toGraph.IsLink f₁ v₁ r) (O : Drawing Shat)
    (hOV : ∀ x, x ∈ O.V ↔ x ∈ K₁.support ∨ x = v₁ ∨ x = r ∨ x ∈ K₂.support)
    (hOE : ∀ e, e ∈ O.E ↔ e ∈ K₁.edges ∨ e = f₁ ∨ e = f₂ ∨ e ∈ K₂.edges) :
    O.U = (walkDrawing D.rad.G K₁).U ∪ (walkDrawing D.rad.G K₂).U ∪ closure f₁ ∪ closure f₂ := by
  have hv₁f : v₁ ∈ closure f₁ := by
    have : v₁ ∈ closure f₁ ∩ D.rad.G.V := by
      rw [hl₁.2.2.2]
      exact .inl rfl
    exact this.1
  have hrf : r ∈ closure f₁ := by
    have : r ∈ closure f₁ ∩ D.rad.G.V := by
      rw [hl₁.2.2.2]
      exact .inr rfl
    exact this.1
  ext x
  rw [O.U_eq]
  simp only [mem_union, mem_iUnion, mem_walkDrawing_U, hOV, hOE, exists_prop]
  constructor
  · rintro ((h' | rfl | rfl | h') | ⟨e, (h' | rfl | rfl | h'), hx⟩)
    · exact .inl (.inl (.inl (.inl h')))
    · exact .inl (.inr hv₁f)
    · exact .inl (.inr hrf)
    · exact .inl (.inl (.inr (.inl h')))
    · exact .inl (.inl (.inl (.inr ⟨e, h', hx⟩)))
    · exact .inl (.inr hx)
    · exact .inr hx
    · exact .inl (.inl (.inr (.inr ⟨e, h', hx⟩)))
  · rintro ((((h' | ⟨e, h', hx⟩) | (h' | ⟨e, h', hx⟩)) | h') | h')
    · exact .inl (.inl h')
    · exact .inr ⟨e, .inl h', hx⟩
    · exact .inl (.inr (.inr (.inr h')))
    · exact .inr ⟨e, .inr (.inr (.inr h')), hx⟩
    · exact .inr ⟨_, .inr (.inl rfl), h'⟩
    · exact .inr ⟨_, .inr (.inr (.inl rfl)), h'⟩

private theorem outer_path_inter_hub_inside
    {S Shat : Type} [TopologicalSpace S] [TopologicalSpace Shat] [T2Space Shat]
    {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}
    {D : TangleDatum cap χ}
    {W : Set Shat} {H : Drawing Shat} {r v₁ v₂ h₁ h₂ : Shat}
    {K₁ : GraphWalk D.rad.G.toGraph v₁ h₁} {K₂ : GraphWalk D.rad.G.toGraph v₂ h₂}
    (h1 : D.IsSpokeWalk W H K₁) (h2 : D.IsSpokeWalk W H K₂)
    (hHW : H.U ⊆ W \ discBd W) (hrH : r ∉ H.V)
    (hcH : H.IsCircuitOf D.rad.G) (hlt : H.E.ncard < 2 * D.rep) (hUi : H.U ⊆ D.ins H)
    (R : GraphWalk D.rad.G.toGraph v₁ h₂) (hRs : R.IsSimple)
    (hsupR : ∀ x, x ∈ R.support ↔ x = v₁ ∨ x = r ∨ x ∈ K₂.support)
    (O : Drawing Shat) (hO : O = walkDrawing D.rad.G (K₁.reverse.append R))
    (hOp : O.IsPathOf D.rad.G h₁ h₂)
    (hOV : ∀ x, x ∈ O.V ↔ x ∈ K₁.support ∨ x = v₁ ∨ x = r ∨ x ∈ K₂.support)
    (hm₁ : O.V ∩ H.V ⊆ {h₁, h₂}) (hm₂ : Disjoint O.E H.E)
    (hout : ∀ {v : Shat}, v ∈ discBd W → v ∉ D.ins H \ H.U) :
    O.U ∩ D.ins H = {h₁, h₂} := by
  apply Subset.antisymm
  · rintro p ⟨hpO, hpi⟩
    have hpH : p ∈ H.U := by
      rw [hO, U_append] at hpO
      rcases hpO with h' | h'
      · have h'' : p ∈ (walkDrawing D.rad.G K₁).U := by
          simpa [mem_walkDrawing_U, GraphWalk.support_reverse, GraphWalk.edges_reverse] using h'
        exact D.part_outside hcH hlt K₁ h1.1 (hout h1.2.v_mem.2) (fun y hy hyH ↦ h1.support_hub hy
          hyH) h'' hpi
      · refine D.part_outside hcH hlt R hRs (hout h1.2.v_mem.2) (fun y hy hyH ↦ ?_) h' hpi
        rcases (hsupR y).mp hy with rfl | rfl | h₃
        · exact absurd h1.2.v_mem.2 (hHW (H.V_subset_U hyH)).2
        · exact absurd hyH hrH
        · exact h2.support_hub h₃ hyH
    have hin' : p ∈ O.U ∩ H.U := ⟨hpO, hpH⟩
    rw [U_inter_of_disjoint hOp.1 hcH.1 hm₂] at hin'
    exact hm₁ hin'
  · rintro p (rfl | rfl)
    · exact ⟨O.V_subset_U ((hOV _).mpr (.inl K₁.end_mem_support)), hUi (H.V_subset_U h1.2.h_mem)⟩
    · exact ⟨O.V_subset_U ((hOV _).mpr (.inr (.inr (.inr K₂.end_mem_support)))), hUi
        (H.V_subset_U h2.2.h_mem)⟩

/-- (13.5) when the two spokes do not meet. -/
theorem sector_of_disjoint (hW : D.IsWheelHubOfRadius W H ρ) (hbdS : discBd W ⊆ cap.emb ''
  (univ \ bd S))
    (hin : ((W \ discBd W) ∩ (cap.emb '' D.Γ.V)).Nonempty) (hr : r ∈ D.rad.Rstar ∩ discBd W) {h₁ h₂
      : Shat}
    {K₁ : GraphWalk D.rad.G.toGraph v₁ h₁} {K₂ : GraphWalk D.rad.G.toGraph v₂ h₂}
      (h1 : D.IsSpokeWalk W H K₁) (h2 : D.IsSpokeWalk W H K₂)
    (hl₁ : D.rad.G.toGraph.IsLink f₁ v₁ r) (hl₂ : D.rad.G.toGraph.IsLink f₂ r v₂)
    (hdis : ∀ x ∈ K₁.support, x ∉ K₂.support) {P : Drawing Shat} (hP : Drawing.IsPathOf P H h₁ h₂)
      {Δv : Set Shat} {Dv : Drawing Shat}
    (hΔ : IsClosedDisc Δv) (hΔW : Δv ⊆ W) (hDv : Dv.IsCircuitOf D.rad.G) (hDU : Dv.U = discBd Δv)
    (hbd : discBd Δv = (walkDrawing D.rad.G K₁).U ∪ (walkDrawing D.rad.G K₂).U ∪ P.U ∪ closure f₁ ∪
      closure f₂)
    (hnot : ¬ D.ins H ⊆ Δv) : Dv.E.ncard ≤ 4 * ρ + 4 := by
  classical
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hHW := hW.H_in_int
  have hrep := hW.rep_ge
  have hr₁ := hW.r_notMem_spoke hbdS hin hr h1
  have hr₂ := hW.r_notMem_spoke hbdS hin hr h2
  have hrH : r ∉ H.V := fun h' ↦ (hHW (H.V_subset_U h')).2 hr.2
  have hend₁ : h₁ ∈ K₁.support := K₁.end_mem_support
  have hend₂ : h₂ ∈ K₂.support := K₂.end_mem_support
  have hne12 : h₁ ≠ h₂ := fun h' ↦ hdis h₁ hend₁ (h' ▸ hend₂)
  -- `H` is a circuit, since it has two vertices.
  have hen : IsEnclave D.tb D.ord D.𝒯 H ∧ H.E.ncard ≤ 4 * ρ + 4 := by
    rcases hW.hub_cond with ⟨hc, -, -⟩ | ⟨h₃, h₄, -⟩
    · exfalso
      obtain ⟨z, hz⟩ := ncard_eq_one.mp hc
      have e₁ := h1.2.h_mem
      have e₂ := h2.2.h_mem
      rw [hz] at e₁ e₂
      exact hne12 (e₁.trans e₂.symm)
    · exact ⟨h₃, h₄⟩
  obtain ⟨hFe, hHle⟩ := hen
  obtain ⟨ord', 𝒯', h𝒯', hcH, hlt₀, Δ₀, hins, hd⟩ := id hFe
  obtain rfl : Δ₀ = D.ins H := D.eq_ins_of_isInsOf hins
  have hlt : H.E.ncard < 2 * D.rep := by omega
  have hsl := D.isSlope (by omega)
  have hUi := (ins_facts_of_length hsl hcH.2 hcH.1 hlt).2.2
  have hinsW : D.ins H ⊆ W := hW.ins_sub H hcH hHle (hHW.trans sdiff_subset)
  -- The outer path.
  set R := GraphWalk.cons hl₁ (GraphWalk.cons hl₂ K₂) with hR
  have hRs : R.IsSimple := by
    have h₃ : (GraphWalk.cons hl₂ K₂).IsSimple := List.nodup_cons.mpr ⟨hr₂, h2.1⟩
    refine List.nodup_cons.mpr ⟨?_, h₃⟩
    rintro (_ | ⟨_, h'⟩)
    · exact hr.1.2 h1.2.v_mem.1
    · exact hdis _ K₁.start_mem_support h'
  have hsupR : ∀ x, x ∈ R.support ↔ x = v₁ ∨ x = r ∨ x ∈ K₂.support := fun x ↦ by simp [hR]
  have hedgR : ∀ e, e ∈ R.edges ↔ e = f₁ ∨ e = f₂ ∨ e ∈ K₂.edges := fun e ↦ by simp [hR]
  have hWkS : (K₁.reverse.append R).IsSimple := by
    refine isSimple_append' h1.1.reverse hRs fun y h₃ h₄ ↦ ?_
    have h₃' : y ∈ K₁.support := by simpa [GraphWalk.support_reverse] using h₃
    rcases (hsupR y).mp h₄ with h₅ | rfl | h₅
    · exact h₅
    · exact absurd h₃' hr₁
    · exact absurd h₅ (hdis y h₃')
  set O := walkDrawing D.rad.G (K₁.reverse.append R) with hO
  have hOp : Drawing.IsPathOf O D.rad.G h₁ h₂ := ⟨walkDrawing_isSubdrawing _ _,
    walkDrawing_isPathBetween _ hWkS⟩
  have hOV : ∀ x, x ∈ O.V ↔ x ∈ K₁.support ∨ x = v₁ ∨ x = r ∨ x ∈ K₂.support := by
    intro x
    rw [hO, walkDrawing_V]
    change x ∈ (K₁.reverse.append R).support ↔ _
    rw [GraphWalk.mem_support_append, hsupR]
    simp [GraphWalk.support_reverse]
  have hOE : ∀ e, e ∈ O.E ↔ e ∈ K₁.edges ∨ e = f₁ ∨ e = f₂ ∨ e ∈ K₂.edges := by
    intro e
    rw [hO, walkDrawing_E]
    change e ∈ (K₁.reverse.append R).edges ↔ _
    rw [GraphWalk.edges_append, List.mem_append, hedgR]
    simp [GraphWalk.edges_reverse]
  have hOlen : O.E.ncard ≤ 2 * ρ + 2 := by
    have e₁ := ncard_walk_E D.rad.G hWkS
    have l₁ := (hW.spoke_length h1).1
    have l₂ := (hW.spoke_length h2).1
    rw [← hO] at e₁
    rw [e₁, GraphWalk.length_append, GraphWalk.length_reverse, hR, GraphWalk.length_cons,
      GraphWalk.length_cons]
    omega
  have hOU : O.U = (walkDrawing D.rad.G K₁).U ∪ (walkDrawing D.rad.G K₂).U ∪ closure f₁ ∪ closure
    f₂ := by
    exact outer_path_point_set hl₁ O hOV hOE
  have hbd' : discBd Δv = O.U ∪ P.U := by
    rw [hbd, hOU]
    ext x
    simp only [mem_union]
    tauto
  -- The theta of `P`, the other path of `H`, and the outer path.
  obtain ⟨F₁, F₂, hF₁, hF₂, hs₁, hs₂, hp₁, hp₂, hV₁₂, hE₁₂, hsup⟩ := hcH.2.exists_two_paths
    h1.2.h_mem h2.2.h_mem hne12
  have hUH : H.U = F₁.U ∪ F₂.U := by
    have hv := Drawing.sup_V hs₁ hs₂
    have he := Drawing.sup_E hs₁ hs₂
    rw [hsup] at hv he
    exact U_union hv he
  have hm₁ : O.V ∩ H.V ⊆ {h₁, h₂} := by
    rintro x ⟨hx, hxH⟩
    rcases (hOV x).mp hx with h' | rfl | rfl | h'
    · exact .inl (h1.support_hub h' hxH)
    · exact .inl (h1.support_hub K₁.start_mem_support hxH)
    · exact absurd hxH hrH
    · exact .inr (h2.support_hub h' hxH)
  have hm₂ : Disjoint O.E H.E := by
    refine disjoint_left.mpr fun e he heH ↦ ?_
    have heG := hcH.1.2 heH
    obtain ⟨a, ha, b, hb, hcap⟩ := D.rad.isPreRadial.2.2.2.2.1 e heG
    have hne : a ≠ b := fun h' ↦ hb.2 (h' ▸ ha)
    have hl : D.rad.G.toGraph.IsLink e a b := ⟨heG, D.rad.isPreRadial.2.1 ha, hb.1, hcap⟩
    obtain ⟨hab, hbb⟩ := Drawing.IsLink.mem_V_of_sub hcH.1 hl heH
    rcases (hOE e).mp he with h' | rfl | rfl | h'
    · obtain ⟨h₃, h₄⟩ := D.ends_mem_support K₁ h' hcap
      exact hne ((h1.support_hub h₃ hab).trans (h1.support_hub h₄ hbb).symm)
    · rcases (show r ∈ ({a, b} : Set Shat) by rw [← hcap, hl₁.2.2.2]; exact .inr rfl) with rfl | rfl
      · exact hrH hab
      · exact hrH hbb
    · rcases (show r ∈ ({a, b} : Set Shat) by rw [← hcap, hl₂.2.2.2]; exact .inl rfl) with rfl | rfl
      · exact hrH hab
      · exact hrH hbb
    · obtain ⟨h₃, h₄⟩ := D.ends_mem_support K₂ h' hcap
      exact hne ((h2.support_hub h₃ hab).trans (h2.support_hub h₄ hbb).symm)
  have hthe : ∃ Z : Drawing Shat, TwoPaths D.rad.G H P Z O h₁ h₂ := by
    have base : TwoPaths D.rad.G H F₁ F₂ O h₁ h₂ := by
      refine ⟨hne12, hcH.1, ⟨hs₁, hF₁⟩, ⟨hs₂, hF₂⟩, ?_, ?_, hV₁₂.le, hE₁₂, hOp, hm₁, hm₂⟩
      · have := Drawing.sup_V hs₁ hs₂
        rwa [hsup] at this
      · have := Drawing.sup_E hs₁ hs₂
        rwa [hsup] at this
    rcases path_of_circuit hne12 hF₁ hF₂ hs₁ hs₂ hV₁₂ hE₁₂ hUH hP with rfl | rfl
    · exact ⟨F₂, base⟩
    · exact ⟨F₁, base.swap⟩
  obtain ⟨Z, ht⟩ := hthe
  have hDsup : Dv = D.rad.G.sup O P := by
    refine eq_of_U_eq hDv.1 (Drawing.sup_isSubdrawing _ _ _) ?_
    rw [hDU, hbd', ht.swap.U_right]
  by_contra hlarge
  push Not at hlarge
  have hDcard : Dv.E.ncard ≤ O.E.ncard + P.E.ncard := by
    rw [hDsup, Drawing.sup_E hOp.1 (hP.1.trans hcH.1)]
    exact ncard_union_le _ _
  have hle : O.E.ncard ≤ P.E.ncard := by omega
  have hlt' : O.E.ncard < P.E.ncard := by omega
  obtain ⟨Δ₂, hins₂, -, hsecond, -⟩ := theorem_8_5_proof χ.isSurface
    D.P.fits.internally_three_connected D.tb D.isTangle h𝒯' hins hd ht hle
    (fun h' ↦ absurd h' hlt'.ne)
  obtain rfl : Δ₂ = D.ins (D.rad.G.sup O Z) := D.eq_ins_of_isInsOf hins₂
  have hv₁O : v₁ ∈ O.U := O.V_subset_U ((hOV v₁).mpr (.inr (.inl rfl)))
  have hout : ∀ {v : Shat}, v ∈ discBd W → v ∉ D.ins H \ H.U := fun hv ↦ hW.bd_not_strict hcH hlt
    hinsW hv
  have hnotsub : ¬ O.U ⊆ D.ins H := by
    intro hs
    exact hout h1.2.v_mem.2 ⟨hs hv₁O, fun h' ↦ (hHW h').2 h1.2.v_mem.2⟩
  have hmeet := hsecond hnotsub
  -- The outer path meets `ins(H)` in its ends only.
  have hOi : O.U ∩ D.ins H = {h₁, h₂} := by
    exact outer_path_inter_hub_inside h1 h2 hHW hrH hcH hlt hUi R hRs hsupR O hO hOp
      hOV hm₁ hm₂ (fun hv ↦ hout hv)
  have hOW : O.U ⊆ W := by
    have : O.U ⊆ discBd Δv := by
      rw [hbd']
      exact subset_union_left
    exact this.trans ((Surface.discBd_subset Δv).trans hΔW)
  have hA := isLine_of_isPathBetween ht.left.2 hne12
  have hB := isLine_of_isPathBetween ht.right.2 hne12
  have hL := isLine_of_isPathBetween hOp.2 hne12
  have hAB : P.U ∪ Z.U = discBd (D.ins H) := by
    rw [(D.ins_spec hcH hlt).2.2.2.1, ht.U_eq]
  have hAB' : P.U ∩ Z.U = {h₁, h₂} := by
    rw [U_inter_of_disjoint ht.left.1 ht.right.1 ht.disj_E]
    refine Subset.antisymm ht.inter_V ?_
    rintro x (rfl | rfl)
    · exact ⟨ht.mem_V₁.1, ht.swap.mem_V₁.1⟩
    · exact ⟨ht.mem_V₁.2, ht.swap.mem_V₁.2⟩
  obtain ⟨W', hW'W, hW', hss, hb⟩ := exists_larger_disc hT hW.is_disc
    (D.ins_spec hcH hlt).2.2.1 hinsW hOW hA hB hL hAB hAB' hOi
  rcases hb with hb | hb
  · have heq := hW.disc_eq hW' hΔ hW'W hΔW (by rw [hb, hbd'])
    exact hnot (heq ▸ hss.1)
  · have hc₂ : Drawing.IsCircuitOf (D.rad.G.sup O Z) D.rad.G := ⟨Drawing.sup_isSubdrawing _ _ _,
      ht.left_circuit⟩
    have hcard₂ : (D.rad.G.sup O Z).E.ncard ≤ 4 * ρ + 4 := by
      have e₁ : H.E.ncard = P.E.ncard + Z.E.ncard := by
        rw [ht.union_E, ncard_union_eq ht.disj_E P.finite_edges Z.finite_edges]
      rw [Drawing.sup_E hOp.1 ht.sub₂]
      have := ncard_union_le O.E Z.E
      omega
    have heq : W' = D.ins (D.rad.G.sup O Z) := hW.eq_ins_of_disc hc₂ hcard₂ hW' hW'W
      (by rw [hb, ht.U_right])
    rw [← heq] at hmeet
    obtain ⟨e, he⟩ := ht.exists_edge
    obtain ⟨z, hz⟩ := ((hP.1.trans hcH.1).2 he).2.2.1.nonempty
    have hzi : z ∈ W' ∩ D.ins H := by
      have : z ∈ D.ins H := hUi (hP.1.U_subset (P.closure_subset_U he (subset_closure hz)))
      exact ⟨hss.1 this, this⟩
    rw [hmeet] at hzi
    have hzG : z ∉ D.rad.G.V := ((hP.1.trans hcH.1).2 he).2.1 hz |>.2
    obtain ⟨e', he', hze'⟩ := Z.exists_edge_of_mem hzi fun h' ↦ hzG (ht.sub₂.1 h')
    obtain rfl := D.rad.G.edge_eq_of_mem ((hP.1.trans hcH.1).2 he) (ht.sub₂.2 he') hz hze'
    exact disjoint_left.mp ht.disj_E he he'

/-- **Graph Minors XIX, (13.5)** (page 368): "With notation as above, $|E(D_v)| \le 4\rho + 4$, and
$ins(D_v) = \Delta_v$." The hypotheses on `W` are those of
(13.1). -/
theorem theorem_13_5_proof (hW : D.IsWheelHubOfRadius W H ρ) (hbdS : discBd W ⊆ cap.emb ''
  (univ \ bd S))
    (hin : ((W \ discBd W) ∩ (cap.emb '' D.Γ.V)).Nonempty) {Δv : Set Shat} {Dv : Drawing Shat}
      (hs : D.IsBoundarySector W H r Δv Dv) :
    Dv.E.ncard ≤ 4 * ρ + 4 ∧ D.ins Dv = Δv := by
  have : ConnectedSpace Shat := cap.connected
  suffices hle : Dv.E.ncard ≤ 4 * ρ + 4 from
    ⟨hle, (hW.eq_ins_of_disc hs.Dv_circuit hle hs.is_disc hs.Δv_sub hs.Dv_U.symm).symm⟩
  obtain ⟨v₁, v₂, h₁, h₂, f₁, f₂, S₁, S₂, hne, hf₁, -, hf₁', hf₂, -, hf₂', hS₁, hS₂, hcase⟩
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
  · rw [walkDrawing_V] at hx₁ hx₂
    obtain rfl := h1.same_end h2 hx₁ hx₂
    obtain ⟨u, A₁, A₂, T, rfl, rfl, -, hmeet⟩ := h1.merge h2 hx₁ hx₂
    have hfan : D.IsFan W H ρ r f₁ f₂ A₁ A₂ T :=
      ⟨hW, hbdS, hin, hs.rstar_mem.1, hs.rstar_mem.2, hne, hl₁, hl₂, h1, h2, fun y h₁ h₂ ↦ hmeet y
        h₁
        ((GraphWalk.mem_support_append A₂ T).mpr (.inl h₂))⟩
    obtain ⟨C, hC⟩ := hfan.exists_circuit
    have heq : Dv = C := eq_of_U_eq hs.Dv_circuit.1 hC.circuit.1 (by rw [hs.Dv_U, hbd,
      hfan.closure_formula hC])
    have := (hfan.card_lt hC).1
    rw [heq]
    omega
  · refine sector_of_disjoint hW hbdS hin hs.rstar_mem h1 h2 hl₁.symm hl₂
      (fun x h₃ h₄ ↦ ?_) hP hs.is_disc hs.Δv_sub
      hs.Dv_circuit hs.Dv_U hbd hnot
    rw [walkDrawing_V, walkDrawing_V] at hdisj
    exact disjoint_left.mp hdisj h₃ h₄

end TangleDatum

end GraphMinor.GM19
