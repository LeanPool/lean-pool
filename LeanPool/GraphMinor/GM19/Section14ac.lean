/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section14ab

/-!
# Graph Minors XIX, Section 14: the edges of `M(Γ, ℒ)` in `Σ'`

An edge of `M(Γ, ℒ)` misses all the wheels. So it is an internal edge of `Γ'`, and each internal
edge of `Γ'` comes from an edge of `M(Γ, ℒ)`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11 TangleDatum

universe w

variable {S Shat : Type} [TopologicalSpace S] [TopologicalSpace Shat] [T2Space S] [T2Space Shat] {α
  : Type w}
  {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

namespace Slice

variable {T : Set S} {D : TangleDatum cap χ} (s : Slice T D)
include s

/-- An edge of `M(Γ, ℒ)` misses each wheel. -/
theorem off_wheels {e : Set S} (he : e ∈ (coverLoc s.𝒲 s.cut.finite s.cut.disj s.fr).M.edgeSet) {x
  : S} (hx : x ∈ e) (W : ↥s.𝒲) : cap.emb x ∉ W.1 := by
  have hT := cap.isClosedSurface
  intro hin
  have hE : e ∈ D.P.Γ.E := he.1
  have hoff : ∀ A ∈ (s.fr W).arms, ∀ Δ X, IsDiscArm (s.fr W) A Δ X → cap.emb x ∉ discInt Δ
    := fun A hA Δ X hd hi ↦ by
    have hc : e ∈ A.compl.edgeSet := he.2 A (mem_iUnion.mpr ⟨W, hA⟩)
    rw [hd.compl] at hc
    have h₁ : cap.emb x ∈ closure Δᶜ := hc.2.1 hx
    rw [closure_compl_disc hT hd.disc] at h₁
    exact h₁ hi
  have hG : cap.emb x ∉ D.rad.G.U := fun hU ↦ by
    have hV : cap.emb x ∈ D.P.Γ.hatV cap := by
      rw [← D.rad.isPreRadial.1]
      exact ⟨⟨x, (hE.2.1 hx).1, rfl⟩, hU⟩
    obtain ⟨v, hv, e'⟩ := hV
    exact (hE.2.1 hx).2 ((cap.isEmbedding.injective e') ▸ hv)
  have hHU : (s.fr W).H.U ⊆ D.rad.G.U := (s.fr W).hW.H_sub.U_subset
  by_cases hA : cap.emb x ∈ (s.fr W).sp.A
  · rcases hA with hh | hu
    · rcases (s.fr W).hW.hub_cases with ⟨z, -, hU, hz⟩ | ⟨-, -, hc, hz⟩
      · rw [hz] at hh
        exact hG (hHU (hU ▸ hh))
      · rw [hz] at hh
        by_cases hb : cap.emb x ∈ discBd (D.ins (s.fr W).H)
        · obtain ⟨-, -, hi⟩ := (s.fr W).hub_data hc
          exact hG (hHU (hi.2.2.2.1 ▸ hb))
        · exact hoff _ (.inr ⟨hc, rfl⟩) _ _ ((s.fr W).hubArm_disc hc) ⟨hh, hb⟩
    · obtain ⟨v, hv⟩ := mem_iUnion.mp hu
      exact hG ((walkDrawing_isSubdrawing D.rad.G _).U_subset hv)
  · obtain ⟨i, hi, hΔ⟩ := (s.fr W).cover_lt hin hA
    by_cases hb : cap.emb x ∈ discBd ((s.fr W).sec i).Δ
    · rw [← ((s.fr W).sec i).full.C_U] at hb
      exact hG (((s.fr W).sec i).full.circuit.1.U_subset hb)
    · exact hoff _ (.inl ⟨i, hi, rfl⟩) _ _ ((s.fr W).secArm_disc i) ⟨hΔ, hb⟩

omit s in
/-- The edge of `Γ` with a given lift. -/
def up (s : Slice T D) (c : Set ↥Tᶜ) : Set S := s.f '' (Subtype.val '' c)

omit s in
/-- The lift of an edge of `Γ`. -/
def down (s : Slice T D) (e : Set S) : Set ↥Tᶜ := Subtype.val ⁻¹' (s.f.symm '' e)

theorem up_inj {c c' : Set ↥Tᶜ} (h : s.up c = s.up c') : c = c' :=
  (Subtype.val_injective.image_injective) (s.f.injective.image_injective h)

variable [Nonempty ↥Tᶜ]

/-- An edge of `M(Γ, ℒ)` is an internal edge of `Γ'`. -/
theorem down_mem (ε : Set ↥Tᶜ → Bool) {e : Set S} (he : e ∈ (coverLoc s.𝒲 s.cut.finite s.cut.disj
  s.fr).M.edgeSet) :
    s.down e ∈ (s.paint ε).E ∧ Painting.IsInternal (s.down e) ∧ s.up (s.down e) = e := by
  have hE : e ∈ D.P.Γ.E := he.1
  have he' : s.f.symm '' e ∈ s.Q.Γ.E := by
    change _ ∈ (D.P.Γ.push s.f.symm).E
    rw [push_E]
    exact ⟨e, hE, rfl⟩
  have hoffT : ∀ x ∈ e, s.f.symm x ∈ Tᶜ := fun x hx hT ↦ by
    have hT' : s.f.symm x ∈ cutT (cap.emb ∘ s.f) s.𝒲 := (Set.ext_iff.mp s.hT _).mpr hT
    obtain ⟨W, hW, hi⟩ := mem_iUnion₂.mp hT'
    have hi' : cap.emb (s.f (s.f.symm x)) ∈ discInt W := hi
    rw [s.f.apply_symm_apply] at hi'
    exact s.off_wheels he hx ⟨W, hW⟩ (Surface.discInt_subset _ hi')
  have hb : ¬ Painting.IsBorder (s.f.symm '' e) := by
    rintro ⟨_, ⟨x, hx, rfl⟩, hxb⟩
    exact hoffT x hx (s.bd_sub_T hxb)
  obtain ⟨x, hx⟩ := hE.1
  have hne : (Subtype.val ⁻¹' (s.f.symm '' e) : Set ↥Tᶜ).Nonempty := ⟨⟨s.f.symm x, hoffT x hx⟩, x,
    hx, rfl⟩
  refine ⟨(s.fd.mem_paint_E _).mpr (.inr ⟨_, he', hb, hne, rfl⟩), ?_, ?_⟩
  · refine disjoint_left.mpr ?_
    rintro y ⟨z, hz, ez⟩ hyb
    obtain ⟨W, hW, hi⟩ := mem_iUnion₂.mp (s.mem_bd.mp hyb)
    have hi' : cap.emb (s.f y.1) ∈ discBd W := hi
    rw [← ez, s.f.apply_symm_apply] at hi'
    exact s.off_wheels he hz ⟨W, hW⟩ (Surface.discBd_subset _ hi')
  · have hsub : s.f.symm '' e ⊆ range (Subtype.val : ↥Tᶜ → S) := by
      rintro _ ⟨z, hz, rfl⟩
      exact ⟨⟨_, hoffT z hz⟩, rfl⟩
    rw [up, down, image_preimage_eq_of_subset hsub, image_image]
    simp

/-- An internal edge of `Γ'` comes from an edge of `Γ`. -/
theorem internal_up (ε : Set ↥Tᶜ → Bool) {e₁ : Set ↥Tᶜ} (he₁ : e₁ ∈ (s.paint ε).E)
  (hi : Painting.IsInternal e₁) :
    s.up e₁ ∈ D.P.Γ.E ∧ (∀ (col : ↥s.𝒲 → ℕ → α) (a₀ : α) (Z : Set ↥Tᶜ), s.cutφ col a₀ Z e₁ = D.P.φ
      (s.up e₁)) ∧ (tilde (s.up e₁)).ncard = (tilde e₁).ncard ∧
      D.P.Γ.γ (s.up e₁) = ((s.paint ε).γ e₁).map (fun x ↦ s.f x.1) ∧ ∀ x ∈ tilde e₁, s.f x.1 ∈
        tilde (s.up e₁) := by
  classical
  obtain ⟨e₂, he₂, hb, hne, rfl⟩ := s.fd.exists_lift_of_internal _ he₁ hi
  have hsub := s.fd.pull.subset_R he₂ hb hne
  have hsur : Subtype.val '' (Subtype.val ⁻¹' e₂ : Set ↥Tᶜ) = e₂ := image_preimage_eq_of_subset
    (hsub.trans (image_subset_range _ _))
  have hE : e₂ ∈ (D.P.Γ.push s.f.symm).E := he₂
  rw [push_E] at hE
  obtain ⟨c, hc, rfl⟩ := hE
  have hff : s.f '' (s.f.symm '' c) = c := by
    rw [image_image]
    simp
  have hup : s.up (Subtype.val ⁻¹' (s.f.symm '' c)) = c := by rw [up, hsur, hff]
  rw [hup]
  refine ⟨hc, fun col a₀ Z ↦ ?_, ?_, ?_, ?_⟩
  · rw [cutφ, ite_eq_left hi, hsur]
    exact s.isImage.φ c hc
  · rw [s.fd.pull.ncard_tilde he₂ hsub, ncard_tilde_image]
  · have h₁ := (s.fd.map_march_lift (flip := flipOf ε) he₂ hb hne).trans (s.isImage.γ c hc)
    have h₂ := congrArg (List.map s.f) h₁
    simp only [List.map_map] at h₂
    have h₃ : List.map (s.f ∘ s.f.symm) (D.P.Γ.γ c) = D.P.Γ.γ c := by
      have : (s.f ∘ s.f.symm : S → S) = id := by
        funext z
        simp
      rw [this, List.map_id]
    rw [h₃] at h₂
    exact h₂.symm
  · intro x hx
    have h₁ : x.1 ∈ tilde (s.f.symm '' c) := by
      rw [← s.fd.pull.frag.image_tilde_preimage hsub]
      exact mem_image_of_mem _ hx
    rw [tilde_image_homeo] at h₁
    obtain ⟨z, hz, ez⟩ := h₁
    have : s.f x.1 = z := by
      rw [← ez]
      simp
    rw [this]
    exact hz

omit [Nonempty ↥Tᶜ] in
/-- An edge of `Γ` with a lift is an edge of `M(Γ, ℒ)`. -/
theorem up_mem_M {c : Set ↥Tᶜ} (hc : s.up c ∈ D.P.Γ.E) : s.up c ∈ (coverLoc s.𝒲 s.cut.finite
  s.cut.disj s.fr).M.edgeSet := by
  have hT := cap.isClosedSurface
  have hcl : IsClosed (s.f '' Tᶜ) := s.f.isClosed_image.mpr s.facts.1
  have hsub : closure (s.up c) ⊆ s.f '' Tᶜ := closure_minimal (by
    rintro _ ⟨_, ⟨x, -, rfl⟩, rfl⟩
    exact ⟨x.1, x.2, rfl⟩) hcl
  refine ⟨hc, fun A hA ↦ ?_⟩
  obtain ⟨W, hW⟩ := mem_iUnion.mp hA
  obtain ⟨Δ, X, hd⟩ := (s.fr W).exists_disc hW
  have key : ∀ x ∈ closure (s.up c), cap.emb x ∈ closure Δᶜ := by
    intro x hx
    rw [closure_compl_disc hT hd.disc]
    obtain ⟨z, hz, rfl⟩ := hsub hx
    intro hi
    have hW' : cap.emb (s.f z) ∈ W.1 := hd.sub (.inl (Surface.discInt_subset _ hi))
    have hbd := discInt_off_bd hT (s.cut.disc W W.2) hd.disc (subset_union_left.trans hd.sub) hi
    have hr : cap.emb (s.f z) ∈ range s.e := ⟨⟨z, hz⟩, rfl⟩
    rw [s.range_e] at hr
    exact hr (mem_iUnion₂.mpr ⟨W, W.2, hW', hbd⟩)
  rw [hd.compl]
  exact ⟨hc, fun x hx ↦ key x (subset_closure hx), fun x hx ↦ key x hx.1.1⟩

end Slice

namespace CutPair

variable {T : Set S} {Da Db : TangleDatum cap χ} [Nonempty ↥Tᶜ] {sa : Slice T Da} {sb : Slice T Db}
  {ε : Set ↥Tᶜ → Bool} {Φ' : Frame ↥Tᶜ} {Z : Set ↥Tᶜ}
  {σv : ↥Tᶜ → Set ↥Tᶜ} {σe : Set ↥Tᶜ → Set ↥Tᶜ} {β : Type*} {Ω : QuasiOrder β} {ξa : Arm Da.P.Γ
    → β} {ξb : Arm Db.P.Γ → β} {cola : ↥sa.𝒲 → ℕ → α} {colb : ↥sb.𝒲 → ℕ
      → α} {a₀ : α} {Ωc : QuasiOrder α}
  (h : CutPair sa sb ε Φ' Z σv σe Ω ξa ξb cola colb a₀ Ωc)
include h

theorem image_internal {e : Set ↥Tᶜ} (he : e ∈ (sa.paint ε).E) (hi : Painting.IsInternal e) :
  Painting.IsInternal (σe e) := by
  refine disjoint_left.mpr fun x hx hxb ↦ ?_
  obtain ⟨C, hC, hxC⟩ := sUnion_cuffs (S := ↥Tᶜ) ▸ hxb
  obtain ⟨y, hy, hyC⟩ := (h.infl.borders_iff e he C hC).mpr ⟨x, hx, hxC⟩
  obtain ⟨W, hW⟩ := sa.exists_wheel ⟨C, hC⟩
  exact disjoint_left.mp hi hy (sa.cf_sub_bd W.2 (hW ▸ hyC))

/-- The map on edges of `M(Γ, ℒ)`. -/
def _root_.GraphMinor.GM19.CutPair.edgeMap (_ : CutPair sa sb ε Φ' Z σv σe Ω ξa ξb cola colb a₀ Ωc)
  (e : Set S) : Set S := sb.up (σe (sa.down e))

theorem edge_facts {e : Set S} (he : e ∈ (coverLoc sa.𝒲 sa.cut.finite sa.cut.disj sa.fr).M.edgeSet)
  :
    h.edgeMap e ∈ (coverLoc sb.𝒲 sb.cut.finite sb.cut.disj sb.fr).M.edgeSet ∧ (tilde
      (h.edgeMap e)).ncard = (tilde e).ncard ∧ χ.unionLE (Da.P.φ e) (Db.P.φ (h.edgeMap e)) ∧
      ∀ (i : ℕ) (hi : i < (Da.P.Γ.γ e).length) (hi' : i < (Db.P.Γ.γ (h.edgeMap e)).length),
        Slice.Out sa sb σv (cap.emb (Db.P.Γ.γ (h.edgeMap e))[i]) (cap.emb (Da.P.Γ.γ e)[i]) := by
  obtain ⟨hE, hint, hup⟩ := sa.down_mem ε he
  have hEb := h.infl.edge_mem _ hE
  have hib := h.image_internal hE hint
  obtain ⟨c₁, φ₁, n₁, γ₁, -⟩ := sa.internal_up ε hE hint
  obtain ⟨c₂, φ₂, n₂, γ₂, -⟩ := sb.internal_up ε hEb hib
  rw [hup] at φ₁ n₁ γ₁
  refine ⟨sb.up_mem_M c₂, ?_, ?_, fun i hi hi' ↦ ?_⟩
  · change (tilde (sb.up _)).ncard = _
    rw [n₂, h.infl.edge_size _ hE, n₁]
  · have := h.le_int _ hE hint
    rwa [φ₁ cola a₀ Z, φ₂ colb a₀ Z] at this
  · have hl₁ : i < ((sa.paint ε).γ (sa.down e)).length := by
      rw [γ₁] at hi
      simpa using hi
    have hl₂ : i < ((sb.paint ε).γ (σe (sa.down e))).length := by
      have hi'' : i < (Db.P.Γ.γ (sb.up (σe (sa.down e)))).length := hi'
      rw [γ₂] at hi''
      simpa using hi''
    have hy := h.infl.ends _ hE i hl₁ hl₂
    have hmem : ((sa.paint ε).γ (sa.down e))[i] ∈ sa.N := by
      rw [← sa.paint_V ε]
      refine (sa.paint ε).tilde_subset_V hE ?_
      have := (sa.paint ε).γ_set _ hE
      exact this ▸ List.getElem_mem hl₁
    refine ⟨_, _, ?_, ?_, hmem, hy⟩
    · change _ = cap.emb (sa.f _)
      congr 1
      simp only [γ₁, List.getElem_map]
    · change _ = cap.emb (sb.f _)
      congr 1
      change (Db.P.Γ.γ (sb.up (σe (sa.down e))))[i] = _
      simp only [γ₂, List.getElem_map]

omit h in
/-- The edges of an inflation stay in `Out`. -/
theorem step_of_adj {x' u w : ↥Tᶜ} (hx : x' ∈ sa.N) (hu : u ∈ σv x') (hw : w ∈ σv x') (hadj :
  (sb.paint ε).skAdj.Adj u w) :
    OutStep sb.fr (Slice.Out sa sb σv) (sa.e x') (sb.e u) (sb.e w) := by
  obtain ⟨hne, huV, hwV, c, hc, huc, hwc⟩ := hadj
  refine ⟨⟨x', u, rfl, rfl, hx, hu⟩, ⟨x', w, rfl, rfl, hx, hw⟩, ?_⟩
  by_cases hi : Painting.IsInternal c
  · obtain ⟨-, -, -, -, ht⟩ := sb.internal_up ε hc hi
    have hN : ∀ {y}, y ∈ (sb.paint ε).V → sb.f y.1 ∈ Db.P.Γ.V := fun {y} hy ↦ by
      rw [sb.paint_V] at hy
      obtain ⟨v, hv, ev⟩ := (show sb.e y ∈ Db.P.Γ.hatV cap from hy)
      exact (cap.isEmbedding.injective ev) ▸ hv
    refine .inl ⟨_, _, rfl, rfl, fun e ↦ hne (Subtype.ext (sb.f.injective e)), hN huV, hN hwV, _,
      (sb.internal_up ε hc hi).1, ht _ huc, ht _ hwc⟩
  · have hb : Painting.IsBorder c := by
      by_contra hn
      exact hi (isInternal_iff_not_border.mpr hn)
    obtain ⟨W, q, hq, rfl⟩ := sb.exists_pos (sb.border_arc ε hc hb)
    rw [sb.tilde_arc] at huc hwc
    rcases huc with rfl | rfl <;> rcases hwc with rfl | rfl
    · exact absurd rfl hne
    · exact .inr ⟨W, q, hq, .inl ⟨sb.e_vx W q, sb.e_vx W (q + 1)⟩⟩
    · exact .inr ⟨W, q, hq, .inr ⟨sb.e_vx W (q + 1), sb.e_vx W q⟩⟩
    · exact absurd rfl hne

theorem outlineData : OutlineData sa.fr sb.fr (sa.wmap sb) (Slice.Out sa sb σv) h.Sym Ω ξa ξb := by
  have hwalk := h.rimWalk
  refine ⟨sa.wmap_bij sb, ?_, hwalk, fun _ _ _ h' ↦ h'.2, fun W hc ↦ (h.last_match W).2.2.2.2.2 hc,
    ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ _ _ ⟨x, y, rfl, rfl, hx, hy⟩ ⟨x', y', rfl, e, hx', hy'⟩
    obtain rfl := sb.isEmbedding.injective e
    rw [h.out_uniq hx hx' hy hy']
  · rintro _ _ ⟨x, y, rfl, rfl, hx, hy⟩
    refine ⟨?_, hx⟩
    have hV := h.infl.vertex_subset x (by rwa [sa.paint_V]) hy
    rw [sb.paint_V] at hV
    exact hV
  · rintro _ _ ⟨x, y, rfl, rfl, -, -⟩ W hi
    have hr : sb.e y ∈ range sb.e := ⟨y, rfl⟩
    rw [sb.range_e] at hr
    exact hr (mem_iUnion₂.mpr ⟨W.1, W.2, hi⟩)
  · rintro _ _ ⟨x, y, rfl, rfl, -, -⟩ W hi
    have hr : sa.e x ∈ range sa.e := ⟨x, rfl⟩
    rw [sa.range_e] at hr
    exact hr (mem_iUnion₂.mpr ⟨W.1, W.2, hi⟩)
  · intro x hx hoff
    have hr : x ∈ range sa.e := by
      rw [sa.range_e]
      intro hi
      obtain ⟨W, hW, hi⟩ := mem_iUnion₂.mp hi
      exact hoff ⟨W, hW⟩ hi
    obtain ⟨x', rfl⟩ := hr
    have hN : x' ∈ sa.N := hx
    obtain ⟨y, hy⟩ := h.infl.vertex_nonempty x' (by rwa [sa.paint_V])
    exact ⟨sb.e y, x', y, rfl, rfl, hN, hy⟩
  · rintro _ _ _ ⟨x, y, rfl, rfl, hx, hy⟩ ⟨x', y', e, rfl, hx', hy'⟩
    obtain rfl := sa.isEmbedding.injective e
    have hconn := h.infl.vertex_connected x (by rwa [sa.paint_V])
    have hr := hconn ⟨y, hy⟩ ⟨y', hy'⟩
    rw [SimpleGraph.reachable_iff_reflTransGen] at hr
    exact hr.lift (fun u : ↥(σv x) ↦ sb.e u.1) fun u w hadj ↦
      step_of_adj (sa := sa) (sb := sb) (ε := ε) hx u.2 w.2 hadj

/-- **The outline given by an inflation.** -/
theorem exists_outline (hd : χ.IsDisjoint) : ∃ τ : Arm Da.P.Γ → Arm Db.P.Γ,
    IsOutline (⟨hd, Da.P, coverLoc sa.𝒲 sa.cut.finite sa.cut.disj sa.fr⟩ : Place χ) ⟨hd, Db.P,
      coverLoc sb.𝒲 sb.cut.finite sb.cut.disj sb.fr⟩ τ ∧
      ∀ A ∈ (coverLoc sa.𝒲 sa.cut.finite sa.cut.disj sa.fr).arms, Ω.le (ξa A) (ξb (τ A)) := by
  refine h.outlineData.exists_outline hd sa.cut.finite sa.cut.disj sb.cut.finite sb.cut.disj
    h.edgeMap (fun e he ↦ (h.edge_facts he).1) (fun e he ↦ (h.edge_facts he).2.1) ?_
      (fun e he i hi hi' ↦ (h.edge_facts he).2.2.2 i hi hi') (fun e he ↦ (h.edge_facts he).2.2.1)
  intro e he e' he' heq
  obtain ⟨hE, -, hup⟩ := sa.down_mem ε he
  obtain ⟨hE', -, hup'⟩ := sa.down_mem ε he'
  have h₁ := sb.up_inj heq
  have h₂ := h.infl.edge_injOn hE hE' h₁
  rw [← hup, ← hup', h₂]

end CutPair

end GraphMinor.GM19
