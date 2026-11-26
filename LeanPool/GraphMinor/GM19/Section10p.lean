/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section10o

/-!
# The second bullet of the distance flaw

A short circuit with one pole inside, and a line from it to the cuff of another pole.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10

universe w

/-- The first step of a walk between two distinct vertices. -/
theorem walk_first_step {α β : Type*} {G : Graph α β} {a b : α} (W : GraphWalk G a b)
  (hW : W.IsSimple) (hab : a ≠ b) :
    ∃ e y, G.IsLink e a y ∧ y ∈ W.support ∧ y ≠ a := by
  cases W with
  | nil h => exact absurd rfl hab
  | @cons _ x _ e h r =>
    have hsim : (GraphWalk.cons h r).support.Nodup := hW
    simp only [GraphWalk.support_cons, List.nodup_cons] at hsim
    refine ⟨e, x, h, by simp [GraphWalk.support_cons, r.start_mem_support],
      fun hx ↦ hsim.1 (hx ▸ r.start_mem_support)⟩

/-- The number of vertices of a walk. -/
theorem ncard_walk_V {T : Type} [TopologicalSpace T] [T2Space T] (G : Drawing T) {u v : T}
  (W : GraphWalk G.toGraph u v) :
    (walkDrawing G W).V.ncard ≤ W.length + 1 := by
  classical
  rw [walkDrawing_V]
  have : {x | x ∈ W.support} = ↑W.support.toFinset := by
    ext x
    simp
  rw [this, ncard_coe_finset]
  exact (List.toFinset_card_le _).trans (length_support W).le

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {cap : IsCappedSurface S Shat} {β : Type w} {χ : ColourScheme S β}


namespace TangleDatum

variable {D : TangleDatum cap χ}

variable (hS : IsSurface S) (h3 : D.P.Γ.IsInternallyThreeConnected)
include hS h3

/-- **The second shape**, from a drawing `P` of the circuit and the line. -/
theorem outer_of_line [Nonempty S] {n : ℕ} (_hn₁ : 1 ≤ n) (hn : n < D.rep) {C : Drawing Shat}
  (hC : C.IsCircuitOf D.rad.G) (hc : C.E.ncard ≤ 2 * n)
    (hlink : GM18.IsLambdaLinkedTo D.tb.lambdaOrder D.𝒯 (partIn cap D.P.Γ (D.ins C))
      (partIn cap D.P.Γ (closure (D.ins C)ᶜ)))
    {r p : Shat} (hr : r ∈ D.rad.poles) (hri : r ∈ D.ins C) (hp : p ∈ D.rad.poles) (hrp : r ≠ p)
      (hpi : p ∉ D.ins C) (hrange : C.U ⊆ range cap.emb)
    {Θ : Set S} (hΘ : Θ ∈ cuffs S) (hreg : D.rad.regionOf p = cap.cuffDisc Θ)
    (hO : IsOArc (cap.emb ⁻¹' C.U)) {a b : S} (hab : a ≠ b) (ha : a ∈ cap.emb ⁻¹' C.U ∩ D.P.Γ.V)
      (hb : b ∈ cap.emb ⁻¹' C.U ∩ D.P.Γ.V)
    {L : Set S} {s u : S} (hL : (L = {u} ∧ s = u) ∨ IsLineWithEnds L s u) {P : Drawing Shat}
      (hPs : P.IsSubdrawing D.rad.G) (hPr : P.U ⊆ range cap.emb)
    (hPi : ∀ v ∈ P.V, ∃ e ∈ P.E, v ∈ closure e) (hPU : P.U = C.U ∪ cap.emb '' L)
      (hLi : cap.emb '' L ∩ D.ins C = {cap.emb u})
    (hLbd : L ∩ bd S ⊆ {s}) (hCbd : C.U ∩ cap.emb '' bd S ⊆ {cap.emb u})
      (hsize : P.V.ncard + P.E.ncard ≤ 8 * n) (huC : cap.emb u ∈ C.U) (hsΘ : s ∈ Θ)
    (hsV : s ∈ D.P.Γ.V) : ∃ 𝓓 K, IsOuterData D n 𝓓 K := by
  classical
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hj := cap.isClosedEmbedding hS
  have hlt : C.E.ncard < 2 * D.rep := by omega
  have hi := D.ins_spec hC hlt
  have hbd : discBd (D.ins C) = C.U := hi.2.2.2.1
  have hfr : frontier (D.ins C) = C.U := by rw [IsClosedDisc.frontier_eq_discBd hT hi.2.2.1, hbd]
  obtain ⟨hinter, hfeat, hlines, hcV, hcE⟩ := comap_facts D.rad D.P.fits hPs hPr hj hPi
  set K : Drawing S := GM19.Drawing.comap P hj hPr with hKdef
  have hKU : cap.emb '' K.U = P.U := image_preimage_eq_of_subset hPr
  have hmemK : ∀ {x}, x ∈ K.U ↔ cap.emb x ∈ C.U ∨ x ∈ L := fun {x} ↦ by
    change cap.emb x ∈ P.U ↔ _
    rw [hPU]
    refine or_congr Iff.rfl ⟨?_, mem_image_of_mem _⟩
    rintro ⟨y, hy, hxy⟩
    exact cap.isEmbedding.injective hxy ▸ hy
  obtain ⟨Θ', hΘ', hreg', hrd⟩ := D.rad.pole_cases hr
  have hΘne : Θ ≠ Θ' := by
    rintro rfl
    obtain ⟨-, -, hG3, -⟩ := id D.rad.isPreRadial
    have m₁ := D.rad.regionOf_mem hr.1
    have m₂ := D.rad.regionOf_mem hp.1
    exact hrp ((hG3 _ m₁.1).unique ⟨m₁.2, hr.1.1⟩ ⟨(hreg'.trans hreg.symm) ▸ m₂.2, hp.1.1⟩)
  have huL : u ∈ L := by
    rcases hL with ⟨rfl, -⟩ | hl
    · rfl
    · exact GM11.IsLineWithEnds.right_mem hl
  have hring : ∀ {x w : S}, cap.emb x ∈ C.U → x ≠ w → ∃ E ⊆ K.U \ {w}, x ∈ E ∧ IsPreconnected E ∧
    (E ∩ D.P.Γ.V).Nonempty := fun {x w} hx hne ↦ by
    obtain ⟨E, hE, hxE, hconn, hm⟩ := ring_part hO ha hb hab hx hne
    exact ⟨E, hE.trans (sdiff_subset_sdiff_left fun z hz ↦ hmemK.2 (Or.inl hz)), hxE, hconn, hm⟩
  refine ⟨{D.ins C}, K, Or.inr (Or.inl ⟨D.ins C, L, s, u, Θ, Θ', rfl, hi.2.2.1,
    hbd.trans_subset hrange, hΘ, hΘ', hΘne, hsΘ, hL, ?_, hLi, hLbd, ?_, ?_, ⟨r, hrd, hri⟩⟩),
    finite_singleton _, by simp, ?_, hfeat, hinter, hlines, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hKU, hPU, hbd]
  · rwa [hbd]
  · exact D.cuffDisc_disjoint_ins hC hlt hrange hp hΘ hreg hpi
  · refine family_of_discs (finite_singleton _) (by rintro _ rfl; exact hlink) ?_ ?_
    · rintro _ rfl
      have := disc_order hS h3 D.rad hC hi.2.2.1 hbd
      omega
    · rintro _ rfl _ rfl h
      exact (h rfl).elim
  · rw [hcV, hcE]
    exact hsize
  · rcases hL with ⟨rfl, -⟩ | hl
    · refine ⟨{cap.emb ⁻¹' C.U}, ∅, finite_singleton _, finite_empty, by rintro _ rfl; exact hO, by
        simp, ?_⟩
      ext x
      rw [hmemK]
      simp only [sUnion_singleton, sUnion_empty, union_empty, mem_preimage]
      refine ⟨?_, Or.inl⟩
      rintro (h | h)
      · exact h
      · rw [mem_singleton_iff.1 h]
        exact huC
    · refine ⟨{cap.emb ⁻¹' C.U}, {L}, finite_singleton _, finite_singleton _, ?_, ?_, ?_⟩
      · rintro _ rfl
        exact hO
      · rintro _ rfl
        refine ⟨s, u, ?_, hl, Or.inl (cuff_subset_bd ⟨Θ, hΘ⟩ hsΘ), Or.inr ?_⟩
        · intro h
          obtain ⟨f, h₀, h₁⟩ := hl
          have := f.injective (Subtype.ext (h₀.trans (h.trans h₁.symm)))
          exact zero_ne_one this
        · simpa using huC
      · ext x
        rw [hmemK]
        simp
  · rintro _ rfl v hv h₁ h₂
    have : cap.emb v ∈ frontier (D.ins C) := by
      rw [frontier_eq_closure_inter_closure]
      exact ⟨subset_closure h₁, h₂⟩
    rw [hfr] at this
    exact hmemK.2 (Or.inl this)
  · rintro v hv _ rfl
    rcases hmemK.1 hv with h | h
    · have : cap.emb v ∈ frontier (D.ins C) := hfr ▸ h
      rw [frontier_eq_closure_inter_closure] at this
      exact this.2
    · by_cases hvi : cap.emb v ∈ D.ins C
      · have hvu : cap.emb v ∈ cap.emb '' L ∩ D.ins C := ⟨mem_image_of_mem _ h, hvi⟩
        rw [hLi] at hvu
        rw [mem_singleton_iff.1 hvu]
        have : cap.emb u ∈ frontier (D.ins C) := hfr ▸ huC
        rw [frontier_eq_closure_inter_closure] at this
        exact this.2
      · exact subset_closure hvi
  · intro w x hx hne
    rcases hmemK.1 hx with h | h
    · exact hring h hne
    · rcases hL with ⟨rfl, -⟩ | hl
      · exact hring (by rw [mem_singleton_iff.1 h]; exact huC) hne
      · refine line_anchor hl (fun z hz ↦ hmemK.2 (Or.inr hz)) (fun w' hne' ↦ ?_)
          (fun w' hne' ↦ hring huC hne') h hne
        refine ⟨{s}, ?_, rfl, isPreconnected_singleton, ⟨s, rfl, hsV⟩⟩
        rintro _ rfl
        exact ⟨hmemK.2 (Or.inr (GM11.IsLineWithEnds.left_mem hl)), hne'⟩

/-- **The second shape.** A short circuit in `Σ` with a pole `r` inside, on a short closed walk that
meets the cuff of a pole `p ≠ r`. -/
theorem outer_of_disc_point [Nonempty S] {n : ℕ} (hn₁ : 1 ≤ n) (hn : n < D.rep) (hd :
  ((n + 2 : ℕ) : ℕ∞) < 2 * Painting.dist D.rad)
    (hNP : ¬ ∃ C, D.IsPairCircuit n C) {C : Drawing Shat} (hC : C.IsCircuitOf D.rad.G)
      (hc : C.E.ncard ≤ 2 * n)
    (hlink : GM18.IsLambdaLinkedTo D.tb.lambdaOrder D.𝒯 (partIn cap D.P.Γ (D.ins C))
      (partIn cap D.P.Γ (closure (D.ins C)ᶜ)))
    {r p : Shat} (hr : r ∈ D.rad.poles) (hri : r ∈ D.ins C) (hnp : ∀ z ∈ C.V, z ∉ D.rad.poles)
      (hp : p ∈ D.rad.poles) (hrp : r ≠ p)
    {Θ : Set S} (hΘ : Θ ∈ cuffs S) (hreg : D.rad.regionOf p = cap.cuffDisc Θ) {u₀ : Shat}
      (Z : GraphWalk D.rad.G.toGraph u₀ u₀) (hZ : Z.length ≤ 2 * n)
    (hZC : ∀ x ∈ C.V, x ∈ Z.support) {s₀ : S} (hs₀ : s₀ ∈ Θ) (hs₀Z : cap.emb s₀ ∈ Z.support) : ∃ 𝓓
      K, IsOuterData D n 𝓓 K := by
  classical
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hj := cap.isClosedEmbedding hS
  have hlt : C.E.ncard < 2 * D.rep := by omega
  have hpi : p ∉ D.ins C := fun h ↦ hNP ⟨C, hC, hc, r, hr, p, hp, hrp, hri, h⟩
  have hrange : C.U ⊆ range cap.emb := subset_range_of_no_pole D.rad hC.1 hnp
  have hpC : p ∉ C.V := fun h ↦ hnp p h hp
  have hl₀ : cuffLabel cap (cap.emb s₀) = some Θ := cuffLabel_emb hΘ hs₀
  have hsame : ∀ {x : Shat} {Θ' : Set S}, x ∈ Z.support → cuffLabel cap x = some Θ' → Θ' = Θ
    := fun hx hl ↦
    labels_eq hS h3 hd Z hZ hx hs₀Z hl hl₀
  have hbdC : ∀ {v : S}, v ∈ bd S → cap.emb v ∈ C.U → v ∈ D.P.Γ.V ∧ cap.emb v ∈ C.V ∧ v ∈ Θ
    := fun {v} hv hvC ↦ by
    obtain ⟨h₁, h₂, Θ', hΘ', hvΘ⟩ := D.rad.bd_point hC.1 hv hvC
    have := hsame (hZC _ h₂) (cuffLabel_emb hΘ' hvΘ)
    exact ⟨h₁, h₂, this ▸ hvΘ⟩
  have hone : ∀ {x y : S}, x ∈ bd S → y ∈ bd S → cap.emb x ∈ C.U → cap.emb y ∈ C.U → x = y
    := fun {x y} hx hy hxC hyC ↦ by
    by_contra hne
    obtain ⟨h₁, h₂, h₃⟩ := hbdC hx hxC
    obtain ⟨h₄, h₅, h₆⟩ := hbdC hy hyC
    exact no_double_touch hS h3 hn hNP hC hc hr hri hp hrp hpC hΘ hreg h₁ h₄ hne h₃ h₆ h₂ h₅
  obtain ⟨hO, a, b, hab, ha, hb⟩ := ring_marks hS h3 hC hlt hnp hone hr hri
  by_cases htouch : ∃ v, v ∈ Θ ∧ cap.emb v ∈ C.U
  · obtain ⟨v, hvΘ, hvC⟩ := htouch
    have hvb : v ∈ bd S := cuff_subset_bd ⟨Θ, hΘ⟩ hvΘ
    refine outer_of_line hS h3 hn₁ hn hC hc hlink hr hri hp hrp hpi hrange hΘ hreg hO hab ha hb (L
      := {v}) (s := v) (u := v) (Or.inl ⟨rfl, rfl⟩) hC.1 hrange
      (circuit_iso hC.2) ?_ ?_ ?_ ?_ ?_ hvC hvΘ (hbdC hvb hvC).1
    · rw [image_singleton, union_singleton, insert_eq_of_mem hvC]
    · rw [image_singleton]
      exact inter_eq_left.2 (singleton_subset_iff.2 (D.U_subset_ins hC hlt hvC))
    · exact inter_subset_left
    · rintro _ ⟨hx, w, hw, rfl⟩
      rw [hone hw hvb hx hvC]
      rfl
    · have := IsCircuit.ncard_V hC.2
      omega
  · push Not at htouch
    have hno : ∀ y, y ∈ closure (cap.cuffDisc Θ) → y ∉ D.ins C := fun y hy hyi ↦ by
      have hyC := D.cuff_inter_ins hC hlt hrange hp hΘ hreg hpi hy hyi
      rw [cap.closure_cuffDisc hΘ] at hy
      rcases hy with hy | ⟨w, hw, rfl⟩
      · exact cap.notMem_range hΘ hy (hrange hyC)
      · exact htouch w hw hyC
    have haV : cap.emb a ∈ C.V := mem_V_of_mem_U hC.1 ha.1 (D.rad.isPreRadial.2.1
      (mem_image_of_mem _ ha.2))
    obtain ⟨W, hWl, hWs, hWe⟩ := exists_half_walk Z (hZC _ haV) hs₀Z
    obtain ⟨a', ha', b', hb', T', hT'e, hT's, hA, hB⟩ := exists_crossing
      (D.ins C) {y | cuffLabel cap y = some Θ} W (D.U_subset_ins hC hlt ha.1) hl₀
    obtain ⟨R, hRs, hRsupp, hRe⟩ := GraphWalk.exists_isSimple T'
    have hne : a' ≠ b' := by
      rintro rfl
      exact hno a' (cuffLabel_some hb').2 ha'
    have hRin : ∀ x ∈ R.support, x ∈ Z.support := fun x hx ↦ hWs x (hT's x (hRsupp x hx))
    have hRA : ∀ x ∈ R.support, x ∈ D.ins C → x = a' := fun x hx ↦ hA x (hRsupp x hx)
    have hRB : ∀ x ∈ R.support, cuffLabel cap x = some Θ → x = b' := fun x hx ↦ hB x (hRsupp x hx)
    have ha'C : a' ∈ C.V := by
      obtain ⟨e, y, hl, hy, hya⟩ := walk_first_step R hRs hne
      exact D.exit_mem hC hlt hl ha' fun h ↦ hya (hRA y hy h)
    have hb'np : b' ∉ D.rad.poles := by
      intro hb'p
      obtain ⟨e, y, hl, hy, hya⟩ := walk_first_step R.reverse (by
        unfold GraphWalk.IsSimple
        rw [GraphWalk.support_reverse]
        exact List.nodup_reverse.2 hRs) hne.symm
      rw [GraphWalk.support_reverse] at hy
      have hy' : y ∈ R.support := List.mem_reverse.1 hy
      obtain ⟨v, hv, rfl, hset⟩ := D.rad.link_cases hl hb'p.1
      obtain ⟨-, hΘ₁, hreg₁⟩ := pole_of_label D.rad hb'p.1 hb'
      have hvΘ := (D.rad.pole_edge hl.1 hb'p hΘ hreg₁ hset).2
      exact hya (hRB _ hy' (cuffLabel_emb hΘ hvΘ))
    have hRnp : ∀ y ∈ R.support, y ∉ D.rad.poles := fun y hy hyp ↦ by
      obtain ⟨Θ', hΘ', -, hyd⟩ := D.rad.pole_cases hyp
      have hly := cuffLabel_eq hΘ' (subset_closure hyd)
      have := hsame (hRin y hy) hly
      subst this
      exact hb'np (hRB y hy hly ▸ hyp)
    have hb'V : b' ∈ D.rad.G.V := mem_V_of_mem_support R R.end_mem_support
    have hb'hat : b' ∈ D.P.Γ.hatV cap := by
      by_contra hn'
      exact hb'np (pole_of_label D.rad ⟨hb'V, hn'⟩ hb').1
    obtain ⟨s, hsV, rfl⟩ := hb'hat
    have hsΘ := (mem_cuff_of_label hb').2
    obtain ⟨u, rfl⟩ := hrange (C.V_subset_U ha'C)
    set Q := walkDrawing D.rad.G R with hQ
    have hQs : Q.IsSubdrawing D.rad.G := walkDrawing_isSubdrawing _ _
    have hQnp : ∀ z ∈ Q.V, z ∉ D.rad.poles := fun z hz ↦ hRnp z (by rwa [hQ, walkDrawing_V] at hz)
    have hQr : Q.U ⊆ range cap.emb := subset_range_of_no_pole D.rad hQs hQnp
    have hQL : cap.emb '' (cap.emb ⁻¹' Q.U) = Q.U := image_preimage_eq_of_subset hQr
    have hQset : Q.U = {x | x ∈ R.support} ∪ ⋃ e ∈ {e | e ∈ R.edges}, closure e := by
      ext x
      rw [hQ, mem_walkDrawing_U]
      simp
    have hline : IsLineWithEnds (cap.emb '' (cap.emb ⁻¹' Q.U)) (cap.emb s) (cap.emb u) := by
      rw [hQL, hQset]
      exact GM11.IsLineWithEnds.symm (walk_isLine D.rad.G R hRs hne)
    have hline' := isLine_comap hj hline
    have hPV : (D.rad.G.sup C Q).V = C.V ∪ Q.V := Drawing.sup_V hC.1 hQs
    have hPE : (D.rad.G.sup C Q).E = C.E ∪ Q.E := Drawing.sup_E hC.1 hQs
    have hPU : (D.rad.G.sup C Q).U = C.U ∪ Q.U := U_union hPV hPE
    have hQmem : ∀ {x}, x ∈ R.support → x ∈ Q.V := fun {x} hx ↦ by
      rw [hQ, walkDrawing_V]
      exact hx
    have hRlen : 0 < R.length := by
      obtain ⟨e, y, hl, hy, hya⟩ := walk_first_step R hRs hne
      rcases Nat.eq_zero_or_pos R.length with h0 | h0
      · have h₁ := length_support R
        rw [h0] at h₁
        have h₂ := R.start_mem_support
        have h₃ := R.end_mem_support
        rcases hsu : R.support with _ | ⟨z, _ | ⟨z', l⟩⟩
        · simp [hsu] at h₁
        · rw [hsu] at h₂ h₃
          simp only [List.mem_singleton] at h₂ h₃
          exact absurd (h₂.trans h₃.symm) hne
        · simp [hsu] at h₁
      · exact h0
    have hlenW : R.length ≤ W.length := length_le_of_edges hRs fun e he ↦ hT'e.subset (hRe e he)
    refine outer_of_line hS h3 hn₁ hn hC hc hlink hr hri hp hrp hpi hrange hΘ hreg hO hab ha hb (L
      := cap.emb ⁻¹' Q.U) (s := s) (u := u) (Or.inr hline')
      (D.rad.G.sup_isSubdrawing C Q) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hsΘ hsV
    · rw [hPU]
      exact union_subset hrange hQr
    · intro v hv
      rw [hPV] at hv
      rcases hv with hv | hv
      · obtain ⟨e, he, hve⟩ := circuit_iso hC.2 v hv
        exact ⟨e, by rw [hPE]; exact Or.inl he, hve⟩
      · obtain ⟨e, he, hve⟩ := exists_edge_at R hRlen (by rwa [hQ, walkDrawing_V] at hv)
        exact ⟨e, by rw [hPE]; exact Or.inr (by rw [hQ, walkDrawing_E]; exact he), hve⟩
    · rw [hPU, hQL]
    · rw [hQL]
      refine Subset.antisymm (fun x hx ↦ ?_) ?_
      · exact D.walk_inter_ins hC hlt hRs hRA hx.1 hx.2
      · rintro _ rfl
        exact ⟨Q.V_subset_U (hQmem R.start_mem_support), ha'⟩
    · rintro x ⟨hxQ, hxb⟩
      obtain ⟨h₁, h₂, Θ', hΘ', hxΘ⟩ := D.rad.bd_point hQs hxb hxQ
      have hxs : cap.emb x ∈ R.support := by rwa [hQ, walkDrawing_V] at h₂
      have hl : cuffLabel cap (cap.emb x) = some Θ' := cuffLabel_emb hΘ' hxΘ
      have := hsame (hRin _ hxs) hl
      subst this
      exact cap.isEmbedding.injective (hRB _ hxs hl)
    · rintro _ ⟨hx, w, hw, rfl⟩
      exact (htouch w (hbdC hw hx).2.2 hx).elim
    · have h₁ := IsCircuit.ncard_V hC.2
      have h₂ : Q.V.ncard ≤ R.length + 1 := ncard_walk_V D.rad.G R
      have h₃ : Q.E.ncard = R.length := ncard_walk_E D.rad.G hRs
      have h₄ : (D.rad.G.sup C Q).V.ncard ≤ C.V.ncard + Q.V.ncard := by
        rw [hPV]
        exact ncard_union_le _ _
      have h₅ : (D.rad.G.sup C Q).E.ncard ≤ C.E.ncard + Q.E.ncard := by
        rw [hPE]
        exact ncard_union_le _ _
      omega
    · exact C.V_subset_U ha'C

end TangleDatum

end GraphMinor.GM19
