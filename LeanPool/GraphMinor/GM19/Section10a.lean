/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Poles
public import LeanPool.GraphMinor.GM19.Defs3

/-!
# Graph Minors XIX, (10.1), the first and third assertions

The improvement step behind the second assertion is `flaw_theta`: a path `Q` that joins two vertices
of a representativeness flaw `F`, and is lighter than both paths of `F`, gives a lighter flaw. The
second assertion is proved in `Section10b.lean`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

universe w

section Theta

variable {T : Type} [TopologicalSpace T] [T2Space T] [ConnectedSpace T]
  {G F F₁ F₂ P : Drawing T} {u v : T}

omit [T2Space T] [ConnectedSpace T] in
/-- The two paths of a circuit meet only in their ends, as point sets. -/
theorem TwoPaths.inter_U (h : TwoPaths G F F₁ F₂ P u v) {x : T} (h₁ : x ∈ F₁.U) (h₂ : x ∈ F₂.U) :
    x = u ∨ x = v := by
  by_cases hxV : x ∈ F₁.V
  · exact h.inter_V ⟨hxV, mem_V_of_mem_U h.sub₂ h₂ (h.sub₁.1 hxV)⟩
  · obtain ⟨g, hg, hxg⟩ := F₁.exists_edge_of_mem h₁ hxV
    have hn : g ∉ F₂.E := disjoint_left.mp h.disj_E hg
    exact absurd h₂ (disjoint_left.mp (edge_disjoint_U h.sub₂ (h.sub₁.2 hg) hn) hxg)

end Theta

/-- The complement of a disc bounded by `F`, if it is a disc, is also bounded by `F`. -/
theorem discBd_closure_compl {T : Type} [TopologicalSpace T] [T2Space T] [ConnectedSpace T]
    (hT : IsClosedSurface T) {F : Drawing T} {Δ : Set T} (hΔ : IsClosedDisc Δ)
    (hbd : discBd Δ = F.U) (hd : IsClosedDisc (closure Δᶜ)) : discBd (closure Δᶜ) = F.U := by
  have hO := isSide_out hT hΔ hbd
  have hE : closure Δᶜ = Δᶜ ∪ F.U := by
    rw [closure_eq_self_union_frontier, hO.frontier_eq]
  have hsub : F.U ⊆ Δ := hbd ▸ Surface.discBd_subset _
  have hc : (closure Δᶜ)ᶜ = discInt Δ := by
    rw [hE]
    ext x
    simp only [mem_compl_iff, mem_union, not_or, not_not]
    exact ⟨fun h ↦ ⟨h.1, hbd ▸ h.2⟩, fun h ↦ ⟨h.1, hbd ▸ h.2⟩⟩
  rw [← IsClosedDisc.frontier_eq_discBd hT hd, frontier_eq_closure_inter_closure,
    closure_closure, hc, closure_discInt hΔ, hE]
  ext x
  exact ⟨fun ⟨h₁, h₂⟩ ↦ h₁.resolve_left (not_not.mpr h₂), fun h ↦ ⟨Or.inr h, hsub h⟩⟩

/-- The two sides of a drawing that bounds a disc `Δ` are `Δ` and the closure of its complement. -/
theorem isSidesOf_cases {T : Type} [TopologicalSpace T] [T2Space T] [ConnectedSpace T]
    (hT : IsClosedSurface T) {F : Drawing T} {Δ S₁ S₂ : Set T} (hΔ : IsClosedDisc Δ)
    (hbd : discBd Δ = F.U) (hs : IsSidesOf F S₁ S₂) :
    (S₁ = Δ ∧ S₂ = closure Δᶜ) ∨ (S₁ = closure Δᶜ ∧ S₂ = Δ) := by
  obtain ⟨C₁, C₂, hne, hset, rfl, rfl⟩ := hs
  have h₀ : Sided F (discInt Δ) Δᶜ := ⟨Δ, hΔ, hbd, Or.inl ⟨rfl, rfl⟩⟩
  have hset' : componentsIn F.Uᶜ = {discInt Δ, Δᶜ} := Sided.components hT h₀
  have hC₁ : C₁ ∈ componentsIn F.Uᶜ := by rw [hset]; exact Or.inl rfl
  have hC₂ : C₂ ∈ componentsIn F.Uᶜ := by rw [hset]; exact Or.inr rfl
  rw [hset'] at hC₁ hC₂
  rcases hC₁ with rfl | rfl
  · rcases hC₂ with rfl | rfl
    · exact absurd rfl hne
    · exact Or.inl ⟨closure_discInt hΔ, rfl⟩
  · rcases hC₂ with rfl | rfl
    · exact Or.inr ⟨rfl, closure_discInt hΔ⟩
    · exact absurd rfl hne

/-- On a surface that is not a sphere, a second disc cannot include the complement of a disc. -/
theorem not_compl_subset {T : Type} [TopologicalSpace T] [T2Space T] [ConnectedSpace T]
    (hT : IsClosedSurface T) (hns : ¬ IsSphere T) {F C : Drawing T} {Δ Δ' : Set T}
    (hΔ : IsClosedDisc Δ) (hbd : discBd Δ = F.U) (hΔ' : IsClosedDisc Δ') (hbd' : discBd Δ' = C.U)
    (h : Δᶜ ⊆ Δ') : False := by
  have hO := isSide_out hT hΔ hbd
  have hsub : F.U ⊆ Δ' := fun x hx ↦
    closure_minimal h hΔ'.isClosed (hO.U_subset_closure hx)
  obtain ⟨D, ⟨hD, hDd, hDb, -⟩, -⟩ := disc_oArc Δ' F.U hΔ' hsub
    (hbd ▸ hΔ.isOArc_discBd)
  have heq : D = Δ := eq_of_discBd_eq (Surface.IsClosedSurface.isSurface hT) hns hDd hΔ
    (hDb.trans hbd.symm)
  obtain ⟨y, hy⟩ := (isSide_out hT hΔ' hbd').nonempty
  by_cases hyΔ : y ∈ Δ
  · exact hy (hD (heq ▸ hyΔ))
  · exact hy (h hyΔ)

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {cap : IsCappedSurface S Shat} {α : Type w} {χ : ColourScheme S α} {D : TangleDatum cap χ}
  {F F₁ F₂ Q : Drawing Shat} {a b : Shat}

namespace TangleDatum

omit [T2Space S] in
/-- A disc bounded by a circuit with `𝒯` on the outside cannot be lighter than a representativeness
flaw. -/
theorem IsRepFlaw.weight_le (hFl : D.IsRepFlaw F) {C : Drawing Shat} (hC : C.IsCircuitOf D.rad.G)
    (hc : C.E.ncard ≤ F.E.ncard) {Δ : Set Shat} (hΔ : IsClosedDisc Δ) (hbd : discBd Δ = C.U)
    (hm : (partIn cap D.Γ (closure Δᶜ), partIn cap D.Γ Δ) ∈ D.𝒯) :
    D.tb.weightSub F ≤ D.tb.weightSub C := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  refine hFl.minimal_weight C hC (hc.trans hFl.card_le) ⟨closure Δᶜ, Δ, ?_, ?_, hm⟩
  · have h : Sided C Δᶜ (discInt Δ) := ⟨Δ, hΔ, hbd, Or.inr ⟨rfl, rfl⟩⟩
    have := h.isSidesOf hT
    rwa [closure_discInt hΔ] at this
  · intro hdisc
    have hfr := (discBd_closure_compl hT hΔ hbd hdisc).trans hbd.symm
    have heq := eq_of_discBd_eq (Surface.IsClosedSurface.isSurface hT) hFl.not_sphere hdisc hΔ hfr
    obtain ⟨y, hy⟩ := (isSide_out hT hΔ hbd).nonempty
    exact hy (heq ▸ subset_closure hy)

omit [T2Space S] in
omit [T2Space Shat] in
/-- A flaw is shorter than twice `rep(Γ)`. -/
theorem IsRepFlaw.lt_two_rep (hFl : D.IsRepFlaw F) : (F.E.ncard : ℕ∞) < 2 * Painting.rep D.rad := by
  have h₁ := hFl.card_le
  have h₂ := hFl.lt_rep_Γ
  generalize Painting.rep D.rad = r at h₂ ⊢
  induction r using ENat.recTopCoe with
  | top =>
    rw [ENat.mul_top (by simp)]
    exact ENat.natCast_lt_top _
  | coe n =>
    have h₃ : D.rep < n := by exact_mod_cast h₂
    have h₄ : F.E.ncard < 2 * n := by omega
    exact_mod_cast h₄

variable (hS : IsSurface S) (h3 : D.P.Γ.IsInternallyThreeConnected)
include hS h3

/-- A circuit no longer than a flaw has one of its two discs on the small side of `𝒯`. -/
theorem IsRepFlaw.disc_mem_or (hFl : D.IsRepFlaw F) {C : Drawing Shat}
    (hC : C.IsCircuitOf D.rad.G) (hc : C.E.ncard ≤ F.E.ncard) {Δ : Set Shat} (hΔ : IsClosedDisc Δ)
    (hbd : discBd Δ = C.U) :
    (partIn cap D.P.Γ Δ, partIn cap D.P.Γ (closure Δᶜ)) ∈ D.𝒯 ∨
      (partIn cap D.P.Γ (closure Δᶜ), partIn cap D.P.Γ Δ) ∈ D.𝒯 := by
  have : ConnectedSpace Shat := cap.connected
  have h₁ := (disc_facts hS h3 D.rad hC hΔ hbd).1
  have o := disc_order hS h3 D.rad hC hΔ hbd
  refine D.isTangle.axiom1 h₁ ?_
  have := hFl.lt_ord_T
  have := hFl.card_le
  omega


/-- **The improvement step.** Let `Q` join two vertices of a representativeness flaw `F`, and meet
`F`
in nothing else. If `Q` is lighter than each of the two paths of `F`, and no longer, then we get a
lighter flaw. So no such `Q` exists. This is the argument in the proof of (10.1) of Graph Minors
XIX:
"Thus if $e_1 \subseteq \Sigma_2$ then one of $F_1 \cup Q, F_2 \cup Q$ contradicts the choice of
$F$. If $e_1 \not\subseteq \Sigma_2$ then one of $U(F_1 \cup Q), U(F_2 \cup Q)$ bounds a disc in
$\hat{\Sigma}_\chi$ including $\Sigma_2$, because $\hat{\Sigma}$ is not a sphere and
$rep(\Gamma) > \frac{1}{2}|E(F)|$, and again the choice of $F$ is contradicted." -/
theorem IsRepFlaw.theta (hFl : D.IsRepFlaw F) {Δ : Set Shat} (hΔ : IsClosedDisc Δ)
    (hbd : discBd Δ = F.U) (hm : (partIn cap D.P.Γ (closure Δᶜ), partIn cap D.P.Γ Δ) ∈ D.𝒯)
    (ht : TwoPaths D.rad.G F F₁ F₂ Q a b) (hc₁ : Q.E.ncard ≤ F₁.E.ncard)
    (hw₁ : D.tb.weightSub Q < D.tb.weightSub F₁) (hc₂ : Q.E.ncard ≤ F₂.E.ncard)
    (hw₂ : D.tb.weightSub Q < D.tb.weightSub F₂) : False := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hsurf := Surface.IsClosedSurface.isSurface hT
  have hns := hFl.not_sphere
  set G := D.rad.G with hG
  have hF : F.IsCircuitOf G := hFl.is_circuit
  -- A circuit made of `Q` and one path of `F` is lighter than `F`.
  have improve : ∀ {Fa Fb : Drawing Shat}, TwoPaths G F Fa Fb Q a b → Q.E.ncard ≤ Fa.E.ncard →
      D.tb.weightSub Q < D.tb.weightSub Fa →
      Drawing.IsCircuitOf (G.sup Q Fb) G ∧ (G.sup Q Fb).E.ncard ≤ F.E.ncard ∧
      D.tb.weightSub (G.sup Q Fb) < D.tb.weightSub F := by
    intro Fa Fb h hc hw
    have hE : (G.sup Q Fb).E = Q.E ∪ Fb.E := Drawing.sup_E h.path.1 h.sub₂
    have hdis : Disjoint Q.E Fb.E := disjoint_left.mpr fun e he he' ↦
      disjoint_left.mp h.meet_E he (h.right.1.2 he')
    refine ⟨⟨G.sup_isSubdrawing Q Fb, h.left_circuit⟩, ?_, ?_⟩
    · rw [hE, ncard_union_eq hdis Q.finite_edges Fb.finite_edges, h.union_E,
        ncard_union_eq h.disj_E Fa.finite_edges Fb.finite_edges]
      omega
    · rw [D.tb.weightSub_sup hE hdis, D.tb.weightSub_sup h.union_E h.disj_E]
      linarith
  have noDisc : ∀ {C : Drawing Shat}, C.IsCircuitOf G → C.E.ncard ≤ F.E.ncard →
      D.tb.weightSub C < D.tb.weightSub F → ∀ {Δ' : Set Shat}, IsClosedDisc Δ' →
      discBd Δ' = C.U → (partIn cap D.P.Γ Δ', partIn cap D.P.Γ (closure Δ'ᶜ)) ∈ D.𝒯 := by
    intro C hC hc hw Δ' hΔ' hbd'
    rcases hFl.disc_mem_or hS h3 hC hc hΔ' hbd' with h | h
    · exact h
    · exact absurd (hFl.weight_le hC hc hΔ' hbd' h) (not_le.mpr hw)
  obtain ⟨hC₂, hcC₂, hwC₂⟩ := improve ht hc₁ hw₁
  obtain ⟨hC₁, hcC₁, hwC₁⟩ := improve ht.swap hc₂ hw₂
  have hfour : ∀ {C : Drawing Shat}, C.IsCircuitOf G → C.E.ncard ≤ F.E.ncard →
      ∃ Δ', IsClosedDisc Δ' ∧ discBd Δ' = C.U := fun hC hc ↦
    exists_disc_of_lt_rep hC (lt_of_le_of_lt (by exact_mod_cast hc) hFl.lt_two_rep)
  obtain ⟨Δ₁, hΔ₁, hbd₁⟩ := hfour hC₁ hcC₁
  obtain ⟨Δ₂, hΔ₂, hbd₂⟩ := hfour hC₂ hcC₂
  have m₁ := noDisc hC₁ hcC₁ hwC₁ hΔ₁ hbd₁
  have m₂ := noDisc hC₂ hcC₂ hwC₂ hΔ₂ hbd₂
  have hin := isSide_int hT hΔ hbd
  have hout := isSide_out hT hΔ hbd
  have hdis : Disjoint (discInt Δ) Δᶜ := disjoint_left.mpr fun x hx hx' ↦ hx' hx.1
  have hcov : F.Uᶜ ⊆ discInt Δ ∪ Δᶜ := fun x hx ↦ by
    by_cases hxΔ : x ∈ Δ
    · exact Or.inl ⟨hxΔ, fun hb ↦ hx (hbd ▸ hb)⟩
    · exact Or.inr hxΔ
  have hO₁ := isSide_int hT hΔ₁ hbd₁
  have hO₂ := isSide_int hT hΔ₂ hbd₂
  rcases path_side ht.sub hin hout hdis hcov ht.path.1 ht.path.2 ht.ne ht.meet_V ht.meet_E with
    hP | hP
  · -- `Q` lies inside `Δ`, so the discs miss the outside.
    have d₁ : Disjoint Δᶜ Δ₁ := disjoint_disc hT hout hΔ₁ hbd₁
      (ht.swap.side_disjoint hout hdis.symm hP) fun h ↦
        not_compl_subset hT hns hΔ hbd hΔ₁ hbd₁ (h.trans (discInt_subset _))
    have d₂ : Disjoint Δᶜ Δ₂ := disjoint_disc hT hout hΔ₂ hbd₂
      (ht.side_disjoint hout hdis.symm hP) fun h ↦
        not_compl_subset hT hns hΔ hbd hΔ₂ hbd₂ (h.trans (discInt_subset _))
    have hc := ht.theta_cover hT hout hΔ₁ hΔ₂ hbd₁ hbd₂ d₁ d₂
    have hu := part_cover D.rad hF.1 hC₁.1 hC₂.1 hout hO₁ hO₂ (fun x ↦ by
      rw [closure_discInt hΔ₁, closure_discInt hΔ₂]
      exact hc x)
    rw [closure_discInt hΔ₁, closure_discInt hΔ₂] at hu
    exact D.isTangle.axiom2 hm m₁ m₂ hu
  · -- `Q` lies outside `Δ`, so a circuit bounds a disc that includes `Δ`.
    have key : ∀ {C : Drawing Shat} {Δ' : Set Shat}, C.IsSubdrawing G → IsClosedDisc Δ' →
        discBd Δ' = C.U → (partIn cap D.P.Γ Δ', partIn cap D.P.Γ (closure Δ'ᶜ)) ∈ D.𝒯 →
        Δ ⊆ Δ' → False := by
      intro C Δ' hC hΔ' hbd' hm' hsub
      have hO := isSide_int hT hΔ' hbd'
      have hu := part_cover D.rad hF.1 hC hC hout hO hO (fun x ↦ by
        rw [closure_discInt hΔ']
        by_cases hx : x ∈ Δ
        · exact Or.inr (Or.inl (hsub hx))
        · exact Or.inl (subset_closure hx))
      rw [closure_discInt hΔ'] at hu
      exact D.isTangle.axiom2 hm hm' hm' hu
    by_cases hin₁ : discInt Δ ⊆ discInt Δ₁
    · refine key hC₁.1 hΔ₁ hbd₁ m₁ ?_
      rw [← closure_discInt hΔ]
      exact closure_minimal (hin₁.trans (discInt_subset _)) hΔ₁.isClosed
    · have d₁ : Disjoint (discInt Δ) Δ₁ := disjoint_disc hT hin hΔ₁ hbd₁
        (ht.swap.side_disjoint hin hdis hP) hin₁
      have hL := isLine_of_isPathBetween ht.left.2 ht.ne
      have hF₁F : F₁.U ⊆ F.U := by rw [ht.U_eq]; exact subset_union_left
      have hF₂F : F₂.U ⊆ F.U := by rw [ht.U_eq]; exact subset_union_right
      have hUC₁ : (G.sup Q F₁).U = Q.U ∪ F₁.U := ht.swap.U_right
      have hUC₂ : (G.sup Q F₂).U = Q.U ∪ F₂.U := ht.U_right
      have hbdΔ : F.U ⊆ Δ := hbd ▸ Surface.discBd_subset _
      have hab := ht.mem_V₁
      have hmeet : Δ₁ ∩ Δ = F₁.U := by
        apply Subset.antisymm
        · rintro x ⟨hx₁, hx⟩
          have hxF : x ∈ F.U := by
            by_contra hn
            exact disjoint_left.mp d₁ ⟨hx, hbd ▸ hn⟩ hx₁
          rcases (ht.U_eq ▸ hxF : x ∈ F₁.U ∪ F₂.U) with h | h
          · exact h
          · by_contra hn
            have hxb : x ∉ discBd Δ₁ := by
              rw [hbd₁, hUC₁]
              rintro (hq | hq)
              · rcases hP x hq with h' | rfl | rfl
                · exact h' (hbdΔ hxF)
                · exact hn (F₁.V_subset_U hab.1)
                · exact hn (F₁.V_subset_U hab.2)
              · exact hn hq
            have hopen := hΔ₁.isOpen_discInt cap.isSurface.2.2
            obtain ⟨z, hz₁, hz⟩ := mem_closure_iff.mp (hin.U_subset_closure hxF) _ hopen ⟨hx₁, hxb⟩
            exact disjoint_left.mp d₁ hz (discInt_subset _ hz₁)
        · intro x hx
          exact ⟨Surface.discBd_subset _ (hbd₁ ▸ hUC₁ ▸ Or.inr hx), hbdΔ (hF₁F hx)⟩
      have hb₁ : F₁.U ⊆ discBd Δ₁ := by rw [hbd₁, hUC₁]; exact subset_union_right
      have hb₂ : F₁.U ⊆ discBd Δ := by rw [hbd]; exact hF₁F
      obtain ⟨hdisc, hbdU⟩ := disc_union Δ₁ Δ F₁.U a b hΔ₁ hΔ hL hmeet hb₁ hb₂
      have hbdU' : discBd (Δ₁ ∪ Δ) = (G.sup Q F₂).U := by
        rw [hbdU, hbd₁, hbd, hUC₁, hUC₂, ht.U_eq]
        have hQa : a ∈ Q.U := by
          obtain ⟨W, -, hWV, -⟩ := ht.path.2
          exact Q.V_subset_U (hWV ▸ W.start_mem_support)
        have hQb : b ∈ Q.U := by
          obtain ⟨W, -, hWV, -⟩ := ht.path.2
          exact Q.V_subset_U (hWV ▸ W.end_mem_support)
        ext x
        constructor
        · rintro ⟨(h | h) | (h | h), hn⟩
          · exact Or.inl h
          · by_cases hxab : x ∈ ({a, b} : Set Shat)
            · rcases hxab with rfl | rfl
              · exact Or.inl hQa
              · exact Or.inl hQb
            · exact absurd ⟨h, hxab⟩ hn
          · by_cases hxab : x ∈ ({a, b} : Set Shat)
            · rcases hxab with rfl | rfl
              · exact Or.inl hQa
              · exact Or.inl hQb
            · exact absurd ⟨h, hxab⟩ hn
          · exact Or.inr h
        · rintro (h | h)
          · refine ⟨Or.inl (Or.inl h), fun ⟨h₁, h₂⟩ ↦ ?_⟩
            rcases hP x h with h' | h' | h'
            · exact h' (hbdΔ (hF₁F h₁))
            · exact h₂ (Or.inl h')
            · exact h₂ (Or.inr h')
          · exact ⟨Or.inr (Or.inr h), fun ⟨h₁, h₂⟩ ↦ h₂ (ht.inter_U h₁ h)⟩
      exact key hC₂.1 hdisc hbdU' (noDisc hC₂ hcC₂ hwC₂ hdisc hbdU') subset_union_right

omit hS h3 in
omit [T2Space S] in
/-- The first assertion of (10.1): the side of a flaw that is not the big one is a disc. -/
theorem IsRepFlaw.isClosedDisc (hFl : D.IsRepFlaw F) {S₁ S₂ : Set Shat} (hs : IsSidesOf F S₁ S₂)
    (hnd : ¬ IsClosedDisc S₁) : IsClosedDisc S₂ := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  obtain ⟨Δ, hΔ, hbd⟩ := exists_disc_of_lt_rep hFl.is_circuit hFl.lt_two_rep
  obtain ⟨Ω₁, Ω₂, ⟨Δ', hΔ', hbd', h⟩, rfl, rfl⟩ := exists_sided_of_isSidesOf hT hΔ hbd hs
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact absurd (by rwa [closure_discInt hΔ']) hnd
  · rwa [closure_discInt hΔ']

/-- The third assertion of (10.1): a representativeness flaw is `λ`-linked to `𝒯`. -/
theorem IsRepFlaw.linked (hFl : D.IsRepFlaw F) {S₁ S₂ : Set Shat} (hs : IsSidesOf F S₁ S₂)
    (hnd : ¬ IsClosedDisc S₁)
    (hm : (partIn cap D.P.Γ S₁, partIn cap D.P.Γ S₂) ∈ D.𝒯) :
    IsLambdaLinkedCircuit D.tb D.ord D.𝒯 F := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hsurf := Surface.IsClosedSurface.isSurface hT
  have hc := hFl.card_le
  have hlo := hFl.lt_ord_T
  have hlt : (F.E.ncard : ℕ∞) < 2 * min (D.ord : ℕ∞) (Painting.rep D.rad) := by
    rcases min_cases (D.ord : ℕ∞) (Painting.rep D.rad) with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h]
      have : F.E.ncard < 2 * D.ord := by omega
      exact_mod_cast this
    · rw [h]
      exact hFl.lt_two_rep
  obtain ⟨F', S₁', S₂', hL, hs', hLT, hle, heq, h₁, h₂⟩ := theorem_8_7_proof hS h3 D.tb D.isTangle
    hFl.is_circuit hlt hs hm
  have hF' := hL.1
  have hm' := hLT.1
  have hsmall : ∀ {C : Drawing Shat}, C.IsCircuitOf D.rad.G → C.E.ncard ≤ F.E.ncard →
      ∃ Δ, IsClosedDisc Δ ∧ discBd Δ = C.U := fun hC hc' ↦
    exists_disc_of_lt_rep hC (lt_of_le_of_lt (by exact_mod_cast hc') hFl.lt_two_rep)
  obtain ⟨Δ, hΔ, hbd⟩ := hsmall hFl.is_circuit le_rfl
  have hS₁ : S₁ = closure Δᶜ ∧ S₂ = Δ := by
    rcases isSidesOf_cases hT hΔ hbd hs with ⟨rfl, -⟩ | h
    · exact absurd hΔ hnd
    · exact h
  obtain ⟨rfl, rfl⟩ := hS₁
  obtain ⟨Δ', hΔ', hbd'⟩ := hsmall hF' hle
  -- `S₁'` is not a disc, because it includes `S₁`.
  have hnd' : ¬ IsClosedDisc S₁' := by
    intro hd'
    have hbdS : discBd S₁' = F'.U := by
      rcases isSidesOf_cases hT hΔ' hbd' hs' with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact hbd'
      · exact discBd_closure_compl hT hΔ' hbd' hd'
    exact not_compl_subset hT hFl.not_sphere hΔ hbd hd' hbdS (subset_closure.trans h₁)
  -- So `F'` is at least as long as `F`, since `½|E(F')| < rep(𝒯)` would give the other orientation.
  have hgeq : F.E.ncard ≤ F'.E.ncard := by
    by_contra hshort
    obtain ⟨Δ'', hΔ'', hbd'', hm''⟩ := (tangleRep_spec D.rad D.ord D.𝒯).2 F' hF' (by
      have : F.E.ncard ≤ 2 * D.rep := hc
      simp only [TangleDatum.rep] at this
      omega)
    rcases isSidesOf_cases hT hΔ'' hbd'' hs' with ⟨e₁, -⟩ | ⟨e₁, e₂⟩
    · exact hnd' (e₁ ▸ hΔ'')
    · rw [e₁, e₂] at hm'
      have hu := part_cover D.rad hF'.1 hF'.1 hF'.1 (isSide_out hT hΔ'' hbd'')
        (isSide_int hT hΔ'' hbd'') (isSide_int hT hΔ'' hbd'') (fun x ↦ by
          rw [closure_discInt hΔ'']
          by_cases hx : x ∈ Δ''
          · exact Or.inr (Or.inl hx)
          · exact Or.inl (subset_closure hx))
      rw [closure_discInt hΔ''] at hu
      exact D.isTangle.axiom2 hm' hm'' hm'' hu
  have hcard : F'.E.ncard = F.E.ncard := le_antisymm hle hgeq
  have hw₁ := heq hcard
  have hw₂ := hFl.minimal_weight F' hF' (hcard ▸ hc) ⟨S₁', S₂', hs', hnd', hm'⟩
  -- The rational independence of the weights gives `E(F') = E(F)`.
  have hEE : F'.E = F.E := by
    by_contra hne
    have hdiff : (F.E \ F'.E).Nonempty := by
      by_contra hemp
      rw [not_nonempty_iff_eq_empty, sdiff_eq_empty] at hemp
      exact hne (eq_of_subset_of_ncard_le hemp hcard.le F'.finite_edges).symm
    have hX : F'.E \ F.E ⊆ D.rad.G.E := fun e he ↦ hF'.1.2 he.1
    have hY : F.E \ F'.E ⊆ D.rad.G.E := fun e he ↦ hFl.is_circuit.1.2 he.1
    have hd : Disjoint (F'.E \ F.E) (F.E \ F'.E) := disjoint_left.mpr fun e h₁ h₂ ↦ h₁.2 h₂.1
    refine D.tb.weight_ne hX hY hd hdiff ?_
    have split : ∀ {s t : Set (Set Shat)}, s.Finite → ∑ᶠ e ∈ s, D.tb.wtE e =
        ∑ᶠ e ∈ s ∩ t, D.tb.wtE e + ∑ᶠ e ∈ s \ t, D.tb.wtE e := by
      intro s t hs
      have hdisj : Disjoint (s ∩ t) (s \ t) := disjoint_left.mpr fun _ h₁ h₂ => h₂.2 h₁.2
      rw [← finsum_mem_union hdisj (hs.inter_of_left _) hs.sdiff, inter_union_sdiff]
    have e₁ := split (s := F'.E) (t := F.E) F'.finite_edges
    have e₂ := split (s := F.E) (t := F'.E) F.finite_edges
    rw [Set.inter_comm] at e₂
    simp only [TieBreaker.weightSub] at hw₁ hw₂
    linarith
  have hUU : F'.U = F.U := by
    have key : ∀ {X Y : Drawing Shat}, X.IsCircuit → X.E = Y.E → X.U ⊆ Y.U := by
      intro X Y hX hE
      refine U_of_edges hX Y.isClosed_U fun e he ↦ ?_
      exact (subset_closure.trans (Y.closure_subset_U (hE ▸ he)))
    exact Subset.antisymm (key hF'.2 hEE) (key hFl.is_circuit.2 hEE.symm)
  obtain ⟨C₁, C₂, hne, hset, e₁, e₂⟩ := hs'
  exact ⟨hFl.is_circuit, hlt, S₁', S₂', ⟨C₁, C₂, hne, hUU ▸ hset, e₁, e₂⟩, hLT⟩

end TangleDatum

end GraphMinor.GM19
