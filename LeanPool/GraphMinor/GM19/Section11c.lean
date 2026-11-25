/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section11b

/-!
# Feasts of small order

This file gathers what a feast can be changed into. A setting fixes a long side, its cuff and its
pole, with the other poles far away and no flaw in freedom
(`IsSideSetting`). We show how to merge two bites with two common vertices
(`IsSideSetting.exists_merge`), how to drop a bite inside another (`IsSideSetting.exists_drop`), and
how to shorten a bite with a vertex off its arc (`IsSideSetting.exists_shorten`). These are used for
(11.3) in `Section11d.lean`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {cap : IsCappedSurface S Shat} {β : Type w} {χ : ColourScheme S β}


namespace TangleDatum

omit [T2Space Shat] in
/-- Taking a member out of a finite family takes `½|E(F)|` off the order. -/
theorem feastOrder_diff_singleton {ℱ : Set (Drawing Shat)} (hf : ℱ.Finite) {F : Drawing Shat}
  (hF : F ∈ ℱ) :
    feastOrder (ℱ \ {F}) + F.E.ncard / 2 = feastOrder ℱ := by
  classical
  have hf' : (ℱ \ {F}).Finite := hf.subset sdiff_subset
  rw [feastOrder, feastOrder, dite_eq_left hf, dite_eq_left hf']
  have : hf.toFinset = insert F hf'.toFinset := by
    ext G
    simp only [Finite.mem_toFinset, Finset.mem_insert, mem_sdiff, mem_singleton_iff]
    by_cases h : G = F
    · simp [h, hF]
    · simp [h]
  rw [this, Finset.sum_insert (by simp), add_comm]

omit [T2Space Shat] in
theorem feastOrder_insert_le {ℱ : Set (Drawing Shat)} (hf : ℱ.Finite)
  (F : Drawing Shat) : feastOrder (insert F ℱ) ≤ feastOrder ℱ + F.E.ncard / 2 := by
  classical
  have hf' : (insert F ℱ).Finite := hf.insert F
  rw [feastOrder, feastOrder, dite_eq_left hf, dite_eq_left hf']
  have : hf'.toFinset = insert F hf.toFinset := by
    ext G
    simp
  rw [this]
  by_cases h : F ∈ hf.toFinset
  · rw [Finset.insert_eq_of_mem h]
    omega
  · rw [Finset.sum_insert h]
    omega

variable {D : TangleDatum cap χ}

open scoped Classical in
/-- The sum of the weights of a family of drawings. -/
noncomputable def feastWeight (D : TangleDatum cap χ) (ℱ : Set (Drawing Shat)) : ℝ :=
  if h : ℱ.Finite then ∑ F ∈ h.toFinset, D.tb.weightSub F else 0

omit [T2Space S] [T2Space Shat] in
theorem feastWeight_diff_singleton {ℱ : Set (Drawing Shat)} (hf : ℱ.Finite) {F : Drawing Shat}
  (hF : F ∈ ℱ) :
    D.feastWeight (ℱ \ {F}) + D.tb.weightSub F = D.feastWeight ℱ := by
  classical
  have hf' : (ℱ \ {F}).Finite := hf.subset sdiff_subset
  rw [feastWeight, feastWeight, dite_eq_left hf, dite_eq_left hf']
  have : hf.toFinset = insert F hf'.toFinset := by
    ext G
    simp only [Finite.mem_toFinset, Finset.mem_insert, mem_sdiff, mem_singleton_iff]
    by_cases h : G = F
    · simp [h, hF]
    · simp [h]
  rw [this, Finset.sum_insert (by simp), add_comm]

omit [T2Space S] [T2Space Shat] in
theorem feastWeight_insert {ℱ : Set (Drawing Shat)} (hf : ℱ.Finite) {F : Drawing Shat}
  (hF : F ∉ ℱ) :
    D.feastWeight (insert F ℱ) = D.feastWeight ℱ + D.tb.weightSub F := by
  have h := feastWeight_diff_singleton (D := D) (hf.insert F) (mem_insert F ℱ)
  rw [insert_sdiff_self_of_notMem hF] at h
  exact h.symm

omit [T2Space S] in
omit [T2Space Shat] in
/-- A family with a larger union of arcs is still a feast. -/
theorem IsFeast.of_arc_subset {r : Shat} {side : Set S} {ω : List β} {ℱ ℱ' : Set (Drawing Shat)}
  (h : D.IsFeast r side ω ℱ) (hf : ℱ'.Finite) (hb : ∀ F ∈ ℱ', D.IsBiteAt r F)
    (hc : ℱ'.ncard ≤ ω.length + 1) (hsub : D.feastArcUnion r ℱ ⊆ D.feastArcUnion r ℱ') : D.IsFeast
      r side ω ℱ' := by
  refine ⟨hf, hb, hc, fun s hs hne ↦ (h.includes_short_sides s hs hne).trans hsub, fun X hX ↦ ?_⟩
  obtain ⟨x, hx, rfl⟩ := hX
  have hdiff : side \ cap.emb ⁻¹' D.feastArcUnion r ℱ' ⊆ side \ cap.emb ⁻¹' D.feastArcUnion r ℱ
    := fun z hz ↦ ⟨hz.1, fun h' ↦ hz.2 (hsub h')⟩
  have hsubY := isPreconnected_connectedComponentIn.subset_connectedComponentIn
    (mem_connectedComponentIn hx) ((connectedComponentIn_subset _ _).trans hdiff)
  obtain ⟨hh, hh', hall⟩ := h.component_omits _ (mem_image_of_mem _ (hdiff hx))
  exact ⟨hh, hh', fun e he hsub' ↦ hall e he (hsub'.trans hsubY)⟩

/-- A long side with its cuff and pole, the other poles far away, and no flaw in freedom. -/
structure IsSideSetting (D : TangleDatum cap χ) (side Θ : Set S) (r : Shat) (N : ℕ) : Prop where
  h3 : D.P.Γ.IsInternallyThreeConnected
  long : side ∈ χ.Φ.longSides
  side_cuff : side ⊆ Θ
  cuff : Θ ∈ cuffs S
  pole : r ∈ D.rad.poles
  reg : D.rad.regionOf r = cap.cuffDisc Θ
  rep_gt : N < D.rep
  far : ∀ r₁ ∈ D.rad.poles, ∀ r₂ ∈ D.rad.poles, r₁ ≠ r₂ → N < D.vDist r₁ r₂
  free : ∀ C, ¬ D.IsFreeCircuit N C

namespace IsSideSetting

variable {side Θ : Set S} {r : Shat} {N : ℕ} (X : D.IsSideSetting side Θ r N)
include X

omit [T2Space S] in
/-- A short circuit with `r` inside has `r` on it, or else it is a flaw in freedom. -/
theorem pole_mem {C : Drawing Shat} (hC : C.IsCircuitOf D.rad.G) (hc : C.E.ncard
  ≤ 2 * N) (hri : r ∈ D.ins C) : r ∈ C.V := by
  have hT := cap.isClosedSurface
  have hman : ∀ x : Shat, IsManifoldPoint x := fun x ↦ (hT.2.2 x).isManifoldPoint
  have : ConnectedSpace Shat := cap.connected
  by_contra hrC
  have hlt : C.E.ncard < 2 * D.rep := by have := X.rep_gt; omega
  have hi := D.ins_spec hC hlt
  have hdis : Disjoint (cap.cuffDisc Θ) C.U := disjoint_left.2 fun x hx hxF ↦ hrC
    (pole_mem_of_meet hC.1 X.pole X.cuff X.reg hxF hx)
  have hrd : r ∈ cap.cuffDisc Θ := X.reg ▸ (D.rad.regionOf_mem X.pole.1).2
  have hconn : IsPreconnected (cap.cuffDisc Θ) := X.reg ▸ isPreconnected_connectedComponentIn
  have hsub : cap.cuffDisc Θ ⊆ discInt (D.ins C) := by
    rcases hi.2.2.1.side hman hconn (by rw [hi.2.2.2.1]; exact hdis) with h | h
    · exact h
    · exact absurd hri (disjoint_left.1 h hrd)
  have hcl : closure (cap.cuffDisc Θ) ⊆ D.ins C := closure_minimal (hsub.trans
    (discInt_subset _)) hi.2.2.1.isClosed
  refine X.free C ⟨hC, hc, Or.inl ⟨side, X.long, ?_⟩⟩
  rintro _ ⟨y, hy, rfl⟩
  exact hcl (cap.mem_closure_emb X.cuff (X.side_cuff hy))

theorem shape (hS : IsSurface S) {F : Drawing Shat} (hb : D.IsBiteAt r F) (hc : F.E.ncard
  ≤ 2 * N) : ∃ v₁ v₂ Β L A A' Di Do, D.IsBiteShape r Θ F v₁ v₂ Β L A A' Di Do :=
  bite_shape_of_far hS X.h3 X.rep_gt X.far hb.is_circuit hc X.pole X.cuff X.reg hb.rstar_mem

theorem biteArc_subset_of_ins (hS : IsSurface S) {F₁ F₂ : Drawing Shat} (h₁ : D.IsBiteAt r F₁)
  (h₂ : D.IsBiteAt r F₂) (c₁ : F₁.E.ncard ≤ 2 * N) (c₂ : F₂.E.ncard ≤ 2 * N)
    (hsub : D.ins F₁ ⊆ D.ins F₂) : D.biteArc r F₁ ⊆ D.biteArc r F₂ := by
  obtain ⟨_, _, _, _, _, _, _, _, s₁⟩ := X.shape hS h₁ c₁
  obtain ⟨_, _, _, _, _, _, _, _, s₂⟩ := X.shape hS h₂ c₂
  exact s₁.biteArc_mono s₂ hsub

omit [T2Space S] in
/-- A short circuit with `r` inside is a bite. -/
theorem bite_of_ins {C : Drawing Shat} (hC : C.IsCircuitOf D.rad.G)
  (hc : C.E.ncard ≤ 2 * N) (hri : r ∈ D.ins C) : D.IsBiteAt r C :=
  ⟨X.pole, hC, by have := X.rep_gt; omega, X.pole_mem hC hc hri⟩

omit [TopologicalSpace S] [T2Space S] X in
omit [T2Space Shat] in
/-- Two distinct members of a feast of order at most `N` have together at most `2N` edges. -/
theorem sum_le {ℱ : Set (Drawing Shat)} (hf : ℱ.Finite) {F₁ F₂ : Drawing Shat} (h₁ : F₁ ∈ ℱ)
  (h₂ : F₂ ∈ ℱ) (hne : F₁ ≠ F₂) :
    F₁.E.ncard / 2 + F₂.E.ncard / 2 + feastOrder ((ℱ \ {F₁}) \ {F₂}) = feastOrder ℱ := by
  have e₁ := feastOrder_diff_singleton hf h₁
  have e₂ := feastOrder_diff_singleton (hf.subset sdiff_subset) (F := F₂) ⟨h₂, fun h ↦ hne
    (mem_singleton_iff.1 h).symm⟩
  omega

/-- **Merging two bites with two common vertices** makes the order drop. -/
theorem exists_merge (hS : IsSurface S) {side' : Set S} {ω : List β} {ℱ : Set
  (Drawing Shat)} {c : ℕ} (hNc : N ≤ c + 1) (hfe : D.IsFeast r side' ω ℱ) (hord : feastOrder ℱ ≤ N)
    (hsm : ∀ F ∈ ℱ, F.E.ncard ≤ 2 * c) {F₁ F₂ : Drawing Shat} (h₁ : F₁ ∈ ℱ) (h₂ : F₂ ∈ ℱ)
      (hne : F₁ ≠ F₂) {x y : Shat} (hxy : x ≠ y) (hx₁ : x ∈ F₁.V) (hx₂ : x ∈ F₂.V)
    (hy₁ : y ∈ F₁.V) (hy₂ : y ∈ F₂.V) : ∃ ℱ', D.IsFeast r side' ω ℱ' ∧ feastOrder ℱ' < feastOrder ℱ
      ∧ ∀ F ∈ ℱ', F.E.ncard ≤ 2 * c := by
  classical
  have : ConnectedSpace Shat := cap.connected
  have hf := hfe.finite_bites
  have b₁ := hfe.all_bites F₁ h₁
  have b₂ := hfe.all_bites F₂ h₂
  have hsum := sum_le hf h₁ h₂ hne
  obtain ⟨k₁, hk₁⟩ : ∃ k, F₁.E.ncard = 2 * k := ⟨_, D.ncard_E_eq_hat b₁.is_circuit⟩
  obtain ⟨k₂, hk₂⟩ : ∃ k, F₂.E.ncard = 2 * k := ⟨_, D.ncard_E_eq_hat b₂.is_circuit⟩
  have d₁ : F₁.E.ncard / 2 = k₁ := by omega
  have d₂ : F₂.E.ncard / 2 = k₂ := by omega
  obtain ⟨C, hC, hcard, i₁, i₂, hV⟩ := no_two_common_vertices X.rep_gt b₁.is_circuit b₂.is_circuit
    (by omega) hxy hx₁ hx₂ hy₁ hy₂
  obtain ⟨k, hk⟩ : ∃ k, C.E.ncard = 2 * k := ⟨_, D.ncard_E_eq_hat hC⟩
  have hlt : C.E.ncard + 2 ≤ F₁.E.ncard + F₂.E.ncard := by
    have e₁ := IsCircuit.ncard_V hC.2
    have e₂ := IsCircuit.ncard_V b₁.is_circuit.2
    have e₃ := IsCircuit.ncard_V b₂.is_circuit.2
    have h₃ := ncard_le_ncard hV (F₁.finite_V.union F₂.finite_V)
    have h₄ := ncard_union_add_ncard_inter F₁.V F₂.V F₁.finite_V F₂.finite_V
    have h₅ : 2 ≤ (F₁.V ∩ F₂.V).ncard := by
      have : ({x, y} : Set Shat) ⊆ F₁.V ∩ F₂.V := by
        rintro z (rfl | hz)
        · exact ⟨hx₁, hx₂⟩
        · rw [mem_singleton_iff.1 hz]
          exact ⟨hy₁, hy₂⟩
      have h₆ := ncard_le_ncard this (F₁.finite_V.subset inter_subset_left)
      rwa [ncard_pair hxy] at h₆
    omega
  have bC : D.IsBiteAt r C := X.bite_of_ins hC (by omega) (i₁ (D.U_subset_ins b₁.is_circuit
    b₁.card_lt (F₁.V_subset_U b₁.rstar_mem)))
  set 𝒜 := (ℱ \ {F₁}) \ {F₂} with h𝒜
  have hfA : 𝒜.Finite := hf.subset fun z hz ↦ hz.1.1
  have hins := feastOrder_insert_le hfA C
  have hnA : 𝒜.ncard + 2 ≤ ℱ.ncard := by
    have e₁ := ncard_sdiff_singleton_add_one h₁ hf
    have e₂ := ncard_sdiff_singleton_add_one (s := ℱ \ {F₁}) (a := F₂) ⟨h₂, fun h ↦ hne
      (mem_singleton_iff.1 h).symm⟩ (hf.subset sdiff_subset)
    rw [← h𝒜] at e₂
    omega
  have hcle := hfe.card_le
  have hsubA : ∀ F ∈ 𝒜, F ∈ ℱ := fun F hF ↦ hF.1.1
  have horder : feastOrder 𝒜 + k₁ + k₂ = feastOrder ℱ := by omega
  have hCord : C.E.ncard ≤ 2 * N := by omega
  refine ⟨insert C 𝒜, hfe.of_arc_subset (hfA.insert C) ?_ ?_ ?_, by omega, ?_⟩
  · rintro F (rfl | hF)
    · exact bC
    · exact hfe.all_bites F (hsubA F hF)
  · have := ncard_insert_le C 𝒜
    omega
  · intro z hz
    obtain ⟨F, hF, hzF⟩ := mem_iUnion₂.1 hz
    by_cases e₁ : F = F₁
    · subst e₁
      exact mem_iUnion₂.2 ⟨C, mem_insert _ _, X.biteArc_subset_of_ins hS b₁ bC
        (by omega) hCord i₁ hzF⟩
    by_cases e₂ : F = F₂
    · subst e₂
      exact mem_iUnion₂.2 ⟨C, mem_insert _ _, X.biteArc_subset_of_ins hS b₂ bC
        (by omega) hCord i₂ hzF⟩
    exact mem_iUnion₂.2 ⟨F, mem_insert_of_mem _ ⟨⟨hF, e₁⟩, e₂⟩, hzF⟩
  · rintro F (rfl | hF)
    · omega
    · exact hsm F (hsubA F hF)

/-- **A bite inside another can be dropped**, and the order drops. -/
theorem exists_drop (hS : IsSurface S) {side' : Set S} {ω : List β} {ℱ : Set (Drawing Shat)}
  (hfe : D.IsFeast r side' ω ℱ) (hord : feastOrder ℱ ≤ N) {F₁ F₂ : Drawing Shat} (h₁ : F₁ ∈ ℱ)
    (h₂ : F₂ ∈ ℱ) (hne : F₁ ≠ F₂) (hsub : D.ins F₁ ⊆ D.ins F₂) : ∃ ℱ', ℱ' ⊆ ℱ
      ∧ D.IsFeast r side' ω ℱ' ∧ feastOrder ℱ' < feastOrder ℱ := by
  classical
  have : ConnectedSpace Shat := cap.connected
  have hf := hfe.finite_bites
  have b₁ := hfe.all_bites F₁ h₁
  have b₂ := hfe.all_bites F₂ h₂
  have hsum := sum_le hf h₁ h₂ hne
  have hpos₁ : 0 < F₁.E.ncard := (ncard_pos F₁.finite_edges).2 (IsCircuit.E_nonempty
    b₁.is_circuit.2)
  obtain ⟨k₁, hk₁⟩ : ∃ k, F₁.E.ncard = 2 * k := ⟨_, D.ncard_E_eq_hat b₁.is_circuit⟩
  obtain ⟨k₂, hk₂⟩ : ∃ k, F₂.E.ncard = 2 * k := ⟨_, D.ncard_E_eq_hat b₂.is_circuit⟩
  have e₁ := feastOrder_diff_singleton hf h₁
  have hF₂ : F₂ ∈ ℱ \ {F₁} := ⟨h₂, fun h ↦ hne (mem_singleton_iff.1 h).symm⟩
  refine ⟨ℱ \ {F₁}, sdiff_subset, hfe.of_arc_subset (hf.subset sdiff_subset)
    (fun F hF ↦ hfe.all_bites F hF.1) ?_ ?_, by omega⟩
  · exact (ncard_le_ncard sdiff_subset hf).trans hfe.card_le
  · intro z hz
    obtain ⟨F, hF, hzF⟩ := mem_iUnion₂.1 hz
    by_cases e : F = F₁
    · subst e
      exact mem_iUnion₂.2 ⟨F₂, hF₂, X.biteArc_subset_of_ins hS b₁ b₂ (by omega) (by omega) hsub hzF⟩
    · exact mem_iUnion₂.2 ⟨F, ⟨hF, e⟩, hzF⟩

/-- **A bite with a vertex on the cuff off its arc can be shortened.** The spoke from the pole to
that vertex runs outside the bite, and it gives a shorter circuit around the bite. -/
theorem exists_shorter (hS : IsSurface S) {F : Drawing Shat} {v₁ v₂ Β L A A' Di Do}
  (h : D.IsBiteShape r Θ F v₁ v₂ Β L A A' Di Do) {x : Shat} (hxV : x ∈ F.V) (hxA : x ∈ A') :
    ∃ F', F'.IsCircuitOf D.rad.G ∧ F'.E.ncard < F.E.ncard ∧ D.ins F ⊆ D.ins F' ∧ r ∈ F'.V := by
  have hT := cap.isClosedSurface
  have hman : ∀ x : Shat, IsManifoldPoint x := fun x ↦ (hT.2.2 x).isManifoldPoint
  have : ConnectedSpace Shat := cap.connected
  have hF := h.circuit
  have hlt := h.lt
  have hrep : 1 ≤ D.rep := by omega
  have hi := D.ins_spec hF hlt
  have hdisc := hi.2.2.1
  have hbd : discBd (D.ins F) = F.U := hi.2.2.2.1
  obtain ⟨hxΘ, hxst⟩ := h.A'_sub hxA
  obtain ⟨v, hvΘ, rfl⟩ := hxΘ
  have hvG := (D.rad.bd_point hF.1 (cuff_subset_bd ⟨Θ, X.cuff⟩ hvΘ) (F.V_subset_U hxV)).1
  obtain ⟨e, he, hset⟩ := D.rad.exists_pole_edge hS X.h3 X.pole X.cuff X.reg hvG hvΘ
  have hvr : cap.emb v ≠ r := fun h' ↦ X.pole.1.2 (h' ▸ mem_image_of_mem _ hvG)
  have heF : e ∉ F.E := by
    intro heF
    apply hxst
    rw [← h.nbrs]
    refine ⟨e, heF, ?_⟩
    rw [hF.1.closure_inter_V heF, hset, pair_comm]
  obtain ⟨P, B, Q, ht, hQe, c₁, c₂⟩ := exists_theta_chord hS X.h3 hF X.pole h.r_mem hvG hxV he hset
    heF
  have hemem : cap.emb v ∈ closure e ∩ D.rad.G.V := by rw [hset]; exact Or.inl rfl
  have hrmem : r ∈ closure e ∩ D.rad.G.V := by rw [hset]; exact Or.inr rfl
  have hedis : Disjoint e F.U := edge_disjoint_U hF.1 he heF
  have hereg : e ⊆ cap.cuffDisc Θ := X.reg ▸ D.rad.edge_subset_region he X.pole.1 hset
  have heDo : e ⊆ discInt Do := by
    have hpre : IsPreconnected e := he.2.2.1.isConnected.isPreconnected
    have hcov : e ⊆ Di ∪ Do := by
      rw [h.union]
      exact hereg.trans subset_closure
    have hnone : e ∩ (Di ∩ Do) = ∅ := by
      rw [h.inter, eq_empty_iff_forall_notMem]
      rintro y ⟨hy, hyΒ⟩
      exact disjoint_left.1 hedis hy (h.Β_F hyΒ)
    have hvDo : cap.emb v ∈ Do := Surface.discBd_subset _ (h.bd_o ▸ Or.inl hxA)
    rcases isPreconnected_iff_subset_of_disjoint_closed.1 hpre Di Do h.di.isClosed h.do_.isClosed
      hcov hnone with hs | hs
    · exfalso
      have hvDi : cap.emb v ∈ Di := closure_minimal hs h.di.isClosed hemem.1
      have hΒ : cap.emb v ∈ Β := h.inter ▸ ⟨hvDi, hvDo⟩
      exact hxst (h.meet ▸ ⟨hΒ, mem_image_of_mem _ hvΘ⟩)
    · intro y hy
      refine ⟨hs hy, ?_⟩
      rw [h.bd_o]
      rintro (hyA | hyΒ)
      · obtain ⟨z, -, rfl⟩ := (h.A'_sub hyA).1
        exact cap.notMem_range X.cuff (hereg hy) (mem_range_self z)
      · exact disjoint_left.1 hedis hy (h.Β_F hyΒ)
  have hQd : Disjoint Q.U (discInt (D.ins F)) := by
    refine disjoint_left.2 fun y hy hyi ↦ ?_
    have hyc := hQe hy
    by_cases hyV : y ∈ D.rad.G.V
    · have hym : y ∈ closure e ∩ D.rad.G.V := ⟨hyc, hyV⟩
      rw [hset] at hym
      have hyF : y ∈ F.U := by
        rcases hym with rfl | hm
        · exact F.V_subset_U hxV
        · rw [mem_singleton_iff.1 hm]
          exact F.V_subset_U h.r_mem
      exact hyi.2 (hbd ▸ hyF)
    · have hye : y ∈ e := D.rad.G.closure_diff_V he ▸ (⟨hyc, hyV⟩ : y ∈ closure e \ D.rad.G.V)
      exact disjoint_left.1 h.out_ins (heDo hye) (discInt_subset _ hyi)
  have hl₂ := improve_card ht c₁.le
  have hl₁ := improve_card ht.swap c₂.le
  have hC₂ : Drawing.IsCircuitOf (D.rad.G.sup Q B) D.rad.G := ⟨D.rad.G.sup_isSubdrawing Q B,
    ht.left_circuit⟩
  have hC₁ : Drawing.IsCircuitOf (D.rad.G.sup Q P) D.rad.G := ⟨D.rad.G.sup_isSubdrawing Q P,
    ht.swap.left_circuit⟩
  have hcard : ∀ {X' Y : Drawing Shat}, TwoPaths D.rad.G F X' Y Q (cap.emb v) r →
    (D.rad.G.sup Q Y).E.ncard + X'.E.ncard = Q.E.ncard + F.E.ncard := by
    intro X' Y ht'
    have hE : (D.rad.G.sup Q Y).E = Q.E ∪ Y.E := Drawing.sup_E ht'.path.1 ht'.sub₂
    have hdis : Disjoint Q.E Y.E := disjoint_left.mpr fun e he he' ↦ disjoint_left.mp ht'.meet_E he
      (ht'.right.1.2 he')
    rw [hE, ncard_union_eq hdis Q.finite_edges Y.finite_edges, ht'.union_E,
      ncard_union_eq ht'.disj_E X'.finite_edges Y.finite_edges]
    omega
  have hrQ : r ∈ Q.U := by
    obtain ⟨W, -, hV, -⟩ := ht.path.2
    exact Q.V_subset_U (hV ▸ W.end_mem_support)
  have key : ∀ {Y : Drawing Shat}, Y.IsCircuitOf D.rad.G → Y.E.ncard < F.E.ncard → Y.U ⊆ Q.U ∪ F.U
    → Q.U ⊆ Y.U → (discInt (D.ins F) ∩ D.ins Y).Nonempty →
      ∃ F', F'.IsCircuitOf D.rad.G ∧ F'.E.ncard < F.E.ncard ∧ D.ins F ⊆ D.ins F' ∧ r ∈ F'.V := by
    intro Y hY hYle hU hQU hm
    have hYlt : Y.E.ncard < 2 * D.rep := by omega
    have hiY := D.ins_spec hY hYlt
    have hdj : Disjoint (discInt (D.ins F)) (discBd (D.ins Y)) := by
      rw [hiY.2.2.2.1]
      refine disjoint_left.2 fun x hx hxX ↦ ?_
      rcases hU hxX with h' | h'
      · exact disjoint_left.1 hQd h' hx
      · exact hx.2 (hbd ▸ h')
    have hsub : D.ins F ⊆ D.ins Y := by
      rcases hiY.2.2.1.side hman hdisc.isPreconnected_discInt hdj with h' | h'
      · rw [← closure_discInt hdisc]
        exact closure_minimal (h'.trans (discInt_subset _)) hiY.2.2.1.isClosed
      · obtain ⟨x, h₁, h₂⟩ := hm
        exact absurd h₂ (disjoint_left.1 h' h₁)
    exact ⟨Y, hY, hYle, hsub, mem_V_of_mem_U hY.1 (hQU hrQ) hrmem.2⟩
  obtain ⟨z, hz⟩ := hdisc.nonempty_discInt
  rcases ins_theta hrep ht hF hlt (by omega) (by omega) (discInt_subset _ hz) with h' | h'
  · refine key hC₁ ?_ ?_ ?_ ⟨z, hz, h'⟩
    · have := hcard ht.swap
      omega
    · rw [ht.swap.U_right]
      exact union_subset_union_right _ ht.left.1.U_subset
    · rw [ht.swap.U_right]
      exact subset_union_left
  · refine key hC₂ ?_ ?_ ?_ ⟨z, hz, h'⟩
    · have := hcard ht
      omega
    · rw [ht.U_right]
      exact union_subset_union_right _ ht.right.1.U_subset
    · rw [ht.U_right]
      exact subset_union_left

end IsSideSetting

end TangleDatum

end GraphMinor.GM19
