/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section10n

/-!
# Circuits with one pole inside

What a circuit with a pole inside and no pole on it looks like, near a cuff and near a path.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10

universe w

/-- A connected set that meets a closed set and its complement meets its frontier. -/
theorem inter_frontier_of_preconnected {X : Type*} [TopologicalSpace X] {t s : Set X}
  (ht : IsPreconnected t) (hs : IsClosed s) (h₁ : (t ∩ s).Nonempty)
    (h₂ : (t ∩ sᶜ).Nonempty) : (t ∩ frontier s).Nonempty := by
  by_contra hno
  have hin : ∀ x ∈ t, x ∈ s → x ∈ interior s := fun x hx hxs ↦ by
    by_contra hni
    exact hno ⟨x, hx, by rw [hs.frontier_eq]; exact ⟨hxs, hni⟩⟩
  obtain ⟨a, ha, has⟩ := h₁
  obtain ⟨z, -, hz₁, hz₂⟩ := ht _ _ isOpen_interior hs.isOpen_compl (fun x hx ↦ by
    by_cases hxs : x ∈ s
    · exact Or.inl (hin x hx hxs)
    · exact Or.inr hxs) ⟨a, ha, hin a ha has⟩ h₂
  exact hz₂ (interior_subset hz₁)

/-- A point of a line off `u` is joined to an end of the line, off `u`. -/
theorem line_part {S : Type} [TopologicalSpace S] {L : Set S} {a b x u : S}
  (hl : IsLineWithEnds L a b) (hx : x ∈ L) (hne : x ≠ u) :
    ∃ C ⊆ L \ {u}, x ∈ C ∧ IsPreconnected C ∧ (a ∈ C ∨ b ∈ C) := by
  obtain ⟨f, rfl, rfl⟩ := hl
  have hc : Continuous fun t ↦ (f t).1 := continuous_subtype_val.comp f.continuous
  let p := f.symm ⟨x, hx⟩
  have hp : (f p).1 = x := by simp [p]
  by_cases hu : u ∈ L
  · let q := f.symm ⟨u, hu⟩
    have hq : (f q).1 = u := by simp [q]
    have hinj : ∀ t, (f t).1 = u → t = q := fun t ht ↦ f.injective (Subtype.ext (ht.trans hq.symm))
    rcases le_total p q with hpq | hpq
    · refine ⟨(fun t ↦ (f t).1) '' Iic p, ?_, ⟨p, le_rfl, hp⟩, isPreconnected_Iic.image _
        hc.continuousOn,
        Or.inl ⟨0, unitInterval.nonneg _, rfl⟩⟩
      rintro _ ⟨t, ht, rfl⟩
      refine ⟨(f t).2, fun htu ↦ hne ?_⟩
      have := hinj t htu
      subst this
      rw [← hp, le_antisymm hpq ht]
      exact hq
    · refine ⟨(fun t ↦ (f t).1) '' Ici p, ?_, ⟨p, le_rfl, hp⟩, isPreconnected_Ici.image _
        hc.continuousOn,
        Or.inr ⟨1, unitInterval.le_one _, rfl⟩⟩
      rintro _ ⟨t, ht, rfl⟩
      refine ⟨(f t).2, fun htu ↦ hne ?_⟩
      have := hinj t htu
      subst this
      rw [← hp, le_antisymm (show p ≤ _ from ht) hpq]
      exact hq
  · have hL : L = (fun t ↦ (f t).1) '' univ := by
      ext y
      constructor
      · intro hy
        exact ⟨f.symm ⟨y, hy⟩, trivial, by simp⟩
      · rintro ⟨t, -, rfl⟩
        exact (f t).2
    refine ⟨L, fun y hy ↦ ⟨hy, fun h ↦ hu (h ▸ hy)⟩, hx, ?_, Or.inl (f 0).2⟩
    rw [hL]
    exact isPreconnected_univ.image _ hc.continuousOn

/-- A point of an `O`-arc with two marks, off `u`, is joined to a mark, off `u`. -/
theorem ring_part {S : Type} [TopologicalSpace S] {O V : Set S}
  (hO : IsOArc O) {a b x u : S} (ha : a ∈ O ∩ V) (hb : b ∈ O ∩ V) (hab : a ≠ b)
    (hx : x ∈ O) (hne : x ≠ u) : ∃ C ⊆ O \ {u}, x ∈ C ∧ IsPreconnected C ∧ (C ∩ V).Nonempty := by
  by_cases hu : u ∈ O
  · refine ⟨O \ {u}, Subset.rfl, ⟨hx, hne⟩, (isPathConnected_oArc_diff hO
      hu).isConnected.isPreconnected, ?_⟩
    by_cases hau : a = u
    · exact ⟨b, ⟨hb.1, fun h ↦ hab (hau.trans h.symm)⟩, hb.2⟩
    · exact ⟨a, ⟨ha.1, hau⟩, ha.2⟩
  · exact ⟨O, fun z hz ↦ ⟨hz, fun h ↦ hu (h ▸ hz)⟩, hx, hO.isPreconnected, ⟨a, ha⟩⟩

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {cap : IsCappedSurface S Shat} {β : Type w} {χ : ColourScheme S β}


omit [T2Space S] in
/-- A line whose ends are anchored in `K` is anchored in `K`. -/
theorem line_anchor {V K L : Set S} {a b : S} (hl : IsLineWithEnds L a b) (hsub : L ⊆ K)
    (ha : ∀ u, a ≠ u → ∃ C ⊆ K \ {u}, a ∈ C ∧ IsPreconnected C ∧ (C ∩ V).Nonempty)
    (hb : ∀ u, b ≠ u → ∃ C ⊆ K \ {u}, b ∈ C ∧ IsPreconnected C ∧ (C ∩ V).Nonempty) {x u : S}
      (hx : x ∈ L) (hne : x ≠ u) :
    ∃ C ⊆ K \ {u}, x ∈ C ∧ IsPreconnected C ∧ (C ∩ V).Nonempty := by
  obtain ⟨C, hC, hxC, hp, h⟩ := line_part hl hx hne
  have key : ∀ {c : S}, c ∈ C → (c ≠ u → ∃ C ⊆ K \ {u}, c ∈ C ∧ IsPreconnected C ∧
    (C ∩ V).Nonempty) →
      ∃ C ⊆ K \ {u}, x ∈ C ∧ IsPreconnected C ∧ (C ∩ V).Nonempty := by
    intro c hc hend
    obtain ⟨C', hC', hcC', hp', hne'⟩ := hend (hC hc).2
    refine ⟨C ∪ C', union_subset (hC.trans (sdiff_subset_sdiff_left hsub)) hC', Or.inl hxC,
      hp.union c hc hcC' hp', ?_⟩
    obtain ⟨z, hz⟩ := hne'
    exact ⟨z, Or.inr hz.1, hz.2⟩
  rcases h with h | h
  · exact key h (ha u)
  · exact key h (hb u)

namespace TangleDatum

variable {D : TangleDatum cap χ}

omit [T2Space S] in
/-- An edge of `Γ*` with a point inside a short circuit, and not on the circuit, lies inside the
circuit. -/
theorem edge_inside (D : TangleDatum cap χ) {C : Drawing Shat} (hC : C.IsCircuitOf D.rad.G)
  (hlt : C.E.ncard < 2 * D.rep) {e : Set Shat}
    (he : e ∈ D.rad.G.E) (heC : e ∉ C.E) (hm : (e ∩ D.ins C).Nonempty) : closure e ⊆ D.ins C := by
  have hT := cap.isClosedSurface
  have hi := D.ins_spec hC hlt
  have hfr : frontier (D.ins C) = C.U := by
    rw [IsClosedDisc.frontier_eq_discBd hT hi.2.2.1, hi.2.2.2.1]
  have hconn : IsPreconnected e := he.2.2.1.isConnected.isPreconnected
  refine closure_minimal (fun x hx ↦ ?_) hi.2.2.1.isClosed
  by_contra hn
  obtain ⟨z, hze, hzf⟩ := inter_frontier_of_preconnected hconn hi.2.2.1.isClosed hm ⟨x, hx, hn⟩
  rw [hfr] at hzf
  obtain ⟨f, hf, hzf'⟩ := C.exists_edge_of_mem hzf fun h ↦ edge_notMem_V he hze (hC.1.1 h)
  exact heC (D.rad.G.edge_eq_of_mem he (hC.1.2 hf) hze hzf' ▸ hf)

omit [T2Space S] in
/-- A walk that leaves the inside of a short circuit leaves it from a vertex of the circuit. -/
theorem exit_mem (D : TangleDatum cap χ) {C : Drawing Shat} (hC : C.IsCircuitOf D.rad.G)
  (hlt : C.E.ncard < 2 * D.rep) {e : Set Shat} {a y : Shat}
    (hl : D.rad.G.toGraph.IsLink e a y) (ha : a ∈ D.ins C) (hy : y ∉ D.ins C) : a ∈ C.V := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hi := D.ins_spec hC hlt
  have hfr : frontier (D.ins C) = C.U := by
    rw [IsClosedDisc.frontier_eq_discBd hT hi.2.2.1, hi.2.2.2.1]
  have hset : closure e ∩ D.rad.G.V = {a, y} := hl.2.2.2
  have hac : a ∈ closure e := (hset ▸ mem_insert a {y} : a ∈ closure e ∩ D.rad.G.V).1
  have hyc : y ∈ closure e := (hset ▸ mem_insert_of_mem a rfl : y ∈ closure e ∩ D.rad.G.V).1
  by_cases heC : e ∈ C.E
  · exact mem_V_of_mem_U hC.1 (C.closure_subset_U heC hac) hl.2.1
  · have hdis : e ∩ D.ins C = ∅ := by
      by_contra hne
      exact hy (D.edge_inside hC hlt hl.1 heC (nonempty_iff_ne_empty.2 hne) hyc)
    have hsub : e ⊆ (D.ins C)ᶜ := fun x hx hxi =>
      eq_empty_iff_forall_notMem.mp hdis x ⟨hx, hxi⟩
    have hcl : a ∈ closure (D.ins C)ᶜ := closure_mono hsub hac
    have : a ∈ frontier (D.ins C) := by
      rw [frontier_eq_closure_inter_closure]
      exact ⟨subset_closure ha, hcl⟩
    rw [hfr] at this
    exact mem_V_of_mem_U hC.1 this hl.2.1

omit [T2Space S] in
/-- A simple walk with only its first vertex inside a short circuit has only that point inside. -/
theorem walk_inter_ins (D : TangleDatum cap χ) {C : Drawing Shat} (hC : C.IsCircuitOf D.rad.G)
  (hlt : C.E.ncard < 2 * D.rep) {a b c : Shat}
    {W : GraphWalk D.rad.G.toGraph a b} (hW : W.IsSimple) (h : ∀ x ∈ W.support, x ∈ D.ins C → x
      = c) {x : Shat} (hx : x ∈ (walkDrawing D.rad.G W).U)
    (hxi : x ∈ D.ins C) : x = c := by
  have : ConnectedSpace Shat := cap.connected
  have hsub := walkDrawing_isSubdrawing D.rad.G W
  by_cases hxV : x ∈ (walkDrawing D.rad.G W).V
  · rw [walkDrawing_V] at hxV
    exact h x hxV hxi
  · exfalso
    obtain ⟨f, hf, hxf⟩ := (walkDrawing D.rad.G W).exists_edge_of_mem hx hxV
    have hf' : f ∈ W.edges := by
      rw [walkDrawing_E] at hf
      exact hf
    by_cases hfC : f ∈ C.E
    · exact edge_off hW h hf' ((C.closure_subset_U hfC).trans (D.U_subset_ins hC hlt))
    · exact edge_off hW h hf' (D.edge_inside hC hlt (hsub.2 hf) hfC ⟨x, hxf, hxi⟩)

variable (hS : IsSurface S)
include hS

omit hS in
omit [T2Space S] in
/-- A cuff disc with its pole outside a circuit in `Σ` misses the inside of the circuit. -/
theorem cuffDisc_disjoint_ins (D : TangleDatum cap χ) {C : Drawing Shat}
  (hC : C.IsCircuitOf D.rad.G) (hlt : C.E.ncard < 2 * D.rep)
    (hr : C.U ⊆ range cap.emb) {p : Shat} (hp : p ∈ D.rad.poles) {Θ : Set S} (hΘ : Θ ∈ cuffs S)
      (hreg : D.rad.regionOf p = cap.cuffDisc Θ)
    (hpi : p ∉ D.ins C) : Disjoint (cap.cuffDisc Θ) (D.ins C) := by
  have hT := cap.isClosedSurface
  have hi := D.ins_spec hC hlt
  have hfr : frontier (D.ins C) = C.U := by
    rw [IsClosedDisc.frontier_eq_discBd hT hi.2.2.1, hi.2.2.2.1]
  have hconn : IsPreconnected (cap.cuffDisc Θ) := hreg ▸ isPreconnected_connectedComponentIn
  have hpd := (D.rad.regionOf_mem hp.1).2
  rw [hreg] at hpd
  refine disjoint_left.2 fun x hx hxi ↦ ?_
  obtain ⟨z, hz, hzf⟩ := inter_frontier_of_preconnected hconn hi.2.2.1.isClosed ⟨x, hx, hxi⟩ ⟨p,
    hpd, hpi⟩
  rw [hfr] at hzf
  exact cap.notMem_range hΘ hz (hr hzf)

omit hS in
omit [T2Space S] in
/-- A point of a cuff inside a circuit in `Σ`, with the pole of that cuff outside, lies on the
circuit. -/
theorem cuff_inter_ins (D : TangleDatum cap χ) {C : Drawing Shat} (hC : C.IsCircuitOf D.rad.G)
  (hlt : C.E.ncard < 2 * D.rep)
    (hr : C.U ⊆ range cap.emb) {p : Shat} (hp : p ∈ D.rad.poles) {Θ : Set S} (hΘ : Θ ∈ cuffs S)
      (hreg : D.rad.regionOf p = cap.cuffDisc Θ)
    (hpi : p ∉ D.ins C) {x : Shat} (hx : x ∈ closure (cap.cuffDisc Θ))
      (hxi : x ∈ D.ins C) : x ∈ C.U := by
  have hT := cap.isClosedSurface
  have hi := D.ins_spec hC hlt
  have hfr : frontier (D.ins C) = C.U := by
    rw [IsClosedDisc.frontier_eq_discBd hT hi.2.2.1, hi.2.2.2.1]
  rw [← hfr, frontier_eq_closure_inter_closure]
  refine ⟨subset_closure hxi, closure_mono (fun y hy ↦ ?_) hx⟩
  exact disjoint_left.1 (D.cuffDisc_disjoint_ins hC hlt hr hp hΘ hreg hpi) hy

variable (h3 : D.P.Γ.IsInternallyThreeConnected)
include h3

omit hS h3 in
omit [T2Space S] in
/-- A path through a pole off `F`, between two vertices of `F` on the cuff of that pole. -/
theorem exists_theta_pole {F : Drawing Shat} (hF : F.IsCircuitOf D.rad.G) {p : Shat}
  (hp : p ∈ D.rad.poles) (hpF : p ∉ F.V) {v₁ v₂ : S} (hv₁ : v₁ ∈ D.P.Γ.V)
    (hv₂ : v₂ ∈ D.P.Γ.V) (hne : v₁ ≠ v₂) (hF₁ : cap.emb v₁ ∈ F.V) (hF₂ : cap.emb v₂ ∈ F.V) {e₁ e₂ :
      Set Shat} (he₁ : e₁ ∈ D.rad.G.E) (he₂ : e₂ ∈ D.rad.G.E)
    (hs₁ : closure e₁ ∩ D.rad.G.V = {cap.emb v₁, p}) (hs₂ : closure e₂ ∩ D.rad.G.V
      = {cap.emb v₂, p}) :
    ∃ A B Q, TwoPaths D.rad.G F A B Q (cap.emb v₁) (cap.emb v₂) ∧ p ∈ Q.V ∧ Q.E.ncard ≤ A.E.ncard
      ∧ Q.E.ncard ≤ B.E.ncard ∧
      Q.U ⊆ closure e₁ ∪ closure e₂ := by
  classical
  have : ConnectedSpace Shat := cap.connected
  set G := D.rad.G with hG
  have hvG : ∀ {v}, v ∈ D.P.Γ.V → cap.emb v ∈ G.V := fun hv ↦ D.rad.isPreRadial.2.1
    (mem_image_of_mem _ hv)
  have hpG : p ∈ G.V := hp.1.1
  have hvp : ∀ {v}, v ∈ D.P.Γ.V → cap.emb v ≠ p := fun hv h ↦ hp.1.2 (h ▸ mem_image_of_mem _ hv)
  have hvne : cap.emb v₁ ≠ cap.emb v₂ := fun h ↦ hne (cap.isEmbedding.injective h)
  have hl₁ : G.toGraph.IsLink e₁ (cap.emb v₁) p := ⟨he₁, hvG hv₁, hpG, hs₁⟩
  have hl₂ : G.toGraph.IsLink e₂ p (cap.emb v₂) := ⟨he₂, hpG, hvG hv₂, by rw [hs₂, pair_comm]⟩
  have hclo : ∀ f ∈ F.E, p ∉ closure f := fun f hf hc ↦ hpF (mem_V_of_mem_U hF.1
    (F.closure_subset_U hf hc) hpG)
  have hn₁ : e₁ ∉ F.E := fun h ↦ hclo e₁ h (by
    have : p ∈ closure e₁ ∩ D.rad.G.V := by rw [hs₁]; exact Or.inr rfl
    exact this.1)
  have hn₂ : e₂ ∉ F.E := fun h ↦ hclo e₂ h (by
    have : p ∈ closure e₂ ∩ D.rad.G.V := by rw [hs₂]; exact Or.inr rfl
    exact this.1)
  have hene : e₁ ≠ e₂ := by
    rintro rfl
    have hm : cap.emb v₂ ∈ ({cap.emb v₁, p} : Set Shat) := hs₁ ▸ hs₂ ▸ Or.inl rfl
    rcases hm with h | h
    · exact hvne h.symm
    · exact hvp hv₂ h
  obtain ⟨A, B, hA, hB, hAs, hBs, -, -, hAB, hd, hsup⟩ := hF.2.exists_two_paths hF₁ hF₂ hvne
  let W : GraphWalk G.toGraph (cap.emb v₁) (cap.emb v₂) := .cons hl₁ (.cons hl₂ (.nil (hvG hv₂)))
  have hWs : W.IsSimple := by
    simp [GraphWalk.IsSimple, W, GraphWalk.support, hvp hv₁, hvne, (hvp hv₂).symm]
  have hQV : (walkDrawing G W).V = {cap.emb v₁, p, cap.emb v₂} := by
    rw [walkDrawing_V]; ext x; simp [W, GraphWalk.support]
  have hQE : (walkDrawing G W).E = {e₁, e₂} := by
    rw [walkDrawing_E]; ext x; simp [W, GraphWalk.edges]
  have ht : TwoPaths G F A B (walkDrawing G W) (cap.emb v₁) (cap.emb v₂) := by
    refine ⟨hvne, hF.1, ⟨hAs, hA⟩, ⟨hBs, hB⟩, ?_, ?_, hAB.le, hd,
      ⟨walkDrawing_isSubdrawing _ _, walkDrawing_isPathBetween _ hWs⟩, ?_, ?_⟩
    · conv_lhs => rw [← hsup, Drawing.sup_V hAs hBs]
    · conv_lhs => rw [← hsup, Drawing.sup_E hAs hBs]
    · rw [hQV]
      rintro x ⟨rfl | rfl | rfl, hx⟩
      · exact Or.inl rfl
      · exact absurd hx hpF
      · exact Or.inr rfl
    · rw [hQE]
      refine disjoint_left.mpr ?_
      rintro _ (rfl | rfl) h
      · exact hn₁ h
      · exact hn₂ h
  have side : ∀ {X : Drawing Shat}, X.IsPathBetween (cap.emb v₁) (cap.emb v₂) → X.IsSubdrawing F →
      (walkDrawing G W).E.ncard ≤ X.E.ncard := by
    intro X hX hXs
    obtain ⟨f, hf, x, hl, -, hsec⟩ := path_first hX hvne
    have hlG := ((hXs.trans hF.1).isLink_iff hf).mp hl
    obtain ⟨hxR, -⟩ := D.rad.link_cases' hlG hv₁
    obtain ⟨f', hf', hff, -⟩ := hsec fun h ↦ hxR.2 (h ▸ mem_image_of_mem _ hv₂)
    have hsub : ({f, f'} : Set (Set Shat)) ⊆ X.E := by
      rintro _ (rfl | rfl)
      · exact hf
      · exact hf'
    rw [hQE, ncard_pair hene, ← ncard_pair hff.symm]
    exact ncard_le_ncard hsub X.finite_edges
  refine ⟨A, B, _, ht, by rw [hQV]; simp, side hA hAs, side hB hBs, fun x hx ↦ ?_⟩
  rw [mem_walkDrawing_U] at hx
  rcases hx with hx | ⟨f, hf, hxf⟩
  · have hmem₁ : cap.emb v₁ ∈ closure e₁ ∩ D.rad.G.V := by rw [hs₁]; exact Or.inl rfl
    have hmem₂ : p ∈ closure e₁ ∩ D.rad.G.V := by rw [hs₁]; exact Or.inr rfl
    have hmem₃ : cap.emb v₂ ∈ closure e₂ ∩ D.rad.G.V := by rw [hs₂]; exact Or.inl rfl
    simp only [W, GraphWalk.support, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact Or.inl hmem₁.1
    · exact Or.inl hmem₂.1
    · exact Or.inr hmem₃.1
  · simp only [W, GraphWalk.edges, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    · exact Or.inl hxf
    · exact Or.inr hxf

/-- No short circuit has a pole inside it and two vertices on the cuff of a pole outside it, if no
short circuit has two poles inside. -/
theorem no_double_touch {n : ℕ} (hn : n < D.rep) (hNP : ¬ ∃ C, D.IsPairCircuit n C) {C : Drawing
  Shat} (hC : C.IsCircuitOf D.rad.G) (hc : C.E.ncard ≤ 2 * n)
    {r p : Shat} (hr : r ∈ D.rad.poles) (hri : r ∈ D.ins C) (hp : p ∈ D.rad.poles) (hrp : r ≠ p)
      (hpC : p ∉ C.V) {Θ : Set S} (hΘ : Θ ∈ cuffs S)
    (hreg : D.rad.regionOf p = cap.cuffDisc Θ) {v₁ v₂ : S} (hv₁ : v₁ ∈ D.P.Γ.V)
      (hv₂ : v₂ ∈ D.P.Γ.V) (hne : v₁ ≠ v₂) (h₁ : v₁ ∈ Θ) (h₂ : v₂ ∈ Θ)
    (hF₁ : cap.emb v₁ ∈ C.V) (hF₂ : cap.emb v₂ ∈ C.V) : False := by
  have : ConnectedSpace Shat := cap.connected
  have hrep : 1 ≤ D.rep := by omega
  obtain ⟨e₁, he₁, hs₁⟩ := D.rad.exists_pole_edge hS h3 hp hΘ hreg hv₁ h₁
  obtain ⟨e₂, he₂, hs₂⟩ := D.rad.exists_pole_edge hS h3 hp hΘ hreg hv₂ h₂
  obtain ⟨A, B, Q, ht, hpQ, c₁, c₂, -⟩ := exists_theta_pole hC hp hpC hv₁ hv₂ hne hF₁ hF₂ he₁ he₂
    hs₁ hs₂
  have hl₂ := improve_card ht c₁
  have hl₁ := improve_card ht.swap c₂
  have hC₂ : Drawing.IsCircuitOf (D.rad.G.sup Q B) D.rad.G := ⟨D.rad.G.sup_isSubdrawing Q B,
    ht.left_circuit⟩
  have hC₁ : Drawing.IsCircuitOf (D.rad.G.sup Q A) D.rad.G := ⟨D.rad.G.sup_isSubdrawing Q A,
    ht.swap.left_circuit⟩
  have key : ∀ {X : Drawing Shat}, X.IsCircuitOf D.rad.G → X.E.ncard ≤ C.E.ncard → Q.U ⊆ X.U
    → r ∈ D.ins X → False := by
    intro X hX hl hQX hrX
    have hlt : X.E.ncard < 2 * D.rep := by omega
    exact hNP ⟨X, hX, by omega, r, hr, p, hp, hrp, hrX, D.U_subset_ins hX hlt (hQX
      (Q.V_subset_U hpQ))⟩
  rcases ins_theta hrep ht hC (by omega) (by omega) (by omega) hri with h | h
  · exact key hC₁ hl₁ (by rw [ht.swap.U_right]; exact subset_union_left) h
  · exact key hC₂ hl₂ (by rw [ht.U_right]; exact subset_union_left) h

omit [T2Space S] in
/-- A circuit in `Σ` with at most one point on the boundary and with a pole inside holds two
vertices of `Γ`. -/
theorem ring_marks [Nonempty S] {C : Drawing Shat} (hC : C.IsCircuitOf D.rad.G)
  (hlt : C.E.ncard < 2 * D.rep)
    (hnp : ∀ z ∈ C.V, z ∉ D.rad.poles) (hone : ∀ {x y : S}, x ∈ bd S → y ∈ bd S → cap.emb x ∈ C.U
      → cap.emb y ∈ C.U → x = y) {r : Shat} (hr : r ∈ D.rad.poles)
    (hri : r ∈ D.ins C) : IsOArc (cap.emb ⁻¹' C.U) ∧ ∃ a b, a ≠ b ∧ a ∈ cap.emb ⁻¹' C.U ∩ D.P.Γ.V
      ∧ b ∈ cap.emb ⁻¹' C.U ∩ D.P.Γ.V := by
  have : ConnectedSpace Shat := cap.connected
  obtain ⟨K, h₁, hKU, hO, hsing⟩ := ring_of_circuit hS D.rad D.P.fits hC.1 hC.2 hnp hone
  have hKU' : cap.emb ⁻¹' C.U = K.U := by rw [hKU, preimage_image_eq _ cap.isEmbedding.injective]
  obtain ⟨a, ha, b, hb, hab⟩ := two_vertices_of_ring (D := D) h3 hO h₁.inter hsing fun Δ d₁ d₂ d₃
    d₄ ↦
    D.no_empty_disc hS hC hlt hr hri d₁ d₂ (d₃.trans hKU.symm) (by rwa [hKU])
  rw [hKU']
  exact ⟨hO, a, b, hab, ha, hb⟩

end TangleDatum

end GraphMinor.GM19
