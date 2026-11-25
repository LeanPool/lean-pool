/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.FreeShape
public import LeanPool.GraphMinor.GM19.Section10r

/-!
# The circuit of a freedom flaw

We pick a flaw circuit `F` that is shortest and, among the shortest, has the most vertices of `Γ*`
in `ins(F)`. By (8.7) it is
`λ`-linked to `𝒯`. A path of `Γ*` outside `ins(F)` with its ends on `F` makes a circuit that is no
longer and whose inside is larger
(`theta_contra`). So only one pole lies in `ins(F)` (`vDist_le_of_ins`), and each other cuff meets
`ins(F)` in at most one point.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {cap : IsCappedSurface S Shat} {β : Type w} {χ : ColourScheme S β}


namespace TangleDatum

variable {D : TangleDatum cap χ}

/-- A circuit as in the definition of "`n`-flawed in freedom". -/
def IsFreeCircuit (D : TangleDatum cap χ) (n : ℕ) (C : Drawing Shat) : Prop :=
  C.IsCircuitOf D.rad.G ∧ C.E.ncard ≤ 2 * n ∧ ((∃ side ∈ χ.Φ.longSides, cap.emb '' side ⊆ D.ins C) ∨
    C.E.ncard < 2 * ((cap.emb '' χ.Φ.V) ∩ D.ins C).ncard)

/-- The number of vertices of `Γ*` inside a circuit. -/
noncomputable def insCount (D : TangleDatum cap χ) (C : Drawing Shat) : ℕ :=
  (D.rad.G.V ∩ D.ins C).ncard

omit [T2Space S] in
omit [T2Space Shat] in
theorem IsFreeCircuit.mono {n : ℕ} {C C' : Drawing Shat} (h : D.IsFreeCircuit n C)
  (hC' : C'.IsCircuitOf D.rad.G) (hle : C'.E.ncard ≤ C.E.ncard)
    (hsub : D.ins C ⊆ D.ins C') : D.IsFreeCircuit n C' := by
  refine ⟨hC', hle.trans h.2.1, ?_⟩
  rcases h.2.2 with ⟨s, hs, hsub'⟩ | hlt
  · exact Or.inl ⟨s, hs, hsub'.trans hsub⟩
  · refine Or.inr (lt_of_le_of_lt hle (lt_of_lt_of_le hlt ?_))
    have hf : ((cap.emb '' χ.Φ.V) ∩ D.ins C').Finite := (χ.Φ.finite_V.image _).subset
      inter_subset_left
    have := ncard_le_ncard (inter_subset_inter_right (cap.emb '' χ.Φ.V) hsub) hf
    omega

variable (hS : IsSurface S) (h3 : D.P.Γ.IsInternallyThreeConnected)

include hS h3 in
/-- **A least flaw circuit that is linked.** -/
theorem exists_least_free {n : ℕ} (hn : n < D.rep) (h : ∃ C, D.IsFreeCircuit n C) :
    ∃ F, D.IsFreeCircuit n F ∧ GM18.IsLambdaLinkedTo D.tb.lambdaOrder D.𝒯 (partIn cap D.P.Γ
      (D.ins F)) (partIn cap D.P.Γ (closure (D.ins F)ᶜ)) ∧
      ∀ C, D.IsFreeCircuit n C → F.E.ncard ≤ C.E.ncard ∧ (F.E.ncard = C.E.ncard → D.insCount C
        ≤ D.insCount F) := by
  have hfin : {C | D.IsFreeCircuit n C}.Finite := (finite_circuits D.rad.G).subset fun C hC ↦
    ⟨hC.1.2, hC.1.1⟩
  obtain ⟨F₀, hF₀, hmin⟩ := Set.exists_min_image _ (fun C ↦ C.E.ncard) hfin h
  have hfin' : {C | D.IsFreeCircuit n C ∧ C.E.ncard = F₀.E.ncard}.Finite
    := hfin.subset fun C hC ↦ hC.1
  obtain ⟨F₁, hF₁, hmax⟩ := Set.exists_max_image _ (fun C ↦ D.insCount C) hfin' ⟨F₀, hF₀, rfl⟩
  have hlt : F₁.E.ncard < 2 * D.rep := by have := hF₁.1.2.1; omega
  obtain ⟨F, hF, hle, -, hsub, hlink⟩ := exists_linked hS h3 hF₁.1.1 hlt
  have hfree := hF₁.1.mono hF hle hsub
  have heq : F.E.ncard = F₀.E.ncard := le_antisymm (hle.trans hF₁.2.le) (hmin F hfree)
  have hcount : D.insCount F₁ ≤ D.insCount F :=
    ncard_le_ncard (inter_subset_inter_right _ hsub) (D.rad.G.finite_V.subset inter_subset_left)
  refine ⟨F, hfree, hlink, fun C hC ↦ ⟨heq ▸ hmin C hC, fun he ↦ ?_⟩⟩
  exact (hmax C ⟨hC, by omega⟩).trans hcount

omit [T2Space S] [T2Space Shat] in
/-- A circuit of `Γ*` has twice as many edges as vertices of `Γ`. -/
theorem ncard_E_eq_hat (D : TangleDatum cap χ) {C : Drawing Shat} (hC : C.IsCircuitOf D.rad.G) :
    C.E.ncard = 2 * (C.V ∩ D.P.Γ.hatV cap).ncard := by
  have : ConnectedSpace Shat := cap.connected
  refine IsCircuit.ncard_E_eq hC.2 fun e x y hl ↦ ?_
  have hlG := (hC.1.isLink_iff hl.1).mp hl
  obtain ⟨v, hv, w, hw, hset⟩ := D.rad.edge_ends hlG.1
  have hset' : ({x, y} : Set Shat) = {cap.emb v, w} := hlG.2.2.2.symm.trans hset
  have hvh : cap.emb v ∈ D.P.Γ.hatV cap := mem_image_of_mem _ hv
  rcases Set.pair_eq_pair_iff.1 hset' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨fun _ ↦ hw.2, fun _ ↦ hvh⟩
  · exact ⟨fun h ↦ absurd h hw.2, fun h ↦ absurd hvh h⟩

omit [T2Space S] in
/-- Two poles inside a short circuit are close. -/
theorem vDist_le_of_ins {n : ℕ} (hn : n < D.rep) {C : Drawing Shat} (hC : C.IsCircuitOf D.rad.G)
  (hc : C.E.ncard ≤ 2 * n) {r₁ r₂ : Shat}
    (h₁ : r₁ ∈ D.rad.poles) (h₂ : r₂ ∈ D.rad.poles) (hne : r₁ ≠ r₂) (hi₁ : r₁ ∈ D.ins C)
      (hi₂ : r₂ ∈ D.ins C) : D.vDist r₁ r₂ ≤ n := by
  classical
  have : ConnectedSpace Shat := cap.connected
  have hlt : C.E.ncard < 2 * D.rep := by omega
  obtain ⟨e, he⟩ := IsCircuit.E_nonempty hC.2
  obtain ⟨v, -, w, -, hset⟩ := D.rad.edge_ends (hC.1.2 he)
  have hvC : cap.emb v ∈ C.V := by
    have hm : cap.emb v ∈ closure e ∩ D.rad.G.V := by rw [hset]; exact Or.inl rfl
    exact mem_V_of_mem_U hC.1 (C.closure_subset_U he hm.1) hm.2
  obtain ⟨W, hl, -, hW⟩ := exists_circuit_walk hC hvC
  have hE := D.ncard_E_eq_hat hC
  let T : ClosedWalkIns D.rad D.ord D.𝒯 :=
    { base := cap.emb v
      walk := W
      sub := C
      halfLen := (C.V ∩ D.P.Γ.hatV cap).ncard
      ins := C.U ∪ ⋃ (F : Drawing Shat) (_ : F.IsSubdrawing C) (Δ : Set Shat)
        (_ : IsInsOf D.rad D.ord D.𝒯 F Δ), Δ
      sub_eq := hW.symm
      walk_len := by omega
      halfLen_lt := by
        change _ < D.rep
        omega
      ins_eq := rfl }
  have hsub : D.ins C ⊆ T.ins := fun x hx ↦ Or.inr (mem_iUnion.2 ⟨C, mem_iUnion.2
    ⟨Drawing.IsSubdrawing.refl C, mem_iUnion.2 ⟨D.ins C,
    mem_iUnion.2 ⟨D.ins_spec hC hlt, hx⟩⟩⟩⟩)
  have ha₁ : D.rad.atomOf r₁ = D.rad.regionOf r₁ := by
    unfold RadialDrawing.atomOf
    rw [ite_eq_right h₁.1.2]
  have ha₂ : D.rad.atomOf r₂ = D.rad.regionOf r₂ := by
    unfold RadialDrawing.atomOf
    rw [ite_eq_right h₂.1.2]
  have m₁ := D.rad.regionOf_mem h₁.1
  have m₂ := D.rad.regionOf_mem h₂.1
  have hreg : D.rad.regionOf r₁ ≠ D.rad.regionOf r₂ := fun heq ↦ by
    obtain ⟨-, -, hG3, -⟩ := id D.rad.isPreRadial
    exact hne ((hG3 _ m₁.1).unique ⟨m₁.2, h₁.1.1⟩ ⟨heq ▸ m₂.2, h₂.1.1⟩)
  have hm₁ : (D.rad.regionOf r₁ ∩ T.ins).Nonempty := ⟨r₁, m₁.2, hsub hi₁⟩
  have hm₂ : (D.rad.regionOf r₂ ∩ T.ins).Nonempty := ⟨r₂, m₂.2, hsub hi₂⟩
  have hk : D.vDist r₁ r₂ ≤ T.halfLen := by
    rw [vDist, ha₁, ha₂, dist, tangleMetric, ite_eq_right hreg, ite_eq_left ⟨T, hm₁, hm₂⟩]
    exact Nat.sInf_le ⟨T, hm₁, hm₂, rfl⟩
  have : T.halfLen ≤ n := by
    change (C.V ∩ D.P.Γ.hatV cap).ncard ≤ n
    omega
  omega

omit [T2Space S] in
/-- **A path outside a least flaw circuit improves it.** -/
theorem theta_contra {n : ℕ} (hn : n < D.rep) {F A B Q : Drawing Shat} {a b : Shat}
  (hF : D.IsFreeCircuit n F)
    (hmin : ∀ C, D.IsFreeCircuit n C → F.E.ncard ≤ C.E.ncard ∧ (F.E.ncard = C.E.ncard
      → D.insCount C ≤ D.insCount F))
    (ht : TwoPaths D.rad.G F A B Q a b) (hQ : Disjoint Q.U (discInt (D.ins F))) (c₁ : Q.E.ncard
      ≤ A.E.ncard) (c₂ : Q.E.ncard ≤ B.E.ncard)
    (hcase : (∃ q ∈ Q.V, q ∉ D.ins F) ∨ (Q.E.ncard < A.E.ncard ∧ Q.E.ncard < B.E.ncard)) : False
      := by
  have hT := cap.isClosedSurface
  have hman : ∀ x : Shat, IsManifoldPoint x := fun x ↦ (hT.2.2 x).isManifoldPoint
  have : ConnectedSpace Shat := cap.connected
  have hFc := hF.1
  have hle := hF.2.1
  have hrep : 1 ≤ D.rep := by omega
  have hlt : F.E.ncard < 2 * D.rep := by omega
  have hi := D.ins_spec hFc hlt
  have hdisc := hi.2.2.1
  have hbd : discBd (D.ins F) = F.U := hi.2.2.2.1
  have hl₂ := improve_card ht c₁
  have hl₁ := improve_card ht.swap c₂
  have hC₂ : Drawing.IsCircuitOf (D.rad.G.sup Q B) D.rad.G := ⟨D.rad.G.sup_isSubdrawing Q B,
    ht.left_circuit⟩
  have hC₁ : Drawing.IsCircuitOf (D.rad.G.sup Q A) D.rad.G := ⟨D.rad.G.sup_isSubdrawing Q A,
    ht.swap.left_circuit⟩
  have hcard : ∀ {X Y : Drawing Shat}, TwoPaths D.rad.G F X Y Q a b →
    (D.rad.G.sup Q Y).E.ncard + X.E.ncard = Q.E.ncard + F.E.ncard := by
    intro X Y ht'
    have hE : (D.rad.G.sup Q Y).E = Q.E ∪ Y.E := Drawing.sup_E ht'.path.1 ht'.sub₂
    have hdis : Disjoint Q.E Y.E := disjoint_left.mpr fun e he he' ↦ disjoint_left.mp ht'.meet_E he
      (ht'.right.1.2 he')
    rw [hE, ncard_union_eq hdis Q.finite_edges Y.finite_edges, ht'.union_E,
      ncard_union_eq ht'.disj_E X.finite_edges Y.finite_edges]
    omega
  have key : ∀ {X : Drawing Shat}, X.IsCircuitOf D.rad.G → X.E.ncard ≤ F.E.ncard → X.U ⊆ Q.U ∪ F.U
    → Q.U ⊆ X.U →
      ((∀ q ∈ Q.V, q ∈ D.ins F) → X.E.ncard < F.E.ncard) → (discInt (D.ins F) ∩ D.ins X).Nonempty
        → False := by
    intro X hX hXle hU hQU hstrict hm
    have hXlt : X.E.ncard < 2 * D.rep := by omega
    have hiX := D.ins_spec hX hXlt
    have hdj : Disjoint (discInt (D.ins F)) (discBd (D.ins X)) := by
      rw [hiX.2.2.2.1]
      refine disjoint_left.2 fun x hx hxX ↦ ?_
      rcases hU hxX with h | h
      · exact disjoint_left.1 hQ h hx
      · exact hx.2 (hbd ▸ h)
    have hsub : D.ins F ⊆ D.ins X := by
      rcases hiX.2.2.1.side hman hdisc.isPreconnected_discInt hdj with h | h
      · rw [← closure_discInt hdisc]
        exact closure_minimal (h.trans (discInt_subset _)) hiX.2.2.1.isClosed
      · obtain ⟨x, h₁, h₂⟩ := hm
        exact absurd h₂ (disjoint_left.1 h h₁)
    obtain ⟨m₁, m₂⟩ := hmin X (hF.mono hX hXle hsub)
    by_cases hall : ∀ q ∈ Q.V, q ∈ D.ins F
    · have := hstrict hall
      omega
    · push Not at hall
      obtain ⟨q, hqQ, hqF⟩ := hall
      have hcount := m₂ (le_antisymm m₁ hXle)
      have hssub : D.rad.G.V ∩ D.ins F ⊂ D.rad.G.V ∩ D.ins X := by
        refine ⟨inter_subset_inter_right _ hsub, fun h ↦ ?_⟩
        have hqG : q ∈ D.rad.G.V := ht.path.1.1 hqQ
        exact hqF (h ⟨hqG, D.U_subset_ins hX hXlt (hQU (Q.V_subset_U hqQ))⟩).2
      have := ncard_lt_ncard hssub (D.rad.G.finite_V.subset inter_subset_left)
      unfold insCount at hcount
      omega
  obtain ⟨z, hz⟩ := hdisc.nonempty_discInt
  rcases ins_theta hrep ht hFc hlt (by omega) (by omega) (discInt_subset _ hz) with h | h
  · refine key hC₁ hl₁ ?_ ?_ ?_ ⟨z, hz, h⟩
    · rw [ht.swap.U_right]
      exact union_subset_union_right _ ht.left.1.U_subset
    · rw [ht.swap.U_right]
      exact subset_union_left
    · intro hq
      rcases hcase with ⟨q, h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact absurd (hq q h₁) h₂
      · have := hcard ht.swap
        omega
  · refine key hC₂ hl₂ ?_ ?_ ?_ ⟨z, hz, h⟩
    · rw [ht.U_right]
      exact union_subset_union_right _ ht.right.1.U_subset
    · rw [ht.U_right]
      exact subset_union_left
    · intro hq
      rcases hcase with ⟨q, h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact absurd (hq q h₁) h₂
      · have := hcard ht
        omega

include hS h3 in
/-- A chord of a circuit through a pole on the circuit, from a vertex of `Γ` on the circuit that is
not next to the pole. -/
theorem exists_theta_chord {F : Drawing Shat} (hF : F.IsCircuitOf D.rad.G) {p : Shat}
  (hp : p ∈ D.rad.poles) (hpF : p ∈ F.V) {v : S}
    (hv : v ∈ D.P.Γ.V) (hFv : cap.emb v ∈ F.V) {e : Set Shat} (he : e ∈ D.rad.G.E)
      (hs : closure e ∩ D.rad.G.V = {cap.emb v, p}) (hn : e ∉ F.E) :
    ∃ A B Q, TwoPaths D.rad.G F A B Q (cap.emb v) p ∧ Q.U ⊆ closure e ∧ Q.E.ncard < A.E.ncard
      ∧ Q.E.ncard < B.E.ncard := by
  classical
  have : ConnectedSpace Shat := cap.connected
  set G := D.rad.G with hG
  have hvG : cap.emb v ∈ G.V := D.rad.isPreRadial.2.1 (mem_image_of_mem _ hv)
  have hpG : p ∈ G.V := hp.1.1
  have hvp : cap.emb v ≠ p := fun h ↦ hp.1.2 (h ▸ mem_image_of_mem _ hv)
  have hl₁ : G.toGraph.IsLink e (cap.emb v) p := ⟨he, hvG, hpG, hs⟩
  obtain ⟨A, B, hA, hB, hAs, hBs, -, -, hAB, hd, hsup⟩ := hF.2.exists_two_paths hFv hpF hvp
  let W : GraphWalk G.toGraph (cap.emb v) p := .cons hl₁ (.nil hpG)
  have hWs : W.IsSimple := by
    simp [GraphWalk.IsSimple, W, GraphWalk.support, hvp]
  have hQV : (walkDrawing G W).V = {cap.emb v, p} := by
    rw [walkDrawing_V]; ext x; simp [W, GraphWalk.support]
  have hQE : (walkDrawing G W).E = {e} := by
    rw [walkDrawing_E]; ext x; simp [W, GraphWalk.edges]
  have ht : TwoPaths G F A B (walkDrawing G W) (cap.emb v) p := by
    refine ⟨hvp, hF.1, ⟨hAs, hA⟩, ⟨hBs, hB⟩, ?_, ?_, hAB.le, hd,
      ⟨walkDrawing_isSubdrawing _ _, walkDrawing_isPathBetween _ hWs⟩, ?_, ?_⟩
    · conv_lhs => rw [← hsup, Drawing.sup_V hAs hBs]
    · conv_lhs => rw [← hsup, Drawing.sup_E hAs hBs]
    · rw [hQV]; exact inter_subset_left
    · rw [hQE]; simpa using hn
  have side : ∀ {X : Drawing Shat}, X.IsPathBetween (cap.emb v) p → X.IsSubdrawing F →
    (walkDrawing G W).E.ncard < X.E.ncard := by
    intro X hX hXs
    obtain ⟨f, hf, x, hl, -, hsec⟩ := path_first hX hvp
    have hfF := hXs.2 hf
    have hlG := ((hXs.trans hF.1).isLink_iff hf).mp hl
    obtain ⟨hxR, hset⟩ := D.rad.link_cases' hlG hv
    have hxp : x ≠ p := by
      rintro rfl
      exact hn (D.rad.edge_unique hS h3 he (hF.1.2 hfF) hv hxR hs hset ▸ hfF)
    obtain ⟨f', hf', hff, -⟩ := hsec hxp
    have hsub : ({f, f'} : Set (Set Shat)) ⊆ X.E := by
      rintro _ (rfl | rfl)
      · exact hf
      · exact hf'
    rw [hQE, ncard_singleton]
    have := ncard_le_ncard hsub X.finite_edges
    rw [ncard_pair hff.symm] at this
    omega
  refine ⟨A, B, _, ht, fun x hx ↦ ?_, side hA hAs, side hB hBs⟩
  rw [mem_walkDrawing_U] at hx
  rcases hx with hx | ⟨f, hf, hxf⟩
  · have hmem₁ : cap.emb v ∈ closure e ∩ D.rad.G.V := by rw [hs]; exact Or.inl rfl
    have hmem₂ : p ∈ closure e ∩ D.rad.G.V := by rw [hs]; exact Or.inr rfl
    simp only [W, GraphWalk.support, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact hmem₁.1
    · exact hmem₂.1
  · simp only [W, GraphWalk.edges, List.mem_cons, List.not_mem_nil, or_false] at hf
    subst hf
    exact hxf

include hS in
omit [T2Space S] [T2Space Shat] hS in
/-- A subdrawing of `Γ*` with no pole but `r` lies in `Σ` and the cuff disc of `r`. -/
theorem U_subset_of_one_pole {F : Drawing Shat} (hF : F.IsSubdrawing D.rad.G) {r : Shat} {Θ : Set
  S} (hreg : D.rad.regionOf r = cap.cuffDisc Θ)
    (hr : r ∈ cap.cuffDisc Θ) (hone : ∀ p ∈ D.rad.poles, p ∈ F.V → p = r) : F.U ⊆ range cap.emb ∪
      cap.cuffDisc Θ := by
  have : ConnectedSpace Shat := cap.connected
  intro x hx
  by_cases hxV : x ∈ F.V
  · by_cases hh : x ∈ D.P.Γ.hatV cap
    · obtain ⟨v, -, rfl⟩ := hh
      exact Or.inl (mem_range_self v)
    · have hw : x ∈ D.rad.Rstar := ⟨hF.1 hxV, hh⟩
      by_cases hp : x ∈ D.rad.poles
      · exact Or.inr (hone x hp hxV ▸ hr)
      · exact Or.inl (D.rad.region_subset_range hw hp (D.rad.regionOf_mem hw).2)
  · obtain ⟨f, hf, hxf⟩ := F.exists_edge_of_mem hx hxV
    obtain ⟨v, -, w, hw, hset⟩ := D.rad.edge_ends (hF.2 hf)
    have hwm : w ∈ closure f ∩ D.rad.G.V := by rw [hset]; exact Or.inr rfl
    have hwF : w ∈ F.V := mem_V_of_mem_U hF (F.closure_subset_U hf hwm.1) hwm.2
    by_cases hp : w ∈ D.rad.poles
    · have := D.rad.edge_subset_region (hF.2 hf) hw hset hxf
      rw [hone w hp hwF, hreg] at this
      exact Or.inr this
    · exact Or.inl (D.rad.edge_subset_range (hF.2 hf) hw hp hset hxf)

include hS h3 in
/-- **A cuff with its pole outside a least flaw circuit meets the inside of the circuit in at most
one point.** -/
theorem touch_subsingleton {n : ℕ} (hn : n < D.rep) {F : Drawing Shat} (hF : D.IsFreeCircuit n F)
    (hmin : ∀ C, D.IsFreeCircuit n C → F.E.ncard ≤ C.E.ncard ∧ (F.E.ncard = C.E.ncard
      → D.insCount C ≤ D.insCount F))
    {p : Shat} (hp : p ∈ D.rad.poles) (hpi : p ∉ D.ins F) {Θ : Set S} (hΘ : Θ ∈ cuffs S)
      (hreg : D.rad.regionOf p = cap.cuffDisc Θ)
    (hdis : Disjoint (cap.cuffDisc Θ) F.U) : (closure (cap.cuffDisc Θ) ∩ D.ins F).Subsingleton := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hle := hF.2.1
  have hlt : F.E.ncard < 2 * D.rep := by omega
  have hi := D.ins_spec hF.1 hlt
  have hfr : frontier (D.ins F) = F.U := by
    rw [IsClosedDisc.frontier_eq_discBd hT hi.2.2.1, hi.2.2.2.1]
  have hconn : IsPreconnected (cap.cuffDisc Θ) := hreg ▸ isPreconnected_connectedComponentIn
  have hpd := (D.rad.regionOf_mem hp.1).2
  rw [hreg] at hpd
  have hd : Disjoint (cap.cuffDisc Θ) (D.ins F) := by
    refine disjoint_left.2 fun x hx hxi ↦ ?_
    obtain ⟨z, hz, hzf⟩ := inter_frontier_of_preconnected hconn hi.2.2.1.isClosed ⟨x, hx, hxi⟩ ⟨p,
      hpd, hpi⟩
    rw [hfr] at hzf
    exact disjoint_left.1 hdis hz hzf
  have hEF : ∀ {x}, x ∈ closure (cap.cuffDisc Θ) ∩ D.ins F → x ∈ F.U := by
    rintro x ⟨hx, hxi⟩
    rw [← hfr, frontier_eq_closure_inter_closure]
    exact ⟨subset_closure hxi, closure_mono (fun y hy ↦ disjoint_left.1 hd hy) hx⟩
  have hEdis : Disjoint (closure (cap.cuffDisc Θ)) (discInt (D.ins F))
    := disjoint_left.2 fun x hx hxi ↦
    hxi.2 (hi.2.2.2.1 ▸ hEF ⟨hx, discInt_subset _ hxi⟩)
  have hemb : ∀ {x}, x ∈ closure (cap.cuffDisc Θ) ∩ D.ins F → ∃ v ∈ Θ, cap.emb v = x := by
    intro x hx
    have h₁ := hx.1
    rw [cap.closure_cuffDisc hΘ] at h₁
    rcases h₁ with h₁ | h₁
    · exact absurd (hEF hx) (disjoint_left.1 hdis h₁)
    · exact h₁
  have hpF : p ∉ F.V := fun h ↦ hpi (D.U_subset_ins hF.1 hlt (F.V_subset_U h))
  intro x hx y hy
  obtain ⟨v₁, h₁, rfl⟩ := hemb hx
  obtain ⟨v₂, h₂, rfl⟩ := hemb hy
  by_contra hne
  have hne' : v₁ ≠ v₂ := fun h ↦ hne (by rw [h])
  obtain ⟨hV₁, hF₁, -⟩ := D.rad.bd_point hF.1.1 (cuff_subset_bd ⟨Θ, hΘ⟩ h₁) (hEF hx)
  obtain ⟨hV₂, hF₂, -⟩ := D.rad.bd_point hF.1.1 (cuff_subset_bd ⟨Θ, hΘ⟩ h₂) (hEF hy)
  obtain ⟨e₁, he₁, hs₁⟩ := D.rad.exists_pole_edge hS h3 hp hΘ hreg hV₁ h₁
  obtain ⟨e₂, he₂, hs₂⟩ := D.rad.exists_pole_edge hS h3 hp hΘ hreg hV₂ h₂
  obtain ⟨A, B, Q, ht, hpQ, c₁, c₂, hQU⟩ := exists_theta_pole hF.1 hp hpF hV₁ hV₂ hne' hF₁ hF₂ he₁
    he₂ hs₁ hs₂
  have hcl : ∀ {e}, e ∈ D.rad.G.E → ∀ {x}, closure e ∩ D.rad.G.V = {x, p} → closure e ⊆ closure
    (cap.cuffDisc Θ) := fun he _ hs ↦
    closure_mono (hreg ▸ D.rad.edge_subset_region he hp.1 (by rw [hs]))
  have hQd : Disjoint Q.U (discInt (D.ins F)) :=
    Disjoint.mono_left (hQU.trans (union_subset (hcl he₁ hs₁) (hcl he₂ hs₂))) hEdis
  exact theta_contra hn hF hmin ht hQd c₁ c₂ (Or.inl ⟨p, hpQ, hpi⟩)

omit [T2Space S] in
/-- A point of a cuff disc inside a circuit that misses the cuff disc, with the pole outside, lies
on the circuit. -/
theorem cuff_inter_ins_of_disjoint (D : TangleDatum cap χ) {C : Drawing Shat}
  (hC : C.IsCircuitOf D.rad.G) (hlt : C.E.ncard < 2 * D.rep) {p : Shat}
    (hp : p ∈ D.rad.poles) (hpi : p ∉ D.ins C) {Θ : Set S} (hreg : D.rad.regionOf p
      = cap.cuffDisc Θ) (hdis : Disjoint (cap.cuffDisc Θ) C.U) {x : Shat}
    (hx : x ∈ closure (cap.cuffDisc Θ)) (hxi : x ∈ D.ins C) : x ∈ C.U := by
  have hT := cap.isClosedSurface
  have hi := D.ins_spec hC hlt
  have hfr : frontier (D.ins C) = C.U := by
    rw [IsClosedDisc.frontier_eq_discBd hT hi.2.2.1, hi.2.2.2.1]
  have hconn : IsPreconnected (cap.cuffDisc Θ) := hreg ▸ isPreconnected_connectedComponentIn
  have hpd := (D.rad.regionOf_mem hp.1).2
  rw [hreg] at hpd
  have hd : Disjoint (cap.cuffDisc Θ) (D.ins C) := by
    refine disjoint_left.2 fun y hy hyi ↦ ?_
    obtain ⟨z, hz, hzf⟩ := inter_frontier_of_preconnected hconn hi.2.2.1.isClosed ⟨y, hy, hyi⟩ ⟨p,
      hpd, hpi⟩
    rw [hfr] at hzf
    exact disjoint_left.1 hdis hz hzf
  rw [← hfr, frontier_eq_closure_inter_closure]
  exact ⟨subset_closure hxi, closure_mono (fun y hy ↦ disjoint_left.1 hd hy) hx⟩

end TangleDatum

end GraphMinor.GM19
