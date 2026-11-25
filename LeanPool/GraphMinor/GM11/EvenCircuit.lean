/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Corners
public import LeanPool.GraphMinor.GM11.DrawingTopology

/-!
# Even valency gives circuits

"every vertex of $N(Z_1)$ has even valency and so every edge of $N(Z_1)$ is in a circuit" (Graph
Minors
XI, proof of (5.4), page 83). This is `exists_circuit_of_even`. Suppose that deleting `e` leaves its
ends in different parts, and let `A` be the vertices reached from one end. Count the half-edges with
end in `A`. The count is even, as each vertex has even valency, and it is odd, as the half-edges
other than one half of `e` come in pairs.
-/

public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval

universe u

variable {S : Type u} [TopologicalSpace S] [T1Space S]

/-- The vertices and edges of a simple-closed walk form a circuit. -/
theorem isCircuit_walkDrawing (N : Drawing S) {u : S} {W : GraphWalk N.toGraph u u}
    (hW : W.IsSimpleClosed) (hpos : 0 < W.length) : (walkDrawing N W).IsCircuit := by
  obtain ⟨W', hs, he⟩ := (walkDrawing_isSubdrawing N W).exists_walk_down W
    (by rw [walkDrawing_V]; exact fun x hx => hx) (by rw [walkDrawing_E]; exact fun e he => he)
  refine ⟨u, W', ?_, ?_, ?_, ?_⟩
  · unfold GraphWalk.IsSimpleClosed
    rw [hs, he]
    exact hW
  · have : W'.edges.length = W.edges.length := by rw [he]
    exact lt_of_lt_of_eq hpos this.symm
  · rw [walkDrawing_V, hs]
  · rw [walkDrawing_E, he]

variable [T2Space S] {Γ N : Drawing S} {γ : Set S → I → S}

omit [T1Space S] in
/-- The vertices of an edge are the two ends of its parametrization. -/
theorem closure_inter_V_eq (hγ : EdgePar Γ γ) {e : Set S} (he : e ∈ Γ.E) :
    closure e ∩ Γ.V = {γ e (endOf false), γ e (endOf true)} := by
  ext x
  constructor
  · rintro ⟨hx, hxV⟩
    obtain ⟨b, rfl⟩ := exists_end_eq hγ he hxV hx
    cases b <;> simp
  · rintro (rfl | rfl)
    · exact ⟨end_mem_closure hγ he _, end_mem_V hγ he _⟩
    · exact ⟨end_mem_closure hγ he _, end_mem_V hγ he _⟩

omit [T1Space S] in
/-- An edge of a subdrawing links the two ends of its parametrization. -/
theorem isLink_ends (hγ : EdgePar Γ γ) (hN : N.IsSubdrawing Γ) {e : Set S} (he : e ∈ N.E)
  (b : Bool) :
    N.toGraph.IsLink e (γ e (endOf b)) (γ e (endOf (!b))) := by
  have hcap := closure_inter_V_eq hγ (hN.2 he)
  have hcap' : closure e ∩ N.V = {γ e (endOf false), γ e (endOf true)} := by
    rw [← hcap]
    exact hN.closure_inter_V he
  have hm : ∀ c, γ e (endOf c) ∈ N.V := fun c => by
    have : γ e (endOf c) ∈ closure e ∩ N.V := by
      rw [hcap']
      cases c <;> simp
    exact this.2
  refine ⟨he, hm _, hm _, ?_⟩
  rw [hcap']
  cases b
  · rfl
  · exact pair_comm _ _

/-- An edge whose ends are joined by a walk that avoids it lies on a circuit. -/
theorem exists_circuit_of_reach (hγ : EdgePar Γ γ) (hN : N.IsSubdrawing Γ) {e : Set S}
  (he : e ∈ N.E)
    (hreach : Nonempty (GraphWalk (N.deleteEdge e).toGraph (γ e (endOf false)) (γ e
      (endOf true)))) :
    ∃ C : Drawing S, C.IsCircuit ∧ C.IsSubdrawing N ∧ e ∈ C.E := by
  classical
  set a := γ e (endOf false) with ha
  set b := γ e (endOf true) with hb
  let D := N.deleteEdge e
  have hDN : D.IsSubdrawing N := deleteEdge_isSubdrawing N e
  have hDE : D.E = N.E \ {e} := deleteEdge_E N e
  have hlink := isLink_ends hγ hN he false
  obtain ⟨P₀⟩ := hreach
  obtain ⟨P₁, hP₁, -, hP₁e⟩ := GraphWalk.exists_isSimple P₀
  have hP₁e' : ∀ f ∈ P₁.edges, f ∈ D.E := fun f hf => by
    exact mem_E_of_mem_edges P₀ (hP₁e f hf)
  obtain ⟨P, hPs, hPe⟩ := hDN.exists_walk_up P₁
  have hPsimple : P.IsSimple := by
    unfold GraphWalk.IsSimple
    rw [hPs]
    exact hP₁
  let W : GraphWalk N.toGraph a a := .cons hlink P.reverse
  have heP : e ∉ P.reverse.edges := by
    intro h
    rw [GraphWalk.edges_reverse, List.mem_reverse, hPe] at h
    have := hP₁e' e h
    rw [hDE] at this
    exact this.2 rfl
  have hW : W.IsSimpleClosed := by
    refine ⟨?_, ?_⟩
    · exact hPsimple.reverse
    · exact List.nodup_cons.mpr ⟨heP, hPsimple.reverse.edges_nodup⟩
  have hlen : 0 < W.length := by
    change 0 < (e :: P.reverse.edges).length
    simp
  refine ⟨_, isCircuit_walkDrawing N hW hlen, walkDrawing_isSubdrawing N W, ?_⟩
  rw [walkDrawing_E]
  exact List.mem_cons_self

/-- Every edge of a subdrawing with even valencies lies on a circuit. -/
theorem exists_circuit_of_even (hγ : EdgePar Γ γ) (hN : N.IsSubdrawing Γ)
    (heven : ∀ v ∈ Γ.V, Even (nHalf N γ v).ncard) {e : Set S} (he : e ∈ N.E) :
    ∃ C : Drawing S, C.IsCircuit ∧ C.IsSubdrawing N ∧ e ∈ C.E := by
  classical
  set a := γ e (endOf false) with ha
  set b := γ e (endOf true) with hb
  let D := N.deleteEdge e
  have hDN : D.IsSubdrawing N := deleteEdge_isSubdrawing N e
  have hDE : D.E = N.E \ {e} := deleteEdge_E N e
  have hDV : D.V = N.V := deleteEdge_V N e
  have hlink := isLink_ends hγ hN he false
  by_cases hreach : Nonempty (GraphWalk D.toGraph a b)
  · exact exists_circuit_of_reach hγ hN he hreach
  · exfalso
    let A : Set S := {x | Nonempty (GraphWalk D.toGraph a x)}
    have haA : a ∈ A := by
      have : a ∈ D.V := by rw [hDV]; exact hlink.2.1
      exact ⟨.nil this⟩
    have hbA : b ∉ A := hreach
    have hAV : A ⊆ Γ.V := by
      rintro x ⟨W⟩
      exact hN.1 (hDN.1 (W.mem_vertexSet_of_mem_support W.end_mem_support))
    have hAfin : A.Finite := Γ.finite_V.subset hAV
    let X : Set (Set S × Bool) := {k | k.1 ∈ N.E ∧ γ k.1 (endOf k.2) ∈ A}
    have hXfin : X.Finite :=
      (N.finite_edges.prod (finite_univ (α := Bool))).subset fun k hk => ⟨hk.1, mem_univ _⟩
    let T := hXfin.toFinset
    have hTmem : ∀ k, k ∈ T ↔ k ∈ X := fun k => hXfin.mem_toFinset
    let f : Set S × Bool → S := fun k => γ k.1 (endOf k.2)
    have hsum := Finset.card_eq_sum_card_fiberwise (f := f) (s := T) (t := hAfin.toFinset)
      (fun k hk => hAfin.mem_toFinset.mpr ((hTmem k).mp hk).2)
    have heT : Even T.card := by
      rw [hsum]
      refine Finset.even_sum _ fun x hx => ?_
      have hxA : x ∈ A := hAfin.mem_toFinset.mp hx
      have : (T.filter fun k => f k = x).card = (nHalf N γ x).ncard := by
        rw [← Set.ncard_coe_finset]
        congr 1
        ext k
        simp only [Finset.coe_filter, mem_ofPred_eq, hTmem]
        change _ ↔ (k.1 ∈ N.E ∧ γ k.1 (endOf k.2) = x)
        constructor
        · rintro ⟨h₁, h₂⟩
          exact ⟨h₁.1, h₂⟩
        · rintro ⟨h₁, h₂⟩
          exact ⟨⟨h₁, h₂ ▸ hxA⟩, h₂⟩
      rw [this]
      exact heven x (hAV hxA)
    have hmem₀ : (e, false) ∈ T := (hTmem _).mpr ⟨he, haA⟩
    have hne : ∀ k ∈ T.erase (e, false), k.1 ≠ e := by
      rintro ⟨g, c⟩ hk rfl
      obtain ⟨h₁, h₂⟩ := Finset.mem_erase.mp hk
      cases c
      · exact h₁ rfl
      · exact hbA ((hTmem _).mp h₂).2
    have hflip : ∀ k ∈ T.erase (e, false), (k.1, !k.2) ∈ T.erase (e, false) := by
      rintro ⟨g, c⟩ hk
      have hg := hne _ hk
      obtain ⟨h₁, h₂⟩ := (hTmem _).mp (Finset.mem_erase.mp hk).2
      dsimp only at hg h₁ h₂ ⊢
      refine Finset.mem_erase.mpr ⟨fun h => hg (congrArg Prod.fst h), (hTmem _).mpr ⟨h₁, ?_⟩⟩
      obtain ⟨W⟩ := h₂
      have hgD : g ∈ D.E := by
        rw [hDE]
        exact ⟨h₁, hg⟩
      have hl : D.toGraph.IsLink g (γ g (endOf c)) (γ g (endOf (!c))) :=
        isLink_ends hγ (hDN.trans hN) hgD c
      exact ⟨W.append (.cons hl (.nil hl.symm.left_mem))⟩
    have hz : ∑ _k ∈ T.erase (e, false), (1 : ZMod 2) = 0 := by
      refine Finset.sum_involution (fun k _ => (k.1, !k.2)) (fun _ _ => rfl) ?_ hflip ?_
      · rintro ⟨g, c⟩ - - h
        have := congrArg Prod.snd h
        simp at this
      · rintro ⟨g, c⟩ -
        simp
    rw [Finset.sum_const, nsmul_one, ZMod.natCast_eq_zero_iff_even] at hz
    have hc := Finset.card_erase_add_one hmem₀
    rw [← hc] at heT
    exact (Nat.not_even_iff_odd.mpr hz.add_one) heT

end GraphMinor.GM11
