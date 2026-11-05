/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BalancedEdgeColourings.Overfull.Multifan

/-!
# Vizing's Adjacency Lemma (CCJS Lemma 2.1)

**VAL** (Vizing 1965). Let `G` be of class two and `xy` an edge such that `G − xy` has a
`Δ(G)`-edge-colouring. Then `x` has at least `Δ − d(y) + 1` neighbours of degree `Δ` other
than `y` (`val`).

Proof: take a multifan at `x` of maximal length. By maximality every colour missing at a fan
vertex colours an edge from `x` to another fan vertex, so the colours missing at fan vertices
are at most the number of fan vertices other than `y`; the fan is elementary (the multifan
lemma), `y` misses `Δ − d(y) + 1` colours and every other fan vertex of degree below `Δ` misses
at least one.
-/

@[expose] public section

namespace LeanPool.BalancedEdgeColourings

namespace Overfull

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The neighbours of `v` joined to `v` by a coloured edge. -/
noncomputable def colNbrs {k : ℕ} (c : PEC G (Fin k)) (v : V) : Finset V :=
  by classical exact (G.neighborFinset v).filter fun u => c.col v u ≠ none

omit [DecidableEq V] in
/-- Missing colours plus coloured edges at `v` make up all `k` colours. -/
theorem card_missing_add_colNbrs {k : ℕ} (c : PEC G (Fin k)) (v : V) :
    #(missing c v) + #(colNbrs c v) = k := by
  classical
  have hpres : #(univ.filter fun γ : Fin k => ¬ c.IsFree v γ) = #(colNbrs c v) := by
    symm
    refine card_bij (fun u hu => (c.col v u).get (Option.isSome_iff_ne_none.2
      (by simp only [colNbrs, mem_filter] at hu; exact hu.2))) (fun u hu => ?_) ?_ ?_
    · simp only [mem_filter, mem_univ, true_and, IsFree, not_forall, not_not]
      exact ⟨u, by simp⟩
    · intro u hu u' hu' h
      have h1 := Option.some_get (Option.isSome_iff_ne_none.2
        (by simp only [colNbrs, mem_filter] at hu; exact hu.2))
      have h2 := Option.some_get (Option.isSome_iff_ne_none.2
        (by simp only [colNbrs, mem_filter] at hu'; exact hu'.2))
      rw [h] at h1
      exact c.col_proper h1.symm h2.symm
    · intro γ hγ
      simp only [mem_filter, mem_univ, true_and, IsFree, not_forall, not_not] at hγ
      obtain ⟨u, hu⟩ := hγ
      refine ⟨u, ?_, by simp [hu]⟩
      simp only [colNbrs, mem_filter, mem_neighborFinset]
      exact ⟨c.col_adj hu, by rw [hu]; exact Option.some_ne_none _⟩
  rw [← hpres, missing, card_filter_add_card_filter_not, card_univ, Fintype.card_fin]

/-- Coloured edges at a vertex for a colouring of `G − ab`. -/
theorem IsColMinus.card_colNbrs {k : ℕ} {c : PEC G (Fin k)} {a b : V} (hcm : IsColMinus c a b)
    (v : V) : #(colNbrs c v) + (if v = a ∨ v = b then 1 else 0) = G.degree v := by
  classical
  rw [← card_neighborFinset_eq_degree]
  split_ifs with hv
  · have hother : ∃ w, G.Adj v w ∧ c.col v w = none ∧
        colNbrs c v = (G.neighborFinset v).erase w := by
      rcases hv with rfl | rfl
      · refine ⟨b, hcm.adj, hcm.uncol, ?_⟩
        ext u
        simp only [colNbrs, mem_filter, mem_erase, mem_neighborFinset]
        constructor
        · rintro ⟨hu, hcol⟩
          exact ⟨fun h => hcol (h ▸ hcm.uncol), hu⟩
        · rintro ⟨hne, hu⟩
          exact ⟨hu, hcm.total _ _ hu (fun h => hne (by
            rcases Sym2.eq_iff.1 h with ⟨-, h⟩ | ⟨h1, -⟩
            · exact h
            · exact absurd h1 hcm.adj.ne))⟩
      · refine ⟨a, hcm.adj.symm, by rw [c.col_symm]; exact hcm.uncol, ?_⟩
        ext u
        simp only [colNbrs, mem_filter, mem_erase, mem_neighborFinset]
        constructor
        · rintro ⟨hu, hcol⟩
          exact ⟨fun h => hcol (by rw [h, c.col_symm]; exact hcm.uncol), hu⟩
        · rintro ⟨hne, hu⟩
          exact ⟨hu, hcm.total _ _ hu (fun h => hne (by
            rcases Sym2.eq_iff.1 h with ⟨h1, -⟩ | ⟨-, h⟩
            · exact absurd h1.symm hcm.adj.ne
            · exact h))⟩
    obtain ⟨w, hw, -, heq⟩ := hother
    rw [heq, card_erase_of_mem ((mem_neighborFinset _ _ _).2 hw)]
    have : 0 < #(G.neighborFinset v) := card_pos.2 ⟨w, (mem_neighborFinset _ _ _).2 hw⟩
    omega
  · push Not at hv
    rw [add_zero]
    congr 1
    ext u
    simp only [colNbrs, mem_filter, mem_neighborFinset, and_iff_left_iff_imp]
    intro hu
    refine hcm.total _ _ hu fun h => ?_
    rcases Sym2.eq_iff.1 h with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hv.1 h1
    · exact hv.2 h1


/-! ### Maximal multifans -/

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem IsMultifan.length_le {k : ℕ} {c : PEC G (Fin k)} {x : V} {L : ℕ} {y : ℕ → V}
    (hF : IsMultifan c x L y) : L ≤ Fintype.card V := by
  classical
  have := card_le_card_of_injOn (s := range L) (t := (univ : Finset V)) y
    (fun i _ => mem_univ _) (fun i hi j hj h => hF.inj i (by simpa using hi) j (by simpa using
        hj) h)
  simpa using this

omit [DecidableEq V] [DecidableRel G.Adj] [Fintype V] in
/-- A multifan at `x` starting with `y₀` that cannot be extended: every neighbour of `x` outside
the fan has an edge colour missing at no fan vertex. -/
theorem exists_maximal_multifan [Finite V] {k : ℕ} (c : PEC G (Fin k)) {x y₀ : V} (hadj :
    G.Adj x y₀)
    (huncol : c.col x y₀ = none) :
    ∃ L y, IsMultifan c x L y ∧ y 0 = y₀ ∧
      ∀ z, G.Adj x z → (∀ i < L, y i ≠ z) → ∀ γ, c.col x z = some γ → ∀ j < L,
        ¬ c.IsFree (y j) γ := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let P : ℕ → Prop := fun L => ∃ y : ℕ → V, IsMultifan c x L y ∧ y 0 = y₀
  have hP1 : P 1 := ⟨fun _ => y₀, ⟨Nat.one_pos, huncol, fun i _ => hadj,
    fun i hi j hj _ => by omega, fun i hi hi' => by omega⟩, rfl⟩
  set N := Fintype.card V
  have hN : 1 ≤ N := Fintype.card_pos_iff.2 ⟨x⟩
  have hspec : P (Nat.findGreatest P N) := Nat.findGreatest_spec hN hP1
  obtain ⟨y, hF, hy0⟩ := hspec
  refine ⟨_, y, hF, hy0, fun z hz hzF γ hγ j hj hfree => ?_⟩
  set L := Nat.findGreatest P N
  -- extend the fan by `z`
  let y' : ℕ → V := fun i => if i = L then z else y i
  have hF' : IsMultifan c x (L + 1) y' := by
    refine ⟨Nat.succ_pos L, ?_, fun i hi => ?_, fun i hi i' hi' h => ?_, fun i hi0 hi => ?_⟩
    · simp only [y', show (0 : ℕ) ≠ L by have := hF.pos; omega, ite_false]
      exact hF.uncol
    · by_cases h : i = L
      · simp only [y', h, ite_true]; exact hz
      · simp only [y', h, ite_false]; exact hF.adj i (by omega)
    · by_cases h1 : i = L <;> by_cases h2 : i' = L <;> simp only [y', h1, h2, ite_true,
        ite_false] at h
      · omega
      · exact absurd h.symm (hzF i' (by omega))
      · exact absurd h (hzF i (by omega))
      · exact hF.inj i (by omega) i' (by omega) h
    · by_cases h : i = L
      · refine ⟨j, by omega, γ, by simp only [y', h, ite_true]; exact hγ, ?_⟩
        simp only [y', show j ≠ L by omega, ite_false]
        exact hfree
      · obtain ⟨j', hj', δ, hδ, hδf⟩ := hF.step i hi0 (by omega)
        refine ⟨j', hj', δ, by simp only [y', h, ite_false]; exact hδ, ?_⟩
        simp only [y', show j' ≠ L by omega, ite_false]
        exact hδf
  have hle : L + 1 ≤ N := hF'.length_le
  have := Nat.findGreatest_is_greatest (Nat.lt_succ_self L) hle
  exact this ⟨y', hF', by simp [y', show (0 : ℕ) ≠ L by have := hF.pos; omega, hy0]⟩

/-- **Vizing's Adjacency Lemma** (CCJS Lemma 2.1). If `G` is of class two and `G − xy` has a
`Δ(G)`-edge-colouring, then `x` has at least `Δ − d(y) + 1` neighbours of degree `Δ` other than
`y`. -/
theorem val (hG : IsClassTwo G) {c : PEC G (Fin G.maxDegree)} {x y₀ : V}
    (hcm : IsColMinus c x y₀) :
    G.maxDegree + 1 ≤ G.degree y₀ +
      #((G.neighborFinset x).filter fun z => z ≠ y₀ ∧ G.degree z = G.maxDegree) := by
  classical
  obtain ⟨L, y, hF, hy0, hmax⟩ := exists_maximal_multifan c hcm.adj hcm.uncol
  subst hy0
  obtain ⟨hA, hA', -⟩ := multifan_elementary hG L c x y hcm hF
  -- each colour missing at a fan vertex colours an edge from `x` to a later fan vertex
  have hidx : ∀ p ∈ (range L).sigma fun j => missing c (y j),
      ∃ i ∈ (range L).erase 0, c.col x (y i) = some p.2 := by
    rintro ⟨j, γ⟩ hp
    simp only [mem_sigma, mem_range, mem_missing] at hp
    have hpres : ¬ c.IsFree x γ := fun h => hA j hp.1 γ h hp.2
    simp only [IsFree, not_forall, not_not] at hpres
    obtain ⟨z, hz⟩ := hpres
    by_cases hzF : ∀ i < L, y i ≠ z
    · exact absurd hp.2 (hmax z (c.col_adj hz) hzF γ hz j hp.1)
    · push Not at hzF
      obtain ⟨i, hi, rfl⟩ := hzF
      refine ⟨i, mem_erase.2 ⟨fun h0 => ?_, mem_range.2 hi⟩, hz⟩
      subst h0
      rw [hF.uncol] at hz
      simp at hz
  choose! idx hidxmem hidxcol using hidx
  have hinj : Set.InjOn idx ((range L).sigma fun j => missing c (y j) : Set _) := by
    rintro ⟨j, γ⟩ hp ⟨j', γ'⟩ hp' h
    simp only [coe_sigma, Set.mem_sigma_iff, mem_coe, mem_range, mem_missing] at hp hp'
    have hc1 := hidxcol ⟨j, γ⟩ (mem_sigma.2 ⟨mem_range.2 hp.1, mem_missing.2 hp.2⟩)
    have hc2 := hidxcol ⟨j', γ'⟩ (mem_sigma.2 ⟨mem_range.2 hp'.1, mem_missing.2 hp'.2⟩)
    simp only at h hc1 hc2
    rw [h, hc2] at hc1
    have hγ : γ' = γ := Option.some_injective _ hc1
    subst hγ
    by_cases hjj : j = j'
    · subst hjj; rfl
    · exact absurd hp'.2 (hA' j hp.1 j' hp'.1 hjj γ' hp.2)
  have hsum := card_le_card_of_injOn idx (fun p hp => hidxmem p hp) hinj
  rw [card_sigma, card_erase_of_mem (mem_range.2 hF.pos), card_range] at hsum
  -- missing colours at the fan vertices
  have hmiss : ∀ j < L, #(missing c (y j)) + G.degree (y j) =
      G.maxDegree + (if j = 0 then 1 else 0) := by
    intro j hj
    have h1 := card_missing_add_colNbrs c (y j)
    have h2 := hcm.card_colNbrs (y j)
    have hx : y j ≠ x := (hF.adj j hj).ne.symm
    by_cases hj0 : j = 0
    · subst hj0
      simp only [ite_true, or_true] at h2 ⊢
      omega
    · have hy : y j ≠ y 0 := fun h => hj0 (hF.inj j hj 0 hF.pos h)
      simp only [hj0, hx, hy, ite_false, or_self] at h2 ⊢
      omega
  have hdeg : ∀ j, G.degree (y j) ≤ G.maxDegree := fun j => G.degree_le_maxDegree _
  -- the fan vertices of degree `Δ` other than `y₀`
  set E := (range L).erase 0
  set D := E.filter fun j => G.degree (y j) = G.maxDegree
  have hlow : #E - #D ≤ ∑ j ∈ E, #(missing c (y j)) := by
    have hge : ∀ j ∈ E, (if G.degree (y j) ≠ G.maxDegree then 1 else 0) ≤
        #(missing c (y j)) := by
      intro j hj
      simp only [E, mem_erase, mem_range] at hj
      have := hmiss j hj.2
      simp only [hj.1, ite_false, add_zero] at this
      have := hdeg j
      split_ifs <;> omega
    have hs := sum_le_sum hge
    rw [sum_boole] at hs
    simp only [ne_eq] at hs
    have := card_filter_add_card_filter_not (s := E) (fun j => G.degree (y j) = G.maxDegree)
    simp only [D] at this ⊢
    push_cast at hs
    omega
  have hsplit : ∑ j ∈ range L, #(missing c (y j)) =
      #(missing c (y 0)) + ∑ j ∈ E, #(missing c (y j)) :=
    (add_sum_erase _ _ (mem_range.2 hF.pos)).symm
  have h0 := hmiss 0 hF.pos
  simp only [ite_true] at h0
  have hD : #D ≤ #((G.neighborFinset x).filter fun z => z ≠ y 0 ∧ G.degree z = G.maxDegree) := by
    refine card_le_card_of_injOn y (fun j hj => ?_) (fun i hi j hj h => ?_)
    · simp only [D, E, mem_erase, mem_range, coe_filter, Set.mem_ofPred_eq] at hj
      simp only [mem_neighborFinset, coe_filter, Set.mem_ofPred_eq]
      exact ⟨hF.adj j hj.1.2, fun h => hj.1.1 (hF.inj j hj.1.2 0 hF.pos h), hj.2⟩
    · simp only [D, E, coe_filter, mem_erase, mem_range, Set.mem_ofPred_eq] at hi hj
      exact hF.inj i hi.1.2 j hj.1.2 h
  have hEcard : #E = L - 1 := by
    rw [card_erase_of_mem (mem_range.2 hF.pos), card_range]
  have hDE : #D ≤ #E := card_filter_le _ _
  omega

end Overfull

end LeanPool.BalancedEdgeColourings
