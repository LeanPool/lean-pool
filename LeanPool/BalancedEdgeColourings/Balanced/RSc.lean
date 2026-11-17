/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BalancedEdgeColourings.Balanced.RSb

/-!
# Equitable strong colourings (Rudašová–Soták, Theorem 3.1)

`exists_equitable`: if `G` has a strong (vertex-distinguishing) proper colouring with `k` colours,
it has an equitable one (Rudašová–Soták, Discrete Math. 308 (2008), Theorem 3.1).

Proof: take a strong colouring minimising `Σ_θ vcnt(θ)²`. If `vcnt a ≥ vcnt b + 4`, some component
`Q` of the graph of ends `H_{a,b}` has more ends with `a` than with `b` (the weights `±1` sum to
`vcnt a − vcnt b`); the excess is at most `2`, since the ends with a partner set are paired inside
`Q` and at most two ends of `Q` have none. Interchanging `a` and `b` on all `(a, b)`-paths of `Q`
keeps the colouring strong and lowers `vcnt a` by the excess `d ∈ {1, 2}`.
-/

@[expose] public section

namespace LeanPool.BalancedEdgeColourings

namespace Balanced

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset Overfull

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {k : ℕ}

theorem swapSet_eq_of_iff {a b : Fin k} {S : Finset (Fin k)} (h : a ∈ S ↔ b ∈ S) :
    swapSet a b S = S := by
  ext θ
  rw [mem_swapSet]
  by_cases h1 : θ = a
  · subst h1; rw [Equiv.swap_apply_left]; exact h.symm
  by_cases h2 : θ = b
  · subst h2; rw [Equiv.swap_apply_right]; exact h
  rw [Equiv.swap_apply_of_ne_of_ne h1 h2]

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
/-- **The improvement step.** -/
theorem improve {c : PEC G (Fin k)} (hc : Strong c) {a b : Fin k} (hab : a ≠ b)
    (hgap : vcnt c b + 4 ≤ vcnt c a) : ∃ c' : PEC G (Fin k), Strong c' ∧ cost2 c' < cost2 c := by
  classical
  obtain ⟨htot, hinj⟩ := hc
  set H := endGraph c a b with hH
  have onlyA_end : ∀ {v}, a ∈ colSet c v → b ∉ colSet c v → IsEnd c a b v :=
    fun h1 h2 => Or.inl ⟨h1, h2⟩
  have onlyB_end : ∀ {v}, b ∈ colSet c v → a ∉ colSet c v → IsEnd c a b v :=
    fun h1 h2 => Or.inr ⟨h1, h2⟩
  let w : V → ℤ := fun v => (if a ∈ colSet c v ∧ b ∉ colSet c v then 1 else 0) -
    (if b ∈ colSet c v ∧ a ∉ colSet c v then 1 else 0)
  have ea : vcnt c a = #(univ.filter fun v => a ∈ colSet c v ∧ b ∉ colSet c v) +
      #(univ.filter fun v => a ∈ colSet c v ∧ b ∈ colSet c v) := by
    unfold vcnt
    rw [← card_union_of_disjoint (disjoint_filter.2 fun v _ h1 h2 => h1.2 h2.2)]
    congr 1; ext v; simp only [mem_filter, mem_univ, true_and, mem_union]; tauto
  have eb : vcnt c b = #(univ.filter fun v => b ∈ colSet c v ∧ a ∉ colSet c v) +
      #(univ.filter fun v => a ∈ colSet c v ∧ b ∈ colSet c v) := by
    unfold vcnt
    rw [← card_union_of_disjoint (disjoint_filter.2 fun v _ h1 h2 => h1.2 h2.1)]
    congr 1; ext v; simp only [mem_filter, mem_univ, true_and, mem_union]; tauto
  have hsum : ∑ v, w v = (vcnt c a : ℤ) - vcnt c b := by
    simp only [w, sum_sub_distrib, sum_boole]
    rw [ea, eb]
    push_cast
    ring
  -- a component with an excess of ends with `a`
  obtain ⟨C, hC⟩ : ∃ C : H.ConnectedComponent,
      0 < ∑ v ∈ univ.filter (fun v => H.connectedComponentMk v = C), w v := by
    by_contra hn
    push Not at hn
    have := Finset.sum_nonpos fun C (_ : C ∈ univ.image H.connectedComponentMk) => hn C
    have h3 : ∑ v, w v ≤ 0 := by
      rw [← Finset.sum_fiberwise_of_maps_to (g := H.connectedComponentMk)
        (t := univ.image H.connectedComponentMk) (fun v _ => mem_image_of_mem _ (mem_univ v))]
      convert this using 3
    omega
  set QA := univ.filter fun v => H.connectedComponentMk v = C ∧ a ∈ colSet c v ∧
    b ∉ colSet c v with hQA
  set QB := univ.filter fun v => H.connectedComponentMk v = C ∧ b ∈ colSet c v ∧
    a ∉ colSet c v with hQB
  have hCsum : ∑ v ∈ univ.filter (fun v => H.connectedComponentMk v = C), w v =
      (#QA : ℤ) - #QB := by
    simp only [w, sum_sub_distrib, sum_boole, filter_filter]
    rw [hQA, hQB]
  have hpos : #QB < #QA := by omega
  -- the excess is at most two
  have hle : #QA ≤ #QB + 2 := by
    set Mat := QA.filter fun u => ∃ x, colSet c x = swapSet a b (colSet c u) with hMd
    set Unm := QA.filter fun u => ¬ ∃ x, colSet c x = swapSet a b (colSet c u) with hUd
    have hsplit : #Mat + #Unm = #QA := by
      rw [hMd, hUd]; exact card_filter_add_card_filter_not _
    let p : V → V := fun u =>
      if h : ∃ x, colSet c x = swapSet a b (colSet c u) then Classical.choose h else u
    have hp : ∀ u ∈ Mat, colSet c (p u) = swapSet a b (colSet c u) := by
      intro u hu
      have h := (mem_filter.1 hu).2
      simp only [p, dite_eq_left h]
      exact Classical.choose_spec h
    have hMat : #Mat ≤ #QB := by
      refine card_le_card_of_injOn p (fun u hu => ?_) (fun u hu u' hu' e => ?_)
      · have hu' := mem_filter.1 (mem_filter.1 hu).1
        obtain ⟨-, hC', ha, hb⟩ := hu'
        have e := hp u hu
        have eu : IsEnd c a b u := onlyA_end ha hb
        have ep : IsEnd c a b (p u) := eu.of_swap (p u) e
        have hne : u ≠ p u := fun h' => eu.swap_ne (by rw [← e, ← h'])
        have hadj : H.Adj u (p u) := ⟨hne, eu, ep, Or.inr e⟩
        rw [mem_coe, hQB, mem_filter]
        refine ⟨mem_univ _, by rw [← hC']; exact (ConnectedComponent.eq.2 hadj.reachable).symm,
          ?_, ?_⟩
        · rw [e, mem_swapSet, Equiv.swap_apply_right]; exact ha
        · rw [e, mem_swapSet, Equiv.swap_apply_left]; exact hb
      · have e1 := hp u hu
        have e2 := hp u' hu'
        rw [e] at e1
        have := congrArg (swapSet a b) (e1.symm.trans e2)
        rw [swapSet_swapSet, swapSet_swapSet] at this
        exact hinj this
    have hUnm : #Unm ≤ 2 := by
      by_contra hlt
      push Not at hlt
      obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ := two_lt_card.1 hlt
      simp only [hUd, hQA, mem_filter, mem_univ, true_and] at hx hy hz
      have dx := endGraph_degree_le_one hinj (a := a) (b := b) (u := x)
        (fun w' e => hx.2 ⟨w', e⟩)
      have dy := endGraph_degree_le_one hinj (a := a) (b := b) (u := y)
        (fun w' e => hy.2 ⟨w', e⟩)
      have dz := endGraph_degree_le_one hinj (a := a) (b := b) (u := z)
        (fun w' e => hz.2 ⟨w', e⟩)
      have rxy : H.Reachable x y := ConnectedComponent.exact (hx.1.1.trans hy.1.1.symm)
      have rxz : H.Reachable x z := ConnectedComponent.exact (hx.1.1.trans hz.1.1.symm)
      exact no_three_endpoints (endGraph_degree_le_two hinj) hxy hxz hyz dx dy dz rxy rxz
    omega
  -- the vertex set of the paths of `Q`
  set X := univ.filter fun v => ∃ q, (H.connectedComponentMk q = C ∧ IsEnd c a b q) ∧
    (c.kempeGraph a b).Reachable q v with hXdef
  have hX : KClosed c a b X := by
    intro u v hu hcol
    obtain ⟨q, hq, r⟩ := (mem_filter.1 hu).2
    exact mem_filter.2 ⟨mem_univ _, q, hq, reachable_of_col r hcol⟩
  have hXE : ∀ {v}, v ∈ X → IsEnd c a b v → H.connectedComponentMk v = C := by
    intro v hv ev
    obtain ⟨q, ⟨hqC, eq⟩, r⟩ := (mem_filter.1 hv).2
    by_cases hqv : q = v
    · rw [← hqv]; exact hqC
    · rw [← hqC]
      exact (ConnectedComponent.eq.2 (show H.Adj q v from ⟨hqv, eq, ev, Or.inl r⟩).reachable).symm
  have hQX : ∀ {v}, H.connectedComponentMk v = C → IsEnd c a b v → v ∈ X :=
    fun h1 h2 => mem_filter.2 ⟨mem_univ _, _, ⟨h1, h2⟩, Reachable.refl _⟩
  have hXnE : ∀ {v}, ¬ IsEnd c a b v → (a ∈ colSet c v ↔ b ∈ colSet c v) := by
    intro v hv
    unfold IsEnd at hv
    tauto
  set c' := swapOn c a b X hX with hc'
  -- strong
  have hstrong : Strong c' := by
    refine ⟨htot.swapOn hX, fun u v huv => ?_⟩
    have cross : ∀ {u v}, u ∈ X → v ∉ X →
        colSet c' u = colSet c' v → False := by
      intro u v hu hv h
      rw [colSet_swapOn_of_mem hX hu, colSet_swapOn_of_not_mem hX hv] at h
      by_cases eu : IsEnd c a b u
      · have ev : IsEnd c a b v := eu.of_swap v h.symm
        have hne : u ≠ v := fun e => hv (e ▸ hu)
        have hadj : H.Adj u v := ⟨hne, eu, ev, Or.inr h.symm⟩
        exact hv (hQX (by rw [← hXE hu eu]; exact (ConnectedComponent.eq.2 hadj.reachable).symm)
          ev)
      · rw [swapSet_eq_of_iff (hXnE eu)] at h
        exact hv (hinj h ▸ hu)
    by_cases hu : u ∈ X <;> by_cases hv : v ∈ X
    · rw [colSet_swapOn_of_mem hX hu, colSet_swapOn_of_mem hX hv] at huv
      have := congrArg (swapSet a b) huv
      rw [swapSet_swapSet, swapSet_swapSet] at this
      exact hinj this
    · exact (cross hu hv huv).elim
    · exact (cross hv hu huv.symm).elim
    · rw [colSet_swapOn_of_not_mem hX hu, colSet_swapOn_of_not_mem hX hv] at huv
      exact hinj huv
  -- counts
  have sa : #(univ.filter fun v => v ∈ X ∧ a ∈ colSet c v) =
      #(univ.filter fun v => v ∈ X ∧ ¬ IsEnd c a b v ∧ a ∈ colSet c v) + #QA := by
    rw [← card_union_of_disjoint]
    · congr 1
      ext v
      simp only [mem_filter, mem_univ, true_and, mem_union, hQA]
      by_cases ev : IsEnd c a b v
      · constructor
        · rintro ⟨hv, hθv⟩
          right
          refine ⟨hXE hv ev, hθv, ?_⟩
          unfold IsEnd at ev; tauto
        · rintro (⟨-, h, -⟩ | ⟨hC', h1, -⟩)
          · exact absurd ev h
          · exact ⟨hQX hC' ev, h1⟩
      · constructor
        · rintro ⟨hv, h⟩; left; exact ⟨hv, ev, h⟩
        · rintro (⟨hv, -, h⟩ | ⟨-, h1, h2⟩)
          · exact ⟨hv, h⟩
          · exact absurd (Or.inl ⟨h1, h2⟩) ev
    · refine disjoint_left.2 fun v h1 h2 => ?_
      rw [mem_filter] at h1
      rw [hQA, mem_filter] at h2
      exact h1.2.2.1 (Or.inl ⟨h2.2.2.1, h2.2.2.2⟩)
  have sb : #(univ.filter fun v => v ∈ X ∧ b ∈ colSet c v) =
      #(univ.filter fun v => v ∈ X ∧ ¬ IsEnd c a b v ∧ a ∈ colSet c v) + #QB := by
    rw [← card_union_of_disjoint]
    · congr 1
      ext v
      simp only [mem_filter, mem_univ, true_and, mem_union, hQB]
      by_cases ev : IsEnd c a b v
      · constructor
        · rintro ⟨hv, hθv⟩
          right
          refine ⟨hXE hv ev, hθv, ?_⟩
          unfold IsEnd at ev; tauto
        · rintro (⟨-, h, -⟩ | ⟨hC', h1, -⟩)
          · exact absurd ev h
          · exact ⟨hQX hC' ev, h1⟩
      · have hiff := hXnE ev
        constructor
        · rintro ⟨hv, h⟩; left; exact ⟨hv, ev, hiff.2 h⟩
        · rintro (⟨hv, -, h⟩ | ⟨-, h1, h2⟩)
          · exact ⟨hv, hiff.1 h⟩
          · exact absurd (Or.inr ⟨h1, h2⟩) ev
    · refine disjoint_left.2 fun v h1 h2 => ?_
      rw [mem_filter] at h1
      rw [hQB, mem_filter] at h2
      exact h1.2.2.1 (Or.inr ⟨h2.2.2.1, h2.2.2.2⟩)
  have va' := vcnt_swapOn hX a
  have vb' := vcnt_swapOn hX b
  rw [Equiv.swap_apply_left] at va'
  rw [Equiv.swap_apply_right] at vb'
  have va := vcnt_split c X a
  have vb := vcnt_split c X b
  rw [← hc'] at va' vb'
  refine ⟨c', hstrong, cost2_lt hab (d := #QA - #QB) (by omega) (by omega) (fun θ h1 h2 => ?_)
    (by omega) (by omega)⟩
  rw [hc', vcnt_swapOn hX θ, Equiv.swap_apply_of_ne_of_ne h1 h2, vcnt_split c X θ]

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- **Rudašová–Soták, Theorem 3.1.** If `G` has a strong colouring with `k` colours, it has an
equitable strong colouring with `k` colours. -/
theorem exists_equitable {c : PEC G (Fin k)} (hc : Strong c) :
    ∃ c' : PEC G (Fin k), Strong c' ∧ Equitable c' := by
  classical
  have hex : ∃ m, ∃ c : PEC G (Fin k), Strong c ∧ cost2 c = m := ⟨_, c, hc, rfl⟩
  obtain ⟨c₀, h₀, hm⟩ := Nat.find_spec hex
  refine ⟨c₀, h₀, fun x y => ?_⟩
  by_contra hxy
  push Not at hxy
  obtain ⟨r, hr⟩ := vcnt_even c₀ x
  obtain ⟨s, hs⟩ := vcnt_even c₀ y
  have hne : x ≠ y := by rintro rfl; omega
  obtain ⟨c', h', hlt⟩ := improve h₀ hne (by omega)
  exact Nat.find_min hex (hm ▸ hlt) ⟨c', h', rfl⟩
end Balanced

end LeanPool.BalancedEdgeColourings
