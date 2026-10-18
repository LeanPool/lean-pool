/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Tutte
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Tauto
public import LeanPool.ClassicalMatchingFactors.Factors.Defs

/-!

Imported from [jtraverso/tutte-f-factor](https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorNec.lean), registered as PALOMAR-2026-10-18-000005. The original proof is retained; module paths and imports are adapted for this collection.

# Necessity in Tutte's f-factor theorem

* `FFactor.oddCnt_le_of_factor`: if `H ≤ G` is an f-factor, then for all disjoint `S, T`,
  `q(S, T) ≤ ∑_S f − ∑_T f + ∑_T deg_{G − S}`.
-/

@[expose] public section

open Finset SimpleGraph

namespace FFactor

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
/-- Handshake lemma inside a finset. -/
theorem even_sum_card_adj (H : SimpleGraph V) [DecidableRel H.Adj] (s : Finset V) :
    Even (∑ w ∈ s, #{u ∈ s | H.Adj w u}) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha]
    have h1 : #{u ∈ insert a s | H.Adj a u} = #{u ∈ s | H.Adj a u} := by
      rw [filter_insert, ite_eq_right (H.loopless.irrefl a)]
    have h2 : ∀ w ∈ s, #{u ∈ insert a s | H.Adj w u} =
        #{u ∈ s | H.Adj w u} + if H.Adj w a then 1 else 0 := by
      intro w hw
      rw [filter_insert]
      split_ifs with h
      · rw [card_insert_of_notMem (by simp [ha])]
      · simp
    rw [sum_congr rfl h2, sum_add_distrib, ← card_filter]
    have h3 : #{w ∈ s | H.Adj w a} = #{u ∈ s | H.Adj a u} := by
      congr 1; ext; simp [H.adj_comm]
    rw [h1, h3]
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + #{u ∈ s | H.Adj a u}, by omega⟩

omit [Fintype V] in
/-- Membership in the complement of `S ∪ T`. -/
theorem mem_compl_union_iff {S T : Finset V} {u : V} :
    u ∈ ((S ∪ T : Finset V) : Set V)ᶜ ↔ u ∉ S ∧ u ∉ T := by
  simp

open Classical in
/-- Every component counted by `q(S, T)` has a witness vertex: an `H`-edge to `S` or a
`G`-edge to `T` which is not in `H`. -/
theorem exists_witness (G H : SimpleGraph V) (hHG : H ≤ G) (f : V → ℕ)
    (hdeg : ∀ v, #{u | H.Adj v u} = f v) (S T : Finset V)
    (c : (G.induce ((S ∪ T : Finset V) : Set V)ᶜ).ConnectedComponent)
    (hc : Odd (∑ w ∈ univ.filter (fun w : ↥(((S ∪ T : Finset V) : Set V)ᶜ) =>
        (G.induce ((S ∪ T : Finset V) : Set V)ᶜ).connectedComponentMk w = c),
      (f w + #{t ∈ T | G.Adj w t}))) :
    ∃ w : ↥(((S ∪ T : Finset V) : Set V)ᶜ),
      (G.induce ((S ∪ T : Finset V) : Set V)ᶜ).connectedComponentMk w = c ∧
      ((∃ z ∈ S, H.Adj w z) ∨ (∃ t ∈ T, G.Adj w t ∧ ¬H.Adj w t)) := by
  by_contra hne
  push Not at hne
  let Cset : Finset V := (univ.filter (fun w : ↥(((S ∪ T : Finset V) : Set V)ᶜ) =>
      (G.induce ((S ∪ T : Finset V) : Set V)ᶜ).connectedComponentMk w = c)).map
      (Function.Embedding.subtype _)
  have hmem : ∀ u (hu : u ∈ ((S ∪ T : Finset V) : Set V)ᶜ),
      u ∈ Cset ↔ (G.induce ((S ∪ T : Finset V) : Set V)ᶜ).connectedComponentMk ⟨u, hu⟩ = c := by
    intro u hu
    simp only [Cset, mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coe_subtype]
    constructor
    · rintro ⟨w, hw, rfl⟩; exact hw
    · intro h; exact ⟨⟨u, hu⟩, h, rfl⟩
  have hmem' : ∀ u ∈ Cset, ∃ hu : u ∈ ((S ∪ T : Finset V) : Set V)ᶜ,
      (G.induce ((S ∪ T : Finset V) : Set V)ᶜ).connectedComponentMk ⟨u, hu⟩ = c := by
    intro u hu
    simp only [Cset, mem_map, mem_filter, mem_univ, true_and,
      Function.Embedding.coe_subtype] at hu
    obtain ⟨w, hw, rfl⟩ := hu
    exact ⟨w.2, hw⟩
  have hCsum : ∑ w ∈ Cset, (f w + #{t ∈ T | G.Adj w t}) =
      ∑ w ∈ univ.filter (fun w : ↥(((S ∪ T : Finset V) : Set V)ᶜ) =>
        (G.induce ((S ∪ T : Finset V) : Set V)ᶜ).connectedComponentMk w = c),
      (f w + #{t ∈ T | G.Adj w t}) := sum_map _ _ _
  rw [← hCsum] at hc
  have hsplit : ∀ w ∈ Cset, f w + #{t ∈ T | G.Adj w t} =
      #{u ∈ Cset | H.Adj w u} + 2 * #{t ∈ T | G.Adj w t} := by
    intro w hw
    obtain ⟨hwc, hwcc⟩ := hmem' w hw
    have hne' := hne ⟨w, hwc⟩ hwcc
    rw [← hdeg w]
    have heq : ({u | H.Adj w u} : Finset V) =
        {t ∈ T | G.Adj w t} ∪ {u ∈ Cset | H.Adj w u} := by
      ext u
      simp only [mem_filter, mem_univ, true_and, mem_union]
      constructor
      · intro hu
        by_cases huT : u ∈ T
        · exact Or.inl ⟨huT, hHG hu⟩
        · have huS : u ∉ S := fun h => hne'.1 u h hu
          have hu' : u ∈ ((S ∪ T : Finset V) : Set V)ᶜ := mem_compl_union_iff.mpr ⟨huS, huT⟩
          refine Or.inr ⟨(hmem u hu').mpr ?_, hu⟩
          rw [← hwcc]
          exact (ConnectedComponent.connectedComponentMk_eq_of_adj
            (by simpa using hHG hu)).symm
      · rintro (⟨huT, hu⟩ | ⟨_, hu⟩)
        · exact hne'.2 u huT hu
        · exact hu
    rw [heq, card_union_of_disjoint]
    · ring
    · rw [Finset.disjoint_left]
      intro u hu hu'
      obtain ⟨hu'', _⟩ := hmem' u (mem_filter.mp hu').1
      exact (mem_compl_union_iff.mp hu'').2 (mem_filter.mp hu).1
  rw [sum_congr rfl hsplit, sum_add_distrib, ← mul_sum] at hc
  exact (Nat.not_even_iff_odd.mpr hc) ((even_sum_card_adj H Cset).add (even_two_mul _))

open Classical in
/-- `q(S, T)` is at most the number of witnesses. -/
theorem oddCnt_le_card_witness (G H : SimpleGraph V) (hHG : H ≤ G) (f : V → ℕ)
    (hdeg : ∀ v, #{u | H.Adj v u} = f v) (S T : Finset V) :
    oddCount G f S T ≤ #{p ∈ (univ \ (S ∪ T)) ×ˢ (univ : Finset V) |
      (p.2 ∈ S ∧ H.Adj p.1 p.2) ∨ (p.2 ∈ T ∧ G.Adj p.1 p.2 ∧ ¬H.Adj p.1 p.2)} := by
  set G' := G.induce ((S ∪ T : Finset V) : Set V)ᶜ
  set Z := ({p ∈ (univ \ (S ∪ T)) ×ˢ (univ : Finset V) |
      (p.2 ∈ S ∧ H.Adj p.1 p.2) ∨ (p.2 ∈ T ∧ G.Adj p.1 p.2 ∧ ¬H.Adj p.1 p.2)} : Finset (V × V))
  have hex : ∀ c : {c : G'.ConnectedComponent // Odd (∑ w ∈ univ.filter
      (fun w : ↥(((S ∪ T : Finset V) : Set V)ᶜ) => G'.connectedComponentMk w = c),
        (f w + #{t ∈ T | G.Adj w t}))},
      ∃ p ∈ Z, ∃ h : p.1 ∈ ((S ∪ T : Finset V) : Set V)ᶜ,
        G'.connectedComponentMk ⟨p.1, h⟩ = c.1 := by
    intro c
    obtain ⟨w, hw, hwit⟩ := exists_witness G H hHG f hdeg S T c.1 c.2
    have hw2 := mem_compl_union_iff.mp w.2
    rcases hwit with ⟨z, hz, hHz⟩ | ⟨t, ht, hGt, hHt⟩
    · refine ⟨(w.1, z), ?_, w.2, hw⟩
      simp only [Z, mem_filter, mem_product, mem_sdiff, mem_univ, mem_union, true_and]
      exact ⟨by tauto, Or.inl ⟨hz, hHz⟩⟩
    · refine ⟨(w.1, t), ?_, w.2, hw⟩
      simp only [Z, mem_filter, mem_product, mem_sdiff, mem_univ, mem_union, true_and]
      exact ⟨by tauto, Or.inr ⟨ht, hGt, hHt⟩⟩
  let g : {c : G'.ConnectedComponent // Odd (∑ w ∈ univ.filter
      (fun w : ↥(((S ∪ T : Finset V) : Set V)ᶜ) => G'.connectedComponentMk w = c),
        (f w + #{t ∈ T | G.Adj w t}))} → Z :=
    fun c => ⟨Classical.choose (hex c), (Classical.choose_spec (hex c)).1⟩
  have hg : Function.Injective g := by
    intro c d hcd
    have hc := (Classical.choose_spec (hex c)).2
    have hd := (Classical.choose_spec (hex d)).2
    have e : Classical.choose (hex c) = Classical.choose (hex d) := congrArg Subtype.val hcd
    obtain ⟨h1, h1'⟩ := hc
    obtain ⟨h2, h2'⟩ := hd
    apply Subtype.ext
    rw [← h1', ← h2']
    congr 2
    rw [e]
  have := Nat.card_le_card_of_injective g hg
  simpa [Nat.card_eq_fintype_card, oddCount] using this

/-- Splitting a sum over `V` along the disjoint sets `S`, `T` and `V \ (S ∪ T)`. -/
theorem sum_split3 {S T : Finset V} (hST : Disjoint S T) (F : V → ℤ) :
    ∑ u, F u = ∑ u ∈ S, F u + ∑ u ∈ T, F u + ∑ u ∈ univ \ (S ∪ T), F u := by
  rw [← sum_union hST, ← sum_union disjoint_sdiff, union_sdiff_of_subset (subset_univ _)]

open Classical in
/-- The number of witnesses is bounded by the right-hand side of the f-factor condition. -/
theorem card_witness_le (G H : SimpleGraph V) (hHG : H ≤ G) (f : V → ℕ)
    (hdeg : ∀ v, #{u | H.Adj v u} = f v) (S T : Finset V) (hST : Disjoint S T) :
    (#{p ∈ (univ \ (S ∪ T)) ×ˢ (univ : Finset V) |
      (p.2 ∈ S ∧ H.Adj p.1 p.2) ∨ (p.2 ∈ T ∧ G.Adj p.1 p.2 ∧ ¬H.Adj p.1 p.2)} : ℤ) ≤
      ∑ v ∈ S, (f v : ℤ) - ∑ v ∈ T, (f v : ℤ) + ∑ v ∈ T, (#{u | G.Adj v u ∧ u ∉ S} : ℤ) := by
  set R := univ \ (S ∪ T) with hR
  let A : V → V → ℤ := fun x y => if H.Adj x y then 1 else 0
  let B : V → V → ℤ := fun x y => if G.Adj x y then 1 else 0
  have hAsymm : ∀ x y, A x y = A y x := fun x y => by simp only [A, H.adj_comm]
  have hBsymm : ∀ x y, B x y = B y x := fun x y => by simp only [B, G.adj_comm]
  have hA0 : ∀ x y, 0 ≤ A x y := fun x y => by simp only [A]; split_ifs <;> norm_num
  have hAB : ∀ x y, A x y ≤ B x y := fun x y => by
    by_cases h1 : H.Adj x y
    · simp [A, B, h1, hHG h1]
    · by_cases h2 : G.Adj x y <;> simp [A, B, h1, h2]
  have hmemR : ∀ u, u ∈ R ↔ u ∉ S ∧ u ∉ T := fun u => by simp [hR]
  have hf : ∀ v, (f v : ℤ) = ∑ u, A v u := fun v => by
    rw [← hdeg v, card_filter]; push_cast; rfl
  have hN : ∀ t, (#{u | G.Adj t u ∧ u ∉ S} : ℤ) = ∑ u ∈ T, B t u + ∑ u ∈ R, B t u := by
    intro t
    rw [card_filter]; push_cast
    rw [sum_split3 hST]
    have h1 : ∑ u ∈ S, (if G.Adj t u ∧ u ∉ S then (1 : ℤ) else 0) = 0 :=
      sum_eq_zero (fun u hu => by simp [hu])
    have h2 : ∑ u ∈ T, (if G.Adj t u ∧ u ∉ S then (1 : ℤ) else 0) = ∑ u ∈ T, B t u :=
      sum_congr rfl (fun u hu => by
        have : u ∉ S := fun h => disjoint_left.mp hST h hu
        simp [B, this])
    have h3 : ∑ u ∈ R, (if G.Adj t u ∧ u ∉ S then (1 : ℤ) else 0) = ∑ u ∈ R, B t u :=
      sum_congr rfl (fun u hu => by simp [B, ((hmemR u).mp hu).1])
    rw [h1, h2, h3, zero_add]
  have hZ : (#{p ∈ R ×ˢ (univ : Finset V) |
      (p.2 ∈ S ∧ H.Adj p.1 p.2) ∨ (p.2 ∈ T ∧ G.Adj p.1 p.2 ∧ ¬H.Adj p.1 p.2)} : ℤ) =
      ∑ w ∈ R, (∑ u ∈ S, A w u + ∑ u ∈ T, (B w u - A w u)) := by
    rw [card_filter]; push_cast
    rw [sum_product]
    refine sum_congr rfl (fun w _ => ?_)
    rw [sum_split3 hST]
    have h1 : ∑ u ∈ S, (if (u ∈ S ∧ H.Adj w u) ∨ (u ∈ T ∧ G.Adj w u ∧ ¬H.Adj w u)
        then (1 : ℤ) else 0) = ∑ u ∈ S, A w u :=
      sum_congr rfl (fun u hu => by
        have : u ∉ T := fun h => disjoint_left.mp hST hu h
        simp [A, hu, this])
    have h2 : ∑ u ∈ T, (if (u ∈ S ∧ H.Adj w u) ∨ (u ∈ T ∧ G.Adj w u ∧ ¬H.Adj w u)
        then (1 : ℤ) else 0) = ∑ u ∈ T, (B w u - A w u) :=
      sum_congr rfl (fun u hu => by
        have : u ∉ S := fun h => disjoint_left.mp hST h hu
        simp only [this, hu, false_and, true_and, false_or, A, B]
        by_cases h1 : H.Adj w u
        · simp [h1, hHG h1]
        · by_cases h2 : G.Adj w u <;> simp [h1, h2])
    have h3 : ∑ u ∈ R, (if (u ∈ S ∧ H.Adj w u) ∨ (u ∈ T ∧ G.Adj w u ∧ ¬H.Adj w u)
        then (1 : ℤ) else 0) = 0 :=
      sum_eq_zero (fun u hu => by simp [((hmemR u).mp hu).1, ((hmemR u).mp hu).2])
    rw [h1, h2, h3, add_zero]
  rw [hZ]
  simp only [hf, hN, sum_split3 hST]
  have e1 : ∑ w ∈ R, ∑ u ∈ S, A w u = ∑ s ∈ S, ∑ u ∈ R, A s u := by
    rw [sum_comm]; exact sum_congr rfl (fun _ _ => sum_congr rfl (fun _ _ => hAsymm _ _))
  have e2 : ∑ w ∈ R, ∑ u ∈ T, (B w u - A w u) = ∑ t ∈ T, ∑ u ∈ R, (B t u - A t u) := by
    rw [sum_comm]
    exact sum_congr rfl (fun _ _ => sum_congr rfl (fun _ _ => by rw [hAsymm, hBsymm]))
  have e3 : ∑ s ∈ S, ∑ u ∈ T, A s u = ∑ t ∈ T, ∑ u ∈ S, A t u := by
    rw [sum_comm]; exact sum_congr rfl (fun _ _ => sum_congr rfl (fun _ _ => hAsymm _ _))
  have p1 : 0 ≤ ∑ s ∈ S, ∑ u ∈ S, A s u := sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => hA0 _ _))
  have p2 : 0 ≤ ∑ t ∈ T, ∑ u ∈ T, (B t u - A t u) :=
    sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => sub_nonneg.mpr (hAB _ _)))
  simp only [sum_add_distrib, sum_sub_distrib] at e2 p2 ⊢
  linarith

open Classical in
/-- Necessity in Tutte's f-factor theorem (classical formulation). -/
theorem oddCnt_le_of_factor (G H : SimpleGraph V) (hHG : H ≤ G) (f : V → ℕ)
    (hdeg : ∀ v, #{u | H.Adj v u} = f v) (S T : Finset V) (hST : Disjoint S T) :
    (oddCount G f S T : ℤ) ≤
      ∑ v ∈ S, (f v : ℤ) - ∑ v ∈ T, (f v : ℤ) + ∑ v ∈ T, (#{u | G.Adj v u ∧ u ∉ S} : ℤ) :=
  (Nat.cast_le.mpr (oddCnt_le_card_witness G H hHG f hdeg S T)).trans
    (card_witness_le G H hHG f hdeg S T hST)

end FFactor
