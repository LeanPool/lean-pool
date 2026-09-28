/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — the counting lemmas of the **placement hypergraph**

A *placement* of a copy `c` of the box-allocation residual (`Nibble.BoxAllocationSpec`) is a triple
`A : ZMod 3 → Finset (Fin P)` of cell sets of the prescribed sizes `u a = sz c a`, one per cluster
of the copy.  The nibble spreads the weight of a copy uniformly over its placements, so all the
loads and codegrees of the placement hypergraph are ratios of the counts collected here: the number
of placements whose `p`-th set contains a prescribed cell, or two prescribed cells, etc.

Everything is an exact identity in `ℕ`, stated in the cleared form `count · P^k = (falling factorial
of the sizes) · #placements`, so that no division and no binomial coefficient survives.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Finset.Fin
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Ring

/-! # BoxPlacementCount -/

open Finset

@[expose] public section

namespace Nibble.AX1.BoxCount

/-- The cell sets of a prescribed size in one cluster. -/
def subs (P u : ℕ) : Finset (Finset (Fin P)) := (Finset.univ : Finset (Fin P)).powersetCard u

/-- The placements of a copy with prescribed sizes `u`: one cell set per cluster. -/
def plc (P : ℕ) (u : ZMod 3 → ℕ) : Finset (ZMod 3 → Finset (Fin P)) :=
  Fintype.piFinset (fun a => subs P (u a))

variable {P : ℕ} {u : ZMod 3 → ℕ}

theorem mem_subs {u : ℕ} {A : Finset (Fin P)} : A ∈ subs P u ↔ #A = u := by
  rw [subs, Finset.mem_powersetCard_univ]

theorem card_subs (P u : ℕ) : #(subs P u) = Nat.choose P u := by
  rw [subs, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

theorem mem_plc {A : ZMod 3 → Finset (Fin P)} : A ∈ plc P u ↔ ∀ a, #(A a) = u a := by
  rw [plc, Fintype.mem_piFinset]
  exact forall_congr' fun a => mem_subs

/-! ### Counting the cell sets of one cluster -/

/-- The subsets of prescribed size containing a prescribed set. -/
theorem card_subs_req {u : ℕ} (B : Finset (Fin P)) (hB : #B ≤ u) :
    #((subs P u).filter (fun A => B ⊆ A)) = Nat.choose (P - #B) (u - #B) := by
  classical
  have hkey : #((subs P u).filter (fun A => B ⊆ A))
      = #(Finset.powersetCard (u - #B) ((Finset.univ : Finset (Fin P)) \ B)) := by
    refine Finset.card_bij' (fun A _ => A \ B) (fun Cc _ => Cc ∪ B) ?_ ?_ ?_ ?_
    · intro A hA
      rw [Finset.mem_filter, mem_subs] at hA
      rw [Finset.mem_powersetCard]
      refine ⟨?_, ?_⟩
      · intro x hx
        rw [Finset.mem_sdiff] at hx ⊢
        exact ⟨Finset.mem_univ x, hx.2⟩
      · rw [Finset.card_sdiff_of_subset hA.2, hA.1]
    · intro Cc hCc
      rw [Finset.mem_powersetCard] at hCc
      rw [Finset.mem_filter, mem_subs]
      have hdisj : Disjoint Cc B := by
        rw [Finset.disjoint_right]
        intro x hxB hxC
        have := hCc.1 hxC
        rw [Finset.mem_sdiff] at this
        exact this.2 hxB
      refine ⟨?_, Finset.subset_union_right⟩
      rw [Finset.card_union_of_disjoint hdisj, hCc.2]
      omega
    · intro A hA
      rw [Finset.mem_filter] at hA
      show A \ B ∪ B = A
      rw [Finset.sdiff_union_of_subset hA.2]
    · intro Cc hCc
      rw [Finset.mem_powersetCard] at hCc
      have hdisj : Disjoint Cc B := by
        rw [Finset.disjoint_right]
        intro x hxB hxC
        have := hCc.1 hxC
        rw [Finset.mem_sdiff] at this
        exact this.2 hxB
      change (Cc ∪ B) \ B = Cc
      rw [Finset.union_sdiff_cancel_right hdisj]
  rw [hkey, Finset.card_powersetCard, Finset.card_sdiff_of_subset (Finset.subset_univ B),
    Finset.card_univ, Fintype.card_fin]

/-- The absorption identity for binomial coefficients, in cleared form. -/
theorem choose_mul_step {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    n * Nat.choose (n - 1) (k - 1) = k * Nat.choose n k := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have := Nat.add_one_mul_choose_eq n' k'
  simpa [Nat.mul_comm] using this

/-- **One prescribed cell in one cluster.** -/
theorem subs_one_mul {u : ℕ} (huP : u ≤ P) (i : Fin P) :
    #((subs P u).filter (fun A => ({i} : Finset (Fin P)) ⊆ A)) * P = u * #(subs P u) := by
  rcases Nat.eq_zero_or_pos u with rfl | hu
  · have hempty : (subs P 0).filter (fun A => ({i} : Finset (Fin P)) ⊆ A) = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun A hA => ?_
      rw [Finset.mem_filter, mem_subs] at hA
      have := Finset.card_le_card hA.2
      simp [hA.1] at this
    rw [hempty]
    simp
  · have hB : #({i} : Finset (Fin P)) = 1 := Finset.card_singleton i
    rw [card_subs_req {i} (by omega), card_subs, hB, Nat.mul_comm]
    exact choose_mul_step hu huP

/-- **Two prescribed cells in one cluster.** -/
theorem subs_two_mul {u : ℕ} (huP : u ≤ P) {i i' : Fin P} (hii : i ≠ i') :
    #((subs P u).filter (fun A => ({i, i'} : Finset (Fin P)) ⊆ A)) * (P * (P - 1))
      = u * (u - 1) * #(subs P u) := by
  have hB : #({i, i'} : Finset (Fin P)) = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hii), Finset.card_singleton]
  by_cases hu : 2 ≤ u
  · have h1 : #((subs P u).filter (fun A => ({i, i'} : Finset (Fin P)) ⊆ A))
        = Nat.choose (P - 2) (u - 2) := by
      rw [card_subs_req _ (by omega), hB]
    have hP2 : 2 ≤ P := le_trans hu huP
    have e1 : (P - 1) * Nat.choose (P - 2) (u - 2) = (u - 1) * Nat.choose (P - 1) (u - 1) := by
      have := choose_mul_step (n := P - 1) (k := u - 1) (by omega) (by omega)
      have h2 : P - 1 - 1 = P - 2 := by omega
      have h3 : u - 1 - 1 = u - 2 := by omega
      rwa [h2, h3] at this
    have e2 : P * Nat.choose (P - 1) (u - 1) = u * Nat.choose P u :=
      choose_mul_step (by omega) huP
    rw [h1, card_subs]
    calc Nat.choose (P - 2) (u - 2) * (P * (P - 1))
        = P * ((P - 1) * Nat.choose (P - 2) (u - 2)) := by ring
      _ = P * ((u - 1) * Nat.choose (P - 1) (u - 1)) := by rw [e1]
      _ = (u - 1) * (P * Nat.choose (P - 1) (u - 1)) := by ring
      _ = (u - 1) * (u * Nat.choose P u) := by rw [e2]
      _ = u * (u - 1) * Nat.choose P u := by ring
  · have hempty : (subs P u).filter (fun A => ({i, i'} : Finset (Fin P)) ⊆ A) = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun A hA => ?_
      rw [Finset.mem_filter, mem_subs] at hA
      have := Finset.card_le_card hA.2
      rw [hB, hA.1] at this
      omega
    rw [hempty]
    have : u * (u - 1) = 0 := by
      interval_cases u <;> simp_all
    simp [this]

/-! ### Counting the placements -/

theorem succ_ne_self (p : ZMod 3) : p ≠ p + 1 := by revert p; decide

/-- Two distinct positions of a copy have a unique third. -/
theorem exists_third {p q : ZMod 3} (hpq : p ≠ q) : ∃ t : ZMod 3, p ≠ t ∧ q ≠ t := by
  revert hpq
  revert p q
  decide

/-- Three distinct positions exhaust `ZMod 3`. -/
theorem univ_eq_three {p q t : ZMod 3} (hpq : p ≠ q) (hpt : p ≠ t) (hqt : q ≠ t) :
    (Finset.univ : Finset (ZMod 3)) = {p, q, t} := by
  have hcard : #({p, q, t} : Finset (ZMod 3)) = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hpq, hpt]),
      Finset.card_insert_of_notMem (by simp [hqt]), Finset.card_singleton]
  refine (Finset.eq_of_subset_of_card_le (Finset.subset_univ _) ?_).symm
  rw [hcard, Finset.card_univ, ZMod.card]

theorem mem_three {p q t : ZMod 3} (hpq : p ≠ q) (hpt : p ≠ t) (hqt : q ≠ t) (a : ZMod 3) :
    a = p ∨ a = q ∨ a = t := by
  have : a ∈ ({p, q, t} : Finset (ZMod 3)) := by
    rw [← univ_eq_three hpq hpt hqt]; exact Finset.mem_univ a
  simpa using this

/-- A product over the three positions of a copy. -/
theorem prod_three {M : Type*} [CommMonoid M] (f : ZMod 3 → M) {p q t : ZMod 3} (hpq : p ≠ q)
    (hpt : p ≠ t) (hqt : q ≠ t) : ∏ a : ZMod 3, f a = f p * f q * f t := by
  rw [univ_eq_three hpq hpt hqt, Finset.prod_insert (by simp [hpq, hpt]),
    Finset.prod_insert (by simp [hqt]), Finset.prod_singleton, mul_assoc]

/-- **The placements are the products of the cell sets**: a coordinatewise condition splits. -/
theorem card_plc_req (req : ZMod 3 → Finset (Fin P)) :
    #((plc P u).filter (fun A => ∀ a, req a ⊆ A a))
      = ∏ a : ZMod 3, #((subs P (u a)).filter (fun A => req a ⊆ A)) := by
  classical
  have hset : (plc P u).filter (fun A => ∀ a, req a ⊆ A a)
      = Fintype.piFinset (fun a => (subs P (u a)).filter (fun A => req a ⊆ A)) := by
    ext A
    simp only [Finset.mem_filter, plc, Fintype.mem_piFinset, ← forall_and]
  rw [hset, Fintype.card_piFinset]

/-- The requirement attached to a triple of prescribed cell sets. -/
private def req3 (p q _t : ZMod 3) (Bp Bq Bt : Finset (Fin P)) : ZMod 3 → Finset (Fin P) :=
  fun a => if a = p then Bp else if a = q then Bq else Bt

/-- **The master count**: a coordinatewise requirement splits into a product over the three
clusters. -/
theorem card_plc_three {p q t : ZMod 3} (hpq : p ≠ q) (hpt : p ≠ t) (hqt : q ≠ t)
    (Bp Bq Bt : Finset (Fin P)) :
    #((plc P u).filter (fun A => Bp ⊆ A p ∧ Bq ⊆ A q ∧ Bt ⊆ A t))
      = #((subs P (u p)).filter (fun A => Bp ⊆ A)) * #((subs P (u q)).filter (fun A => Bq ⊆ A))
        * #((subs P (u t)).filter (fun A => Bt ⊆ A)) := by
  classical
  have hp : req3 p q t Bp Bq Bt p = Bp := by rw [req3, ite_eq_left rfl]
  have hq : req3 p q t Bp Bq Bt q = Bq := by
    rw [req3, ite_eq_right (Ne.symm hpq), ite_eq_left rfl]
  have ht : req3 p q t Bp Bq Bt t = Bt := by
    rw [req3, ite_eq_right (Ne.symm hpt), ite_eq_right (Ne.symm hqt)]
  have hfil : (plc P u).filter (fun A => Bp ⊆ A p ∧ Bq ⊆ A q ∧ Bt ⊆ A t)
      = (plc P u).filter (fun A => ∀ a, req3 p q t Bp Bq Bt a ⊆ A a) := by
    refine Finset.filter_congr fun A _ => ?_
    constructor
    · rintro ⟨h1, h2, h3⟩ a
      rcases mem_three hpq hpt hqt a with rfl | rfl | rfl
      · rwa [hp]
      · rwa [hq]
      · rwa [ht]
    · intro h
      exact ⟨by have := h p; rwa [hp] at this, by have := h q; rwa [hq] at this,
        by have := h t; rwa [ht] at this⟩
  rw [hfil, card_plc_req, prod_three _ hpq hpt hqt, hp, hq, ht]

/-- The empty requirement is no requirement. -/
theorem filter_empty_req (v : ℕ) :
    ((subs P v).filter (fun A => (∅ : Finset (Fin P)) ⊆ A)) = subs P v :=
  Finset.filter_true_of_mem fun _ _ => Finset.empty_subset _

theorem card_plc_prod {p q t : ZMod 3} (hpq : p ≠ q) (hpt : p ≠ t) (hqt : q ≠ t) :
    #(plc P u) = #(subs P (u p)) * #(subs P (u q)) * #(subs P (u t)) := by
  rw [plc, Fintype.card_piFinset, prod_three (fun a => #(subs P (u a))) hpq hpt hqt]

theorem card_plc_pos (huP : ∀ a, u a ≤ P) : 0 < #(plc P u) := by
  rw [Finset.card_pos]
  refine ⟨fun a => (Finset.range (u a)).attachFin
      (fun m hm => lt_of_lt_of_le (Finset.mem_range.mp hm) (huP a)), ?_⟩
  rw [mem_plc]
  intro a
  simp

theorem card_one (huP : ∀ a, u a ≤ P) (p : ZMod 3) (i : Fin P) :
    #((plc P u).filter (fun A => i ∈ A p)) * P = u p * #(plc P u) := by
  classical
  set q : ZMod 3 := p + 1 with hqdef
  have hpq : p ≠ q := succ_ne_self p
  obtain ⟨t, hpt, hqt⟩ := exists_third hpq
  have hfil : (plc P u).filter (fun A => i ∈ A p)
      = (plc P u).filter (fun A => ({i} : Finset (Fin P)) ⊆ A p ∧ (∅ : Finset (Fin P)) ⊆ A q
          ∧ (∅ : Finset (Fin P)) ⊆ A t) := by
    refine Finset.filter_congr fun A _ => ?_
    simp [Finset.singleton_subset_iff]
  rw [hfil, card_plc_three hpq hpt hqt, filter_empty_req, filter_empty_req,
    card_plc_prod (u := u) hpq hpt hqt]
  calc #((subs P (u p)).filter (fun A => ({i} : Finset (Fin P)) ⊆ A)) * #(subs P (u q))
        * #(subs P (u t)) * P
      = (#((subs P (u p)).filter (fun A => ({i} : Finset (Fin P)) ⊆ A)) * P)
        * (#(subs P (u q)) * #(subs P (u t))) := by ring
    _ = (u p * #(subs P (u p))) * (#(subs P (u q)) * #(subs P (u t))) := by
        rw [subs_one_mul (huP p) i]
    _ = u p * (#(subs P (u p)) * #(subs P (u q)) * #(subs P (u t))) := by ring

theorem card_two (huP : ∀ a, u a ≤ P) {p q : ZMod 3} (hpq : p ≠ q) (i j : Fin P) :
    #((plc P u).filter (fun A => i ∈ A p ∧ j ∈ A q)) * (P * P) = u p * u q * #(plc P u) := by
  classical
  obtain ⟨t, hpt, hqt⟩ := exists_third hpq
  have hfil : (plc P u).filter (fun A => i ∈ A p ∧ j ∈ A q)
      = (plc P u).filter (fun A => ({i} : Finset (Fin P)) ⊆ A p ∧ ({j} : Finset (Fin P)) ⊆ A q
          ∧ (∅ : Finset (Fin P)) ⊆ A t) := by
    refine Finset.filter_congr fun A _ => ?_
    simp [Finset.singleton_subset_iff]
  rw [hfil, card_plc_three hpq hpt hqt, filter_empty_req, card_plc_prod (u := u) hpq hpt hqt]
  calc #((subs P (u p)).filter (fun A => ({i} : Finset (Fin P)) ⊆ A))
        * #((subs P (u q)).filter (fun A => ({j} : Finset (Fin P)) ⊆ A))
        * #(subs P (u t)) * (P * P)
      = (#((subs P (u p)).filter (fun A => ({i} : Finset (Fin P)) ⊆ A)) * P)
        * (#((subs P (u q)).filter (fun A => ({j} : Finset (Fin P)) ⊆ A)) * P)
        * #(subs P (u t)) := by ring
    _ = (u p * #(subs P (u p))) * (u q * #(subs P (u q))) * #(subs P (u t)) := by
        rw [subs_one_mul (huP p) i, subs_one_mul (huP q) j]
    _ = u p * u q * (#(subs P (u p)) * #(subs P (u q)) * #(subs P (u t))) := by ring

theorem card_two_one (huP : ∀ a, u a ≤ P) {p q : ZMod 3} (hpq : p ≠ q) {i i' : Fin P}
    (hii : i ≠ i') (j : Fin P) :
    #((plc P u).filter (fun A => i ∈ A p ∧ i' ∈ A p ∧ j ∈ A q)) * (P * (P - 1) * P)
      = u p * (u p - 1) * u q * #(plc P u) := by
  classical
  obtain ⟨t, hpt, hqt⟩ := exists_third hpq
  have hfil : (plc P u).filter (fun A => i ∈ A p ∧ i' ∈ A p ∧ j ∈ A q)
      = (plc P u).filter (fun A => ({i, i'} : Finset (Fin P)) ⊆ A p
          ∧ ({j} : Finset (Fin P)) ⊆ A q ∧ (∅ : Finset (Fin P)) ⊆ A t) := by
    refine Finset.filter_congr fun A _ => ?_
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.empty_subset,
      and_true]
    tauto
  rw [hfil, card_plc_three hpq hpt hqt, filter_empty_req, card_plc_prod (u := u) hpq hpt hqt]
  calc #((subs P (u p)).filter (fun A => ({i, i'} : Finset (Fin P)) ⊆ A))
        * #((subs P (u q)).filter (fun A => ({j} : Finset (Fin P)) ⊆ A))
        * #(subs P (u t)) * (P * (P - 1) * P)
      = (#((subs P (u p)).filter (fun A => ({i, i'} : Finset (Fin P)) ⊆ A)) * (P * (P - 1)))
        * (#((subs P (u q)).filter (fun A => ({j} : Finset (Fin P)) ⊆ A)) * P)
        * #(subs P (u t)) := by ring
    _ = (u p * (u p - 1) * #(subs P (u p))) * (u q * #(subs P (u q))) * #(subs P (u t)) := by
        rw [subs_two_mul (huP p) hii, subs_one_mul (huP q) j]
    _ = u p * (u p - 1) * u q * (#(subs P (u p)) * #(subs P (u q)) * #(subs P (u t))) := by ring

theorem card_three (huP : ∀ a, u a ≤ P) {p q t : ZMod 3} (hpq : p ≠ q) (hpt : p ≠ t)
    (hqt : q ≠ t) (i j l : Fin P) :
    #((plc P u).filter (fun A => i ∈ A p ∧ j ∈ A q ∧ l ∈ A t)) * (P * P * P)
      = u p * u q * u t * #(plc P u) := by
  classical
  have hfil : (plc P u).filter (fun A => i ∈ A p ∧ j ∈ A q ∧ l ∈ A t)
      = (plc P u).filter (fun A => ({i} : Finset (Fin P)) ⊆ A p ∧ ({j} : Finset (Fin P)) ⊆ A q
          ∧ ({l} : Finset (Fin P)) ⊆ A t) := by
    refine Finset.filter_congr fun A _ => ?_
    simp [Finset.singleton_subset_iff]
  rw [hfil, card_plc_three hpq hpt hqt, card_plc_prod (u := u) hpq hpt hqt]
  calc #((subs P (u p)).filter (fun A => ({i} : Finset (Fin P)) ⊆ A))
        * #((subs P (u q)).filter (fun A => ({j} : Finset (Fin P)) ⊆ A))
        * #((subs P (u t)).filter (fun A => ({l} : Finset (Fin P)) ⊆ A)) * (P * P * P)
      = (#((subs P (u p)).filter (fun A => ({i} : Finset (Fin P)) ⊆ A)) * P)
        * (#((subs P (u q)).filter (fun A => ({j} : Finset (Fin P)) ⊆ A)) * P)
        * (#((subs P (u t)).filter (fun A => ({l} : Finset (Fin P)) ⊆ A)) * P) := by ring
    _ = (u p * #(subs P (u p))) * (u q * #(subs P (u q))) * (u t * #(subs P (u t))) := by
        rw [subs_one_mul (huP p) i, subs_one_mul (huP q) j, subs_one_mul (huP t) l]
    _ = u p * u q * u t * (#(subs P (u p)) * #(subs P (u q)) * #(subs P (u t))) := by ring

end Nibble.AX1.BoxCount
