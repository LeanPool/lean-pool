/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BalancedEdgeColourings.Bkls.Comp

/-!
# Two-colouring graphs of maximum degree two with even cycles

`two_colour`: a graph of maximum degree two whose cycles have even length has a proper colouring
with two colours (each component, a path or an even cycle, is coloured by the parity of the
position along it). `two_colour_two_matchings`: the union of two matchings has only even cycles.
-/

@[expose] public section

namespace LeanPool.BalancedEdgeColourings

namespace Bkls.Comp

open Finset

variable {E : Type*} [Fintype E] [DecidableEq E] {L : SimpleGraph E}

omit [DecidableEq E] in
/-- **Two colours suffice.** -/
theorem two_colour [DecidableRel L.Adj] (hdeg : ∀ v, L.degree v ≤ 2)
    (heven : ∀ n p, IsPathFn L n p → 2 ≤ n → L.Adj (p 0) (p n) → Even (n + 1)) :
    ∃ g : E → Bool, ∀ a b, L.Adj a b → g a ≠ g b := by
  classical
  let Cl : Finset E → Prop := fun D => ∀ a b, L.Adj a b → (a ∈ D ↔ b ∈ D)
  suffices key : ∀ m, ∀ D : Finset E, #D ≤ m → Cl D →
      ∃ g : E → Bool, ∀ a b, a ∈ D → L.Adj a b → g a ≠ g b by
    obtain ⟨g, hg⟩ := key _ univ le_rfl (fun a b _ => by simp)
    exact ⟨g, fun a b h => hg a b (mem_univ _) h⟩
  intro m
  induction m with
  | zero =>
    intro D _ hD
    have : D = ∅ := card_eq_zero.1 (by omega)
    subst this
    exact ⟨fun _ => false, fun a b ha => absurd ha (notMem_empty a)⟩
  | succ m ih =>
    intro D hDc hD
    rcases D.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · exact ⟨fun _ => false, fun a b ha => absurd ha (notMem_empty a)⟩
    obtain ⟨n, p, hp, hpx, hmax⟩ := exists_maxPath L x
    have hcl : ∀ j ≤ n, ∀ y, L.Adj (p j) y → ∃ k ≤ n, p k = y := fun j hj y hy =>
      maxPath_closed hdeg hp hpx hmax hj hy
    set C := (range (n + 1)).image p with hC
    have hmemC : ∀ w, w ∈ C ↔ ∃ i ≤ n, p i = w := fun w => by
      simp only [hC, mem_image, mem_range]
      exact ⟨fun ⟨i, hi, h⟩ => ⟨i, by omega, h⟩, fun ⟨i, hi, h⟩ => ⟨i, by omega, h⟩⟩
    have hpD0 : ∀ i ≤ n, (p i ∈ D ↔ p 0 ∈ D) := by
      intro i hi
      induction i with
      | zero => rfl
      | succ i ihi => rw [← ihi (by omega), hD _ _ (hp.2 i (by omega))]
    have hCD : C ⊆ D := by
      intro w hw
      obtain ⟨i, hi, rfl⟩ := (hmemC w).1 hw
      obtain ⟨i0, hi0, hx0⟩ := hpx
      rw [hpD0 i hi, ← hpD0 i0 hi0, hx0]; exact hx
    set D' := D \ C with hD'
    have hCcl : ∀ a b, L.Adj a b → (a ∈ C ↔ b ∈ C) := by
      intro a b hab
      constructor
      · intro ha
        obtain ⟨i, hi, rfl⟩ := (hmemC a).1 ha
        obtain ⟨k, hk, rfl⟩ := hcl i hi b hab
        exact (hmemC _).2 ⟨k, hk, rfl⟩
      · intro hb
        obtain ⟨i, hi, rfl⟩ := (hmemC b).1 hb
        obtain ⟨k, hk, rfl⟩ := hcl i hi a hab.symm
        exact (hmemC _).2 ⟨k, hk, rfl⟩
    have hD'c : Cl D' := fun a b hab => by
      simp only [hD', mem_sdiff]
      rw [hD a b hab, hCcl a b hab]
    have hcardD' : #D' ≤ m := by
      have h1 := card_sdiff_add_card_eq_card hCD
      have h2 : 0 < #C := card_pos.2 ⟨p 0, (hmemC _).2 ⟨0, by omega, rfl⟩⟩
      rw [hD']; omega
    obtain ⟨g, hg⟩ := ih D' hcardD' hD'c
    let idx : E → ℕ := fun w => if h : ∃ i ≤ n, p i = w then h.choose else 0
    have hidx : ∀ i ≤ n, idx (p i) = i := fun i hi => by
      have h : ∃ i' ≤ n, p i' = p i := ⟨i, hi, rfl⟩
      simp only [idx, dite_eq_left h]
      exact hp.1 _ _ h.choose_spec.1 hi h.choose_spec.2
    let g' : E → Bool := fun w => if w ∈ C then decide (idx w % 2 = 0) else g w
    refine ⟨g', fun a b ha hab => ?_⟩
    by_cases haC : a ∈ C
    · have hbC := (hCcl a b hab).1 haC
      obtain ⟨i, hi, rfl⟩ := (hmemC a).1 haC
      obtain ⟨j, hj, rfl⟩ := (hmemC _).1 hbC
      simp only [g', ite_eq_left haC, ite_eq_left hbC, hidx i hi, hidx j hj]
      have key : j = i + 1 ∨ i = j + 1 ∨ (i = 0 ∧ j = n ∧ 2 ≤ n) ∨ (j = 0 ∧ i = n ∧ 2 ≤ n) := by
        rcases lt_trichotomy i j with hij | hij | hij
        · rcases maxPath_adj hdeg hp hij hj hab with h | h
          · exact Or.inl h
          · by_cases hn2 : 2 ≤ n
            · exact Or.inr (Or.inr (Or.inl ⟨h.1, h.2, hn2⟩))
            · left; omega
        · rw [hij] at hab; exact absurd hab (L.loopless.irrefl _)
        · rcases maxPath_adj hdeg hp hij hi hab.symm with h | h
          · exact Or.inr (Or.inl h)
          · by_cases hn2 : 2 ≤ n
            · exact Or.inr (Or.inr (Or.inr ⟨h.1, h.2, hn2⟩))
            · right; left; omega
      have hend : 2 ≤ n → L.Adj (p 0) (p n) → ∃ k, n + 1 = k + k := fun h1 h2 => heven n p hp h1 h2
      simp only [ne_eq, decide_eq_decide]
      rcases key with h | h | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · omega
      · omega
      · obtain ⟨k, hk⟩ := hend h3 (by rw [← h1, ← h2]; exact hab)
        omega
      · obtain ⟨k, hk⟩ := hend h3 (by rw [← h1, ← h2]; exact hab.symm)
        omega
    · have hbC : b ∉ C := fun h => haC ((hCcl a b hab).2 h)
      simp only [g', ite_eq_right haC, ite_eq_right hbC]
      exact hg a b (mem_sdiff.2 ⟨ha, haC⟩) hab

omit [DecidableEq E] [Fintype E] in
/-- **The union of two matchings is two-colourable.** -/
theorem two_matchings [Finite E] (Q B : E → E → Prop) (hQs : ∀ u v, Q u v → Q v u)
    (hQu : ∀ u v w, Q u v → Q u w → v = w) (hBs : ∀ u v, B u v → B v u)
    (hBu : ∀ u v w, B u v → B u w → v = w) :
    ∃ g : E → Bool, (∀ u v, u ≠ v → Q u v → g u ≠ g v) ∧ (∀ u v, u ≠ v → B u v → g u ≠ g v) := by
  classical
  let : Fintype E := Fintype.ofFinite E
  let Γ : SimpleGraph E :=
    { Adj := fun u v => u ≠ v ∧ (Q u v ∨ B u v)
      symm := ⟨fun u v ⟨h1, h2⟩ => ⟨Ne.symm h1, h2.imp (hQs u v) (hBs u v)⟩⟩
      loopless := ⟨fun v h => h.1 rfl⟩ }
  have hdeg : ∀ v, Γ.degree v ≤ 2 := by
    intro v
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have hsub : Γ.neighborFinset v ⊆ (univ.filter (Q v)) ∪ (univ.filter (B v)) := by
      intro w hw
      rw [SimpleGraph.mem_neighborFinset] at hw
      rcases hw.2 with h | h
      · exact mem_union_left _ (mem_filter.2 ⟨mem_univ _, h⟩)
      · exact mem_union_right _ (mem_filter.2 ⟨mem_univ _, h⟩)
    have h1 : #(univ.filter (Q v)) ≤ 1 := card_le_one.2 fun a ha b hb =>
      hQu v a b (mem_filter.1 ha).2 (mem_filter.1 hb).2
    have h2 : #(univ.filter (B v)) ≤ 1 := card_le_one.2 fun a ha b hb =>
      hBu v a b (mem_filter.1 ha).2 (mem_filter.1 hb).2
    have := card_le_card hsub
    have := card_union_le (univ.filter (Q v)) (univ.filter (B v))
    omega
  -- at a vertex, two distinct neighbours are joined by edges of different kinds
  have halt : ∀ a b c, b ≠ c → Γ.Adj a b → Γ.Adj a c → (Q a b ↔ ¬ Q a c) := by
    intro a b c hbc hab hac
    constructor
    · intro h1 h2; exact hbc (hQu a b c h1 h2)
    · intro h2
      rcases hab.2 with h1 | h1
      · exact h1
      · rcases hac.2 with h3 | h3
        · exact absurd h3 h2
        · exact absurd (hBu a b c h1 h3) hbc
  have hsym : ∀ a b, Q a b ↔ Q b a := fun a b => ⟨hQs a b, hQs b a⟩
  obtain ⟨g, hg⟩ := two_colour hdeg (fun n p hp hn2 hend => by
    -- the kinds of consecutive edges alternate
    have hstep : ∀ i, i + 2 ≤ n →
        (Q (p (i + 1)) (p (i + 1 + 1)) ↔ ¬ Q (p i) (p (i + 1))) := by
      intro i hi
      have hne : p i ≠ p (i + 1 + 1) := fun e => by
        have := hp.1 _ _ (by omega) (by omega) e; omega
      have hA := halt (p (i + 1)) (p i) (p (i + 1 + 1)) hne (hp.2 i (by omega)).symm
        (hp.2 (i + 1) (by omega))
      rw [hsym (p (i + 1)) (p i)] at hA
      constructor
      · intro h h'; exact hA.1 h' h
      · intro h; by_contra h'; exact h (hA.2 h')
    let t : ℕ → Bool := fun i => decide (Q (p i) (p (i + 1)))
    have hflip : ∀ i, i + 2 ≤ n → t (i + 1) = !t i := by
      intro i hi
      have := hstep i hi
      simp only [t]
      by_cases h : Q (p i) (p (i + 1))
      · have h' : ¬ Q (p (i + 1)) (p (i + 1 + 1)) := fun h'' => this.1 h'' h
        simp [h, h']
      · have h' : Q (p (i + 1)) (p (i + 1 + 1)) := this.2 h
        simp [h, h']
    have hpar : ∀ i, i + 1 ≤ n → t i = (if i % 2 = 0 then t 0 else !t 0) := by
      intro i hi
      induction i with
      | zero => simp
      | succ i ih =>
        rw [hflip i (by omega), ih (by omega)]
        split_ifs with h1 h2 h2 <;> first | omega | simp
    -- the two edges at `p n` and at `p 0`
    have hne1 : p (n - 1) ≠ p 0 := fun e => by have := hp.1 _ _ (by omega) (by omega) e; omega
    have hne0 : p n ≠ p 1 := fun e => by have := hp.1 _ _ (by omega) (by omega) e; omega
    have hadj1 : Γ.Adj (p n) (p (n - 1)) := by
      have := hp.2 (n - 1) (by omega); rw [show n - 1 + 1 = n by omega] at this; exact this.symm
    have hA := halt (p n) (p (n - 1)) (p 0) hne1 hadj1 hend.symm
    have hB := halt (p 0) (p n) (p 1) hne0 hend (hp.2 0 (by omega))
    have e1 : t (n - 1) = t 0 := by
      simp only [t, show n - 1 + 1 = n by omega, zero_add]
      rw [decide_eq_decide, hsym (p (n - 1)) (p n), hA, hsym (p n) (p 0), hB]
      tauto
    have h3 := hpar (n - 1) (by omega)
    rw [e1] at h3
    split_ifs at h3 with h4
    · exact ⟨(n + 1) / 2, by omega⟩
    · cases ht : t 0 <;> rw [ht] at h3 <;> simp at h3)
  exact ⟨g, fun u v huv h => hg u v ⟨huv, Or.inl h⟩, fun u v huv h => hg u v ⟨huv, Or.inr h⟩⟩
end Bkls.Comp

end LeanPool.BalancedEdgeColourings
