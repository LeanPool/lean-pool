/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.R434.RobustHosts

/-! Score certificates extend across isolated residual vertices. -/

@[expose] public section
namespace GapExtremal.R434
open Finset

variable {V X : Type}

/-- Adds a disjoint set of isolated vertices to `B`. -/
def withIsolates (B : SimpleGraph V) : SimpleGraph (V ⊕ X) := B.map Function.Embedding.inl

@[simp] theorem isolates_adj_inl (B : SimpleGraph V) (a b : V) :
    (withIsolates B : SimpleGraph (V ⊕ X)).Adj (.inl a) (.inl b) ↔ B.Adj a b :=
  SimpleGraph.map_adj_apply

@[simp] theorem isolates_not_adj_inr (B : SimpleGraph V) (a : V ⊕ X) (x : X) :
    ¬ (withIsolates B).Adj a (.inr x) := by
  simp [withIsolates, SimpleGraph.map_adj, Function.Embedding.inl]

instance (B : SimpleGraph V) [DecidableRel B.Adj] :
    DecidableRel (withIsolates (X := X) B).Adj := fun a b =>
  match a, b with
  | .inl u, .inl v => decidable_of_iff _ (isolates_adj_inl B u v).symm
  | .inl _, .inr _ => isFalse (isolates_not_adj_inr B _ _)
  | .inr _, .inr _ => isFalse (isolates_not_adj_inr B _ _)
  | .inr _, .inl _ => isFalse fun h => isolates_not_adj_inr B _ _ h.symm

@[simp] theorem isolates_not_adj_inr_left (B : SimpleGraph V) (x : X) (a : V ⊕ X) :
    ¬ (withIsolates B).Adj (.inr x) a := fun h => isolates_not_adj_inr B a x h.symm

variable [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X]
variable (B : SimpleGraph V) [DecidableRel B.Adj]

theorem isolate_edges (Q : Finset (V ⊕ X)) :
    e (withIsolates B) Q = e B Q.toLeft := by
  rw [← Nat.mul_right_inj (a := 2) (by decide), two_mul_e_eq_D, two_mul_e_eq_D]
  have h : ∀ (L : Finset V) (R : Finset X), D (withIsolates B) (L.disjSum R) (L.disjSum R)
    = D B L L := by
    intro L R
    simp only [D, sum_disjSum, isolates_adj_inl, isolates_not_adj_inr,
      isolates_not_adj_inr_left, ite_false, sum_const_zero, add_zero]
  simpa only [toLeft_disjSum_toRight] using h Q.toLeft Q.toRight

theorem isolate_score_le (Q : Finset (V ⊕ X)) :
    w (withIsolates B) Q ≤ w B Q.toLeft := by
  unfold w
  rw [isolate_edges]
  have hc := Nat.choose_le_choose 2 (card_toLeft_le (u := Q))
  omega

theorem isolate_integral_bound (I : ℤ)
    (hi : ∀ P : Finset (Finset V), IsPack P → ∑ S ∈ P, w B S ≤ I)
    (P : Finset (Finset (V ⊕ X))) (hp : IsPack P) :
    ∑ Q ∈ P, w (withIsolates B) Q ≤ I := by
  classical
  let P' := P.filter fun Q => 2 ≤ Q.toLeft.card
  have share {Q S : Finset (V ⊕ X)} (hq : Q ∈ P) (hs : S ∈ P)
      {a b : V} (hne : a ≠ b) (ha : a ∈ Q.toLeft ∩ S.toLeft)
      (hb : b ∈ Q.toLeft ∩ S.toLeft) : Q = S := by
    by_contra hqs
    have small := card_le_one.mp (hp Q hq S hs hqs)
    have lift {u : V} (hu : u ∈ Q.toLeft ∩ S.toLeft) :
        (Sum.inl u : V ⊕ X) ∈ Q ∩ S := by simpa [mem_toLeft] using hu
    exact hne (Sum.inl_injective (small _ (lift ha) _ (lift hb)))
  have noCollisions : Set.InjOn (fun Q : Finset (V ⊕ X) => Q.toLeft) (↑P' : Set _) := by
    intro Q hq S hs eq
    obtain ⟨hq, htwo⟩ := mem_filter.mp hq
    obtain ⟨hs, _⟩ := mem_filter.mp hs
    change Q.toLeft = S.toLeft at eq
    obtain ⟨a, ha, b, hb, hne⟩ := one_lt_card.mp htwo
    exact share hq hs hne (mem_inter.mpr ⟨ha, eq ▸ ha⟩) (mem_inter.mpr ⟨hb, eq ▸ hb⟩)
  have hpack : IsPack (P'.image fun Q => Q.toLeft) := by
    intro Q hQ S hS hne
    obtain ⟨U, hu, rfl⟩ := mem_image.mp hQ
    obtain ⟨W, hw, rfl⟩ := mem_image.mp hS
    rw [card_le_one]
    intro a ha b hb
    by_contra hab
    exact hne (congrArg Finset.toLeft (share (mem_filter.mp hu).1 (mem_filter.mp hw).1 hab ha hb))
  calc
    ∑ Q ∈ P, w (withIsolates B) Q ≤ ∑ Q ∈ P', w (withIsolates B) Q := by
      apply sum_le_sum_of_subset_of_nonpos (filter_subset _ _)
      intro Q hq hnot
      have hs : Q.toLeft.card < 2 := by
        exact Nat.lt_of_not_ge fun hh => hnot (mem_filter.mpr ⟨hq, hh⟩)
      exact (isolate_score_le B Q).trans (by
        rw [w_eq_D, D_self_eq_zero_of_card_le_one B (by omega : Q.toLeft.card ≤ 1)]
        omega)
    _ ≤ ∑ Q ∈ P', w B Q.toLeft := sum_le_sum fun Q _ => isolate_score_le B Q
    _ = ∑ S ∈ P'.image (fun Q => Q.toLeft), w B S := (sum_image noCollisions).symm
    _ ≤ I := hi _ hpack

private noncomputable def liftWeights (y : Finset V → ℝ) (Q : Finset (V ⊕ X)) : ℝ :=
  if Q.toRight = ∅ then y Q.toLeft else 0

omit [DecidableEq V] [DecidableEq X] in
private theorem sum_old_columns {A : Type} [AddCommMonoid A] (g : Finset (V ⊕ X) → A)
    (hz : ∀ Q, Q.toRight ≠ ∅ → g Q = 0) :
    ∑ Q, g Q = ∑ S : Finset V, g (S.disjSum ∅) := by
  classical
  let incl : Finset V ↪ Finset (V ⊕ X) :=
    ⟨fun S => S.disjSum ∅, fun _ _ h => (disjSum_inj.mp h).1⟩
  rw [← show ∑ Q ∈ (univ.map incl), g Q = ∑ S : Finset V, g (S.disjSum ∅) from sum_map _ _ _]
  symm
  apply sum_subset (subset_univ _)
  intro Q _ hq
  apply hz Q
  intro hr
  apply hq
  exact mem_map.mpr ⟨Q.toLeft, mem_univ _, by simpa [incl, hr] using
    (toLeft_disjSum_toRight (u := Q))⟩

theorem isolate_fractional_lift_with_support {y : Finset V → ℝ} (hy : ResPack y) :
    ∃ z : Finset (V ⊕ X) → ℝ, ResPack z ∧
      ((∀ S, y S ≠ 0 → S.card ≤ 3) → ∀ Q, z Q ≠ 0 → Q.card ≤ 3) ∧
      ∑ Q, z Q * (w (withIsolates B) Q : ℝ) = ∑ S, y S * (w B S : ℝ) := by
  classical
  let z : Finset (V ⊕ X) → ℝ := liftWeights y
  refine ⟨z, ⟨fun Q => ?_, fun Q hq => ?_, fun a b hab => ?_⟩, ?_, ?_⟩
  · unfold z liftWeights
    split
    · exact hy.nonneg _
    · exact le_rfl
  · have hr : Q.toRight = ∅ := by
      by_contra hr
      exact hq (by simp [z, liftWeights, hr])
    exact (hy.two _ (by simpa [z, liftWeights, hr] using hq)).trans card_toLeft_le
  · rw [sum_old_columns _ (fun Q hr => by simp [z, liftWeights, hr])]
    rcases a with a | a <;> rcases b with b | b
    · simpa [z, liftWeights, ← disjSum_empty] using hy.load a b (by simpa using hab)
    · simp
    · simp
    · simp
  · intro hsmall Q hQ
    have hr : Q.toRight = ∅ := by
      by_contra hr
      exact hQ (by simp [z, liftWeights, hr])
    have hcard := card_toLeft_add_card_toRight (u := Q)
    rw [hr, card_empty, add_zero] at hcard
    exact hcard ▸ hsmall _ (by simpa [z, liftWeights, hr] using hQ)
  · rw [sum_old_columns _ (fun Q hr => by simp [z, liftWeights, hr])]
    refine sum_congr rfl fun S _ => ?_
    have hw : w (withIsolates B : SimpleGraph (V ⊕ X)) (S.disjSum (∅ : Finset X)) = w B S := by
      simp only [w, isolate_edges, toLeft_disjSum, card_disjSum, card_empty, add_zero]
    simp only [z, liftWeights, toLeft_disjSum, toRight_disjSum, ite_true, hw]

theorem isolate_fractional_lift {y : Finset V → ℝ} (hy : ResPack y) :
    ∃ z : Finset (V ⊕ X) → ℝ, ResPack z ∧
      ∑ Q, z Q * (w (withIsolates B) Q : ℝ) = ∑ S, y S * (w B S : ℝ) := by
  obtain ⟨z, hz, _, hscore⟩ := isolate_fractional_lift_with_support (X := X) B hy
  exact ⟨z, hz, hscore⟩

end GapExtremal.R434
