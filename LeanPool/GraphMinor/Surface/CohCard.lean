/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.CohExist

/-!
# The number of classes of a model surface

`card_kCl` counts the classes of a space presented by the word `ew a b c`. With coefficients in
`ZMod 2` their number
is `2 ^ (2 * a + b)`. With coefficients in `ZMod 3` it is `3 ^ (2 * a)` if `b = 0`, and `3 ^ (2 * a
+ b - 1)` otherwise.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric

universe u

variable {a b c : ℕ} {Y : Type u} [TopologicalSpace Y] {f : ℕ × ℂ → Y} {A : Type} [AddCommGroup A]

/-- Values on the labels of the handles and of the cross-caps. -/
abbrev LamT (a b : ℕ) (A : Type) [AddCommGroup A] : Type :=
  (Fin (2 * a) → A) × {μ : Fin b → A // (2 : ℕ) • ∑ i, μ i = 0}

theorem card_kCl [T2Space Y] [Finite A] (hf : Presents (sW (ew a b c)) f) :
    Nat.card (KCl Y A) = Nat.card (LamT a b A) := by
  classical
  have hex : ∀ φ : KSet Y A, ∃ g, IsPrim φ.1 (pmap f) g := fun φ => exists_prim φ.2.1 (pmap_cont hf)
  choose G hG using hex
  have hsum : ∀ φ : KSet Y A, (2 : ℕ) • ∑ i : Fin b, lval a b c (G φ) (2 * a + i) = 0 := by
    intro φ
    have h1 := Sm_prim hf (hG φ)
    rw [Sm_total] at h1
    have h2 : ∑ l ∈ Finset.range c, lval a b c (G φ) (2 * a + b + 2 * l + 1) = 0 := by
      refine Finset.sum_eq_zero fun l hl => ?_
      have hl' := Finset.mem_range.mp hl
      have e : lab a b c (4 * a + 2 * b + 3 * l + 1) = 2 * a + b + 2 * l + 1 := lab_t hl' (by omega)
      rw [← e, ← volt_eq hf (hG φ) (by omega), volt_free hf φ.2.2 (hG φ) hl']
    rw [h2, add_zero, Finset.sum_range] at h1
    exact h1
  let T : KSet Y A → LamT a b A := fun φ =>
    (fun i => lval a b c (G φ) i, ⟨fun i => lval a b c (G φ) (2 * a + i), hsum φ⟩)
  have hT : ∀ φ φ' : KSet Y A, (kSetoid Y A).r φ φ' → T φ = T φ' := by
    intro φ φ' h
    refine Prod.ext (funext fun i => ?_) (Subtype.ext (funext fun i => ?_))
    · exact lval_rel hf (hG φ) (hG φ') h (by omega)
    · exact lval_rel hf (hG φ) (hG φ') h (by omega)
  let T' : KCl Y A → LamT a b A := Quotient.lift T hT
  refine Nat.card_eq_of_bijective T' ⟨?_, ?_⟩
  · intro x y he
    obtain ⟨φ, rfl⟩ := Quotient.exists_rep x
    obtain ⟨φ', rfl⟩ := Quotient.exists_rep y
    have he' : T φ = T φ' := he
    refine Quotient.sound (cohRel_of_lval hf φ.2.1 φ'.2.1 φ.2.2 φ'.2.2 (hG φ) (hG φ') fun k hk
      => ?_)
    by_cases h : k < 2 * a
    · exact congrFun (congrArg Prod.fst he') ⟨k, h⟩
    · have h1 := congrFun (congrArg (fun x : LamT a b A => x.2.1) he') ⟨k - 2 * a, by omega⟩
      have e : 2 * a + (k - 2 * a) = k := by omega
      simp only [T, e] at h1
      exact h1
  · rintro ⟨l, μ, hμ⟩
    let V : ℕ → A := fun k => if h : k < 2 * a then l ⟨k, h⟩ else if h' : k - 2 * a < b then μ ⟨k -
      2 * a, h'⟩ else 0
    have hV1 : ∀ i : Fin (2 * a), V i = l i := fun i => by simp [V]
    have hV2 : ∀ i : Fin b, V (2 * a + i) = μ i := fun i => by simp [V]
    have hV3 : ∀ i, V (2 * a + b + 2 * i + 1) = 0 := fun i => by
      have h1 : ¬ 2 * a + b + 2 * i + 1 < 2 * a := by omega
      have h2 : ¬ 2 * a + b + 2 * i + 1 - 2 * a < b := by omega
      simp only [V, h1, h2, dite_false]
    have hS : Sm a b c V (4 * a + 2 * b + 3 * c + 2) = 0 := by
      rw [Sm_total, Finset.sum_eq_zero (s := Finset.range c) fun i _ => hV3 i, add_zero,
        Finset.sum_range]
      simp only [hV2]
      exact hμ
    obtain ⟨φ, g, h1, h2, h3, h4⟩ := exists_class hf V hS fun i _ => hV3 i
    refine ⟨Quotient.mk _ ⟨φ, h1, h2⟩, ?_⟩
    have h5 : ∀ k < 2 * a + b, lval a b c (G ⟨φ, h1, h2⟩) k = V k := fun k hk => by
      rw [lval_rel hf (hG ⟨φ, h1, h2⟩) h3 (.refl φ) hk, h4 k (by omega)]
    change T ⟨φ, h1, h2⟩ = _
    refine Prod.ext (funext fun i => ?_) (Subtype.ext (funext fun i => ?_))
    · change lval a b c _ i = l i
      rw [h5 _ (by omega), hV1]
    · change lval a b c _ (2 * a + i) = μ i
      rw [h5 _ (by omega), hV2]

theorem card_fin_fun (n p : ℕ) [NeZero p] : Nat.card (Fin n → ZMod p) = p ^ n := by
  simp [Nat.card_eq_fintype_card, ZMod.card]

theorem card_lam_two (a b : ℕ) : Nat.card (LamT a b (ZMod 2)) = 2 ^ (2 * a + b) := by
  have hz : ∀ x : ZMod 2, (2 : ℕ) • x = 0 := by decide
  let e : {μ : Fin b → ZMod 2 // (2 : ℕ) • ∑ i, μ i = 0} ≃ (Fin b → ZMod 2) :=
    ⟨fun μ => μ.1, fun μ => ⟨μ, hz _⟩, fun _ => rfl, fun _ => rfl⟩
  rw [Nat.card_prod, Nat.card_congr e, card_fin_fun, card_fin_fun, pow_add]

theorem card_lam_three_zero (a : ℕ) : Nat.card (LamT a 0 (ZMod 3)) = 3 ^ (2 * a) := by
  have : Nat.card {μ : Fin 0 → ZMod 3 // (2 : ℕ) • ∑ i, μ i = 0} = 1 := by
    refine Nat.card_eq_one_iff_unique.mpr ⟨⟨fun x y => Subtype.ext (funext fun i => i.elim0)⟩,
      ⟨⟨fun i => i.elim0, by simp⟩⟩⟩
  rw [Nat.card_prod, this, card_fin_fun, mul_one]

theorem card_lam_three_succ (a b : ℕ) : Nat.card (LamT a (b + 1) (ZMod 3)) = 3 ^ (2 * a + b) := by
  have hz : ∀ x : ZMod 3, (2 : ℕ) • x = 0 → x = 0 := by decide
  let e : {μ : Fin (b + 1) → ZMod 3 // (2 : ℕ) • ∑ i, μ i = 0} ≃ (Fin b → ZMod 3) :=
    { toFun := fun μ => fun i => μ.1 i.succ
      invFun := fun ν => ⟨Fin.cons (-∑ i, ν i) ν, by simp [Fin.sum_univ_succ]⟩
      left_inv := fun μ => by
        apply Subtype.ext
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · have h1 := hz _ μ.2
          rw [Fin.sum_univ_succ] at h1
          simp only [Fin.cons_zero]
          exact (eq_neg_of_add_eq_zero_left h1).symm ▸ rfl
        · simp
      right_inv := fun ν => by
        funext i
        simp }
  rw [Nat.card_prod, Nat.card_congr e, card_fin_fun, card_fin_fun, pow_add]

end GraphMinor.Surface
