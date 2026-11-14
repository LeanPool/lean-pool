/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.GroupTheory.Perm.DomMulAct
public import Mathlib.GroupTheory.GroupAction.Quotient

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

@[expose] public section

namespace MatrixMultiplicationAllFields



namespace MatrixMultiplication.Foundation

open scoped BigOperators

variable {A I J : Type*} [Fintype A] [DecidableEq A] [Fintype I] [Fintype J]
  [DecidableEq I]

/-- Number of occurrences of a letter in a finitely indexed word. -/
def wordPopulation (w : I → A) (a : A) : ℕ := Fintype.card {i // w i = a}

omit [DecidableEq I] in
theorem wordPopulation_sum (w : I → A) :
    ∑ a, wordPopulation w a = Fintype.card I := by
  simpa [wordPopulation] using Fintype.card_congr (Equiv.sigmaFiberEquiv w)

omit [Fintype A] [DecidableEq I] in
theorem wordPopulation_reindex (w : I → A) (e : J ≃ I) (a : A) :
    wordPopulation (w ∘ e) a = wordPopulation w a :=
  Fintype.card_congr (Equiv.subtypeEquiv e fun _ => Iff.rfl)

/-- Words of the prescribed total length with exactly the specified letter populations. -/
abbrev ExactWords (counts : A → ℕ) :=
  {w : Fin (∑ a, counts a) → A // ∀ a, wordPopulation w a = counts a}

theorem wordPopulation_sigma_fst (counts : A → ℕ) (a : A) :
    wordPopulation (fun i : Σ b, Fin (counts b) => i.1) a = counts a := by
  let e : {i : Σ b, Fin (counts b) // i.1 = a} ≃ Fin (counts a) :=
    { toFun := fun i => i.property ▸ i.val.2
      invFun := fun i => ⟨⟨a, i⟩, rfl⟩
      left_inv := by
        rintro ⟨⟨b, i⟩, h⟩
        cases h
        rfl
      right_inv := by intro i; rfl }
  exact (Fintype.card_congr e).trans (Fintype.card_fin _)

theorem exactWords_nonempty (counts : A → ℕ) : Nonempty (ExactWords counts) := by
  classical
  let e : Fin (∑ a, counts a) ≃ (Σ a, Fin (counts a)) :=
    Fintype.equivOfCardEq (by simp)
  refine ⟨⟨(fun i : Σ a, Fin (counts a) => i.1) ∘ e, ?_⟩⟩
  intro a
  rw [wordPopulation_reindex, wordPopulation_sigma_fst]

omit [Fintype A] [DecidableEq I] in
theorem samePopulation_iff_permutation (w v : I → A) :
    (∀ a, wordPopulation v a = wordPopulation w a) ↔
      ∃ e : Equiv.Perm I, w ∘ e = v := by
  classical
  constructor
  · intro h
    let es : ∀ a, {i // v i = a} ≃ {i // w i = a} :=
      fun a => Fintype.equivOfCardEq (h a)
    refine ⟨Equiv.ofFiberEquiv es, ?_⟩
    funext i
    exact Equiv.ofFiberEquiv_map es i
  · rintro ⟨e, rfl⟩ a
    exact wordPopulation_reindex w e a

theorem samePopulation_card_mul (w : I → A) :
    Fintype.card {v : I → A // ∀ a, wordPopulation v a = wordPopulation w a} *
      (∏ a, (wordPopulation w a).factorial) = (Fintype.card I).factorial := by
  classical
  let G := DomMulAct (Equiv.Perm I)
  let : Fintype G := Fintype.ofEquiv (Equiv.Perm I) DomMulAct.mk
  let eOrbit : {v : I → A // ∀ a, wordPopulation v a = wordPopulation w a} ≃
      MulAction.orbit G w :=
    Equiv.subtypeEquivRight fun v => by
      rw [samePopulation_iff_permutation, MulAction.mem_orbit_iff]
      constructor
      · rintro ⟨e, he⟩
        exact ⟨DomMulAct.mk e, he⟩
      · rintro ⟨g, hg⟩
        exact ⟨DomMulAct.mk.symm g, hg⟩
  let eStab : MulAction.stabilizer G w ≃
      {e : Equiv.Perm I // w ∘ e = w} :=
    Equiv.subtypeEquiv DomMulAct.mk.symm fun _ => DomMulAct.mem_stabilizer_iff
  have hstab : Fintype.card (MulAction.stabilizer G w) =
      ∏ a, (wordPopulation w a).factorial := by
    rw [Fintype.card_congr eStab]
    exact DomMulAct.stabilizer_card w
  have hgroup : Fintype.card G = (Fintype.card I).factorial :=
    (Fintype.card_congr DomMulAct.mk.symm).trans Fintype.card_perm
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group G w
  rw [← Fintype.card_congr eOrbit, hstab, hgroup] at h
  exact h

theorem exactWords_card (counts : A → ℕ) :
    Fintype.card (ExactWords counts) = Nat.multinomial Finset.univ counts := by
  classical
  obtain ⟨w⟩ := exactWords_nonempty counts
  let e : ExactWords counts ≃
      {v : Fin (∑ a, counts a) → A // ∀ a,
        wordPopulation v a = wordPopulation w.val a} :=
    Equiv.subtypeEquivRight fun v => by simp only [w.property]
  have h := samePopulation_card_mul w.val
  rw [← Fintype.card_congr e] at h
  simp only [w.property, Fintype.card_fin] at h
  exact Nat.eq_div_of_mul_eq_left
    (ne_of_gt (Nat.prod_factorial_pos Finset.univ counts)) h

theorem exactWords_card_pos (counts : A → ℕ) : 0 < Fintype.card (ExactWords counts) := by
  rw [exactWords_card]
  exact Nat.multinomial_pos Finset.univ counts

theorem exactWords_card_le (counts : A → ℕ) :
    Fintype.card (ExactWords counts) ≤ (Fintype.card A) ^ (∑ a, counts a) := by
  classical
  calc
    Fintype.card (ExactWords counts) ≤
        Fintype.card (Fin (∑ a, counts a) → A) :=
      Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    _ = _ := by simp

end MatrixMultiplication.Foundation

end MatrixMultiplicationAllFields
