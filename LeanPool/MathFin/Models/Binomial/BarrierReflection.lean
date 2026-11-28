/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Binomial.PathReflection
public import Mathlib.Basic.Real.Basic
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Barrier-option counting via the reflection principle

`Models/Binomial/PathReflection.lean` builds André's reflection bijection
`reflectionPrincipleEquivBelow : {ω // hit a ∧ end = b} ≃ {ω // end = 2a − b}` (for
`0 < a`, `b ≤ a`) and notes that *"the `Fintype.card` identity is their immediate corollary
and is not separately stated here."* This file states it — the counting backbone of
binomial barrier-option pricing — and derives the **maximal-distribution identity**, the
running-maximum law that prices the knock-in.

## Main definitions

* `reflectHitLtGt`: the equivalence between paths that hit `a` and end below `a`, and paths that
  hit `a` and end above `a`.
* `hitAboveEquiv`: for `0 < a`, paths that hit `a` and end above `a` are in bijection with paths
  ending above `a`.
* `hitAtEquiv`: for `0 < a`, paths that hit `a` and end at `a` are in bijection with paths
  ending at `a`.

## Main results

* `reflection_principle_card` — for `0 < a`, `b ≤ a`, `#{hit a, end b} = #{end 2a−b}` (the
  counting form of the bijection), and its finance reading `barrierDigital_knockIn_reflection`:
  under the symmetric tree, a cash-or-nothing up-and-in digital at terminal `b ≤ a` equals the
  vanilla digital at the reflected level.
* `binomial_maximal_distribution_card` — the running-maximum distribution
  `#{ω : max ≥ a} = 2·#{end > a} + #{end = a}` (`a > 0`), the discrete
  `P(max ≥ a) = 2P(S_n > a) + P(S_n = a)` — obtained by trichotomising the hit-set and
  reflecting the below-barrier endpoints onto the above-barrier ones.

## References

* [André (1887)][Andre1887]

## Tags

barrier option, reflection principle, running maximum, knock-in, André reflection, lattice paths,
MSC 91G20, MSC 60G50, JEL G13
-/

@[expose] public section

namespace MathFin

open Finset

variable {n : ℕ}

/-- **Counting form of André's reflection principle.** For a barrier `0 < a` and terminal
`b ≤ a`, the number of `n`-step ±1 paths that touch `a` and finish at `b` equals the number
that finish at `2a − b`. Immediate from `reflectionPrincipleEquivBelow`. -/
theorem reflection_principle_card (a b : ℤ) (ha : 0 < a) (hb : b ≤ a) :
    Nat.card {ω : Fin n → Bool // HitsLevel a ω ∧ walkPos ω n = b}
      = Nat.card {ω : Fin n → Bool // walkPos ω n = 2 * a - b} :=
  Nat.card_congr (reflectionPrincipleEquivBelow a b ha hb)

/-- **Barrier cash-or-nothing knock-in = vanilla digital at the reflected level** (symmetric
tree). Under the symmetric `q = 1/2` binomial measure (each path weight `2⁻ⁿ`), the up-and-in
digital paying `1` on `{touch a, finish b}` (with `b ≤ a`) has the same price as the vanilla
digital paying `1` on `{finish 2a − b}`. -/
theorem barrierDigital_knockIn_reflection (a b : ℤ) (ha : 0 < a) (hb : b ≤ a) :
    (Nat.card {ω : Fin n → Bool // HitsLevel a ω ∧ walkPos ω n = b} : ℝ) / 2 ^ n
      = (Nat.card {ω : Fin n → Bool // walkPos ω n = 2 * a - b} : ℝ) / 2 ^ n := by
  rw [reflection_principle_card a b ha hb]

/-- Reflection swaps below-barrier and above-barrier endpoints on the hit-set:
`{hit a, end < a} ≃ {hit a, end > a}` via reflection at the first hit. -/
noncomputable def reflectHitLtGt (a : ℤ) :
    {ω : Fin n → Bool // HitsLevel a ω ∧ walkPos ω n < a} ≃
    {ω : Fin n → Bool // HitsLevel a ω ∧ a < walkPos ω n} where
  toFun ω := ⟨reflectAtFirstHit a ω.1, by
    refine ⟨?_, ?_⟩
    · rw [reflectAtFirstHit, dite_eq_left ω.2.1]
      exact HitsLevel.reflectAfter_firstHit ω.1 a ω.2.1
    · have h := walkPos_reflectAtFirstHit_endpoint ω.1 a (walkPos ω.1 n) ω.2.1 rfl
      have := ω.2.2; rw [h]; linarith⟩
  invFun ω := ⟨reflectAtFirstHit a ω.1, by
    refine ⟨?_, ?_⟩
    · rw [reflectAtFirstHit, dite_eq_left ω.2.1]
      exact HitsLevel.reflectAfter_firstHit ω.1 a ω.2.1
    · have h := walkPos_reflectAtFirstHit_endpoint ω.1 a (walkPos ω.1 n) ω.2.1 rfl
      have := ω.2.2; rw [h]; linarith⟩
  left_inv ω := Subtype.ext (reflectAtFirstHit_involutive a ω.1)
  right_inv ω := Subtype.ext (reflectAtFirstHit_involutive a ω.1)

/-- Above a positive barrier the hit condition is automatic (discrete IVT):
`{hit a, end > a} ≃ {end > a}`. -/
noncomputable def hitAboveEquiv (a : ℤ) (ha : 0 < a) :
    {ω : Fin n → Bool // HitsLevel a ω ∧ a < walkPos ω n} ≃
    {ω : Fin n → Bool // a < walkPos ω n} where
  toFun ω := ⟨ω.1, ω.2.2⟩
  invFun ω := ⟨ω.1, HitsLevel_of_endpoint_gt (le_of_lt ha) ω.2, ω.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- At a positive barrier the hit condition is automatic: `{hit a, end = a} ≃ {end = a}`. -/
noncomputable def hitAtEquiv (a : ℤ) (ha : 0 < a) :
    {ω : Fin n → Bool // HitsLevel a ω ∧ walkPos ω n = a} ≃
    {ω : Fin n → Bool // walkPos ω n = a} where
  toFun ω := ⟨ω.1, ω.2.2⟩
  invFun ω := ⟨ω.1, HitsLevel_of_walkPos_endpoint_ge ω.1 a (le_of_lt ha) ω.2.ge, ω.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The binomial maximal-distribution identity** (running-maximum law). For a barrier
`0 < a`, the number of `n`-step ±1 paths whose running maximum reaches `a` (i.e. that hit `a`)
is `2·#{end > a} + #{end = a}` — the discrete `P(max ≥ a) = 2·P(S_n > a) + P(S_n = a)`.

Proof: trichotomise the hit-set by the terminal position. Paths ending `> a` or `= a` hit `a`
automatically (`hitAboveEquiv`, `hitAtEquiv`, discrete IVT), and reflection at the first hit
(`reflectHitLtGt`) bijects the below-barrier endpoints onto the above-barrier ones, so
`#{hit a, end < a} = #{end > a}`. -/
theorem binomial_maximal_distribution_card (a : ℤ) (ha : 0 < a) :
    Nat.card {ω : Fin n → Bool // HitsLevel a ω}
      = 2 * Nat.card {ω : Fin n → Bool // a < walkPos ω n}
        + Nat.card {ω : Fin n → Bool // walkPos ω n = a} := by
  classical
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  -- The three hit-set slices, with the ≥-barrier slices' hit condition dissolved by IVT.
  have e1 : (univ.filter (fun ω : Fin n → Bool ↦ HitsLevel a ω ∧ a < walkPos ω n)).card
      = (univ.filter (fun ω : Fin n → Bool ↦ a < walkPos ω n)).card := by
    rw [← Fintype.card_subtype, ← Fintype.card_subtype]; exact Fintype.card_congr
        (hitAboveEquiv a ha)
  have e2 : (univ.filter (fun ω : Fin n → Bool ↦ HitsLevel a ω ∧ walkPos ω n = a)).card
      = (univ.filter (fun ω : Fin n → Bool ↦ walkPos ω n = a)).card := by
    rw [← Fintype.card_subtype, ← Fintype.card_subtype]; exact Fintype.card_congr (hitAtEquiv a ha)
  have e3 : (univ.filter (fun ω : Fin n → Bool ↦ HitsLevel a ω ∧ walkPos ω n < a)).card
      = (univ.filter (fun ω : Fin n → Bool ↦ HitsLevel a ω ∧ a < walkPos ω n)).card := by
    rw [← Fintype.card_subtype, ← Fintype.card_subtype]; exact Fintype.card_congr (reflectHitLtGt a)
  -- Trichotomy partition of the hit-set by the terminal position.
  have hunion : (univ.filter (fun ω : Fin n → Bool ↦ HitsLevel a ω))
      = (univ.filter (fun ω ↦ HitsLevel a ω ∧ a < walkPos ω n))
        ∪ (univ.filter (fun ω ↦ HitsLevel a ω ∧ walkPos ω n = a))
        ∪ (univ.filter (fun ω ↦ HitsLevel a ω ∧ walkPos ω n < a)) := by
    ext ω
    simp only [mem_filter, mem_union, mem_univ, true_and]
    constructor
    · intro h
      rcases lt_trichotomy (walkPos ω n) a with h1 | h1 | h1
      · exact Or.inr ⟨h, h1⟩
      · exact Or.inl (Or.inr ⟨h, h1⟩)
      · exact Or.inl (Or.inl ⟨h, h1⟩)
    · rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
  have hd12 : Disjoint (univ.filter (fun ω : Fin n → Bool ↦ HitsLevel a ω ∧ a < walkPos ω n))
      (univ.filter (fun ω ↦ HitsLevel a ω ∧ walkPos ω n = a)) :=
    disjoint_filter.2 (fun ω _ hp hq ↦ by omega)
  have hd3 : Disjoint ((univ.filter (fun ω : Fin n → Bool ↦ HitsLevel a ω ∧ a < walkPos ω n))
      ∪ (univ.filter (fun ω ↦ HitsLevel a ω ∧ walkPos ω n = a)))
      (univ.filter (fun ω ↦ HitsLevel a ω ∧ walkPos ω n < a)) := by
    rw [disjoint_union_left]
    exact ⟨disjoint_filter.2 (fun ω _ hp hq ↦ by omega),
      disjoint_filter.2 (fun ω _ hp hq ↦ by omega)⟩
  rw [hunion, card_union_of_disjoint hd3, card_union_of_disjoint hd12, e3]
  simp only [e1, e2]
  ring

end MathFin
