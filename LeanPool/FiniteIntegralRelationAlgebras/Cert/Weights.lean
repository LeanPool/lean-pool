/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

-- Modified for Lean Pool, including adaptations to its Lean module layout.

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import LeanPool.FiniteIntegralRelationAlgebras.Cert.Popcount

/-!
# Weighted position classes and counting independent bits

Purely arithmetic tools for certificates that count with multiplicities:

* a list `E = [E₀, E₁, …]` of bit masks represents the weight function
  `β ↦ ∑ⱼ 2^j · [β ∈ Eⱼ]` (`RACert.wsum`); `RACert.stepE` multiplies the weight of every position
  by `1` (forced), `2` (free) or `0`, and `RACert.wtot` is the total weight;
* `RACert.cnt Q i` counts the `ζ < 2^i` whose bits are all allowed by `Q`, a product of
  per-bit counts (`cnt_succ`);
* `RACert.sum_range_two_pow_add` regroups a sum over `b + m` bits into low and high bits.
-/

@[expose] public section

namespace RACert

/-! ### Weighted position classes -/

/-- One elimination step: with `F` the positions where the variable is forced and `R` those where
it is free, `E'ⱼ = (Eⱼ ∧ F) ∨ (Eⱼ₋₁ ∧ R)`. `prev` is `Eⱼ₋₁` (`0` at the start). -/
noncomputable def stepE (F R : ℕ) (E : List ℕ) : ℕ → List ℕ :=
  List.rec (motive := fun _ => ℕ → List ℕ) (fun prev => [Nat.land prev R])
    (fun e _ ih prev => Nat.lor (Nat.land e F) (Nat.land prev R) :: ih e) E

/-- The weight of position `β`. -/
def wsum (β : ℕ) : List ℕ → ℕ
  | [] => 0
  | e :: es => (e.testBit β).toNat + 2 * wsum β es

theorem stepE_nil (F R prev : ℕ) : stepE F R [] prev = [Nat.land prev R] := rfl

theorem stepE_cons (F R e : ℕ) (es : List ℕ) (prev : ℕ) :
    stepE F R (e :: es) prev = Nat.lor (Nat.land e F) (Nat.land prev R) :: stepE F R es e := rfl

theorem wsum_nil (β : ℕ) : wsum β [] = 0 := rfl

theorem wsum_cons (β e : ℕ) (es : List ℕ) :
    wsum β (e :: es) = (e.testBit β).toNat + 2 * wsum β es := rfl

theorem wsum_stepE {F R β : ℕ} (h : ¬ (F.testBit β = true ∧ R.testBit β = true)) (E : List ℕ)
    (prev : ℕ) :
    wsum β (stepE F R E prev) =
      (F.testBit β).toNat * wsum β E +
        (R.testBit β).toNat * ((prev.testBit β).toNat + 2 * wsum β E) := by
  induction E generalizing prev with
  | nil =>
    rw [stepE_nil, wsum_cons, wsum_nil, testBit_land]
    cases F.testBit β <;> cases R.testBit β <;> cases prev.testBit β <;> rfl
  | cons e es ih =>
    rw [stepE_cons, wsum_cons, ih, wsum_cons, testBit_lor, testBit_land, testBit_land]
    generalize wsum β es = w
    revert h
    cases F.testBit β <;> cases R.testBit β <;> cases e.testBit β <;> cases prev.testBit β <;>
      intro h <;> simp at h ⊢

/-- In particular, starting with `prev = 0`, the weight is multiplied by `[F] + 2 [R]`. -/
theorem wsum_stepE_zero {F R β : ℕ} (h : ¬ (F.testBit β = true ∧ R.testBit β = true))
    (E : List ℕ) :
    wsum β (stepE F R E 0) = ((F.testBit β).toNat + 2 * (R.testBit β).toNat) * wsum β E := by
  rw [wsum_stepE h, Nat.zero_testBit, Bool.toNat_false, Nat.zero_add, Nat.add_mul,
    Nat.mul_left_comm, Nat.mul_assoc]

theorem stepE_lt {N F R : ℕ} {E : List ℕ} {prev : ℕ} (hE : ∀ e ∈ E, e < 2 ^ N)
    (hprev : prev < 2 ^ N) : ∀ e ∈ stepE F R E prev, e < 2 ^ N := by
  induction E generalizing prev with
  | nil =>
    intro e he
    rw [stepE_nil, List.mem_singleton] at he
    rw [he]
    exact land_lt_left hprev
  | cons a as ih =>
    have ha : a < 2 ^ N := hE a List.mem_cons_self
    intro e he
    rw [stepE_cons, List.mem_cons] at he
    rcases he with he | he
    · rw [he]
      exact lor_lt (land_lt_left ha) (land_lt_left hprev)
    · exact ih (fun x hx => hE x (List.mem_cons_of_mem _ hx)) ha e he

/-- The total weight `∑ⱼ 2^j · popcount Eⱼ`, with few big-number operations. -/
noncomputable def wtot (b : ℕ) (E : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun e _ ih => Nat.add (popcountF b e) (Nat.mul 2 ih)) E

theorem wtot_nil (b : ℕ) : wtot b [] = 0 := rfl

theorem wtot_cons (b e : ℕ) (es : List ℕ) :
    wtot b (e :: es) = popcountF b e + 2 * wtot b es := rfl

theorem wtot_eq {b : ℕ} {E : List ℕ} (hE : ∀ e ∈ E, e < 2 ^ 2 ^ b) :
    wtot b E = ∑ β ∈ Finset.range (2 ^ b), wsum β E := by
  induction E with
  | nil => simp [wtot_nil, wsum_nil]
  | cons e es ih =>
    rw [wtot_cons, ih (fun x hx => hE x (List.mem_cons_of_mem _ hx)),
      popcountF_eq_card_filter (hE e List.mem_cons_self), Finset.card_filter, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [wsum_cons]
    cases e.testBit β <;> rfl

/-! ### Counting assignments of independent bits -/

/-- The number of `ζ < 2^i` all of whose bits `j < i` are allowed by `Q j`. -/
def cnt (Q : ℕ → Bool → Bool) (i : ℕ) : ℕ :=
  ∑ ζ ∈ Finset.range (2 ^ i), if ∀ j < i, Q j (ζ.testBit j) = true then 1 else 0

theorem cnt_zero (Q : ℕ → Bool → Bool) : cnt Q 0 = 1 := by
  simp [cnt]

theorem cnt_succ (Q : ℕ → Bool → Bool) (i : ℕ) :
    cnt Q (i + 1) = cnt Q i * ((Q i false).toNat + (Q i true).toNat) := by
  have hpow : 2 ^ (i + 1) = 2 ^ i + 2 ^ i := by rw [pow_succ, Nat.mul_two]
  rw [cnt, hpow, Finset.sum_range_add, cnt, Nat.mul_add, Finset.sum_mul, Finset.sum_mul]
  congr 1
  · refine Finset.sum_congr rfl fun ζ hζ => ?_
    rw [Finset.mem_range] at hζ
    simp only [Nat.forall_lt_succ_right, Nat.testBit_lt_two_pow hζ]
    by_cases h : ∀ j < i, Q j (ζ.testBit j) = true <;> cases Q i false <;> simp [h]
  · refine Finset.sum_congr rfl fun ζ hζ => ?_
    rw [Finset.mem_range] at hζ
    have h1 : ∀ j < i, (2 ^ i + ζ).testBit j = ζ.testBit j := fun j hj =>
      Nat.testBit_two_pow_add_gt hj ζ
    have h2 : (2 ^ i + ζ).testBit i = true := by
      rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hζ]; rfl
    have h3 : (∀ j < i, Q j ((2 ^ i + ζ).testBit j) = true) ↔
        ∀ j < i, Q j (ζ.testBit j) = true :=
      forall₂_congr fun j hj => by rw [h1 j hj]
    simp only [Nat.forall_lt_succ_right, h2, h3]
    by_cases h : ∀ j < i, Q j (ζ.testBit j) = true <;> cases Q i true <;> simp [h]

/-! ### Regrouping a sum over `b + m` bits -/

theorem sum_range_mul (f : ℕ → ℕ) (n m : ℕ) :
    ∑ β ∈ Finset.range (n * m), f β =
      ∑ ζ ∈ Finset.range m, ∑ β' ∈ Finset.range n, f (β' + n * ζ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, Finset.sum_range_succ, ih]
    congr 1
    exact Finset.sum_congr rfl fun β' _ => by rw [Nat.add_comm]

theorem sum_range_two_pow_add (f : ℕ → ℕ) (b m : ℕ) :
    ∑ β ∈ Finset.range (2 ^ (b + m)), f β =
      ∑ ζ ∈ Finset.range (2 ^ m), ∑ β' ∈ Finset.range (2 ^ b), f (β' + 2 ^ b * ζ) := by
  rw [pow_add, sum_range_mul]

theorem testBit_add_two_pow_mul {b β' ζ : ℕ} (h : β' < 2 ^ b) (j : ℕ) :
    (β' + 2 ^ b * ζ).testBit j = if j < b then β'.testBit j else ζ.testBit (j - b) := by
  rw [Nat.add_comm, Nat.testBit_two_pow_mul_add _ h]

end RACert
