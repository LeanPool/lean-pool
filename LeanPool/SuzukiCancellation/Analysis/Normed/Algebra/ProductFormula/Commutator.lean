/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.Analysis.Normed.Algebra.Commutator
public import LeanPool.SuzukiCancellation.Data.Nat.Choose.Multinomial

/-!
# Commutator scaling quantities for product-formula errors

The quantities `αComm` and `αCommConj` are the nested-commutator norm sums of
arXiv:1912.08854. Their original multiplicities, multinomial weights, and ordering
are preserved. Algebraic commutator identities and general norm estimates are
provided by the shared modules imported above.

## Main definitions and results

* `TrotterError.αComm` sums the norms of nested commutators over all tuples of summand indices.
* `TrotterError.αCommConj` sums multinomial-weighted norms of iterated adjoint actions.
* `TrotterError.αCommConj_smul_fun_le` shows that scaling each conjugating generator by a real
  scalar of absolute value at most one cannot increase this sum.
-/

@[expose] public section

namespace TrotterError

open Finset LieAlgebra
open scoped algebraMap

attribute [local instance] LieRing.ofAssociativeRing

/-- The paper's `α~_comm`: the sum of the norms of all nested commutators
`[H_{γ_{p+1}}, ⋯ [H_{γ_2}, H_{γ_1}]]` over all tuples `γ : Fin (p + 1) → Fin Γ`
(repeated indices allowed). -/
noncomputable def αComm {𝔸 : Type*} [NormedRing 𝔸] {Γ : ℕ} (p : ℕ)
    (H : Fin Γ → 𝔸) : ℝ :=
  ∑ γ : Fin (p + 1) → Fin Γ, ‖nestedComm (H ∘ γ)‖

/-- The paper's `α_comm(A_s, …, A_1, B)`: the multinomial-weighted sum
`Σ_{q₁+⋯+q_s = p} (p choose q₁⋯q_s) ‖ad_{A_s}^{q_s} ⋯ ad_{A_1}^{q_1}(B)‖`. -/
noncomputable def αCommConj {𝔸 : Type*} [NormedRing 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin s → 𝔸)
    (B : 𝔸) (p : ℕ) : ℝ :=
  ∑ q ∈ Finset.finAntidiagonal s p,
    (Nat.multinomial (Finset.univ : Finset (Fin s)) q : ℝ) * ‖adSequence A q B‖

/-- `αComm p H` is a sum of norms, hence nonnegative. -/
theorem αComm_nonneg {𝔸 : Type*} [NormedRing 𝔸] {Γ : ℕ} (p : ℕ) (H : Fin Γ → 𝔸) :
    0 ≤ αComm p H := Finset.sum_nonneg (fun _ _ => norm_nonneg _)

/-- `αCommConj (fun i => c i • A i) B p ≤ αCommConj A B p` for `|c i| ≤ 1`. -/
lemma αCommConj_smul_fun_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] {s : ℕ}
    (c : Fin s → ℝ) (A : Fin s → 𝔸) (hc : ∀ i, |c i| ≤ 1) (B : 𝔸) (p : ℕ) :
    αCommConj (fun i => c i • A i) B p ≤ αCommConj A B p := by
  rw [αCommConj, αCommConj]
  apply sum_le_sum
  intro q hq
  rw [adSequence_smul_fun c A q B, norm_smul, Real.norm_eq_abs]
  have hprod : |∏ i : Fin s, (c i) ^ q i| ≤ 1 := by
    rw [abs_prod]
    exact prod_le_one₀ (fun i _ => abs_nonneg _) (fun i _ => by
      rw [abs_pow]
      exact pow_le_one₀ (abs_nonneg _) (hc i))
  exact mul_le_mul_of_nonneg_left
    (mul_le_of_le_one_left (norm_nonneg _) hprod) (Nat.cast_nonneg _)

/-- `αCommConj A (c • B) p ≤ αCommConj A B p` for `|c| ≤ 1`. -/
lemma αCommConj_smul_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] {s : ℕ}
    (A : Fin s → 𝔸) (c : ℝ) (hc : |c| ≤ 1) (B : 𝔸) (p : ℕ) :
    αCommConj A (c • B) p ≤ αCommConj A B p := by
  rw [αCommConj, αCommConj]
  apply sum_le_sum
  intro q hq
  rw [adSequence_smul, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left
    (mul_le_of_le_one_left (norm_nonneg _) hc) (Nat.cast_nonneg _)

/-- `αCommConj` is invariant under `Fin.cast` reindexing. -/
lemma αCommConj_cast {𝔸 : Type*} [NormedRing 𝔸] [Algebra ℝ 𝔸] {s t : ℕ} (h : s = t) (A : Fin s → 𝔸)
    (B : 𝔸) (p : ℕ) :
    αCommConj (fun i : Fin t => A (Fin.cast h.symm i)) B p = αCommConj A B p := by
  subst h
  simp [αCommConj]

/-- `αCommConj A (∑ γ, H γ) p ≤ ∑ γ, αCommConj A (H γ) p`. -/
lemma αCommConj_sum_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] {s : ℕ}
    (A : Fin s → 𝔸) {ι : Type*} [Fintype ι] (H : ι → 𝔸) (p : ℕ) :
    αCommConj A (∑ γ : ι, H γ) p ≤ ∑ γ : ι, αCommConj A (H γ) p := by
  rw [αCommConj]
  calc
    (∑ q ∈ finAntidiagonal s p,
        (Nat.multinomial (univ : Finset (Fin s)) q : ℝ) *
          ‖adSequence A q (∑ γ : ι, H γ)‖)
        = ∑ q ∈ finAntidiagonal s p,
            (Nat.multinomial (univ : Finset (Fin s)) q : ℝ) *
              ‖∑ γ : ι, adSequence A q (H γ)‖ := by
              apply sum_congr rfl
              intro q hq
              rw [adSequence_sum A q H]
    _ ≤ ∑ q ∈ finAntidiagonal s p,
            (Nat.multinomial (univ : Finset (Fin s)) q : ℝ) *
              (∑ γ : ι, ‖adSequence A q (H γ)‖) := by
              apply sum_le_sum
              intro q hq
              exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (Nat.cast_nonneg _)
    _ = ∑ γ : ι, ∑ q ∈ finAntidiagonal s p,
            (Nat.multinomial (univ : Finset (Fin s)) q : ℝ) *
              ‖adSequence A q (H γ)‖ := by
              simp_rw [mul_sum]
              rw [sum_comm]
    _ = ∑ γ : ι, αCommConj A (H γ) p := by rfl

/-- Dropping the innermost summand does not increase `αCommConj`. -/
lemma αCommConj_succ_le {𝔸 : Type*} [NormedRing 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin (s + 1) → 𝔸)
    (B : 𝔸) (p : ℕ) :
    αCommConj (fun i : Fin s => A i.succ) B p ≤ αCommConj A B p := by
  rw [αCommConj, αCommConj]
  calc
    (∑ q ∈ finAntidiagonal s p,
        (Nat.multinomial (univ : Finset (Fin s)) q : ℝ) *
          ‖adSequence (fun i => A i.succ) q B‖)
        = ∑ q ∈ finAntidiagonal s p,
            (Nat.multinomial (univ : Finset (Fin (s + 1))) (Fin.cons 0 q) : ℝ) *
              ‖adSequence A (Fin.cons 0 q) B‖ := by
              apply sum_congr rfl
              intro q hq
              rw [adSequence_cons_zero A q B, multinomial_cons_zero q]
    _ = ∑ q' ∈ (finAntidiagonal s p).image (Fin.cons 0),
            (Nat.multinomial (univ : Finset (Fin (s + 1))) q' : ℝ) *
              ‖adSequence A q' B‖ := by
              rw [sum_image]
              intro q₁ hq₁ q₂ hq₂ h
              funext i
              simpa using (congrFun h (i.succ))
    _ ≤ ∑ q' ∈ finAntidiagonal (s + 1) p,
            (Nat.multinomial (univ : Finset (Fin (s + 1))) q' : ℝ) *
              ‖adSequence A q' B‖ := by
              apply sum_le_sum_of_subset_of_nonneg
              · intro q hq
                rw [mem_image] at hq
                rcases hq with ⟨q₀, hq₀, rfl⟩
                rw [mem_finAntidiagonal]
                rw [mem_finAntidiagonal] at hq₀
                rw [Fin.sum_univ_succ]
                simpa using hq₀
              · intro q _ _
                exact mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)

/-- `αCommConj` of the last `n` entries of `A : Fin (m + n) → 𝔸` (indexed by `Fin.natAdd m`)
is bounded by the full `αCommConj`. -/
lemma αCommConj_natAdd_le {𝔸 : Type*} [NormedRing 𝔸] [Algebra ℝ 𝔸] {m n : ℕ} (A : Fin (m + n) → 𝔸)
    (B : 𝔸) (p : ℕ) :
    αCommConj (A ∘ Fin.natAdd m) B p ≤ αCommConj A B p := by
  induction m with
  | zero =>
      rw [show A ∘ Fin.natAdd 0 = (fun i : Fin n => A (Fin.cast (Nat.zero_add n).symm i)) by
        funext i
        apply congrArg A
        apply Fin.ext
        rw [Fin.val_natAdd, Fin.val_cast]
        exact Nat.zero_add i.val]
      exact (αCommConj_cast (Nat.zero_add n) A B p).le
  | succ m ih =>
      let e : (m + 1) + n = (m + n) + 1 := Nat.succ_add m n
      rw [show A ∘ Fin.natAdd (m + 1) =
          (fun j : Fin (m + n) => A (Fin.cast e.symm j.succ)) ∘ Fin.natAdd m by
        funext i
        apply congrArg A
        apply Fin.ext
        rw [Fin.val_natAdd, Fin.val_cast, Fin.val_succ, Fin.val_natAdd]
        exact Nat.succ_add m i.val]
      calc
        αCommConj ((fun j : Fin (m + n) => A (Fin.cast e.symm j.succ)) ∘ Fin.natAdd m) B p
            ≤ αCommConj (fun j : Fin (m + n) => A (Fin.cast e.symm j.succ)) B p :=
                ih (fun j : Fin (m + n) => A (Fin.cast e.symm j.succ))
        _ ≤ αCommConj (A ∘ Fin.cast e.symm) B p :=
                αCommConj_succ_le (A ∘ Fin.cast e.symm) B p
        _ = αCommConj A B p := αCommConj_cast e A B p

/-- Removing an initial segment of a list cannot increase its commutator scaling.
The list representation hides the dependent lengths and index casts from callers. -/
lemma αCommConj_get_drop_le {ι 𝔸 : Type*} [NormedRing 𝔸] [Algebra ℝ 𝔸]
    (l : List ι) (f : ι → 𝔸) (n : ℕ) (B : 𝔸) (p : ℕ) :
    αCommConj (fun k => f ((l.drop n).get k)) B p ≤
      αCommConj (fun k => f (l.get k)) B p := by
  induction n generalizing l with
  | zero => exact le_rfl
  | succ n ih =>
      cases l with
      | nil => exact le_rfl
      | cons a l =>
          exact (ih l).trans (by
            simpa using αCommConj_succ_le (fun k => f ((a :: l).get k)) B p)

/-- `αCommConj A B p` is a sum of nonnegative terms, hence nonnegative. -/
lemma αCommConj_nonneg {𝔸 : Type*} [NormedRing 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin s → 𝔸) (B : 𝔸)
    (p : ℕ) : 0 ≤ αCommConj A B p :=
  sum_nonneg (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))

end TrotterError
