/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
# Finite antidiagonals and multinomial reindexing

Combinatorial identities for ordered-product expansions: splitting and reindexing
antidiagonals, multinomial coefficients, and products of factorials.
This module has no dependency on the TrotterError analysis modules.

## Main results

* `sum_finAntidiagonal_succ`, `sum_finAntidiagonal_snoc`: split an antidiagonal by an endpoint.
* `sum_piAntidiag_univ_equiv`, `multinomial_univ_equiv`: reindex by an equivalence.
* `sum_range_add_antidiagonal`: reindex the triangular sum in the conjugation expansion.
-/

@[expose] public section

namespace TrotterError

open Finset
open scoped BigOperators

/-- The multinomial coefficient is invariant under renaming the index type by an injective map. -/
lemma multinomial_image {α β : Type*} [DecidableEq β] (s : Finset α) (e : α → β)
    (he : Set.InjOn e s) (f : β → ℕ) :
    Nat.multinomial (s.image e) f = Nat.multinomial s (f ∘ e) := by
  simp [Nat.multinomial, Finset.sum_image he, Finset.prod_image he, Function.comp_apply]

/-- The multinomial recursion for `Fin (m + 1)`, splitting off the index `0`. -/
lemma multinomial_fin_succ {m : ℕ} (k : ℕ) (q : Fin m → ℕ) :
    Nat.multinomial (Finset.univ : Finset (Fin (m + 1))) (Fin.cons k q) =
      (k + ∑ i : Fin m, q i).choose k * Nat.multinomial (Finset.univ : Finset (Fin m)) q := by
  have huniv : (Finset.univ : Finset (Fin (m + 1))) =
      insert (0 : Fin (m + 1)) (Finset.univ.image (Fin.succ : Fin m → Fin (m + 1))) := by
    ext i
    simp [Fin.image_succ_univ]
  rw [huniv, Nat.multinomial_insert (show (0 : Fin (m + 1)) ∉
      Finset.univ.image (Fin.succ : Fin m → Fin (m + 1)) by
    simp [Fin.image_succ_univ])]
  simp only [Fin.cons_zero]
  have hinj : Set.InjOn (Fin.succ : Fin m → Fin (m + 1))
      (↑(Finset.univ : Finset (Fin m)) : Set (Fin m)) := by
    intro a _ b _ h
    exact Fin.succ_injective m h
  rw [Finset.sum_image hinj, multinomial_image (Finset.univ : Finset (Fin m))
    (Fin.succ : Fin m → Fin (m + 1)) hinj (Fin.cons k q)]
  have hsum :
      (∑ x : Fin m, ((Fin.cons k q : Fin (m + 1) → ℕ) (Fin.succ x))) = ∑ x : Fin m, q x := rfl
  have hcomp : ((Fin.cons k q : Fin (m + 1) → ℕ) ∘ Fin.succ) = q := rfl
  rw [hsum, hcomp]

/-- The antidiagonal of `Fin (m + 1)` fibers over that of `Fin m` by the value at `0`. -/
lemma sum_finAntidiagonal_succ {𝔸 : Type*} [AddCommMonoid 𝔸] (m n : ℕ)
    (G : (Fin (m + 1) → ℕ) → 𝔸) :
    (∑ q' ∈ Finset.finAntidiagonal (m + 1) n, G q') =
      ∑ k ∈ Finset.range (n + 1), ∑ q ∈ Finset.finAntidiagonal m (n - k), G (Fin.cons k q) := by
  rw [Finset.sum_sigma']
  refine (Finset.sum_bij (fun x _ => Fin.cons x.1 x.2) ?_ ?_ ?_ ?_).symm
  · intro x hx
    rw [Finset.mem_finAntidiagonal, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    have hx' : x.1 ∈ Finset.range (n + 1) ∧ x.2 ∈ Finset.finAntidiagonal m (n - x.1) :=
      Finset.mem_sigma.mp hx
    have hle : x.1 ≤ n := by simpa using Finset.mem_range.mp hx'.1
    have hsum : (∑ i : Fin m, x.2 i) = n - x.1 := by
      simpa using Finset.mem_finAntidiagonal.mp hx'.2
    rw [hsum, Nat.add_sub_of_le hle]
  · intro x₁ _ x₂ _ h
    obtain ⟨h1, h2⟩ := Fin.cons_inj.mp h
    exact Sigma.ext h1 (heq_of_eq h2)
  · intro q' hq'
    have hsum : (∑ i : Fin (m + 1), q' i) = n := Finset.mem_finAntidiagonal.mp hq'
    have hsplit : q' 0 + (∑ i : Fin m, q' (Fin.succ i)) = n := by
      simpa [Fin.sum_univ_succ] using hsum
    refine ⟨⟨q' 0, Fin.tail q'⟩, ?_, ?_⟩
    · rw [Finset.mem_sigma]
      constructor
      · rw [Finset.mem_range]
        have hle : q' 0 ≤ n := by
          rw [← hsplit]
          exact Nat.le_add_right _ _
        exact Nat.lt_succ_of_le hle
      · rw [Finset.mem_finAntidiagonal]
        have htail : (∑ i : Fin m, q' (Fin.succ i)) = n - q' 0 := by
          rw [← hsplit, Nat.add_sub_cancel_left]
        simpa [Fin.tail] using htail
    · exact Fin.cons_self_tail q'
  · intro x _
    rfl

/-- The `Fin m` antidiagonal coincides with `piAntidiag` on `univ`. -/
lemma finAntidiagonal_eq_piAntidiag_univ (m n : ℕ) :
    Finset.finAntidiagonal m n = Finset.piAntidiag (Finset.univ : Finset (Fin m)) n := by
  ext f
  simp [Finset.mem_finAntidiagonal, Finset.mem_piAntidiag]

/-- The antidiagonal over the empty index type. -/
lemma finAntidiagonal_zero (n : ℕ) : Finset.finAntidiagonal 0 n = if n = 0 then {0} else ∅ := by
  ext f
  rw [Finset.mem_finAntidiagonal]
  by_cases h : n = 0
  · subst n
    simp [funext_iff]
  · simp only [ite_eq_right h, Finset.notMem_empty, iff_false, Fin.sum_univ_zero]
    intro hsum
    exact h hsum.symm

/-- Reindexing a sum over `Finset.piAntidiag univ` by an equivalence of the index type. -/
lemma sum_piAntidiag_univ_equiv {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] (e : α ≃ β) (n : ℕ) {𝕄 : Type*} [AddCommMonoid 𝕄] (G : (α → ℕ) → 𝕄) :
    (∑ q ∈ Finset.piAntidiag (Finset.univ : Finset α) n, G q) =
      ∑ q' ∈ Finset.piAntidiag (Finset.univ : Finset β) n, G (q' ∘ e) := by
  refine Finset.sum_bij (fun q _ => q ∘ e.symm) ?_ ?_ ?_ ?_
  · intro q hq
    rw [Finset.mem_piAntidiag] at hq ⊢
    constructor
    · exact (Equiv.sum_comp e.symm q).trans hq.1
    · intro b hb
      simp
  · intro q₁ hq₁ q₂ hq₂ h
    funext x
    have hx : x = e.symm (e x) := (e.symm_apply_apply x).symm
    rw [hx]
    exact congr_fun h (e x)
  · intro q' hq'
    refine ⟨q' ∘ e, ?_, ?_⟩
    · rw [Finset.mem_piAntidiag] at hq' ⊢
      constructor
      · exact (Equiv.sum_comp e q').trans hq'.1
      · intro a ha; simp
    · ext b; simp
  · intro q hq
    apply congrArg G
    funext x
    simp

/-- The multinomial coefficient over `univ` is invariant under reindexing by an equivalence. -/
lemma multinomial_univ_equiv {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β) (q : β → ℕ) :
    Nat.multinomial (Finset.univ : Finset β) q =
      Nat.multinomial (Finset.univ : Finset α) (q ∘ e) := by
  classical
  rw [← Finset.image_univ_equiv e]
  exact multinomial_image (Finset.univ : Finset α) e (fun a _ b _ h ↦ e.injective h) q

/-! ### Finset / `finAntidiagonal` / multinomial reindexing -/

/-- The antidiagonal of `Fin (m + 1)` fibers over that of `Fin m` by the value at the last index,
via `Fin.snoc`. -/
lemma sum_finAntidiagonal_snoc {𝔸 : Type*} [AddCommMonoid 𝔸] (m n : ℕ)
    (G : (Fin (m + 1) → ℕ) → 𝔸) :
    (∑ q' ∈ finAntidiagonal (m + 1) n, G q') =
      ∑ k ∈ range (n + 1), ∑ q ∈ finAntidiagonal m (n - k), G (Fin.snoc q k) := by
  rw [sum_sigma']
  refine (sum_bij (fun x _ => Fin.snoc x.2 x.1) ?_ ?_ ?_ ?_).symm
  · intro x hx
    rw [mem_finAntidiagonal, Fin.sum_snoc]
    have hx' : x.1 ∈ range (n + 1) ∧ x.2 ∈ finAntidiagonal m (n - x.1) :=
      mem_sigma.mp hx
    have hle : x.1 ≤ n := by simpa using mem_range.mp hx'.1
    have hsum : (∑ i : Fin m, x.2 i) = n - x.1 := by
      simpa using mem_finAntidiagonal.mp hx'.2
    rw [hsum, Nat.sub_add_cancel hle]
  · intro x₁ _ x₂ _ h
    obtain ⟨hq, hk⟩ := Fin.snoc_inj.mp h
    exact Sigma.ext hk (heq_of_eq hq)
  · intro q' hq'
    have hsum : (∑ i : Fin (m + 1), q' i) = n := mem_finAntidiagonal.mp hq'
    have hsplit : (∑ i : Fin m, q' i.castSucc) + q' (Fin.last m) = n := by
      simpa [Fin.sum_univ_castSucc] using hsum
    refine ⟨⟨q' (Fin.last m), Fin.init q'⟩, ?_, Fin.snoc_init_self q'⟩
    rw [mem_sigma]; constructor
    · rw [mem_range]
      have hle : q' (Fin.last m) ≤ n := by
        rw [← hsplit]
        exact Nat.le_add_left _ _
      exact Nat.lt_succ_of_le hle
    · rw [mem_finAntidiagonal]
      have hinit : (∑ i : Fin m, q' i.castSucc) = n - q' (Fin.last m) := by
        rw [← hsplit, Nat.add_sub_cancel_right]
      simpa [Fin.init] using hinit
  · tauto

/-- Appending a zero multiplicity does not change the multinomial coefficient. -/
lemma multinomial_snoc_zero {m : ℕ} (q : Fin m → ℕ) :
    Nat.multinomial (univ : Finset (Fin (m + 1))) (Fin.snoc q 0) =
      Nat.multinomial (univ : Finset (Fin m)) q := by
  simp only [Nat.multinomial]
  rw [Fin.sum_snoc, Fin.prod_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

/-- Reindexing `range (n+1)` minus `0` to `range n` by `k ↦ k + 1`. -/
lemma sum_range_filter_ne_zero {𝔸 : Type*} [AddCommMonoid 𝔸] (n : ℕ) (f : ℕ → 𝔸) :
    (∑ k ∈ (range (n + 1)).filter (fun k => k ≠ 0), f k) =
      ∑ k ∈ range n, f (k + 1) := by
  refine (sum_bij (fun k _ => k + 1) ?_ ?_ ?_ ?_).symm
  · intro k hk
    rw [mem_filter, mem_range]
    exact ⟨Nat.add_lt_add_right (mem_range.mp hk) 1, Nat.succ_ne_zero k⟩
  · intros; lia
  · intro b hb
    rw [mem_filter, mem_range] at hb
    have hbpos : 0 < b := Nat.pos_of_ne_zero hb.2
    refine ⟨b - 1, ?_, ?_⟩
    · rw [mem_range]; lia
    · lia
  · tauto

/-- The sum over `finAntidiagonal (s + 1) p` filtered by nonzero last entry equals the sum over the
`k ≥ 1` slices of the `Fin.snoc` fibration. -/
lemma sum_finAntidiagonal_filter_last_ne_zero {𝔸 : Type*} [AddCommMonoid 𝔸] (s p : ℕ)
    (G : (Fin (s + 1) → ℕ) → 𝔸) :
    (∑ q ∈ (finAntidiagonal (s + 1) p).filter (fun q => q (Fin.last s) ≠ 0), G q) =
      ∑ k ∈ range p, ∑ q ∈ finAntidiagonal s (p - (k + 1)),
        G (Fin.snoc q (k + 1)) := by
  rw [sum_filter, sum_finAntidiagonal_snoc]
  simp only [Fin.snoc_last]
  trans (∑ x ∈ (range (p + 1)).filter (fun x => x ≠ 0),
      ∑ q ∈ finAntidiagonal s (p - x), G (Fin.snoc q x))
  · rw [sum_filter]
    apply sum_congr rfl
    intro x _
    by_cases h : x = 0 <;> simp [h]
  · rw [sum_range_filter_ne_zero]

/-- The inverse factorial coefficient of a snoc'd multiplicity factors as `j!⁻¹ · ∏qᵢ!⁻¹`. -/
lemma factorial_inv_snoc {s : ℕ} (q : Fin s → ℕ) (j : ℕ) :
    (Nat.factorial j : ℝ)⁻¹ * (∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹ =
      (∏ i : Fin (s + 1), (Nat.factorial ((Fin.snoc q j : Fin (s + 1) → ℕ) i) : ℝ))⁻¹ := by
  rw [← mul_inv, mul_comm (Nat.factorial j : ℝ) (∏ i : Fin s, (Nat.factorial (q i) : ℝ)),
    Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

/-- Reindexing the double sum over `{(j, i) | j < p, i < p - j}` (equivalently `i + j < p`)
to the sum over `{(m, i) | m < p, i ≤ m}` via `m = i + j`. -/
lemma sum_range_add_antidiagonal {𝔸 : Type*} [AddCommMonoid 𝔸] (p : ℕ) (f : ℕ → ℕ → 𝔸) :
    (∑ j ∈ range p, ∑ i ∈ range (p - j), f i j) =
      ∑ m ∈ range p, ∑ i ∈ range (m + 1), f i (m - i) := by
  rw [← sum_range_diag_flip p (fun j i => f i j)]
  refine sum_congr rfl fun m _ => ?_
  simpa only [Nat.sum_antidiagonal_eq_sum_range_succ_mk, Prod.swap_prod_mk, Nat.succ_eq_add_one]
    using (Nat.sum_antidiagonal_swap (n := m) (f := fun q => f q.1 q.2))

/-- Reindexing `j ↦ p - j - 1` over the antidiagonal fibers: the sum over `j < p` of the
`Fin.snoc q (p - j)`-fiber equals the sum over `k < p` of the `Fin.snoc q (k + 1)`-fiber. -/
lemma sum_range_finAntidiagonal_reflect {s p : ℕ} {𝔸 : Type*} [AddCommMonoid 𝔸]
    (G : (Fin (s + 1) → ℕ) → 𝔸) :
    (∑ j ∈ range p, ∑ q ∈ finAntidiagonal s j, G (Fin.snoc q (p - j))) =
      ∑ k ∈ range p, ∑ q ∈ finAntidiagonal s (p - (k + 1)), G (Fin.snoc q (k + 1)) := by
  calc
    (∑ j ∈ range p, ∑ q ∈ finAntidiagonal s j, G (Fin.snoc q (p - j)))
        = ∑ j ∈ range p, ∑ q ∈ finAntidiagonal s (p - ((p - 1 - j) + 1)),
            G (Fin.snoc q ((p - 1 - j) + 1)) := by
              apply Finset.sum_congr rfl
              intro j hj
              have hj' : j < p := mem_range.mp hj
              have h1 : p - ((p - 1 - j) + 1) = j := by lia
              have h2 : (p - 1 - j) + 1 = p - j := by lia
              rw [h1, h2]
    _ = ∑ k ∈ range p, ∑ q ∈ finAntidiagonal s (p - (k + 1)), G (Fin.snoc q (k + 1)) := by
              simpa using (Finset.sum_range_reflect
                (fun k => ∑ q ∈ finAntidiagonal s (p - (k + 1)), G (Fin.snoc q (k + 1))) p)

end TrotterError
