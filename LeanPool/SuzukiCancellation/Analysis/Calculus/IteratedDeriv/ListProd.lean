/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.Algebra.BigOperators.FinAntidiagonal
public import LeanPool.SuzukiCancellation.Analysis.Calculus.ListProd
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Higher derivatives of ordered finite products

The multinomial Leibniz expansion preserves multiplication order without commutativity.

## Main results

* `TrotterError.natCast_mul_smul_eq`.
* `TrotterError.iteratedDeriv_ofFn_prod`.
* `TrotterError.iteratedDeriv_list_prod_general`.
-/

@[expose] public section

namespace TrotterError

open NormedSpace Asymptotics Finset
open scoped Topology BigOperators ContDiff algebraMap

/-- A natural-number cast factors through the real scalar action:
`(a : 𝔸) * x * ((b : ℝ) • y) = ((a * b : ℕ) : ℝ) • (x * y)`. -/
lemma natCast_mul_smul_eq {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    (a b : ℕ) (x y : 𝔸) :
    (a : 𝔸) * x * ((b : ℝ) • y) = ((a * b : ℕ) : ℝ) • (x * y) := by
  rw [(algebraMap.coe_natCast (R := ℝ) (A := 𝔸) a).symm, ← Algebra.smul_def (a : ℝ) x,
    smul_mul_assoc, mul_smul_comm, smul_smul, ← Nat.cast_mul]

/-- The `n`-th iterated derivative of a finite product of functions is the multinomial Leibniz
expansion, indexed by `Finset.finAntidiagonal`. -/
theorem iteratedDeriv_ofFn_prod {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    {m : ℕ} (f : Fin m → ℝ → 𝔸) (n : ℕ) (t : ℝ)
    (hf : ∀ i, ContDiffAt ℝ n (f i) t) :
    iteratedDeriv n (fun t : ℝ => (List.ofFn (fun i : Fin m => f i t)).prod) t =
      ∑ q ∈ Finset.finAntidiagonal m n,
        (Nat.multinomial (Finset.univ : Finset (Fin m)) q : ℝ) •
          (List.ofFn (fun i : Fin m => iteratedDeriv (q i) (f i) t)).prod := by
  induction m generalizing n t with
  | zero =>
      cases n with
      | zero => simp [iteratedDeriv_zero, finAntidiagonal_zero]
      | succ n => simp [iteratedDeriv_const, finAntidiagonal_zero]
  | succ m ih =>
      let g : Fin m → ℝ → 𝔸 := fun i => f i.succ
      calc
        iteratedDeriv n (fun t : ℝ => (List.ofFn (fun i : Fin (m + 1) => f i t)).prod) t
            = iteratedDeriv n
                ((f 0) * (fun t : ℝ => (List.ofFn (fun i : Fin m => g i t)).prod)) t := by
                congr 1
                funext t
                rw [List.ofFn_succ]
                rfl
        _ = ∑ k ∈ Finset.range (n + 1), n.choose k * iteratedDeriv k (f 0) t *
              iteratedDeriv (n - k) (fun t : ℝ => (List.ofFn (fun i : Fin m => g i t)).prod) t := by
                rw [iteratedDeriv_mul (hf 0) (by
                  simpa [List.ofFn_eq_map] using
                    contDiffAt_list_prod (List.finRange m) g n t (fun i _ => hf i.succ))]
        _ = ∑ k ∈ Finset.range (n + 1), ∑ q ∈ Finset.finAntidiagonal m (n - k),
              n.choose k * iteratedDeriv k (f 0) t *
                ((Nat.multinomial (Finset.univ : Finset (Fin m)) q : ℝ) •
                  (List.ofFn (fun i : Fin m => iteratedDeriv (q i) (g i) t)).prod) := by
                apply Finset.sum_congr rfl
                intro k _
                rw [ih g (n - k) t (fun i => (hf i.succ).of_le (mod_cast Nat.sub_le n k)),
                  Finset.mul_sum]
        _ = ∑ k ∈ Finset.range (n + 1), ∑ q ∈ Finset.finAntidiagonal m (n - k),
              (Nat.multinomial (Finset.univ : Finset (Fin (m + 1))) (Fin.cons k q) : ℝ) •
                (List.ofFn (fun i : Fin (m + 1) =>
                  iteratedDeriv (((Fin.cons k q : Fin (m + 1) → ℕ) i)) (f i) t)).prod := by
                apply Finset.sum_congr rfl
                intro k hk
                apply Finset.sum_congr rfl
                intro q hq
                have hle : k ≤ n := by simpa using Finset.mem_range.mp hk
                have hqsum : (∑ i : Fin m, q i) = n - k := by
                  simpa using Finset.mem_finAntidiagonal.mp hq
                rw [natCast_mul_smul_eq (n.choose k)
                  (Nat.multinomial (Finset.univ : Finset (Fin m)) q)
                  (iteratedDeriv k (f 0) t)
                  ((List.ofFn (fun i : Fin m => iteratedDeriv (q i) (g i) t)).prod)]
                have hrec : Nat.multinomial (Finset.univ : Finset (Fin (m + 1))) (Fin.cons k q) =
                    n.choose k * Nat.multinomial (Finset.univ : Finset (Fin m)) q := by
                  rw [multinomial_fin_succ, hqsum, Nat.add_sub_of_le hle]
                rw [hrec]
                congr 1
                rw [List.ofFn_succ]
                simp [g, Fin.cons_zero, Fin.cons_succ]
        _ = ∑ q' ∈ Finset.finAntidiagonal (m + 1) n,
              (Nat.multinomial (Finset.univ : Finset (Fin (m + 1))) q' : ℝ) •
                (List.ofFn (fun i : Fin (m + 1) => iteratedDeriv (q' i) (f i) t)).prod := by
                rw [sum_finAntidiagonal_succ m n (fun q' =>
                  (Nat.multinomial (Finset.univ : Finset (Fin (m + 1))) q' : ℝ) •
                    (List.ofFn (fun i : Fin (m + 1) => iteratedDeriv (q' i) (f i) t)).prod)]

/-- The `n`-th iterated derivative of the product of a family indexed by an arbitrary list `l`
is the multinomial Leibniz expansion, with multi-indices indexed by the positions `Fin l.length`. -/
theorem iteratedDeriv_list_prod_general {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    {ι : Type*} (l : List ι) (f : ι → ℝ → 𝔸) (n : ℕ) (t : ℝ)
    (hf : ∀ i ∈ l, ContDiffAt ℝ n (f i) t) :
    iteratedDeriv n (fun t : ℝ => (l.map (fun i => f i t)).prod) t =
      ∑ q ∈ Finset.piAntidiag (Finset.univ : Finset (Fin l.length)) n,
        (Nat.multinomial (Finset.univ : Finset (Fin l.length)) q : ℝ) •
          (List.ofFn (fun j : Fin l.length => iteratedDeriv (q j) (f (l.get j)) t)).prod := by
  have hprod : (fun t : ℝ => (List.ofFn (fun j : Fin l.length => f (l.get j) t)).prod) =
      fun t : ℝ => (l.map (fun i => f i t)).prod := by
    funext t
    congr 1
    simpa using (List.ofFn_getElem_eq_map l (fun i : ι => f i t))
  rw [← hprod]
  simpa [finAntidiagonal_eq_piAntidiag_univ] using
    iteratedDeriv_ofFn_prod (fun j : Fin l.length => f (l.get j)) n t
      (fun j => hf (l.get j) (List.get_mem l j))

end TrotterError
