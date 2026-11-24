/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.Algebra.BigOperators.Group.List.Fin
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Differentiation and smoothness of ordered list products

The pointwise product of finitely many algebra-valued functions satisfies the
ordered product rule and preserves differentiability classes.

## Main results

* `TrotterError.List.hasDerivAt_list_prod_at` gives the ordered product rule at a point.
* `TrotterError.List.contDiff_list_prod` shows that finite ordered products preserve smoothness.
-/

@[expose] public section

namespace TrotterError

open scoped Topology ContDiff

/-- `ContDiffAt` for the pointwise product of a finite list of functions. -/
lemma contDiffAt_list_prod {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    {ι : Type*} (l : List ι) (f : ι → ℝ → 𝔸) (n : ℕ∞ω) (t : ℝ)
    (hf : ∀ i ∈ l, ContDiffAt ℝ n (f i) t) :
    ContDiffAt ℝ n (fun t : ℝ => (l.map (fun i => f i t)).prod) t := by
  induction l with
  | nil => simpa using (contDiffAt_const : ContDiffAt ℝ n (fun _ : ℝ => (1 : 𝔸)) t)
  | cons a l ih =>
      simp only [List.map_cons, List.prod_cons]
      exact ContDiffAt.mul (hf a (by simp)) (ih (fun i hi => hf i (by simp [hi])))

namespace List

/-- The ordered product rule, assuming derivatives only at the evaluation point. -/
lemma hasDerivAt_list_prod_at {ι 𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    (l : List ι) (f : ι → ℝ → 𝔸) (Df : ι → 𝔸) (t : ℝ)
    (hf : ∀ i ∈ l, HasDerivAt (f i) (Df i) t) :
    HasDerivAt (fun s : ℝ => (l.map (fun i => f i s)).prod)
      (∑ k : Fin l.length,
        ((l.take (k : ℕ)).map (fun i => f i t)).prod * Df (l.get k) *
          ((l.drop ((k : ℕ) + 1)).map (fun i => f i t)).prod) t := by
  induction l with
  | nil => simpa using (hasDerivAt_const t (1 : 𝔸))
  | cons a l ih =>
      have hf' : ∀ i ∈ l, HasDerivAt (f i) (Df i) t := by
        intro i hi
        exact hf i (List.mem_cons_of_mem a hi)
      have ih' : HasDerivAt (fun s : ℝ => (l.map (fun i => f i s)).prod)
          (∑ k : Fin l.length,
            ((l.take (k : ℕ)).map (fun i => f i t)).prod * Df (l.get k) *
              ((l.drop ((k : ℕ) + 1)).map (fun i => f i t)).prod) t := ih hf'
      have hfa : HasDerivAt (f a) (Df a) t := hf a (show a ∈ a :: l from List.mem_cons_self)
      have hprod : HasDerivAt (fun s : ℝ => f a s * (l.map (fun i => f i s)).prod)
          (Df a * (l.map (fun i => f i t)).prod + f a t *
            (∑ k : Fin l.length,
              ((l.take (k : ℕ)).map (fun i => f i t)).prod * Df (l.get k) *
                ((l.drop ((k : ℕ) + 1)).map (fun i => f i t)).prod)) t := hfa.mul ih'
      have hsum :
          (∑ k : Fin (l.length + 1),
            (((a :: l).take (k : ℕ)).map (fun i => f i t)).prod * Df ((a :: l).get k) *
              (((a :: l).drop ((k : ℕ) + 1)).map (fun i => f i t)).prod)
            = Df a * (l.map (fun i => f i t)).prod + f a t *
                (∑ k : Fin l.length,
                  ((l.take (k : ℕ)).map (fun i => f i t)).prod * Df (l.get k) *
                    ((l.drop ((k : ℕ) + 1)).map (fun i => f i t)).prod) := by
        rw [Fin.sum_univ_succ]
        congr 1; · simp
        · rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          simp [mul_assoc]
      change HasDerivAt (fun s : ℝ => f a s * (l.map (fun i => f i s)).prod)
        (∑ k : Fin (l.length + 1),
          (((a :: l).take (k : ℕ)).map (fun i => f i t)).prod * Df ((a :: l).get k) *
            (((a :: l).drop ((k : ℕ) + 1)).map (fun i => f i t)).prod) t
      rwa [hsum]

/-- The pointwise product of a finite list of `C^n` functions is `C^n`. -/
lemma contDiff_list_prod {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    {ι : Type*} (l : List ι) (f : ι → ℝ → 𝔸) {n : ℕ∞ω}
    (hf : ∀ i ∈ l, ContDiff ℝ n (f i)) :
    ContDiff ℝ n (fun t : ℝ => (l.map (fun i => f i t)).prod) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  exact contDiffAt_list_prod l f n t (fun i hi => (hf i hi).contDiffAt)

end List

end TrotterError
