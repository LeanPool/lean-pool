/-
Copyright (c) 2026 LongTails contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Tyurin, QuocViet Pham, Valentin Khrulkov, Ivan Oseledets
-/
module

public import LeanPool.LongTails.Proofs.DampedGeneralizedDynamics
public import LeanPool.LongTails.Proofs.Execution

/-!
Adapted from k3nfalt/longtails, commit 269cbc764dd36851fd0b64f2f950f329ee127de4.
Modified for Lean Pool: module visibility, namespace isolation, and current Mathlib.
-/

@[expose] public section

namespace LongTails.OracleTemplate.GeneralizedAccelerated

open LongTails.Setups.GeneralizedSmoothAndConvex

lemma two_queries (p : Public) (g : p.E → p.E) (s : Iterate p.E) :
    (fun state => (algorithm p).update state (g (((algorithm p).query state).2)))^[2]
      (.ready s) = .ready (step p.L0 p.L1 g s) := rfl

lemma first_two_queries (p : Public) (g : p.E → p.E)
    (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1) (hΔ : 0 < p.Δ) :
    (fun state => (algorithm p).update state (g (((algorithm p).query state).2)))^[2]
      ((algorithm p).initial ()) =
        .ready (step p.L0 p.L1 g (initialIterate p.L0 p.L1 p.R p.Δ p.x0 g)) := by
  have hc := coupling_same (p.R ^ 2 / (2 * p.Δ))
    (localCurvature p.L0 p.L1 (g p.x0)) p.x0 (by positivity)
    (localCurvature_pos hL0 hL1 _)
  simp only [step, initialIterate, hc]
  rfl

lemma execute_algorithm (p : Public) (g : p.E → p.E)
    (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1) (hΔ : 0 < p.Δ) (N : ℕ) :
    execute { answer := fun _ (_, x) _ => g x } (algorithm p) (fun _ => (2 * N)) =
      (run p.L0 p.L1 g (initialIterate p.L0 p.L1 p.R p.Δ p.x0 g) N).x := by
  let T := fun state => (algorithm p).update state (g (((algorithm p).query state).2))
  have hi : ∀ n, T^[2 * (n + 1)] ((algorithm p).initial ()) =
      .ready (run p.L0 p.L1 g (initialIterate p.L0 p.L1 p.R p.Δ p.x0 g) (n + 1)) := by
    intro n
    induction n with
    | zero => exact first_two_queries p g hL0 hL1 hΔ
    | succ n ih =>
      rw [show 2 * (n + 1 + 1) = 2 + 2 * (n + 1) by omega,
        Function.iterate_add_apply, ih]
      exact two_queries p g _
  erw [execute_iterate]
  cases N with
  | zero => rfl
  | succ n =>
    change (algorithm p).output (T^[2 * (n + 1)] ((algorithm p).initial ())) = _
    rw [hi]
    rfl

lemma execute_gradient_oracle (p : Public) (f : p.E → ℝ) (g : p.E → p.E)
    (oracle : Oracle p.E p.E)
    (hg : ∀ x, HasGradientAt f (g x) x)
    (horacle : ∀ k seed x, HasGradientAt f (oracle.answer k (0, x) seed) x)
    (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1) (hΔ : 0 < p.Δ) (N : ℕ)
    (seed : (algorithm p).Seed) (oracleSeed : (k : ℕ) → oracle.Seed k) :
    execute oracle (algorithm p) (fun _ => (2 * N)) seed oracleSeed =
      (run p.L0 p.L1 g (initialIterate p.L0 p.L1 p.R p.Δ p.x0 g) N).x := by
  have hanswer : ∀ k x sample, oracle.answer k (0, x) sample = g x :=
    fun k x sample => (horacle k sample x).unique (hg x)
  rw [execute_eq_of_answer_eq oracle g hanswer]
  cases seed
  exact execute_algorithm p g hL0 hL1 hΔ N

end LongTails.OracleTemplate.GeneralizedAccelerated
