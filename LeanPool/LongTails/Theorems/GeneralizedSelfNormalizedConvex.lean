/-
Copyright (c) 2026 LongTails contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Tyurin, QuocViet Pham, Valentin Khrulkov, Ivan Oseledets
-/
module

public import LeanPool.LongTails.Setups.GeneralizedSmoothAndConvex
public import LeanPool.LongTails.Proofs.Execution
public import LeanPool.LongTails.Proofs.GeneralizedSelfNormalizedConvergence

/-!
Adapted from k3nfalt/longtails, commit 269cbc764dd36851fd0b64f2f950f329ee127de4.
Modified for Lean Pool: module visibility, namespace isolation, and current Mathlib.
-/

@[expose] public section

namespace LongTails.OracleTemplate.GeneralizedAccelerated.SelfNormalized

open LongTails.Setups.GeneralizedSmoothAndConvex

/-- Exact gradient-query budget, including both queries in every accelerated step. -/
noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ =>
  if q.Δ ≤ q.ε then 0 else
    2 * ⌈4096 * (1 + Real.sqrt (q.L0 * q.R ^ 2 / q.ε) +
      min ((⌈(q.L1 * q.R) ^ (2 / 3 : ℝ)⌉₊ : ℝ) * Real.log (4 + 4 * q.Δ / q.ε))
        (Real.log (4 + 4 * q.Δ / q.ε) +
          (q.L1 * q.R * Real.log (4 + 4 * q.Δ / q.ε)) ^ (2 / 3 : ℝ)))⌉₊

/-- Gradient-only acceleration under a Hessian-growth bound, uniformly in the target accuracy. -/
theorem result : Convergence LongTails.Setups.GeneralizedSmoothAndConvex.spec budget := by
  let trials (q : Public) (ε : ℝ) : ℕ :=
    ⌈4096 * (1 + Real.sqrt (q.L0 * q.R ^ 2 / ε) +
      min ((⌈(q.L1 * q.R) ^ (2 / 3 : ℝ)⌉₊ : ℝ) * Real.log (4 + 4 * q.Δ / ε))
        (Real.log (4 + 4 * q.Δ / ε) +
          (q.L1 * q.R * Real.log (4 + 4 * q.Δ / ε)) ^ (2 / 3 : ℝ)))⌉₊
  refine ⟨algorithm, ?_, fun _ _ => trivial⟩
  rintro q ⟨hL0, hL1, hR, hΔ, hε⟩
  rintro f oracle ⟨hc, hg, hgd, hH, u, hmin, hdist, hgap⟩
  let seed0 := (Classical.choice oracle.law.nonempty) 0
  let g := fun x => oracle.answer 0 (0, x) seed0
  by_cases he : q.Δ ≤ q.ε
  · refine ⟨u, hmin, Filter.Eventually.of_forall ?_⟩
    intro seed
    change f (execute oracle (algorithm q.toPublic) (budget q) seed.1 seed.2) - f u ≤ q.ε
    have hb : budget q = fun _ => 0 := by funext i; simp [budget, he]
    rw [hb]
    exact hgap.trans he
  · let K := trials q.toPublic q.ε
    have hacc := run_accuracy_min hL0 hL1 hR hΔ hε hc (hg 0 seed0) (hgd 0 seed0)
      (hH 0 seed0) q.x0 u hmin hdist hgap K (Nat.le_ceil _)
    refine ⟨u, hmin, Filter.Eventually.of_forall ?_⟩
    intro seed
    have hexec := execute_gradient_oracle q.toPublic f g oracle (hg 0 seed0) hg hL0 hL1 hΔ K
      seed.1 seed.2
    change f (execute oracle (algorithm q.toPublic) (budget q) seed.1 seed.2) - f u ≤ q.ε
    have hb : budget q = fun _ => 2 * K := by
      funext i
      simp only [budget, ite_eq_right he]
      rfl
    rw [hb]
    change f (execute oracle (algorithm q.toPublic) (fun _ => 2 * K) seed.1 seed.2) - f u ≤ q.ε
    rw [hexec]
    exact hacc

end LongTails.OracleTemplate.GeneralizedAccelerated.SelfNormalized
