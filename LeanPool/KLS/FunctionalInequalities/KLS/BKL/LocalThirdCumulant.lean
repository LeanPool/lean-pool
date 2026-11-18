/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Cumulant.Local
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Density.BorellRepresentation.Moments
public import LeanPool.KLS.FunctionalInequalities.KLS.Isotropic
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Suspension.Law

/-!
# BKL Lemma 4.2 in its source scope, conditional on the Letwin bound

Bizeul–Klartag–Lehec arXiv:2610.05474v1, Lemma 4.2 and the base of the Section 4 induction. For an
isotropic log-concave law, Borell gives some positive exponential radius (not every exponential
moment);
with the Letwin quadratic-form bound
(Letwin Theorem 1.2, an explicit hypothesis) the third cumulants satisfy `∑_{jk} κ₃(u,e_j,e_k)² ≤
8‖u‖²`.
If this holds for all isotropic log-concave laws in positive dimension, `CumulantBound 2 8` follows.
The statement in `Analysis/BakryEmery/Cumulant/Basic.lean` assumes all exponential moments, which
general log-concave laws (e.g. Laplace) do not have; this module is the source-faithful version.
The noncompact input is proved separately by `KLS.LogConcave.letwinQuadraticBound` in
`KLS/Letwin/QuadraticBound.lean`; the interfaces here remain conditional to avoid that import.
The proof of Theorem 4.1 uses compact Letwin and cutoff induction; no uncut Eldan process
is constructed.
-/

@[expose] public section

open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace

namespace FunctionalInequalities.KLS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/--
**BKL Lemma 4.2 (source scope), conditional on the Letwin quadratic bound**: for every isotropic
log-concave law `μ` with `LetwinQuadraticBound μ`, `∑_{jk} κ₃(u, b_j, b_k)² ≤ 8‖u‖²` in any
orthonormal
basis; the exponential radius comes from Borell. The noncompact input is supplied separately by
`KLS.LogConcave.letwinQuadraticBound` in positive dimension; this interface remains conditional. -/
theorem LogConcave.sum_sq_cumulant_three_le_of_letwin (μ : ProbabilityMeasure E)
    (hLC : KLS.LogConcave μ) (hiso : KLS.Isotropic μ)
    (hL : LetwinQuadraticBound (μ : Measure E)) {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E)
    (u : E) : ∑ j, ∑ k, cumulant (μ : Measure E) 3 ![u, b j, b k] ^ 2 ≤ 8 * ‖u‖ ^ 2 := by
  obtain ⟨r, hr, hexp⟩ := ((KLS.LogConcave.borel_iff μ).1 hLC).exists_integrable_exp_norm
  apply
    Analysis.BakryEmery.sum_sq_cumulant_three_le_of_letwin_of_integrable_exp_basis
      (μ : Measure E) hr hexp ?_ hiso.integral_inner_mul_inner hL b u
  intro v
  have h := (innerSL ℝ v).integral_comp_comm (hiso.memLp_two.integrable (by norm_num))
  simpa only [Function.comp_def, innerSL_apply_apply, id_eq, hiso.mean_zero,
    inner_zero_right] using h

/--
**Base case of the Eldan induction**: if every isotropic log-concave law on `ℝⁿ` (`n > 0`) satisfies
the
Letwin quadratic bound, then `CumulantBound 2 8` holds (order `(d+1) = 3`, `b = 8`); dimension zero
is vacuous.
The input is proved in `KLS/Letwin/QuadraticBound.lean`; this interface remains conditional. -/
theorem LogConcave.Suspension.cumulantBound_two_of_letwin
    (hLetwin :
      ∀ (n : ℕ),
        0 < n →
          ∀ μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)),
            KLS.LogConcave μ →
              KLS.Isotropic μ → LetwinQuadraticBound (μ : Measure (EuclideanSpace ℝ (Fin n)))) :
    CumulantBound 2 8 := by
  classical
  intro n μ hiso hLC u
  cases n with
  |
    zero =>
    have hs :
      (∑ J : Fin 2 → Fin 0,
          cumulant (μ : Measure _) 3
              (Fin.cons u fun k => EuclideanSpace.basisFun (Fin 0) ℝ (J k)) ^
            2) =
        0 := by
      apply Finset.sum_eq_zero
      intro J _hJ
      exact Fin.elim0 (J 0)
    rw [hs]
    positivity
  | succ n =>
    let b := EuclideanSpace.basisFun (Fin (n + 1)) ℝ
    have h :=
      LogConcave.sum_sq_cumulant_three_le_of_letwin μ hLC hiso
        (hLetwin (n + 1) (Nat.succ_pos _) μ hLC hiso) b u
    have heq :
      (∑ J : Fin 2 → Fin (n + 1),
          cumulant (μ : Measure _) 3 (Fin.cons u fun k => b (J k)) ^ 2) =
        ∑ j, ∑ k, cumulant (μ : Measure _) 3 ![u, b j, b k] ^ 2 := by
      exact
        Analysis.Tensor.sum_finTwo_arrow_cons b u (fun v => cumulant (μ : Measure _) 3 v ^ 2)
    change
      (∑ J : Fin 2 → Fin (n + 1),
          cumulant (μ : Measure _) 3 (Fin.cons u fun k => b (J k)) ^ 2) ≤
        _
    rw [heq]
    exact h

end FunctionalInequalities.KLS
