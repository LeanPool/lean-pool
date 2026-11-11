/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.LevelExitTail
public import LeanPool.ECRuntime.UnrestrictedRuntime

/-!
Exact expected runtimes from Bellman certificates and geometric survival.
Finite-horizon residual identities and a vanishing-tail argument identify the
unrestricted expectation without assuming that every Bellman solution is minimal.

Ported from ECRuntime at a0e34dce6395d48d0fb9c7b8850088973f503d8b.
The module paths and public visibility are adapted for Lean Pool.
-/

@[expose] public section

open Filter
namespace ECRuntime

/-!
Reusable finite-horizon Bellman residual infrastructure. These supporting
lemmas were copied without altering the proof bodies from the compiler-clean
Stage 127 support branch. The combined public module is provisional until
its pinned full-gate check succeeds.
-/

/-- Every exact Bellman solution is an upper-bound certificate.
The reverse inequality, and thus uniqueness, remains the hard part. -/
theorem stage127_bellman_is_superSolution
    {alpha : Type*} [Fintype alpha]
    (P : TransitionMatrix alpha) (target : Set alpha)
    (R : alpha → Real)
    (hRzero : ∀ x, x ∈ target → R x = 0)
    (hRbellman : ∀ x, x ∉ target → R x = 1 + expectedValueAfter P R x) :
    IsRuntimeSuperSolution P target R := by
  constructor
  · exact hRzero
  · intro x hx
    exact le_of_eq (hRbellman x hx).symm

/-- The Bellman equality already yields the upper-bound half of the
runtime characterization using the certified supersolution theorem. -/
theorem stage127_bellman_gives_runtime_upperBound
    {alpha : Type*} [Fintype alpha]
    (P : TransitionMatrix alpha) (target : Set alpha)
    [DecidablePred (fun x => x ∈ target)]
    (hP : IsStochastic P) (R : alpha → Real)
    (hRnonneg : ∀ x, 0 ≤ R x)
    (hRzero : ∀ x, x ∈ target → R x = 0)
    (hRbellman : ∀ x, x ∉ target → R x = 1 + expectedValueAfter P R x)
    (x : alpha) :
    runtimeSup P target x ≤ ENNReal.ofReal (R x) := by
  exact runtimeSup_le_of_superSolution P target hP R hRnonneg
    (stage127_bellman_is_superSolution P target R hRzero hRbellman) x

/-- The Bellman residual after `t` transitions, killed when the chain
enters the target. This is a finite-state object, with no measure theory. -/
def bellmanResidual
    {alpha : Type*} [Fintype alpha]
    (P : TransitionMatrix alpha) (target : Set alpha)
    [DecidablePred (fun x => x ∈ target)] (R : alpha → Real) :
    Nat → alpha → Real
  | 0, x => R x
  | t + 1, x =>
      if x ∈ target then 0
      else expectedValueAfter P (bellmanResidual P target R t) x

/-- Exact stopped Bellman identity at *every finite horizon*.
The gap to the expected-runtime equality is the nonnegative residual;
showing this residual tends to zero requires a separate survival argument. -/
theorem stage127_bellman_split_finite
    {alpha : Type*} [Fintype alpha]
    (P : TransitionMatrix alpha) (target : Set alpha)
    [DecidablePred (fun x => x ∈ target)] (R : alpha → Real)
    (hRzero : ∀ x, x ∈ target → R x = 0)
    (hRbellman : ∀ x, x ∉ target → R x = 1 + expectedValueAfter P R x) :
    ∀ t (x : alpha),
      R x = finiteHorizonRuntime P target t x +
        bellmanResidual P target R t x := by
  intro t
  induction t with
  | zero =>
      intro x
      simp [finiteHorizonRuntime, bellmanResidual]
  | succ t ih =>
      intro x
      by_cases hx : x ∈ target
      · rw [hRzero x hx,
          finiteHorizonRuntime_succ_of_mem P target t x hx]
        simp [bellmanResidual, hx]
      · have hsplit :
            expectedValueAfter P R x =
              expectedValueAfter P (finiteHorizonRuntime P target t) x +
                expectedValueAfter P (bellmanResidual P target R t) x := by
          calc
            expectedValueAfter P R x =
                expectedValueAfter P (fun y => finiteHorizonRuntime P target t y +
                  bellmanResidual P target R t y) x := by
                    unfold expectedValueAfter
                    apply Finset.sum_congr rfl
                    intro y _
                    rw [ih y]
            _ = _ := expectedValueAfter_add P _ _ x
        rw [hRbellman x hx,
          finiteHorizonRuntime_succ_of_not_mem P target t x hx]
        simp only [bellmanResidual, ite_eq_right hx]
        rw [hsplit]
        ring

/-- The Bellman remainder is nonnegative for stochastic kernels and a
nonnegative terminal certificate. It vanishes only in the infinite-horizon
limit, which is precisely the outstanding Stage 127 obligation. -/
theorem bellmanResidual_nonneg
    {alpha : Type*} [Fintype alpha]
    (P : TransitionMatrix alpha) (target : Set alpha)
    [DecidablePred (fun x => x ∈ target)]
    (hP : IsStochastic P) (R : alpha → Real)
    (hRnonneg : ∀ x, 0 ≤ R x) :
    ∀ t (x : alpha), 0 ≤ bellmanResidual P target R t x := by
  intro t
  induction t with
  | zero =>
      intro x
      simpa [bellmanResidual] using hRnonneg x
  | succ t ih =>
      intro x
      by_cases hx : x ∈ target
      · simp [bellmanResidual, hx]
      · simp only [bellmanResidual, ite_eq_right hx]
        exact expectedValueAfter_nonneg P hP
          (bellmanResidual P target R t) ih x

/-- Uniformly bounded Bellman residuals are bounded by the survival mass
of the non-target set. This isolates the exact residual-limit obligation:
one only needs survival to tend to zero, not an independence assertion. -/
theorem bellmanResidual_le_survival
    {alpha : Type*} [Fintype alpha]
    (P : TransitionMatrix alpha) (target : Set alpha)
    [DecidablePred (fun x => x ∈ target)]
    (hP : IsStochastic P) (R : alpha → Real)
    (hRzero : ∀ x, x ∈ target → R x = 0)
    (B : Real) (hRbound : ∀ x, R x ≤ B) :
    ∀ t (x : alpha),
      bellmanResidual P target R t x ≤
        B * finiteLevelSurvival P targetᶜ t x := by
  classical
  intro t
  induction t with
  | zero =>
      intro x
      by_cases hx : x ∈ target
      · have houtside : x ∉ targetᶜ := by simpa using hx
        rw [finiteLevelSurvival_zero_of_not_mem P targetᶜ x houtside]
        simp [bellmanResidual, hRzero x hx]
      · have hinside : x ∈ targetᶜ := hx
        rw [finiteLevelSurvival_zero_of_mem P targetᶜ x hinside]
        simp [bellmanResidual, hRbound x]
  | succ t ih =>
      intro x
      by_cases hx : x ∈ target
      · have houtside : x ∉ targetᶜ := by simpa using hx
        rw [finiteLevelSurvival_succ_of_not_mem P targetᶜ t x houtside]
        simp [bellmanResidual, hx]
      · have hinside : x ∈ targetᶜ := hx
        rw [finiteLevelSurvival_succ_of_mem P targetᶜ t x hinside]
        simp only [bellmanResidual, ite_eq_right hx]
        have hmono := expectedValueAfter_mono P hP
          (bellmanResidual P target R t)
          (fun y : alpha => B * finiteLevelSurvival P targetᶜ t y)
          ih x
        calc
          expectedValueAfter P (bellmanResidual P target R t) x ≤
              expectedValueAfter P
                (fun y : alpha => B * finiteLevelSurvival P targetᶜ t y) x := hmono
          _ = B * (∑ y, P x y * finiteLevelSurvival P targetᶜ t y) := by
            unfold expectedValueAfter
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro y _
            ring

/-- A compiler-checkable *lower approximation* for the unrestricted runtime.
Its only error is the survival-probability remainder. Stage 129 gives an
explicit geometric bound for the RLS specialization. -/
theorem stage127_runtimeSup_lowerApprox
    {alpha : Type*} [Fintype alpha]
    (P : TransitionMatrix alpha) (target : Set alpha)
    [DecidablePred (fun x => x ∈ target)]
    (hP : IsStochastic P) (R : alpha → Real)
    (hRzero : ∀ x, x ∈ target → R x = 0)
    (hRbellman : ∀ x, x ∉ target → R x = 1 + expectedValueAfter P R x)
    (B : Real) (hRbound : ∀ x, R x ≤ B)
    (t : Nat) (x : alpha) :
    ENNReal.ofReal (R x - B * finiteLevelSurvival P targetᶜ t x) ≤
      runtimeSup P target x := by
  have hsplit := stage127_bellman_split_finite
    P target R hRzero hRbellman t x
  have hres := bellmanResidual_le_survival
    P target hP R hRzero B hRbound t x
  have hfinite : R x - B * finiteLevelSurvival P targetᶜ t x ≤
      finiteHorizonRuntime P target t x := by
    linarith
  exact (ENNReal.ofReal_le_ofReal hfinite).trans
    (finiteHorizonRuntime_ofReal_le_runtimeSup P target t x)

/-!
Unpromoted geometric-survival Bellman bridge, used by Stages 109 and 131.
The same mathematical assertion is user-approved as Stage 131. This support
lemma is internal: the public statement remains in the numbered candidate.
-/

/-- A bounded Bellman certificate is an exact runtime when the non-target
survival probability decays geometrically. -/
theorem candidate_geometricBellman_runtime_eq
    {alpha : Type*} [Fintype alpha]
    (P : TransitionMatrix alpha) (target : Set alpha)
    [DecidablePred (fun x => x ∈ target)]
    (hP : IsStochastic P) (R : alpha → Real)
    (hRnonneg : ∀ x, 0 ≤ R x)
    (hRzero : ∀ x, x ∈ target → R x = 0)
    (hRbellman : ∀ x, x ∉ target → R x = 1 + expectedValueAfter P R x)
    (B C q : Real) (hRB : ∀ x, R x ≤ B)
    (hC : 0 ≤ C) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hsurvival : ∀ t x,
      finiteLevelSurvival P targetᶜ t x ≤ C * q ^ t)
    (x : alpha) :
    runtimeSup P target x = ENNReal.ofReal (R x) := by
  -- The generic finite-horizon residual theorem is independent of geometric
  -- decay; this stage supplies the missing limit argument.
  have hupper : runtimeSup P target x ≤ ENNReal.ofReal (R x) :=
    stage127_bellman_gives_runtime_upperBound
      P target hP R hRnonneg hRzero hRbellman x
  have htail_limit : Tendsto (fun t : Nat => C * q ^ t)
      atTop (nhds (0 : Real)) := by
    have hpow : Tendsto (fun t : Nat => q ^ t)
        atTop (nhds (0 : Real)) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul hpow :
        Tendsto (fun t : Nat => C * q ^ t) atTop (nhds (C * 0)))
  have hsurvival_limit :
      Tendsto (fun t : Nat => finiteLevelSurvival P targetᶜ t x)
        atTop (nhds (0 : Real)) := by
    apply squeeze_zero
    · intro t
      exact finiteLevelSurvival_nonneg P targetᶜ hP t x
    · intro t
      exact hsurvival t x
    · exact htail_limit
  have hresidual_limit :
      Tendsto
        (fun t : Nat => R x - B * finiteLevelSurvival P targetᶜ t x)
        atTop (nhds (R x)) := by
    have hprod : Tendsto
        (fun t : Nat => B * finiteLevelSurvival P targetᶜ t x)
        atTop (nhds (0 : Real)) := by
      simpa only [mul_zero] using
        (tendsto_const_nhds.mul hsurvival_limit :
          Tendsto
            (fun t : Nat => B * finiteLevelSurvival P targetᶜ t x)
            atTop (nhds (B * 0)))
    simpa only [sub_zero] using
      (tendsto_const_nhds.sub hprod :
        Tendsto
          (fun t : Nat => R x - B * finiteLevelSurvival P targetᶜ t x)
          atTop (nhds (R x - 0)))
  have hENN_limit :
      Tendsto
        (fun t : Nat => ENNReal.ofReal
          (R x - B * finiteLevelSurvival P targetᶜ t x))
        atTop (nhds (ENNReal.ofReal (R x))) :=
    ENNReal.tendsto_ofReal hresidual_limit
  have hlower : ENNReal.ofReal (R x) ≤ runtimeSup P target x := by
    apply le_of_tendsto hENN_limit
    exact Filter.Eventually.of_forall (fun t =>
      stage127_runtimeSup_lowerApprox
        P target hP R hRzero hRbellman B hRB t x)
  -- C is nonnegative by hypothesis; the proof uses the stronger supplied
  -- bound directly, which already entails nonnegativity of every tail.
  have _hC : 0 ≤ C := hC
  exact le_antisymm hupper hlower

/-!
Stage 131 approved statement. Its hypotheses and conclusion match the
approved candidate exactly. Provisional integration: official full gate pending.
-/

/-- A nonnegative Bellman certificate with geometric survival bounds
computes the unrestricted expected first-hitting time exactly. -/
theorem proposed_exactRuntime_of_bellmanAndGeometricSurvival
    {alpha : Type*} [Fintype alpha]
    (P : TransitionMatrix alpha) (target : Set alpha)
    [DecidablePred (fun x => x ∈ target)]
    (hP : IsStochastic P) (R : alpha → Real)
    (hRnonneg : ∀ x, 0 ≤ R x)
    (hRzero : ∀ x, x ∈ target → R x = 0)
    (hRbellman : ∀ x, x ∉ target → R x = 1 + expectedValueAfter P R x)
    (B C q : Real) (hRB : ∀ x, R x ≤ B)
    (hC : 0 ≤ C) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hsurvival : ∀ t x,
      finiteLevelSurvival P targetᶜ t x ≤ C * q ^ t)
    (x : alpha) :
    runtimeSup P target x = ENNReal.ofReal (R x) := by
  exact candidate_geometricBellman_runtime_eq
    P target hP R hRnonneg hRzero hRbellman
    B C q hRB hC hq0 hq1 hsurvival x

end ECRuntime
