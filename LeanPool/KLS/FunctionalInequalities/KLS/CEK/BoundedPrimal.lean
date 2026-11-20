/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.CEK.VariationalMaximum
public import LeanPool.KLS.FunctionalInequalities.KLS.Isotropic
public import LeanPool.KLS.FunctionalInequalities.Probability.Covariance.Positivity
public import LeanPool.KLS.FunctionalInequalities.Probability.MomentMeasure.Integrability
public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Legendre.BoundedDomain

/-!
# A normalized Lipschitz primal for a bounded isotropic source law

For a bundled isotropic probability law `μ` on a finite-dimensional real inner-product space
(dimension zero included) and
`L : ℝ≥0` with `‖y‖ ≤ L` `μ`-almost everywhere, the CEK variational maximiser
(`exists_variational_maximum`, Proposition 12)
capped to `closedBall 0 L` is again a maximiser: convex, lower semicontinuous, `μ`-integrable, with
effective domain in the
ball, conjugate mass `1` and every competitor's functional at most its own
(`bounded_source_cap_lsc`; the original interface
`bounded_source_cap`). It attains a real minimum and has a globally finite conjugate
(`bounded_source_finite_conjugate`),
whose real representative `ψ` is convex, `L`-Lipschitz and continuous, with `exp(−ψ)` Bochner
integrable, `∫ exp(−ψ) = 1`
and `weightedMeasure volume ψ` a probability measure (`bounded_source_lipschitz_primal`);
consequences for the density
`exp(−ψ)` (Fenchel contact at the origin, Lipschitz envelope, positivity, midpoint log-concavity):
`bounded_source_real_density_client`. The source inputs are only `μ`, its isotropy, `L` and the
almost-everywhere bound.

This is a weak normalized convex Lipschitz primal linked to the source law, a support toward the
moment map of
Cordero-Erausquin–Klartag Theorem 2 and Letwin, arXiv:2607.24164v1, Lemmas 2.1–2.2. Not provided:
the Euler–Lagrange
identification, the gradient pushforward `(∇ψ)_# e^{−ψ} = μ`, smoothness, a positive definite
Hessian, the gradient
diffeomorphism, the Monge–Ampère equation, Letwin Theorem 2.5.
-/

@[expose] public section

noncomputable section

namespace FunctionalInequalities.KLS.CEK

open MeasureTheory Set Metric
open scoped ENNReal Topology RealInnerProductSpace

open FunctionalInequalities
open FunctionalInequalities.Analysis
open FunctionalInequalities.KLS
open FunctionalInequalities.Probability
open FunctionalInequalities.Probability.MomentMeasure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Strengthening of the cap-only source construction. The LSC input for the
cap helper is obtained from this very CEK optimizer, not supplied by the caller.
The original admissibility, mass-one and all-competitor conclusions are retained. -/
theorem bounded_source_cap_lsc
    (μ : ProbabilityMeasure E) (hμ : KLS.Isotropic μ) (L : NNReal)
    (hL : ∀ᵐ y ∂(μ : Measure E), ‖y‖ ≤ (L : ℝ)) :
    ∃ q : E → EReal,
      ConvexPotential q ∧
      LowerSemicontinuous q ∧
      PotentialIntegrable q (μ : Measure E) ∧
      (∀ y, q y ≠ ⊤ → y ∈ closedBall (0 : E) (L : ℝ)) ∧
      mass (volume : Measure E) (legendre q) = 1 ∧
      ∀ f : E → EReal, PotentialIntegrable f (μ : Measure E) →
        variationalFunctional (volume : Measure E) (μ : Measure E) f ≤
          variationalFunctional (volume : Measure E) (μ : Measure E) q := by
  classical
  have hfirst : Integrable (fun x : E => x) (μ : Measure E) :=
    hμ.memLp_two.integrable (by norm_num)
  have hinj : Function.Injective (Covariance.operator (μ : Measure E)) := by
    intro x y hxy
    rw [hμ.covariance_identity] at hxy
    simpa only [ContinuousLinearMap.id_apply] using hxy
  have hsub :
      ∀ V : Submodule ℝ E, (μ : Measure E) (V : Set E)ᶜ = 0 → V = ⊤ := by
    intro V hV
    have hfull : Probability.affineSupport μ = ⊤ :=
      Probability.affineSupport_eq_top_of_covariance_injective μ hμ.memLp_two hinj
    let A : AffineSubspace ℝ E := AffineSubspace.mk' (0 : E) V
    have hAe : ∀ᵐ x ∂(μ : Measure E), x ∈ A := by
      filter_upwards [hV] with x hx
      simpa [A, AffineSubspace.mem_mk'] using hx
    have hle : Probability.affineSupport μ ≤ A :=
      Probability.affineSupport_le_of_ae_mem μ A A.isClosed_of_finiteDimensional hAe
    have hAtop : A = ⊤ := by
      rw [hfull] at hle
      exact top_unique hle
    apply top_unique
    intro x hx
    have hxA : x ∈ A := by
      rw [hAtop]
      trivial
    simpa [A, AffineSubspace.mem_mk'] using hxA
  obtain ⟨q0, hq0conv, hq0lsc, hq0pot, hq0mass, hq0max⟩ :=
    KLS.CEK.exists_variational_maximum
      (volume : Measure E) (μ : Measure E) hsub hfirst hμ.mean_zero
  let q : E → EReal := closedBallCap q0 L
  have hqlsc : LowerSemicontinuous q :=
    closedBallCap_lowerSemicontinuous q0 L hq0lsc
  have hqeq : q =ᵐ[(μ : Measure E)] q0 := by
    filter_upwards [hL] with y hy
    have hyB : y ∈ closedBall (0 : E) (L : ℝ) := by
      simpa [mem_closedBall] using hy
    simp [q, closedBallCap, hyB]
  have hqconv : ConvexPotential q := by
    refine ⟨?_, ?_⟩
    · intro x
      by_cases hx : x ∈ closedBall (0 : E) (L : ℝ)
      · simpa [q, closedBallCap, hx] using hq0conv.1 x
      · simp [q, closedBallCap, hx]
    · intro p hp r hr a b ha hb hab
      have hpB : p.1 ∈ closedBall (0 : E) (L : ℝ) := by
        by_contra hpB
        have htop : (⊤ : EReal) ≤ (p.2 : EReal) := by
          change
            (if p.1 ∈ closedBall (0 : E) (L : ℝ) then q0 p.1 else ⊤) ≤
              (p.2 : EReal) at hp
          rw [ite_eq_right hpB] at hp
          exact hp
        exact (not_le_of_gt (EReal.coe_lt_top p.2)) htop
      have hrB : r.1 ∈ closedBall (0 : E) (L : ℝ) := by
        by_contra hrB
        have htop : (⊤ : EReal) ≤ (r.2 : EReal) := by
          change
            (if r.1 ∈ closedBall (0 : E) (L : ℝ) then q0 r.1 else ⊤) ≤
              (r.2 : EReal) at hr
          rw [ite_eq_right hrB] at hr
          exact hr
        exact (not_le_of_gt (EReal.coe_lt_top r.2)) htop
      have hp0 : q0 p.1 ≤ (p.2 : EReal) := by
        change
          (if p.1 ∈ closedBall (0 : E) (L : ℝ) then q0 p.1 else ⊤) ≤
            (p.2 : EReal) at hp
        rw [ite_eq_left hpB] at hp
        exact hp
      have hr0 : q0 r.1 ≤ (r.2 : EReal) := by
        change
          (if r.1 ∈ closedBall (0 : E) (L : ℝ) then q0 r.1 else ⊤) ≤
            (r.2 : EReal) at hr
        rw [ite_eq_left hrB] at hr
        exact hr
      have habB : a • p.1 + b • r.1 ∈ closedBall (0 : E) (L : ℝ) :=
        (convex_closedBall (0 : E) (L : ℝ)) hpB hrB ha hb hab
      change
        (if a • p.1 + b • r.1 ∈ closedBall (0 : E) (L : ℝ) then
            q0 (a • p.1 + b • r.1)
          else ⊤) ≤
          (↑a : EReal) * ↑p.2 + (↑b : EReal) * ↑r.2
      rw [ite_eq_left habB]
      exact hq0conv.2 hp0 hr0 ha hb hab
  have hqpot : PotentialIntegrable q (μ : Measure E) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      by_cases hx : x ∈ closedBall (0 : E) (L : ℝ)
      · simpa [q, closedBallCap, hx] using hq0conv.1 x
      · simp [q, closedBallCap, hx]
    · filter_upwards [hqeq, hq0pot.2.1] with x hx hxf
      rw [hx]
      exact hxf
    · have hto :
          (fun x => (q x).toReal) =ᵐ[(μ : Measure E)]
            (fun x => (q0 x).toReal) := by
        filter_upwards [hqeq] with x hx
        rw [hx]
      exact hq0pot.2.2.congr hto.symm
  have hqdom : ∀ y, q y ≠ ⊤ → y ∈ closedBall (0 : E) (L : ℝ) := by
    intro y hy
    by_contra hyB
    apply hy
    simp [q, closedBallCap, hyB]
  have hqle : ∀ x, q0 x ≤ q x := by
    intro x
    by_cases hx : x ∈ closedBall (0 : E) (L : ℝ)
    · simp [q, closedBallCap, hx]
    · simp [q, closedBallCap, hx]
  have hmassmono :
      mass (volume : Measure E) (legendre q0) ≤
        mass (volume : Measure E) (legendre q) :=
    mass_legendre_mono (volume : Measure E) hqle
  have hqint :
      (∫ x, (q x).toReal ∂(μ : Measure E)) =
        ∫ x, (q0 x).toReal ∂(μ : Measure E) := by
    have hto :
        (fun x => (q x).toReal) =ᵐ[(μ : Measure E)]
          (fun x => (q0 x).toReal) := by
      filter_upwards [hqeq] with x hx
      rw [hx]
    exact integral_congr_ae hto
  have hmassq : mass (volume : Measure E) (legendre q) = 1 := by
    have hupper := hq0max q hqpot
    unfold variationalFunctional at hupper
    rw [hqint, hq0mass, ENNReal.log_one] at hupper
    have hlogupper :
        ENNReal.log (mass (volume : Measure E) (legendre q)) ≤ 0 := by
      let I : ℝ := ∫ x, (q0 x).toReal ∂(μ : Measure E)
      have hcancel :
          ENNReal.log (mass (volume : Measure E) (legendre q)) + ((-I : ℝ) : EReal) ≤
            (0 : EReal) + ((-I : ℝ) : EReal) := by
        simpa only [sub_eq_add_neg, EReal.coe_neg, I] using hupper
      exact (EReal.addLECancellable_coe (-I)).add_le_add_iff_right.mp hcancel
    have hloglower :
        0 ≤ ENNReal.log (mass (volume : Measure E) (legendre q)) := by
      have h := ENNReal.log_monotone hmassmono
      rw [hq0mass, ENNReal.log_one] at h
      exact h
    apply ENNReal.log_injective
    apply le_antisymm
    · simpa only [ENNReal.log_one] using hlogupper
    · simpa only [ENNReal.log_one] using hloglower
  have hqmax :
      ∀ f : E → EReal, PotentialIntegrable f (μ : Measure E) →
        variationalFunctional (volume : Measure E) (μ : Measure E) f ≤
          variationalFunctional (volume : Measure E) (μ : Measure E) q := by
    intro f hf
    have hf0 := hq0max f hf
    have hq0eq :
        variationalFunctional (volume : Measure E) (μ : Measure E) q =
          variationalFunctional (volume : Measure E) (μ : Measure E) q0 := by
      unfold variationalFunctional
      rw [hmassq, hq0mass, hqint]
    rw [hq0eq]
    exact hf0
  exact ⟨q, hqconv, hqlsc, hqpot, hqdom, hmassq, hqmax⟩

/-- The original cap-only interface, retained at precisely its original scope.
Its statement does not expose LSC or finite-conjugate conclusions. -/
theorem bounded_source_cap
    (μ : ProbabilityMeasure E) (hμ : KLS.Isotropic μ) (L : NNReal)
    (hL : ∀ᵐ y ∂(μ : Measure E), ‖y‖ ≤ (L : ℝ)) :
    ∃ q : E → EReal,
      ConvexPotential q ∧
      PotentialIntegrable q (μ : Measure E) ∧
      (∀ y, q y ≠ ⊤ → y ∈ closedBall (0 : E) (L : ℝ)) ∧
      mass (volume : Measure E) (legendre q) = 1 ∧
      ∀ f : E → EReal, PotentialIntegrable f (μ : Measure E) →
        variationalFunctional (volume : Measure E) (μ : Measure E) f ≤
          variationalFunctional (volume : Measure E) (μ : Measure E) q := by
  obtain ⟨q, hc, _hlsc, hi, hd, hm, hmax⟩ :=
    bounded_source_cap_lsc μ hμ L hL
  exact ⟨q, hc, hi, hd, hm, hmax⟩

/-- Source-derived compact minimum and globally finite actual conjugate.
The only source inputs are the bundled isotropic probability and its AE norm
bound. The real primal is defined after global finiteness has been established.
This endpoint does not yet assert real convexity, Lipschitz continuity, or the
Bochner exponential-integrability and probability-law bridge. -/
theorem bounded_source_finite_conjugate
    (μ : ProbabilityMeasure E) (hμ : KLS.Isotropic μ) (L : NNReal)
    (hL : ∀ᵐ y ∂(μ : Measure E), ‖y‖ ≤ (L : ℝ)) :
    ∃ (q : E → EReal) (a : E) (m : ℝ) (ψ : E → ℝ),
      ConvexPotential q ∧
      LowerSemicontinuous q ∧
      PotentialIntegrable q (μ : Measure E) ∧
      (∀ y, q y ≠ ⊤ → y ∈ closedBall (0 : E) (L : ℝ)) ∧
      a ∈ closedBall (0 : E) (L : ℝ) ∧
      q a = (m : EReal) ∧
      (∀ y, (m : EReal) ≤ q y) ∧
      (∀ x, legendre q x ≠ ⊤ ∧ legendre q x ≠ ⊥) ∧
      (∀ x, legendre q x ≤ (((L : ℝ) * ‖x‖ - m : ℝ) : EReal)) ∧
      ψ = (fun x => (legendre q x).toReal) ∧
      (∀ x, legendre q x = (ψ x : EReal)) ∧
      mass (volume : Measure E) (legendre q) = 1 ∧
      ∀ f : E → EReal, PotentialIntegrable f (μ : Measure E) →
        variationalFunctional (volume : Measure E) (μ : Measure E) f ≤
          variationalFunctional (volume : Measure E) (μ : Measure E) q := by
  classical
  obtain ⟨q, hqconv, hqlsc, hqpot, hqdom, hqmass, hqmax⟩ :=
    bounded_source_cap_lsc μ hμ L hL
  have hμne : (μ : Measure E) ≠ 0 := by
    intro hzero
    have hprob : (μ : Measure E) univ = 1 := measure_univ
    rw [hzero] at hprob
    simp at hprob
  have hqfinite : ∃ y, q y ≠ ⊤ :=
    potentialIntegrable_exists_finite q hμne hqpot
  obtain ⟨a, haB, m, ham, hfloor⟩ :=
    exists_real_global_minimum_of_bounded_domain
      q L hqpot.1 hqfinite hqlsc hqdom
  have hfinite : ∀ x, legendre q x ≠ ⊤ ∧ legendre q x ≠ ⊥ :=
    legendre_finite_of_bounded_domain q L m hqpot.1 hqfinite hqdom hfloor
  let ψ : E → ℝ := fun x => (legendre q x).toReal
  have hψ : ∀ x, legendre q x = (ψ x : EReal) := by
    intro x
    exact (EReal.coe_toReal (hfinite x).1 (hfinite x).2).symm
  refine ⟨q, a, m, ψ, hqconv, hqlsc, hqpot, hqdom, haB, ham, hfloor,
    hfinite, ?_, rfl, hψ, hqmass, hqmax⟩
  intro x
  exact legendre_le_of_real_lower_bound q L m hqpot.1 hqdom hfloor x

/-- Weak source-law-linked normalized primal. Every new conclusion is derived
from `bounded_source_finite_conjugate` for this actual bounded isotropic source.
No convexity, Lipschitz, integrability, normalization, or optimizer premise is
added to the source interface. The original finite-conjugate data are retained. -/
theorem bounded_source_lipschitz_primal
    (μ : ProbabilityMeasure E) (hμ : KLS.Isotropic μ) (L : NNReal)
    (hL : ∀ᵐ y ∂(μ : Measure E), ‖y‖ ≤ (L : ℝ)) :
    ∃ (q : E → EReal) (a : E) (m : ℝ) (ψ : E → ℝ),
      ConvexPotential q ∧
      LowerSemicontinuous q ∧
      PotentialIntegrable q (μ : Measure E) ∧
      (∀ y, q y ≠ ⊤ → y ∈ closedBall (0 : E) (L : ℝ)) ∧
      a ∈ closedBall (0 : E) (L : ℝ) ∧
      q a = (m : EReal) ∧
      (∀ y, (m : EReal) ≤ q y) ∧
      (∀ x, legendre q x ≠ ⊤ ∧ legendre q x ≠ ⊥) ∧
      (∀ x, legendre q x ≤ (((L : ℝ) * ‖x‖ - m : ℝ) : EReal)) ∧
      ψ = (fun x => (legendre q x).toReal) ∧
      (∀ x, legendre q x = (ψ x : EReal)) ∧
      mass (volume : Measure E) (legendre q) = 1 ∧
      ConvexOn ℝ (univ : Set E) ψ ∧
      LipschitzWith L ψ ∧
      Continuous ψ ∧
      Integrable (fun x => Real.exp (-ψ x)) (volume : Measure E) ∧
      (∫ x, Real.exp (-ψ x) ∂(volume : Measure E)) = 1 ∧
      IsProbabilityMeasure
        (weightedMeasure (volume : Measure E) (fun x => (ψ x : EReal))) ∧
      ∀ f : E → EReal, PotentialIntegrable f (μ : Measure E) →
        variationalFunctional (volume : Measure E) (μ : Measure E) f ≤
          variationalFunctional (volume : Measure E) (μ : Measure E) q := by
  obtain ⟨q, a, m, ψ, hqconv, hqlsc, hqpot, hqdom, haB, ham, hfloor,
    hfinite, hupper, hdef, hψ, hqmass, hqmax⟩ :=
    bounded_source_finite_conjugate μ hμ L hL
  have hconv : ConvexOn ℝ (univ : Set E) ψ :=
    real_convexOn_legendre q ψ hψ
  have hlip : LipschitzWith L ψ :=
    lipschitzWith_real_legendre q L ψ hqpot.1 hqdom hψ
  obtain ⟨hexp, hint, hprob⟩ :=
    real_legendre_normalization (volume : Measure E) q ψ hψ hqmass
  exact ⟨q, a, m, ψ, hqconv, hqlsc, hqpot, hqdom, haB, ham, hfloor,
    hfinite, hupper, hdef, hψ, hqmass, hconv, hlip, hlip.continuous,
    hexp, hint, hprob, hqmax⟩

/-- A real-valued source-law client: the normalized optimizer density has
Fenchel contact at the origin, a sharp origin-relative Lipschitz envelope,
strict positivity, an exponential lower envelope, and midpoint log-concavity.
This is not a moment-pushforward or regularity theorem. -/
theorem bounded_source_real_density_client
    (μ : ProbabilityMeasure E) (hμ : KLS.Isotropic μ) (L : NNReal)
    (hL : ∀ᵐ y ∂(μ : Measure E), ‖y‖ ≤ (L : ℝ)) :
    ∃ (q : E → EReal) (a : E) (m : ℝ) (ψ : E → ℝ),
      PotentialIntegrable q (μ : Measure E) ∧
      (∀ x, legendre q x = (ψ x : EReal)) ∧
      q a = (m : EReal) ∧
      ψ 0 = -m ∧
      (∀ x, inner ℝ a x - m ≤ ψ x ∧
        |ψ x + m| ≤ (L : ℝ) * ‖x‖) ∧
      Integrable (fun x => Real.exp (-ψ x)) (volume : Measure E) ∧
      (∫ x, Real.exp (-ψ x) ∂(volume : Measure E)) = 1 ∧
      IsProbabilityMeasure
        (weightedMeasure (volume : Measure E) (fun x => (ψ x : EReal))) ∧
      (∀ x, 0 < Real.exp (-ψ x) ∧
        Real.exp (m - (L : ℝ) * ‖x‖) ≤ Real.exp (-ψ x)) ∧
      (∀ x y, Real.exp (-ψ x) * Real.exp (-ψ y) ≤
        Real.exp (-ψ ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y)) ^ 2) ∧
      mass (volume : Measure E) (legendre q) = 1 ∧
      ∀ f : E → EReal, PotentialIntegrable f (μ : Measure E) →
        variationalFunctional (volume : Measure E) (μ : Measure E) f ≤
          variationalFunctional (volume : Measure E) (μ : Measure E) q := by
  obtain ⟨q, a, m, ψ, _hc, _hlsc, hpot, _hdom, _ha, ham, _hfloor,
    _hfinite, hupper, _hdef, hψ, hmass, hconv, hlip, _hcont,
    hexp, hint, hprob, hmax⟩ :=
    bounded_source_lipschitz_primal μ hμ L hL
  have hsupport : ∀ x, inner ℝ a x - m ≤ ψ x :=
    fun x => real_legendre_fenchel q ψ hψ a m ham x
  have hzero : ψ 0 = -m := by
    apply le_antisymm
    · have hu := hupper (0 : E)
      rw [hψ (0 : E)] at hu
      have hu' := EReal.coe_le_coe_iff.mp hu
      simpa only [norm_zero, mul_zero, zero_sub] using hu'
    · simpa using hsupport (0 : E)
  have henv : ∀ x, |ψ x + m| ≤ (L : ℝ) * ‖x‖ := by
    intro x
    have hd := hlip.dist_le_mul x (0 : E)
    simpa only [dist_eq_norm, Real.norm_eq_abs, hzero,
      sub_neg_eq_add, sub_zero] using hd
  refine ⟨q, a, m, ψ, hpot, hψ, ham, hzero, ?_, hexp, hint,
    hprob, ?_, ?_, hmass, hmax⟩
  · intro x
    exact ⟨hsupport x, henv x⟩
  · intro x
    refine ⟨Real.exp_pos _, Real.exp_le_exp.mpr ?_⟩
    have hu : ψ x + m ≤ (L : ℝ) * ‖x‖ :=
      (le_abs_self (ψ x + m)).trans (henv x)
    linarith only [hu]
  · intro x y
    have hc : ψ ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) ≤
        (1 / 2 : ℝ) * ψ x + (1 / 2 : ℝ) * ψ y := by
      simpa only [smul_eq_mul] using
        (hconv.2 (mem_univ x) (mem_univ y)
          (show (0 : ℝ) ≤ 1 / 2 by norm_num)
          (show (0 : ℝ) ≤ 1 / 2 by norm_num)
          (by norm_num))
    have hlin : -ψ x + -ψ y ≤
        -ψ ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) +
        -ψ ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) := by
      linarith only [hc]
    have he := Real.exp_le_exp.mpr hlin
    simpa only [Real.exp_add, pow_two] using he

end FunctionalInequalities.KLS.CEK
