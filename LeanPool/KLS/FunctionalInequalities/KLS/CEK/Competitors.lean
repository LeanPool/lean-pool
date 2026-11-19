/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Probability.MomentMeasure.Normalization
public import LeanPool.KLS.FunctionalInequalities.Probability.MomentMeasure.Truncation
public import LeanPool.KLS.FunctionalInequalities.Probability.MomentMeasure.Coercivity
public import LeanPool.KLS.FunctionalInequalities.Probability.MomentMeasure.Baseline

/-!
# CEK Proposition 12: reduction of every admissible competitor

Cordero-Erausquin–Klartag, *Moment measures* (arXiv:1304.0630v1), proof of Proposition 12: every
admissible competitor
is reduced, up to epsilon, to a normalized convex one; a finite real ceiling over all admissible
competitors and a
finite norm baseline bound the variational range.
-/

@[expose] public section

noncomputable section

namespace FunctionalInequalities.KLS.CEK

open FunctionalInequalities.Analysis
open FunctionalInequalities.Probability
open FunctionalInequalities.Probability.MomentMeasure

section
-- Normalized competitors and a uniform upper bound for the functional.

open MeasureTheory Filter Set
open scoped ENNReal Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- Actual reduction of every admissible source competitor: truncate, take the
actual biconjugate, derive its domain interior, produce a touching plane and
subtract it. Every normalization and the epsilon value comparison is proved. -/
theorem exists_normalized_competitor (dx μ : Measure E) [dx.IsAddHaarMeasure]
    [IsProbabilityMeasure μ] (hsub : ∀ V : Submodule ℝ E, μ (V : Set E)ᶜ = 0 → V = ⊤)
    (hfirst : Integrable (fun x : E => x) μ) (hbar : ∫ x, x ∂μ = 0) (f : E → EReal)
    (hf : PotentialIntegrable f μ) (ε : ℝ) (hε : 0 < ε) :
    ∃ ψ : E → EReal,
      ConvexPotential ψ ∧
        PotentialIntegrable ψ μ ∧
          (∀ x, 0 ≤ ψ x) ∧
            ψ 0 = 0 ∧
              variationalFunctional dx μ f ≤ variationalFunctional dx μ ψ + (ε : EReal) := by
  have hμ : μ ≠ 0 := by
    intro hz
    have hu : μ univ = 1 := measure_univ
    simp only [hz, FunLike.coe_zero, Pi.zero_apply, zero_ne_one] at hu
  have h0 :=
    FunctionalInequalities.Probability.zero_mem_interior_convexHull_support_of_integral_eq_zero
      μ hμ hsub hfirst hbar
  obtain ⟨n, _hn, hc, _hls, hp, hvalue⟩ :=
    exists_convexified_lowerTruncate_variational_le_add dx f hμ hf ε hε
  let c := legendre (legendre (lowerTruncate f (n : ℝ)))
  have hlower : ∀ x, ((-(n : ℝ) : ℝ) : EReal) ≤ c x :=
    lower_bound_biconjugate _ (n : ℝ) (fun _ => le_max_right _ _)
  have hD := origin_mem_interior_domain_of_lower_bound μ h0 hfirst c hc hp (n : ℝ) hlower
  obtain ⟨a, hconv, hpot, hnn, hzero, heq⟩ :=
    exists_origin_zero_affine_of_probability dx c hp hc hD hfirst hbar
  refine ⟨affineSubtract c a (c 0).toReal, hconv, hpot, hnn, hzero, ?_⟩
  rwa [heq]
/-- A fixed finite real upper bound over ALL source admissible competitors.
The upper bound is derived by actual epsilon reduction; neither convexity of
f nor finite/positive conjugate mass nor finite functional value is assumed. -/
theorem exists_uniform_functional_upper (dx μ : Measure E) [dx.IsAddHaarMeasure]
    [IsProbabilityMeasure μ] (hsub : ∀ V : Submodule ℝ E, μ (V : Set E)ᶜ = 0 → V = ⊤)
    (hfirst : Integrable (fun x : E => x) μ) (hbar : ∫ x, x ∂μ = 0) :
    ∃ U : ℝ,
      ∀ f : E → EReal, PotentialIntegrable f μ → variationalFunctional dx μ f ≤ (U : EReal) := by
  obtain ⟨A, _hA, hc⟩ := exists_coercivity_of_centered_probability dx μ hsub hfirst hbar
  let U : ℝ :=
    Real.log A + (Module.finrank ℝ E : ℝ) * Real.log (2 * ((Module.finrank ℝ E : ℝ) + 1))
  refine ⟨U, ?_⟩
  intro f hf
  have heps : ∀ ε : ℝ, 0 < ε → variationalFunctional dx μ f ≤ ((U + ε : ℝ) : EReal) := by
    intro ε hε
    obtain ⟨ψ, hconv, hp, hnn, hzero, hvalue⟩ :=
      exists_normalized_competitor dx μ hsub hfirst hbar f hf ε hε
    have hnorm := (hc ψ hnn hzero hconv hp).2
    have hM := (lintegral_nonneg_potential ψ hp hnn).2.2
    have hreal := real_coercivity_le_uniform A (Module.finrank ℝ E) (∫ x, (ψ x).toReal ∂μ) hM
    have hψ : variationalFunctional dx μ ψ ≤ (U : EReal) :=
      hnorm.trans (EReal.coe_le_coe_iff.mpr hreal)
    simpa only [EReal.coe_add] using hvalue.trans (add_le_add hψ (le_refl (ε : EReal)))
  have ht : Tendsto (fun ε : ℝ => ((U + ε : ℝ) : EReal)) (𝓝[>] 0) (𝓝 (U : EReal)) := by
    have hc : Continuous (fun ε : ℝ => ((U + ε : ℝ) : EReal)) :=
      continuous_coe_real_ereal.comp (continuous_const.add continuous_id)
    simpa only [add_zero] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact heps ε hε

end

section
-- A finite baseline value and an upper bound for the functional.

open MeasureTheory Set Filter
open scoped ENNReal Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- Actual finite baseline and a fixed finite all-competitor upper bound.
This establishes the variational range bounds, not an optimizer. -/
theorem exists_finite_baseline_and_upper (dx μ : Measure E) [dx.IsAddHaarMeasure]
    [IsProbabilityMeasure μ] (hsub : ∀ V : Submodule ℝ E, μ (V : Set E)ᶜ = 0 → V = ⊤)
    (hfirst : Integrable (fun x : E => x) μ) (hbar : ∫ x, x ∂μ = 0) :
    ∃ L U : ℝ,
      PotentialIntegrable (fun x : E => (‖x‖ : EReal)) μ ∧
        variationalFunctional dx μ (fun x : E => (‖x‖ : EReal)) = (L : EReal) ∧
          L ≤ U ∧
            ∀ f : E → EReal,
              PotentialIntegrable f μ → variationalFunctional dx μ f ≤ (U : EReal) := by
  obtain ⟨_hc, hp, L, hL⟩ := norm_baseline_finite dx μ hfirst
  obtain ⟨U, hU⟩ := exists_uniform_functional_upper dx μ hsub hfirst hbar
  refine ⟨L, U, hp, hL, ?_, hU⟩
  have h := hU (fun x : E => (‖x‖ : EReal)) hp
  rw [hL] at h
  exact EReal.coe_le_coe_iff.mp h

end

end FunctionalInequalities.KLS.CEK
