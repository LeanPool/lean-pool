/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Energy.LocalSlope.Basic
public import LeanPool.KLS.FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.Measurable

/-!
# Local metric slope and the canonical Hilbert gradient

Five proved interfaces for `thm:smooth-lipschitz-constant-equivalence`.
Source: the existing `Energy.LocalSlope.apply` definition and Blueprint shared analytic bridges.
Read the pointwise identity first, then its almost-everywhere consequence, extended energy
identity, finite-energy domain characterization, and the real-integral form of the energy
(`energy_eq_integral_gradient`).


The pointwise result needs only differentiability at the point and includes the zero space.
For locally Lipschitz tests, absolute continuity transfers the proved Rademacher statement
from a Haar reference measure to the probability law. Energy equality allows infinity;
only the admissibility characterization adds L2 membership. No factor of one half is used.
These declarations do not redefine the target, slope, gradient or admissibility predicate.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace FunctionalInequalities.Energy.LocalSlope

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Step 1: the one-moving-point local slope equals the derivative norm at a differentiable
point, expressed through the canonical Hilbert gradient. No nontriviality premise is needed. -/
theorem apply_eq_norm_gradient
    (f : E → ℝ) (x : E) (hf : DifferentiableAt ℝ f x) :
    apply f x = ENNReal.ofReal ‖gradient f x‖ := by
  rw [Energy.Euclidean.LipschitzApproximation.norm_gradient_eq_norm_fderiv]
  apply le_antisymm
  · apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    have hεr : 0 < (ε : ℝ) := by exact_mod_cast hε
    obtain ⟨r, hr, hrem⟩ := Metric.eventually_nhds_iff_ball.mp
      (hf.hasFDerivAt.isLittleO.bound hεr)
    calc
      apply f x ≤ ENNReal.ofReal (‖fderiv ℝ f x‖ + ε) := by
        unfold apply
        refine iInf_le_of_le r (iInf_le_of_le hr ?_)
        refine iSup_le fun y => iSup_le fun hy => ?_
        apply ENNReal.ofReal_le_ofReal
        by_cases hyx : y = x
        · subst y
          simp only [dist_self, div_zero]
          positivity
        · apply (div_le_iff₀ (dist_pos.mpr hyx)).2
          rw [dist_eq_norm, dist_eq_norm]
          calc
            ‖f y - f x‖ = ‖(f y - f x - (fderiv ℝ f x) (y - x)) +
                (fderiv ℝ f x) (y - x)‖ := by rw [sub_add_cancel]
            _ ≤ ‖f y - f x - (fderiv ℝ f x) (y - x)‖ +
                ‖(fderiv ℝ f x) (y - x)‖ := norm_add_le _ _
            _ ≤ ε * ‖y - x‖ + ‖fderiv ℝ f x‖ * ‖y - x‖ :=
              add_le_add (hrem y hy) ((fderiv ℝ f x).le_opNorm _)
            _ = (‖fderiv ℝ f x‖ + ε) * ‖y - x‖ := by ring
      _ = ENNReal.ofReal ‖fderiv ℝ f x‖ + ε := by
        have hadd (a : ℝ) (ha : 0 ≤ a) :
            ENNReal.ofReal (a + (ε : ℝ)) = ENNReal.ofReal a + (ε : ENNReal) := by
          convert! ENNReal.ofReal_add ha ε.2 using 1
          simp
        exact hadd _ (by positivity)
  · unfold apply
    refine le_iInf fun r => le_iInf fun hr => ?_
    let S : ENNReal := ⨆ (y : E) (_ : dist y x < r),
      ENNReal.ofReal (dist (f y) (f x) / dist y x)
    change ENNReal.ofReal ‖fderiv ℝ f x‖ ≤ S
    by_cases hS : S = ⊤
    · simp [hS]
    apply (ENNReal.ofReal_le_iff_le_toReal hS).2
    apply hf.hasFDerivAt.le_of_lip' ENNReal.toReal_nonneg
    filter_upwards [Metric.ball_mem_nhds x hr] with y hy
    by_cases hyx : y = x
    · subst y
      simp
    · have hq : ENNReal.ofReal (dist (f y) (f x) / dist y x) ≤ S :=
        le_iSup_of_le y (le_iSup_of_le hy le_rfl)
      have := (ENNReal.ofReal_le_iff_le_toReal hS).1 hq
      have := (div_le_iff₀ (dist_pos.mpr hyx)).1 this
      simpa only [dist_eq_norm] using this

variable [MeasurableSpace E] [BorelSpace E] [sct : SecondCountableTopology E]
  [FiniteDimensional ℝ E] (ν : ProbabilityMeasure E) (m : Measure E)
  [Measure.IsAddHaarMeasure m]

section GradientIdentification

omit sct
/-- Step 2: Rademacher and absolute continuity identify the two pointwise energies almost
everywhere for locally Lipschitz tests, with no integrability or density lower bound premise. -/
theorem apply_ae_eq_norm_gradient (hν : (ν : Measure E) ≪ m)
    (f : E → ℝ) (hf : LocallyLipschitz f) :
    (fun x ↦ apply f x) =ᵐ[(ν : Measure E)]
      (fun x ↦ ENNReal.ofReal ‖gradient f x‖) := by
  filter_upwards [hν.ae_le
    (Energy.Euclidean.LipschitzApproximation.ae_differentiableAt_of_locallyLipschitz hf m)]
    with x hx
  exact apply_eq_norm_gradient f x hx

/-- Step 3: equality of the extended local-slope and gradient energies, also when infinite.
The lintegral keeps nonintegrable functions from acquiring a spurious zero energy. -/
theorem energy_eq_lintegral_gradient (hν : (ν : Measure E) ≪ m)
    (f : E → ℝ) (hf : LocallyLipschitz f) :
    energy ν f = ∫⁻ x, (ENNReal.ofReal ‖gradient f x‖) ^ 2 ∂(ν : Measure E) := by
  unfold energy
  apply lintegral_congr_ae
  filter_upwards [apply_ae_eq_norm_gradient ν m hν f hf] with x hx
  rw [hx]

end GradientIdentification

/-- Step 4: the exact existing literature test domain, expressed by L2 gradient membership.
This is a theorem about the existing definition, not an additional admissibility assumption. -/
theorem admissible_iff_memLp_gradient (hν : (ν : Measure E) ≪ m) (f : E → ℝ) :
    Admissible ν f ↔
      LocallyLipschitz f ∧ MemLp f 2 (ν : Measure E) ∧ MemLp (gradient f) 2 (ν : Measure E) := by
  have hmem : MemLp (gradient f) 2 (ν : Measure E) ↔
      (∫⁻ x, (ENNReal.ofReal ‖gradient f x‖) ^ 2 ∂(ν : Measure E)) ≠ ⊤ := by
    rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)
      (Energy.Euclidean.LipschitzApproximation.aestronglyMeasurable_gradient f _)]
    simp [← ofReal_norm, lt_top_iff_ne_top]
  constructor
  · intro h
    refine ⟨h.locallyLipschitz, h.memLp_two, hmem.mpr ?_⟩
    rw [← energy_eq_lintegral_gradient ν m hν f h.locallyLipschitz]
    exact h.finite_energy
  · rintro ⟨hlip, hL2, hgrad⟩
    refine ⟨hlip, hL2, ?_⟩
    rw [energy_eq_lintegral_gradient ν m hν f hlip]
    exact hmem.mp hgrad

section RealIntegral

/-! The real-integral form of the gradient energy. The binder context reproduces the one this
theorem was elaborated in before the move, so its universe parameter, implicit type variable and
hypothesis names are unchanged. -/

universe u

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
  (ν : ProbabilityMeasure V) (m : Measure V) [m.IsAddHaarMeasure]

/-- The literature energy of a locally Lipschitz function with square-integrable gradient is the
real integral of the squared gradient norm, under absolute continuity. -/
theorem energy_eq_integral_gradient
    (hac : (ν : Measure V) ≪ m) (f : V → ℝ) (hf : LocallyLipschitz f)
    (hg : MemLp (gradient f) 2 (ν : Measure V)) :
    energy ν f = ENNReal.ofReal (∫ x, ‖gradient f x‖ ^ 2 ∂(ν : Measure V)) := by
  rw [energy_eq_lintegral_gradient ν m hac f hf,
    ofReal_integral_eq_lintegral_ofReal
      ((memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg)
      (ae_of_all _ fun x ↦ sq_nonneg ‖gradient f x‖)]
  congr 1
  funext x
  rw [ENNReal.ofReal_pow (norm_nonneg _) 2]

end RealIntegral

end FunctionalInequalities.Energy.LocalSlope
