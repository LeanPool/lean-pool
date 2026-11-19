/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Regular.Isotropic
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Isotropic
public import LeanPool.KLS.FunctionalInequalities.Poincare.CovarianceGradient.Transport

/-!
# Conditional Poincaré transfer from isotropic regular laws to regular laws

Bizeul–Klartag–Lehec arXiv:2610.05474v1, Section 2 (p. 5): a universal Poincaré bound `K` for
isotropic regular laws (an explicit hypothesis here; the paper's Theorem 1.1 for the regular class)
gives `C_P(μ) ≤ K‖Cov μ‖` for every regular law `μ`, by centering and whitening to an isotropic
regular law (`RegularIsotropic`) and transporting the covariance energy; the envelope form
`K(1 + ‖Cov μ − Id‖)` tends to `K` along laws whose covariances tend to `Id`. No whitening-sequence
limit and no unconditional bound is asserted.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

section

namespace FunctionalInequalities.KLS.RegularPotential

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

private theorem regular_ac {V : E → ℝ} {a b : ℝ} (hV : KLS.RegularPotential V a b) :
    (hV.law : Measure E) ≪ volume :=
  hV.logConcave_law.absolutelyContinuous_of_interior_support_nonempty volume hV.interior_support_law

private theorem regular_frontier {V : E → ℝ} {a b : ℝ} (hV : KLS.RegularPotential V a b) :
    (hV.law : Measure E) (frontier (hV.law : Measure E).support) = 0 := by
  rw [support_law hV, frontier_univ, measure_empty]

private theorem covariance_constant_eq_localSlope {V : E → ℝ} {a b : ℝ}
    (hV : KLS.RegularPotential V a b) (hiso : KLS.Isotropic hV.law) :
    Poincare.L2Energy.optimalConstant hV.law (Energy.CovarianceGradient.relaxation hV.law) =
      Poincare.LocalSlope.Intrinsic.optimalConstant hV.law := by
  rw [Energy.CovarianceGradient.relaxation_eq_lipschitz hV.law volume (regular_ac hV)
    (regular_frontier hV) hiso.covariance_identity,
    ← Poincare.SmoothTest.constant_eq_lipschitz hV.law volume (regular_ac hV) (regular_frontier hV)]
  exact hV.logConcave_law.smoothTest_constant_eq_localSlope

private theorem localSlope_le_covariance_norm_of_covariance_constant {V : E → ℝ} {a b : ℝ}
    (hV : KLS.RegularPotential V a b) {K : NNReal}
    (hK : Poincare.L2Energy.optimalConstant hV.law (Energy.CovarianceGradient.relaxation hV.law) ≤
      K) :
    Poincare.LocalSlope.Intrinsic.optimalConstant hV.law ≤
      (K : ENNReal) * ENNReal.ofReal ‖Covariance.operator (hV.law : Measure E)‖ := by
  have hlit : Poincare.LocalSlope.Intrinsic.optimalConstant hV.law =
      Poincare.L2Energy.optimalConstant hV.law
        (Energy.LipschitzGradient.relaxation hV.law volume (regular_ac hV)) := by
    rw [← hV.logConcave_law.smoothTest_constant_eq_localSlope,
      Poincare.SmoothTest.constant_eq_lipschitz hV.law volume (regular_ac hV) (regular_frontier hV)]
  have hh := (Poincare.L2Energy.holds_iff_constant_le hV.law
    (Energy.CovarianceGradient.relaxation hV.law) K).mpr hK
  have hcmp : ∀ f : (Energy.LipschitzGradient.relaxation hV.law volume (regular_ac hV)).domain,
      Energy.CovarianceGradient.relaxation hV.law f.1 ≤
        (‖Covariance.operator (hV.law : Measure E)‖₊ : ENNReal) *
          Energy.LipschitzGradient.relaxation hV.law volume (regular_ac hV) f.1 :=
    fun f => Energy.CovarianceGradient.relaxation_le_mul_lipschitz hV.law volume
      (regular_ac hV) (regular_frontier hV) f.1 ((Energy.Functional.mem_domain _ _).mp f.2)
  have h := Poincare.L2Energy.constant_le_mul_of_energy_le_mul hh hcmp
  rw [hlit]
  refine h.trans (le_of_eq ?_)
  rw [ENNReal.coe_mul, mul_comm, ← coe_nnNorm, ENNReal.ofReal_coe_nnreal]

/--
**Conditional Poincaré transfer** (BKL Section 2, p. 5): if every isotropic regular law (with
positive
upper curvature) has literature constant `≤ K`, then every regular law has `C_P ≤ K·‖Cov‖` (center
and
whiten by `exists_regular_isotropic`, then transport the covariance energy). The universal bound is
a
hypothesis, not asserted. -/
theorem localSlope_le_covariance_norm {K : NNReal}
    (hBound :
      ∀ {U : E → ℝ} {α β : ℝ} (hU : KLS.RegularPotential U α β),
        0 < β →
          KLS.Isotropic hU.law → Poincare.LocalSlope.Intrinsic.optimalConstant hU.law ≤
            (K : ENNReal))
    {V : E → ℝ} {a b : ℝ} (hV : KLS.RegularPotential V a b) :
    Poincare.LocalSlope.Intrinsic.optimalConstant hV.law ≤
      (K : ENNReal) * ENNReal.ofReal ‖Covariance.operator (hV.law : Measure E)‖ := by
  obtain ⟨W, c, U, α, β, hU, _, _, _, _, _, hβ, hiso, hlaw⟩ := exists_regular_isotropic hV
  have hnew :
    Poincare.L2Energy.optimalConstant hU.law (Energy.CovarianceGradient.relaxation hU.law) ≤
      (K : ENNReal) := by
    rw [covariance_constant_eq_localSlope hU hiso]
    exact hBound hU hβ hiso
  rw [hlaw, Poincare.CovarianceGradient.constant_mapContinuousLinearEquiv,
    Poincare.CovarianceGradient.constant_translateLaw] at hnew
  exact localSlope_le_covariance_norm_of_covariance_constant hV hnew

omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- `‖A‖ ≤ 1 + ‖A − Id‖`. -/
theorem covariance_norm_le_envelope (A : E →L[ℝ] E) :
    ‖A‖ ≤ 1 + ‖A - ContinuousLinearMap.id ℝ E‖ := by
  calc
    ‖A‖ = ‖(A - ContinuousLinearMap.id ℝ E) + ContinuousLinearMap.id ℝ E‖ := by
      rw [sub_add_cancel]
    _ ≤ ‖A - ContinuousLinearMap.id ℝ E‖ + ‖ContinuousLinearMap.id ℝ E‖ := norm_add_le _ _
    _ ≤ 1 + ‖A - ContinuousLinearMap.id ℝ E‖ := by
      linarith [ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E)]

/-- The transfer with the envelope coefficient `K (1 + ‖Cov − Id‖)`. -/
theorem localSlope_le_covariance_envelope {K : NNReal}
    (hBound :
      ∀ {U : E → ℝ} {α β : ℝ} (hU : KLS.RegularPotential U α β),
        0 < β →
          KLS.Isotropic hU.law → Poincare.LocalSlope.Intrinsic.optimalConstant hU.law ≤
            (K : ENNReal))
    {V : E → ℝ} {a b : ℝ} (hV : KLS.RegularPotential V a b) :
    Poincare.LocalSlope.Intrinsic.optimalConstant hV.law ≤
      ENNReal.ofReal
        ((K : ℝ) *
          (1 + ‖Covariance.operator (hV.law : Measure E) - ContinuousLinearMap.id ℝ E‖)) := by
  have h := localSlope_le_covariance_norm hBound hV
  rw [ENNReal.ofReal_mul K.coe_nonneg, ENNReal.ofReal_coe_nnreal]
  apply h.trans
  gcongr
  exact covariance_norm_le_envelope _

section EnvelopeCoefficients

omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- The envelope coefficient converges to `K` when the covariances converge to `Id`. -/
theorem envelope_coefficient_tendsto {ι : Type*} {l : Filter ι} {A : ι → E →L[ℝ] E}
    (K : NNReal) (hA : Filter.Tendsto A l (𝓝 (ContinuousLinearMap.id ℝ E))) :
    Filter.Tendsto (fun i => (K : ℝ) * (1 + ‖A i - ContinuousLinearMap.id ℝ E‖)) l (𝓝 (K : ℝ)) := by
  have hnorm : Tendsto (fun i => ‖A i - ContinuousLinearMap.id ℝ E‖) l (𝓝 (0 : ℝ)) := by
    simpa only [sub_self, norm_zero] using
      (hA.sub (tendsto_const_nhds (x := ContinuousLinearMap.id ℝ E))).norm
  have hplus : Tendsto (fun i => 1 + ‖A i - ContinuousLinearMap.id ℝ E‖) l (𝓝 (1 : ℝ)) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := (1 : ℝ))).add hnorm
  simpa only [mul_one] using (tendsto_const_nhds (x := (K : ℝ))).mul hplus

/-- The envelope coefficient is positive for `K > 0`. -/
theorem envelope_coefficient_pos (K : NNReal) (hK : 0 < K) (A : E →L[ℝ] E) :
    0 < (K : ℝ) * (1 + ‖A - ContinuousLinearMap.id ℝ E‖) := by
  exact mul_pos (NNReal.coe_pos.mpr hK) (by positivity)

end EnvelopeCoefficients

end FunctionalInequalities.KLS.RegularPotential

end
