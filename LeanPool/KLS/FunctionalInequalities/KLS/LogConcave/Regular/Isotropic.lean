/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Regular.Affine
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Translation
public import LeanPool.KLS.FunctionalInequalities.Probability.Covariance.Whitening
public import LeanPool.KLS.FunctionalInequalities.Probability.Transport
public import LeanPool.KLS.FunctionalInequalities.KLS.Isotropic

/-!
# Regular laws reduce to isotropic regular laws

Bizeul–Klartag–Lehec arXiv:2610.05474v1, Section 2 (p. 5): the reduction of Theorem 1.1 to
isotropic regular laws by centering and whitening. A regular law has finite second moment, full
support and positive definite covariance; a covariance whitening `W` exists, and the affine
potential `V (W⁻¹ · + mean)` is regular (`RegularAffine`) and isotropic, with its law the
translated and whitened law. No continuity or uniqueness of the whitening is asserted.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace FunctionalInequalities.KLS.RegularPotential

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {V : E → ℝ} {a b : ℝ}

/-- A regular law has a finite second moment. -/
theorem memLp_id_two (hV : KLS.RegularPotential V a b) : MemLp id 2 (hV.law : Measure E) :=
  hV.logConcave_law.memLp_id_two

/-- Lebesgue measure is absolutely continuous with respect to a regular law (positive density). -/
theorem volume_absolutelyContinuous_law (hV : KLS.RegularPotential V a b) :
    (volume : Measure E) ≪ (hV.law : Measure E) :=
  absolutelyContinuous_tilted hV.integrable_exp_neg

/-- A regular law has full support. -/
theorem support_law (hV : KLS.RegularPotential V a b) :
    (hV.law : Measure E).support = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  apply (Measure.mem_support_iff_forall x).2
  intro U hU
  have hmU : 0 < (volume : Measure E) U := Measure.measure_pos_of_mem_nhds volume hU
  exact pos_iff_ne_zero.2 fun h0 =>
    (pos_iff_ne_zero.1 hmU) (volume_absolutelyContinuous_law hV h0)

/-- The covariance of a regular law is positive definite. -/
theorem covariance_pos (hV : KLS.RegularPotential V a b) {v : E} (hv : v ≠ 0) :
    0 < inner ℝ (Covariance.operator (hV.law : Measure E) v) v := by
  rw [Covariance.operator_inner, covarianceBilin_self (memLp_id_two hV)]
  rcases (variance_nonneg (fun x => inner ℝ v x) (hV.law : Measure E)).lt_or_eq with h | h
  · exact h
  exfalso
  have hX : MemLp (fun x => inner ℝ v x) 2 (hV.law : Measure E) := by
    simpa only [Function.comp_def, id_eq, innerSL_apply_apply] using
      (innerSL ℝ v).comp_memLp' (memLp_id_two hV)
  have hae := ae_eq_integral_of_variance_eq_zero hX h.symm
  have hvol := (volume_absolutelyContinuous_law hV).ae_le hae
  have heq : (fun x : E => inner ℝ v x) =
      fun _ => ∫ x, inner ℝ v x ∂(hV.law : Measure E) :=
    Measure.eq_of_ae_eq hvol (by fun_prop) continuous_const
  have h0 := congrFun heq 0
  have hvv := congrFun heq v
  simp only [inner_zero_right] at h0
  rw [← h0, real_inner_self_eq_norm_sq] at hvv
  exact hv (norm_eq_zero.mp (sq_eq_zero_iff.mp hvv))

/--
Centering and whitening by a self-adjoint `W` with `⟪Cov (W u), W v⟫ = ⟪u, v⟫` makes the affine
regular potential `V (W⁻¹ · + mean)` isotropic. -/
theorem isotropic_comp_affine_of_whitening (hV : KLS.RegularPotential V a b) (W : E ≃L[ℝ] E)
    (hWadj : (W : E →L[ℝ] E).adjoint = W)
    (hW : ∀ u v, inner ℝ (Covariance.operator (hV.law : Measure E) (W u)) (W v) = inner ℝ u v) :
    KLS.Isotropic (comp_affine hV W.symm (∫ x, x ∂(hV.law : Measure E))).law := by
  let c : E := ∫ x, x ∂(hV.law : Measure E)
  let μc := Probability.translateLaw hV.law (-c)
  let μt := Probability.mapContinuousLinearEquiv μc W
  have hc2 : MemLp id 2 (μc : Measure E) :=
    Probability.memLp_id_two_translateLaw _ _ (memLp_id_two hV)
  have ht2 : MemLp id 2 (μt : Measure E) :=
    Probability.memLp_id_two_mapContinuousLinearEquiv μc W hc2
  have hmean_c : ∫ x, x ∂(μc : Measure E) = 0 :=
    Probability.integral_id_translateLaw_neg_integral hV.law
      ((memLp_id_two hV).integrable one_le_two)
  have hmean_t : ∫ y, y ∂(μt : Measure E) = 0 := by
    rw [Probability.integral_id_mapContinuousLinearEquiv μc W (hc2.integrable one_le_two),
      hmean_c, map_zero]
  have hcov_t : Covariance.operator (μt : Measure E) = ContinuousLinearMap.id ℝ E := by
    rw [Covariance.operator_mapContinuousLinearEquiv, Covariance.operator_translateLaw, hWadj]
    refine ContinuousLinearMap.ext fun u => ext_inner_right ℝ fun v => ?_
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
    rw [← hWadj, ContinuousLinearMap.adjoint_inner_left, hWadj]
    exact hW u v
  rw [law_comp_affine_eq_map hV W.symm c, ContinuousLinearEquiv.symm_symm]
  exact ⟨ht2, hmean_t, hcov_t⟩

/--
Every regular law can be centered and whitened by an affine map preserving regularity: there is a
self-adjoint whitening `W` with the affine potential isotropic and its law the translated, whitened
law. -/
theorem exists_isotropic_comp_affine (hV : KLS.RegularPotential V a b) :
    ∃ W : E ≃L[ℝ] E,
      (W : E →L[ℝ] E).adjoint = W ∧
        (∀ u v, inner ℝ (Covariance.operator (hV.law : Measure E) (W u)) (W v) = inner ℝ u v) ∧
          KLS.Isotropic (comp_affine hV W.symm (∫ x, x ∂(hV.law : Measure E))).law ∧
            (comp_affine hV W.symm (∫ x, x ∂(hV.law : Measure E))).law =
              Probability.mapContinuousLinearEquiv
                (Probability.translateLaw hV.law (-∫ x, x ∂(hV.law : Measure E))) W := by
  obtain ⟨W, hWadj, hW⟩ :=
    Covariance.exists_whitening (hV.law : Measure E) (fun _ hv => covariance_pos hV hv)
  refine ⟨W, hWadj, hW, isotropic_comp_affine_of_whitening hV W hWadj hW, ?_⟩
  simpa only [ContinuousLinearEquiv.symm_symm] using
    law_comp_affine_eq_map hV W.symm (∫ x, x ∂(hV.law : Measure E))

/--
**Regular laws reduce to isotropic regular laws** (BKL Section 2, p. 5, reduction of Theorem 1.1 to
isotropic regular laws): for every regular potential `V` there are an affine change of variables
`x ↦ W⁻¹ x + c` (`c` the mean, `W` a covariance whitening) and positive constants such that
`V (W⁻¹ · + c)` is regular and isotropic, with the explicit image law. -/
theorem exists_regular_isotropic (hV : KLS.RegularPotential V a b) :
    ∃ (W : E ≃L[ℝ] E) (c : E) (V' : E → ℝ) (a' b' : ℝ) (hV' : KLS.RegularPotential V' a' b'),
      c = (∫ x, x ∂(hV.law : Measure E)) ∧
        V' = (fun x => V (W.symm x + c)) ∧
          a' = affineLowerConstant a W.symm ∧
            b' = affineUpperConstant b W.symm ∧
              0 < a' ∧
                0 < b' ∧
                  KLS.Isotropic hV'.law ∧
                    hV'.law =
                      Probability.mapContinuousLinearEquiv
                        (Probability.translateLaw hV.law (-c)) W := by
  obtain ⟨W, _, _, hiso, hlaw⟩ := exists_isotropic_comp_affine hV
  refine
    ⟨W, _, _, _, _, comp_affine hV W.symm (∫ x, x ∂(hV.law : Measure E)), rfl, rfl, rfl, rfl,
      ?_, ?_, hiso, hlaw⟩
  · exact affineLowerConstant_pos hV.pos _
  · exact affineUpperConstant_pos _ _


end FunctionalInequalities.KLS.RegularPotential
