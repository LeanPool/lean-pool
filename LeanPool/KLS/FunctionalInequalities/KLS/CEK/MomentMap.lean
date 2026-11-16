/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.CEK.PartitionVariation

/-!
# The weak moment map of a bounded isotropic law

Euler–Lagrange identification for the Cordero-Erausquin–Klartag variational problem: the gradient of
the bounded-source
primal pushes `e^{−ψ} dx` forward to the source law (weak moment map), the existence step of the
weak moment-map route to
Letwin arXiv:2607.24164v1.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace FunctionalInequalities.KLS.CEK

open FunctionalInequalities
open FunctionalInequalities.Analysis
open FunctionalInequalities.Probability
open FunctionalInequalities.Probability.MomentMeasure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **Weak moment map of a bounded isotropic law** (Cordero-Erausquin–Klartag arXiv:1304.0630v1,
Theorem 2, existence, via the bounded CEK primal `bounded_source_lipschitz_primal` and the first
variation): for an isotropic probability law `μ` supported in the
closed ball of radius `L`, there is a convex `L`-Lipschitz potential `ψ` with `∫ e^{-ψ} = 1`
whose a.e. gradient pushes the law `e^{-ψ} dx` forward to `μ`. No regularity beyond Lipschitz is
claimed. -/
private theorem exists_momentMap_aux (μ : ProbabilityMeasure E)
    (hμ : KLS.Isotropic μ) (L : NNReal) (hL : ∀ᵐ y ∂(μ : Measure E), ‖y‖ ≤ (L : ℝ)) :
    ∃ ψ : E → ℝ, ConvexOn ℝ (univ : Set E) ψ ∧ LipschitzWith L ψ ∧
      (∫ x, Real.exp (-ψ x) ∂(volume : Measure E)) = 1 ∧
      ((volume : Measure E).tilted (fun x => -ψ x)).map (gradient ψ) = (μ : Measure E) := by
  classical

  -- Obtain the variational moment potential and normalize its law.
  obtain ⟨q, a, m, ψ, hq, hlsc, hqint, hqball, ha, hqa, hfloor, hleg, hupper,
    hψdef, hψ, hmass, hconv, hlip, hcont, hint, hnorm, hprob, hmax⟩ :=
    bounded_source_lipschitz_primal μ hμ L hL
  refine ⟨ψ, hconv, hlip, hnorm, ?_⟩
  have hμne : (μ : Measure E) ≠ 0 := by
    intro hzero
    have h := (measure_univ : (μ : Measure E) univ = 1)
    rw [hzero] at h
    simp at h
  have hqproper : ProperPotential q :=
    ⟨hq.1, potentialIntegrable_exists_finite q hμne hqint⟩
  have hgrad : Measurable (gradient ψ) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.measurable.comp
      (measurable_fderiv ℝ ψ)
  let ν : Measure E := (volume : Measure E).tilted (fun x => -ψ x)
  have hνprob : IsProbabilityMeasure ν := by
    dsimp [ν]
    exact isProbabilityMeasure_tilted hint
  have hpush : ν.map (gradient ψ) = (μ : Measure E) := by
    have hmapfinite : IsFiniteMeasure (ν.map (gradient ψ)) :=
      ⟨by
        rw [Measure.map_apply hgrad MeasurableSet.univ]
        simp only [preimage_univ, hνprob.measure_univ]
        exact ENNReal.one_lt_top⟩
    apply @ext_of_forall_integral_eq_of_IsFiniteMeasure E _ _ _ _
      (ν.map (gradient ψ)) (μ : Measure E) hmapfinite inferInstance
    intro b
    have hb : Continuous (b : E → ℝ) := b.continuous
    have hM : ∀ z, |b z| ≤ (‖b‖ : ℝ) := by
      intro z
      simpa only [Real.norm_eq_abs] using b.norm_coe_le_norm z

    -- Perturb the dual potential by a bounded continuous test function.
    let Z : ℝ → ℝ := fun t =>
      ∫ x, Real.exp
        (-(legendre (fun z => q z + ((t * b z : ℝ) : EReal)) x).toReal)
        ∂(volume : Measure E)
    have hZdata : ∀ t : ℝ, 0 < Z t ∧
        mass (volume : Measure E)
            (legendre (fun z => q z + ((t * b z : ℝ) : EReal))) =
          ENNReal.ofReal (Z t) := by
      intro t
      let φt : E → EReal := fun z => q z + ((t * b z : ℝ) : EReal)
      let ψt : E → ℝ := fun x => (legendre φt x).toReal
      have htop : ∀ x, legendre φt x ≠ ⊤ := by
        intro x
        exact
          (legendre_bounded_perturbation_finite_curve q hqproper x
            (hleg x).1 b (‖b‖ : ℝ) (norm_nonneg _) hM t).1
      have hbot : ∀ x, legendre φt x ≠ ⊥ := by
        intro x
        exact
          (legendre_bounded_perturbation_finite_curve q hqproper x
            (hleg x).1 b (‖b‖ : ℝ) (norm_nonneg _) hM t).2.1
      have hc : ∀ x, |ψt x - ψ x| ≤ |t| * (‖b‖ : ℝ) := by
        intro x
        dsimp [ψt, φt]
        simpa [hψdef] using
          (legendre_bounded_perturbation_finite_curve q hqproper x
            (hleg x).1 b (‖b‖ : ℝ) (norm_nonneg _) hM t).2.2
      let c : ℝ := |t| * (‖b‖ : ℝ)
      have hmeas : AEStronglyMeasurable
          (fun x => Real.exp (-(legendre φt x).toReal))
          (volume : Measure E) := by
        apply Measurable.aestronglyMeasurable
        exact
          (Continuous.measurable
            (Continuous.comp Real.continuous_exp continuous_neg)).comp
          (Measurable.ereal_toReal
            (LowerSemicontinuous.measurable
              (lowerSemicontinuous_legendre φt)))
      have hbound : ∀ᵐ x ∂(volume : Measure E),
          ‖Real.exp (-(legendre φt x).toReal)‖ ≤
            Real.exp c * Real.exp (-ψ x) := by
        filter_upwards [] with x
        have hx := hc x
        have hle : -ψt x ≤ -ψ x + c := by
          have hx' := (abs_le.mp hx).1
          dsimp [c] at hx' ⊢
          linarith
        have he : Real.exp (-ψt x) ≤ Real.exp (-ψ x + c) :=
          Real.exp_le_exp.mpr hle
        dsimp [ψt] at he
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        calc
          Real.exp (-(legendre φt x).toReal) = Real.exp (-ψt x) := rfl
          _ ≤ Real.exp (-ψ x + c) := he
          _ = Real.exp c * Real.exp (-ψ x) := by
            rw [Real.exp_add]
            exact mul_comm _ _
      have hInt : Integrable
          (fun x => Real.exp (-(legendre φt x).toReal))
          (volume : Measure E) :=
        (hint.const_mul (Real.exp c)).mono' hmeas hbound
      have hnonneg : 0 ≤ᵐ[(volume : Measure E)]
          fun x => Real.exp (-(legendre φt x).toReal) :=
        Filter.Eventually.of_forall fun x => (Real.exp_pos _).le
      have hlow : ∀ᵐ x ∂(volume : Measure E),
          Real.exp (-c) * Real.exp (-ψ x) ≤
            Real.exp (-(legendre φt x).toReal) := by
        filter_upwards [] with x
        have hx := hc x
        have hle : -ψ x - c ≤ -ψt x := by
          have hx' := (abs_le.mp hx).2
          dsimp [c] at hx' ⊢
          linarith
        have he : Real.exp (-ψ x - c) ≤ Real.exp (-ψt x) :=
          Real.exp_le_exp.mpr hle
        dsimp [ψt] at he
        calc
          Real.exp (-c) * Real.exp (-ψ x) =
              Real.exp (-ψ x - c) := by
                rw [← Real.exp_add]
                congr 1
                ring
          _ ≤ Real.exp (-ψt x) := he
          _ = Real.exp (-(legendre φt x).toReal) := rfl
      have hlowint := integral_mono_ae
        (hint.const_mul (Real.exp (-c))) hInt hlow
      have hZpos : 0 < Z t := by
        have hlowint' :
            Real.exp (-c) * 1 ≤ Z t := by
          calc
            Real.exp (-c) * 1 =
                ∫ x, Real.exp (-c) * Real.exp (-ψ x) ∂(volume : Measure E) := by
                  rw [integral_const_mul, hnorm]
            _ ≤ Z t := hlowint
        exact lt_of_lt_of_le (by positivity) hlowint'
      constructor
      · exact hZpos
      · rw [mass]
        calc
          (∫⁻ x, density (legendre φt) x ∂(volume : Measure E)) =
              ∫⁻ x, ENNReal.ofReal
                (Real.exp (-(legendre φt x).toReal)) ∂(volume : Measure E) := by
            apply lintegral_congr
            intro x
            rw [density]
            have hr :
                legendre φt x =
                  ((legendre φt x).toReal : EReal) :=
              (EReal.coe_toReal (htop x) (hbot x)).symm
            have hneg :
                -(legendre φt x) =
                  ((-(legendre φt x).toReal : ℝ) : EReal) := by
              calc
                -(legendre φt x) =
                    -((legendre φt x).toReal : EReal) :=
                  congrArg Neg.neg hr
                _ = ((-(legendre φt x).toReal : ℝ) : EReal) := by
                  rw [EReal.coe_neg]
            rw [hneg]
            exact EReal.exp_coe _
          _ = ENNReal.ofReal
                (∫ x, Real.exp (-(legendre φt x).toReal)
                  ∂(volume : Measure E)) :=
            (ofReal_integral_eq_lintegral_ofReal hInt hnonneg).symm
          _ = ENNReal.ofReal (Z t) := rfl
    have hpot : ∀ t : ℝ,
        PotentialIntegrable
          (fun z => q z + ((t * b z : ℝ) : EReal)) (μ : Measure E) := by
      intro t
      refine ⟨?_, ?_, ?_⟩
      · intro z hz
        rw [EReal.add_eq_bot_iff] at hz
        rcases hz with hz | hz
        · exact (hqint.1 z) hz
        · exact (EReal.coe_ne_bot _) hz
      · filter_upwards [hqint.2.1] with z hz
        exact EReal.add_ne_top hz (EReal.coe_ne_top _)
      · have hbint : Integrable (fun z => t * b z) (μ : Measure E) :=
          (b.integrable (μ : Measure E)).const_mul t
        have hi := hqint.2.2.add hbint
        apply hi.congr
        filter_upwards [hqint.2.1] with z hz
        rw [EReal.toReal_add]
        · rfl
        · exact hz
        · exact hqint.1 z
        · exact EReal.coe_ne_top _
        · exact EReal.coe_ne_bot _
    have hIntq : ∀ t : ℝ,
        (∫ z, (q z + ((t * b z : ℝ) : EReal)).toReal ∂(μ : Measure E)) =
          ∫ z, (q z).toReal ∂(μ : Measure E) +
            t * ∫ z, b z ∂(μ : Measure E) := by
      intro t
      have hbint : Integrable (fun z => t * b z) (μ : Measure E) :=
        (b.integrable (μ : Measure E)).const_mul t
      have hqreal : Integrable (fun z => (q z).toReal) (μ : Measure E) :=
        hqint.2.2
      calc
        (∫ z, (q z + ((t * b z : ℝ) : EReal)).toReal ∂(μ : Measure E)) =
            ∫ z, (q z).toReal + t * b z ∂(μ : Measure E) := by
              apply integral_congr_ae
              filter_upwards [hqint.2.1] with z hz
              rw [EReal.toReal_add]
              · rfl
              · exact hz
              · exact hqint.1 z
              · exact EReal.coe_ne_top _
              · exact EReal.coe_ne_bot _
        _ = ∫ z, (q z).toReal ∂(μ : Measure E) +
              ∫ z, t * b z ∂(μ : Measure E) :=
            integral_add hqreal hbint
        _ = ∫ z, (q z).toReal ∂(μ : Measure E) +
              t * ∫ z, b z ∂(μ : Measure E) := by
            rw [integral_const_mul]
    have hJt : ∀ t : ℝ,
        variationalFunctional (volume : Measure E) (μ : Measure E)
            (fun z => q z + ((t * b z : ℝ) : EReal)) =
          (Real.log (Z t) - ∫ z, (q z).toReal ∂(μ : Measure E) -
            t * ∫ z, b z ∂(μ : Measure E) : EReal) := by
      intro t
      have hz := hZdata t
      rw [variationalFunctional, hz.2, ENNReal.log_ofReal]
      simp only [ite_eq_right (not_le.mpr hz.1)]
      rw [hIntq t]
      let A : ℝ := ∫ z, (q z).toReal ∂(μ : Measure E)
      let B : ℝ := ∫ z, b z ∂(μ : Measure E)
      change (↑(Real.log (Z t)) - ↑(A + t * B) : EReal) =
        (↑(Real.log (Z t)) - ↑A - ↑t * ↑B : EReal)
      calc
        (↑(Real.log (Z t)) - ↑(A + t * B) : EReal) =
            ↑(Real.log (Z t) - (A + t * B)) :=
          (EReal.coe_sub _ _).symm
        _ = ↑((Real.log (Z t) - A) - t * B) := by
          congr 1
          ring
        _ = (↑(Real.log (Z t)) - ↑A - ↑t * ↑B : EReal) := by
          simp only [EReal.coe_sub, EReal.coe_mul]
    have hJq :
        variationalFunctional (volume : Measure E) (μ : Measure E) q =
          (-(∫ z, (q z).toReal ∂(μ : Measure E)) : EReal) := by
      rw [variationalFunctional, hmass]
      simp only [ENNReal.log_one, zero_sub]
    have hZ0 : Z 0 = 1 := by
      dsimp [Z]
      simp only [zero_mul, add_zero]
      calc
        (∫ x, Real.exp (-(legendre q x).toReal) ∂(volume : Measure E)) =
            ∫ x, Real.exp (-ψ x) ∂(volume : Measure E) := by
              apply integral_congr_ae
              filter_upwards [] with x
              rw [hψ x, EReal.toReal_coe]
        _ = 1 := hnorm
    have hmax0 :
        IsLocalMax
          (fun t => Real.log (Z t) -
            t * ∫ z, b z ∂(μ : Measure E)) 0 := by
      apply IsMaxOn.isLocalMax
      · intro t _
        have hi := hmax
          (fun z => q z + ((t * b z : ℝ) : EReal)) (hpot t)
        rw [hJt t, hJq] at hi
        have hi' := EReal.coe_le_coe_iff.mp hi
        have hi'' :
            Real.log (Z t) - t * ∫ z, b z ∂(μ : Measure E) ≤ 0 := by
          linarith
        simpa [hZ0] using hi''
      · exact Filter.univ_mem

    -- Differentiate the partition function and use the Euler-Lagrange identity.
    have hderiv :=
      hasDerivAt_integral_exp_neg_legendre_add_smul q hqproper hlsc ψ hψ hlip hint
        (b : E → ℝ) hb hM
    have hZderiv :
        HasDerivAt Z
          (∫ x, Real.exp (-ψ x) * b (gradient ψ x) ∂(volume : Measure E)) 0 := by
      change HasDerivAt
        (fun t =>
          ∫ x, Real.exp
            (-(legendre (fun z => q z + ((t * b z : ℝ) : EReal)) x).toReal)
            ∂(volume : Measure E))
        (∫ x, Real.exp (-ψ x) * b (gradient ψ x) ∂(volume : Measure E)) 0
      exact hderiv
    have hderivlog :
        HasDerivAt
          (fun t => Real.log (Z t) - t * ∫ x, b x ∂(μ : Measure E))
          (∫ x, Real.exp (-ψ x) * b (gradient ψ x) ∂(volume : Measure E) -
            ∫ x, b x ∂(μ : Measure E)) 0 := by
      let B : ℝ := ∫ x, b x ∂(μ : Measure E)
      have hmul : HasDerivAt (fun t : ℝ => t * B) B 0 := by
        simpa only [id_eq, one_mul] using
          (hasDerivAt_id (0 : ℝ)).mul_const B
      have hlog := HasDerivAt.log hZderiv (by simp [hZ0])
      have hsub := hlog.sub hmul
      change HasDerivAt
        (fun t : ℝ => Real.log (Z t) - t * B)
        (_ / Z 0 - B) 0 at hsub
      rw [hZ0, div_one] at hsub
      simpa only [B] using hsub
    have hEL :
        ∫ x, Real.exp (-ψ x) * b (gradient ψ x) ∂(volume : Measure E) =
          ∫ x, b x ∂(μ : Measure E) :=
      sub_eq_zero.mp (IsLocalMax.hasDerivAt_eq_zero hmax0 hderivlog)
    calc
      ∫ y, b y ∂(ν.map (gradient ψ)) =
          ∫ x, b (gradient ψ x) ∂ν := by
            exact integral_map hgrad.aemeasurable hb.aestronglyMeasurable
      _ = ∫ x, (Real.exp (-ψ x) /
            ∫ y, Real.exp (-ψ y) ∂(volume : Measure E)) •
            b (gradient ψ x) ∂(volume : Measure E) := by
            dsimp [ν]
            exact integral_tilted (fun x => -ψ x) (fun x => b (gradient ψ x))
      _ = ∫ x, Real.exp (-ψ x) * b (gradient ψ x) ∂(volume : Measure E) := by
            simp only [hnorm, div_one, smul_eq_mul]
      _ = ∫ x, b x ∂(μ : Measure E) := hEL
  exact hpush

/-- **Weak moment map of a bounded isotropic law** (Cordero-Erausquin–Klartag arXiv:1304.0630v1,
Theorem 2, existence, via the bounded CEK primal `bounded_source_lipschitz_primal` and the first
variation): for an isotropic probability law `μ` supported in the closed
ball of radius `L`, there is a convex `L`-Lipschitz potential `ψ` with `∫ e^{-ψ} = 1` whose a.e.
gradient pushes the law `e^{-ψ} dx` forward to `μ`. No regularity beyond Lipschitz is claimed. -/
theorem exists_momentMap_of_isotropic_of_ae_norm_le (μ : ProbabilityMeasure E)
    (hμ : KLS.Isotropic μ) (L : NNReal) (hL : ∀ᵐ y ∂(μ : Measure E), ‖y‖ ≤ (L : ℝ)) :
    ∃ ψ : E → ℝ, ConvexOn ℝ (univ : Set E) ψ ∧ LipschitzWith L ψ ∧
      (∫ x, Real.exp (-ψ x) ∂(volume : Measure E)) = 1 ∧
      ((volume : Measure E).tilted (-ψ)).map (gradient ψ) = (μ : Measure E) := by
  exact exists_momentMap_aux μ hμ L hL

end FunctionalInequalities.KLS.CEK
