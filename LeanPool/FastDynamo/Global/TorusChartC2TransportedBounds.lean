/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Global.TorusChartC2TransportedField

/-!
# Norm bounds for the transported field

§7.1 of the paper asks the selected summand of `eq:Rapp` for the two halves (`L²` and
gradient) of `eq:local-gradient` transported to the torus:

`‖auxiliaryCutoff_n·w‖_{L²(T²)} ≤ ‖w‖_{L²(ℝ²)}`  and
`√ε‖∇_⊥(auxiliaryCutoff_n w)‖_{L²(T²)} ≤ C₁√ε/Rcut ‖w‖ + √ε‖∇_⊥w‖`,

where the gradient picks up the Leibniz term `(∇auxiliaryCutoff_n)w`, and `‖∇auxiliaryCutoff_n‖_∞
≤ C₁/Rcut`.
Both are proved here for the chart transports of `Global/TorusChartC2Transfer.lean`, at an
arbitrary radius; the caller instantiates them at the auxiliary radius `3R/2` of
`Global/TorusChartC2AuxiliaryCutoff.lean` and feeds the two halves of `eq:local-gradient`
from `Global/WholePlaneScaledLocalResolvent.lean` into the right-hand sides.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory Metric Set

namespace TorusChartC2Transfer

open ConstantCoefficientBackground
open ParametrixExplicitCutoff
open TorusChartH2
open TorusChartL2
open TorusSupportedH2Output
open WholePlaneHorizontalFibre

variable (p : WholePlane) (R : ℝ) (hR : 0 < R)

/-! ## Sup bounds for the output cut-off certificate -/

/-- A pointwise almost-everywhere bound is an `L∞` bound. -/
theorem norm_wholePlaneScalarLInf_le_of_ae {a : WholePlaneScalarLInf} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ᵐ x ∂volume, ‖(a : WholePlane → ℂ) x‖ ≤ C) : ‖a‖ ≤ C := by
  rw [Lp.norm_def]
  apply ENNReal.toReal_le_of_le_ofReal hC
  rw [eLpNorm_exponent_top (Lp.aestronglyMeasurable a)]
  exact eLpNormEssSup_le_of_ae_bound h

/-- The output cut-off certificate has sup-norm at most one. -/
theorem norm_outputCutoffW2InfCertificate_value_le_one :
    ‖(outputCutoffW2InfCertificate p R hR).value‖ ≤ 1 := by
  refine norm_wholePlaneScalarLInf_le_of_ae (by norm_num) ?_
  filter_upwards [outputCutoffW2InfCertificate_value_coe_ae p R hR] with x hx
  rw [hx]
  exact norm_outputCutoffComplex_le_one p R hR x

/-- Each stored derivative of the output cut-off certificate obeys the scaling bound
`C₁/R` of `eq:parametrix-cutoff-bounds`. -/
theorem norm_outputCutoffW2InfCertificate_deriv_le (j : Fin 2) :
    ‖(outputCutoffW2InfCertificate p R hR).deriv j‖ ≤ firstDerivativeConstant / R := by
  refine norm_wholePlaneScalarLInf_le_of_ae ?_ ?_
  · exact div_nonneg (le_of_lt firstDerivativeConstant_pos) (le_of_lt hR)
  · filter_upwards [outputCutoffW2InfCertificate_deriv_coe_ae p R hR j] with x hx
    rw [hx, Complex.norm_real]
    exact norm_outputCutoff_coordinateDerivative_le p R hR j x

/-! ## The transported value and gradient -/

variable (hbox : closedBall p (R / 2) ⊆ wholePlaneFundamentalBox)

/-- The transported value is a contraction. -/
theorem norm_transverseH2Embedding_extendDomainC2_le (w : WholePlaneC2H2) :
    ‖transverseH2Embedding (extendDomainC2 p R hR hbox w)‖ ≤
      ‖wholePlaneH2Embedding C2 w‖ := by
  rw [transverseH2Embedding_extendDomainC2]
  exact norm_extendStateC2_apply_le p R hR (wholePlaneH2Embedding C2 w)

/-- The stored transverse derivative of the transported field, expanded by the Leibniz rule of
`Analysis/WholePlaneScalarH2Leibniz.lean`. -/
theorem transverseVecDerivFromH2_extendDomainC2 (j : Fin 2) (w : WholePlaneC2H2) :
    transverseVecDerivFromH2 (Fin 2) j (extendDomainC2 p R hR hbox w) =
      horizontalProjL2 (wholePlaneToTorusL2
        (wholePlaneScalarMulC3L2 ((outputCutoffW2InfCertificate p R hR).deriv j)
            (wholePlaneVerticalZeroExtendL2 (wholePlaneH2Embedding C2 w)) +
          wholePlaneScalarMulC3L2 (outputCutoffW2InfCertificate p R hR).value
            (wholePlaneVerticalZeroExtendL2 (wholePlaneH2FirstDerivative C2 j w)))) := by
  have h1 : transverseDerivFromH2 j (wholePlaneOutputLocalizationH2 p R hR hbox
        (wholePlaneVerticalZeroExtendH2 w)) =
      chartFirstDerivativeL2 j (outputCutoffToChartSupportedH2 p R hR hbox
        (wholePlaneVerticalZeroExtendH2 w)) :=
    transverseDerivFromH2_wholePlaneChartToTransverseH2
      (outputCutoffToChartSupportedH2 p R hR hbox (wholePlaneVerticalZeroExtendH2 w)) j
  have h2 : chartFirstDerivativeL2 j (outputCutoffToChartSupportedH2 p R hR hbox
        (wholePlaneVerticalZeroExtendH2 w)) =
      wholePlaneToTorusL2
        (wholePlaneScalarMulC3L2 ((outputCutoffW2InfCertificate p R hR).deriv j)
            (wholePlaneVerticalZeroExtendL2 (wholePlaneH2Embedding C2 w)) +
          wholePlaneScalarMulC3L2 (outputCutoffW2InfCertificate p R hR).value
            (wholePlaneVerticalZeroExtendL2 (wholePlaneH2FirstDerivative C2 j w))) := rfl
  rw [extendDomainC2_apply, ← horizontalProjL2_transverseDerivFromH2]
  exact congrArg (fun X : TransverseC3L2 ↦ horizontalProjL2 X) (h1.trans h2)

/-- The transported gradient obeys the Leibniz bound: the cut-off contributes `C₁/R` times the
value, the field itself contributes its own derivative. -/
theorem norm_transverseVecDerivFromH2_extendDomainC2_le (j : Fin 2) (w : WholePlaneC2H2) :
    ‖transverseVecDerivFromH2 (Fin 2) j (extendDomainC2 p R hR hbox w)‖ ≤
      firstDerivativeConstant / R * ‖wholePlaneH2Embedding C2 w‖ +
        ‖wholePlaneH2FirstDerivative C2 j w‖ := by
  rw [transverseVecDerivFromH2_extendDomainC2 p R hR hbox j w]
  refine le_trans (norm_horizontalProjL2_apply_le _) ?_
  refine le_trans (norm_wholePlaneToTorusL2_apply_le _) ?_
  refine le_trans (norm_add_le _ _) ?_
  refine add_le_add ?_ ?_
  · refine le_trans (norm_scalarVectorMulL2_apply_le volume _ _) ?_
    refine le_trans (mul_le_mul_of_nonneg_right
      (norm_outputCutoffW2InfCertificate_deriv_le p R hR j) (norm_nonneg _)) ?_
    rw [norm_wholePlaneVerticalZeroExtendL2]
  · refine le_trans (norm_scalarVectorMulL2_apply_le volume _ _) ?_
    refine le_trans (mul_le_mul_of_nonneg_right
      (norm_outputCutoffW2InfCertificate_value_le_one p R hR) (norm_nonneg _)) ?_
    rw [one_mul, norm_wholePlaneVerticalZeroExtendL2]

/-- The gradient-energy form of the previous bound: if each transported derivative is bounded
by `c` after the `√ε` weight, the gradient energy is bounded by `√2 c`. -/
theorem sqrt_mul_transverseGradientEnergy_le {epsilon c : ℝ} (hepsilon : 0 ≤ epsilon)
    (hc : 0 ≤ c) (h : TransverseC2H2)
    (hbound : ∀ j : Fin 2,
      Real.sqrt epsilon * ‖transverseVecDerivFromH2 (Fin 2) j h‖ ≤ c) :
    Real.sqrt (epsilon * transverseGradientEnergy h) ≤ Real.sqrt 2 * c := by
  have hsq : ∀ j : Fin 2, epsilon * ‖transverseVecDerivFromH2 (Fin 2) j h‖ ^ 2 ≤ c ^ 2 := by
    intro j
    have h1 := hbound j
    have h2 : (Real.sqrt epsilon * ‖transverseVecDerivFromH2 (Fin 2) j h‖) ^ 2 ≤ c ^ 2 := by
      have h0 : 0 ≤ Real.sqrt epsilon * ‖transverseVecDerivFromH2 (Fin 2) j h‖ :=
        mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
      nlinarith [h1, h0, hc]
    calc epsilon * ‖transverseVecDerivFromH2 (Fin 2) j h‖ ^ 2
        = (Real.sqrt epsilon * ‖transverseVecDerivFromH2 (Fin 2) j h‖) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hepsilon]
      _ ≤ c ^ 2 := h2
  have henergy : epsilon * transverseGradientEnergy h ≤ 2 * c ^ 2 := by
    unfold transverseGradientEnergy
    rw [Finset.mul_sum, Fin.sum_univ_two]
    have h0 := hsq 0
    have h1 := hsq 1
    linarith
  calc Real.sqrt (epsilon * transverseGradientEnergy h) ≤ Real.sqrt (2 * c ^ 2) :=
        Real.sqrt_le_sqrt henergy
    _ = Real.sqrt 2 * c := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hc]

end TorusChartC2Transfer

end

end FastDynamo
