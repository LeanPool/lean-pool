/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Energy.LocalSlope.Gradient
public import LeanPool.KLS.FunctionalInequalities.Poincare.LocalSlope.Basic

/-!
# The literature Poincaré constant in gradient form

The literature-Poincaré clause of `thm:klartag-density-frontend-identification`.

`def:literature-poincare-constant` defines `C_P^lit` through the **local metric slope**
`Energy.LocalSlope.apply`. The Klartag frontend states the same constant through the **gradient**:
`C_P^lit(μ)` is the infimum of the finite `C ≥ 0` for which `Var_ν(g) ≤ C ∫ ‖∇g‖² dν` holds for
every locally Lipschitz `g ∈ L²(ν)` of finite gradient energy, where `ν` is the intrinsic law.

No new definition is introduced: the gradient-form validity is written out inline, and the optimal
constant remains `Poincare.LocalSlope.Intrinsic.optimalConstant`. The analysis is already done in
`Energy/LocalSlope/Gradient.lean` (Rademacher plus absolute continuity); what is proved here is
only the transport of that identification through the validity predicate and its infimum.

Read `holds_iff_memLp_gradient` first, then `Intrinsic.constant_eq_iInf_gradient` and its
log-concave specialization in `KLS/LogConcave/Poincare.lean`.
`holds_iff_lintegral_gradient_le_one` is the normalization of Letwin arXiv:2607.24164v1,
Equation (1.1): locally Lipschitz tests with `E|∇g|² ≤ 1` and no `L²` premise.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory TopologicalSpace

namespace FunctionalInequalities.Poincare.LocalSlope

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

/--
fixed-constant equivalence: for an absolutely continuous law the local-slope and gradient
descriptions of a valid
finite constant agree. Both directions rewrite the same two proved identifications, so no
inequality is weakened: the admissible class and the energy are transported simultaneously. -/
theorem holds_iff_memLp_gradient (ν : ProbabilityMeasure V) (m : Measure V)
    [Measure.IsAddHaarMeasure m] (hν : (ν : Measure V) ≪ m) (C : NNReal) :
    Holds ν C ↔
      ∀ g : V → ℝ,
        LocallyLipschitz g →
          MemLp g 2 (ν : Measure V) →
            MemLp (gradient g) 2 (ν : Measure V) →
              evariance g (ν : Measure V) ≤
                (C : ENNReal) * ∫⁻ x, (ENNReal.ofReal ‖gradient g x‖) ^ 2 ∂(ν : Measure V) := by
  constructor
  · intro hC g hlip hL2 hgrad
    have hadm : Energy.LocalSlope.Admissible ν g :=
      (Energy.LocalSlope.admissible_iff_memLp_gradient ν m hν g).mpr ⟨hlip, hL2, hgrad⟩
    have := hC g hadm
    rwa [Energy.LocalSlope.energy_eq_lintegral_gradient ν m hν g hlip] at this
  · intro hC g hadm
    obtain ⟨hlip, hL2, hgrad⟩ :=
      (Energy.LocalSlope.admissible_iff_memLp_gradient ν m hν g).mp hadm
    rw [Energy.LocalSlope.energy_eq_lintegral_gradient ν m hν g hlip]
    exact hC g hlip hL2 hgrad

omit [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- The scaled function `c • g` has gradient `c • ∇g` everywhere, including Mathlib's zero
convention at points of non-differentiability. -/
private theorem gradient_const_smul (c : ℝ) (g : V → ℝ) (x : V) :
    gradient (c • g) x = c • gradient g x := by
  simp only [gradient, fderiv_const_smul_field, Pi.smul_apply, LinearIsometryEquiv.map_smulₛₗ,
    RCLike.conj_to_real]

omit [SecondCountableTopology V] in
/-- Letwin arXiv:2607.24164v1, Equation (1.1): for an absolutely continuous law, a finite
constant `C` is valid for the local-slope test class exactly when
`Var_ν g ≤ C E_ν |∇g|²` for every locally Lipschitz `g` with `E_ν |∇g|² ≤ 1`, where `∇g` is the
Fréchet gradient (Rademacher, `ν`-a.e.). No `L²` premise on `g` or on `∇g` appears: under a finite
constant it follows from `Holds.memLp_two`, and the unit-energy normalization is removed by
scaling `g`. The variance is the extended variance, `⊤` outside `L²`. -/
theorem holds_iff_lintegral_gradient_le_one (ν : ProbabilityMeasure V) (m : Measure V)
    [Measure.IsAddHaarMeasure m] (hν : (ν : Measure V) ≪ m) (C : NNReal) :
    Holds ν C ↔
      ∀ g : V → ℝ, LocallyLipschitz g →
        ∫⁻ x, (ENNReal.ofReal ‖gradient g x‖) ^ 2 ∂(ν : Measure V) ≤ 1 →
        evariance g (ν : Measure V) ≤
          (C : ENNReal) * ∫⁻ x, (ENNReal.ofReal ‖gradient g x‖) ^ 2 ∂(ν : Measure V) := by
  constructor
  · intro hC g hlip hle
    have hE := Energy.LocalSlope.energy_eq_lintegral_gradient ν m hν g hlip
    have hfin : Energy.LocalSlope.energy ν g ≠ ⊤ := by
      rw [hE]; exact ne_top_of_le_ne_top ENNReal.one_ne_top hle
    have := hC g ⟨hlip, hC.memLp_two hlip hfin, hfin⟩
    rwa [hE] at this
  · intro h g hadm
    rw [Energy.LocalSlope.energy_eq_lintegral_gradient ν m hν g hadm.locallyLipschitz]
    have hfin := hadm.finite_energy
    rw [Energy.LocalSlope.energy_eq_lintegral_gradient ν m hν g hadm.locallyLipschitz] at hfin
    set e := ∫⁻ x, (ENNReal.ofReal ‖gradient g x‖) ^ 2 ∂(ν : Measure V) with he
    rcases eq_or_ne e 0 with h0 | h0
    · exact h g hadm.locallyLipschitz (by rw [← he, h0]; exact zero_le_one)
    set c : ℝ := (Real.sqrt e.toReal)⁻¹ with hc
    have hepos : 0 < e.toReal := ENNReal.toReal_pos h0 hfin
    have hcpos : 0 < c := inv_pos.mpr (Real.sqrt_pos.mpr hepos)
    have hc2 : c ^ 2 = e.toReal⁻¹ := by
      rw [hc, inv_pow, Real.sq_sqrt hepos.le]
    have hk0 : ENNReal.ofReal (c ^ 2) ≠ 0 := by
      rw [ENNReal.ofReal_ne_zero_iff]; positivity
    have hlip' : LocallyLipschitz (c • g) :=
      (lipschitzWith_smul c).locallyLipschitz.comp hadm.locallyLipschitz
    have hgrad : ∫⁻ x, (ENNReal.ofReal ‖gradient (c • g) x‖) ^ 2 ∂(ν : Measure V) =
        ENNReal.ofReal (c ^ 2) * e := by
      rw [he, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr fun x ↦ ?_
      rw [gradient_const_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hcpos,
        ENNReal.ofReal_mul hcpos.le, mul_pow, ENNReal.ofReal_pow hcpos.le]
    have hone : ENNReal.ofReal (c ^ 2) * e = 1 := by
      calc ENNReal.ofReal (c ^ 2) * e =
            ENNReal.ofReal e.toReal⁻¹ * ENNReal.ofReal e.toReal := by
            rw [hc2, ENNReal.ofReal_toReal hfin]
        _ = 1 := by
            rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hepos.le), inv_mul_cancel₀ hepos.ne',
              ENNReal.ofReal_one]
    have hb := h (c • g) hlip' (by rw [hgrad, hone])
    have hvar : evariance (c • g) (ν : Measure V) =
        ENNReal.ofReal (c ^ 2) * evariance g (ν : Measure V) :=
      evariance_mul c g _
    rw [hvar, hgrad, mul_left_comm] at hb
    exact (ENNReal.mul_le_mul_iff_right hk0 ENNReal.ofReal_ne_top).mp hb

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]

omit [CompleteSpace E] in
/--
the optimal-constant identity: the literature optimum of an absolutely continuous intrinsic law, in
gradient form.
The two infima range over subtypes cut out by equivalent predicates, so each bounds the other. -/
theorem Intrinsic.constant_eq_iInf_gradient (μ : ProbabilityMeasure E)
    (m : Measure (Probability.affineSupport μ).direction) [Measure.IsAddHaarMeasure m]
    (hμ :
      (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) ≪ m) :
    Poincare.LocalSlope.Intrinsic.optimalConstant μ =
      ⨅ C :
        { C : NNReal //
          ∀ g : (Probability.affineSupport μ).direction → ℝ,
            LocallyLipschitz g →
              MemLp g 2
                  (Probability.intrinsicMeasure μ :
                    Measure (Probability.affineSupport μ).direction) →
                MemLp (gradient g) 2
                    (Probability.intrinsicMeasure μ :
                      Measure (Probability.affineSupport μ).direction) →
                  evariance g
                      (Probability.intrinsicMeasure μ :
                        Measure (Probability.affineSupport μ).direction) ≤
                    (C : ENNReal) *
                      ∫⁻ x,
                        (ENNReal.ofReal ‖gradient g x‖) ^
                          2 ∂(Probability.intrinsicMeasure μ :
                          Measure (Probability.affineSupport μ).direction) },
        (C.1 : ENNReal) := by
  have hiff := holds_iff_memLp_gradient (Probability.intrinsicMeasure μ) m hμ
  apply le_antisymm
  · refine le_iInf fun C => ?_
    exact iInf_le_of_le ⟨C.1, (hiff C.1).mpr C.2⟩ le_rfl
  · refine le_iInf fun C => ?_
    exact iInf_le_of_le ⟨C.1, (hiff C.1).mp C.2⟩ le_rfl


end FunctionalInequalities.Poincare.LocalSlope
