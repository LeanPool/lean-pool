/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Finish.MagneticScale
public import LeanPool.FastDynamo.Global.MainTheoremWitnesses

/-!
# Axial index and magnetic length of the eigenmodes of Theorem 1.2

Corollary 8.3 (`cor:magnetic-scale`) of the paper for the magnetic eigenmodes of Theorem 1.2
(`thm:main`) at the explicit witnesses `mainVelocity`, `mainEps0`, `mainGrowthFloor`.

`main_theorem_magnetic_scale` gives constants `0 < c`, `0 < C`, independent of `ε`, such that
for every `0 < ε ≤ mainEps0` one triple `(K, λ, b)` carries the clauses of Theorem 1.2
(`MainPhysicalClausesAt`, the body of `MainPhysicalClauses`) together with

`c ε^{-1/2} ≤ |K| ≤ C ε^{-1/2}`,  `c √ε ≤ L_B ≤ C √ε`,

where `L_B` is the magnetic length `‖V‖₂ / ‖∇V‖₂` of the complex mode `V = e^{2πiKx₃} b`
(`complexAxialMagneticLength`), and the real datum `B_in = Re V` (and, more generally, the
real part of `V` at every phase) has the same magnetic length.  The triple is the eigenpair
in the axial sector `K = K_{n(ε)}` of the matching cell `n(ε)` of the parameter chain.

**Deviation.**  The norm `‖∇V‖₂` is the `L²` norm of the weak gradient of the product-torus
field, `(‖∂₁V‖₂² + ‖∂₂V‖₂² + ‖∂₃V‖₂²)^{1/2}`, and `‖V‖₂` is the product-measure norm
(`productGradientFromH2`, `complexAxialMagneticLength`).  The magnetic length of the real
field is `realPhaseAxialMagneticLength`, whose gradient `phaseAxialGradientL2` is the weak
gradient of the real `H²` field `Re(e^{iθ} V)` (`complexifyProductR3L2_phaseAxialGradientL2`).
The lower bound uses
`M = ‖transverseStretchingCoefficient mainVelocity‖`, the `L∞` norm of the literal stretching
coefficient, in place of `ess sup ‖∇u‖_op`.  The index `K` is the integer `K_n = k_*/ℓ_n` with
`k_* = 1`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open HorizontalMode

/-- **Corollary 8.3 of the paper at the eigenmodes of Theorem 1.2.**  There are constants
`c, C > 0` such that for every `0 < ε ≤ mainEps0` there is a triple `(K, λ, b)` satisfying the
clauses of Theorem 1.2 at `mainVelocity` and `mainGrowthFloor`, with
`c ε^{-1/2} ≤ |K| ≤ C ε^{-1/2}` and `c √ε ≤ L_B ≤ C √ε` for the magnetic length of the complex
mode `e^{2πiKx₃} b`, and the real part of that mode at every phase (in particular the real datum,
phase `0`) has the same magnetic length. -/
theorem main_theorem_magnetic_scale :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ mainEps0 →
        ∃ (K : ℤ) (lambda : ℂ) (b : TransverseC3H2),
          MainPhysicalClausesAt mainVelocity mainGrowthFloor eps K lambda b ∧
          c * eps ^ (-(1 / 2 : ℝ)) ≤ |(K : ℝ)| ∧ |(K : ℝ)| ≤ C * eps ^ (-(1 / 2 : ℝ)) ∧
          c * Real.sqrt eps ≤ complexAxialMagneticLength K b ∧
          complexAxialMagneticLength K b ≤ C * Real.sqrt eps ∧
          ∀ phase : ℝ, realPhaseAxialMagneticLength K phase b =
            complexAxialMagneticLength K b := by
  set p := globalSeedInterface.parameters with hp
  -- the stretching norm is positive
  have hM : 0 < ‖transverseStretchingCoefficient mainVelocity‖ := by
    obtain ⟨K, lambda, b, hK, hgrowth, hpair⟩ :=
      mainReducedClauses_holds mainEps0 mainEps0_pos le_rfl
    have hb : b ≠ 0 := fun hb => hpair.1 (by rw [hb, map_zero])
    exact ReducedInductionMagneticScale.norm_transverseStretchingCoefficient_pos_of_reducedEigenpair
      mainVelocity mainVelocity_isTransverseDivergenceFree mainEps0 mainEps0_pos K hK lambda
      (mainGrowthFloor_pos.le.trans hgrowth) b hb hpair
  have hdm : 0 < p.deltaMinus := p.deltaMinus_pos
  have hdp : 0 < p.deltaPlus := p.deltaPlus_pos
  have hsm : 0 < Real.sqrt p.deltaMinus := Real.sqrt_pos.2 hdm
  have hsp : 0 < Real.sqrt p.deltaPlus := Real.sqrt_pos.2 hdp
  have hsM : 0 < Real.sqrt ‖transverseStretchingCoefficient mainVelocity‖ :=
    Real.sqrt_pos.2 hM
  have hc1 : 0 < 1 / Real.sqrt ‖transverseStretchingCoefficient mainVelocity‖ := by positivity
  have hC1 : 0 < 1 / (2 * Real.pi * Real.sqrt p.deltaMinus) := by positivity
  refine ⟨min (Real.sqrt p.deltaMinus)
      (1 / Real.sqrt ‖transverseStretchingCoefficient mainVelocity‖),
    max (Real.sqrt p.deltaPlus) (1 / (2 * Real.pi * Real.sqrt p.deltaMinus)),
    lt_min hsm hc1, lt_max_of_lt_left hsp, ?_⟩
  intro eps hpos hle
  set cell := mainParameterChoice.matchingCell hpos hle with hcell
  obtain ⟨lambda, b, hfloor, hreduced, -, -, -⟩ :=
    exists_growing_reducedInduction_eigenpair_matchingCell hpos cell
  have hK := mainParameterChoice.fourierIndex_ne_zero cell
  refine ⟨mainParameterChoice.fourierIndex cell, lambda, b,
    mainPhysicalClausesAt_of_reducedEigenpair mainVelocity_isTransverseDivergenceFree
      mainGrowthFloor_pos hpos hK hfloor hreduced, ?_⟩
  have hb : b ≠ 0 := fun hb => hreduced.1 (by rw [hb, map_zero])
  have hmatch : eps / mainParameterChoice.scaleFamily.ell cell.index ^ 2 ∈ p.interval :=
    cell.admissible
  have hlow := ScaleFamily.matching_fourierIndex_lower mainParameterChoice.scaleFamily
    cell.index hpos hmatch
  have hup := ScaleFamily.matching_fourierIndex_upper mainParameterChoice.scaleFamily
    cell.index hpos hmatch
  have hk1 : (p.kStar : ℝ) = 1 := by rw [hp, seed_kStar]; simp
  rw [hk1, one_mul] at hlow hup
  have habsK : |((mainParameterChoice.fourierIndex cell : ℤ) : ℝ)| =
      (mainParameterChoice.scaleFamily.fourierIndex cell.index : ℝ) := by
    simp [GlobalParameterChoice.fourierIndex]
  have hse : 0 < Real.sqrt eps := Real.sqrt_pos.2 hpos
  have hrpow : eps ^ (-(1 / 2 : ℝ)) = (Real.sqrt eps)⁻¹ := by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg hpos.le]
  have hdivm : Real.sqrt (p.deltaMinus / eps) = Real.sqrt p.deltaMinus / Real.sqrt eps :=
    Real.sqrt_div hdm.le eps
  have hdivp : Real.sqrt (p.deltaPlus / eps) = Real.sqrt p.deltaPlus / Real.sqrt eps :=
    Real.sqrt_div hdp.le eps
  have hc : min (Real.sqrt p.deltaMinus)
      (1 / Real.sqrt ‖transverseStretchingCoefficient mainVelocity‖) ≤ Real.sqrt p.deltaMinus :=
    min_le_left _ _
  have hc' : min (Real.sqrt p.deltaMinus)
      (1 / Real.sqrt ‖transverseStretchingCoefficient mainVelocity‖) ≤
        1 / Real.sqrt ‖transverseStretchingCoefficient mainVelocity‖ := min_le_right _ _
  have hC : Real.sqrt p.deltaPlus ≤
      max (Real.sqrt p.deltaPlus) (1 / (2 * Real.pi * Real.sqrt p.deltaMinus)) :=
    le_max_left _ _
  have hC' : 1 / (2 * Real.pi * Real.sqrt p.deltaMinus) ≤
      max (Real.sqrt p.deltaPlus) (1 / (2 * Real.pi * Real.sqrt p.deltaMinus)) :=
    le_max_right _ _
  have hlowL := ReducedInductionMagneticScale.complexAxialMagneticLength_lower mainVelocity
    mainVelocity_isTransverseDivergenceFree eps hpos (mainParameterChoice.fourierIndex cell) hK
    lambda (mainGrowthFloor_pos.le.trans hfloor) b hb hreduced
  have hupL := complexAxialMagneticLength_le (mainParameterChoice.fourierIndex cell) hK hb
  rw [habsK] at hupL
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [habsK, hrpow]
    refine le_trans ?_ hlow
    rw [hdivm, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hc (inv_nonneg.2 hse.le)
  · rw [habsK, hrpow]
    refine hup.trans ?_
    rw [hdivp, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hC (inv_nonneg.2 hse.le)
  · refine le_trans ?_ hlowL
    rw [Real.sqrt_div hpos.le, div_eq_mul_one_div (Real.sqrt eps)]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left hc' hse.le
  · refine hupL.trans ?_
    have hKlow : Real.sqrt p.deltaMinus / Real.sqrt eps ≤
        (mainParameterChoice.scaleFamily.fourierIndex cell.index : ℝ) := hdivm ▸ hlow
    have hpos' : 0 < 2 * Real.pi * (Real.sqrt p.deltaMinus / Real.sqrt eps) := by positivity
    calc 1 / (2 * Real.pi * (mainParameterChoice.scaleFamily.fourierIndex cell.index : ℝ))
        ≤ 1 / (2 * Real.pi * (Real.sqrt p.deltaMinus / Real.sqrt eps)) :=
          one_div_le_one_div_of_le hpos'
            (mul_le_mul_of_nonneg_left hKlow (by positivity))
      _ = 1 / (2 * Real.pi * Real.sqrt p.deltaMinus) * Real.sqrt eps := by
          field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hC' hse.le
  · exact fun phase => realPhaseAxialMagneticLength_eq_complex _ hK phase hb

end

end FastDynamo
