/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalCurrentPullback
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalBedfordTaylorForms

/-! # Borel multiplication of finite positive current inputs
The full statements and entire mathematical proofs precede the source. -/

@[expose] public section

noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped Distributions ENNReal
namespace SGPT.Foundations.Analysis.Pending.PositiveCurrentBorelAddition
open FirstPass StronglyPositiveForms LocalProductCurrents LocalCurrentLebesgue
  LocalCurrentPullback LocalBedfordTaylorForms
attribute [local instance] LocalCurrentLebesgue.addCommGroupFormSpan
variable {n q : ℕ} {U : Opens (ComplexModel n)}

private theorem coefficient_measure_local_density_one
    {T : LocalProductCurrent n U q} (hT : IsPositive T) (γ : formSpan n q) :
    IsLocalDensity (U := U) (coeffMeasure hT γ) (fun _ => (1 : ℝ)) :=
  ⟨coeffMeasure_compl hT γ, coeffMeasure_lt_top hT γ,
    measurable_const, fun _ _ _ => ⟨1, fun _ _ => by simp⟩⟩

private theorem local_density_one_add
    {μ ν : Measure (ComplexModel n)}
    (hμ : IsLocalDensity (U := U) μ (fun _ => (1 : ℝ)))
    (hν : IsLocalDensity (U := U) ν (fun _ => (1 : ℝ))) :
    IsLocalDensity (U := U) (μ + ν) (fun _ => (1 : ℝ)) := by
  refine ⟨?_, ?_, measurable_const, fun _ _ _ => ⟨1, fun _ _ => by simp⟩⟩
  · rw [add_apply, hμ.compl, hν.compl, add_zero]
  · intro K hK hKU
    rw [add_apply]
    exact ENNReal.add_lt_top.mpr ⟨hμ.lt_top K hK hKU, hν.lt_top K hK hKU⟩

/-- Smooth representation and Borel-weight integrability are internally
proved from the actual positive coefficient measures. -/
private theorem positive_coefficient_add
    {D R : LocalProductCurrent n U q} (hD : IsPositive D) (hR : IsPositive R)
    {f : ComplexModel n → ℝ} (hf : Measurable f) (hfb : IsLocallyBoundedOn f U)
    {γ : formSpan n q} (hγ : γ ∈ posCone n q) (φ : 𝓓(U, ℝ)) :
    mulBorel (D + R) f γ φ = mulBorel D f γ φ + mulBorel R f γ φ := by
  let νD := coeffMeasure hD γ
  let νR := coeffMeasure hR γ
  have hνD : IsLocalDensity (U := U) νD (fun _ => (1 : ℝ)) :=
    coefficient_measure_local_density_one hD γ
  have hνR : IsLocalDensity (U := U) νR (fun _ => (1 : ℝ)) :=
    coefficient_measure_local_density_one hR γ
  have hiD (ψ : 𝓓(U, ℝ)) : Integrable (fun x => ψ x) νD := by
    simpa only [one_mul] using hνD.integrable (isTestWeight_testFunction ψ)
  have hiR (ψ : 𝓓(U, ℝ)) : Integrable (fun x => ψ x) νR := by
    simpa only [one_mul] using hνR.integrable (isTestWeight_testFunction ψ)
  have hrD : ∀ ψ : 𝓓(U, ℝ), D γ ψ = ∫ x, ψ x * (1 : ℝ) ∂νD := by
    intro ψ
    simpa only [mul_one] using (integral_coeffMeasure hD hγ ψ).symm
  have hrR : ∀ ψ : 𝓓(U, ℝ), R γ ψ = ∫ x, ψ x * (1 : ℝ) ∂νR := by
    intro ψ
    simpa only [mul_one] using (integral_coeffMeasure hR hγ ψ).symm
  have hrSum : ∀ ψ : 𝓓(U, ℝ), (D + R) γ ψ = ∫ x, ψ x * (1 : ℝ) ∂(νD + νR) := by
    intro ψ
    simp only [LinearMap.add_apply, _root_.add_apply]
    rw [hrD ψ, hrR ψ]
    simp only [mul_one]
    exact (integral_add_measure (hiD ψ) (hiR ψ)).symm
  have eSum := mulBorel_apply_of_integral_eq (hD.add hR) γ
    (local_density_one_add hνD hνR) hrSum hf hfb φ
  have eD := mulBorel_apply_of_integral_eq hD γ hνD hrD hf hfb φ
  have eR := mulBorel_apply_of_integral_eq hR γ hνR hrR hf hfb φ
  have hifD : Integrable (fun x => φ x * f x) νD := by
    simpa only [one_mul] using hνD.integrable (isTestWeight_mul φ hf hfb)
  have hifR : Integrable (fun x => φ x * f x) νR := by
    simpa only [one_mul] using hνR.integrable (isTestWeight_mul φ hf hfb)
  rw [eSum, eD, eR]
  simpa only [mul_one] using integral_add_measure hifD hifR

/-- Natural current-input additivity, distinguished from the existing
function-input theorem LocalProductCurrents.mulBorel_add. -/
theorem mulBorel_add_currents
    {D R : LocalProductCurrent n U q} (hD : IsPositive D) (hR : IsPositive R)
    {f : ComplexModel n → ℝ} (hf : Measurable f) (hfb : IsLocallyBoundedOn f U) :
    mulBorel (D + R) f = mulBorel D f + mulBorel R f := by
  ext γ φ
  obtain ⟨C, _, hm, hp⟩ := exists_orderUnit γ.2
  let δ : formSpan n q := C • kahlerPower n q
  have hm' : δ - γ ∈ posCone n q := by
    change C • formPower (standardHermitianTwoForm n) q - (γ : RealForm n (2 * q)) ∈ spCone q
    exact hm
  have hp' : δ + γ ∈ posCone n q := by
    change C • formPower (standardHermitianTwoForm n) q + (γ : RealForm n (2 * q)) ∈ spCone q
    exact hp
  have em := positive_coefficient_add hD hR hf hfb hm' φ
  have ep := positive_coefficient_add hD hR hf hfb hp' φ
  simp only [map_sub, map_add, _root_.sub_apply, _root_.add_apply] at em ep
  change mulBorel (D + R) f γ φ = mulBorel D f γ φ + mulBorel R f γ φ
  linarith

private theorem mulBorel_zero_current
    {f : ComplexModel n → ℝ} (hf : Measurable f) (hfb : IsLocallyBoundedOn f U) :
    mulBorel (0 : LocalProductCurrent n U q) f = 0 := by
  have e := mulBorel_add_currents
    (D := (0 : LocalProductCurrent n U q)) (R := 0) isPositive_zero isPositive_zero hf hfb
  ext γ φ
  have ev := congrArg (fun L : LocalProductCurrent n U q => L γ φ) e
  simp only [zero_add, LinearMap.add_apply, _root_.add_apply] at ev
  change mulBorel (0 : LocalProductCurrent n U q) f γ φ = 0
  linarith

private theorem isPositive_finsetSum {ι : Type*} (s : Finset ι)
    (T : ι → LocalProductCurrent n U q) (hT : ∀ i ∈ s, IsPositive (T i)) :
    IsPositive (∑ i ∈ s, T i) := by
  classical
  revert hT
  induction s using Finset.induction_on with
  | empty =>
      intro hT
      simpa only [Finset.sum_empty] using (isPositive_zero : IsPositive (0 : LocalProductCurrent n
        U q))
  | @insert i s his ih =>
      intro hT
      rw [Finset.sum_insert his]
      exact (hT i (Finset.mem_insert_self i s)).add
        (ih (fun j hj => hT j (Finset.mem_insert_of_mem hj)))

/-- Finite families need positivity only at selected indices. The empty
family is included; no total mass or connectedness hypothesis is present. -/
theorem mulBorel_finsetSum_positive {ι : Type*} (s : Finset ι)
    (T : ι → LocalProductCurrent n U q) (hT : ∀ i ∈ s, IsPositive (T i))
    {f : ComplexModel n → ℝ} (hf : Measurable f) (hfb : IsLocallyBoundedOn f U) :
    mulBorel (∑ i ∈ s, T i) f = ∑ i ∈ s, mulBorel (T i) f := by
  classical
  revert hT
  induction s using Finset.induction_on with
  | empty =>
      intro hT
      simpa only [Finset.sum_empty] using (mulBorel_zero_current (q := q) hf hfb)
  | @insert i s his ih =>
      intro hT
      have hTs : ∀ j ∈ s, IsPositive (T j) := fun j hj => hT j (Finset.mem_insert_of_mem hj)
      rw [Finset.sum_insert his, Finset.sum_insert his,
        mulBorel_add_currents (hT i (Finset.mem_insert_self i s))
          (isPositive_finsetSum s T hTs) hf hfb, ih hTs]

end SGPT.Foundations.Analysis.Pending.PositiveCurrentBorelAddition
