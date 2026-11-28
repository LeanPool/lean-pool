/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Risk.Credit.BernoulliMixture
public import LeanPool.MathFin.Probability.Dependence.GaussianCopula

/-!
# The one-factor default model is the one-factor Gaussian copula

The library writes the one-factor Gaussian default model in two parametrizations. The threshold
model of `Risk/Credit/BernoulliMixture.lean` (and of `VasicekIRB.lean`, `TrancheLoss.lean`) uses
the asset correlation `ρ ∈ [0, 1)`: obligor `i` defaults when `√ρ F + √(1 − ρ) εᵢ ≤ Φ⁻¹(π)`. The
copula of `Probability/Dependence/GaussianCopula.lean` uses a factor loading `ℓ ∈ [−1, 1]`, with
latent vector `ℓ Z₀ + √(1 − ℓ²) Zᵢ` and pairwise correlation `ℓ²`. This file proves that, with
`ℓ = √ρ`, they assign the same joint default probabilities at a common default probability `π`,
so that the library's parameter is the asset correlation `ρ`:

* `gaussianFactorCopula_sqrt_real_Iic_const`: the copula at loading `√ρ`, evaluated at
  `(π, …, π)`, is the mixture integral `∫ p(x)ⁿ dN(0,1)(x)` of
  `oneFactor_measureReal_iInter_default`, with `p = oneFactorPD π ρ`.
* `oneFactor_measureReal_iInter_default_eq_gaussianFactorCopula`: for any one-factor model on any
  probability space (`F`, `εᵢ` independent standard normals), the probability that all `n` names
  default is `C(π, …, π)` for the copula `C = gaussianFactorCopula n √ρ`.
* `integral_oneFactorPD_sq`, `oneFactor_measureReal_inter_default`: two names default together
  with probability `N₂(Φ⁻¹(π), Φ⁻¹(π); ρ)`, the standard bivariate normal CDF at correlation `ρ`
  (O. Vasicek, "Loan portfolio value", *Risk* 15(12) (2002)). With
  `oneFactor_measureReal_default`, the default covariance of two names is
  `N₂(Φ⁻¹(π), Φ⁻¹(π); ρ) − π²`; that corollary is not stated separately.

## Main results

* `gaussianFactorCopula_sqrt_real_Iic_const`: for `π ∈ (0, 1)` and `0 ≤ ρ < 1`, the Gaussian
  factor copula at loading `√ρ`, evaluated at `(π, …, π)`, is `∫ oneFactorPD π ρ (x) ^ n` against
  `N(0, 1)`.
* `oneFactor_measureReal_iInter_default_eq_gaussianFactorCopula`: for independent standard
  normals `F`, `ε₁, …, εₙ`, the probability that every name defaults, `√ρ F + √(1 − ρ) εᵢ ≤ Φ⁻¹(π)`
  for all `i`, is `C(π, …, π)` for the copula `C = gaussianFactorCopula n √ρ`.
* `integral_oneFactorPD_sq`: `∫ oneFactorPD π ρ (x) ^ 2 dN(0, 1) = N₂(Φ⁻¹(π), Φ⁻¹(π); ρ)`, the
  bivariate normal CDF at correlation `ρ`.
* `oneFactor_measureReal_inter_default`: two names default together with probability
  `N₂(Φ⁻¹(π), Φ⁻¹(π); ρ)` in the one-factor Gaussian threshold model.

## References

* [J. Hull and A. White, *Valuation of a CDO and an $n$-th to default CDS without Monte Carlo
  simulation*][HullWhite2004]
* [*QRM Exercise Book*][QRMExerciseBook], Ex. 11.9
* [O. Vasicek, *Loan portfolio value*][Vasicek2002]

## Tags

one-factor Gaussian copula, Vasicek model, asset correlation, factor loading,
joint default probability, bivariate normal, CDO modelling, MSC 91G40, MSC 62H05, JEL G32
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Set

variable {n : ℕ}

/-! ### The factors of `stdNormalFactors` -/

/-- On the factor space the systematic factor `z₀` is standard normal. -/
lemma hasLaw_fst_stdNormalFactors :
    HasLaw (Prod.fst : ℝ × (Fin n → ℝ) → ℝ) (gaussianReal 0 1) (stdNormalFactors n) :=
  measurePreserving_fst.hasLaw

/-- On the factor space each idiosyncratic factor `zᵢ` is standard normal. -/
lemma hasLaw_snd_apply_stdNormalFactors (i : Fin n) :
    HasLaw (fun z : ℝ × (Fin n → ℝ) ↦ z.2 i) (gaussianReal 0 1) (stdNormalFactors n) :=
  ((measurePreserving_eval (fun _ : Fin n ↦ gaussianReal 0 1) i).comp measurePreserving_snd).hasLaw

/-- On the factor space the idiosyncratic factors are independent. -/
lemma iIndepFun_snd_stdNormalFactors :
    iIndepFun (fun i (z : ℝ × (Fin n → ℝ)) ↦ z.2 i) (stdNormalFactors n) := by
  refine (iIndepFun_iff_map_fun_eq_pi_map fun i ↦
    (hasLaw_snd_apply_stdNormalFactors i).aemeasurable).2 ?_
  rw [show (fun (z : ℝ × (Fin n → ℝ)) (i : Fin n) ↦ z.2 i) = Prod.snd from rfl,
    Measure.map_snd_prod, measure_univ, one_smul]
  exact congrArg Measure.pi (funext fun i ↦ (hasLaw_snd_apply_stdNormalFactors i).map_eq.symm)

/-- On the factor space the systematic factor is independent of the idiosyncratic ones. -/
lemma indepFun_fst_snd_stdNormalFactors :
    (Prod.fst : ℝ × (Fin n → ℝ) → ℝ) ⟂ᵢ[stdNormalFactors n] fun z i ↦ z.2 i :=
  indepFun_prod (X := (id : ℝ → ℝ)) (Y := (id : (Fin n → ℝ) → Fin n → ℝ)) measurable_id
    measurable_id

/-- On the factor space, the event that every name's latent variable `√ρ z₀ + √(1 − ρ) zᵢ` lies
below `Φ⁻¹(π)` has probability `∫ p(x)ⁿ dN(0,1)(x)`. -/
private lemma measureReal_iInter_stdNormalFactors {π ρ : ℝ} (hρ1 : ρ < 1) :
    (stdNormalFactors n).real
        (⋂ i ∈ (Finset.univ : Finset (Fin n)),
          {z : ℝ × (Fin n → ℝ) | √ρ * z.1 + √(1 - ρ) * z.2 i ≤ PhiInv π}) =
      ∫ x, oneFactorPD π ρ x ^ n ∂gaussianReal 0 1 := by
  rw [oneFactor_measureReal_iInter_default hasLaw_fst_stdNormalFactors
    hasLaw_snd_apply_stdNormalFactors iIndepFun_snd_stdNormalFactors
    indepFun_fst_snd_stdNormalFactors hρ1, Finset.card_univ, Fintype.card_fin]

/-! ### All names: the copula at `(π, …, π)` -/

/-- **The one-factor copula at loading `√ρ` is the one-factor default model.** For `π ∈ (0, 1)`
and `0 ≤ ρ < 1`, the Gaussian factor copula at loading `√ρ` assigns to `[0, π]ⁿ` the mixture
integral `∫ p(x)ⁿ dN(0,1)(x)`, `p(x) = Φ((Φ⁻¹(π) − √ρ x)/√(1 − ρ))`, which is the probability
that all `n` names of the asset-correlation-`ρ` threshold model default
(`oneFactor_measureReal_iInter_default`). -/
theorem gaussianFactorCopula_sqrt_real_Iic_const {π ρ : ℝ} (hπ : π ∈ Ioo 0 1) (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) :
    (gaussianFactorCopula n √ρ).real (Iic fun _ ↦ π) =
      ∫ x, oneFactorPD π ρ x ^ n ∂gaussianReal 0 1 := by
  have hρ' : √ρ ∈ Icc (-1) 1 :=
    ⟨by linarith [Real.sqrt_nonneg ρ], (Real.sqrt_le_sqrt hρ1.le).trans_eq Real.sqrt_one⟩
  rw [gaussianFactorCopula_real_Iic hρ' _ fun _ ↦ hπ, ← measureReal_iInter_stdNormalFactors hρ1]
  congr 1
  ext z
  simp [gaussianFactorVec, Pi.le_def, Real.sq_sqrt hρ0]

/-- **The joint default probability of the one-factor model is the Gaussian factor copula.** Let
`F` and `ε₁, …, εₙ` be independent standard normals on any probability space, `π ∈ (0, 1)` and
`0 ≤ ρ < 1`. The probability that every name defaults, `√ρ F + √(1 − ρ) εᵢ ≤ Φ⁻¹(π)` for all `i`,
is `C(π, …, π)` for the copula `C = gaussianFactorCopula n √ρ`. -/
theorem oneFactor_measureReal_iInter_default_eq_gaussianFactorCopula {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {π ρ : ℝ} {F : Ω → ℝ}
    {ε : Fin n → Ω → ℝ} (hF : HasLaw F (gaussianReal 0 1) P)
    (hε : ∀ i, HasLaw (ε i) (gaussianReal 0 1) P) (hεind : iIndepFun ε P)
    (hFε : F ⟂ᵢ[P] fun ω i ↦ ε i ω) (hπ : π ∈ Ioo 0 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    P.real (⋂ i, {ω | √ρ * F ω + √(1 - ρ) * ε i ω ≤ PhiInv π}) =
      (gaussianFactorCopula n √ρ).real (Iic fun _ ↦ π) := by
  have h := oneFactor_measureReal_iInter_default (π := π) hF hε hεind hFε hρ1 Finset.univ
  rw [Finset.card_univ, Fintype.card_fin] at h
  rw [gaussianFactorCopula_sqrt_real_Iic_const hπ hρ0 hρ1, ← h]
  simp

/-! ### Two names: the bivariate normal CDF -/

/-- **Vasicek's joint default probability**: `∫ p(x)² dN(0,1)(x) = N₂(Φ⁻¹(π), Φ⁻¹(π); ρ)` for
`0 ≤ ρ < 1`, where `p = oneFactorPD π ρ`. Both sides are the probability that two names of the
factor space default together: the left by the mixture formula, the right because the two latent
variables form a standard bivariate normal pair with correlation `(√ρ)² = ρ`
(`measureReal_gaussianFactorVec_le`). -/
theorem integral_oneFactorPD_sq {π ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    ∫ x, oneFactorPD π ρ x ^ 2 ∂gaussianReal 0 1 = bivariateNormalCDF (PhiInv π) (PhiInv π) ρ := by
  have hρ' : √ρ ∈ Icc (-1) 1 :=
    ⟨by linarith [Real.sqrt_nonneg ρ], (Real.sqrt_le_sqrt hρ1.le).trans_eq Real.sqrt_one⟩
  have h := measureReal_gaussianFactorVec_le hρ' (show (0 : Fin 2) ≠ 1 by decide)
    (PhiInv π) (PhiInv π)
  rw [Real.sq_sqrt hρ0] at h
  rw [← h, ← measureReal_iInter_stdNormalFactors hρ1]
  congr 1
  ext z
  simp [gaussianFactorVec, Fin.forall_fin_two, Real.sq_sqrt hρ0]

/-- **Two names default together with probability `N₂(Φ⁻¹(π), Φ⁻¹(π); ρ)`** in the one-factor
Gaussian threshold model with asset correlation `ρ ∈ [0, 1)`: `F` and the `εᵢ` are independent
standard normals on any probability space, and `i ≠ j`. -/
theorem oneFactor_measureReal_inter_default {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {ι : Type*} [Finite ι] {π ρ : ℝ} {F : Ω → ℝ} {ε : ι → Ω → ℝ}
    (hF : HasLaw F (gaussianReal 0 1) P) (hε : ∀ i, HasLaw (ε i) (gaussianReal 0 1) P)
    (hεind : iIndepFun ε P) (hFε : F ⟂ᵢ[P] fun ω i ↦ ε i ω) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    {i j : ι} (hij : i ≠ j) :
    P.real ({ω | √ρ * F ω + √(1 - ρ) * ε i ω ≤ PhiInv π} ∩
        {ω | √ρ * F ω + √(1 - ρ) * ε j ω ≤ PhiInv π}) =
      bivariateNormalCDF (PhiInv π) (PhiInv π) ρ := by
  classical
  have h := oneFactor_measureReal_iInter_default (π := π) hF hε hεind hFε hρ1 {i, j}
  rw [Finset.card_pair hij, integral_oneFactorPD_sq hρ0 hρ1, Finset.set_biInter_insert,
    Finset.set_biInter_singleton] at h
  exact h

end MathFin
