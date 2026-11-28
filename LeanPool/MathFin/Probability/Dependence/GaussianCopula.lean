/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye, Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Dependence.Sklar
public import LeanPool.MathFin.Probability.Gaussian.BivariateNormalCDF
public import Mathlib.Algebra.Order.Star.Real

/-!
# The one-factor Gaussian copula

The **one-factor Gaussian copula** on `n` names with factor loading `ρ ∈ [−1, 1]` is the copula of
the latent vector
`Xᵢ = ρ Z₀ + √(1 − ρ²) Zᵢ`, `i : Fin n`,
where the systematic factor `Z₀` and the idiosyncratic factors `Z₁, …, Zₙ` are independent standard
normals (`stdNormalFactors`). Every `Xᵢ` is standard normal (`map_gaussianFactorVec`),
`Cov(Xᵢ, Xⱼ) = ρ²` for `i ≠ j` (`covariance_gaussianFactorVec`), and each pair `(Xᵢ, Xⱼ)` has the
standard bivariate normal law with correlation `ρ²` (`map_pair_gaussianFactorVec`, through
`eq_bivariateNormalLaw`). Loadings `ρ` and `−ρ` give the same copula
(`gaussianFactorCopula_neg`), so the family is parametrized by the pairwise correlation `ρ²`
alone. The library's one-factor default model (`Risk/Credit/BernoulliMixture.lean`,
`VasicekIRB.lean`, `TrancheLoss.lean`) is written in that parameter, the asset correlation `ρ` of
`√ρ F + √(1 − ρ) εᵢ`; the probability that all its names default at a common default
probability `π` is this copula at loading `√ρ`, evaluated at `(π, …, π)`
(`Risk/Credit/OneFactorCopula.lean`). Name `i` defaults by time `t` when `Xᵢ ≤ Φ⁻¹(pᵢ(t))`.

We take the factors as a point `(z₀, z) : ℝ × (Fin n → ℝ)` under the product of standard normal
laws, with the systematic factor in the first slot, so that every name is treated symmetrically.
(A common bivariate construction instead writes the pair as `(Z₁, ρ Z₁ + √(1 − ρ²) Z₂)`, with
correlation `ρ`; the symmetric model here has pairwise correlation `ρ²`, never negative.)

The copula is defined via `copulaOf`, so being a copula is Sklar's theorem.

## Main definitions

* `stdNormalFactors`: the product of `n + 1` standard normal laws on `ℝ × (Fin n → ℝ)`, the
  systematic factor `Z₀` in the first slot and the idiosyncratic factors in the second.
* `gaussianFactorVec`: the latent vector `Xᵢ = ρ z₀ + √(1 − ρ²) zᵢ`.
* `gaussianFactorCopula`: the copula of `gaussianFactorVec ρ` under `stdNormalFactors n`.

## Main results

* `gaussianFactorCopula`, `isCopula_gaussianFactorCopula`, `gaussianFactorCopula_real_Iic`.
* `covariance_gaussianFactorVec`, `map_pair_gaussianFactorVec`, `measureReal_gaussianFactorVec_le`:
  pairwise covariance `ρ²`, bivariate normal pairs, and the pairwise joint distribution function
  `P(Xᵢ ≤ a, Xⱼ ≤ b) = N₂(a, b; ρ²)`.
* `gaussianFactorCopula_neg`: loadings `ρ` and `−ρ` give the same copula.
* `gaussianFactorCopula_zero`: `ρ = 0` gives the independence copula `Π`.
* `gaussianFactorCopula_one`: `ρ = 1` gives the comonotonicity copula `M` (so does `ρ = −1`, by
  `gaussianFactorCopula_neg`).

The countermonotonicity copula `W` (`countermonotoneCopula`) is defined on `Fin 2` only (for `d ≥ 3`
the lower Fréchet bound is not a copula, `not_exists_isCopula_frechetLower`). Since the pairwise
correlations `ρ²` are nonnegative, `W` is not a member of this family; that is not stated as a
lemma.

## References

* [J. Hull and A. White, *Valuation of a CDO and an $n$-th to default CDS without Monte Carlo
  simulation*][HullWhite2004]

## Tags

Gaussian copula, one-factor model, factor loading, asset correlation, default dependence,
latent variable, MSC 62H05, MSC 91G40, JEL G32
-/
@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Set

variable {n : ℕ} {ρ : ℝ}

/-- The law of the factors of the one-factor model: a systematic standard normal `Z₀` and `n`
idiosyncratic standard normals, all independent. -/
noncomputable abbrev stdNormalFactors (n : ℕ) : Measure (ℝ × (Fin n → ℝ)) :=
  (gaussianReal 0 1).prod (stdNormalVec (Fin n))

/-- The **one-factor Gaussian latent vector** `Xᵢ = ρ z₀ + √(1 − ρ²) zᵢ`. -/
noncomputable def gaussianFactorVec (ρ : ℝ) (z : ℝ × (Fin n → ℝ)) : Fin n → ℝ :=
  fun i ↦ ρ * z.1 + √(1 - ρ ^ 2) * z.2 i

@[fun_prop] lemma measurable_gaussianFactorVec (ρ : ℝ) :
    Measurable (gaussianFactorVec (n := n) ρ) :=
  measurable_pi_iff.2 fun i ↦ by unfold gaussianFactorVec; fun_prop

/-- `(Z₀, Zᵢ)` is a pair of independent standard normals. -/
lemma map_stdNormalFactors_pair (i : Fin n) :
    (stdNormalFactors n).map (fun z ↦ (z.1, z.2 i)) = stdNormalPair := by
  rw [show (fun z : ℝ × (Fin n → ℝ) ↦ (z.1, z.2 i)) = Prod.map id (fun w ↦ w i) from rfl,
    ← Measure.map_prod_map _ _ measurable_id (measurable_pi_apply i), Measure.map_id,
    (measurePreserving_eval (fun _ ↦ gaussianReal 0 1) i).map_eq]

/-- For `ρ ∈ [−1, 1]` every coordinate of the latent vector is standard normal. -/
lemma map_gaussianFactorVec (hρ : ρ ∈ Icc (-1) 1) (i : Fin n) :
    (stdNormalFactors n).map (fun z ↦ gaussianFactorVec ρ z i) = gaussianReal 0 1 := by
  rw [show (fun z ↦ gaussianFactorVec ρ z i) =
      (fun p : ℝ × ℝ ↦ ρ * p.1 + √(1 - ρ ^ 2) * p.2) ∘ (fun z ↦ (z.1, z.2 i)) from rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop), map_stdNormalFactors_pair,
    map_linear_stdNormalPair, Real.sq_sqrt (by nlinarith [hρ.1, hρ.2]), add_sub_cancel,
    Real.toNNReal_one]

/-- `Φ` pushes the standard normal law to the uniform law on `(0, 1)`. -/
lemma map_Phi_gaussianReal : (gaussianReal 0 1).map Phi = volume.restrict (Ioo 0 1) := by
  simpa [cdf_gaussianReal_zero_one] using (hasLaw_cdf (μ := gaussianReal 0 1) HasLaw.id
    (by rw [cdf_gaussianReal_zero_one]; exact continuous_Phi)).map_eq

/-! ### Moments and pairs of the latent vector -/

/-- The systematic factor is square integrable. -/
private lemma memLp_fst_stdNormalFactors :
    MemLp (fun z : ℝ × (Fin n → ℝ) ↦ z.1) 2 (stdNormalFactors n) :=
  (memLp_id_gaussianReal' 2 (by simp)).comp_fst _

/-- Each idiosyncratic factor is square integrable. -/
private lemma memLp_snd_apply_stdNormalFactors (k : Fin n) :
    MemLp (fun z : ℝ × (Fin n → ℝ) ↦ z.2 k) 2 (stdNormalFactors n) :=
  (memLp_eval_stdNormalVec k).comp_snd _

/-- Each latent coordinate is centred. -/
lemma integral_gaussianFactorVec (hρ : ρ ∈ Icc (-1) 1) (i : Fin n) :
    ∫ z, gaussianFactorVec ρ z i ∂stdNormalFactors n = 0 := by
  have h := integral_id_gaussianReal (μ := 0) (v := 1)
  rw [← map_gaussianFactorVec hρ i, integral_map (by fun_prop) (by fun_prop)] at h
  exact h

/-- Each latent coordinate has unit variance. -/
lemma variance_gaussianFactorVec (hρ : ρ ∈ Icc (-1) 1) (i : Fin n) :
    Var[fun z ↦ gaussianFactorVec ρ z i; stdNormalFactors n] = 1 := by
  rw [← variance_id_map (by fun_prop), map_gaussianFactorVec hρ i, variance_id_gaussianReal,
    NNReal.coe_one]

/-- **Pairwise covariance `ρ²`**: for `i ≠ j`, `Cov(Xᵢ, Xⱼ) = ρ²`, for every `ρ`. Only the
systematic factor is shared: `Cov(Z₀, Z₀) = 1`, while `Z₀`, `Zᵢ`, `Zⱼ` are pairwise uncorrelated. -/
theorem covariance_gaussianFactorVec (ρ : ℝ) {i j : Fin n} (hij : i ≠ j) :
    cov[fun z ↦ gaussianFactorVec ρ z i, fun z ↦ gaussianFactorVec ρ z j; stdNormalFactors n] =
      ρ ^ 2 := by
  have h₀ := memLp_fst_stdNormalFactors (n := n)
  have hA : MemLp (fun z : ℝ × (Fin n → ℝ) ↦ ρ * z.1) 2 (stdNormalFactors n) := h₀.const_mul ρ
  have hB (k : Fin n) :
      MemLp (fun z : ℝ × (Fin n → ℝ) ↦ √(1 - ρ ^ 2) * z.2 k) 2 (stdNormalFactors n) :=
    (memLp_snd_apply_stdNormalFactors k).const_mul _
  -- the covariances of the factors
  have c00 : cov[fun z : ℝ × (Fin n → ℝ) ↦ z.1, fun z ↦ z.1; stdNormalFactors n] = 1 := by
    rw [covariance_self h₀.aemeasurable]
    have h := (measurePreserving_fst (μ := gaussianReal 0 1)
      (ν := stdNormalVec (Fin n))).variance_fun_comp (f := id) aemeasurable_id
    rw [variance_id_gaussianReal] at h
    exact h.trans NNReal.coe_one
  have c0 (k : Fin n) : cov[fun z : ℝ × (Fin n → ℝ) ↦ z.1, fun z ↦ z.2 k; stdNormalFactors n] = 0 :=
    covariance_fst_snd_prod (memLp_id_gaussianReal' 2 (by simp)) (memLp_eval_stdNormalVec k)
  have ci0 : cov[fun z : ℝ × (Fin n → ℝ) ↦ z.2 i, fun z ↦ z.1; stdNormalFactors n] = 0 := by
    rw [covariance_comm, c0 i]
  have cij : cov[fun z : ℝ × (Fin n → ℝ) ↦ z.2 i, fun z ↦ z.2 j; stdNormalFactors n] = 0 := by
    have hsnd : (stdNormalFactors n).map Prod.snd = stdNormalVec (Fin n) := by
      rw [Measure.map_snd_prod, measure_univ, one_smul]
    have h := covariance_map_fun (μ := stdNormalFactors n) (X := fun w : Fin n → ℝ ↦ w i)
      (Y := fun w ↦ w j) (Z := Prod.snd) (measurable_pi_apply i).aestronglyMeasurable
      (measurable_pi_apply j).aestronglyMeasurable measurable_snd.aemeasurable
    rw [hsnd] at h
    exact h.symm.trans <| ((iIndepFun_pi (μ := fun _ : Fin n ↦ gaussianReal 0 1)
      (X := fun _ : Fin n ↦ (id : ℝ → ℝ)) fun _ ↦ aemeasurable_id).indepFun hij).covariance_eq_zero
        (memLp_eval_stdNormalVec i) (memLp_eval_stdNormalVec j)
  -- bilinearity
  change cov[(fun z : ℝ × (Fin n → ℝ) ↦ ρ * z.1) + fun z ↦ √(1 - ρ ^ 2) * z.2 i,
    (fun z : ℝ × (Fin n → ℝ) ↦ ρ * z.1) + fun z ↦ √(1 - ρ ^ 2) * z.2 j; stdNormalFactors n] = ρ ^ 2
  rw [covariance_add_left hA (hB i) (hA.add (hB j)), covariance_add_right hA hA (hB j),
    covariance_add_right (hB i) hA (hB j)]
  simp only [covariance_const_mul_left, covariance_const_mul_right]
  linear_combination ρ ^ 2 * c00 + ρ * √(1 - ρ ^ 2) * c0 j + √(1 - ρ ^ 2) * ρ * ci0 +
    √(1 - ρ ^ 2) ^ 2 * cij

/-- The pair `(Xᵢ, Xⱼ)` as a continuous linear image of the factors. -/
private noncomputable def gaussianFactorPairCLM (ρ : ℝ) (i j : Fin n) :
    ℝ × (Fin n → ℝ) →L[ℝ] ℝ × ℝ :=
  (ρ • ContinuousLinearMap.fst ℝ ℝ (Fin n → ℝ) + √(1 - ρ ^ 2) •
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ ℝ) i).comp
        (ContinuousLinearMap.snd ℝ ℝ (Fin n → ℝ))).prod
    (ρ • ContinuousLinearMap.fst ℝ ℝ (Fin n → ℝ) + √(1 - ρ ^ 2) •
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ ℝ) j).comp
        (ContinuousLinearMap.snd ℝ ℝ (Fin n → ℝ)))

/-- **Each pair of latent coordinates is standard bivariate normal with correlation `ρ²`**: for
`ρ ∈ [−1, 1]` and `i ≠ j`, the law of `(Xᵢ, Xⱼ)` is `bivariateNormalLaw (ρ²)`. The pair is a
continuous linear image of the Gaussian factors, hence Gaussian, with centred unit-variance
coordinates and covariance `ρ²` (`covariance_gaussianFactorVec`); `eq_bivariateNormalLaw`
identifies it. -/
theorem map_pair_gaussianFactorVec (hρ : ρ ∈ Icc (-1) 1) {i j : Fin n} (hij : i ≠ j) :
    (stdNormalFactors n).map (fun z ↦ (gaussianFactorVec ρ z i, gaussianFactorVec ρ z j)) =
      bivariateNormalLaw (ρ ^ 2) := by
  have hpair : ⇑(gaussianFactorPairCLM ρ i j) =
      fun z ↦ (gaussianFactorVec ρ z i, gaussianFactorVec ρ z j) := by
    funext z
    simp [gaussianFactorPairCLM, gaussianFactorVec]
  have : IsGaussian ((stdNormalFactors n).map
      fun z ↦ (gaussianFactorVec ρ z i, gaussianFactorVec ρ z j)) := by
    have h : IsGaussian ((stdNormalFactors n).map (gaussianFactorPairCLM ρ i j)) := inferInstance
    rwa [hpair] at h
  have hm : Measurable fun z : ℝ × (Fin n → ℝ) ↦
      (gaussianFactorVec ρ z i, gaussianFactorVec ρ z j) := by
    fun_prop
  have hρ2 : ρ ^ 2 ≤ 1 := by nlinarith [hρ.1, hρ.2]
  refine eq_bivariateNormalLaw (by nlinarith [hρ2, sq_nonneg ρ]) ?_ ?_ ?_ ?_ ?_
  · rw [integral_map hm.aemeasurable measurable_fst.aestronglyMeasurable]
    exact integral_gaussianFactorVec hρ i
  · rw [integral_map hm.aemeasurable measurable_snd.aestronglyMeasurable]
    exact integral_gaussianFactorVec hρ j
  · rw [variance_map measurable_fst.aemeasurable hm.aemeasurable]
    exact variance_gaussianFactorVec hρ i
  · rw [variance_map measurable_snd.aemeasurable hm.aemeasurable]
    exact variance_gaussianFactorVec hρ j
  · rw [covariance_map_fun measurable_fst.aestronglyMeasurable measurable_snd.aestronglyMeasurable
      hm.aemeasurable]
    exact covariance_gaussianFactorVec ρ hij

/-- **Pairwise joint distribution function**: for `ρ ∈ [−1, 1]` and `i ≠ j`,
`P(Xᵢ ≤ a, Xⱼ ≤ b) = N₂(a, b; ρ²)`. -/
theorem measureReal_gaussianFactorVec_le (hρ : ρ ∈ Icc (-1) 1) {i j : Fin n} (hij : i ≠ j)
    (a b : ℝ) :
    (stdNormalFactors n).real {z | gaussianFactorVec ρ z i ≤ a ∧ gaussianFactorVec ρ z j ≤ b} =
      bivariateNormalCDF a b (ρ ^ 2) := by
  rw [bivariateNormalCDF_eq_law, ← map_pair_gaussianFactorVec hρ hij,
    map_measureReal_apply (by fun_prop) (measurableSet_Iic.prod measurableSet_Iic)]
  rfl

/-! ### The copula -/

/-- The **one-factor Gaussian copula** on `n` names with loading `ρ`: the copula of
`gaussianFactorVec ρ`. It is a copula for `ρ ∈ [−1, 1]` (`isCopula_gaussianFactorCopula`). -/
noncomputable def gaussianFactorCopula (n : ℕ) (ρ : ℝ) : Measure (Fin n → ℝ) :=
  copulaOf (gaussianFactorVec ρ) (stdNormalFactors n)

/-- Each marginal CDF of the latent vector is `Φ`, hence continuous — the hypothesis Sklar's
theorem needs. -/
lemma continuous_cdf_gaussianFactorVec (hρ : ρ ∈ Icc (-1) 1) (i : Fin n) :
    Continuous (cdf ((stdNormalFactors n).map fun z ↦ gaussianFactorVec ρ z i)) := by
  rw [map_gaussianFactorVec hρ, cdf_gaussianReal_zero_one]
  exact continuous_Phi

/-- For `ρ ∈ [−1, 1]` the copula is the law of `(Φ(X₁), …, Φ(Xₙ))`. -/
lemma gaussianFactorCopula_eq_map (hρ : ρ ∈ Icc (-1) 1) :
    gaussianFactorCopula n ρ =
      (stdNormalFactors n).map fun z i ↦ Phi (gaussianFactorVec ρ z i) := by
  simp only [gaussianFactorCopula, copulaOf, map_gaussianFactorVec hρ, cdf_gaussianReal_zero_one]

/-- **The one-factor Gaussian copula is a copula** for every `ρ ∈ [−1, 1]`. -/
theorem isCopula_gaussianFactorCopula (hρ : ρ ∈ Icc (-1) 1) : IsCopula (gaussianFactorCopula n ρ) :=
  isCopula_copulaOf (measurable_gaussianFactorVec ρ).aemeasurable
    (continuous_cdf_gaussianFactorVec hρ)

/-- **Distribution function**: on `(0, 1)ⁿ`, `C(u) = P(Xᵢ ≤ Φ⁻¹(uᵢ) for all i)`. -/
theorem gaussianFactorCopula_real_Iic (hρ : ρ ∈ Icc (-1) 1) (u : Fin n → ℝ)
    (hu : ∀ i, u i ∈ Ioo 0 1) :
    (gaussianFactorCopula n ρ).real (Iic u) =
      (stdNormalFactors n).real {z | gaussianFactorVec ρ z ≤ fun i ↦ PhiInv (u i)} := by
  rw [measureReal_le_eq_copulaOf (measurable_gaussianFactorVec ρ).aemeasurable
    (continuous_cdf_gaussianFactorVec hρ)]
  simp only [map_gaussianFactorVec hρ, cdf_gaussianReal_zero_one]
  rw [show (fun i ↦ Phi (PhiInv (u i))) = u from funext fun i ↦ Phi_PhiInv (hu i)]
  rfl

/-! ### The independence and comonotone members -/

/-- **`ρ = 0` gives the independence copula** `Π`. -/
theorem gaussianFactorCopula_zero : gaussianFactorCopula n 0 = independenceCopula (Fin n) := by
  have hf : (fun z : ℝ × (Fin n → ℝ) ↦ fun i ↦ Phi (gaussianFactorVec 0 z i)) =
      (fun w i ↦ Phi (w i)) ∘ Prod.snd := by
    ext z i; simp [gaussianFactorVec]
  rw [gaussianFactorCopula_eq_map (by norm_num), hf,
    ← Measure.map_map (by fun_prop) measurable_snd, Measure.map_snd_prod, measure_univ, one_smul,
    Measure.pi_map_pi (fun _ ↦ measurable_Phi.aemeasurable)]
  simp [map_Phi_gaussianReal, independenceCopula]

/-- **`ρ = 1` gives the comonotonicity copula** `M`: every name loads only on `Z₀`. -/
theorem gaussianFactorCopula_one : gaussianFactorCopula n 1 = comonotoneCopula (Fin n) := by
  have hf : (fun z : ℝ × (Fin n → ℝ) ↦ fun i ↦ Phi (gaussianFactorVec 1 z i)) =
      (fun t _ ↦ t) ∘ Phi ∘ Prod.fst := by
    ext z i; simp [gaussianFactorVec]
  rw [gaussianFactorCopula_eq_map (by norm_num), hf,
    ← Measure.map_map (by fun_prop) (measurable_Phi.comp measurable_fst),
    ← Measure.map_map measurable_Phi measurable_fst, Measure.map_fst_prod, measure_univ, one_smul]
  simp [map_Phi_gaussianReal, comonotoneCopula]

/-- **The copula sees the loading only through `ρ²`**: loadings `ρ` and `−ρ` give the same copula.
Negating the systematic factor preserves its law and turns one latent vector into the other. -/
theorem gaussianFactorCopula_neg (hρ : ρ ∈ Icc (-1) 1) :
    gaussianFactorCopula n (-ρ) = gaussianFactorCopula n ρ := by
  have hρ' : -ρ ∈ Icc (-1) 1 := ⟨by linarith [hρ.2], by linarith [hρ.1]⟩
  have hN : (stdNormalFactors n).map (fun z : ℝ × (Fin n → ℝ) ↦ (-z.1, z.2)) =
      stdNormalFactors n := by
    rw [show (fun z : ℝ × (Fin n → ℝ) ↦ (-z.1, z.2)) = Prod.map (fun x : ℝ ↦ -x) id from rfl,
      ← Measure.map_prod_map _ _ (by fun_prop) measurable_id, gaussianReal_map_neg, neg_zero,
      Measure.map_id]
  have hf : (fun z : ℝ × (Fin n → ℝ) ↦ fun i ↦ Phi (gaussianFactorVec (-ρ) z i)) =
      (fun z i ↦ Phi (gaussianFactorVec ρ z i)) ∘ fun z ↦ (-z.1, z.2) := by
    ext z i
    simp [gaussianFactorVec]
  rw [gaussianFactorCopula_eq_map hρ', gaussianFactorCopula_eq_map hρ, hf,
    ← Measure.map_map (by fun_prop) (by fun_prop), hN]

end MathFin
