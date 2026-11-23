/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.GaussianTransport.MomentComparison
public import LeanPool.CutoffRigidity.GaussianTransport.Projection
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import TauCeti.MeasureTheory.OptimalTransport.Cost.Basic

/-! # Quadratic Wasserstein lower bound from Gaussian-coordinate moments -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace CutoffRigidity.Riemann

section Split

variable {M N : Type*} [PseudoEMetricSpace M] [MeasurableSpace M] [OpensMeasurableSpace M]
  [PseudoEMetricSpace N] [MeasurableSpace N] {k : ℕ} {ρ : ℝ} {μ : Measure M}

namespace SplitData

variable (D : SplitData M N k ρ μ)

/-- Gaussian moments of the Euclidean coordinate under the equilibrium measure. -/
theorem proj_moments (hρ : 0 < ρ) :
    (∀ a : EuclideanSpace ℝ (Fin k), ∫ y, ⟪a, D.proj y⟫ ∂μ = 0) ∧
    Integrable (fun y => ‖D.proj y‖ ^ 2) μ ∧ ∫ y, ‖D.proj y‖ ^ 2 ∂μ = k / ρ := by
  have hS : (ρ⁻¹ • (1 : Matrix (Fin k) (Fin k) ℝ)).PosSemidef :=
    Matrix.PosSemidef.one.smul (inv_nonneg.mpr hρ.le)
  set γ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin k))
    (ρ⁻¹ • (1 : Matrix (Fin k) (Fin k) ℝ)) with hγ
  have hmap := D.map_proj_eq
  have hpm : AEMeasurable D.proj μ := D.measurable_proj.aemeasurable
  have hid : Integrable (fun x : EuclideanSpace ℝ (Fin k) => x) γ := IsGaussian.integrable_id
  have hm2 : MemLp id 2 γ := IsGaussian.memLp_two_id
  have hint2 : Integrable (fun x : EuclideanSpace ℝ (Fin k) => ‖x‖ ^ 2) γ := by
    have := hm2.integrable_norm_pow (p := 2) (by norm_num)
    simpa using this
  refine ⟨fun a => ?_, ?_, ?_⟩
  · have : ∫ y, ⟪a, D.proj y⟫ ∂μ = ∫ x, ⟪a, x⟫ ∂(μ.map D.proj) := by
      rw [integral_map hpm (by fun_prop)]
    rw [this, hmap, integral_inner hid, hγ, integral_id_multivariateGaussian]
    simp
  · have := (integrable_map_measure (f := D.proj)
      (g := fun x : EuclideanSpace ℝ (Fin k) => ‖x‖ ^ 2) (by fun_prop) hpm).1
      (by rw [hmap]; exact hint2)
    exact this
  · have : ∫ y, ‖D.proj y‖ ^ 2 ∂μ = ∫ x, ‖x‖ ^ 2 ∂(μ.map D.proj) := by
      rw [integral_map hpm (by fun_prop)]
    rw [this, hmap]
    have hcoord : ∀ i : Fin k, ∫ x, x i ^ 2 ∂γ = ρ⁻¹ := by
      intro i
      have hL : MemLp (fun x : EuclideanSpace ℝ (Fin k) => x i) 2 γ :=
        (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ).comp_memLp' hm2
      have h3 : ∫ x, x i ∂γ = 0 := by
        have := (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ).integral_comp_comm hid
        simpa [hγ] using this
      have h1 := variance_of_integral_eq_zero hL.aemeasurable h3
      have h2 := variance_eval_multivariateGaussian (μ := (0 : EuclideanSpace ℝ (Fin k))) hS i
      rw [h2] at h1
      simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h1
      simpa using h1.symm
    have e : ∀ x : EuclideanSpace ℝ (Fin k), ‖x‖ ^ 2 = ∑ i, x i ^ 2 := fun x => by
      rw [EuclideanSpace.norm_sq_eq]; simp
    simp_rw [e]
    have hint_i : ∀ i ∈ (Finset.univ : Finset (Fin k)),
        Integrable (fun x : EuclideanSpace ℝ (Fin k) => x i ^ 2) γ := fun i _ => by
      have hL : MemLp (fun x : EuclideanSpace ℝ (Fin k) => x i) 2 γ :=
        (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ).comp_memLp' hm2
      simpa using hL.integrable_sq
    rw [integral_finsetSum _ hint_i]
    simp only [hcoord, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp

/-- **Lower bound for one law from two moments** (Tier C, lemma C1): if the Euclidean coordinate has
under `ν` the mean `e^{-ρt} p x₀` and second moment `e^{-2ρt}‖p x₀‖² + (k/ρ)(1-e^{-2ρt})`, then
`ρ e^{-2ρt}‖p x₀‖² + k (1-√(1-e^{-2ρt}))² ≤ ρ W₂²(ν, μ)`. -/
theorem lower_of_moments (hρ : 0 < ρ) {t : ℝ} (ht : 0 ≤ t) (x₀ : M)
    (ν : Measure M) [IsProbabilityMeasure ν]
    (h1 : ∀ a : EuclideanSpace ℝ (Fin k),
      ∫ y, ⟪a, D.proj y⟫ ∂ν = Real.exp (-ρ * t) * ⟪a, D.proj x₀⟫)
    (h2i : Integrable (fun y => ‖D.proj y‖ ^ 2) ν)
    (h2 : ∫ y, ‖D.proj y‖ ^ 2 ∂ν =
      Real.exp (-2 * ρ * t) * ‖D.proj x₀‖ ^ 2 + k / ρ * (1 - Real.exp (-2 * ρ * t))) :
    ENNReal.ofReal (ρ * (Real.exp (-2 * ρ * t) * ‖D.proj x₀‖ ^ 2) +
        k * (1 - Real.sqrt (1 - Real.exp (-2 * ρ * t))) ^ 2) ≤
      ENNReal.ofReal ρ * TauCeti.transportCost (fun z => edist z.1 z.2 ^ 2) ν μ := by
  obtain ⟨hμ1, hμ2i, hμ2⟩ := D.proj_moments hρ
  have hne0 : ENNReal.ofReal ρ ≠ 0 := by simpa using hρ
  rw [← TauCeti.transportCost_const_mul hne0 ENNReal.ofReal_ne_top]
  refine TauCeti.le_transportCost fun π hπ => ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hpm := D.measurable_proj
  let : IsProbabilityMeasure π := hπ.isProbabilityMeasure
  set q := Real.exp (-2 * ρ * t) with hq
  have hq1 : q ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  set s := Real.sqrt (1 - q) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 1 - q := Real.sq_sqrt (by linarith)
  have hkρ : 0 ≤ (k : ℝ) / ρ := by positivity
  set X : M × M → EuclideanSpace ℝ (Fin k) := fun z => D.proj z.1 with hX
  set Z : M × M → EuclideanSpace ℝ (Fin k) := fun z => D.proj z.2 with hZ
  have hXm : Measurable X := hpm.comp measurable_fst
  have hZm : Measurable Z := hpm.comp measurable_snd
  have e1 : ∀ (g : EuclideanSpace ℝ (Fin k) → ℝ), Measurable g →
      ∫ z, g (X z) ∂π = ∫ y, g (D.proj y) ∂ν := fun g hg => by
    exact hπ.integral_comp_fst (hg.comp hpm).aestronglyMeasurable
  have e2 : ∀ (g : EuclideanSpace ℝ (Fin k) → ℝ), Measurable g →
      ∫ z, g (Z z) ∂π = ∫ y, g (D.proj y) ∂μ := fun g hg => by
    exact hπ.integral_comp_snd (hg.comp hpm).aestronglyMeasurable
  have hX2 : Integrable (fun z => ‖X z‖ ^ 2) π := hπ.integrable_comp_fst h2i
  have hZ2 : Integrable (fun z => ‖Z z‖ ^ 2) π := hπ.integrable_comp_snd hμ2i
  have hsq : Measurable (fun x : EuclideanSpace ℝ (Fin k) => ‖x‖ ^ 2) := by fun_prop
  have hE : Real.exp (-ρ * t) ^ 2 = q := by
    rw [hq, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have key := integral_norm_sub_sq_lower_bound π X Z hXm hZm
    (Real.exp (-ρ * t) • D.proj x₀) (k / ρ * (1 - q)) (k / ρ)
    (fun a => by
      rw [e1 (fun x => ⟪a, x⟫) (by fun_prop), h1 a, inner_smul_right])
    hX2
    (by rw [e1 _ hsq, h2, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hE])
    (fun a => by rw [e2 (fun x => ⟪a, x⟫) (by fun_prop), hμ1 a])
    hZ2
    (by rw [e2 _ hsq, hμ2])
  -- algebra
  have hCB : Real.sqrt (k / ρ * (1 - q) * (k / ρ)) = k / ρ * s := by
    rw [show k / ρ * (1 - q) * (k / ρ) = (k / ρ * s) ^ 2 by rw [mul_pow, hs2]; ring]
    exact Real.sqrt_sq (mul_nonneg hkρ hs0)
  rw [hCB, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hE] at key
  have hXL2 := (memLp_two_iff_integrable_sq_norm hXm.aestronglyMeasurable).2 hX2
  have hZL2 := (memLp_two_iff_integrable_sq_norm hZm.aestronglyMeasurable).2 hZ2
  have hdiff := hXL2.sub hZL2
  have hint : Integrable (fun z => ‖X z - Z z‖ ^ 2) π :=
    (memLp_two_iff_integrable_sq_norm hdiff.aestronglyMeasurable).1 hdiff
  have hle : ∫⁻ z, ENNReal.ofReal (‖X z - Z z‖ ^ 2) ∂π ≤ ∫⁻ z, edist z.1 z.2 ^ 2 ∂π := by
    refine lintegral_mono fun z => ?_
    have h := D.edist_proj_le z.1 z.2
    calc ENNReal.ofReal (‖X z - Z z‖ ^ 2) = edist (D.proj z.1) (D.proj z.2) ^ 2 := by
          rw [edist_dist, dist_eq_norm, ENNReal.ofReal_pow (norm_nonneg _)]
      _ ≤ edist z.1 z.2 ^ 2 := pow_le_pow_left' h 2
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun z => sq_nonneg _)] at hle
  calc ENNReal.ofReal (ρ * (q * ‖D.proj x₀‖ ^ 2) + k * (1 - s) ^ 2)
      ≤ ENNReal.ofReal (ρ * ∫ z, ‖X z - Z z‖ ^ 2 ∂π) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hρ' : ρ * (k / ρ) = k := by field_simp
        have : k * (1 - s) ^ 2 = ρ * (k / ρ * (1 - s) ^ 2) := by field_simp
        rw [this, ← mul_add]
        refine mul_le_mul_of_nonneg_left ?_ hρ.le
        nlinarith [key, hs2]
    _ = ENNReal.ofReal ρ * ENNReal.ofReal (∫ z, ‖X z - Z z‖ ^ 2 ∂π) :=
        ENNReal.ofReal_mul hρ.le
    _ ≤ ENNReal.ofReal ρ * ∫⁻ z, edist z.1 z.2 ^ 2 ∂π := by gcongr

end SplitData

end Split

end CutoffRigidity.Riemann
