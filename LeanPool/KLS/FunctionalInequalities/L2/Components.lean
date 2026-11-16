/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.L2.MeanVariance
public import LeanPool.KLS.FunctionalInequalities.L2.Pairing

/-!
# Components of vector-valued `L²` functions

For a real inner product space `G`, the scalar components of `g ∈ L²(μ; G)` along
`c ∈ G` are `(innerSL ℝ c).compLp g ∈ L²(μ)`. On a probability space the component means are the
components of the Bochner mean, and for an orthonormal basis the squared `L²` norms of the
components add up to `‖g‖²` (Parseval). These are the facts used to lift scalar results on `L²`
componentwise to tensor-valued data (Bizeul–Klartag–Lehec, Lemma 2.1, tensor version).

`sq_sum_eLpNorm_le_dim_mul_integral_sum_sq` compares the sum of coordinate `L²` norms with the
Euclidean energy
`∫ Σᵢ (a i)²`, with the exact factor `n`, for any measure.
`memLp_sqrt_sum_sq` and `gradient_density_l1_of_coordinate_l2` pass coordinate `L^p` membership and
coordinate `L²`
convergence to the Euclidean density `√(Σᵢ (a i)²)` (`L¹` convergence on finite measures).
-/

@[expose] public section

noncomputable section

open scoped InnerProductSpace RealInnerProductSpace
open MeasureTheory

namespace FunctionalInequalities.L2

variable {α : Type*} [MeasurableSpace α]
  {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]

/-- The mean of the component `⟪c, g⟫` of `g ∈ L²(μ; G)` is `⟪c, ∫ g⟫`. -/
theorem mean_compLp_innerSL [CompleteSpace G] (μ : ProbabilityMeasure α) (c : G)
    (g : Lp G 2 (μ : Measure α)) :
    mean μ ((innerSL ℝ c).compLp g) = ⟪c, ∫ x, g x ∂(μ : Measure α)⟫ := by
  rw [mean_eq_integral]
  calc
    ∫ x, ((innerSL ℝ c).compLp g) x ∂(μ : Measure α) =
        ∫ x, ⟪c, g x⟫_ℝ ∂(μ : Measure α) := by
      apply integral_congr_ae
      filter_upwards [ContinuousLinearMap.coeFn_compLp (innerSL ℝ c) g] with x hx
      simpa [innerSL] using hx
    _ = ⟪c, ∫ x, g x ∂(μ : Measure α)⟫_ℝ := by
      exact integral_inner ((Lp.memLp g).integrable (by norm_num)) c

section InnerProduct

variable {F : Type*}
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

private theorem integrable_norm_sq
    {μ : Measure α} (f : Lp F 2 μ) : Integrable (fun x => ‖f x‖ ^ 2) μ := by
  simpa only [real_inner_self_eq_norm_sq] using MeasureTheory.L2.integrable_inner (𝕜 := ℝ) f f

end InnerProduct

/-- Parseval in `L²(μ; G)`: the squared norms of the components in an orthonormal basis add up
to the squared norm. -/
theorem sum_norm_sq_compLp_innerSL {μ : Measure α} {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ G) (g : Lp G 2 μ) :
    ∑ k, ‖(innerSL ℝ (b k)).compLp g‖ ^ 2 = ‖g‖ ^ 2 := by
  rw [norm_sq_eq_integral_norm_sq g]
  rw [Finset.sum_congr rfl (fun k _ => norm_sq_eq_integral_norm_sq ((innerSL ℝ (b k)).compLp g))]
  rw [← integral_finsetSum _ (fun k _ => integrable_norm_sq _)]
  apply integral_congr_ae
  have hae : ∀ᵐ x ∂μ, ∀ k, ((innerSL ℝ (b k)).compLp g) x = ⟪b k, g x⟫ := by
    rw [ae_all_iff]
    intro k
    filter_upwards [ContinuousLinearMap.coeFn_compLp (innerSL ℝ (b k)) g] with x hx
    rw [hx, innerSL_apply_apply]
  filter_upwards [hae] with x hx
  simp only [hx]
  simpa only [Real.norm_eq_abs, sq_abs] using b.sum_sq_norm_inner_right (g x)

/--
**Finite-coordinate energy.** For any measure and `n` coordinates in `L²` (every `n`, zero
included),
`(Σᵢ ‖a i‖₂)² ≤ n · ∫ Σᵢ (a i)²`: finite Cauchy–Schwarz together with `‖a i‖₂² = ∫ (a i)²`
(`integral_norm_sq_eq_eLpNorm_sq`). The integrability of `Σᵢ (a i)²` is derived, not assumed. -/
theorem sq_sum_eLpNorm_le_dim_mul_integral_sum_sq {X : Type*} [MeasurableSpace X] {n : ℕ}
    (μ : Measure X) {a : Fin n → X → ℝ} (ha : ∀ i : Fin n, MemLp (a i) 2 μ) :
    (∑ i : Fin n, eLpNorm (a i) 2 μ) ^ 2 ≤
      (n : ENNReal) * ENNReal.ofReal (∫ x, ∑ i : Fin n, (a i x) ^ 2 ∂μ) := by
  classical
  have hfin (i : Fin n) : eLpNorm (a i) 2 μ ≠ ⊤ := (ha i).eLpNorm_lt_top.ne
  have hnormsq (i : Fin n) :
    eLpNorm (a i) 2 μ ^ (2 : ℕ) = ENNReal.ofReal (∫ x, (a i x) ^ 2 ∂μ) := by
    have h := integral_norm_sq_eq_eLpNorm_sq (ha i)
    simp only [Real.norm_eq_abs, sq_abs] at h
    rw [h, ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hfin i)]
  have hCS :=
    Finset.sum_mul_sq_le_sq_mul_sq (R := NNReal) Finset.univ (fun _ : Fin n => 1)
      (fun i : Fin n => (eLpNorm (a i) 2 μ).toNNReal)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at hCS
  have hCSE :
    ((∑ i : Fin n, (eLpNorm (a i) 2 μ).toNNReal : NNReal) : ENNReal) ^ 2 ≤
      (n : ENNReal) * ((∑ i : Fin n, (eLpNorm (a i) 2 μ).toNNReal ^ 2 : NNReal) : ENNReal) := by
    exact_mod_cast hCS
  simp only [ENNReal.ofNNReal_finsetSum, ENNReal.coe_pow, ENNReal.coe_toNNReal (hfin _)] at hCSE
  calc
    _ ≤ (n : ENNReal) * ∑ i : Fin n, eLpNorm (a i) 2 μ ^ (2 : ℕ) := hCSE
    _ = _ := by
      rw [integral_finsetSum Finset.univ (fun i _ => (ha i).integrable_sq),
        ENNReal.ofReal_sum_of_nonneg (fun i _ => integral_nonneg fun _ => sq_nonneg _)]
      simp only [hnormsq]

section EuclideanDensity

open Filter
open scoped ENNReal Topology

/-- The Euclidean norm is at most the sum of the absolute coordinates. -/
private theorem euclidean_norm_le_sum_abs {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) :
    ‖v‖ ≤ ∑ i : Fin n, |v i| := by
  have he := (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v
  calc
    _ =
        ‖∑ i : Fin n,
            (EuclideanSpace.basisFun (Fin n) ℝ).repr v i •
              EuclideanSpace.basisFun (Fin n) ℝ i‖ :=
      (congrArg norm he).symm
    _ ≤
        ∑ i : Fin n,
          ‖(EuclideanSpace.basisFun (Fin n) ℝ).repr v i •
              EuclideanSpace.basisFun (Fin n) ℝ i‖ :=
      norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_smul, EuclideanSpace.basisFun_repr, Real.norm_eq_abs,
        (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.1 i, mul_one]

/-- Coordinate errors control the error of the Euclidean density. -/
private theorem abs_sqrt_sum_sq_sub_le_sum_abs {n : ℕ} (a b : Fin n → ℝ) :
    |Real.sqrt (∑ i, (a i) ^ 2) - Real.sqrt (∑ i, (b i) ^ 2)| ≤ ∑ i, |a i - b i| := by
  let A : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 a
  let B : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 b
  have h := (abs_norm_sub_norm_le A B).trans (euclidean_norm_le_sum_abs (A - B))
  simpa only [EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs, WithLp.ofLp_sub,
    WithLp.ofLp_toLp, Pi.sub_apply] using h

section MeasurableSpace

variable {X : Type*}
  [MeasurableSpace X]

/-- **Euclidean density in `L^p`.** If every coordinate is in `L^p`, so is `√(Σ aᵢ²)`. -/
theorem memLp_sqrt_sum_sq {μ : Measure X} {n : ℕ} {a : Fin n → X → ℝ} {p : ℝ≥0∞}
    (ha : ∀ i, MemLp (a i) p μ) : MemLp (fun x => Real.sqrt (∑ i : Fin n, (a i x) ^ 2)) p μ := by
  have hsum : MemLp (fun x => ∑ i : Fin n, |a i x|) p μ := by
    simpa only [Real.norm_eq_abs] using memLp_finsetSum Finset.univ (fun i _ => (ha i).norm)
  have hm : AEStronglyMeasurable (fun x => Real.sqrt (∑ i : Fin n, (a i x) ^ 2)) μ := by
    apply Real.continuous_sqrt.comp_aestronglyMeasurable
    exact
      Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
        ((ha i).aestronglyMeasurable.aemeasurable.pow_const (2 : ℕ)).aestronglyMeasurable
  apply hsum.mono' hm
  apply ae_of_all
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have H :=
    euclidean_norm_le_sum_abs
      (WithLp.toLp 2 (fun i : Fin n => a i x) : EuclideanSpace ℝ (Fin n))
  simpa only [EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs, WithLp.ofLp_toLp] using H

/--
**Coordinate `L²` to density `L¹`.** On a finite measure, coordinate `L²` convergence `g m i → a i`
gives `L¹`
convergence of `√(Σ (g m i)²) − √(Σ (a i)²)` to zero; every `n`, zero included. -/
theorem gradient_density_l1_of_coordinate_l2 {μ : Measure X} [IsFiniteMeasure μ] {n : ℕ}
    {g : ℕ → Fin n → X → ℝ} {a : Fin n → X → ℝ} (hg : ∀ m i, MemLp (g m i) 2 μ)
    (ha : ∀ i, MemLp (a i) 2 μ)
    (hconv : ∀ i, Tendsto (fun m => eLpNorm (fun x => g m i x - a i x) 2 μ) atTop (𝓝 0)) :
    (∀ m,
        MemLp
          (fun x =>
            Real.sqrt (∑ i : Fin n, (g m i x) ^ 2) - Real.sqrt (∑ i : Fin n, (a i x) ^ 2))
          1 μ) ∧
      Tendsto
        (fun m =>
          eLpNorm
            (fun x =>
              Real.sqrt (∑ i : Fin n, (g m i x) ^ 2) - Real.sqrt (∑ i : Fin n, (a i x) ^ 2))
            1 μ)
        atTop (𝓝 0) := by
  classical
  let e := fun m i x => g m i x - a i x
  let d := fun m x =>
    Real.sqrt (∑ i : Fin n, (g m i x) ^ 2) - Real.sqrt (∑ i : Fin n, (a i x) ^ 2)
  have he2 (m : ℕ) (i : Fin n) : MemLp (e m i) 2 μ := (hg m i).sub (ha i)
  have he1 (m : ℕ) (i : Fin n) : MemLp (e m i) 1 μ := (he2 m i).mono_exponent (by norm_num)
  have hd (m : ℕ) : AEStronglyMeasurable (d m) μ :=
    (memLp_sqrt_sum_sq (hg m)).aestronglyMeasurable.sub
      (memLp_sqrt_sum_sq ha).aestronglyMeasurable
  have hbound (m : ℕ) (x : X) : ‖d m x‖ ≤ ∑ i : Fin n, |e m i x| := by
    exact abs_sqrt_sum_sq_sub_le_sum_abs (fun i => g m i x) (fun i => a i x)
  have hsum1 (m : ℕ) : MemLp (fun x => ∑ i : Fin n, |e m i x|) 1 μ := by
    simpa only [Real.norm_eq_abs] using memLp_finsetSum Finset.univ (fun i _ => (he1 m i).norm)
  have hd1 (m : ℕ) : MemLp (d m) 1 μ := (hsum1 m).mono' (hd m) (ae_of_all _ (hbound m))
  have hnormbound (m : ℕ) : eLpNorm (d m) 1 μ ≤ ∑ i : Fin n, eLpNorm (e m i) 1 μ := by
    calc
      _ ≤ eLpNorm (fun x => ∑ i : Fin n, |e m i x|) 1 μ :=
        eLpNorm_mono_ae_real (hd m) (ae_of_all _ (hbound m))
      _ = eLpNorm (∑ i : Fin n, fun x => |e m i x|) 1 μ := by
        congr 1
        funext x
        simp only [Finset.sum_apply]
      _ ≤ ∑ i : Fin n, eLpNorm (fun x => |e m i x|) 1 μ :=
        eLpNorm_sum_le le_rfl
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        simpa only [Real.norm_eq_abs] using eLpNorm_norm (e m i) (he1 m i).aestronglyMeasurable (p := 1) (μ := μ)
  let B : ℝ≥0∞ := μ Set.univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal)
  have hB : B ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top μ Set.univ)
  have hconv1 (i : Fin n) : Tendsto (fun m => eLpNorm (e m i) 1 μ) atTop (𝓝 0) := by
    have H : Tendsto (fun m => eLpNorm (e m i) 2 μ * B) atTop (𝓝 0) := by
      simpa only [zero_mul] using ENNReal.Tendsto.mul_const (hconv i) (Or.inr hB)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds H (fun _ => zero_le)
    intro m
    exact eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num) (he2 m i).aestronglyMeasurable
  have htotal : Tendsto (fun m => ∑ i : Fin n, eLpNorm (e m i) 1 μ) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun i _ => hconv1 i)
  exact
    ⟨hd1,
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htotal (fun _ => zero_le)
        hnormbound⟩

end MeasurableSpace

end EuclideanDensity

end FunctionalInequalities.L2
