/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Rd.Sobolev.SobolevTwoLittlewoodPaley
public import LeanPool.FunctionSpaces.Analysis.Lp.IndicatorOperator
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Topology.MetricSpace.UniformConvergence

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Rellich compactness of `H^1(V)` in `L_2` of a bounded set

Let `V` be a finite-dimensional real inner product space, such as `ℝ^d`, with Lebesgue measure,
and `Ω ⊆ V` bounded. **Rellich's theorem**: the map `F ↦ F|_Ω` from Mathlib's Sobolev space
`H^1(V) = H^{1,2}(V, ℂ)` to `L_2(Ω)` is a compact operator (`Rd.isCompactOperator_restr_toL2`).
Every bounded sequence in `H^1(V)` has a subsequence whose restrictions to `Ω` converge in
`L_2(Ω)` (`Rd.exists_subseq_tendsto_restr`), and so has every sequence `f_n ∈ L_2(V)` with weak
gradients and `‖f_n‖_2² + ∑_i ‖∂_{e_i} f_n‖_2² ≤ M²`
(`Rd.exists_subseq_tendsto_restr_of_hasWeakLineDeriv`).

* **The inverse Fourier transform on `L_1 ∩ L_2`**: for every integrable `h ∈ L_2(V)` the `L_2`
  inverse Fourier transform is the pointwise inverse Fourier integral
  (`Rd.fourierInv_Lp_ae_eq_of_integrable`).
* **`H^1(V)` in `L_2(V)`**: an element `F` of `H^{1,2}(V, ℂ)` is the `L_2` function
  `𝓕⁻(⟨ξ⟩⁻¹ 𝓕(J_1 F))` (`Rd.toL2`, `Rd.toTemperedDistribution_toL2`), which determines `F`
  (`Rd.toL2_injective`), and `‖F‖_2 ≤ ‖F‖_{H^1}` (`Rd.norm_toL2_le`).
* **Fourier truncation**: cutting `𝓕F` off to the ball `|ξ| ≤ K` changes `F` by at most
  `K⁻¹ ‖F‖_{H^1}` in `L_2(V)`, since `⟨ξ⟩⁻¹ ≤ K⁻¹` outside the ball
  (`Rd.norm_toL2_sub_truncL2_le`), so the truncations converge in operator norm
  (`Rd.tendsto_truncL2`).
* **Band-limited functions**: for `h ∈ L_2(V)` the cut-off `1_{B_K} h` to the ball
  `B_K = {|ξ| ≤ K}` is integrable (`Rd.integrable_indicator_closedBall`), and its inverse Fourier
  integral is bounded by `|B_K|^{1/2} ‖h‖_2` and Lipschitz with constant
  `2π max(K, 0) |B_K|^{1/2} ‖h‖_2` on `V` (`Rd.norm_fourierInv_indicator_le`,
  `Rd.lipschitzWith_fourierInv_indicator`).
* **Compactness of the truncations**: by the Arzelà–Ascoli theorem on the compact closure of `Ω`
  (`Rd.totallyBounded_setOf_lipschitzWith`), the truncated operators restricted to `Ω` are
  compact (`Rd.isCompactOperator_restr_truncL2`), and a limit of compact operators is compact
  (Mathlib's `isCompactOperator_of_tendsto`).
-/

@[expose] public section

open MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal SchwartzMap FourierTransform Real BesselPotentialSpace
  BoundedContinuousFunction
open TemperedDistribution (besselPotential)

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### The inverse Fourier transform on `L_1 ∩ L_2` -/

/-- **The `L_2` inverse Fourier transform of an `L_1 ∩ L_2` function is the inverse Fourier
integral**: for `h ∈ L_2(V)` integrable, Plancherel's `𝓕⁻h` agrees almost everywhere with
`x ↦ ∫ e^(2πi⟪ξ, x⟫) h(ξ) dξ`. Both are locally integrable (the second is continuous) and have
the same integrals against smooth compactly supported functions `u`:
`∫ u · 𝓕⁻h = (𝓕⁻h)(u) = h(𝓕⁻u) = ∫ 𝓕⁻u · h`, by Mathlib's
`Lp.fourierInv_toTemperedDistribution_eq` and `Rd.integral_fourierInv_smul_eq_of_integrable`. -/
theorem fourierInv_Lp_ae_eq_of_integrable (h : Lp ℂ 2 (volume : Measure V))
    (hh : Integrable (h : V → ℂ)) :
    ((𝓕⁻ h : Lp ℂ 2 (volume : Measure V)) : V → ℂ) =ᵐ[volume] 𝓕⁻ (h : V → ℂ) := by
  refine ae_eq_of_integral_contDiff_smul_eq ((Lp.memLp _).locallyIntegrable (by norm_num))
    (continuous_fourierInv_of_integrable hh).locallyIntegrable fun φ hφ hφc => ?_
  have hφ₁ : HasCompactSupport (Complex.ofRealCLM ∘ φ) := hφc.comp_left rfl
  have hφ₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Complex.ofRealCLM ∘ φ) := by fun_prop
  have key : ((𝓕⁻ h : Lp ℂ 2 (volume : Measure V)) : 𝓢'(V, ℂ)) (hφ₁.toSchwartzMap hφ₂) =
      ∫ x, hφ₁.toSchwartzMap hφ₂ x • 𝓕⁻ (h : V → ℂ) x := by
    rw [← Lp.fourierInv_toTemperedDistribution_eq, TemperedDistribution.fourierInv_apply,
      Lp.toTemperedDistribution_apply, integral_fourierInv_smul_eq_of_integrable _ hh]
  rw [Lp.toTemperedDistribution_apply] at key
  convert key using 2 with x x <;> simp [Complex.real_smul]

/-! ### `H^1(V)` as a space of `L_2` functions -/

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- `⟨ξ⟩^{-1} = (⟨ξ⟩^1)⁻¹`: the Bessel weight of order `-1` is the reciprocal of the one of
order `1`. -/
theorem besselWeight_neg_one_eq_inv (ξ : V) : besselWeight (-1) ξ = (besselWeight 1 ξ)⁻¹ := by
  rw [besselWeight, besselWeight, neg_div, Real.rpow_neg (by positivity)]

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- `⟨ξ⟩⁻¹ ≤ 1`. -/
theorem besselWeight_neg_one_le_one (ξ : V) : besselWeight (-1) ξ ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (le_add_of_nonneg_right (sq_nonneg _)) (by norm_num)

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- `⟨ξ⟩⁻¹ ≤ K⁻¹` for `|ξ| ≥ K > 0`, since `|ξ| ≤ ⟨ξ⟩`. -/
theorem besselWeight_neg_one_le_inv {K : ℝ} (hK : 0 < K) {ξ : V} (hξ : K ≤ ‖ξ‖) :
    besselWeight (-1) ξ ≤ K⁻¹ := by
  rw [besselWeight_neg_one_eq_inv]
  exact inv_anti₀ hK (hξ.trans (norm_le_besselWeight_one ξ))

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- `|⟨ξ⟩⁻¹| ≤ 1` for the Bessel weight of order `-1` as a complex number. -/
theorem norm_besselWeight_neg_one_le_one (ξ : V) : ‖(besselWeight (-1) ξ : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_of_nonneg (besselWeight_nonneg _ _)]
  exact besselWeight_neg_one_le_one ξ

/-- The Bessel weight `⟨ξ⟩⁻¹` of order `-1` is a bounded function, an element of `L_∞(V)`. -/
theorem memLp_top_besselWeight_neg_one :
    MemLp (fun ξ : V => (besselWeight (-1) ξ : ℂ)) ∞ volume :=
  memLp_top_of_bound (hasTemperateGrowth_besselWeight (-1)).1.continuous.aestronglyMeasurable 1
    (ae_of_all _ norm_besselWeight_neg_one_le_one)

/-- **Multiplication by `⟨ξ⟩⁻¹` on `L_2(V)`**, as a bounded operator (Mathlib's Hölder
multiplication `L_∞ × L_2 → L_2`); its norm is at most `1` (`Rd.norm_besselInvMul_le_one`). -/
noncomputable def besselInvMul : Lp ℂ 2 (volume : Measure V) →L[ℂ] Lp ℂ 2 (volume : Measure V) :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL volume ∞ 2 2 (memLp_top_besselWeight_neg_one.toLp _)

/-- Multiplication by `⟨ξ⟩⁻¹` is pointwise multiplication, almost everywhere. -/
theorem besselInvMul_apply_ae (g : Lp ℂ 2 (volume : Measure V)) :
    (besselInvMul g : V → ℂ) =ᵐ[volume] fun ξ => (besselWeight (-1) ξ : ℂ) * g ξ := by
  filter_upwards [ContinuousLinearMap.coeFn_holder (r := 2) (ContinuousLinearMap.mul ℂ ℂ)
    (memLp_top_besselWeight_neg_one.toLp _) g, memLp_top_besselWeight_neg_one.coeFn_toLp]
    with x h1 h2
  rw [besselInvMul, ContinuousLinearMap.holderL_apply_apply, h1, ContinuousLinearMap.mul_apply',
    h2]

/-- Multiplication by `⟨ξ⟩⁻¹` has operator norm at most `1` on `L_2(V)`, since `|⟨ξ⟩⁻¹| ≤ 1`
(Mathlib's `Lp.norm_le_norm_of_ae_le`). -/
theorem norm_besselInvMul_le_one :
    ‖(besselInvMul : Lp ℂ 2 (volume : Measure V) →L[ℂ] Lp ℂ 2 (volume : Measure V))‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun g => by
    rw [one_mul]
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [besselInvMul_apply_ae g] with ξ hξ
    rw [hξ, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_besselWeight_neg_one_le_one ξ)

/-- **An element of `H^1(V)` as an `L_2` function**: for `F ∈ H^{1,2}(V, ℂ)`, given by the
tempered distribution `u = F.toDistr` and the `L_2` function `J_1 u = F.toLp`, the `L_2`
function `𝓕⁻(⟨ξ⟩⁻¹ 𝓕(J_1 u))`, which is `u` (`Rd.toTemperedDistribution_toL2`). -/
noncomputable def toL2 : H^{1, 2}(V, ℂ) →L[ℂ] Lp ℂ 2 (volume : Measure V) :=
  FourierTransform.fourierInvCLM ℂ (Lp ℂ 2 (volume : Measure V)) ∘L besselInvMul ∘L
    FourierTransform.fourierCLM ℂ (Lp ℂ 2 (volume : Measure V)) ∘L
    (BesselPotentialSpace.toLpₗᵢ V ℂ 1 2).toLinearIsometry.toContinuousLinearMap

/-- `toL2 F = 𝓕⁻(⟨ξ⟩⁻¹ 𝓕(J_1 F))`. -/
theorem toL2_apply (F : H^{1, 2}(V, ℂ)) : toL2 F = 𝓕⁻ (besselInvMul (𝓕 F.toLp)) := by
  simp only [toL2, ContinuousLinearMap.coe_comp, Function.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    BesselPotentialSpace.toLpₗᵢ_apply, FourierTransform.fourierCLM_apply,
    FourierTransform.fourierInvCLM_apply]

/-- The Fourier transform of `toL2 F` is `⟨ξ⟩⁻¹ 𝓕(J_1 F)`. -/
theorem fourier_toL2 (F : H^{1, 2}(V, ℂ)) : 𝓕 (toL2 F) = besselInvMul (𝓕 F.toLp) := by
  rw [toL2_apply, FourierTransform.fourier_fourierInv_eq]

/-- The Fourier transform of `toL2 F` is `⟨ξ⟩⁻¹ 𝓕(J_1 F)` almost everywhere. -/
theorem fourier_toL2_ae_eq (F : H^{1, 2}(V, ℂ)) :
    ((𝓕 (toL2 F) : Lp ℂ 2 (volume : Measure V)) : V → ℂ) =ᵐ[volume]
      fun ξ => (besselWeight (-1) ξ : ℂ) * (𝓕 F.toLp : Lp ℂ 2 (volume : Measure V)) ξ := by
  rw [fourier_toL2]
  exact besselInvMul_apply_ae _

/-- **`toL2 F` represents `F`**: the tempered distribution of the `L_2` function `toL2 F` is the
distribution `F.toDistr`. Indeed `F.toDistr = J_{-1}(J_1 F)` (Mathlib's
`BesselPotentialSpace.besselPotential_neg_toLp_eq`), and the Fourier transform of `J_{-1} g` is
`⟨ξ⟩⁻¹ 𝓕g`, which for `g ∈ L_2` is the distribution of the `L_2` function `⟨ξ⟩⁻¹ 𝓕g`
(`Rd.smulLeftCLM_toTemperedDistribution_eq`). -/
theorem toTemperedDistribution_toL2 (F : H^{1, 2}(V, ℂ)) :
    ((toL2 F : Lp ℂ 2 (volume : Measure V)) : 𝓢'(V, ℂ)) = F.toDistr := by
  have hm : MemLp (fun ξ => (besselWeight (-1) ξ : ℂ) *
      (𝓕 F.toLp : Lp ℂ 2 (volume : Measure V)) ξ) 2 volume :=
    (Lp.memLp (besselInvMul (𝓕 F.toLp))).ae_eq (besselInvMul_apply_ae _)
  have h1 : besselInvMul (𝓕 F.toLp) = hm.toLp _ :=
    Lp.ext ((besselInvMul_apply_ae _).trans hm.coeFn_toLp.symm)
  conv_rhs => rw [← BesselPotentialSpace.besselPotential_neg_toLp_eq (f := F),
    ← FourierTransform.fourierInv_fourier_eq (F := 𝓢'(V, ℂ)) (besselPotential V ℂ (-1) _),
    TemperedDistribution.fourier_besselPotential_eq_smulLeftCLM_fourier_apply,
    Lp.fourier_toTemperedDistribution_eq]
  rw [toL2_apply, ← Lp.fourierInv_toTemperedDistribution_eq, h1,
    ← smulLeftCLM_toTemperedDistribution_eq (hasTemperateGrowth_besselWeight (-1))]
  rfl

/-- An `L_2` function `f` is `toL2 F` as soon as its tempered distribution is `F.toDistr`:
`L_2` functions are determined by their distributions (`Rd.eq_of_toTemperedDistribution_eq`).
-/
theorem toL2_eq_of_toDistr_eq (F : H^{1, 2}(V, ℂ)) {f : Lp ℂ 2 (volume : Measure V)}
    (hf : (f : 𝓢'(V, ℂ)) = F.toDistr) : toL2 F = f :=
  eq_of_toTemperedDistribution_eq ((toTemperedDistribution_toL2 F).trans hf.symm)

/-- **`H^1(V)` is determined by its `L_2` functions**: `F ↦ toL2 F` is injective, since the
tempered distribution of `toL2 F` is `F.toDistr` (`Rd.toTemperedDistribution_toL2`) and an element
of `H^1(V)` is determined by its distribution (Mathlib's `BesselPotentialSpace.ext`). -/
theorem toL2_injective : Function.Injective (toL2 (V := V)) :=
  fun U W h => BesselPotentialSpace.ext (by
    rw [← toTemperedDistribution_toL2, h, toTemperedDistribution_toL2])

/-- **`‖F‖_2 ≤ ‖F‖_{H^1}`**: by Plancherel, `‖toL2 F‖_2 = ‖⟨ξ⟩⁻¹ 𝓕(J_1 F)‖_2 ≤ ‖𝓕(J_1 F)‖_2`
(`Rd.norm_besselInvMul_le_one`), and `‖𝓕(J_1 F)‖_2 = ‖F‖_{H^1}` (Mathlib's
`BesselPotentialSpace.norm_fourier_toLp_eq`). -/
theorem norm_toL2_le (F : H^{1, 2}(V, ℂ)) : ‖toL2 F‖ ≤ ‖F‖ := by
  rw [← Lp.norm_fourier_eq (toL2 F), fourier_toL2, ← BesselPotentialSpace.norm_fourier_toLp_eq]
  exact (besselInvMul.le_of_opNorm_le norm_besselInvMul_le_one _).trans_eq (one_mul _)

/-! ### Truncation in frequency -/

/-- **The frequency truncation**: `truncL2 K F = 𝓕⁻(1_{B_K} 𝓕(toL2 F))`, the part of `F` with
frequencies in the closed ball `B_K = {|ξ| ≤ K}`, where `1_{B_K}` acts by the project's
`Rd.indicatorLp`. -/
noncomputable def truncL2 (K : ℝ) : H^{1, 2}(V, ℂ) →L[ℂ] Lp ℂ 2 (volume : Measure V) :=
  FourierTransform.fourierInvCLM ℂ (Lp ℂ 2 (volume : Measure V)) ∘L
    indicatorLp (measurableSet_closedBall (x := (0 : V)) (ε := K)) ∘L
    FourierTransform.fourierCLM ℂ (Lp ℂ 2 (volume : Measure V)) ∘L toL2

/-- `truncL2 K F = 𝓕⁻(1_{B_K} 𝓕(toL2 F))`. -/
theorem truncL2_apply (K : ℝ) (F : H^{1, 2}(V, ℂ)) :
    truncL2 K F = 𝓕⁻ (indicatorLp (measurableSet_closedBall (x := (0 : V)) (ε := K))
      (𝓕 (toL2 F))) := rfl

/-- **The truncation error**: for `K > 0` and `F ∈ H^1(V)`,
`‖toL2 F - truncL2 K F‖_2 ≤ K⁻¹ ‖F‖_{H^1}`. By Plancherel the left side is the `L_2` norm of
`1_{|ξ| > K} ⟨ξ⟩⁻¹ 𝓕(J_1 F)`, and `⟨ξ⟩⁻¹ ≤ K⁻¹` for `|ξ| > K`. -/
theorem norm_toL2_sub_truncL2_apply_le {K : ℝ} (hK : 0 < K) (F : H^{1, 2}(V, ℂ)) :
    ‖toL2 F - truncL2 K F‖ ≤ K⁻¹ * ‖F‖ := by
  have hB := measurableSet_closedBall (x := (0 : V)) (ε := K)
  have hsub : 𝓕 (toL2 F - truncL2 K F) = 𝓕 (toL2 F) - 𝓕 (truncL2 K F) :=
    map_sub (FourierTransform.fourierCLM ℂ (Lp ℂ 2 (volume : Measure V))) _ _
  rw [← Lp.norm_fourier_eq, hsub, truncL2_apply, FourierTransform.fourier_fourierInv_eq,
    ← BesselPotentialSpace.norm_fourier_toLp_eq]
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [Lp.coeFn_sub (𝓕 (toL2 F)) (indicatorLp hB (𝓕 (toL2 F))),
    indicatorLp_apply_ae hB (𝓕 (toL2 F)), fourier_toL2_ae_eq F] with ξ h1 h2 h3
  rw [h1, Pi.sub_apply, h2]
  by_cases hξ : ξ ∈ closedBall (0 : V) K
  · rw [Set.indicator_of_mem hξ, sub_self, norm_zero]
    positivity
  · rw [Set.indicator_of_notMem hξ, sub_zero, h3, norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [Complex.norm_real, Real.norm_of_nonneg (besselWeight_nonneg _ _)]
    rw [mem_closedBall, dist_zero_right, not_le] at hξ
    exact besselWeight_neg_one_le_inv hK hξ.le

/-- **The truncations approximate in operator norm**: `‖toL2 - truncL2 K‖ ≤ K⁻¹` for `K > 0`. -/
theorem norm_toL2_sub_truncL2_le {K : ℝ} (hK : 0 < K) :
    ‖(toL2 : H^{1, 2}(V, ℂ) →L[ℂ] Lp ℂ 2 (volume : Measure V)) - truncL2 K‖ ≤ K⁻¹ :=
  ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.2 hK.le) fun F =>
    norm_toL2_sub_truncL2_apply_le hK F

/-- **The truncations converge to `toL2`** in operator norm as `K → ∞`. -/
theorem tendsto_truncL2 :
    Tendsto (fun K : ℝ => (truncL2 K : H^{1, 2}(V, ℂ) →L[ℂ] Lp ℂ 2 (volume : Measure V))) atTop
      (𝓝 toL2) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun K => norm_nonneg _) ?_ tendsto_inv_atTop_zero
  filter_upwards [eventually_gt_atTop 0] with K hK
  rw [norm_sub_rev]
  exact norm_toL2_sub_truncL2_le hK

/-! ### Band-limited functions are bounded and Lipschitz -/

variable (V) in
/-- The constant `|B_K|^{1/2}`, the square root of the volume of the closed ball
`B_K = {|ξ| ≤ K}` in `V`: by Cauchy–Schwarz, `∫_{B_K} |h| ≤ |B_K|^{1/2} ‖h‖_2`. -/
noncomputable def ballVolumeSqrt (K : ℝ) : ℝ :=
  (volume (closedBall (0 : V) K)).toReal ^ (1 / 2 : ℝ)

/-- `|B_K|^{1/2} ≥ 0`. -/
theorem ballVolumeSqrt_nonneg (K : ℝ) : 0 ≤ ballVolumeSqrt V K :=
  Real.rpow_nonneg ENNReal.toReal_nonneg _

/-- **Cauchy–Schwarz on a ball**: for `h ∈ L_2(V)`, `∫_{B_K} |h| ≤ |B_K|^{1/2} ‖h‖_2`, in
`ℝ≥0∞` (Mathlib's `eLpNorm_le_eLpNorm_mul_rpow_measure_univ` on the ball). -/
theorem eLpNorm_one_indicator_closedBall_le (h : Lp ℂ 2 (volume : Measure V)) (K : ℝ) :
    eLpNorm ((closedBall (0 : V) K).indicator h) 1 volume ≤
      volume (closedBall (0 : V) K) ^ (1 / 2 : ℝ) * ‖h‖ₑ := by
  rw [eLpNorm_indicator_eq_eLpNorm_restrict
    (measurableSet_closedBall : MeasurableSet (closedBall (0 : V) K)).nullMeasurableSet]
  refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ (q := 2) (by norm_num)
    (Lp.aestronglyMeasurable h).restrict).trans ?_
  rw [Measure.restrict_apply_univ, mul_comm, Lp.eNorm_def]
  norm_num
  gcongr
  exact Measure.restrict_le_self

/-- A function `h ∈ L_2(V)` cut off to a ball is integrable. -/
theorem integrable_indicator_closedBall (h : Lp ℂ 2 (volume : Measure V)) (K : ℝ) :
    Integrable ((closedBall (0 : V) K).indicator h) := by
  refine memLp_one_iff_integrable.1 (memLp_iff.2 ?_)
  refine (eLpNorm_one_indicator_closedBall_le h K).trans_lt (ENNReal.mul_lt_top ?_ eNorm_lt_top)
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) measure_closedBall_lt_top.ne

/-- **Cauchy–Schwarz on a ball**, in `ℝ`: `∫ |1_{B_K} h| ≤ |B_K|^{1/2} ‖h‖_2` for `h ∈ L_2(V)`. -/
theorem integral_norm_indicator_closedBall_le (h : Lp ℂ 2 (volume : Measure V)) (K : ℝ) :
    ∫ ξ, ‖(closedBall (0 : V) K).indicator h ξ‖ ≤ ballVolumeSqrt V K * ‖h‖ := by
  have hfin : volume (closedBall (0 : V) K) ^ (1 / 2 : ℝ) * ‖h‖ₑ ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      measure_closedBall_lt_top.ne) eNorm_ne_top
  have hm : AEStronglyMeasurable ((closedBall (0 : V) K).indicator (h : V → ℂ)) volume :=
    (Lp.aestronglyMeasurable h).indicator measurableSet_closedBall
  rw [integral_norm_eq_lintegral_eNorm hm, ← eLpNorm_one_eq_lintegral_eNorm hm]
  refine (ENNReal.toReal_mono hfin (eLpNorm_one_indicator_closedBall_le h K)).trans_eq ?_
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, toReal_eNorm, ballVolumeSqrt]

/-- **Band-limited functions are bounded**: for `h ∈ L_2(V)` and every `x`,
`|𝓕⁻(1_{B_K} h)(x)| ≤ |B_K|^{1/2} ‖h‖_2`. -/
theorem norm_fourierInv_indicator_le (h : Lp ℂ 2 (volume : Measure V)) (K : ℝ) (x : V) :
    ‖𝓕⁻ ((closedBall (0 : V) K).indicator h) x‖ ≤ ballVolumeSqrt V K * ‖h‖ :=
  (norm_fourierInv_le_integral_norm _ x).trans (integral_norm_indicator_closedBall_le h K)

/-- **Band-limited functions are Lipschitz**, with explicit constant: for `h ∈ L_2(V)`, the
function `𝓕⁻(1_{B_K} h)` is Lipschitz on `V` with constant `2π max(K, 0) |B_K|^{1/2} ‖h‖_2`
(`Rd.norm_fourierInv_sub_le` and Cauchy–Schwarz on the ball). -/
theorem lipschitzWith_fourierInv_indicator (h : Lp ℂ 2 (volume : Measure V)) (K : ℝ) :
    LipschitzWith (2 * π * max K 0 * ballVolumeSqrt V K * ‖h‖).toNNReal
      (𝓕⁻ ((closedBall (0 : V) K).indicator h)) := by
  have hC := ballVolumeSqrt_nonneg (V := V) K
  have hsupp : ∀ ξ : V, max K 0 < ‖ξ‖ → (closedBall (0 : V) K).indicator h ξ = 0 :=
    fun ξ hξ => Set.indicator_of_notMem (by
      rw [mem_closedBall, dist_zero_right, not_le]
      exact (le_max_left K 0).trans_lt hξ) _
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
  calc _ ≤ 2 * π * max K 0 * ‖x - y‖ * ∫ ξ, ‖(closedBall (0 : V) K).indicator h ξ‖ :=
        norm_fourierInv_sub_le (integrable_indicator_closedBall h K) (Eventually.of_forall hsupp)
          x y
    _ ≤ 2 * π * max K 0 * ‖x - y‖ * (ballVolumeSqrt V K * ‖h‖) := by
        gcongr
        exact integral_norm_indicator_closedBall_le h K
    _ = _ := by ring

/-! ### Arzelà–Ascoli and the restriction to a bounded set -/

/-- **Arzelà–Ascoli for Lipschitz functions**: on a compact metric space `X`, the bounded
continuous functions with `|g| ≤ C` that are Lipschitz with constant `L` form a totally bounded
set in the uniform norm (Mathlib's `BoundedContinuousFunction.arzela_ascoli`: the family is
equicontinuous and takes values in the compact disc of radius `C`). -/
theorem totallyBounded_setOf_lipschitzWith {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    (C : ℝ) (L : ℝ≥0) :
    TotallyBounded {g : X →ᵇ ℂ | (∀ x, ‖g x‖ ≤ C) ∧ LipschitzWith L g} :=
  (BoundedContinuousFunction.arzela_ascoli (closedBall (0 : ℂ) C) (isCompact_closedBall 0 C)
    {g : X →ᵇ ℂ | (∀ x, ‖g x‖ ≤ C) ∧ LipschitzWith L g}
    (fun _ x hg => mem_closedBall_zero_iff.2 (hg.1 x))
    (LipschitzWith.uniformEquicontinuous _ L fun g => g.2.2).equicontinuous).totallyBounded.subset
    subset_closure

variable {Ω : Set V}

open scoped Classical in
/-- A bounded continuous function `g` on the closure of `Ω ⊆ V`, extended by `0` to all of
`V`. -/
noncomputable def extendClosure (Ω : Set V) (g : closure Ω →ᵇ ℂ) : V → ℂ :=
  fun x => if hx : x ∈ closure Ω then g ⟨x, hx⟩ else 0

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- On the closure of `Ω` the extension by `0` is `g`. -/
theorem extendClosure_of_mem (g : closure Ω →ᵇ ℂ) {x : V} (hx : x ∈ closure Ω) :
    extendClosure Ω g x = g ⟨x, hx⟩ := by
  simp [extendClosure, hx]

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
/-- The extension by `0` is measurable: `g` is continuous on the closed set `closure Ω`. -/
theorem measurable_extendClosure (g : closure Ω →ᵇ ℂ) : Measurable (extendClosure Ω g) := by
  classical
  exact Measurable.dite g.continuous.measurable measurable_const isClosed_closure.measurableSet

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The extension by `0` is bounded by the uniform norm of `g`. -/
theorem norm_extendClosure_le (g : closure Ω →ᵇ ℂ) (x : V) : ‖extendClosure Ω g x‖ ≤ ‖g‖ := by
  by_cases hx : x ∈ closure Ω
  · rw [extendClosure_of_mem g hx]
    exact g.norm_coe_le_norm _
  · simp only [extendClosure, hx, dite_false, norm_zero]
    exact norm_nonneg g

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The extensions by `0` of `g` and `g'` differ by at most the uniform distance of `g` and
`g'`. -/
theorem norm_extendClosure_sub_le (g g' : closure Ω →ᵇ ℂ) (x : V) :
    ‖extendClosure Ω g x - extendClosure Ω g' x‖ ≤ dist g g' := by
  by_cases hx : x ∈ closure Ω
  · rw [extendClosure_of_mem g hx, extendClosure_of_mem g' hx, ← dist_eq_norm]
    exact g.dist_coe_le_dist _
  · simp only [extendClosure, hx, dite_false, sub_zero, norm_zero]
    exact dist_nonneg

/-- On a bounded set `Ω`, the extension by `0` lies in `L_2(Ω)`: it is measurable and bounded,
and `Ω` has finite volume. -/
theorem memLp_extendClosure (hΩ : Bornology.IsBounded Ω) (g : closure Ω →ᵇ ℂ) :
    MemLp (extendClosure Ω g) 2 (volume.restrict Ω) := by
  have : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.2 hΩ.measure_lt_top.ne
  exact MemLp.of_bound (measurable_extendClosure g).aestronglyMeasurable ‖g‖
    (ae_of_all _ (norm_extendClosure_le g))

/-- **Bounded continuous functions on `closure Ω` as elements of `L_2(Ω)`**, for bounded `Ω`. -/
noncomputable def closureToLp (hΩ : Bornology.IsBounded Ω) (g : closure Ω →ᵇ ℂ) :
    Lp ℂ 2 (volume.restrict Ω) :=
  (memLp_extendClosure hΩ g).toLp _

/-- `‖g - g'‖_{L_2(Ω)} ≤ |Ω|^{1/2} ‖g - g'‖_∞` (Mathlib's `Lp.norm_le_of_ae_bound`). -/
theorem dist_closureToLp_le (hΩ : Bornology.IsBounded Ω) (g g' : closure Ω →ᵇ ℂ) :
    dist (closureToLp hΩ g) (closureToLp hΩ g') ≤
      (volume Ω).toReal ^ (1 / 2 : ℝ) * dist g g' := by
  have : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.2 hΩ.measure_lt_top.ne
  have hae : ∀ᵐ x ∂(volume.restrict Ω),
      ‖(closureToLp hΩ g - closureToLp hΩ g' : Lp ℂ 2 (volume.restrict Ω)) x‖ ≤ dist g g' := by
    filter_upwards [Lp.coeFn_sub (closureToLp hΩ g) (closureToLp hΩ g'),
      (memLp_extendClosure hΩ g).coeFn_toLp, (memLp_extendClosure hΩ g').coeFn_toLp]
      with x h0 h1 h2
    rw [h0, Pi.sub_apply, closureToLp, closureToLp, h1, h2]
    exact norm_extendClosure_sub_le g g' x
  rw [dist_eq_norm]
  refine (Lp.norm_le_of_ae_bound dist_nonneg hae).trans_eq ?_
  rw [measureUnivNNReal, Measure.restrict_apply_univ, ENNReal.coe_toNNReal_eq_toReal]
  norm_num

/-- The map `g ↦ g` from bounded continuous functions on `closure Ω` to `L_2(Ω)` is Lipschitz
with constant `|Ω|^{1/2}`. -/
theorem lipschitzWith_closureToLp (hΩ : Bornology.IsBounded Ω) :
    LipschitzWith ((volume Ω).toReal ^ (1 / 2 : ℝ)).toNNReal (closureToLp hΩ) :=
  LipschitzWith.of_dist_le_mul fun g g' => by
    rw [Real.coe_toNNReal _ (Real.rpow_nonneg ENNReal.toReal_nonneg _)]
    exact dist_closureToLp_le hΩ g g'

/-! ### Rellich's theorem -/

/-- **The truncation as an inverse Fourier integral**: `truncL2 K F` agrees almost everywhere with
the pointwise inverse Fourier integral `x ↦ ∫ e^(2πi⟪ξ, x⟫) 1_{B_K}(ξ) 𝓕(toL2 F)(ξ) dξ`, since
`1_{B_K} 𝓕(toL2 F)` is integrable (`Rd.integrable_indicator_closedBall`,
`Rd.fourierInv_Lp_ae_eq_of_integrable`). -/
theorem truncL2_ae_eq_fourierInv_indicator (K : ℝ) (F : H^{1, 2}(V, ℂ)) :
    (truncL2 K F : V → ℂ) =ᵐ[volume]
      𝓕⁻ ((closedBall (0 : V) K).indicator (𝓕 (toL2 F) : Lp ℂ 2 (volume : Measure V))) := by
  rw [truncL2_apply]
  refine (fourierInv_Lp_ae_eq_of_integrable _ ((integrable_indicator_closedBall _ K).congr
    (indicatorLp_apply_ae _ _).symm)).trans (Eventually.of_forall fun x => ?_)
  exact Real.fourierInv_congr_ae (indicatorLp_apply_ae _ _) x

/-- **The truncations restricted to `Ω` are band-limited functions**: for `‖F‖_{H^1} ≤ 1`, the
restriction of `truncL2 K F` to a bounded set `Ω` is (the class of) a bounded continuous function
on `closure Ω` with `|g| ≤ |B_K|^{1/2}` that is Lipschitz with constant
`2π max(K, 0) |B_K|^{1/2}`: the function `𝓕⁻(1_{B_K} 𝓕(toL2 F))`
(`Rd.truncL2_ae_eq_fourierInv_indicator`, `Rd.norm_fourierInv_indicator_le`,
`Rd.lipschitzWith_fourierInv_indicator`), since `‖𝓕(toL2 F)‖_2 ≤ ‖F‖_{H^1} ≤ 1`. -/
theorem restr_truncL2_mem_closureToLp_image (hΩ : Bornology.IsBounded Ω) (K : ℝ)
    {F : H^{1, 2}(V, ℂ)} (hF : ‖F‖ ≤ 1) :
    LpToLpRestrictCLM V ℂ ℂ volume 2 Ω (truncL2 K F) ∈ closureToLp hΩ ''
      {g | (∀ x, ‖g x‖ ≤ ballVolumeSqrt V K) ∧
        LipschitzWith (2 * π * max K 0 * ballVolumeSqrt V K).toNNReal g} := by
  have : CompactSpace (closure Ω) := isCompact_iff_compactSpace.1 hΩ.isCompact_closure
  have hy : ‖(𝓕 (toL2 F) : Lp ℂ 2 (volume : Measure V))‖ ≤ 1 := by
    rw [Lp.norm_fourier_eq]
    exact (norm_toL2_le F).trans hF
  have hC := ballVolumeSqrt_nonneg (V := V) K
  have hGL := lipschitzWith_fourierInv_indicator (𝓕 (toL2 F)) K
  have hle : (2 * π * max K 0 * ballVolumeSqrt V K *
      ‖(𝓕 (toL2 F) : Lp ℂ 2 (volume : Measure V))‖).toNNReal ≤
      (2 * π * max K 0 * ballVolumeSqrt V K).toNNReal :=
    Real.toNNReal_le_toNNReal (mul_le_of_le_one_right (by positivity) hy)
  let g : closure Ω →ᵇ ℂ := BoundedContinuousFunction.mkOfCompact
    ⟨fun x => 𝓕⁻ ((closedBall (0 : V) K).indicator
      (𝓕 (toL2 F) : Lp ℂ 2 (volume : Measure V))) x,
      hGL.continuous.comp continuous_subtype_val⟩
  refine ⟨g, ⟨fun x => ?_, LipschitzWith.of_dist_le_mul fun a b => ?_⟩, ?_⟩
  · exact (norm_fourierInv_indicator_le _ K x.1).trans (mul_le_of_le_one_right hC hy)
  · exact (hGL.weaken hle).dist_le_mul a b
  · refine Lp.ext ?_
    have h4 : ∀ᵐ x ∂(volume.restrict Ω), x ∈ closure Ω :=
      (ae_restrict_mem isClosed_closure.measurableSet).filter_mono
        (ae_mono (Measure.restrict_mono subset_closure le_rfl))
    filter_upwards [(memLp_extendClosure hΩ g).coeFn_toLp,
      LpToLpRestrictCLM_coeFn ℂ Ω (truncL2 K F),
      ae_restrict_of_ae (truncL2_ae_eq_fourierInv_indicator K F), h4] with x e1 e2 e3 e4
    rw [closureToLp, e1, e2, e3, extendClosure_of_mem g e4]
    rfl

/-- **The truncated operators are compact on bounded sets**: for bounded `Ω ⊆ V` and every
`K`, `F ↦ (truncL2 K F)|_Ω` is a compact operator from `H^1(V)` to `L_2(Ω)`. The image of the
unit ball lies in the image, under the Lipschitz map `Rd.closureToLp`, of a set of uniformly
bounded and uniformly Lipschitz functions on the compact set `closure Ω`
(`Rd.restr_truncL2_mem_closureToLp_image`), which is totally bounded by Arzelà–Ascoli
(`Rd.totallyBounded_setOf_lipschitzWith`). -/
theorem isCompactOperator_restr_truncL2 (hΩ : Bornology.IsBounded Ω) (K : ℝ) :
    IsCompactOperator (LpToLpRestrictCLM V ℂ ℂ volume 2 Ω ∘L truncL2 K) := by
  have : CompactSpace (closure Ω) := isCompact_iff_compactSpace.1 hΩ.isCompact_closure
  refine (isCompactOperator_iff_isCompact_closure_image_closedBall
    ((LpToLpRestrictCLM V ℂ ℂ volume 2 Ω ∘L truncL2 K : H^{1, 2}(V, ℂ) →L[ℂ] _) :
      H^{1, 2}(V, ℂ) →ₗ[ℂ] Lp ℂ 2 (volume.restrict Ω)) one_pos).2 ?_
  refine isCompact_iff_totallyBounded_isComplete.2
    ⟨TotallyBounded.closure ?_, isClosed_closure.isComplete⟩
  refine ((totallyBounded_setOf_lipschitzWith (ballVolumeSqrt V K)
    (2 * π * max K 0 * ballVolumeSqrt V K).toNNReal).image
    (lipschitzWith_closureToLp hΩ).uniformContinuous).subset ?_
  rintro _ ⟨F, hF, rfl⟩
  exact restr_truncL2_mem_closureToLp_image hΩ K (mem_closedBall_zero_iff.1 hF)

/-- **Rellich's theorem**: for every bounded set `Ω ⊆ V`, the restriction
`F ↦ F|_Ω` from Mathlib's Sobolev space `H^1(V) = H^{1,2}(V, ℂ)` to `L_2(Ω)` is a compact
operator. It is the operator-norm limit of the compact operators `F ↦ (truncL2 K F)|_Ω` as
`K → ∞` (`Rd.tendsto_truncL2`, `Rd.isCompactOperator_restr_truncL2`, Mathlib's
`isCompactOperator_of_tendsto`). -/
theorem isCompactOperator_restr_toL2 (hΩ : Bornology.IsBounded Ω) :
    IsCompactOperator (LpToLpRestrictCLM V ℂ ℂ volume 2 Ω ∘L
      (toL2 : H^{1, 2}(V, ℂ) →L[ℂ] Lp ℂ 2 (volume : Measure V))) :=
  isCompactOperator_of_tendsto
    (((ContinuousLinearMap.compL ℂ H^{1, 2}(V, ℂ) (Lp ℂ 2 (volume : Measure V))
      (Lp ℂ 2 (volume.restrict Ω)) (LpToLpRestrictCLM V ℂ ℂ volume 2 Ω)).continuous.tendsto
        _).comp tendsto_truncL2)
    (Eventually.of_forall fun K => isCompactOperator_restr_truncL2 hΩ K)

/-- **Rellich's theorem for sequences**: for bounded `Ω ⊆ V`, every sequence `F_n` in `H^1(V)`
with `‖F_n‖_{H^1} ≤ M` has a subsequence whose restrictions to `Ω` converge in `L_2(Ω)`
(Mathlib's `IsCompact.tendsto_subseq` on the compact closure of the image of the ball of radius
`M`). -/
theorem exists_subseq_tendsto_restr (hΩ : Bornology.IsBounded Ω) {M : ℝ}
    (F : ℕ → H^{1, 2}(V, ℂ)) (hF : ∀ n, ‖F n‖ ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ u : Lp ℂ 2 (volume.restrict Ω),
      Tendsto (fun k => LpToLpRestrictCLM V ℂ ℂ volume 2 Ω (toL2 (F (φ k)))) atTop (𝓝 u) := by
  obtain ⟨u, -, φ, hφ, hu⟩ := (IsCompactOperator.isCompact_closure_image_closedBall
    (f := ((LpToLpRestrictCLM V ℂ ℂ volume 2 Ω ∘L toL2 : H^{1, 2}(V, ℂ) →L[ℂ] _) :
      H^{1, 2}(V, ℂ) →ₗ[ℂ] Lp ℂ 2 (volume.restrict Ω)))
    (isCompactOperator_restr_toL2 hΩ) M).tendsto_subseq
    (x := fun n => LpToLpRestrictCLM V ℂ ℂ volume 2 Ω (toL2 (F n)))
    (fun n => subset_closure ⟨F n, mem_closedBall_zero_iff.2 (hF n), rfl⟩)
  exact ⟨φ, hφ, u, hu⟩

/-! ### Rellich's theorem by weak gradients -/

/-- **Rellich's theorem by weak gradients**: let `Ω ⊆ V` be bounded and `(e_i)` an orthonormal
basis of `V`. Every sequence `f_n ∈ L_2(V)` with weak derivatives `g_{n,i} = ∂_{e_i} f_n` on `V`
in `L_2(V)` and `‖f_n‖_2² + ∑_i ‖g_{n,i}‖_2² ≤ M²` has a subsequence whose restrictions to `Ω`
converge in `L_2(Ω)`. Weak derivatives on `V` are derivatives of tempered distributions
(`Rd.hasWeakLineDeriv_top_iff`), so each `f_n` lies in `H^1(V)`
(`Rd.memSobolev_one_two_of_lineDerivOp_eq`) and is `toL2` of the element
`TemperedDistribution.MemSobolev.toBesselPotentialSpace` of `H^{1,2}(V, ℂ)`, of norm at most `|M|`
(`Rd.sq_norm_besselPotential_one_le`); `Rd.exists_subseq_tendsto_restr` applies. -/
theorem exists_subseq_tendsto_restr_of_hasWeakLineDeriv (hΩ : Bornology.IsBounded Ω)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V) {f : ℕ → Lp ℂ 2 (volume : Measure V)}
    {g : ℕ → ι → Lp ℂ 2 (volume : Measure V)}
    (hg : ∀ n i, HasWeakLineDeriv ⊤ (fun _ : Fin 1 => b i) (f n) (g n i)) {M : ℝ}
    (hM : ∀ n, ‖f n‖ ^ 2 + ∑ i, ‖g n i‖ ^ 2 ≤ M ^ 2) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ u : Lp ℂ 2 (volume.restrict Ω),
      Tendsto (fun k => LpToLpRestrictCLM V ℂ ℂ volume 2 Ω (f (φ k))) atTop (𝓝 u) := by
  have hS : ∀ n, TemperedDistribution.MemSobolev 1 2 (f n : 𝓢'(V, ℂ)) := fun n =>
    memSobolev_one_two_of_lineDerivOp_eq b fun i => hasWeakLineDeriv_top_iff.1 (hg n i)
  let F : ℕ → H^{1, 2}(V, ℂ) := fun n => (hS n).toBesselPotentialSpace
  have hF : ∀ n, toL2 (F n) = f n := fun n =>
    toL2_eq_of_toDistr_eq (F n) (hS n).toBesselPotentialSpace_toDistr.symm
  have hJ : ∀ n, besselPotential V ℂ 1 (f n : 𝓢'(V, ℂ)) = ((F n).toLp : 𝓢'(V, ℂ)) := fun n => by
    conv_lhs => rw [← (hS n).toBesselPotentialSpace_toDistr]
    exact (F n).bessel_toDistr_eq_toLp
  have hFM : ∀ n, ‖F n‖ ≤ |M| := fun n => by
    rw [← BesselPotentialSpace.norm_toLp_eq]
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (abs_nonneg M) two_ne_zero).1 ?_
    rw [sq_abs]
    exact (sq_norm_besselPotential_one_le b (hg n) (hJ n)).trans (hM n)
  obtain ⟨φ, hφ, u, hu⟩ := exists_subseq_tendsto_restr hΩ F hFM
  exact ⟨φ, hφ, u, by simpa only [hF] using hu⟩

end Rd
