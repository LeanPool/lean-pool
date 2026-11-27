/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Traces.GraphTraceExtension
public import Mathlib.MeasureTheory.Measure.Hausdorff

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Traces in charts: locality, approximation and change of chart

Three properties of the trace on a Lipschitz graph domain that make it a function on the boundary,
independent of the graph that describes it:

* **Locality** (`Rd.LipschitzGraph.trace_ae_eq_zero_of_ae_eq_zero`): if `f = 0` on `Ω ∩ U` for an
  open set `U`, then `Tr f = 0` almost everywhere on `γ⁻¹(U)`. The trace is the almost everywhere
  limit of mollified restrictions `(m_{2^J} ⋆ (m_{2^J} ⋆ f))(γ x')`
  (`Rd.LipschitzGraph.exists_subseq_tendsto_trace`), which only see `f` on
  `Ω ∩ B(γ x', 2LR 2^(-J))`. Hence two functions that agree on `Ω ∩ U` have the same trace on
  `γ⁻¹(U)` (`Rd.LipschitzGraph.trace_ae_eq_of_ae_eq`).
* **Approximation by continuous functions** (`Rd.LocalMeansBump.tendsto_modNorm_sub_partialSum`):
  the partial sums `G_J = ∑_{j ≤ J} η_j ⋆ (k_j ⋆ f)` of the reproducing formula are continuous and
  converge to `f` in `B^{σ'}_{p,1}` for `σ' < σ`, by the synthesis with the dual kernels.
* **Change of chart** (`Rd.LipschitzGraph.trace_ae_eq_trace_comp`): if the boundaries of two graph
  domains `Ω₁`, `Ω₂` agree near `γ₁(x')`, then `Tr₁ F(x') = Tr₂ F(P₂ γ₁ x')` for almost every such
  `x'`. Both traces are limits of the restrictions of the same continuous `G_J`, and the change of
  chart `P₁ ∘ γ₂` is Lipschitz between spaces of the same dimension, so it maps null sets to null
  sets (`Rd.volume_image_eq_zero_of_lipschitzWith`, through Mathlib's Hausdorff measures, which are
  Haar measures in finite dimension); hence almost everywhere statements pass from one chart to the
  other (`Rd.LipschitzGraph.ae_proj_graphMap`).
* **Products with smooth functions** (`Rd.LipschitzGraph.trace_mulLp_ae`): `Tr(ψ F) = (ψ ∘ γ) Tr F`,
  and the trace of `ψ F` is bounded in `B^s_{p,q}(H)` by the norm of `F`
  (`Rd.LipschitzGraph.exists_modNorm_trace_mulLp_le`).
* **Finite sums** (`Rd.LipschitzGraph.trace_finsetSum`): the trace of a finite sum is the sum of the
  traces.

The trace depends only on `1_Ω f` (`Rd.LipschitzGraph.trace_congr`).
-/

@[expose] public section

open MeasureTheory Filter Topology Module Metric
open scoped ENNReal NNReal

open ENNReal (lqNorm dyadicWeight)

namespace Rd

/-! ### Lipschitz images of null sets -/

/-- **Lipschitz maps keep null sets** between finite-dimensional inner product spaces of the same
dimension: `μ_H^k (f '' N) ≤ K^k μ_H^k N` for the Hausdorff measure `μ_H^k`, a Haar measure in
dimension `k` (Mathlib's `isAddHaarMeasure_hausdorffMeasure`), and Haar measures have the same null
sets. -/
theorem volume_image_eq_zero_of_lipschitzWith {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F]
    [BorelSpace F] (hEF : finrank ℝ E = finrank ℝ F) {f : E → F} {K : ℝ≥0}
    (hf : LipschitzWith K f) {N : Set E} (hN : volume N = 0) : volume (f '' N) = 0 := by
  have h1 : (μH[finrank ℝ E] : Measure E) N = 0 :=
    (Measure.absolutelyContinuous_isAddHaarMeasure μH[finrank ℝ E] (volume : Measure E)) hN
  have h2 : (μH[finrank ℝ F] : Measure F) (f '' N) = 0 := by
    have h := hf.hausdorffMeasure_image_le (d := finrank ℝ E) (Nat.cast_nonneg _) N
    rw [h1, mul_zero, hEF] at h
    exact le_antisymm h zero_le
  exact (Measure.absolutelyContinuous_isAddHaarMeasure (volume : Measure F) μH[finrank ℝ F]) h2

namespace LocalMeansBump

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] (b : LocalMeansBump V) {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The partial sums of the reproducing formula, `G_J = ∑_{j ≤ J} η_j ⋆ (k_j ⋆ f)`. -/
noncomputable def partialSum (hp : p ≠ ∞) (L J : ℕ) (f : Lp ℂ p (volume : Measure V)) :
    Lp ℂ p (volume : Measure V) :=
  ∑ j ∈ Finset.range (J + 1), convLp hp (b.integrable_dual L j) (b.localMean hp L j f)

/-- The partial sums have the continuous representatives `∑_{j ≤ J} η_j ⋆ (k_j ⋆ f)`. -/
theorem partialSum_ae (hp : p ≠ ∞) (L J : ℕ) (f : Lp ℂ p (volume : Measure V)) :
    b.partialSum hp L J f =ᵐ[volume]
      fun x => ∑ j ∈ Finset.range (J + 1), conv (b.dual L j) (b.localMean hp L j f) volume x := by
  filter_upwards [Lp.coeFn_fun_finsetSum (Finset.range (J + 1))
    (fun j => convLp hp (b.integrable_dual L j) (b.localMean hp L j f)),
    ae_all_iff.2 fun j => convLp_apply_ae hp (b.integrable_dual L j) (b.localMean hp L j f)]
    with x h1 h2
  rw [partialSum, h1]
  exact Finset.sum_congr rfl fun j _ => h2 j

/-- The representatives of the partial sums are continuous. -/
theorem continuous_partialSum_rep (hp : p ≠ ∞) (L J : ℕ) (f : Lp ℂ p (volume : Measure V)) :
    Continuous fun x => ∑ j ∈ Finset.range (J + 1),
      conv (b.dual L j) (b.localMean hp L j f) volume x :=
  continuous_finsetSum _ fun j _ => (b.hasCompactSupport_dual L j).continuous_convolution_left
    (ContinuousLinearMap.mul ℂ ℂ) (b.continuous_dual L j) ((Lp.memLp _).locallyIntegrable Fact.out)

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- `∑_{j ≤ I} [J < j] u_j = ∑_{j ≤ I} u_j - ∑_{j ≤ J} u_j` for `J ≤ I`. -/
theorem sum_range_ite_lt {E : Type*} [AddCommGroup E] (u : ℕ → E) {I J : ℕ} (hJI : J ≤ I) :
    ∑ j ∈ Finset.range (I + 1), (if J < j then u j else 0) =
      ∑ j ∈ Finset.range (I + 1), u j - ∑ j ∈ Finset.range (J + 1), u j := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, eq_sub_iff_add_eq,
    ← Finset.sum_filter_add_sum_filter_not (Finset.range (I + 1)) (fun j => J < j)]
  congr 1
  apply Finset.sum_congr _ fun _ _ => rfl
  ext j
  simp only [Finset.mem_filter, Finset.mem_range, not_lt]
  omega

/-- **The reproducing formula in `B^{σ'}_{p,1}`** (approximation by continuous functions): if
`‖f‖_p + ‖(2^(kσ) ω_L(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞` and `0 < σ' < σ`, `σ' < L`, then
`‖f - G_J‖_p + ∑_k 2^(kσ') ω_L(f - G_J, 2^(-k))_p → 0`: the tail
`f - G_J = ∑_{j > J} η_j ⋆ (k_j ⋆ f)` is bounded by the synthesis with the dual kernels
(`Rd.LocalMeansBump.modNorm_le_of_tendsto`) by
`∑_{j > J} 2^(jσ') ‖k_j ⋆ f‖_p ≤ ∑_{j > J} 2^(-j(σ - σ')) ‖(2^(iσ) ‖k_i ⋆ f‖_p)_i‖_{ℓ_q}`. -/
theorem tendsto_modNorm_sub_partialSum (hp : p ≠ ∞) {L : ℕ} (hL : 1 ≤ L) {σ σ' : ℝ}
    (hσ' : 0 < σ') (hσσ' : σ' < σ) (hσ'L : σ' < L) {q : ℝ≥0∞} (hq : 1 ≤ q)
    {f : Lp ℂ p (volume : Measure V)}
    (hf : ‖f‖ₑ + lqNorm q (fun k => dyadicWeight σ k * lpModulus p L f k) < ∞) :
    Tendsto (fun J => ‖f - b.partialSum hp L J f‖ₑ + lqNorm 1 (fun k =>
      dyadicWeight σ' k * lpModulus p L (f - b.partialSum hp L J f) k)) atTop (𝓝 0) := by
  set Y := b.localMeansNorm hp L σ q f
  have hY : Y < ∞ := (b.localMeansNorm_le hp L σ hq f).trans_lt
    (ENNReal.mul_lt_top (b.upperConst_ne_top L σ).lt_top hf)
  set a : ℕ → ℝ≥0∞ := fun j => dyadicWeight σ' j * ‖b.localMean hp L j f‖ₑ
  have ha : ∀ j, a j ≤ Y * dyadicWeight (-(σ - σ')) j := fun j => by
    have hYj : dyadicWeight σ j * ‖b.localMean hp L j f‖ₑ ≤ Y :=
      ENNReal.le_lqNorm (zero_lt_one.trans_le hq).ne'
        (fun j => dyadicWeight σ j * ‖b.localMean hp L j f‖ₑ) j
    calc a j = dyadicWeight (-(σ - σ')) j * (dyadicWeight σ j * ‖b.localMean hp L j f‖ₑ) := by
          simp only [a]
          rw [← mul_assoc, ← ENNReal.dyadicWeight_add]
          congr 2
          ring
      _ ≤ dyadicWeight (-(σ - σ')) j * Y := mul_le_mul' le_rfl hYj
      _ = Y * dyadicWeight (-(σ - σ')) j := mul_comm _ _
  have hasum : ∑' j, a j ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (tsum_le_tsum ha)
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_dyadicWeight_neg]
    exact ENNReal.mul_ne_top hY.ne (ENNReal.one_sub_two_rpow_neg_inv_ne_top (by linarith))
  have hbound : ∀ J, ‖f - b.partialSum hp L J f‖ₑ + lqNorm 1 (fun k =>
      dyadicWeight σ' k * lpModulus p L (f - b.partialSum hp L J f) k) ≤
        b.synthConst L σ' * ∑' i, a (i + (J + 1)) := fun J => by
    set h' : ℕ → Lp ℂ p (volume : Measure V) := fun j => if J < j then b.localMean hp L j f else 0
    have hrep : Tendsto (fun I => ∑ j ∈ Finset.range (I + 1),
        convLp hp (b.integrable_dual L j) (h' j)) atTop (𝓝 (f - b.partialSum hp L J f)) := by
      have h0 := (b.tendsto_sum_dual_localMean hp hL f).sub_const (b.partialSum hp L J f)
      refine h0.congr' ?_
      filter_upwards [eventually_ge_atTop J] with I hI
      have hite : ∀ j, convLp hp (b.integrable_dual L j) (h' j) =
          if J < j then convLp hp (b.integrable_dual L j) (b.localMean hp L j f) else 0 :=
        fun j => by
          simp only [h']
          split_ifs <;> simp
      simp_rw [hite]
      rw [sum_range_ite_lt _ hI, partialSum]
    refine (b.modNorm_le_of_tendsto hp L σ' le_rfl hrep).trans (mul_le_mul' le_rfl ?_)
    rw [ENNReal.lqNorm_one]
    have hsplit : ∑' j, dyadicWeight σ' j * ‖h' j‖ₑ = ∑' i, a (i + (J + 1)) := by
      rw [← (CompleteLattice.summable).sum_add_tsum_nat_add' (k := J + 1)]
      have hzero : ∑ j ∈ Finset.range (J + 1), dyadicWeight σ' j * ‖h' j‖ₑ = 0 :=
        Finset.sum_eq_zero fun j hj => by
          have : ¬ J < j := by
            have := Finset.mem_range.1 hj
            omega
          simp [h', this]
      rw [hzero, zero_add]
      refine tsum_congr fun i => ?_
      simp [h', a, show J < i + (J + 1) by omega]
    exact hsplit.le
  have htail : Tendsto (fun J => b.synthConst L σ' * ∑' i, a (i + (J + 1))) atTop (𝓝 0) := by
    have h := ((ENNReal.tendsto_sum_nat_add a hasum).comp (tendsto_add_atTop_nat 1))
    simpa using ENNReal.Tendsto.const_mul h (Or.inr (b.synthConst_ne_top hσ' hσ'L))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htail
    (fun J => zero_le) hbound

/-- **The partial sums have finite norms**: `‖G_J‖_p + ‖(2^(kσ) ω_L(G_J, 2^(-k))_p)_k‖_{ℓ_q} < ∞`
for `0 < σ < L`, by the synthesis with the dual kernels for finitely many terms. -/
theorem modNorm_partialSum_lt_top (hp : p ≠ ∞) (L J : ℕ) {σ : ℝ} (hσ : 0 < σ) (hσL : σ < L)
    {q : ℝ≥0∞} (hq : 1 ≤ q) (f : Lp ℂ p (volume : Measure V)) :
    ‖b.partialSum hp L J f‖ₑ + lqNorm q (fun k =>
      dyadicWeight σ k * lpModulus p L (b.partialSum hp L J f) k) < ∞ := by
  set h' : ℕ → Lp ℂ p (volume : Measure V) := fun j => if j ≤ J then b.localMean hp L j f else 0
  have hrep : Tendsto (fun I => ∑ j ∈ Finset.range (I + 1),
      convLp hp (b.integrable_dual L j) (h' j)) atTop (𝓝 (b.partialSum hp L J f)) := by
    refine tendsto_atTop_of_eventually_const (i₀ := J) fun I hI => ?_
    have hite : ∀ j, convLp hp (b.integrable_dual L j) (h' j) =
        if j ≤ J then convLp hp (b.integrable_dual L j) (b.localMean hp L j f) else 0 :=
      fun j => by
        simp only [h']
        split_ifs <;> simp
    simp_rw [hite]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, partialSum]
    apply Finset.sum_congr _ fun _ _ => rfl
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  refine (b.modNorm_le_of_tendsto hp L σ hq hrep).trans_lt (ENNReal.mul_lt_top
    (b.synthConst_ne_top hσ hσL).lt_top ?_)
  refine (ENNReal.lqNorm_le_lqNorm_one hq _).trans_lt ?_
  rw [tsum_eq_sum (s := Finset.range (J + 1)) fun j hj => by
    have : ¬ j ≤ J := fun h => hj (Finset.mem_range.2 (Nat.lt_succ_of_le h))
    simp [h', this]]
  exact ENNReal.sum_lt_top.2 fun j _ => ENNReal.mul_lt_top (ENNReal.dyadicWeight_lt_top _ _)
    eNorm_lt_top

end LocalMeansBump

namespace LipschitzGraph

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] (Ω : LipschitzGraph V) {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ### Locality -/

/-- **The mollified restrictions vanish where `f` does**: if `f = 0` almost everywhere on
`Ω ∩ B(γ x', δ)` and `2 L R 2^(-J) < δ`, then `(m_{2^J} ⋆ (m_{2^J} ⋆ f))(γ x') = 0`, since the cone
kernels only see `f` on `Ω ∩ B(γ x', 2 L R 2^(-J))`. -/
theorem conv_scaled_convLp_eq_zero (hp : p ≠ ∞) (L J : ℕ) {f : Lp ℂ p (volume : Measure V)}
    (x' : Ω.hyperplane) {δ : ℝ} (hJ : 2 * L * Ω.coneBump.radius / 2 ^ J < δ)
    (hf : ∀ᵐ x ∂volume, x ∈ Ω.domain → x ∈ ball (Ω.graphMap x') δ → f x = 0) :
    conv (Ω.coneBump.scaled L J) (convLp hp (Ω.coneBump.integrable_scaled L J) f) volume
      (Ω.graphMap x') = 0 := by
  set y := Ω.graphMap x'
  have hLR : 0 ≤ (L : ℝ) * Ω.coneBump.radius :=
    mul_nonneg (Nat.cast_nonneg L) Ω.coneBump.radius_nonneg
  have hsmall : ∀ z, Ω.coneBump.scaled L J z ≠ 0 → ‖z‖ ≤ L * Ω.coneBump.radius / 2 ^ J :=
    fun z hz => not_lt.1 fun h => hz (Ω.coneBump.scaled_eq_zero_of_lt L J h)
  rw [conv_congr_ae (convLp_apply_ae hp _ f), conv_apply]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun z => ?_)
  by_cases hz : Ω.coneBump.scaled L J z = 0
  · simp [hz]
  have hw : y - z ∈ Ω.domain := by
    rw [sub_eq_add_neg]
    exact Ω.graphMap_add_mem x' (Ω.coneSupported_scaled L J z hz)
  have hinner : conv (Ω.coneBump.scaled L J) f volume (y - z) = 0 := by
    rw [conv_apply]
    have hf' := (Measure.measurePreserving_sub_left volume (y - z)).quasiMeasurePreserving.ae hf
    refine integral_eq_zero_of_ae (hf'.mono fun z' hz' => ?_)
    by_cases hz'0 : Ω.coneBump.scaled L J z' = 0
    · simp [hz'0]
    have hdom : y - z - z' ∈ Ω.domain := by
      rw [sub_eq_add_neg]
      exact Ω.add_mem hw (Ω.coneSupported_scaled L J z' hz'0)
    have hball : y - z - z' ∈ ball y δ := by
      rw [mem_ball, dist_eq_norm]
      calc ‖y - z - z' - y‖ = ‖z + z'‖ := by rw [show y - z - z' - y = -(z + z') by abel, norm_neg]
        _ ≤ ‖z‖ + ‖z'‖ := norm_add_le _ _
        _ ≤ L * Ω.coneBump.radius / 2 ^ J + L * Ω.coneBump.radius / 2 ^ J :=
            add_le_add (hsmall z hz) (hsmall z' hz'0)
        _ = 2 * L * Ω.coneBump.radius / 2 ^ J := by ring
        _ < δ := hJ
    simp [hz' hdom hball]
  simp [hinner]

/-- **Locality of the trace**: if `f = 0` almost everywhere on `Ω ∩ U` for an open set `U`, then
`Tr f = 0` almost everywhere on `γ⁻¹(U)`. -/
theorem trace_ae_eq_zero_of_ae_eq_zero (hp : p ≠ ∞) (L : ℕ) {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞}
    (hq : 1 ≤ q) {f : Lp ℂ p (volume : Measure V)}
    (hX : Ω.intrinsicNorm hp L (s + 1 / p.toReal) q f < ∞) {U : Set V} (hU : IsOpen U)
    (hfU : ∀ᵐ x ∂volume, x ∈ Ω.domain → x ∈ U → f x = 0) :
    ∀ᵐ x' ∂(volume : Measure Ω.hyperplane), Ω.graphMap x' ∈ U → Ω.trace hp L f x' = 0 := by
  obtain ⟨ns, hns, hae⟩ := Ω.exists_subseq_tendsto_trace hp L hs hq hX
  filter_upwards [hae] with x' hx hxU
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hU _ hxU
  obtain ⟨J₀, hJ₀⟩ := pow_unbounded_of_one_lt (2 * L * Ω.coneBump.radius / δ)
    (one_lt_two : (1 : ℝ) < 2)
  have hev : ∀ᶠ k in atTop, conv (Ω.coneBump.scaled L (ns k))
      (convLp hp (Ω.coneBump.integrable_scaled L (ns k)) f) volume (Ω.graphMap x') = 0 := by
    filter_upwards [hns.tendsto_atTop.eventually_ge_atTop J₀] with k hk
    refine Ω.conv_scaled_convLp_eq_zero hp L (ns k) x' ?_ (hfU.mono fun x hx hxd hxb =>
      hx hxd (hball hxb))
    have h2 : (2 : ℝ) ^ J₀ ≤ 2 ^ ns k := pow_le_pow_right₀ one_le_two hk
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hδ] at hJ₀
    nlinarith
  exact tendsto_nhds_unique hx (tendsto_const_nhds.congr' (hev.mono fun k hk => hk.symm))

/-- The intrinsic quasi-norm of a difference is at most the sum of the intrinsic quasi-norms. -/
theorem intrinsicNorm_sub_le (hp : p ≠ ∞) (L : ℕ) (σ : ℝ) {q : ℝ≥0∞} (hq : 1 ≤ q)
    (f₁ f₂ : Lp ℂ p (volume : Measure V)) :
    Ω.intrinsicNorm hp L σ q (f₁ - f₂) ≤
      Ω.intrinsicNorm hp L σ q f₁ + Ω.intrinsicNorm hp L σ q f₂ := by
  simp only [intrinsicNorm_def]
  refine (ENNReal.lqNorm_mono fun j => ?_).trans (ENNReal.lqNorm_add_le hq _ _)
  rw [map_sub, map_sub, ← mul_add]
  exact mul_le_mul' le_rfl (eNorm_sub_le)

/-- **Locality for two functions**: if `f₁ = f₂` almost everywhere on `Ω ∩ U` for an open set `U`,
then `Tr f₁ = Tr f₂` almost everywhere on `γ⁻¹(U)`. -/
theorem trace_ae_eq_of_ae_eq (hp : p ≠ ∞) (L : ℕ) {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞} (hq : 1 ≤ q)
    {f₁ f₂ : Lp ℂ p (volume : Measure V)}
    (h₁ : Ω.intrinsicNorm hp L (s + 1 / p.toReal) q f₁ < ∞)
    (h₂ : Ω.intrinsicNorm hp L (s + 1 / p.toReal) q f₂ < ∞) {U : Set V} (hU : IsOpen U)
    (hfU : ∀ᵐ x ∂volume, x ∈ Ω.domain → x ∈ U → f₁ x = f₂ x) :
    ∀ᵐ x' ∂(volume : Measure Ω.hyperplane), Ω.graphMap x' ∈ U →
      Ω.trace hp L f₁ x' = Ω.trace hp L f₂ x' := by
  have h0 := Ω.trace_ae_eq_zero_of_ae_eq_zero hp L hs hq
    ((Ω.intrinsicNorm_sub_le hp L _ hq f₁ f₂).trans_lt (ENNReal.add_lt_top.2 ⟨h₁, h₂⟩)) hU
    (by
      filter_upwards [hfU, Lp.coeFn_sub f₁ f₂] with x hx hsub hxd hxU
      rw [hsub, Pi.sub_apply, hx hxd hxU, sub_self])
  rw [Ω.trace_sub hp L hs hq h₁ h₂] at h0
  filter_upwards [h0, Lp.coeFn_sub (Ω.trace hp L f₁) (Ω.trace hp L f₂)] with x' h0' hsub hxU
  have h := h0' hxU
  rw [hsub, Pi.sub_apply, sub_eq_zero] at h
  exact h

/-- **The trace depends only on `f` on `Ω`**: `1_Ω F = 1_Ω f` gives `Tr F = Tr f`, since the
trace is built from the cut-offs `1_Ω (k_j ⋆ f)` and the kernels `k_j` are supported in `-K`. -/
theorem trace_congr (hp : p ≠ ∞) (L : ℕ) {F f : Lp ℂ p (volume : Measure V)}
    (hFf : Ω.cutoff F = Ω.cutoff f) : Ω.trace hp L F = Ω.trace hp L f := by
  unfold trace
  congr 1
  funext j
  exact Ω.cutoff_convLp_eq hp (Ω.coneBump.integrable_kernel L j) (Ω.coneSupported_kernel L j) hFf

/-! ### Change of chart -/

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The change of chart `P₁ ∘ γ₂` is Lipschitz with constant `1 + M₂`. -/
theorem lipschitzWith_proj_graphMap (Ω₁ Ω₂ : LipschitzGraph V) :
    LipschitzWith ⟨1 + Ω₂.M, by linarith [Ω₂.M_nonneg]⟩
      (fun y' : Ω₂.hyperplane => Ω₁.proj (Ω₂.graphMap y')) :=
  LipschitzWith.of_dist_le_mul fun y' z' => by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact (Ω₁.norm_proj_le _).trans (Ω₂.norm_graphMap_sub_le y' z')

omit [MeasurableSpace V] [BorelSpace V] in
/-- All the hyperplanes have dimension `n - 1`. -/
theorem finrank_hyperplane_eq_finrank (Ω₁ Ω₂ : LipschitzGraph V) :
    finrank ℝ Ω₁.hyperplane = finrank ℝ Ω₂.hyperplane := by
  have h1 := Ω₁.finrank_hyperplane_add_one
  have h2 := Ω₂.finrank_hyperplane_add_one
  omega

/-- **Null sets under the change of chart**: a property of almost every point of `H₂` holds at
`P₂ γ₁ x'` for almost every `x' ∈ H₁` whose boundary point `γ₁ x'` lies on the boundary of `Ω₂`:
the exceptional `x'` lie in the image of a null set under the Lipschitz map `P₁ ∘ γ₂`
(`Rd.volume_image_eq_zero_of_lipschitzWith`). -/
theorem ae_proj_graphMap (Ω₁ Ω₂ : LipschitzGraph V) {P : Ω₂.hyperplane → Prop}
    (hP : ∀ᵐ y' ∂(volume : Measure Ω₂.hyperplane), P y') :
    ∀ᵐ x' ∂(volume : Measure Ω₁.hyperplane),
      Ω₂.graphMap (Ω₂.proj (Ω₁.graphMap x')) = Ω₁.graphMap x' → P (Ω₂.proj (Ω₁.graphMap x')) := by
  have hσ : volume ((fun y' : Ω₂.hyperplane => Ω₁.proj (Ω₂.graphMap y')) '' {y' | ¬ P y'}) = 0 :=
    volume_image_eq_zero_of_lipschitzWith (Ω₂.finrank_hyperplane_eq_finrank Ω₁)
      (Ω₁.lipschitzWith_proj_graphMap Ω₂) (ae_iff.1 hP)
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hσ] with x' hx hA
  by_contra hcon
  exact hx ⟨_, hcon, by simp only; rw [hA, Ω₁.proj_graphMap]⟩

/-- **The traces of the partial sums converge**: for `F` with a finite `B^{s+1/p}_{p,q}`-norm of
order `L > s + 1/p` on `V`, `Tr G_J → Tr F` in `L_p(H)`, by the approximation in `B^{1/p}_{p,1}`
and the continuity of the trace there. -/
theorem tendsto_trace_partialSum (b : LocalMeansBump V) (hp : p ≠ ∞) {L : ℕ} (hL : 1 ≤ L)
    {s : ℝ} (hs : 0 < s) (hsL : s + 1 / p.toReal < L) {q : ℝ≥0∞} (hq : 1 ≤ q)
    {F : Lp ℂ p (volume : Measure V)}
    (hF : ‖F‖ₑ + lqNorm q (fun k =>
      dyadicWeight (s + 1 / p.toReal) k * lpModulus p L F k) < ∞) :
    Tendsto (fun J => Ω.trace hp L (b.partialSum hp L J F)) atTop (𝓝 (Ω.trace hp L F)) := by
  have hp1 : 1 ≤ p := Fact.out
  have hpr : 1 ≤ p.toReal := ENNReal.one_le_toReal_of_one_le hp1 hp
  have hpinv0 : 0 < 1 / p.toReal := by positivity
  have happ := b.tendsto_modNorm_sub_partialSum hp hL hpinv0 (by linarith) (by linarith) hq hF
  -- from some `J₀` on, the norms of `F - G_J` are finite
  obtain ⟨J₀, hJ₀⟩ := eventually_atTop.1
    (happ.eventually (gt_mem_nhds (zero_lt_one : (0 : ℝ≥0∞) < 1)))
  rw [← tendsto_add_atTop_iff_nat J₀]
  exact Ω.tendsto_trace_of_modNorm_sub_le hp L hs hq
    (Ω.intrinsicNorm_lt_top_of_modNorm hp L hq hF).2
    (fun J => (Ω.intrinsicNorm_lt_top_of_modNorm hp L hq
      (b.modNorm_partialSum_lt_top hp L (J + J₀) (by positivity) hsL hq F)).2)
    (happ.comp (tendsto_add_atTop_nat J₀))
    (fun J => ((hJ₀ (J + J₀) (Nat.le_add_left J₀ J)).trans ENNReal.one_lt_top).ne)
    fun _ => le_rfl

/-- **Change of chart for traces**: let `Ω₁`, `Ω₂` be Lipschitz graph domains and `F ∈ L_p(V)` with
a finite `B^{s+1/p}_{p,q}`-norm of order `L > s + 1/p`. For almost every `x' ∈ H₁` whose boundary
point `γ₁(x')` lies on the boundary of `Ω₂`, `Tr₁ F(x') = Tr₂ F(P₂ γ₁ x')`. -/
theorem trace_ae_eq_trace_comp (Ω₁ Ω₂ : LipschitzGraph V) (hp : p ≠ ∞) {L : ℕ} (hL : 1 ≤ L)
    {s : ℝ} (hs : 0 < s) (hsL : s + 1 / p.toReal < L) {q : ℝ≥0∞} (hq : 1 ≤ q)
    {F : Lp ℂ p (volume : Measure V)}
    (hF : ‖F‖ₑ + lqNorm q (fun k =>
      dyadicWeight (s + 1 / p.toReal) k * lpModulus p L F k) < ∞) :
    ∀ᵐ x' ∂(volume : Measure Ω₁.hyperplane),
      Ω₂.graphMap (Ω₂.proj (Ω₁.graphMap x')) = Ω₁.graphMap x' →
        Ω₁.trace hp L F x' = Ω₂.trace hp L F (Ω₂.proj (Ω₁.graphMap x')) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  set b := Ω₁.coneBump
  set g : ℕ → V → ℂ := fun J x => ∑ j ∈ Finset.range (J + 1),
    conv (b.dual L j) (b.localMean hp L j F) volume x
  have hGfin : ∀ J, ‖b.partialSum hp L J F‖ₑ + lqNorm q (fun k =>
      dyadicWeight (s + 1 / p.toReal) k * lpModulus p L (b.partialSum hp L J F) k) < ∞ :=
    fun J => b.modNorm_partialSum_lt_top hp L J (by positivity) hsL hq F
  have htr : ∀ (Ω' : LipschitzGraph V) J,
      Ω'.trace hp L (b.partialSum hp L J F) =ᵐ[volume] g J ∘ Ω'.graphMap := fun Ω' J =>
    Ω'.trace_ae_eq_comp_graphMap hp hL hs hq (Ω'.intrinsicNorm_lt_top_of_modNorm hp L hq
      (hGfin J)).1 (b.continuous_partialSum_rep hp L J F) (b.partialSum_ae hp L J F)
  obtain ⟨ns, hns, h2⟩ := (tendstoInMeasure_of_tendsto_eLpNorm hp0
    ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).1
      (Ω₂.tendsto_trace_partialSum b hp hL hs hsL hq hF))).exists_seq_tendsto_ae
  obtain ⟨ms, hms, h1⟩ := (tendstoInMeasure_of_tendsto_eLpNorm hp0
    ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).1
      ((Ω₁.tendsto_trace_partialSum b hp hL hs hsL hq hF).comp
        hns.tendsto_atTop))).exists_seq_tendsto_ae
  have hae2 : ∀ᵐ y' ∂(volume : Measure Ω₂.hyperplane), Tendsto (fun k =>
      g (ns (ms k)) (Ω₂.graphMap y')) atTop (𝓝 (Ω₂.trace hp L F y')) := by
    filter_upwards [h2, ae_all_iff.2 fun J => htr Ω₂ J] with y' hy hy'
    have h := hy.comp hms.tendsto_atTop
    refine h.congr fun k => ?_
    simp only [Function.comp_apply]
    exact hy' _
  have hae1 : ∀ᵐ x' ∂(volume : Measure Ω₁.hyperplane), Tendsto (fun k =>
      g (ns (ms k)) (Ω₁.graphMap x')) atTop (𝓝 (Ω₁.trace hp L F x')) := by
    filter_upwards [h1, ae_all_iff.2 fun J => htr Ω₁ J] with x' hx hx'
    refine hx.congr fun k => ?_
    simp only [Function.comp_apply]
    exact hx' _
  filter_upwards [hae1, Ω₁.ae_proj_graphMap Ω₂ hae2] with x' hx1 hx2 hA
  have h := hx2 hA
  rw [hA] at h
  exact tendsto_nhds_unique hx1 h

/-! ### Traces of products with smooth functions -/

/-- **Traces of products with smooth functions**: for smooth `ψ` with bounded derivatives up to
order `L` and `F` with a finite `B^{s+1/p}_{p,q}`-norm of order `L > s + 1/p`,
`Tr(ψ F) = (ψ ∘ γ) Tr F` almost everywhere: both are limits of the restrictions of the continuous
`ψ G_J` and `G_J`, and multiplication by `ψ` is bounded in `B^{1/p}_{p,1}`. -/
theorem trace_mulLp_ae (hp : p ≠ ∞) {L : ℕ} (hL : 1 ≤ L) {s : ℝ} (hs : 0 < s)
    (hsL : s + 1 / p.toReal < L) {q : ℝ≥0∞} (hq : 1 ≤ q) {ψ : V → ℂ}
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) {C : ℝ}
    (hC : ∀ l ≤ L, ∀ x, ‖iteratedFDeriv ℝ l ψ x‖ ≤ C) {F : Lp ℂ p (volume : Measure V)}
    (hF : ‖F‖ₑ + lqNorm q (fun k =>
      dyadicWeight (s + 1 / p.toReal) k * lpModulus p L F k) < ∞) :
    Ω.trace hp L (mulLp hψ.continuous (norm_le_of_iteratedFDeriv_le hC) F) =ᵐ[volume]
      fun x' => ψ (Ω.graphMap x') * Ω.trace hp L F x' := by
  have hp1 : 1 ≤ p := Fact.out
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  have hpr : 1 ≤ p.toReal := ENNReal.one_le_toReal_of_one_le hp1 hp
  have hpinv0 : 0 < 1 / p.toReal := by positivity
  have hpL : 1 / p.toReal < L := by linarith
  have hψC := norm_le_of_iteratedFDeriv_le hC
  set b := Ω.coneBump
  set G : ℕ → Lp ℂ p (volume : Measure V) := fun J => b.partialSum hp L J F
  set g : ℕ → V → ℂ := fun J x => ∑ j ∈ Finset.range (J + 1),
    conv (b.dual L j) (b.localMean hp L j F) volume x
  set M := ENNReal.ofReal C + ∑ l ∈ Finset.range (L + 1),
    (L.choose l : ℝ≥0∞) * ENNReal.ofReal C * multiplierConst (V := V) hp L (1 / p.toReal) l
  have hM : M ≠ ∞ := multiplierTotal_ne_top hp hpL C
  have hGfin : ∀ J, ‖G J‖ₑ + lqNorm q (fun k =>
      dyadicWeight (s + 1 / p.toReal) k * lpModulus p L (G J) k) < ∞ :=
    fun J => b.modNorm_partialSum_lt_top hp L J (by positivity) hsL hq F
  -- the products have finite intrinsic norms
  have hψfin : ∀ {H : Lp ℂ p (volume : Measure V)}, ‖H‖ₑ + lqNorm q (fun k =>
      dyadicWeight (s + 1 / p.toReal) k * lpModulus p L H k) < ∞ →
        Ω.intrinsicNorm hp L (s + 1 / p.toReal) q (mulLp hψ.continuous hψC H) < ∞ := fun hH =>
    (Ω.intrinsicNorm_lt_top_of_modNorm hp L hq (modNorm_mulLp_lt_top hp hψ hC hsL hq hH)).2
  -- convergence of the traces of the products, from some `J₀` on
  have happ := b.tendsto_modNorm_sub_partialSum hp hL hpinv0 (by linarith) hpL hq hF
  have hMb : Tendsto (fun J => M * (‖F - G J‖ₑ + lqNorm 1 (fun k =>
      dyadicWeight (1 / p.toReal) k * lpModulus p L (F - G J) k))) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul happ (Or.inr hM)
  obtain ⟨J₀, hJ₀⟩ := eventually_atTop.1
    (happ.eventually (gt_mem_nhds (zero_lt_one : (0 : ℝ≥0∞) < 1)))
  have hconvψ : Tendsto (fun J => Ω.trace hp L (mulLp hψ.continuous hψC (G J))) atTop
      (𝓝 (Ω.trace hp L (mulLp hψ.continuous hψC F))) := by
    rw [← tendsto_add_atTop_iff_nat J₀]
    refine Ω.tendsto_trace_of_modNorm_sub_le hp L hs hq (hψfin hF)
      (fun J => hψfin (hGfin (J + J₀))) (hMb.comp (tendsto_add_atTop_nat J₀))
      (fun J => ENNReal.mul_ne_top hM
        ((hJ₀ (J + J₀) (Nat.le_add_left J₀ J)).trans ENNReal.one_lt_top).ne) fun J => ?_
    rw [← mulLp_sub]
    exact modNorm_mulLp_le hp hψ hC hpL le_rfl (F - G (J + J₀))
  have hconv := Ω.tendsto_trace_partialSum b hp hL hs hsL hq hF
  -- the restrictions
  have htrψ : ∀ J, Ω.trace hp L (mulLp hψ.continuous hψC (G J)) =ᵐ[volume]
      (fun x => ψ x * g J x) ∘ Ω.graphMap := fun J =>
    Ω.trace_ae_eq_comp_graphMap hp hL hs hq (Ω.intrinsicNorm_lt_top_of_modNorm hp L hq
      (modNorm_mulLp_lt_top hp hψ hC hsL hq (hGfin J))).1
      (hψ.continuous.mul (b.continuous_partialSum_rep hp L J F))
      ((mulLp_apply_ae hψ.continuous hψC (G J)).trans
        ((b.partialSum_ae hp L J F).mono fun x hx => congrArg (ψ x * ·) hx))
  have htr : ∀ J, Ω.trace hp L (G J) =ᵐ[volume] g J ∘ Ω.graphMap := fun J =>
    Ω.trace_ae_eq_comp_graphMap hp hL hs hq (Ω.intrinsicNorm_lt_top_of_modNorm hp L hq
      (hGfin J)).1 (b.continuous_partialSum_rep hp L J F) (b.partialSum_ae hp L J F)
  -- subsequences converging almost everywhere
  obtain ⟨ns, hns, h1⟩ := (tendstoInMeasure_of_tendsto_eLpNorm hp0
    ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).1 hconvψ)).exists_seq_tendsto_ae
  obtain ⟨ms, hms, h2⟩ := (tendstoInMeasure_of_tendsto_eLpNorm hp0
    ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).1
      (hconv.comp hns.tendsto_atTop))).exists_seq_tendsto_ae
  filter_upwards [h1, h2, ae_all_iff.2 htrψ, ae_all_iff.2 htr] with x' hx1 hx2 hx3 hx4
  have hlim1 := hx1.comp hms.tendsto_atTop
  have hlim2 : Tendsto (fun k => ψ (Ω.graphMap x') *
      Ω.trace hp L (G (ns (ms k))) x') atTop (𝓝 (ψ (Ω.graphMap x') * Ω.trace hp L F x')) :=
    hx2.const_mul _
  refine tendsto_nhds_unique hlim1 (hlim2.congr fun k => ?_)
  simp only [Function.comp_apply]
  rw [hx3, hx4]
  rfl

/-- **The trace of a localised function is bounded**: for `1 ≤ p < ∞`, `0 < s < 1`, `1 ≤ q ≤ ∞`,
`s + 1/p < L` and a smooth `ψ` with derivatives bounded by `M` up to order `L`, there is `K < ∞`
with `‖Tr(ψ F)‖_p + ‖(2^(ks) ω_1(Tr(ψ F), 2^(-k))_p)_k‖_{ℓ_q} ≤
K (‖F‖_p + ‖(2^(k(s+1/p)) ω_L(F, 2^(-k))_p)_k‖_{ℓ_q})` for every `F ∈ L_p(V)` with a finite right
side: the trace bound by the intrinsic norm (`Rd.LipschitzGraph.modNorm_trace_le`), the intrinsic
norm by the norm on `V` (`Rd.LipschitzGraph.modNormOn_le_modNorm`) and the multiplier bound
(`Rd.modNorm_mulLp_le`). -/
theorem exists_modNorm_trace_mulLp_le (hp : p ≠ ∞) {L : ℕ} {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (hsL : s + 1 / p.toReal < L) {q : ℝ≥0∞} (hq : 1 ≤ q) {ψ : V → ℂ}
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) {M : ℝ}
    (hM : ∀ l ≤ L, ∀ x, ‖iteratedFDeriv ℝ l ψ x‖ ≤ M) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ F : Lp ℂ p (volume : Measure V), ‖F‖ₑ + lqNorm q (fun k =>
        dyadicWeight (s + 1 / p.toReal) k * lpModulus p L F k) < ∞ →
      ‖Ω.trace hp L (mulLp hψ.continuous (norm_le_of_iteratedFDeriv_le hM) F)‖ₑ +
          lqNorm q (fun k => dyadicWeight s k *
            lpModulus p 1 (Ω.trace hp L (mulLp hψ.continuous (norm_le_of_iteratedFDeriv_le hM) F))
              k) ≤
        K * (‖F‖ₑ + lqNorm q (fun k =>
          dyadicWeight (s + 1 / p.toReal) k * lpModulus p L F k)) := by
  obtain ⟨K, hK, hle⟩ := Ω.modNorm_trace_le hp L hs hs1 hq
  refine ⟨K * multiplierTotal (V := V) hp L (s + 1 / p.toReal) M,
    ENNReal.mul_ne_top hK (multiplierTotal_ne_top hp hsL M), fun F hF => ?_⟩
  have hX := (Ω.intrinsicNorm_lt_top_of_modNorm hp L hq
    (modNorm_mulLp_lt_top hp hψ hM hsL hq hF)).1
  rw [mul_assoc]
  exact (hle _ hX).trans (mul_le_mul' le_rfl ((Ω.modNormOn_le_modNorm L _ q rfl).trans
    (modNorm_mulLp_le hp hψ hM hsL hq F)))

/-! ### Finite sums -/

/-- The trace of `0` is `0`. -/
theorem trace_zero (hp : p ≠ ∞) (L : ℕ) : Ω.trace hp L 0 = 0 := by
  have h0 : ∀ j, Ω.traceTerm Ω.coneBump hp L j 0 = 0 := fun j => by
    simpa using Ω.traceTerm_sub Ω.coneBump hp L j 0 0
  simp only [trace, traceSeries, map_zero, h0, tsum_zero]

/-- The intrinsic quasi-norm of a sum is at most the sum of the intrinsic quasi-norms. -/
theorem intrinsicNorm_add_le (hp : p ≠ ∞) (L : ℕ) (σ : ℝ) {q : ℝ≥0∞} (hq : 1 ≤ q)
    (f₁ f₂ : Lp ℂ p (volume : Measure V)) :
    Ω.intrinsicNorm hp L σ q (f₁ + f₂) ≤
      Ω.intrinsicNorm hp L σ q f₁ + Ω.intrinsicNorm hp L σ q f₂ := by
  simp only [intrinsicNorm_def]
  refine (ENNReal.lqNorm_mono fun j => ?_).trans (ENNReal.lqNorm_add_le hq _ _)
  rw [map_add, map_add, ← mul_add]
  exact mul_le_mul' le_rfl (eNorm_add_le _ _)

/-- Finite sums of functions with finite intrinsic quasi-norms have finite intrinsic
quasi-norms. -/
theorem intrinsicNorm_finsetSum_lt_top (hp : p ≠ ∞) (L : ℕ) (σ : ℝ) {q : ℝ≥0∞} (hq : 1 ≤ q)
    {ι : Type*} (t : Finset ι) {F : ι → Lp ℂ p (volume : Measure V)}
    (hF : ∀ i ∈ t, Ω.intrinsicNorm hp L σ q (F i) < ∞) :
    Ω.intrinsicNorm hp L σ q (∑ i ∈ t, F i) < ∞ := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, intrinsicNorm_def, map_zero, eNorm_zero, mul_zero,
      ENNReal.lqNorm_zero_right]
    exact ENNReal.zero_lt_top
  | insert i t hi ih =>
    rw [Finset.sum_insert hi]
    exact (Ω.intrinsicNorm_add_le hp L σ hq _ _).trans_lt (ENNReal.add_lt_top.2
      ⟨hF i (Finset.mem_insert_self i t), ih fun j hj => hF j (Finset.mem_insert_of_mem hj)⟩)

/-- **The trace of a finite sum** is the sum of the traces, for summands with finite intrinsic
quasi-norms of smoothness `s + 1/p`. -/
theorem trace_finsetSum_of_intrinsicNorm (hp : p ≠ ∞) (L : ℕ) {s : ℝ} (hs : 0 < s)
    {q : ℝ≥0∞} (hq : 1 ≤ q) {ι : Type*} (t : Finset ι) {F : ι → Lp ℂ p (volume : Measure V)}
    (hF : ∀ i ∈ t, Ω.intrinsicNorm hp L (s + 1 / p.toReal) q (F i) < ∞) :
    Ω.trace hp L (∑ i ∈ t, F i) = ∑ i ∈ t, Ω.trace hp L (F i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Ω.trace_zero hp L]
  | insert i t hi ih =>
    have hS := Ω.intrinsicNorm_finsetSum_lt_top hp L _ hq t fun j hj =>
      hF j (Finset.mem_insert_of_mem hj)
    have hiS := Ω.intrinsicNorm_finsetSum_lt_top hp L _ hq (insert i t) hF
    rw [Finset.sum_insert hi] at hiS
    have h := Ω.trace_sub hp L hs hq hiS hS
    rw [add_sub_cancel_right] at h
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      ← ih fun j hj => hF j (Finset.mem_insert_of_mem hj), h, sub_add_cancel]

/-- **The trace of a finite sum** is the sum of the traces, for summands with finite
`B^{s+1/p}_{p,q}`-norms of order `L` on `V`: these have finite intrinsic quasi-norms
(`Rd.LipschitzGraph.intrinsicNorm_lt_top_of_modNorm`), so
`Rd.LipschitzGraph.trace_finsetSum_of_intrinsicNorm` applies. -/
theorem trace_finsetSum (hp : p ≠ ∞) (L : ℕ) {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞} (hq : 1 ≤ q)
    {ι : Type*} (t : Finset ι) {F : ι → Lp ℂ p (volume : Measure V)}
    (hF : ∀ i ∈ t, ‖F i‖ₑ + lqNorm q (fun k =>
      dyadicWeight (s + 1 / p.toReal) k * lpModulus p L (F i) k) < ∞) :
    Ω.trace hp L (∑ i ∈ t, F i) = ∑ i ∈ t, Ω.trace hp L (F i) :=
  Ω.trace_finsetSum_of_intrinsicNorm hp L hs hq t fun i hi =>
    (Ω.intrinsicNorm_lt_top_of_modNorm hp L hq (hF i hi)).2

end LipschitzGraph

end Rd
