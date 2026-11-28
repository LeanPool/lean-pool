/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Rd.Sobolev.CriticalSobolevEmbedding
public import TauCeti.Analysis.InnerProductSpace.Orthonormal.Multilinear
public import LeanPool.FunctionSpaces.Rd.Sobolev.WeakDerivativeChangeOfVariables
public import Mathlib.Analysis.FunctionalSpaces.SobolevInequality

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The Gagliardo–Nirenberg–Sobolev inequality

Let `V` have dimension `n ≥ 1`, `1 ≤ p`, and `1/p' = 1/p - 1/n`. Mathlib proves the
Gagliardo–Nirenberg–Sobolev inequality `‖u‖_{p'} ≤ C_{V,p} ‖Du‖_p` for compactly supported
`C^1` functions `u` (`MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq_inner`, constant
`MeasureTheory.eLpNormLESNormFDerivOfEqInnerConst`). This file carries it to weakly
differentiable functions by mollification, cut-off and Fatou's lemma
(`MeasureTheory.eLpNorm_le_of_ae_tendsto_of_tendsto`):

* **compact support** (`Rd.eLpNorm_le_of_hasCompactSupport_of_hasWeakLineDeriv`): for `h` with
  compact support and weak derivatives `g_k` along the orthonormal basis `e` of `Rd.gridBasis`,
  `‖h‖_{p'} ≤ C_{V,p} ∑_k ‖g_k‖_p`; the mollified `η_c ⋆ h`, `η = Rd.LocalMeansBump.std`,
  satisfy the bound by Young's inequality, with `D_{e_k}(η_c ⋆ h) = η_c ⋆ g_k`
  (`Rd.fderiv_conv_apply_eq_conv`), and converge to `h` in `L_1`, hence in measure;
* **the homogeneous inequality** (`Rd.eLpNorm_le_of_hasWeakLineDeriv`): the same bound for every
  `f ∈ L_p(V)` with weak derivatives along `e`, through the cut-offs `χ_R f`
  (`Rd.realCutoff`), whose weak derivatives differ from `χ_R g_k` by `O(1/R) |f|`;
* **`W^1_p ↪ L_r` for `1/r = 1/p - 1/n`** and every `1 ≤ p`, `p = 1` included
  (`Rd.exists_memLp_ae_eq_of_hasWeakLineDeriv_one`, `Rd.exists_memLp_ae_eq_of_memSobolev_one`),
  also with the exponents in the form `1/r + 1/n = 1/p`
  (`Rd.exists_memLp_ae_eq_of_memSobolev_one_of_inv_add_inv`);
* **`W^m_1 ↪ L_r` for `1/r = 1 - m/n`** (`Rd.exists_memLp_ae_eq_of_memSobolev_one_of_eq`): the
  derivatives of order below `m` lie in `L_{n/(n-1)}`, and the critical Sobolev embedding of
  `W^{m-1}_{n/(n-1)}` (`Rd.exists_memLp_ae_eq_of_memSobolev_of_eq`) applies.
-/

@[expose] public section

open MeasureTheory Filter Topology Module TopologicalSpace
open scoped ENNReal NNReal SchwartzMap LineDeriv

/-- **Fatou's lemma for `L_p` norms with convergent bounds**: if almost everywhere strongly
measurable `u_i` converge to `f` almost everywhere, `‖u_i‖_p ≤ B_i` for every `i` and `B_i → b`,
then `‖f‖_p ≤ b`. This extends Mathlib's `MeasureTheory.Lp.eLpNorm_le_of_ae_tendsto`, the case of
a constant bound, to convergent bounds. The proof is Mathlib's Fatou lemma
`MeasureTheory.Lp.eLpNorm_lim_le_liminf_eLpNorm`, with `f` measurable as an almost everywhere
limit (Mathlib's `aestronglyMeasurable_of_tendsto_ae`). -/
theorem MeasureTheory.eLpNorm_le_of_ae_tendsto_of_tendsto {α E : Type*} [MeasurableSpace α]
    {μ : Measure α} [NormedAddCommGroup E] {p : ℝ≥0∞} {u : ℕ → α → E} {f : α → E}
    (hu : ∀ i, AEStronglyMeasurable (u i) μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun i => u i x) atTop (𝓝 (f x))) {B : ℕ → ℝ≥0∞} {b : ℝ≥0∞}
    (hB : Tendsto B atTop (𝓝 b)) (hle : ∀ i, eLpNorm (u i) p μ ≤ B i) : eLpNorm f p μ ≤ b :=
  (Lp.eLpNorm_lim_le_liminf_eLpNorm hu f (aestronglyMeasurable_of_tendsto_ae atTop hu hlim)
    hlim).trans ((liminf_le_liminf (Eventually.of_forall hle)).trans_eq hB.liminf_eq)

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### Derivatives through a basis -/

omit [MeasurableSpace V] [BorelSpace V] in
/-- **The operator norm through the grid basis**: for a continuous linear map `L : V → F`,
`‖L‖ ≤ ∑_k ‖L e_k‖` for the orthonormal basis `e` of `Rd.gridBasis`
(`ContinuousLinearMap.opNorm_le_sum_norm_apply_orthonormalBasis`). -/
theorem norm_le_sum_norm_apply_gridBasis {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : V →L[ℝ] F) : ‖L‖ ≤ ∑ k, ‖L (gridBasis V k)‖ :=
  L.opNorm_le_sum_norm_apply_orthonormalBasis (gridBasis V)

/-- **The `L_p` norm of a derivative through a basis**: for a `C^1` function `u : V → ℂ` and
`1 ≤ p`, `‖Du‖_p ≤ ∑_k ‖D_{e_k} u‖_p` (`Rd.norm_le_sum_norm_apply_gridBasis` and Mathlib's
`MeasureTheory.eLpNorm_sum_le`). -/
theorem eLpNorm_fderiv_le_sum {u : V → ℂ} (hu : ContDiff ℝ 1 u) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (fderiv ℝ u) p volume ≤
      ∑ k, eLpNorm (fun x => fderiv ℝ u x (gridBasis V k)) p volume := by
  have hc : Continuous (fderiv ℝ u) := hu.continuous_fderiv one_ne_zero
  calc eLpNorm (fderiv ℝ u) p volume
      ≤ eLpNorm (∑ k, fun x => ‖fderiv ℝ u x (gridBasis V k)‖) p volume :=
        eLpNorm_mono_real hc.aestronglyMeasurable fun x => by
          rw [Finset.sum_apply]
          exact norm_le_sum_norm_apply_gridBasis _
    _ ≤ ∑ k, eLpNorm (fun x => ‖fderiv ℝ u x (gridBasis V k)‖) p volume := eLpNorm_sum_le hp
    _ = _ := Finset.sum_congr rfl fun k _ =>
        eLpNorm_norm _ (hc.clm_apply continuous_const).aestronglyMeasurable

/-! ### Functions with compact support -/

/-- **The Gagliardo–Nirenberg–Sobolev inequality for a mollification**: let `n ≥ 1`, `1 ≤ p`,
`1/p' = 1/p - 1/n`, `K` smooth with compact support, and `h` with compact support and weak
derivatives `g_k` along the orthonormal basis `e` of `Rd.gridBasis`. Then
`‖K ⋆ h‖_{p'} ≤ C_{V,p} ‖K‖_1 ∑_k ‖g_k‖_p`: Mathlib's inequality for the smooth function `K ⋆ h`
with compact support, `D_{e_k}(K ⋆ h) = K ⋆ g_k` (`Rd.fderiv_conv_apply_eq_conv`) and Young's
inequality (`Rd.eLpNorm_conv_le`). -/
theorem eLpNorm_conv_le_of_hasWeakLineDeriv {p p' : ℝ≥0} (hp : 1 ≤ p) (hn : 0 < finrank ℝ V)
    (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (finrank ℝ V : ℝ)⁻¹) {K : V → ℂ}
    (hK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) K) (hKs : HasCompactSupport K) {h : V → ℂ}
    (hc : HasCompactSupport h) {g : Fin (finrank ℝ V) → V → ℂ}
    (hhg : ∀ k, HasWeakLineDeriv ⊤ (fun _ : Fin 1 => gridBasis V k) h (g k)) :
    eLpNorm (conv K h volume) p' volume ≤
      eLpNormLESNormFDerivOfEqInnerConst (volume : Measure V) p *
        (eLpNorm K 1 volume * ∑ k, eLpNorm (g k) p volume) := by
  have hu := contDiff_conv hK hKs (hhg ⟨0, hn⟩).locallyIntegrable
  have hu1 : ContDiff ℝ 1 (conv K h volume) := hu.of_le (by exact_mod_cast le_top)
  have hus : HasCompactSupport (conv K h volume) :=
    hKs.convolution (L := ContinuousLinearMap.mul ℂ ℂ) (μ := volume) hc
  have hp1 : (1 : ℝ≥0∞) ≤ p := ENNReal.one_le_coe_iff.2 hp
  refine (eLpNorm_le_eLpNorm_fderiv_of_eq_inner volume hu1 hus hp hn hp').trans ?_
  gcongr
  refine (eLpNorm_fderiv_le_sum hu1 hp1).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  have he : (fun x => fderiv ℝ (conv K h volume) x (gridBasis V k)) = conv K (g k) volume :=
    funext fun x => fderiv_conv_apply_eq_conv hK hKs (hhg k) x
  rw [he]
  exact eLpNorm_conv_le hp1 hK.continuous.aestronglyMeasurable
    (hhg k).locallyIntegrable_deriv.aestronglyMeasurable

/-- **The Gagliardo–Nirenberg–Sobolev inequality with compact support**: let `n ≥ 1`, `1 ≤ p`,
`1/p' = 1/p - 1/n`, and let `h` have compact support and weak derivatives `g_k` along the
orthonormal basis `e` of `Rd.gridBasis`. Then `‖h‖_{p'} ≤ C_{V,p} ∑_k ‖g_k‖_p` with Mathlib's
constant `C_{V,p} = MeasureTheory.eLpNormLESNormFDerivOfEqInnerConst volume p`. The mollified
`η_c ⋆ h`, `η = Rd.LocalMeansBump.std`, satisfy the bound
(`Rd.eLpNorm_conv_le_of_hasWeakLineDeriv`, `Rd.LocalMeansBump.eLpNorm_std_one`); they converge to
the integrable `h` in `L_1` (`Rd.tendsto_eLpNorm_conv_dilate_sub`), hence in measure, and
Mathlib's `MeasureTheory.eLpNorm_le_of_tendstoInMeasure` passes the bound to `h`. -/
theorem eLpNorm_le_of_hasCompactSupport_of_hasWeakLineDeriv {p p' : ℝ≥0} (hp : 1 ≤ p)
    (hn : 0 < finrank ℝ V) (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (finrank ℝ V : ℝ)⁻¹) {h : V → ℂ}
    (hc : HasCompactSupport h) {g : Fin (finrank ℝ V) → V → ℂ}
    (hhg : ∀ k, HasWeakLineDeriv ⊤ (fun _ : Fin 1 => gridBasis V k) h (g k)) :
    eLpNorm h p' volume ≤
      eLpNormLESNormFDerivOfEqInnerConst (volume : Measure V) p * ∑ k, eLpNorm (g k) p volume := by
  have hloc := (hhg ⟨0, hn⟩).locallyIntegrable
  have hint : Integrable h volume := hloc.integrable_of_hasCompactSupport hc
  have hlim : Tendsto (fun i : ℕ => eLpNorm (conv (dilate ((i : ℝ) + 1)
      (LocalMeansBump.std (V := V)).toFun) h volume - h) 1 volume) atTop (𝓝 0) :=
    (tendsto_eLpNorm_conv_dilate_sub ENNReal.one_ne_top LocalMeansBump.std.integrable
      LocalMeansBump.std.integral_eq_one (memLp_one_iff_integrable.2 hint)).comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  refine eLpNorm_le_of_tendstoInMeasure (Eventually.of_forall fun i => ?_)
    (tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero hlim) fun i => ?_
  · have hci : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    have hbound := eLpNorm_conv_le_of_hasWeakLineDeriv hp hn hp'
      (contDiff_dilate LocalMeansBump.std.contDiff _)
      (hasCompactSupport_dilate LocalMeansBump.std.hasCompactSupport hci.ne') hc hhg
    rwa [eLpNorm_dilate_one LocalMeansBump.std.integrable hci, LocalMeansBump.eLpNorm_std_one,
      one_mul] at hbound
  · exact (contDiff_conv (contDiff_dilate LocalMeansBump.std.contDiff _)
      (hasCompactSupport_dilate LocalMeansBump.std.hasCompactSupport (by positivity))
      hloc).continuous.aestronglyMeasurable

/-! ### The cut-off -/

/-- The smooth bump around `0` with radii `1` and `2`, the bump of the cut-off `Rd.cutoff 1 2`. -/
noncomputable def cutoffBump : ContDiffBump (0 : V) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The **real cut-off** `χ_R(x) = b(x/R)` with the smooth bump `b = Rd.cutoffBump`, written
`b(R⁻¹ x)`: smooth, with values in `[0, 1]`, equal to `1` on `closedBall(0, R)` for `R > 0`. -/
noncomputable def realCutoff (R : ℝ) (x : V) : ℝ :=
  cutoffBump (V := V) (R⁻¹ • x)

omit [MeasurableSpace V] [BorelSpace V] in
/-- As a complex function, the real cut-off is the rescaled cut-off of the Littlewood–Paley
kernels: `χ_R(x) = Rd.cutoff 1 2 (R⁻¹ x)`. -/
theorem ofReal_realCutoff (R : ℝ) (x : V) :
    (realCutoff R x : ℂ) = cutoff 1 2 one_pos one_lt_two (R⁻¹ • x) :=
  rfl

omit [MeasurableSpace V] [BorelSpace V] in
/-- The cut-off `χ_R` is smooth. -/
theorem contDiff_realCutoff (R : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (realCutoff (V := V) R) :=
  (cutoffBump (V := V)).contDiff.comp (contDiff_const_smul R⁻¹)

omit [MeasurableSpace V] [BorelSpace V] in
/-- The cut-off `χ_R` has compact support for `R ≠ 0`. -/
theorem hasCompactSupport_realCutoff {R : ℝ} (hR : R ≠ 0) :
    HasCompactSupport (realCutoff (V := V) R) :=
  (cutoffBump (V := V)).hasCompactSupport.comp_homeomorph
    (Homeomorph.smulOfNeZero R⁻¹ (inv_ne_zero hR))

omit [MeasurableSpace V] [BorelSpace V] in
/-- The cut-off `χ_R` is `1` on `closedBall(0, R)`, `R > 0`. -/
theorem realCutoff_eq_one {R : ℝ} (hR : 0 < R) {x : V} (hx : ‖x‖ ≤ R) : realCutoff R x = 1 := by
  refine (cutoffBump (V := V)).one_of_mem_closedBall ?_
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hR.le)]
  change R⁻¹ * ‖x‖ ≤ 1
  rw [inv_mul_le_iff₀ hR, mul_one]
  exact hx

omit [MeasurableSpace V] [BorelSpace V] in
/-- The cut-off `χ_R` takes values in `[0, 1]`: `|χ_R(x)| ≤ 1`. -/
theorem abs_realCutoff_le_one (R : ℝ) (x : V) : |realCutoff R x| ≤ 1 := by
  unfold realCutoff
  rw [abs_of_nonneg (cutoffBump (V := V)).nonneg]
  exact (cutoffBump (V := V)).le_one

omit [MeasurableSpace V] [BorelSpace V] in
/-- **The derivative of the bump**: `|Db(y) w| ≤ sup ‖Db‖ ‖w‖`, with `sup ‖Db‖` the Schwartz
seminorm `p_{0,1}` of the cut-off `Rd.cutoffSchwartz 1 2`, whose real part is `b`. -/
theorem abs_fderiv_cutoffBump_le (y w : V) :
    |fderiv ℝ (cutoffBump (V := V)) y w| ≤
      SchwartzMap.seminorm ℝ 0 1 (cutoffSchwartz (V := V) 1 2 one_pos one_lt_two) * ‖w‖ := by
  have hc : HasFDerivAt (cutoff (V := V) 1 2 one_pos one_lt_two)
      (Complex.ofRealCLM.comp (fderiv ℝ (cutoffBump (V := V)) y)) y :=
    Complex.ofRealCLM.hasFDerivAt.comp y
      (((cutoffBump (V := V)).contDiff.differentiable (n := 1) one_ne_zero) y).hasFDerivAt
  calc |fderiv ℝ (cutoffBump (V := V)) y w|
      = ‖fderiv ℝ (cutoff (V := V) 1 2 one_pos one_lt_two) y w‖ := by
        rw [hc.fderiv, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, Complex.norm_real,
          Real.norm_eq_abs]
    _ ≤ ‖fderiv ℝ (cutoff (V := V) 1 2 one_pos one_lt_two) y‖ * ‖w‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ _ := by
        gcongr
        rw [← norm_iteratedFDeriv_one (𝕜 := ℝ)]
        exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ
          (cutoffSchwartz (V := V) 1 2 one_pos one_lt_two) 1 y

omit [MeasurableSpace V] [BorelSpace V] in
/-- **The derivative of the cut-off**: for `R > 0` and all `x`, `v`,
`|Dχ_R(x) v| ≤ sup ‖Db‖ R⁻¹ ‖v‖`, with `sup ‖Db‖` the Schwartz seminorm `p_{0,1}` of
`Rd.cutoffSchwartz 1 2`, since `Dχ_R(x) v = Db(x/R)(v/R)` (`Rd.abs_fderiv_cutoffBump_le`). -/
theorem abs_fderiv_realCutoff_le {R : ℝ} (hR : 0 < R) (x v : V) :
    |fderiv ℝ (realCutoff R) x v| ≤
      SchwartzMap.seminorm ℝ 0 1 (cutoffSchwartz (V := V) 1 2 one_pos one_lt_two) * R⁻¹ * ‖v‖ := by
  have hd : HasFDerivAt (realCutoff (V := V) R)
      ((fderiv ℝ (cutoffBump (V := V)) (R⁻¹ • x)).comp (R⁻¹ • ContinuousLinearMap.id ℝ V)) x :=
    (((cutoffBump (V := V)).contDiff.differentiable (n := 1) one_ne_zero) _).hasFDerivAt.comp x
      ((hasFDerivAt_id x).const_smul R⁻¹)
  rw [hd.fderiv, ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply]
  refine (abs_fderiv_cutoffBump_le _ _).trans_eq ?_
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hR.le), mul_assoc]

/-- **The weak derivatives of `χ_R f`**: if `|Dχ_R(x) v| ≤ M R⁻¹ ‖v‖` for all `x`, `v`, then
`‖χ_R g + (D_{e_k} χ_R) f‖_p ≤ ‖g‖_p + M R⁻¹ ‖f‖_p` for `1 ≤ p`, since `|χ_R| ≤ 1` and
`‖e_k‖ = 1`; for `g = ∂_{e_k} f` the left side is the weak derivative of `χ_R f`
(`Rd.HasWeakLineDeriv.mul_contDiff`). -/
theorem eLpNorm_realCutoff_mul_deriv_le {p : ℝ≥0∞} (hp : 1 ≤ p) {M R : ℝ}
    (hM : ∀ x v : V, |fderiv ℝ (realCutoff R) x v| ≤ M * R⁻¹ * ‖v‖) {f g : V → ℂ}
    (hf : AEStronglyMeasurable f volume) (hg : AEStronglyMeasurable g volume)
    (k : Fin (finrank ℝ V)) :
    eLpNorm (fun x => (realCutoff R x : ℂ) * g x +
        (fderiv ℝ (realCutoff R) x (gridBasis V k) : ℂ) * f x) p volume ≤
      eLpNorm g p volume + ENNReal.ofReal (M * R⁻¹) * eLpNorm f p volume := by
  have hχ := contDiff_realCutoff (V := V) R
  have h1 : AEStronglyMeasurable (fun x => (realCutoff R x : ℂ) * g x) volume :=
    (Complex.continuous_ofReal.comp hχ.continuous).aestronglyMeasurable.mul hg
  have h2 : AEStronglyMeasurable
      (fun x => (fderiv ℝ (realCutoff R) x (gridBasis V k) : ℂ) * f x) volume :=
    (Complex.continuous_ofReal.comp ((hχ.continuous_fderiv (by simp)).clm_apply
      continuous_const)).aestronglyMeasurable.mul hf
  refine (eLpNorm_add_le (f := fun x => (realCutoff R x : ℂ) * g x)
    (g := fun x => (fderiv ℝ (realCutoff R) x (gridBasis V k) : ℂ) * f x) hp).trans
    (add_le_add ?_ ?_)
  · refine eLpNorm_mono h1 fun x => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (abs_realCutoff_le_one R x)
  · refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul h2 (ae_of_all _ fun x => ?_) p
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_right ((hM x _).trans_eq ?_) (norm_nonneg _)
    rw [(gridBasis V).orthonormal.1 k, mul_one]

/-! ### The homogeneous Sobolev inequality -/

/-- **The Gagliardo–Nirenberg–Sobolev inequality on `W^1_p`** (Gagliardo 1958 and Nirenberg 1959,
independently, for `p = 1`; `1 < p < n` follows by applying it to `|u|^γ`): let `n ≥ 1`, `1 ≤ p`,
`1/p' = 1/p - 1/n`, and let `f ∈ L_p(V)` have weak derivatives `g_k` along the orthonormal
basis `e` of `Rd.gridBasis`. Then `‖f‖_{p'} ≤ C_{V,p} ∑_k ‖g_k‖_p` with Mathlib's constant
`C_{V,p} = MeasureTheory.eLpNormLESNormFDerivOfEqInnerConst volume p`. The cut-offs
`χ_R f`, `R = i + 1`, have compact support and weak derivatives `χ_R g_k + (D_{e_k} χ_R) f`
(`Rd.HasWeakLineDeriv.mul_contDiff`) with `L_p` norms at most `‖g_k‖_p + M R⁻¹ ‖f‖_p`, where
`M = sup ‖Db‖` (`Rd.abs_fderiv_realCutoff_le`, `Rd.eLpNorm_realCutoff_mul_deriv_le`); the case of
compact support (`Rd.eLpNorm_le_of_hasCompactSupport_of_hasWeakLineDeriv`) and Fatou's lemma
(`MeasureTheory.eLpNorm_le_of_ae_tendsto_of_tendsto`) along `χ_R f → f` give the bound. -/
theorem eLpNorm_le_of_hasWeakLineDeriv {p p' : ℝ≥0} (hp : 1 ≤ p) (hn : 0 < finrank ℝ V)
    (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (finrank ℝ V : ℝ)⁻¹) {f : V → ℂ} (hf : MemLp f p volume)
    {g : Fin (finrank ℝ V) → V → ℂ}
    (hfg : ∀ k, HasWeakLineDeriv ⊤ (fun _ : Fin 1 => gridBasis V k) f (g k)) :
    eLpNorm f p' volume ≤
      eLpNormLESNormFDerivOfEqInnerConst (volume : Measure V) p * ∑ k, eLpNorm (g k) p volume := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := ENNReal.one_le_coe_iff.2 hp
  have h0 : Tendsto (fun i : ℕ => ENNReal.ofReal
      (SchwartzMap.seminorm ℝ 0 1 (cutoffSchwartz (V := V) 1 2 one_pos one_lt_two) *
        ((i : ℝ) + 1)⁻¹)) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.tendsto_ofReal ?_
    simpa [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul
      (SchwartzMap.seminorm ℝ 0 1 (cutoffSchwartz (V := V) 1 2 one_pos one_lt_two))
  have hk : ∀ k, Tendsto (fun i : ℕ => eLpNorm (g k) p volume + ENNReal.ofReal
      (SchwartzMap.seminorm ℝ 0 1 (cutoffSchwartz (V := V) 1 2 one_pos one_lt_two) *
        ((i : ℝ) + 1)⁻¹) * eLpNorm f p volume) atTop (𝓝 (eLpNorm (g k) p volume)) := fun k => by
    have h := tendsto_const_nhds (x := eLpNorm (g k) p volume).add
      (ENNReal.Tendsto.mul_const h0 (Or.inr hf.eLpNorm_ne_top))
    rwa [zero_mul, add_zero] at h
  refine eLpNorm_le_of_ae_tendsto_of_tendsto
    (u := fun i x => (realCutoff ((i : ℝ) + 1) x : ℂ) * f x) (fun i => ?_)
    (ae_of_all _ fun x => ?_) (ENNReal.Tendsto.const_mul (tendsto_finsetSum _ fun k _ => hk k)
      (Or.inr ENNReal.coe_ne_top)) fun i => ?_
  · exact (Complex.continuous_ofReal.comp
      (contDiff_realCutoff _).continuous).aestronglyMeasurable.mul hf.aestronglyMeasurable
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ⌈‖x‖⌉₊] with i hi
    have hx : ‖x‖ ≤ (i : ℝ) + 1 := by
      have h1 := Nat.le_ceil ‖x‖
      have h2 : (⌈‖x‖⌉₊ : ℝ) ≤ i := by exact_mod_cast hi
      linarith
    rw [realCutoff_eq_one (by positivity) hx, Complex.ofReal_one, one_mul]
  · have hR : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    have hcs : HasCompactSupport fun x => (realCutoff ((i : ℝ) + 1) x : ℂ) * f x :=
      hasCompactSupport_cutoff_smul_mul i f
    refine (eLpNorm_le_of_hasCompactSupport_of_hasWeakLineDeriv hp hn hp' hcs
      fun k => (hfg k).mul_contDiff (contDiff_realCutoff _)).trans ?_
    gcongr with k
    exact eLpNorm_realCutoff_mul_deriv_le hp1 (abs_fderiv_realCutoff_le hR)
      hf.aestronglyMeasurable (hfg k).locallyIntegrable_deriv.aestronglyMeasurable k

/-! ### The Sobolev embedding of `W^1_p` -/

/-- **`W^1_p ↪ L_r` with Mathlib's constant** (Gagliardo 1958 and Nirenberg 1959, independently,
for `p = 1`; `1 < p < n` follows by applying it to `|u|^γ`): let `1 ≤ p`, `r < ∞` and
`n(1/p - 1/r) = 1`, so that `p < ∞` and `1/r = 1/p - 1/n`
(`toReal_inv_eq_of_nikolskiiExponent_eq_one`), and let `f ∈ L_p(V)` have weak derivatives
`g_k ∈ L_p(V)` along the orthonormal basis `e` of `Rd.gridBasis`. Then there is `u ∈ L_r(V)`
with `u = f` almost everywhere and `‖u‖_r ≤ C_{V,p} ∑_k ‖g_k‖_p`,
`C_{V,p} = MeasureTheory.eLpNormLESNormFDerivOfEqInnerConst volume p`
(`Rd.eLpNorm_le_of_hasWeakLineDeriv`). The order of the derivatives is `1`. -/
theorem exists_memLp_ae_eq_of_hasWeakLineDeriv_one {p r : ℝ≥0∞} [Fact (1 ≤ p)]
    (hr : r ≠ ∞) (hs : nikolskiiExponent (finrank ℝ V) p r = 1)
    {f : Lp ℂ p (volume : Measure V)} {g : Fin (finrank ℝ V) → Lp ℂ p (volume : Measure V)}
    (hfg : ∀ k, HasWeakLineDeriv ⊤ (fun _ : Fin 1 => gridBasis V k) f (g k)) :
    ∃ u : Lp ℂ r (volume : Measure V), (u : V → ℂ) =ᵐ[volume] f ∧
      ‖u‖ₑ ≤ eLpNormLESNormFDerivOfEqInnerConst (volume : Measure V) p.toReal * ∑ k, ‖g k‖ₑ := by
  obtain ⟨hn, hp, hinv⟩ := toReal_inv_eq_of_nikolskiiExponent_eq_one (Nat.cast_nonneg _) hs
  have hp1 : (1 : ℝ≥0) ≤ p.toNNReal := by
    have h := ENNReal.toNNReal_mono hp (Fact.out : 1 ≤ p)
    rwa [ENNReal.toNNReal_one] at h
  have hbound := eLpNorm_le_of_hasWeakLineDeriv (p' := r.toNNReal) hp1 (Nat.cast_pos.1 hn) hinv
    (by rw [ENNReal.coe_toNNReal hp]; exact Lp.memLp f) hfg
  rw [ENNReal.coe_toNNReal hp, ENNReal.coe_toNNReal hr, ENNReal.coe_toNNReal_eq_toReal] at hbound
  simp only [← Lp.eNorm_def] at hbound
  have hmem : MemLp (f : V → ℂ) r volume := memLp_iff.2 (hbound.trans_lt
    (ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.sum_lt_top.2 fun k _ => eNorm_lt_top)))
  exact ⟨hmem.toLp f, hmem.coeFn_toLp, by rw [Lp.eNorm_toLp]; exact hbound⟩

/-- **`W^1_p ↪ L_r` for `1/r = 1/p - 1/n`** (Gagliardo 1958 and Nirenberg 1959, independently,
for `p = 1`; `1 < p < n` follows by applying it to `|u|^γ`): for `1 ≤ p`, `r < ∞` and
`n(1/p - 1/r) = 1`, every `f ∈ W^1_p(V)`, of order `1`, has weak derivatives `G_k ∈ L_p(V)`
along the orthonormal basis `e` of `Rd.gridBasis` and a representative `u ∈ L_r(V)` with
`‖u‖_r ≤ C_{V,p} ∑_k ‖G_k‖_p` (`Rd.exists_memLp_ae_eq_of_hasWeakLineDeriv_one`). This includes
`p = 1`, where `W^1_1` is larger than `F^1_{1,2}`. -/
theorem exists_memLp_ae_eq_of_memSobolev_one {p r : ℝ≥0∞} [Fact (1 ≤ p)]
    (hr : r ≠ ∞) (hs : nikolskiiExponent (finrank ℝ V) p r = 1)
    {f : Lp ℂ p (volume : Measure V)} (hf : MemSobolev 1 f) :
    ∃ G : Fin (finrank ℝ V) → Lp ℂ p (volume : Measure V),
      (∀ k, HasWeakLineDeriv ⊤ (fun _ : Fin 1 => gridBasis V k) f (G k)) ∧
      ∃ u : Lp ℂ r (volume : Measure V), (u : V → ℂ) =ᵐ[volume] f ∧
        ‖u‖ₑ ≤ eLpNormLESNormFDerivOfEqInnerConst (volume : Measure V) p.toReal *
          ∑ k, ‖G k‖ₑ := by
  choose G hG using fun k : Fin (finrank ℝ V) =>
    (memSobolev_iff_exists_hasWeakLineDeriv f).1 hf 1 le_rfl (fun _ => gridBasis V k)
  exact ⟨G, hG, exists_memLp_ae_eq_of_hasWeakLineDeriv_one hr hs hG⟩

/-- **`W^1_p ↪ L_r` with the exponents `1/r + 1/n = 1/p`**, the form of TauCeti's
`W1p.eLpNorm_value_le_mul_enorm_gradient`: for `1 ≤ p`, `r < ∞` and `r⁻¹ + n⁻¹ = p⁻¹` in
`[0, ∞]`, every `f ∈ W^1_p(V)` has weak derivatives `G_k ∈ L_p(V)` along the orthonormal basis
of `Rd.gridBasis` and a representative `u ∈ L_r(V)` with `‖u‖_r ≤ C_{V,p} ∑_k ‖G_k‖_p`
(`nikolskiiExponent_eq_one_of_inv_add_inv`, `Rd.exists_memLp_ae_eq_of_memSobolev_one`). -/
theorem exists_memLp_ae_eq_of_memSobolev_one_of_inv_add_inv {p r : ℝ≥0∞} [Fact (1 ≤ p)]
    (hr : r ≠ ∞) (hexp : r⁻¹ + (finrank ℝ V : ℝ≥0∞)⁻¹ = p⁻¹)
    {f : Lp ℂ p (volume : Measure V)} (hf : MemSobolev 1 f) :
    ∃ G : Fin (finrank ℝ V) → Lp ℂ p (volume : Measure V),
      (∀ k, HasWeakLineDeriv ⊤ (fun _ : Fin 1 => gridBasis V k) f (G k)) ∧
      ∃ u : Lp ℂ r (volume : Measure V), (u : V → ℂ) =ᵐ[volume] f ∧
        ‖u‖ₑ ≤ eLpNormLESNormFDerivOfEqInnerConst (volume : Measure V) p.toReal *
          ∑ k, ‖G k‖ₑ :=
  exists_memLp_ae_eq_of_memSobolev_one hr (nikolskiiExponent_eq_one_of_inv_add_inv Fact.out hexp).2
    hf

/-! ### The Sobolev embedding of `W^m_1` -/

/-- **The derivatives of order below `m` of `f ∈ W^m_1` lie in `L_q` for `n(1 - 1/q) = 1`**:
for `f ∈ L_1(V)` in `W^m_1(V)`, every weak derivative `∂^v f ∈ L_1(V)` of order `k < m` has the
weak derivatives `∂^{(e_j, v)} f ∈ L_1(V)` along the orthonormal basis `e` of `Rd.gridBasis`
(`Rd.HasWeakLineDeriv.of_cons`), so it has a representative in `L_q(V)`
(`Rd.exists_memLp_ae_eq_of_hasWeakLineDeriv_one` with `p = 1`). -/
theorem exists_hasWeakLineDeriv_memLp_of_memSobolev_of_lt {m : ℕ}
    {f : Lp ℂ 1 (volume : Measure V)} (hf : MemSobolev m f) {q : ℝ≥0∞}
    (hq : q ≠ ∞) (hs : nikolskiiExponent (finrank ℝ V) 1 q = 1) {k : ℕ} (hk : k < m)
    (v : Fin k → V) : ∃ u : Lp ℂ q (volume : Measure V), HasWeakLineDeriv ⊤ v f u := by
  have hder := (memSobolev_iff_exists_hasWeakLineDeriv f).1 hf
  obtain ⟨G, hG⟩ := hder k hk.le v
  choose H hH using fun j : Fin (finrank ℝ V) => hder (k + 1) hk (Fin.cons (gridBasis V j) v)
  obtain ⟨u, hu, -⟩ := exists_memLp_ae_eq_of_hasWeakLineDeriv_one hq hs
    fun j => hG.of_cons (hH j)
  refine ⟨u, hG.congr_ae EventuallyEq.rfl ?_⟩
  rw [volume_restrict_top]
  exact hu.symm

/-- **`W^m_1 ↪ L_r` for `1/r = 1 - m/n`**, the integrability exponent being `p = 1` (Gagliardo
1958 and Nirenberg 1959): let `m ≥ 1`, `r < ∞` and `n(1 - 1/r) = m`. Every `f ∈ W^m_1(V)` has a
representative in `L_r(V)`. For `m = 1` this is `Rd.exists_memLp_ae_eq_of_memSobolev_one`; for
`m ≥ 2` and `q = n/(n - 1)` (`nikolskiiExponent_conjExponent_of_eq`), the derivatives of `f` of
order below `m` lie in `L_q` (`Rd.exists_hasWeakLineDeriv_memLp_of_memSobolev_of_lt`), so `f`
has a representative in `W^{m-1}_q(V)`, and the critical Sobolev embedding for `1 < q < ∞`
(`Rd.exists_memLp_ae_eq_of_memSobolev_of_eq`) applies. -/
theorem exists_memLp_ae_eq_of_memSobolev_one_of_eq {m : ℕ} (hm : 1 ≤ m) {r : ℝ≥0∞}
    (hr : r ≠ ∞) (hs : nikolskiiExponent (finrank ℝ V) 1 r = m)
    {f : Lp ℂ 1 (volume : Measure V)} (hf : MemSobolev m f) :
    ∃ g : Lp ℂ r (volume : Measure V), (g : V → ℂ) =ᵐ[volume] f := by
  rcases hm.eq_or_lt with rfl | hm2
  · obtain ⟨-, -, u, hu, -⟩ :=
      exists_memLp_ae_eq_of_memSobolev_one hr (by exact_mod_cast hs) hf
    exact ⟨u, hu⟩
  obtain ⟨hq1, hq, hq1s, hqr⟩ := nikolskiiExponent_conjExponent_of_eq hm2 hs
  generalize ENNReal.conjExponent (finrank ℝ V : ℝ≥0∞) = q at hq1 hq hq1s hqr
  have : Fact (1 ≤ q) := ⟨hq1.le⟩
  have : Nontrivial V := Module.nontrivial_of_finrank_pos
    (Nat.cast_pos.1 (toReal_inv_eq_of_nikolskiiExponent_eq_one (Nat.cast_nonneg _) hq1s).1)
  obtain ⟨f', hf'⟩ := exists_hasWeakLineDeriv_memLp_of_memSobolev_of_lt hf hq hq1s
    (by omega : 0 < m) Fin.elim0
  have hff' : (f' : V → ℂ) =ᵐ[volume] f := by
    have h := hf'.unique (hasWeakLineDeriv_fin_zero _ hf'.1)
    rwa [volume_restrict_top] at h
  have hS : MemSobolev (m - 1) f' := (memSobolev_iff_exists_hasWeakLineDeriv f').2 fun k hk v => by
    obtain ⟨u, hu⟩ := exists_hasWeakLineDeriv_memLp_of_memSobolev_of_lt hf hq hq1s
      (by omega : k < m) v
    refine ⟨u, hu.congr_ae ?_ EventuallyEq.rfl⟩
    rw [volume_restrict_top]
    exact hff'.symm
  obtain ⟨g, hg⟩ := exists_memLp_ae_eq_of_memSobolev_of_eq hq1 hq hr hqr hS
  exact ⟨g, hg.trans hff'⟩

end Rd
