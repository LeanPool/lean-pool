/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Rd.SingularIntegrals.ConvolutionAdjoint
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Weak derivatives under Lipschitz changes of variables, and cutoffs

Let `V` be a finite-dimensional real inner product space with Lebesgue measure and the
orthonormal basis `e_0, …, e_{n-1}` of `Rd.gridBasis`; the integrals of line derivatives hold for
every Haar measure on a finite-dimensional normed space, and the composition bounds for every
measure-preserving map between measure spaces.

* **Two general facts** (`MeasureTheory.LocallyIntegrable.integrable_of_hasCompactSupport`,
  `MeasureTheory.eLpNorm_mul_le_of_forall_norm_le`): locally integrable functions with compact
  support are integrable, and `‖c u‖_{L_p} ≤ C ‖u‖_{L_p}` for every multiplier `|c| ≤ C`.
* **Lipschitz functions** (`Rd.integral_lineDeriv_eq_zero_complex`,
  `Rd.hasWeakLineDeriv_of_lipschitzWith`): the line derivative of a compactly supported Lipschitz
  function integrates to zero, and the almost everywhere line derivative `∂_v f` of a Lipschitz
  function `f` is its weak derivative on every open set (Mathlib's integration by parts
  `LipschitzWith.integral_lineDeriv_mul_eq` and Rademacher's theorem). The classical derivative
  of a `C^1` function is its weak derivative (`Rd.hasWeakLineDeriv_of_contDiff`, Mathlib's
  `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`); in particular constants have weak
  gradient zero (`Rd.hasWeakLineDeriv_const`).
* **Directions** (`Rd.HasWeakLineDeriv.sum_smul_dir`, `Rd.hasWeakLineDeriv_of_forall_gridBasis`):
  weak derivatives are linear in the direction, so the derivatives `g_i = ∂_{e_i} f` give
  `∂_v f = ∑_i ⟪v, e_i⟫ g_i` for every `v`, and `W^1_p(V)` and `W^1_p(Ω)` need only the basis
  directions (`Rd.memSobolev_one_of_forall_gridBasis`, `Rd.memWeakSobolev_one_of_forall_gridBasis`).
* **Cutoffs**: the `L_p` bounds of the product rule with a cutoff of
  `FunctionSpaces.Rd.Sobolev.WeakDerivatives`: if the smooth `χ` has closed support in `B`, the
  `L_p(O)` norms of `χ g + (∂_w χ) f` and `χ f` are bounded by the `L_p(O ∩ B)` norms of `f`
  and `g` (`Rd.eLpNorm_mul_add_fderiv_mul_le`, `Rd.eLpNorm_mul_le_of_tsupport_subset`), on `V`
  in the norm `‖f‖_p + ∑_i ‖g_i‖_p` (`Rd.eLpNorm_mul_add_sum_le_of_tsupport_subset`); smooth
  cutoffs equal to `1` near a compact set exist (`Rd.exists_contDiff_eventuallyEq_one`), with
  bounded derivatives (`Rd.exists_norm_fderiv_gridBasis_le`).
* **Mollification on open sets** (`Rd.fderiv_conv_apply_eq_conv`,
  `Rd.exists_tendsto_contDiff_of_hasWeakLineDeriv`): mollification commutes with weak
  derivatives, and for every compact `K ⊆ O` smooth compactly supported `u_k` converge to `f`
  in `L_1(K)` with `∂_{w_i} u_k → ∂_{w_i} f` in `L_1(K)`, through a smooth cutoff equal to `1`
  near `K`.
* **The chain rule** (`Rd.HasWeakLineDeriv.comp_lipschitzWith`; local to global:
  `Rd.hasWeakLineDeriv_of_forall_isCompact`): for a Lipschitz map `Φ` that preserves Lebesgue
  measure and maps `U` into `O`, the derivatives `g_i = ∂_{e_i} f` on `O` give
  `∂_v (f ∘ Φ)(x) = ∑_i ⟪DΦ(x) v, e_i⟫ g_i(Φ x)` on `U`, with the `L_p` bounds
  `‖h ∘ Φ‖_{L_p(U)} ≤ ‖h‖_{L_p(O)}` (`Rd.eLpNorm_comp_le_of_mapsTo`) and, for `1 ≤ p`,
  `‖∑_i ⟪DΦ v, e_i⟫ h_i ∘ Φ‖_{L_p(U)} ≤ K ‖v‖ ∑_i ‖h_i‖_{L_p(O)}`
  (`Rd.eLpNorm_sum_inner_fderiv_mul_comp_le`).
-/

@[expose] public section

open MeasureTheory Filter Topology TopologicalSpace Module Set
open scoped ENNReal NNReal SchwartzMap LineDeriv Distributions

namespace MeasureTheory

/-- **Locally integrable functions with compact support are integrable**: such a function is
integrable on its compact closed support (Mathlib's `LocallyIntegrable.integrableOn_isCompact`) and
zero outside it, as for continuous functions in `Continuous.integrable_of_hasCompactSupport`. -/
theorem LocallyIntegrable.integrable_of_hasCompactSupport {X E : Type*} [TopologicalSpace X]
    [MeasurableSpace X] {μ : Measure X} [NormedAddCommGroup E] {f : X → E}
    (hf : LocallyIntegrable f μ) (hc : HasCompactSupport f) : Integrable f μ :=
  (integrableOn_iff_integrable_of_support_subset (subset_tsupport f)).1
    (hf.integrableOn_isCompact hc.isCompact)

/-- **Bounded multipliers on `L_p`**: if `c` is almost everywhere strongly measurable with
`‖c x‖ ≤ C` for every `x`, then `‖c u‖_{L_p(μ)} ≤ C ‖u‖_{L_p(μ)}` for every `u` and every
`0 ≤ p ≤ ∞`. For almost everywhere strongly measurable `u` this is Mathlib's
`eLpNorm_le_mul_eLpNorm_of_ae_le_mul'`; for the other `u`, `‖u‖_{L_p(μ)} = ∞`
(`eLpNorm_of_not_aestronglyMeasurable`), and for `C = 0` the product is `0`. -/
theorem eLpNorm_mul_le_of_forall_norm_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {c u : α → ℂ} (hc : AEStronglyMeasurable c μ) {C : ℝ≥0} (hC : ∀ x, ‖c x‖ ≤ C)
    (p : ℝ≥0∞) : eLpNorm (fun x => c x * u x) p μ ≤ C * eLpNorm u p μ := by
  by_cases hu : AEStronglyMeasurable u μ
  · refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul' (hc.mul hu) (ae_of_all _ fun x => ?_) p
    rw [Pi.mul_apply, eNorm_mul]
    gcongr
    exact eNorm_le_coe.2 (by rw [← NNReal.coe_le_coe, coe_nnNorm]; exact hC x)
  rcases eq_or_ne C 0 with rfl | hC0
  · have h0 : (fun x => c x * u x) = 0 := funext fun x => by
      have hx := hC x
      rw [NNReal.coe_zero, norm_le_zero_iff] at hx
      simp [hx]
    rw [h0, eLpNorm_zero]
    exact zero_le
  · rw [eLpNorm_of_not_aestronglyMeasurable hu, ENNReal.mul_top (ENNReal.coe_ne_zero.2 hC0)]
    exact le_top

end MeasureTheory

namespace Rd

/-! ### Integrals of line derivatives of Lipschitz functions -/

section LineDerivIntegral

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] {μ : Measure F} [μ.IsAddHaarMeasure] {C : ℝ≥0}

/-- **The line derivative of a compactly supported Lipschitz function integrates to zero**: for a
Lipschitz `f : F → ℝ` with compact support on a finite-dimensional space with a Haar measure,
`∫ ∂_v f = 0` for every direction `v`. This is Mathlib's integration by parts for Lipschitz
functions (`LipschitzWith.integral_lineDeriv_mul_eq`) against the constant `1`. -/
theorem integral_lineDeriv_eq_zero {f : F → ℝ} (hf : LipschitzWith C f)
    (hfc : HasCompactSupport f) (v : F) : ∫ x, lineDeriv ℝ f x v ∂μ = 0 := by
  have h := (LipschitzWith.const (1 : ℝ)).integral_lineDeriv_mul_eq (μ := μ) hf hfc (-v)
  simp only [neg_neg, mul_one] at h
  rw [← h]
  simp [lineDeriv]

/-- **The line derivative of a compactly supported Lipschitz function is integrable**: it is
measurable (Mathlib's `aestronglyMeasurable_lineDeriv`), bounded by `C ‖v‖`
(`norm_lineDeriv_le_of_lipschitz`) and zero outside the closed support of `f`. -/
theorem integrable_lineDeriv {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G] {f : F → G}
    (hf : LipschitzWith C f) (hfc : HasCompactSupport f) (v : F) :
    Integrable (fun x => lineDeriv ℝ f x v) μ := by
  refine IntegrableOn.integrable_of_forall_notMem_eq_zero (s := tsupport f)
    (Measure.integrableOn_of_bounded hfc.measure_lt_top.ne
      (aestronglyMeasurable_lineDeriv hf.continuous _)
      (ae_of_all _ fun _ => norm_lineDeriv_le_of_lipschitz ℝ hf)) fun x hx => ?_
  rw [((notMem_tsupport_iff_eventuallyEq).1 hx).lineDeriv_eq]
  simp [lineDeriv]

/-- **Real parts of line derivatives**: for a Lipschitz `f : F → ℂ`, almost everywhere the real
part of `∂_v f` is the line derivative of `Re f`, since `f` is differentiable almost everywhere
(Rademacher's theorem, Mathlib's `LipschitzWith.ae_differentiableAt`). -/
theorem ae_re_lineDeriv_eq {f : F → ℂ} (hf : LipschitzWith C f) (v : F) :
    ∀ᵐ x ∂μ, (lineDeriv ℝ f x v).re = lineDeriv ℝ (fun y => (f y).re) x v := by
  filter_upwards [hf.ae_differentiableAt] with x hx
  have h2 : HasFDerivAt (fun y => (f y).re) (Complex.reCLM.comp (fderiv ℝ f x)) x :=
    Complex.reCLM.hasFDerivAt.comp x hx.hasFDerivAt
  rw [hx.lineDeriv_eq_fderiv, h2.differentiableAt.lineDeriv_eq_fderiv, h2.fderiv]
  rfl

/-- **Imaginary parts of line derivatives**: for a Lipschitz `f : F → ℂ`, almost everywhere the
imaginary part of `∂_v f` is the line derivative of `Im f` (Rademacher's theorem). -/
theorem ae_im_lineDeriv_eq {f : F → ℂ} (hf : LipschitzWith C f) (v : F) :
    ∀ᵐ x ∂μ, (lineDeriv ℝ f x v).im = lineDeriv ℝ (fun y => (f y).im) x v := by
  filter_upwards [hf.ae_differentiableAt] with x hx
  have h2 : HasFDerivAt (fun y => (f y).im) (Complex.imCLM.comp (fderiv ℝ f x)) x :=
    Complex.imCLM.hasFDerivAt.comp x hx.hasFDerivAt
  rw [hx.lineDeriv_eq_fderiv, h2.differentiableAt.lineDeriv_eq_fderiv, h2.fderiv]
  rfl

/-- **The complex form**: for a compactly supported Lipschitz `f : F → ℂ`, `∫ ∂_v f = 0`. The
real and imaginary parts of `∂_v f` are almost everywhere the line derivatives of the real and
imaginary parts of `f` (`Rd.ae_re_lineDeriv_eq`, `Rd.ae_im_lineDeriv_eq`), whose integrals vanish
(`Rd.integral_lineDeriv_eq_zero`), and `∂_v f` is integrable (`Rd.integrable_lineDeriv`). -/
theorem integral_lineDeriv_eq_zero_complex {f : F → ℂ} (hf : LipschitzWith C f)
    (hfc : HasCompactSupport f) (v : F) : ∫ x, lineDeriv ℝ f x v ∂μ = 0 := by
  have h := integral_re_add_im (integrable_lineDeriv (μ := μ) hf hfc v)
  simp only [RCLike.re_to_complex, RCLike.im_to_complex, RCLike.I_to_complex] at h
  have h0re : ∫ x, lineDeriv ℝ (fun y => (f y).re) x v ∂μ = 0 :=
    integral_lineDeriv_eq_zero (Complex.reCLM.lipschitzWith.comp hf)
      (hfc.comp_left Complex.zero_re) v
  have h0im : ∫ x, lineDeriv ℝ (fun y => (f y).im) x v ∂μ = 0 :=
    integral_lineDeriv_eq_zero (Complex.imCLM.lipschitzWith.comp hf)
      (hfc.comp_left Complex.zero_im) v
  rw [← h, integral_congr_ae (ae_re_lineDeriv_eq hf v), integral_congr_ae (ae_im_lineDeriv_eq hf v),
    h0re, h0im]
  simp

end LineDerivIntegral

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### Lipschitz functions -/

section Lipschitz

/-- **Integration by parts for a Lipschitz function and a test function**: for a Lipschitz
`u : V → ℝ` and every test function `φ` on an open set, `∫ φ ∂_v u = -∫ (∂_v φ) u`, Mathlib's
`LipschitzWith.integral_lineDeriv_mul_eq` with the Lipschitz function `φ` of compact support
(`ContDiff.lipschitzWith_of_hasCompactSupport`). -/
theorem integral_testFunction_mul_lineDeriv {Ω : Opens V} {u : V → ℝ} {K : ℝ≥0}
    (hu : LipschitzWith K u) (φ : 𝓓(Ω, ℝ)) (v : V) :
    ∫ x, φ x * lineDeriv ℝ u x v = -∫ x, (∂_{v} φ) x * u x := by
  obtain ⟨D, hD⟩ := φ.contDiff.lipschitzWith_of_hasCompactSupport φ.hasCompactSupport (by simp)
  have h := hu.integral_lineDeriv_mul_eq (μ := volume) hD φ.hasCompactSupport v
  have hφ : ∀ x, lineDeriv ℝ φ x (-v) = -(∂_{v} φ) x := fun x => by
    rw [((φ.contDiff.differentiable (by simp)).differentiableAt).lineDeriv_eq_fderiv,
      lineDerivOp_testFunction_apply, map_neg]
  simp only [hφ, neg_mul, integral_neg] at h
  rw [← h]
  exact integral_congr_ae (ae_of_all _ fun x => mul_comm _ _)

/-- **Lipschitz functions are weakly differentiable**: for a Lipschitz `f : V → ℂ`, the almost
everywhere line derivative `∂_v f` (Mathlib's `lineDeriv`) is the weak derivative of `f` on every
open set, for every direction `v`. The real and imaginary parts are almost everywhere the line
derivatives of `Re f` and `Im f` (`Rd.ae_re_lineDeriv_eq`, `Rd.ae_im_lineDeriv_eq`), and
`Rd.integral_testFunction_mul_lineDeriv` integrates by parts. -/
theorem hasWeakLineDeriv_of_lipschitzWith {K : ℝ≥0} {f : V → ℂ} (hf : LipschitzWith K f)
    (Ω : Opens V) (v : V) :
    HasWeakLineDeriv Ω (fun _ : Fin 1 => v) f (fun x => lineDeriv ℝ f x v) := by
  have hfl : LocallyIntegrable f volume := hf.continuous.locallyIntegrable
  have hgl : LocallyIntegrable (fun x => lineDeriv ℝ f x v) volume :=
    (memLp_top_of_bound (aestronglyMeasurable_lineDeriv hf.continuous _) (K * ‖v‖)
      (ae_of_all _ fun _ => norm_lineDeriv_le_of_lipschitz ℝ hf)).locallyIntegrable le_top
  refine (hasWeakLineDeriv_iff_integral (hfl.locallyIntegrableOn _)
    (hgl.locallyIntegrableOn _)).2 fun φ => ?_
  rw [LineDeriv.iteratedLineDerivOp_one]
  have i1 := φ.integrable_smul (hgl.locallyIntegrableOn (Ω : Set V))
  have i2 := (∂_{v} φ).integrable_smul (hfl.locallyIntegrableOn (Ω : Set V))
  have hre : ∫ x, φ x * lineDeriv ℝ (fun y => (f y).re) x v = -∫ x, (∂_{v} φ) x * (f x).re :=
    integral_testFunction_mul_lineDeriv (Complex.reCLM.lipschitzWith.comp hf) φ v
  have him : ∫ x, φ x * lineDeriv ℝ (fun y => (f y).im) x v = -∫ x, (∂_{v} φ) x * (f x).im :=
    integral_testFunction_mul_lineDeriv (Complex.imCLM.lipschitzWith.comp hf) φ v
  apply Complex.ext
  · have h1 := integral_re i1
    have h2 := integral_re i2
    simp only [RCLike.re_to_complex, Complex.smul_re, smul_eq_mul] at h1 h2
    rw [← h1, integral_congr_ae ((ae_re_lineDeriv_eq hf v).mono fun x hx => by rw [hx]), hre,
      pow_one, neg_one_smul, Complex.neg_re, ← h2]
  · have h1 := integral_im i1
    have h2 := integral_im i2
    simp only [RCLike.im_to_complex, Complex.smul_im, smul_eq_mul] at h1 h2
    rw [← h1, integral_congr_ae ((ae_im_lineDeriv_eq hf v).mono fun x hx => by rw [hx]), him,
      pow_one, neg_one_smul, Complex.neg_im, ← h2]

/-- **Classical derivatives are weak derivatives**: for a `C^1` function `F` on `V`, the
classical directional derivative `x ↦ DF(x) w` is the weak derivative `∂_w F` on every open set
`Ω`. This is integration by parts against compactly supported test functions (Mathlib's
`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`). -/
theorem hasWeakLineDeriv_of_contDiff {F : V → ℂ} (hF : ContDiff ℝ 1 F) (Ω : Opens V) (w : V) :
    HasWeakLineDeriv Ω (fun _ : Fin 1 => w) F (fun x => fderiv ℝ F x w) := by
  have hc : Continuous F := hF.continuous
  have hd : Continuous fun x => fderiv ℝ F x w :=
    (hF.continuous_fderiv one_ne_zero).clm_apply continuous_const
  refine (hasWeakLineDeriv_iff_integral (hc.locallyIntegrable.locallyIntegrableOn _)
    (hd.locallyIntegrable.locallyIntegrableOn _)).2 fun φ => ?_
  have hi : ∀ (ψ : 𝓓(Ω, ℝ)) {u : V → ℂ}, Continuous u →
      Integrable (fun x => (testSchwartz ψ) x * u x) volume := fun ψ u hu => by
    simpa only [testSchwartz_apply, Complex.real_smul] using
      ψ.integrable_smul (hu.locallyIntegrable.locallyIntegrableOn _)
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (f := testSchwartz φ) (g := F)
    (v := w) (by simpa only [fderiv_testSchwartz_apply, testSchwartz_apply] using hi (∂_{w} φ) hc)
    (hi φ hd) (hi φ hc) (fun x _ => (testSchwartz φ).differentiableAt)
    (fun x _ => (hF.differentiable one_ne_zero).differentiableAt)
  simp only [fderiv_testSchwartz_apply, testSchwartz_apply] at h
  rw [LineDeriv.iteratedLineDerivOp_one, pow_one, neg_one_smul]
  simpa only [Complex.real_smul] using h

/-- **Constants have weak gradient zero**: on every open set `O`, the constant function `c` has
the weak derivative `0` in every direction `w` (`Rd.hasWeakLineDeriv_of_contDiff`). -/
theorem hasWeakLineDeriv_const (O : Opens V) (w : V) (c : ℂ) :
    HasWeakLineDeriv O (fun _ : Fin 1 => w) (fun _ => c) 0 := by
  have h := hasWeakLineDeriv_of_contDiff (contDiff_const (c := c)) O w
  have h0 : (fun x => fderiv ℝ (fun _ : V => c) x w) = 0 := funext fun x => by simp
  rwa [h0] at h

end Lipschitz

/-! ### Directions -/

section Directions

variable {Ω : Opens V} {f : V → ℂ}

/-- Finite sums of locally integrable functions on `Ω` with coefficients in a normed field `𝕜`
acting on `ℂ`, such as `ℝ` or `ℂ`, are locally integrable on `Ω`, by induction over the sum as in
Mathlib's `locallyIntegrable_finsetSum'`. -/
theorem locallyIntegrableOn_sum_smul {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 ℂ] {ι : Type*}
    (s : Finset ι) (c : ι → 𝕜) {g : ι → V → ℂ}
    (hg : ∀ i ∈ s, LocallyIntegrableOn (g i) Ω volume) :
    LocallyIntegrableOn (∑ i ∈ s, c i • g i) Ω volume :=
  Finset.sum_induction (fun i => c i • g i)
    (fun u : V → ℂ => LocallyIntegrableOn u (Ω : Set V) volume)
    (fun _ _ => LocallyIntegrableOn.add) locallyIntegrableOn_zero fun i hi => (hg i hi).smul (c i)

/-- **Weak derivatives are linear in the direction**: if `g_i = ∂_{v_i} f` weakly on `Ω` for every
`i ∈ s`, `s` finite, and `f` is locally integrable on `Ω`, then for all real `c_i`,
`∑_i c_i g_i = ∂_v f` weakly on `Ω` for `v = ∑_i c_i v_i`. Tested against `φ`, this is the
linearity of `w ↦ ∂_w φ = Dφ(·) w` (`Rd.lineDerivOp_testFunction_apply`). -/
theorem HasWeakLineDeriv.sum_smul_dir {ι : Type*} (s : Finset ι) {v : ι → V} (c : ι → ℝ)
    {g : ι → V → ℂ} (hf : LocallyIntegrableOn f Ω volume)
    (h : ∀ i ∈ s, HasWeakLineDeriv Ω (fun _ : Fin 1 => v i) f (g i)) :
    HasWeakLineDeriv Ω (fun _ : Fin 1 => ∑ i ∈ s, c i • v i) f (∑ i ∈ s, (c i : ℂ) • g i) := by
  refine (hasWeakLineDeriv_iff_integral hf
    (locallyIntegrableOn_sum_smul s (fun i => (c i : ℂ)) fun i hi => (h i hi).2)).2 fun φ => ?_
  have hL : ∀ x, (∂^{fun _ : Fin 1 => ∑ i ∈ s, c i • v i} φ) x =
      ∑ i ∈ s, c i * (∂^{fun _ : Fin 1 => v i} φ) x := fun x => by
    simp only [LineDeriv.iteratedLineDerivOp_one, lineDerivOp_testFunction_apply, map_sum,
      map_smul, smul_eq_mul]
  have e1 : (fun x => φ x • (∑ i ∈ s, (c i : ℂ) • g i) x) =
      fun x => ∑ i ∈ s, (c i : ℂ) * (φ x • g i x) := funext fun x => by
    rw [Finset.sum_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, Complex.real_smul]
    ring
  have e2 : (fun x => (∂^{fun _ : Fin 1 => ∑ i ∈ s, c i • v i} φ) x • f x) =
      fun x => ∑ i ∈ s, (c i : ℂ) * ((∂^{fun _ : Fin 1 => v i} φ) x • f x) := funext fun x => by
    rw [hL, Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Complex.real_smul, Complex.ofReal_mul]
    ring
  rw [e1, e2, integral_finsetSum _ fun i hi => (φ.integrable_smul (h i hi).2).const_mul _,
    integral_finsetSum _ fun i _ => ((∂^{fun _ : Fin 1 => v i} φ).integrable_smul hf).const_mul _,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [integral_const_mul, integral_const_mul, (h i hi).integral_eq φ]
  simp only [Complex.real_smul]
  ring

/-- **Local integrability from the basis derivatives**: if `f` has weak derivatives `g_i` along
the basis vectors `e_i` on `Ω`, then `f` is locally integrable on `Ω`; in dimension `0` every
function on `V` is constant, hence continuous. -/
theorem locallyIntegrableOn_of_forall_gridBasis {g : Fin (finrank ℝ V) → V → ℂ}
    (h : ∀ i, HasWeakLineDeriv Ω (fun _ : Fin 1 => gridBasis V i) f (g i)) :
    LocallyIntegrableOn f Ω volume := by
  rcases (finrank ℝ V).eq_zero_or_pos with h0 | h0
  · have : Subsingleton V := Module.finrank_zero_iff.1 h0
    have hc : Continuous f := by
      have hf : f = fun _ => f 0 := funext fun x => congrArg f (Subsingleton.elim x 0)
      rw [hf]
      exact continuous_const
    exact hc.locallyIntegrable.locallyIntegrableOn _
  · exact (h ⟨0, h0⟩).locallyIntegrableOn

/-- **All directions from the basis**: if `g_i = ∂_{e_i} f` weakly on `Ω` for the basis vectors
`e_i` of `Rd.gridBasis`, then `∑_i ⟪v, e_i⟫ g_i = ∂_v f` weakly on `Ω` for every `v ∈ V`
(`Rd.HasWeakLineDeriv.sum_smul_dir` with `v = ∑_i ⟪v, e_i⟫ e_i`, Mathlib's
`OrthonormalBasis.sum_repr'`). -/
theorem hasWeakLineDeriv_of_forall_gridBasis {g : Fin (finrank ℝ V) → V → ℂ}
    (h : ∀ i, HasWeakLineDeriv Ω (fun _ : Fin 1 => gridBasis V i) f (g i)) (v : V) :
    HasWeakLineDeriv Ω (fun _ : Fin 1 => v) f
      (fun x => ∑ i, (inner ℝ v (gridBasis V i) : ℂ) * g i x) := by
  have h' := HasWeakLineDeriv.sum_smul_dir Finset.univ (fun i => inner ℝ v (gridBasis V i))
    (locallyIntegrableOn_of_forall_gridBasis h) fun i _ => h i
  have hv : ∑ i, inner ℝ v (gridBasis V i) • gridBasis V i = v := by
    simpa only [real_inner_comm] using (gridBasis V).sum_repr' v
  rw [hv] at h'
  convert h' using 1
  funext x
  simp [Finset.sum_apply]

/-- **`W^1_p(V)` from the basis derivatives**: a function `F ∈ L_p(V)`, `1 ≤ p`, with weak
derivatives `G_i ∈ L_p(V)` along the basis vectors `e_i` on `V` lies in `W^1_p(V)`; the
derivative along `v` is the class of `∑_i ⟪v, e_i⟫ G_i`
(`Rd.hasWeakLineDeriv_of_forall_gridBasis`, `Rd.memSobolev_one_of_forall_hasWeakLineDeriv`). -/
theorem memSobolev_one_of_forall_gridBasis {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {F : Lp ℂ p (volume : Measure V)} {G : Fin (finrank ℝ V) → Lp ℂ p (volume : Measure V)}
    (h : ∀ i, HasWeakLineDeriv ⊤ (fun _ : Fin 1 => gridBasis V i) F (G i)) : MemSobolev 1 F := by
  refine memSobolev_one_of_forall_hasWeakLineDeriv fun v => ?_
  have hm : MemLp (fun x => ∑ i, (inner ℝ v (gridBasis V i) : ℂ) * G i x) p volume :=
    memLp_finsetSum Finset.univ fun i _ => (Lp.memLp (G i)).const_mul _
  refine ⟨hm.toLp _, (hasWeakLineDeriv_of_forall_gridBasis h v).congr_ae EventuallyEq.rfl ?_⟩
  rw [volume_restrict_top]
  exact hm.coeFn_toLp.symm

/-- **`W^1_p(Ω)` from the basis derivatives**: on an open set `Ω`, for `1 ≤ p`, a function
`f ∈ L_p(Ω)` with weak derivatives `g_i = ∂_{e_i} f ∈ L_p(Ω)` along the basis vectors
`e_i = Rd.gridBasis V i` lies in `W^1_p(Ω)`; the derivative along `v` is
`∑_i ⟪v, e_i⟫ g_i` (`Rd.hasWeakLineDeriv_of_forall_gridBasis`), and the derivative of order zero
is `f` itself. -/
theorem memWeakSobolev_one_of_forall_gridBasis {p : ℝ≥0∞} (hp : 1 ≤ p)
    {g : Fin (finrank ℝ V) → V → ℂ} (hf : MemLp f p (volume.restrict Ω))
    (hg : ∀ i, MemLp (g i) p (volume.restrict Ω))
    (h : ∀ i, HasWeakLineDeriv Ω (fun _ : Fin 1 => gridBasis V i) f (g i)) :
    MemWeakSobolev Ω 1 p f := by
  refine ⟨hf, fun k hk v => ?_⟩
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hk with rfl | rfl
  · exact ⟨f, hf, hasWeakLineDeriv_fin_zero v (locallyIntegrableOn_of_memLp hp hf)⟩
  have hv : v = fun _ => v 0 := funext fun i => congrArg v (Subsingleton.elim i 0)
  rw [hv]
  refine ⟨fun x => ∑ i, (inner ℝ (v 0) (gridBasis V i) : ℂ) * g i x, ?_,
    hasWeakLineDeriv_of_forall_gridBasis h (v 0)⟩
  exact memLp_finsetSum Finset.univ fun i _ => (hg i).const_mul _

end Directions

/-! ### Cutoffs -/

section Cutoff

variable {O B : Opens V}

/-- **Restriction to the support**: if `h` vanishes outside the open set `B`, then its `L_p` norm
on `O` is its `L_p` norm on `O ∩ B`, for every `0 ≤ p ≤ ∞` (Mathlib's
`eLpNorm_indicator_eq_eLpNorm_restrict`). -/
theorem eLpNorm_restrict_eq_inf_of_support_subset {E : Type*} [NormedAddCommGroup E] {h : V → E}
    (hB : Function.support h ⊆ B) (p : ℝ≥0∞) :
    eLpNorm h p (volume.restrict O) = eLpNorm h p (volume.restrict (O ⊓ B : Opens V)) := by
  conv_lhs => rw [← indicator_eq_self.2 hB]
  rw [eLpNorm_indicator_eq_eLpNorm_restrict B.isOpen.measurableSet.nullMeasurableSet,
    Measure.restrict_restrict B.isOpen.measurableSet, Opens.coe_inf, inter_comm]

/-- **The `L_p` bound for a cutoff derivative**: if `χ` has closed support in `B`, `|χ| ≤ C` and
`|∂_w χ| ≤ C'`, then `‖χ g + (∂_w χ) f‖_{L_p(O)} ≤ C ‖g‖_{L_p(O ∩ B)} + C' ‖f‖_{L_p(O ∩ B)}` for
all `f`, `g` and `1 ≤ p`: the function vanishes outside `B`, and each term is bounded by
`MeasureTheory.eLpNorm_mul_le_of_forall_norm_le`. -/
theorem eLpNorm_mul_add_fderiv_mul_le {p : ℝ≥0∞} (hp : 1 ≤ p) {w : V} {f g : V → ℂ} {χ : V → ℝ}
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (hχB : tsupport χ ⊆ B) {C C' : ℝ≥0}
    (hC : ∀ x, ‖χ x‖ ≤ C) (hC' : ∀ x, ‖fderiv ℝ χ x w‖ ≤ C') :
    eLpNorm (fun x => (χ x : ℂ) * g x + (fderiv ℝ χ x w : ℂ) * f x) p (volume.restrict O) ≤
      C * eLpNorm g p (volume.restrict (O ⊓ B : Opens V)) +
        C' * eLpNorm f p (volume.restrict (O ⊓ B : Opens V)) := by
  have hc : Continuous fun x => (χ x : ℂ) := Complex.continuous_ofReal.comp hχ.continuous
  have hχ' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun x => fderiv ℝ χ x w :=
    (hχ.fderiv_right (by simp)).clm_apply contDiff_const
  have hc' : Continuous fun x => (fderiv ℝ χ x w : ℂ) :=
    Complex.continuous_ofReal.comp hχ'.continuous
  have hsupp : (Function.support fun x => (χ x : ℂ) * g x + (fderiv ℝ χ x w : ℂ) * f x) ⊆ B := by
    intro x hx
    by_contra hxB
    have h0 : χ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.1 fun h => hxB (hχB h)
    exact hx (by simp [h0.eq_of_nhds, h0.fderiv_eq])
  rw [eLpNorm_restrict_eq_inf_of_support_subset hsupp]
  exact (eLpNorm_add_le hp).trans (add_le_add
    (eLpNorm_mul_le_of_forall_norm_le hc.aestronglyMeasurable
      (fun x => by rw [Complex.norm_real]; exact hC x) p)
    (eLpNorm_mul_le_of_forall_norm_le hc'.aestronglyMeasurable
      (fun x => by rw [Complex.norm_real]; exact hC' x) p))

/-- **Cutoffs in `L_p`**: if `χ` is continuous with closed support in `B` and `|χ| ≤ C`, then
`‖χ f‖_{L_p(O)} ≤ C ‖f‖_{L_p(O ∩ B)}` for every `f` and every `0 ≤ p ≤ ∞`: the product vanishes
outside `B` (`Rd.eLpNorm_restrict_eq_inf_of_support_subset`), and
`MeasureTheory.eLpNorm_mul_le_of_forall_norm_le` bounds it. -/
theorem eLpNorm_mul_le_of_tsupport_subset {p : ℝ≥0∞} {f : V → ℂ} {χ : V → ℝ}
    (hχ : Continuous χ) (hχB : tsupport χ ⊆ B) {C : ℝ≥0} (hC : ∀ x, ‖χ x‖ ≤ C) :
    eLpNorm (fun x => (χ x : ℂ) * f x) p (volume.restrict O) ≤
      C * eLpNorm f p (volume.restrict (O ⊓ B : Opens V)) := by
  have hsupp : (Function.support fun x => (χ x : ℂ) * f x) ⊆ B := fun x hx =>
    hχB (subset_tsupport _ (Function.mem_support.2
      (Complex.ofReal_ne_zero.1 (left_ne_zero_of_mul (Function.mem_support.1 hx)))))
  rw [eLpNorm_restrict_eq_inf_of_support_subset hsupp]
  have hc : Continuous fun x => (χ x : ℂ) := Complex.continuous_ofReal.comp hχ
  exact eLpNorm_mul_le_of_forall_norm_le hc.aestronglyMeasurable
    (fun x => by rw [Complex.norm_real]; exact hC x) p

omit [MeasurableSpace V] [BorelSpace V] in
/-- **Smooth cutoffs**: for a compact `K` inside an open set `U` there is a smooth
`χ : V → [0, 1]` with compact closed support in `U` and `χ = 1` on a neighbourhood of `K`
(Mathlib's `exists_compact_between`, `exists_open_between_and_isCompact_closure` and
`exists_contDiff_support_eq_eq_one_iff`). -/
theorem exists_contDiff_eventuallyEq_one {K U : Set V} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ χ : V → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧
      (∀ x, χ x ∈ Icc (0 : ℝ) 1) ∧ ∀ᶠ x in 𝓝ˢ K, χ x = 1 := by
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨W, hW, hLW, hWU, hWc⟩ := exists_open_between_and_isCompact_closure hL hU hLU
  obtain ⟨χ, hχ, hrange, hsupp, h1⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hW hL.isClosed hLW
  refine ⟨χ, hχ, ?_, ?_, fun x => hrange ⟨x, rfl⟩, ?_⟩
  · rw [HasCompactSupport, tsupport, hsupp]
    exact hWc
  · rw [tsupport, hsupp]
    exact hWU
  · exact eventually_of_mem (isOpen_interior.mem_nhdsSet.2 hKL) fun x hx =>
      (h1 x).1 (interior_subset hx)

omit [MeasurableSpace V] [BorelSpace V] in
/-- **Bounded derivatives of a cutoff**: a smooth `χ` with compact support has
`|∂_{e_i} χ| ≤ d_i` for constants `d_i ≥ 0` (Mathlib's
`Continuous.bounded_above_of_compact_support`). -/
theorem exists_norm_fderiv_gridBasis_le {χ : V → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hχc : HasCompactSupport χ) :
    ∃ d : Fin (finrank ℝ V) → ℝ≥0, ∀ i x, ‖fderiv ℝ χ x (gridBasis V i)‖ ≤ d i := by
  choose d hd using fun i => ((hχ.continuous_fderiv (by simp)).clm_apply
    continuous_const).bounded_above_of_compact_support (hχc.fderiv_apply (𝕜 := ℝ) (gridBasis V i))
  exact ⟨fun i => (d i).toNNReal, fun i x => (hd i x).trans (Real.le_coe_toNNReal _)⟩

/-- A real function with values in `[0, 1]`, such as the cutoffs of
`Rd.exists_contDiff_eventuallyEq_one`, has norm at most `1`. -/
theorem norm_le_one_of_forall_mem_Icc {α : Type*} {χ : α → ℝ} (h : ∀ x, χ x ∈ Icc (0 : ℝ) 1)
    (x : α) : ‖χ x‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (h x).1]
  exact (h x).2

/-- **The bound of a cutoff on `V`**: for `1 ≤ p`, an open `O`, a smooth `χ` with values in
`[0, 1]`, closed support in `O` and `|∂_{e_i} χ| ≤ d_i`, and all `f`, `g_i`,
`‖χ f‖_p + ∑_i ‖χ g_i + (∂_{e_i} χ) f‖_p ≤ (1 + ∑_i d_i) (‖f‖_{L_p(O)} + ∑_i ‖g_i‖_{L_p(O)})`
(`Rd.eLpNorm_mul_le_of_tsupport_subset` and `Rd.eLpNorm_mul_add_fderiv_mul_le` on `V`). -/
theorem eLpNorm_mul_add_sum_le_of_tsupport_subset {p : ℝ≥0∞} (hp : 1 ≤ p) {χ : V → ℝ}
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (hχO : tsupport χ ⊆ O)
    (hχ01 : ∀ x, χ x ∈ Icc (0 : ℝ) 1) {d : Fin (finrank ℝ V) → ℝ≥0}
    (hd : ∀ i x, ‖fderiv ℝ χ x (gridBasis V i)‖ ≤ d i) (f : V → ℂ)
    (g : Fin (finrank ℝ V) → V → ℂ) :
    eLpNorm (fun x => (χ x : ℂ) * f x) p volume + ∑ i, eLpNorm
        (fun x => (χ x : ℂ) * g i x + (fderiv ℝ χ x (gridBasis V i) : ℂ) * f x) p volume ≤
      (1 + ∑ i, (d i : ℝ≥0∞)) *
        (eLpNorm f p (volume.restrict O) + ∑ i, eLpNorm (g i) p (volume.restrict O)) := by
  have h1 : ∀ x, ‖χ x‖ ≤ ((1 : ℝ≥0) : ℝ) := fun x =>
    (norm_le_one_of_forall_mem_Icc hχ01 x).trans_eq NNReal.coe_one.symm
  have hF := eLpNorm_mul_le_of_tsupport_subset (O := ⊤) (B := O) (f := f) (p := p)
    hχ.continuous hχO h1
  have hG := fun i => eLpNorm_mul_add_fderiv_mul_le (O := ⊤) (B := O) (f := f) (g := g i)
    hp hχ hχO h1 (hd i)
  simp only [volume_restrict_top, top_inf_eq, ENNReal.coe_one, one_mul] at hF hG
  calc _ ≤ eLpNorm f p (volume.restrict O) + ∑ i, (eLpNorm (g i) p
        (volume.restrict O) + d i * eLpNorm f p (volume.restrict O)) :=
        add_le_add hF (Finset.sum_le_sum fun i _ => hG i)
    _ ≤ _ := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul]
        calc _ ≤ eLpNorm f p (volume.restrict O) +
              (∑ i, eLpNorm (g i) p (volume.restrict O) +
                (∑ i, (d i : ℝ≥0∞)) * eLpNorm f p (volume.restrict O)) +
              (∑ i, (d i : ℝ≥0∞)) * ∑ i, eLpNorm (g i) p (volume.restrict O) :=
              le_self_add
          _ = _ := by ring

end Cutoff

/-! ### Mollification on open sets -/

section Mollification

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The directional derivative of a smooth compactly supported `K`, as a Schwartz function
(Mathlib's `HasCompactSupport.toSchwartzMap`), is `y ↦ DK(y) v`. -/
theorem coe_lineDerivOp_toSchwartzMap {K : V → ℂ} (hK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) K)
    (hKs : HasCompactSupport K) (v : V) :
    ((∂^{fun _ : Fin 1 => v} (hKs.toSchwartzMap hK) : 𝓢(V, ℂ)) : V → ℂ) =
      fun y => fderiv ℝ K y v := by
  funext y
  rw [LineDeriv.iteratedLineDerivOp_one, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  rfl

/-- **The derivative of a mollification is the mollified weak derivative**: for a smooth `K`
with compact support and `g = ∂_v h` weakly on `V`, `D(K ⋆ h)(x) v = (K ⋆ g)(x)` for every `x`.
The derivative falls on the kernel (`Rd.fderiv_conv_apply`), and the weak derivative tested with
the reflected translate `y ↦ K(x - y)` moves it back to `h`
(`Rd.conv_eq_conv_iteratedLineDerivOp_of_hasWeakLineDeriv`). -/
theorem fderiv_conv_apply_eq_conv {K : V → ℂ} (hK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) K)
    (hKs : HasCompactSupport K) {v : V} {h g : V → ℂ}
    (hhg : HasWeakLineDeriv ⊤ (fun _ : Fin 1 => v) h g) (x : V) :
    fderiv ℝ (conv K h volume) x v = conv K g volume x := by
  have hc := conv_eq_conv_iteratedLineDerivOp_of_hasWeakLineDeriv hhg
    (η := hKs.toSchwartzMap hK) hKs (x := x) fun _ _ => by simp
  rw [fderiv_conv_apply (hK.of_le (by exact_mod_cast le_top)) hKs hhg.locallyIntegrable,
    ← coe_lineDerivOp_toSchwartzMap hK hKs v]
  exact hc.symm

/-- **Mollifiers converge in `L_1` of a set**: for an integrable `h` that agrees with `h'` almost
everywhere on `K`, the mollifications `η_{k+1} ⋆ h` with the standard bump
`η = Rd.LocalMeansBump.std` converge to `h'` in `L_1(K)` (`Rd.tendsto_eLpNorm_conv_dilate_sub`
with `p = 1`). -/
theorem tendsto_eLpNorm_mollify_sub_restrict {h h' : V → ℂ} (hh : Integrable h volume) {K : Set V}
    (hK : h =ᵐ[volume.restrict K] h') :
    Tendsto (fun k : ℕ => eLpNorm (conv (dilate ((k : ℝ) + 1)
      (LocalMeansBump.std (V := V)).toFun) h volume - h') 1 (volume.restrict K)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun k : ℕ => eLpNorm (conv (dilate ((k : ℝ) + 1)
      (LocalMeansBump.std (V := V)).toFun) h volume - h) 1 volume) atTop (𝓝 0) :=
    (tendsto_eLpNorm_conv_dilate_sub ENNReal.one_ne_top LocalMeansBump.std.integrable
      LocalMeansBump.std.integral_eq_one (memLp_one_iff_integrable.2 hh)).comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le)
    fun k => ?_
  calc eLpNorm (conv (dilate ((k : ℝ) + 1) (LocalMeansBump.std (V := V)).toFun) h volume - h') 1
        (volume.restrict K)
      = eLpNorm (conv (dilate ((k : ℝ) + 1) (LocalMeansBump.std (V := V)).toFun) h volume - h) 1
        (volume.restrict K) := eLpNorm_congr_ae (EventuallyEq.rfl.sub hK.symm)
    _ ≤ _ := eLpNorm_mono_measure _ Measure.restrict_le_self

/-- **The cutoff of a weakly differentiable function**: if `g = ∂_w f` weakly on `O` and `χ` is
smooth with compact closed support in `O`, then `χ f` and `χ g + (∂_w χ) f` are integrable on `V`
and `χ g + (∂_w χ) f = ∂_w (χ f)` weakly on `V` (`Rd.HasWeakLineDeriv.mul_of_tsupport_subset`
with `V` for `O` and `O` for `B`, and
`MeasureTheory.LocallyIntegrable.integrable_of_hasCompactSupport`). -/
theorem HasWeakLineDeriv.cutoff_top {O : Opens V} {w : V} {f g : V → ℂ}
    (hfg : HasWeakLineDeriv O (fun _ : Fin 1 => w) f g) {χ : V → ℝ}
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hχO : tsupport χ ⊆ O) :
    HasWeakLineDeriv ⊤ (fun _ : Fin 1 => w) (fun x => (χ x : ℂ) * f x)
        (fun x => (χ x : ℂ) * g x + (fderiv ℝ χ x w : ℂ) * f x) ∧
      Integrable (fun x => (χ x : ℂ) * f x) volume ∧
      Integrable (fun x => (χ x : ℂ) * g x + (fderiv ℝ χ x w : ℂ) * f x) volume := by
  have h : HasWeakLineDeriv ⊤ (fun _ : Fin 1 => w) (fun x => (χ x : ℂ) * f x)
      (fun x => (χ x : ℂ) * g x + (fderiv ℝ χ x w : ℂ) * f x) :=
    (hfg.mono (by simp)).mul_of_tsupport_subset hχ hχO
  have hc : HasCompactSupport fun x => (χ x : ℂ) := hχc.comp_left Complex.ofReal_zero
  have hc' : HasCompactSupport fun x => (fderiv ℝ χ x w : ℂ) :=
    (hχc.fderiv_apply (𝕜 := ℝ) w).comp_left Complex.ofReal_zero
  exact ⟨h, h.locallyIntegrable.integrable_of_hasCompactSupport hc.mul_right,
    h.locallyIntegrable_deriv.integrable_of_hasCompactSupport (hc.mul_right.add hc'.mul_right)⟩

/-- **Interior mollification in `L_1`**: let `g_i = ∂_{w_i} f` weakly on the open set `O`
(`i ∈ ι`), `f` locally integrable on `O`, and `K ⊆ O` compact. Then there are smooth compactly
supported `u_k` with `u_k → f` and `D u_k(·) w_i → g_i` in `L_1(K)` for every `i`: with a cutoff
`χ = 1` near `K` (`Rd.exists_contDiff_eventuallyEq_one`), `u_k = η_{k+1} ⋆ (χ f)`, whose
derivatives are `η_{k+1} ⋆ (χ g_i + (∂_{w_i} χ) f)` (`Rd.fderiv_conv_apply_eq_conv`). -/
theorem exists_tendsto_contDiff_of_hasWeakLineDeriv {O : Opens V} {K : Set V} (hK : IsCompact K)
    (hKO : K ⊆ O) {ι : Type*} {w : ι → V} {f : V → ℂ} {g : ι → V → ℂ}
    (hfg : ∀ i, HasWeakLineDeriv O (fun _ : Fin 1 => w i) f (g i))
    (hf : LocallyIntegrableOn f O volume) :
    ∃ u : ℕ → V → ℂ, (∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (u k)) ∧
      (∀ k, HasCompactSupport (u k)) ∧
      Tendsto (fun k => eLpNorm (u k - f) 1 (volume.restrict K)) atTop (𝓝 0) ∧
      ∀ i, Tendsto (fun k => eLpNorm ((fun x => fderiv ℝ (u k) x (w i)) - g i) 1
        (volume.restrict K)) atTop (𝓝 0) := by
  obtain ⟨χ, hχ, hχc, hχO, -, hχ1⟩ := exists_contDiff_eventuallyEq_one hK O.isOpen hKO
  have hχK : ∀ x ∈ K, χ x = 1 ∧ fderiv ℝ χ x = 0 := fun x hx => by
    have hev : χ =ᶠ[𝓝 x] fun _ => 1 := hχ1.filter_mono (nhds_le_nhdsSet hx)
    exact ⟨hev.eq_of_nhds, by rw [hev.fderiv_eq, fderiv_const_apply]⟩
  have hc : HasCompactSupport fun x => (χ x : ℂ) := hχc.comp_left Complex.ofReal_zero
  have hFl : LocallyIntegrable (fun x => (χ x : ℂ) * f x) volume := by
    have h := locallyIntegrableOn_mul_of_tsupport_subset (O := ⊤) (B := O) (hf.mono_set (by simp))
      (Complex.continuous_ofReal.comp hχ.continuous)
      ((tsupport_comp_subset Complex.ofReal_zero χ).trans hχO)
    rwa [Opens.coe_top, locallyIntegrableOn_univ] at h
  have hFi := hFl.integrable_of_hasCompactSupport hc.mul_right
  set η := (LocalMeansBump.std (V := V)).toFun
  have hη : ∀ k : ℕ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dilate ((k : ℝ) + 1) η) := fun k =>
    contDiff_dilate LocalMeansBump.std.contDiff _
  have hηc : ∀ k : ℕ, HasCompactSupport (dilate ((k : ℝ) + 1) η) := fun k =>
    hasCompactSupport_dilate LocalMeansBump.std.hasCompactSupport (by positivity)
  refine ⟨fun k => conv (dilate ((k : ℝ) + 1) η) (fun x => (χ x : ℂ) * f x) volume,
    fun k => contDiff_conv (hη k) (hηc k) hFl,
    fun k => (hηc k).convolution (L := ContinuousLinearMap.mul ℂ ℂ) (μ := volume) hc.mul_right,
    tendsto_eLpNorm_mollify_sub_restrict hFi ?_, fun i => ?_⟩
  · filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    simp [(hχK x hx).1]
  obtain ⟨hG, -, hGi⟩ := (hfg i).cutoff_top hχ hχc hχO
  have he : ∀ k : ℕ, (fun x => fderiv ℝ (conv (dilate ((k : ℝ) + 1) η)
      (fun x => (χ x : ℂ) * f x) volume) x (w i)) = conv (dilate ((k : ℝ) + 1) η)
        (fun x => (χ x : ℂ) * g i x + (fderiv ℝ χ x (w i) : ℂ) * f x) volume := fun k =>
    funext fun x => fderiv_conv_apply_eq_conv (hη k) (hηc k) hG x
  simp only [he]
  refine tendsto_eLpNorm_mollify_sub_restrict hGi ?_
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  simp [(hχK x hx).1, (hχK x hx).2]

end Mollification

/-! ### Compositions with measure-preserving maps -/

section Composition

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β] [NormedAddCommGroup E]
  {μ : Measure α} {ν : Measure β} {Φ : α → β} {U : Set α} {O : Set β} {h : β → E}

/-- **Measurability of a composition on a subset**: if `Φ` carries `μ` to `ν` and maps the set
`U` into the measurable set `O`, and `h` is almost everywhere strongly measurable on `O`, then
`h ∘ Φ` is almost everywhere strongly measurable on `U`. The map `Φ` carries `μ` on `Φ⁻¹(O)` to
`ν` on `O` (Mathlib's `MeasurePreserving.restrict_preimage`), and `U ⊆ Φ⁻¹(O)`. -/
theorem aestronglyMeasurable_comp_of_mapsTo (hmp : MeasurePreserving Φ μ ν)
    (hO : MeasurableSet O) (hUO : MapsTo Φ U O)
    (hh : AEStronglyMeasurable h (ν.restrict O)) : AEStronglyMeasurable (h ∘ Φ) (μ.restrict U) :=
  (hh.comp_measurePreserving (hmp.restrict_preimage hO)).mono_measure
    (Measure.restrict_mono_set μ hUO.subset_preimage)

/-- **`L_p` norms of compositions on a subset**: if `Φ` carries `μ` to `ν` and maps the set `U`
into the measurable set `O`, then `‖h ∘ Φ‖_{L_p(U)} ≤ ‖h‖_{L_p(O)}` for every `h` and every
`0 ≤ p ≤ ∞`. The map `Φ` carries `μ` on `Φ⁻¹(O) ⊇ U` to `ν` on `O`
(Mathlib's `MeasurePreserving.restrict_preimage`, `eLpNorm_comp_measurePreserving`); for an `h`
that is not almost everywhere strongly measurable on `O`, the right side is `∞`. -/
theorem eLpNorm_comp_le_of_mapsTo (hmp : MeasurePreserving Φ μ ν)
    (hO : MeasurableSet O) (hUO : MapsTo Φ U O) (p : ℝ≥0∞) :
    eLpNorm (h ∘ Φ) p (μ.restrict U) ≤ eLpNorm h p (ν.restrict O) := by
  by_cases hh : AEStronglyMeasurable h (ν.restrict O)
  swap
  · rw [eLpNorm_of_not_aestronglyMeasurable hh]
    exact le_top
  exact (eLpNorm_mono_measure _ (Measure.restrict_mono_set μ hUO.subset_preimage)).trans_eq
    (eLpNorm_comp_measurePreserving hh (hmp.restrict_preimage hO))

end Composition

/-! ### The chain rule -/

section ChainRule

omit [MeasurableSpace V] [BorelSpace V] in
/-- **The chain rule through the basis**: if `u` is differentiable at `Φ x` and `Φ` at `x`, then
`∂_v (u ∘ Φ)(x) = ∑_i ⟪DΦ(x) v, e_i⟫ Du(Φ x) e_i`, by `DΦ(x) v = ∑_i ⟪e_i, DΦ(x) v⟫ e_i`
(Mathlib's `OrthonormalBasis.sum_repr'`). -/
theorem lineDeriv_comp_eq_sum {u : V → ℂ} {Φ : V → V} {x : V}
    (hu : DifferentiableAt ℝ u (Φ x)) (hΦ : DifferentiableAt ℝ Φ x) (v : V) :
    lineDeriv ℝ (u ∘ Φ) x v =
      ∑ i, (inner ℝ (fderiv ℝ Φ x v) (gridBasis V i) : ℂ) * fderiv ℝ u (Φ x) (gridBasis V i) := by
  rw [(hu.comp x hΦ).lineDeriv_eq_fderiv, fderiv_comp x hu hΦ, ContinuousLinearMap.comp_apply]
  conv_lhs => rw [← (gridBasis V).sum_repr' (fderiv ℝ Φ x v)]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Complex.real_smul, real_inner_comm]

/-- **Smooth functions after a Lipschitz map**: for a smooth `u` with compact support and a
Lipschitz `Φ`, the weak derivative of `u ∘ Φ` on every open set along `v` is
`x ↦ ∑_i ⟪DΦ(x) v, e_i⟫ Du(Φ x) e_i`: `u ∘ Φ` is Lipschitz
(`Rd.hasWeakLineDeriv_of_lipschitzWith`), and `Rd.lineDeriv_comp_eq_sum` holds where `Φ` is
differentiable, almost everywhere by Rademacher's theorem. -/
theorem hasWeakLineDeriv_comp_of_contDiff {u : V → ℂ}
    (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u) (huc : HasCompactSupport u) {K : ℝ≥0}
    {Φ : V → V} (hΦ : LipschitzWith K Φ) (Ω : Opens V) (v : V) :
    HasWeakLineDeriv Ω (fun _ : Fin 1 => v) (u ∘ Φ)
      (fun x => ∑ i, (inner ℝ (fderiv ℝ Φ x v) (gridBasis V i) : ℂ) *
        fderiv ℝ u (Φ x) (gridBasis V i)) := by
  obtain ⟨D, hD⟩ := hu.lipschitzWith_of_hasCompactSupport huc (by simp)
  refine (hasWeakLineDeriv_of_lipschitzWith (hD.comp hΦ) Ω v).congr_ae EventuallyEq.rfl ?_
  refine ae_restrict_of_ae ?_
  filter_upwards [hΦ.ae_differentiableAt (μ := volume)] with x hx
  exact lineDeriv_comp_eq_sum ((hu.differentiable (by simp)).differentiableAt) hx v

/-- **The `L_p` bound of the chain-rule derivative**: for a `K`-Lipschitz `Φ` that preserves
Lebesgue measure and maps the set `U` into the measurable set `O`, every `v` and all `h_i`,
`‖∑_i ⟪DΦ v, e_i⟫ h_i ∘ Φ‖_{L_p(U)} ≤ K ‖v‖ ∑_i ‖h_i‖_{L_p(O)}` for `1 ≤ p`, since
`|⟪DΦ(x) v, e_i⟫| ≤ ‖DΦ(x)‖ ‖v‖ ≤ K ‖v‖` (Mathlib's `norm_fderiv_le_of_lipschitz`),
`MeasureTheory.eLpNorm_mul_le_of_forall_norm_le` and `Rd.eLpNorm_comp_le_of_mapsTo`. -/
theorem eLpNorm_sum_inner_fderiv_mul_comp_le {p : ℝ≥0∞} (hp : 1 ≤ p) {K : ℝ≥0} {Φ : V → V}
    (hΦ : LipschitzWith K Φ) (hmp : MeasurePreserving Φ volume volume) {U O : Set V}
    (hO : MeasurableSet O) (hUO : MapsTo Φ U O) (v : V) (h : Fin (finrank ℝ V) → V → ℂ) :
    eLpNorm (fun x => ∑ i, (inner ℝ (fderiv ℝ Φ x v) (gridBasis V i) : ℂ) * h i (Φ x)) p
        (volume.restrict U) ≤ K * ‖v‖ₑ * ∑ i, eLpNorm (h i) p (volume.restrict O) := by
  have hfun : (fun x => ∑ i, (inner ℝ (fderiv ℝ Φ x v) (gridBasis V i) : ℂ) * h i (Φ x)) =
      ∑ i, fun x => (inner ℝ (fderiv ℝ Φ x v) (gridBasis V i) : ℂ) * h i (Φ x) := by
    funext x
    simp [Finset.sum_apply]
  rw [hfun, Finset.mul_sum]
  refine (eLpNorm_sum_le hp).trans (Finset.sum_le_sum fun i _ => ?_)
  have hc : Measurable fun x => (inner ℝ (fderiv ℝ Φ x v) (gridBasis V i) : ℂ) :=
    Complex.measurable_ofReal.comp
      (Measurable.inner (measurable_fderiv_apply_const ℝ Φ v) measurable_const)
  have hb : ∀ x, ‖(inner ℝ (fderiv ℝ Φ x v) (gridBasis V i) : ℂ)‖ ≤ (K * ‖v‖₊ : ℝ≥0) := by
    intro x
    rw [Complex.norm_real, NNReal.coe_mul, coe_nnNorm]
    calc ‖inner ℝ (fderiv ℝ Φ x v) (gridBasis V i)‖
        ≤ ‖fderiv ℝ Φ x v‖ * ‖gridBasis V i‖ := norm_inner_le_norm _ _
      _ = ‖fderiv ℝ Φ x v‖ := by rw [(gridBasis V).orthonormal.1 i, mul_one]
      _ ≤ ‖fderiv ℝ Φ x‖ * ‖v‖ := (fderiv ℝ Φ x).le_opNorm v
      _ ≤ K * ‖v‖ := by gcongr; exact norm_fderiv_le_of_lipschitz ℝ hΦ
  calc _ ≤ (K * ‖v‖₊ : ℝ≥0) * eLpNorm (h i ∘ Φ) p (volume.restrict U) :=
        eLpNorm_mul_le_of_forall_norm_le hc.aestronglyMeasurable hb p
    _ ≤ (K * ‖v‖₊ : ℝ≥0) * eLpNorm (h i) p (volume.restrict O) := by
        gcongr
        exact eLpNorm_comp_le_of_mapsTo hmp hO hUO p
    _ = _ := by rw [ENNReal.coe_mul, eNorm_eq_nnNorm]

/-- **Local-to-global for weak derivatives**: if every compact `K ⊆ U` lies in an open `U'` on
which `G = ∂^v F` weakly, then `G = ∂^v F` weakly on `U`. A test function on `U` is a test
function on such a `U'` containing its closed support; local integrability is checked near the
points of `U`. -/
theorem hasWeakLineDeriv_of_forall_isCompact {U : Opens V} {k : ℕ} {v : Fin k → V} {F G : V → ℂ}
    (h : ∀ K ⊆ (U : Set V), IsCompact K →
      ∃ U' : Opens V, K ⊆ U' ∧ HasWeakLineDeriv U' v F G) :
    HasWeakLineDeriv U v F G := by
  have hloc : ∀ {u : V → ℂ}, (∀ U' : Opens V, HasWeakLineDeriv U' v F G →
      LocallyIntegrableOn u U' volume) → LocallyIntegrableOn u U volume := by
    intro u hu x hx
    obtain ⟨U', hxU', hU'⟩ := h {x} (singleton_subset_iff.2 hx) isCompact_singleton
    have hx' : x ∈ (U' : Set V) := hxU' rfl
    have h' := hu U' hU' x hx'
    rwa [nhdsWithin_eq_nhds.2 (U'.isOpen.mem_nhds hx'),
      ← nhdsWithin_eq_nhds.2 (U.isOpen.mem_nhds hx)] at h'
  refine (hasWeakLineDeriv_iff_integral (hloc fun _ h' => h'.1) (hloc fun _ h' => h'.2)).2
    fun φ => ?_
  obtain ⟨U', hKU', hU'⟩ := h (tsupport φ) φ.tsupport_subset φ.hasCompactSupport
  let ψ : 𝓓(U', ℝ) := ⟨φ, φ.contDiff, φ.hasCompactSupport, hKU'⟩
  have hψ : (ψ : V → ℝ) = φ := rfl
  have h' := hU'.integral_eq ψ
  rwa [coe_iteratedLineDerivOp_eq hψ, hψ] at h'

/-- **The chain rule on a piece**: let `g_i = ∂_{e_i} f` weakly on `O`, `f` locally integrable on
`O`, `L ⊆ O` compact, `Φ` a `K`-Lipschitz map preserving Lebesgue measure, and `U` open with
`Φ(U) ⊆ L`. Then `∑_i ⟪DΦ(·) v, e_i⟫ g_i ∘ Φ = ∂_v (f ∘ Φ)` weakly on `U`: the smooth `u_k` of
`Rd.exists_tendsto_contDiff_of_hasWeakLineDeriv` give the chain rule for `u_k ∘ Φ`
(`Rd.hasWeakLineDeriv_comp_of_contDiff`), and both sides converge in `L_1(U)` by
`Rd.eLpNorm_comp_le_of_mapsTo` and `Rd.eLpNorm_sum_inner_fderiv_mul_comp_le`
(`Rd.HasWeakLineDeriv.of_tendsto`). -/
theorem HasWeakLineDeriv.comp_lipschitzWith_of_mapsTo_isCompact {O U : Opens V} {L : Set V}
    (hL : IsCompact L) (hLO : L ⊆ O) {f : V → ℂ} {g : Fin (finrank ℝ V) → V → ℂ}
    (hf : LocallyIntegrableOn f O volume)
    (hfg : ∀ i, HasWeakLineDeriv O (fun _ : Fin 1 => gridBasis V i) f (g i)) {K : ℝ≥0}
    {Φ : V → V} (hΦ : LipschitzWith K Φ) (hmp : MeasurePreserving Φ volume volume)
    (hUL : MapsTo Φ U L) (v : V) :
    HasWeakLineDeriv U (fun _ : Fin 1 => v) (f ∘ Φ)
      (fun x => ∑ i, (inner ℝ (fderiv ℝ Φ x v) (gridBasis V i) : ℂ) * g i (Φ x)) := by
  obtain ⟨u, hu, huc, hlim, hlimd⟩ := exists_tendsto_contDiff_of_hasWeakLineDeriv hL hLO hfg hf
  have hLm := hL.measurableSet
  have hfL : MemLp f 1 (volume.restrict L) :=
    memLp_one_iff_integrable.2 (hf.integrableOn_compact_subset hLO hL)
  have hgL : ∀ i, MemLp (g i) 1 (volume.restrict L) := fun i =>
    memLp_one_iff_integrable.2 ((hfg i).2.integrableOn_compact_subset hLO hL)
  have hKv : (K : ℝ≥0∞) * ‖v‖ₑ ≠ ∞ := ENNReal.mul_ne_top ENNReal.coe_ne_top eNorm_ne_top
  refine HasWeakLineDeriv.of_tendsto le_rfl le_rfl (l := atTop)
    (fun k => hasWeakLineDeriv_comp_of_contDiff (hu k) (huc k) hΦ U v)
    ((eLpNorm_comp_le_of_mapsTo hmp hLm hUL 1).trans_lt hfL)
    ((eLpNorm_sum_inner_fderiv_mul_comp_le le_rfl hΦ hmp hLm hUL v g).trans_lt
      (ENNReal.mul_lt_top hKv.lt_top (ENNReal.sum_lt_top.2 fun i _ => hgL i))) ?_ ?_
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le)
      fun k => ?_
    exact eLpNorm_comp_le_of_mapsTo (h := u k - f) hmp hLm hUL 1
  · have hsum := ENNReal.Tendsto.const_mul (tendsto_finsetSum Finset.univ fun i _ =>
      hlimd i) (Or.inr hKv)
    simp only [Finset.sum_const_zero, mul_zero] at hsum
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => bot_le)
      fun k => ?_
    have he : ((fun x => ∑ i, (inner ℝ (fderiv ℝ Φ x v) (gridBasis V i) : ℂ) *
        fderiv ℝ (u k) (Φ x) (gridBasis V i)) -
        fun x => ∑ i, (inner ℝ (fderiv ℝ Φ x v) (gridBasis V i) : ℂ) * g i (Φ x)) =
        fun x => ∑ i, (inner ℝ (fderiv ℝ Φ x v) (gridBasis V i) : ℂ) *
          ((fun y => fderiv ℝ (u k) y (gridBasis V i)) - g i) (Φ x) := by
      funext x
      simp only [Pi.sub_apply, ← Finset.sum_sub_distrib, mul_sub]
    rw [he]
    exact eLpNorm_sum_inner_fderiv_mul_comp_le le_rfl hΦ hmp hLm hUL v
      fun i => (fun y => fderiv ℝ (u k) y (gridBasis V i)) - g i

/-- **The chain rule for weak derivatives under Lipschitz maps**: let `g_i = ∂_{e_i} f` weakly on
the open set `O` for the basis vectors `e_i` of `Rd.gridBasis`, let `Φ : V → V` be `K`-Lipschitz
and preserve Lebesgue measure, and let `Φ` map the open set `U` into `O`. Then for every `v ∈ V`,
`x ↦ ∑_i ⟪DΦ(x) v, e_i⟫ g_i(Φ x)` is the weak derivative `∂_v (f ∘ Φ)` on `U`; here `DΦ(x)` is
Mathlib's `fderiv`, which exists almost everywhere by Rademacher's theorem. Every compact
`K' ⊆ U` lies in the open set `Φ⁻¹(int L)` for a compact `L ⊆ O` with `Φ(K') ⊆ int L`, where
`Rd.HasWeakLineDeriv.comp_lipschitzWith_of_mapsTo_isCompact` applies
(`Rd.hasWeakLineDeriv_of_forall_isCompact`). -/
theorem HasWeakLineDeriv.comp_lipschitzWith {O U : Opens V} {f : V → ℂ}
    {g : Fin (finrank ℝ V) → V → ℂ}
    (hfg : ∀ i, HasWeakLineDeriv O (fun _ : Fin 1 => gridBasis V i) f (g i)) {K : ℝ≥0}
    {Φ : V → V} (hΦ : LipschitzWith K Φ) (hmp : MeasurePreserving Φ volume volume)
    (hUO : MapsTo Φ U O) (v : V) :
    HasWeakLineDeriv U (fun _ : Fin 1 => v) (f ∘ Φ)
      (fun x => ∑ i, (inner ℝ (fderiv ℝ Φ x v) (gridBasis V i) : ℂ) * g i (Φ x)) := by
  refine hasWeakLineDeriv_of_forall_isCompact fun Kc hKc hKcc => ?_
  obtain ⟨L, hL, hΦL, hLO⟩ := exists_compact_between (hKcc.image hΦ.continuous) O.isOpen
    (image_subset_iff.2 (hKc.trans hUO))
  let U' : Opens V := ⟨Φ ⁻¹' interior L, isOpen_interior.preimage hΦ.continuous⟩
  refine ⟨U', fun x hx => hΦL (mem_image_of_mem Φ hx), ?_⟩
  exact HasWeakLineDeriv.comp_lipschitzWith_of_mapsTo_isCompact hL hLO
    (locallyIntegrableOn_of_forall_gridBasis hfg) hfg hΦ hmp
    (fun x hx => interior_subset hx) v

end ChainRule

end Rd
