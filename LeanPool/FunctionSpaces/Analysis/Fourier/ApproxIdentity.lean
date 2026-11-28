/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Analysis.Fourier.Convolution
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Approximate identities in `L_p`

**Changes of scale**: `∫ f(r x) dμ(x) = |r|^(-n) ∫ f dμ` for `r ≠ 0`, every additive Haar
measure `μ` and every `f : V → [0, ∞]`, also over sets (`Rd.lintegral_comp_smul`,
`Rd.setLIntegral_comp_smul`, `Rd.lintegral_comp_two_pow_smul`).

The **dilation** `Φ_c(x) = c^n Φ(c x)`, `n = dim V`, keeps the integral and the `L_1` norm of `Φ`
(`Rd.integral_dilate`, `Rd.lintegral_enorm_dilate`, `Rd.eLpNorm_dilate_one`) and compact
supports (`Rd.hasCompactSupport_dilate`); every `x` in its support has `c x` in the support of
`Φ`, so the support shrinks into small balls as `c → ∞`
(`Rd.smul_mem_tsupport_of_mem_tsupport_dilate`, `Rd.norm_le_of_mem_tsupport_dilate`,
`Rd.eventually_tsupport_dilate_add_subset_thickening`). The convolution with `Φ_c` averages `f`
over the shifts `c^(-1) z` weighted by `Φ(z)`: `(Φ_c ⋆ f)(x) = ∫ Φ(z) f(x - c^(-1) z) dz`
(`Rd.conv_dilate_apply`, Mathlib's `Measure.integral_comp_smul`).

**Approximate identities** (`Rd.tendsto_eLpNorm_conv_dilate_sub`): for an integrable `Φ` with
`∫ Φ = 1` and `f ∈ L_p`, `1 ≤ p < ∞`, `‖Φ_c ⋆ f - f‖_p → 0` as `c → ∞`. With `∫ Φ = 1`,
`(Φ_c ⋆ f)(x) - f(x) = ∫ Φ(z) (f(x - c^(-1) z) - f(x)) dz`, and the weighted Jensen inequality
gives `‖Φ_c ⋆ f - f‖_p^p ≤ ‖Φ‖_1^(p-1) ∫ |Φ(z)| ‖f(· - c^(-1) z) - f‖_p^p dz`
(`Rd.eLpNorm_conv_dilate_sub_le`). Translation is
continuous in `L_p` (`Rd.continuous_eLpNorm_comp_sub_sub`, from Mathlib's continuity of the
action of `V` on `L_p` by translation of the domain), so the integrand tends to `0`, and dominated
convergence applies with the bound `|Φ(z)| (2 ‖f‖_p)^p`. For the operators of `Rd.convLp` this
reads `Φ_{c_i} ⋆ f → f` in `L_p` along any dilation factors `c_i → ∞`
(`Rd.tendsto_convLp_dilate`). Uniformly bounded operators with `T_i f → f` also satisfy
`T_i (T_i f) → f` (`Rd.tendsto_apply_apply_of_tendsto`).

**At points of continuity** (`Rd.conv_dilate_near`): for `Φ` vanishing outside a ball,
`(Φ_{2^J} ⋆ F_J)(z) → z₀` as `J → ∞` and `z → y` whenever `F_J(z) → z₀` as `J → ∞` and `z → y`.

**First moments of dilates** (`Rd.integral_inner_mul_dilate`): `∫ ⟪w, x⟫ Φ_c(x) dx` is `c⁻¹` times
the first moment of `Φ`, since `⟪w, x⟫ Φ_c(x) = c⁻¹ (⟪w, ·⟫ Φ)_c(x)` (`Rd.inner_mul_dilate_eq`).
-/

@[expose] public section

open MeasureTheory Filter Topology Module
open scoped ENNReal

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {μ : Measure V} [μ.IsAddHaarMeasure]

/-! ### Continuity of translation -/

/-- **Continuity of translation in `L_p`**, `1 ≤ p < ∞`: `w ↦ ‖f(· - w) - f‖_p` is continuous,
from Mathlib's continuity of the action of `V` on `L_p` by translation of the domain
(`Lp.instContinuousVAddDomAddAct`). -/
theorem continuous_eLpNorm_comp_sub_sub {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) {f : V → ℂ}
    (hf : MemLp f p μ) : Continuous fun w : V => eLpNorm (fun x => f (x - w) - f x) p μ := by
  have : Fact (p ≠ ∞) := ⟨hp⟩
  set G : V → Lp ℂ p μ := fun w =>
    (hf.comp_measurePreserving (measurePreserving_vadd (-w) μ)).toLp (fun x => f (-w +ᵥ x))
  have hc : Continuous fun w : V => DomAddAct.mk (-w) +ᵥ hf.toLp f :=
    (DomAddAct.continuous_mk.comp continuous_neg).vadd continuous_const
  have hG : Continuous G := hc.congr fun w => DomAddAct.mk_vadd_toLp (-w) hf
  have hT : Continuous fun w : V => ‖G w - hf.toLp f‖ₑ := (hG.sub continuous_const).eNorm
  refine hT.congr fun w => ?_
  simp only [G]
  rw [← MemLp.toLp_sub, Lp.eNorm_toLp]
  congr 1
  funext x
  simp only [Pi.sub_apply, vadd_eq_add, neg_add_eq_sub]

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- `‖f(· - w)‖_p = ‖f‖_p`: translation preserves `L_p` norms. -/
theorem eLpNorm_comp_sub_right {f : V → ℂ} (hf : AEStronglyMeasurable f μ) (p : ℝ≥0∞) (w : V) :
    eLpNorm (fun x => f (x - w)) p μ = eLpNorm f p μ :=
  eLpNorm_comp_measurePreserving hf (measurePreserving_sub_right μ w)

/-! ### Changes of scale -/

/-- **Integrals under a change of scale**: `∫ f(r x) dμ(x) = |r^(-n)| ∫ f dμ` for `r ≠ 0`, every
additive Haar measure `μ` and every `f : V → [0, ∞]` (Mathlib's `Measure.map_addHaar_smul`). -/
theorem lintegral_comp_smul (f : V → ℝ≥0∞) {r : ℝ} (hr : r ≠ 0) :
    ∫⁻ x, f (r • x) ∂μ = ENNReal.ofReal |(r ^ finrank ℝ V)⁻¹| * ∫⁻ x, f x ∂μ := by
  rw [← smul_eq_mul, ← lintegral_smul_measure, ← Measure.map_addHaar_smul μ hr]
  exact (lintegral_map_equiv f (Homeomorph.smulOfNeZero r hr).toMeasurableEquiv).symm

open scoped Pointwise in
/-- The set version of `Rd.lintegral_comp_smul`: `∫_s f(r x) dμ(x) = |r^(-n)| ∫_{r s} f dμ` for
every set `s`, since `x ↦ r x` is a measurable equivalence (Mathlib's
`MeasurableEmbedding.restrict_map`). -/
theorem setLIntegral_comp_smul (f : V → ℝ≥0∞) {r : ℝ} (hr : r ≠ 0) (s : Set V) :
    ∫⁻ x in s, f (r • x) ∂μ = ENNReal.ofReal |(r ^ finrank ℝ V)⁻¹| * ∫⁻ x in r • s, f x ∂μ := by
  let e := (Homeomorph.smulOfNeZero (α := V) r hr).toMeasurableEquiv
  have hpre : e ⁻¹' (r • s) = s := by
    ext x
    exact Set.smul_mem_smul_set_iff₀ hr s x
  rw [← smul_eq_mul, ← lintegral_smul_measure, ← Measure.restrict_smul,
    ← Measure.map_addHaar_smul μ hr]
  rw [show (fun x : V => r • x) = ⇑e from rfl, e.measurableEmbedding.restrict_map,
    lintegral_map_equiv, hpre]
  rfl

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
open scoped Pointwise in
/-- `r {z : a ≤ ‖z‖} = {u : r a ≤ ‖u‖}` for `r > 0`. -/
theorem smul_setOf_le_norm {r : ℝ} (hr : 0 < r) (a : ℝ) :
    r • {z : V | a ≤ ‖z‖} = {u : V | r * a ≤ ‖u‖} := by
  ext u
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hr.ne', Set.mem_ofPred_eq, Set.mem_ofPred_eq, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.2 hr.le), le_inv_mul_iff₀ hr]

/-- `∫ f(2^j x) dμ(x) = 2^(-jn) ∫ f dμ`. -/
theorem lintegral_comp_two_pow_smul (f : V → ℝ≥0∞) (j : ℕ) :
    ∫⁻ x, f (((2 : ℝ) ^ j) • x) ∂μ = (2 ^ (j * finrank ℝ V))⁻¹ * ∫⁻ x, f x ∂μ := by
  rw [lintegral_comp_smul f (by positivity), abs_of_pos (by positivity), ← pow_mul,
    ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow zero_le_two,
    ENNReal.ofReal_ofNat]

/-! ### Dilations -/

/-- The **dilation** `Φ_c(x) = c^n Φ(c x)`, `n = dim V`, which keeps the integral of `Φ`. -/
noncomputable def dilate (c : ℝ) (Φ : V → ℂ) (x : V) : ℂ :=
  (((c ^ finrank ℝ V : ℝ)) : ℂ) * Φ (c • x)

/-- Dilations of integrable functions are integrable. -/
theorem integrable_dilate {Φ : V → ℂ} (hΦ : Integrable Φ μ) {c : ℝ} (hc : c ≠ 0) :
    Integrable (dilate c Φ) μ :=
  (hΦ.comp_smul hc).const_mul _

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- Dilates of compactly supported functions have compact support. -/
theorem hasCompactSupport_dilate {K : V → ℂ} (hK : HasCompactSupport K) {c : ℝ} (hc : c ≠ 0) :
    HasCompactSupport (dilate c K) :=
  (hK.comp_homeomorph (Homeomorph.smulOfNeZero c hc)).mul_left

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **The support of a dilation**: if `x` lies in the closed support of `Φ_c`, `c ≠ 0`, then
`c x` lies in the closed support of `Φ`; the closed support of `Φ_c` lies in the preimage of that
of `Φ` under `x ↦ c x` (Mathlib's `tsupport_comp_eq_preimage`). -/
theorem smul_mem_tsupport_of_mem_tsupport_dilate {η : V → ℂ} {c : ℝ} (hc : c ≠ 0) {x : V}
    (hx : x ∈ tsupport (dilate c η)) : c • x ∈ tsupport η := by
  have h1 : tsupport (dilate c η) ⊆ tsupport (η ∘ Homeomorph.smulOfNeZero c hc) :=
    tsupport_mul_subset_right (f := fun _ => (((c ^ finrank ℝ V : ℝ)) : ℂ))
  have h2 := h1 hx
  rw [tsupport_comp_eq_preimage] at h2
  exact h2

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **Dilated supports shrink**: if the closed support of `η` lies in `closedBall(0, R)` and `c
> 0`, the
closed support of `η_c` lies in `closedBall(0, R/c)`. -/
theorem norm_le_of_mem_tsupport_dilate {η : V → ℂ} {R : ℝ}
    (hηR : tsupport η ⊆ Metric.closedBall 0 R) {c : ℝ} (hc : 0 < c) {x : V}
    (hx : x ∈ tsupport (dilate c η)) : ‖x‖ ≤ R / c := by
  have h := hηR (smul_mem_tsupport_of_mem_tsupport_dilate hc.ne' hx)
  rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg hc.le] at h
  rw [le_div_iff₀ hc]
  linarith

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
open scoped Pointwise in
/-- **Dilated supports plus a set lie in a thickening**: if the closed support of `η` lies in
`closedBall(0, R)` and `δ > 0`, then `supp η_{2^n} + S` lies in the `δ`-neighbourhood of `S` for
all large
`n`: once `R / 2^n < δ`, `supp η_{2^n} ⊆ B(0, δ)` (`Rd.norm_le_of_mem_tsupport_dilate`), and
`B(0, δ) + S` is the `δ`-neighbourhood of `S` (Mathlib's `ball_add_zero`). -/
theorem eventually_tsupport_dilate_add_subset_thickening {η : V → ℂ} {R δ : ℝ}
    (hηR : tsupport η ⊆ Metric.closedBall 0 R) (hδ : 0 < δ) (S : Set V) :
    ∀ᶠ n : ℕ in atTop, tsupport (dilate ((2 : ℝ) ^ n) η) + S ⊆ Metric.thickening δ S := by
  filter_upwards [(tendsto_pow_atTop_atTop_of_one_lt one_lt_two).eventually_gt_atTop (R / δ)]
    with n hn
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  rw [div_lt_iff₀ hδ] at hn
  rw [← ball_add_zero]
  refine Set.add_subset_add (fun z hz => ?_) subset_rfl
  rw [mem_ball_zero_iff]
  refine (norm_le_of_mem_tsupport_dilate hηR hpos hz).trans_lt ?_
  rw [div_lt_iff₀ hpos]
  linarith

/-- **The dilation keeps the integral**: `∫ Φ_c = ∫ Φ` for `c > 0` (Mathlib's
`Measure.integral_comp_smul`). -/
theorem integral_dilate (Φ : V → ℂ) {c : ℝ} (hc : 0 < c) :
    ∫ x, dilate c Φ x ∂μ = ∫ x, Φ x ∂μ := by
  have hpow : (0 : ℝ) < c ^ finrank ℝ V := pow_pos hc _
  simp only [dilate]
  rw [integral_const_mul, Measure.integral_comp_smul μ Φ c, abs_of_pos (inv_pos.2 hpow),
    Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hpow.ne',
    Complex.ofReal_one, one_mul]

/-- **Dilations keep the `L_1` norm of every function**: `∫ |F_c| dμ = ∫ |F| dμ` for `c > 0` and
every `F : V → ℂ`, integrable or not, by the change of scale `u = c x`
(`Rd.lintegral_comp_smul`). -/
theorem lintegral_enorm_dilate (F : V → ℂ) {c : ℝ} (hc : 0 < c) :
    ∫⁻ x, ‖dilate c F x‖ₑ ∂μ = ∫⁻ x, ‖F x‖ₑ ∂μ := by
  have hpow : (0 : ℝ) < c ^ finrank ℝ V := pow_pos hc _
  have h : ∀ x, ‖dilate c F x‖ₑ = ENNReal.ofReal (c ^ finrank ℝ V) * ‖F (c • x)‖ₑ := fun x => by
    rw [dilate, eNorm_mul, ← ofReal_norm (((c ^ finrank ℝ V : ℝ)) : ℂ), Complex.norm_real,
      Real.norm_of_nonneg hpow.le]
  simp_rw [h]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_comp_smul (fun u => ‖F u‖ₑ) hc.ne',
    ← mul_assoc, abs_of_pos (inv_pos.2 hpow), ← ENNReal.ofReal_mul hpow.le,
    mul_inv_cancel₀ hpow.ne', ENNReal.ofReal_one, one_mul]

/-- **The dilation keeps the `L_1` norm**: `‖Φ_c‖_1 = ‖Φ‖_1` for `c > 0`
(`Rd.lintegral_enorm_dilate`). -/
theorem eLpNorm_dilate_one {Φ : V → ℂ} (hΦ : Integrable Φ μ) {c : ℝ} (hc : 0 < c) :
    eLpNorm (dilate c Φ) 1 μ = eLpNorm Φ 1 μ := by
  rw [eLpNorm_one_eq_lintegral_eNorm (integrable_dilate hΦ hc.ne').aestronglyMeasurable,
    eLpNorm_one_eq_lintegral_eNorm hΦ.aestronglyMeasurable, lintegral_enorm_dilate Φ hc]

/-- **Convolution with a dilation**: `(Φ_c ⋆ f)(x) = ∫ Φ(z) f(x - c^(-1) z) dz` for `c > 0`
(substitute `y = c^(-1) z`, Mathlib's `Measure.integral_comp_smul`). -/
theorem conv_dilate_apply (Φ f : V → ℂ) {c : ℝ} (hc : 0 < c) (x : V) :
    conv (dilate c Φ) f μ x = ∫ z, Φ z * f (x - c⁻¹ • z) ∂μ := by
  have hpow : (0 : ℝ) < c ^ finrank ℝ V := pow_pos hc _
  rw [conv_apply]
  have h : ∀ y, dilate c Φ y * f (x - y) =
      (((c ^ finrank ℝ V : ℝ)) : ℂ) * (fun z => Φ z * f (x - c⁻¹ • z)) (c • y) := fun y => by
    simp only [dilate, inv_smul_smul₀ hc.ne']
    ring
  simp_rw [h]
  rw [integral_const_mul, Measure.integral_comp_smul μ (fun z => Φ z * f (x - c⁻¹ • z)) c,
    abs_of_pos (inv_pos.2 hpow), Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
    mul_inv_cancel₀ hpow.ne', Complex.ofReal_one, one_mul]

/-! ### Approximate identities -/

/-- **The averaged translates are integrable**: for integrable `Φ`, `f ∈ L_p`, `c > 0` and almost
every `x`, `z ↦ Φ(z) f(x - c^(-1) z)` is integrable; its integral is `(Φ_c ⋆ f)(x)`. -/
theorem ae_integrable_dilate_mul {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {Φ f : V → ℂ}
    (hΦ : Integrable Φ μ) (hf : MemLp f p μ) {c : ℝ} (hc : 0 < c) :
    ∀ᵐ x ∂μ, Integrable (fun z => Φ z * f (x - c⁻¹ • z)) μ := by
  have hpow : (0 : ℝ) < c ^ finrank ℝ V := pow_pos hc _
  filter_upwards [ae_convolutionExistsAt hp1 hp (integrable_dilate hΦ hc.ne') hf] with x hx
  have hx' : Integrable (fun y => dilate c Φ y * f (x - y)) μ := hx
  have h2 := (hx'.comp_smul (inv_ne_zero hc.ne')).const_mul ((((c ^ finrank ℝ V)⁻¹ : ℝ)) : ℂ)
  refine h2.congr (Eventually.of_forall fun z => ?_)
  simp only [dilate, smul_inv_smul₀ hc.ne']
  rw [← mul_assoc, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hpow.ne',
    Complex.ofReal_one, one_mul]

/-- **The local bound of an approximate identity**: for `∫ Φ = 1`, `c > 0` and almost every
`x`, `|(Φ_c ⋆ f)(x) - f(x)| ≤ ∫ |Φ(z)| |f(x - c^(-1) z) - f(x)| dz`. -/
theorem ae_enorm_conv_dilate_sub_le {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {Φ f : V → ℂ}
    (hΦ : Integrable Φ μ) (h1 : ∫ x, Φ x ∂μ = 1) (hf : MemLp f p μ) {c : ℝ} (hc : 0 < c) :
    ∀ᵐ x ∂μ, ‖conv (dilate c Φ) f μ x - f x‖ₑ ≤
      ∫⁻ z, ‖Φ z‖ₑ * ‖f (x - c⁻¹ • z) - f x‖ₑ ∂μ := by
  filter_upwards [ae_integrable_dilate_mul hp1 hp hΦ hf hc] with x hint
  have hconst : Integrable (fun z => Φ z * f x) μ := hΦ.mul_const (f x)
  calc ‖conv (dilate c Φ) f μ x - f x‖ₑ
      = ‖∫ z, (Φ z * f (x - c⁻¹ • z) - Φ z * f x) ∂μ‖ₑ := by
        rw [integral_sub hint hconst, integral_mul_const, h1, one_mul, conv_dilate_apply Φ f hc x]
    _ ≤ ∫⁻ z, ‖Φ z * f (x - c⁻¹ • z) - Φ z * f x‖ₑ ∂μ := eNorm_integral_le_lintegral_eNorm _
    _ = ∫⁻ z, ‖Φ z‖ₑ * ‖f (x - c⁻¹ • z) - f x‖ₑ ∂μ := by
        congr 1
        funext z
        rw [← mul_sub, eNorm_mul]

/-- **The `L_p` distance of an approximate identity**: for an integrable `Φ` with `∫ Φ = 1`, a
strongly measurable `g ∈ L_p` and `c > 0`,
`‖Φ_c ⋆ g - g‖_p ≤ (‖Φ‖_1^(p-1) ∫ |Φ(z)| ‖g(· - c^(-1) z) - g‖_p^p dz)^(1/p)`, by the local bound
`Rd.ae_enorm_conv_dilate_sub_le`, the weighted Jensen inequality and Tonelli's theorem. -/
theorem eLpNorm_conv_dilate_sub_le {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {Φ g : V → ℂ}
    (hΦ : Integrable Φ μ) (h1 : ∫ x, Φ x ∂μ = 1) (hgm : StronglyMeasurable g)
    (hg : MemLp g p μ) {c : ℝ} (hc : 0 < c) :
    eLpNorm (conv (dilate c Φ) g μ - g) p μ ≤
      ((∫⁻ z, ‖Φ z‖ₑ ∂μ) ^ (p.toReal - 1) *
        ∫⁻ z, ‖Φ z‖ₑ * eLpNorm (fun x => g (x - c⁻¹ • z) - g x) p μ ^ p.toReal ∂μ) ^
          (1 / p.toReal) := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp1).ne'
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hq1 : 1 ≤ p.toReal := ENNReal.one_le_toReal_of_one_le hp1 hp
  set q := p.toReal
  have hgmeas : Measurable g := hgm.measurable
  have hconvm : AEStronglyMeasurable (conv (dilate c Φ) g μ - g) μ :=
    (aestronglyMeasurable_conv (integrable_dilate hΦ hc.ne').aestronglyMeasurable
      hg.aestronglyMeasurable).sub hgm.aestronglyMeasurable
  refine eLpNorm_le_of_lintegral_le hconvm hp0 hp ?_
  rw [← ENNReal.rpow_mul, one_div_mul_cancel hq.ne', ENNReal.rpow_one]
  have hprod : AEMeasurable (Function.uncurry fun x z =>
      ‖Φ z‖ₑ * ‖g (x - c⁻¹ • z) - g x‖ₑ ^ q) (μ.prod μ) :=
    hΦ.aestronglyMeasurable.eNorm.comp_snd.mul
      (((hgmeas.comp (measurable_fst.sub (measurable_snd.const_smul c⁻¹))).sub
        (hgmeas.comp measurable_fst)).eNorm.pow_const q).aemeasurable
  calc ∫⁻ x, ‖(conv (dilate c Φ) g μ - g) x‖ₑ ^ q ∂μ
      ≤ ∫⁻ x, (∫⁻ z, ‖Φ z‖ₑ * ‖g (x - c⁻¹ • z) - g x‖ₑ ∂μ) ^ q ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_enorm_conv_dilate_sub_le hp1 hp hΦ h1 hg hc] with x hx
        exact ENNReal.rpow_le_rpow hx hq.le
    _ ≤ ∫⁻ x, (∫⁻ z, ‖Φ z‖ₑ ∂μ) ^ (q - 1) *
          ∫⁻ z, ‖Φ z‖ₑ * ‖g (x - c⁻¹ • z) - g x‖ₑ ^ q ∂μ ∂μ :=
        lintegral_mono fun x => lintegral_mul_rpow_le hq1 hΦ.aestronglyMeasurable.eNorm
          ((hgmeas.comp (measurable_const.sub (measurable_id.const_smul c⁻¹))).sub
            measurable_const).eNorm.aemeasurable
    _ = (∫⁻ z, ‖Φ z‖ₑ ∂μ) ^ (q - 1) *
          ∫⁻ x, ∫⁻ z, ‖Φ z‖ₑ * ‖g (x - c⁻¹ • z) - g x‖ₑ ^ q ∂μ ∂μ :=
        lintegral_const_mul'' _ hprod.lintegral_prod_right'
    _ = (∫⁻ z, ‖Φ z‖ₑ ∂μ) ^ (q - 1) *
          ∫⁻ z, ∫⁻ x, ‖Φ z‖ₑ * ‖g (x - c⁻¹ • z) - g x‖ₑ ^ q ∂μ ∂μ := by
        rw [lintegral_lintegral_swap hprod]
    _ = _ := by
        congr 1
        refine lintegral_congr fun z => ?_
        have hm : Measurable fun x => ‖g (x - c⁻¹ • z) - g x‖ₑ ^ q :=
          ((hgmeas.comp (measurable_id.sub_const _)).sub hgmeas).eNorm.pow_const q
        have hsm : AEStronglyMeasurable (fun x => g (x - c⁻¹ • z) - g x) μ :=
          ((hgm.comp_measurable (measurable_id.sub_const _)).sub hgm).aestronglyMeasurable
        rw [lintegral_const_mul _ hm]
        congr 1
        exact (eLpNorm_rpow_eq hsm hp0 hp).symm

/-- **Approximate identities in `L_p`**: for an integrable `Φ` with `∫ Φ = 1` and `f ∈ L_p`,
`1 ≤ p < ∞`, `‖Φ_c ⋆ f - f‖_p → 0` as `c → ∞`. -/
theorem tendsto_eLpNorm_conv_dilate_sub {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) {Φ f : V → ℂ}
    (hΦ : Integrable Φ μ) (h1 : ∫ x, Φ x ∂μ = 1) (hf : MemLp f p μ) :
    Tendsto (fun c : ℝ => eLpNorm (conv (dilate c Φ) f μ - f) p μ) atTop (𝓝 0) := by
  -- reduce to a strongly measurable representative of `f`
  obtain ⟨g, hgm, hfg⟩ := hf.aestronglyMeasurable
  have hg : MemLp g p μ := hf.ae_eq hfg
  have hcong : ∀ c : ℝ, eLpNorm (conv (dilate c Φ) f μ - f) p μ =
      eLpNorm (conv (dilate c Φ) g μ - g) p μ := fun c => by
    rw [conv_congr_ae hfg]
    exact eLpNorm_congr_ae ((Filter.EventuallyEq.refl _ _).sub hfg)
  simp_rw [hcong]
  have hp1 : 1 ≤ p := Fact.out
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp1).ne'
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hq1 : 1 ≤ p.toReal := ENNReal.one_le_toReal_of_one_le hp1 hp
  set q := p.toReal
  set T : V → ℝ≥0∞ := fun w => eLpNorm (fun x => g (x - w) - g x) p μ
  have hT : Continuous T := continuous_eLpNorm_comp_sub_sub hp hg
  have hT0 : T 0 = 0 := by simp [T]
  have hΦ1 : ∫⁻ z, ‖Φ z‖ₑ ∂μ ≠ ∞ := hΦ.2.ne
  -- the bound for `c > 0`
  set I : ℝ → ℝ≥0∞ := fun c => ∫⁻ z, ‖Φ z‖ₑ * T (c⁻¹ • z) ^ q ∂μ
  have hbound : ∀ c : ℝ, 0 < c → eLpNorm (conv (dilate c Φ) g μ - g) p μ ≤
      ((∫⁻ z, ‖Φ z‖ₑ ∂μ) ^ (q - 1) * I c) ^ (1 / q) := fun c hc =>
    eLpNorm_conv_dilate_sub_le hp1 hp hΦ h1 hgm hg hc
  -- dominated convergence for `I`
  have hI : Tendsto I atTop (𝓝 0) := by
    have hlim := tendsto_lintegral_filter_of_dominated_convergence'
      (μ := μ) (l := atTop) (F := fun (c : ℝ) z => ‖Φ z‖ₑ * T (c⁻¹ • z) ^ q)
      (f := fun _ => 0) (fun z => ‖Φ z‖ₑ * (2 * eLpNorm g p μ) ^ q)
      (Eventually.of_forall fun c => hΦ.aestronglyMeasurable.eNorm.mul
        ((hT.measurable.comp (measurable_const_smul c⁻¹)).pow_const q).aemeasurable)
      (Eventually.of_forall fun c => Eventually.of_forall fun z => by
        gcongr
        calc T (c⁻¹ • z) ≤ eLpNorm (fun x => g (x - c⁻¹ • z)) p μ + eLpNorm g p μ :=
              eLpNorm_sub_le hp1
          _ = 2 * eLpNorm g p μ := by
              rw [eLpNorm_comp_sub_right hgm.aestronglyMeasurable, two_mul])
      (by
        rw [lintegral_mul_const'' _ hΦ.aestronglyMeasurable.eNorm]
        exact ENNReal.mul_ne_top hΦ1 (ENNReal.rpow_ne_top_of_nonneg hq.le
          (ENNReal.mul_ne_top (by simp) hg.eLpNorm_ne_top)))
      (Eventually.of_forall fun z => by
        have h0 : Tendsto (fun c : ℝ => c⁻¹ • z) atTop (𝓝 0) := by
          have := (tendsto_inv_atTop_zero (𝕜 := ℝ)).smul_const z
          rwa [zero_smul ℝ z] at this
        have h2 : Tendsto (fun c : ℝ => T (c⁻¹ • z)) atTop (𝓝 0) := by
          have := (hT.tendsto 0).comp h0
          rwa [hT0] at this
        have h1' : Tendsto (fun c : ℝ => T (c⁻¹ • z) ^ q) atTop (𝓝 0) := by
          have := ((ENNReal.continuous_rpow_const (y := q)).tendsto 0).comp h2
          rwa [ENNReal.zero_rpow_of_pos hq] at this
        have := ENNReal.Tendsto.const_mul (a := ‖Φ z‖ₑ) h1' (Or.inr eNorm_ne_top)
        rwa [mul_zero] at this)
    rwa [lintegral_zero] at hlim
  -- conclusion
  have hlim2 : Tendsto (fun c => ((∫⁻ z, ‖Φ z‖ₑ ∂μ) ^ (q - 1) * I c) ^ (1 / q)) atTop (𝓝 0) := by
    have h3 : Tendsto (fun c => (∫⁻ z, ‖Φ z‖ₑ ∂μ) ^ (q - 1) * I c) atTop (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul (a := (∫⁻ z, ‖Φ z‖ₑ ∂μ) ^ (q - 1)) hI
        (Or.inr (ENNReal.rpow_ne_top_of_nonneg (by linarith) hΦ1))
      rwa [mul_zero] at this
    have := ((ENNReal.continuous_rpow_const (y := 1 / q)).tendsto 0).comp h3
    rwa [ENNReal.zero_rpow_of_pos (one_div_pos.2 hq)] at this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim2
    (Eventually.of_forall fun _ => zero_le)
    ((eventually_gt_atTop 0).mono fun c hc => hbound c hc)

/-- **Approximate identities as operators on `L_p`**: for an integrable `Φ` with `∫ Φ = 1`,
dilation factors `c_i ≠ 0` with `c_i → ∞` and `f ∈ L_p`, `1 ≤ p < ∞`, `Φ_{c_i} ⋆ f → f` in `L_p`
(Mathlib's `Lp.tendsto_Lp_iff_tendsto_eLpNorm'`). -/
theorem tendsto_convLp_dilate {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) {Φ : V → ℂ}
    (hΦ : Integrable Φ μ) (h1 : ∫ x, Φ x ∂μ = 1) {ι : Type*} {l : Filter ι} {c : ι → ℝ}
    (hc : ∀ i, c i ≠ 0) (hcl : Tendsto c l atTop) (f : Lp ℂ p μ) :
    Tendsto (fun i => convLp hp (integrable_dilate hΦ (hc i)) f) l (𝓝 f) := by
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  refine ((tendsto_eLpNorm_conv_dilate_sub hp hΦ h1 (Lp.memLp f)).comp hcl).congr fun i => ?_
  exact eLpNorm_congr_ae ((convLp_apply_ae hp _ f).sub (Filter.EventuallyEq.refl _ _)).symm

end Rd

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- **Uniformly bounded operators applied twice**: if additive maps `T_i : E → E` satisfy
`‖T_i g‖ ≤ C ‖g‖` for all `i` and `g`, and `T_i f → f`, then `T_i (T_i f) → f`, since
`T_i (T_i f) - f = T_i (T_i f - f) + (T_i f - f)` has norm at most `(C + 1) ‖T_i f - f‖`. -/
theorem tendsto_apply_apply_of_tendsto {ι E F : Type*} [SeminormedAddCommGroup E] [FunLike F E E]
    [AddMonoidHomClass F E E] {l : Filter ι} {T : ι → F} {C : ℝ} (hT : ∀ i g, ‖T i g‖ ≤ C * ‖g‖)
    {f : E} (h : Tendsto (fun i => T i f) l (𝓝 f)) : Tendsto (fun i => T i (T i f)) l (𝓝 f) := by
  rw [tendsto_iff_norm_sub_tendsto_zero] at h ⊢
  refine squeeze_zero (fun i => norm_nonneg _) (fun i => ?_) (by simpa using h.const_mul (C + 1))
  calc ‖T i (T i f) - f‖ = ‖T i (T i f - f) + (T i f - f)‖ := by
        rw [map_sub]
        congr 1
        abel
    _ ≤ C * ‖T i f - f‖ + ‖T i f - f‖ := (norm_add_le _ _).trans (add_le_add (hT i _) le_rfl)
    _ = (C + 1) * ‖T i f - f‖ := by ring

/-! ### Approximate identities at points of continuity -/

/-- **Approximate identities at points of continuity**: if `Φ` is integrable with `∫ Φ = 1` and
vanishes outside `closedBall(0, R)`, and `F_J(z) → z₀` as `J → ∞` and `z → y`, then
`(Φ_{2^J} ⋆ F_J)(z) → z₀` as `J → ∞` and `z → y`: for every `ε > 0` there are `J₀` and `δ > 0`
with `|(Φ_{2^J} ⋆ F_J)(z) - z₀| < ε` for `J ≥ J₀` and `‖z - y‖ < δ`. Since `∫ Φ_{2^J} = 1`,
`(Φ_{2^J} ⋆ F_J)(z) - z₀ = ∫ Φ_{2^J}(w) (F_J(z - w) - z₀) dw`, and only `‖w‖ ≤ R 2^(-J)` enters. -/
theorem conv_dilate_near {Φ : V → ℂ} (hΦ : Integrable Φ) (h1 : ∫ x, Φ x = 1) {R : ℝ}
    (hR : 0 ≤ R) (hΦR : ∀ w, R < ‖w‖ → Φ w = 0) {F : ℕ → V → ℂ}
    (hFm : ∀ J, AEStronglyMeasurable (F J) volume) {y : V} {z₀ : ℂ}
    (hF : ∀ ε > 0, ∃ J₀ : ℕ, ∃ δ > 0, ∀ J ≥ J₀, ∀ z, ‖z - y‖ < δ → ‖F J z - z₀‖ < ε) :
    ∀ ε > 0, ∃ J₀ : ℕ, ∃ δ > 0, ∀ J ≥ J₀, ∀ z, ‖z - y‖ < δ →
      ‖conv (dilate (2 ^ J) Φ) (F J) volume z - z₀‖ < ε := by
  intro ε hε
  have hM : 0 ≤ ∫ x, ‖Φ x‖ := integral_nonneg fun _ => norm_nonneg _
  obtain ⟨J₁, δ₁, hδ₁, hJ₁⟩ := hF (ε / ((∫ x, ‖Φ x‖) + 1)) (by positivity)
  obtain ⟨J₂, hJ₂⟩ := pow_unbounded_of_one_lt (2 * R / δ₁) (one_lt_two : (1 : ℝ) < 2)
  have hJ₂' : ∀ J ≥ J₂, R / 2 ^ J < δ₁ / 2 := fun J hJ => by
    have h2 : (2 : ℝ) ^ J₂ ≤ 2 ^ J := pow_le_pow_right₀ one_le_two hJ
    rw [div_lt_div_iff₀ (by positivity) two_pos]
    rw [div_lt_iff₀ hδ₁] at hJ₂
    nlinarith
  refine ⟨max J₁ J₂, δ₁ / 2, half_pos hδ₁, fun J hJ z hz => ?_⟩
  have hJ1 : J₁ ≤ J := le_of_max_le_left hJ
  have hJ2 : J₂ ≤ J := le_of_max_le_right hJ
  have hΦ' : Integrable (dilate ((2 : ℝ) ^ J) Φ) := integrable_dilate hΦ (by positivity)
  have hsupp : ∀ w, dilate ((2 : ℝ) ^ J) Φ w ≠ 0 → ‖w‖ < δ₁ / 2 := fun w hw => by
    by_contra hcon
    push Not at hcon
    apply hw
    rw [dilate, hΦR _ ?_, mul_zero]
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    have h3 := hJ₂' J hJ2
    rw [div_lt_iff₀ (by positivity)] at h3
    nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) J]
  have hpt : ∀ w, ‖dilate ((2 : ℝ) ^ J) Φ w * (F J (z - w) - z₀)‖ ≤
      ‖dilate ((2 : ℝ) ^ J) Φ w‖ * (ε / ((∫ x, ‖Φ x‖) + 1)) := fun w => by
    by_cases hw : dilate ((2 : ℝ) ^ J) Φ w = 0
    · simp [hw]
    · rw [norm_mul]
      refine mul_le_mul_of_nonneg_left (hJ₁ J hJ1 (z - w) ?_).le (norm_nonneg _)
      calc ‖z - w - y‖ = ‖(z - y) - w‖ := by congr 1; abel
        _ ≤ ‖z - y‖ + ‖w‖ := norm_sub_le _ _
        _ < δ₁ / 2 + δ₁ / 2 := add_lt_add hz (hsupp w hw)
        _ = δ₁ := by ring
  have hmeas : AEStronglyMeasurable (fun w => F J (z - w)) volume :=
    (hFm J).comp_measurePreserving (Measure.measurePreserving_sub_left volume z)
  have hint1 : Integrable (fun w => dilate ((2 : ℝ) ^ J) Φ w * (F J (z - w) - z₀)) volume :=
    Integrable.mono' (hΦ'.norm.mul_const _)
      (hΦ'.aestronglyMeasurable.mul (hmeas.sub aestronglyMeasurable_const))
      (Eventually.of_forall hpt)
  have hint2 : Integrable (fun w => dilate ((2 : ℝ) ^ J) Φ w * F J (z - w)) volume :=
    (hint1.add (hΦ'.mul_const z₀)).congr (Eventually.of_forall fun w => by
      simp only [Pi.add_apply]
      ring)
  have hone : ∫ w, dilate ((2 : ℝ) ^ J) Φ w = 1 := by
    rw [integral_dilate Φ (by positivity), h1]
  have hkey : conv (dilate (2 ^ J) Φ) (F J) volume z - z₀ =
      ∫ w, dilate ((2 : ℝ) ^ J) Φ w * (F J (z - w) - z₀) := by
    rw [conv_apply]
    calc (∫ w, dilate ((2 : ℝ) ^ J) Φ w * F J (z - w)) - z₀
        = (∫ w, dilate ((2 : ℝ) ^ J) Φ w * F J (z - w)) -
            ∫ w, dilate ((2 : ℝ) ^ J) Φ w * z₀ := by
          rw [integral_mul_const, hone, one_mul]
      _ = ∫ w, (dilate ((2 : ℝ) ^ J) Φ w * F J (z - w) - dilate ((2 : ℝ) ^ J) Φ w * z₀) :=
          (integral_sub hint2 (hΦ'.mul_const z₀)).symm
      _ = _ := by
          congr 1
          funext w
          ring
  have hnorm : ∫ w, ‖dilate ((2 : ℝ) ^ J) Φ w‖ = ∫ x, ‖Φ x‖ := by
    rw [integral_norm_eq_lintegral_eNorm hΦ'.aestronglyMeasurable,
      integral_norm_eq_lintegral_eNorm hΦ.aestronglyMeasurable,
      ← eLpNorm_one_eq_lintegral_eNorm hΦ'.aestronglyMeasurable,
      ← eLpNorm_one_eq_lintegral_eNorm hΦ.aestronglyMeasurable,
      eLpNorm_dilate_one hΦ (by positivity)]
  rw [hkey]
  calc ‖∫ w, dilate ((2 : ℝ) ^ J) Φ w * (F J (z - w) - z₀)‖
      ≤ ∫ w, ‖dilate ((2 : ℝ) ^ J) Φ w‖ * (ε / ((∫ x, ‖Φ x‖) + 1)) :=
        norm_integral_le_of_norm_le (hΦ'.norm.mul_const _) (Eventually.of_forall hpt)
    _ = (∫ x, ‖Φ x‖) * ε / ((∫ x, ‖Φ x‖) + 1) := by
        rw [integral_mul_const, hnorm]
        ring
    _ < ε := by
        rw [div_lt_iff₀ (by positivity)]
        nlinarith

/-! ### First moments of dilates -/

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- `⟪w, x⟫ m_c(x) = c⁻¹ (⟪w, ·⟫ m)_c(x)` for `c ≠ 0`. -/
theorem inner_mul_dilate_eq (m : V → ℂ) (w : V) {c : ℝ} (hc : c ≠ 0) (x : V) :
    (inner ℝ w x : ℂ) * dilate c m x =
      ((c⁻¹ : ℝ) : ℂ) * dilate c (fun y => (inner ℝ w y : ℂ) * m y) x := by
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  simp only [dilate, inner_smul_right, Complex.ofReal_mul, Complex.ofReal_inv]
  field_simp

/-- **First moments of a dilate**: `∫ ⟪w, x⟫ m_c(x) dx = c⁻¹ ∫ ⟪w, x⟫ m(x) dx` for `c > 0`
and every additive Haar measure, since `⟪w, x⟫ m_c(x) = c⁻¹ (⟪w, ·⟫ m)_c(x)`
(`Rd.inner_mul_dilate_eq`, `Rd.integral_dilate`). -/
theorem integral_inner_mul_dilate {μ : Measure V} [μ.IsAddHaarMeasure] (m : V → ℂ) (w : V) {c : ℝ}
    (hc : 0 < c) :
    ∫ x, (inner ℝ w x : ℂ) * dilate c m x ∂μ =
      ((c⁻¹ : ℝ) : ℂ) * ∫ x, (inner ℝ w x : ℂ) * m x ∂μ := by
  simp_rw [inner_mul_dilate_eq m w hc.ne']
  rw [integral_const_mul, integral_dilate _ hc]

end Rd
