/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Rd.Differences.DilatedDifferences
public import LeanPool.FunctionSpaces.Rd.Approximation.BandLimited
public import LeanPool.FunctionSpaces.ApproximationSpaces.Sequences.Lq

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The inverse inequality for band-limited functions

For a band-limited `a ∈ E_j`, `a = Θ_j ⋆ a`, so every difference of `a` is the convolution of `a`
with a difference of the kernel: `Δ_h^r a = (Δ_h^r Θ_j) ⋆ a` (`Rd.higherDiff_conv_ae`). By Young's
inequality and the dilation `Δ_h^r Θ_j = (Δ_{2^j h}^r Θ)_{2^j}` (`Rd.higherDiff_dilate`),

`‖Δ_h^r a‖_p ≤ ‖Δ_{2^j h}^r Θ‖_1 ‖a‖_p`.

**Differences of Schwartz functions in `L_p`** (`Rd.lintegral_enorm_fwdDiff_rpow_le`):
`‖Δ_v G‖_p ≤ ‖∂_v G‖_p` for `1 ≤ p < ∞`. The fundamental theorem of calculus along the segment
from `x` to `x + v` gives `G(x + v) - G(x) = ∫_0^1 ∂_v G(x + t v) dt`
(`Rd.fwdDiff_schwartz_eq_integral`); Jensen's inequality on `(0, 1]` (`Rd.rpow_lintegral_Ioc_le`)
and Tonelli's theorem with the translation invariance of Lebesgue measure
(`Rd.lintegral_lintegral_Ioc_add_smul`) give the bound, with the cases `p = 1` and `p = 2`
(`Rd.lintegral_enorm_fwdDiff_le`, `Rd.eLpNorm_fwdDiff_schwartz_le`). The difference
`Δ_v f = f(· + v) - f` is a bounded operator on `L_2` (`Rd.fwdDiffL2`).

**Higher differences in `L_1`** (`Rd.lintegral_enorm_higherDiff_schwartz_le`):
`‖Δ_v^r G‖_1 ≤ ‖v‖^r ‖D^r G‖_1`. Differences commute with line derivatives
(`Rd.lineDerivOp_fwdDiffSchwartz`), so induction gives `‖Δ_v^r G‖_1 ≤ ‖∂_v^r G‖_1`, and
`|∂_v^r G(x)| ≤ ‖v‖^r ‖D^r G(x)‖`. Mathlib's Schwartz space provides the translations, the line
derivatives `∂_v` and the integrability of all derivatives.

**The inverse inequality** (`Rd.lpModulus_le_of_mem_bandSpace`): for `a ∈ E_j`,
`ω_r(a, 2^(-k))_p ≤ C 2^(-(k-j) r) ‖a‖_p` with `C = 2^r + ‖D^r Θ‖_1` (for `k < j` the bound
`ω_r ≤ 2^r ‖a‖_p` is used).
-/

@[expose] public section

open MeasureTheory Filter Topology Module
open scoped ENNReal SchwartzMap LineDeriv

namespace Rd

open ENNReal (dyadicWeight)

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### Differences of Schwartz functions -/

/-- The forward difference `G ↦ G(· + v) - G` as an operator on Schwartz functions. -/
noncomputable def fwdDiffSchwartz (v : V) : 𝓢(V, ℂ) →L[ℝ] 𝓢(V, ℂ) :=
  SchwartzMap.compSubConstCLM ℝ (-v) - ContinuousLinearMap.id ℝ _

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The Schwartz forward difference is the forward difference. -/
theorem coe_fwdDiffSchwartz (v : V) (G : 𝓢(V, ℂ)) :
    (fwdDiffSchwartz v G : V → ℂ) = fwdDiff v G := by
  funext x
  simp [fwdDiffSchwartz, fwdDiff, sub_neg_eq_add]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **Differences commute with line derivatives**: `∂_u (Δ_v G) = Δ_v (∂_u G)`. -/
theorem lineDerivOp_fwdDiffSchwartz (u v : V) (G : 𝓢(V, ℂ)) :
    ∂_{u} (fwdDiffSchwartz v G) = fwdDiffSchwartz v (∂_{u} G) := by
  ext x
  have hcoe : ((fwdDiffSchwartz v G : 𝓢(V, ℂ)) : V → ℂ) = fun y => G (y + v) - G y :=
    coe_fwdDiffSchwartz v G
  have hd : DifferentiableAt ℝ (fun y => G (y + v)) x :=
    G.differentiableAt.comp x (differentiableAt_id.add_const v)
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, hcoe, fderiv_fun_sub hd G.differentiableAt,
    fderiv_comp_add_right, coe_fwdDiffSchwartz, fwdDiff, SchwartzMap.lineDerivOp_apply_eq_fderiv,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]
  rfl

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- Iterated line derivatives commute with differences. -/
theorem iteratedLineDerivOp_fwdDiffSchwartz (v : V) (r : ℕ) (G : 𝓢(V, ℂ)) :
    ∂^{fun _ : Fin r => v} (fwdDiffSchwartz v G) =
      fwdDiffSchwartz v (∂^{fun _ : Fin r => v} G) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [LineDeriv.iteratedLineDerivOp_succ_left, LineDeriv.iteratedLineDerivOp_succ_left]
    exact (congrArg _ ih).trans (lineDerivOp_fwdDiffSchwartz v v _)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **The fundamental theorem of calculus along a segment**: for a Schwartz function `G`,
`G(x + v) - G(x) = ∫_0^1 ∂_v G(x + t v) dt` (Mathlib's
`intervalIntegral.integral_eq_sub_of_hasDerivAt`). -/
theorem fwdDiff_schwartz_eq_integral (v : V) (G : 𝓢(V, ℂ)) (x : V) :
    fwdDiff v (G : V → ℂ) x = ∫ t in (0 : ℝ)..1, (∂_{v} G : 𝓢(V, ℂ)) (x + t • v) := by
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => G (x + t • v))
      ((∂_{v} G : 𝓢(V, ℂ)) (x + t • v)) t := fun t _ => by
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    have h1 : HasDerivAt (fun t : ℝ => x + t • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add x
    exact (G.hasFDerivAt (x + t • v)).comp_hasDerivAt t h1
  have hcont : Continuous fun t : ℝ => (∂_{v} G : 𝓢(V, ℂ)) (x + t • v) :=
    (SchwartzMap.continuous _).comp (continuous_const.add (continuous_id.smul continuous_const))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable 0 1)]
  simp [fwdDiff]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **A difference by the line derivative, pointwise**: for a Schwartz function `G`,
`|G(x + v) - G(x)| ≤ ∫_0^1 |∂_v G(x + t v)| dt` (`Rd.fwdDiff_schwartz_eq_integral`). -/
theorem enorm_fwdDiff_schwartz_le_lintegral (v : V) (G : 𝓢(V, ℂ)) (x : V) :
    ‖fwdDiff v (G : V → ℂ) x‖ₑ ≤
      ∫⁻ t in Set.Ioc (0 : ℝ) 1, ‖(∂_{v} G : 𝓢(V, ℂ)) (x + t • v)‖ₑ := by
  rw [fwdDiff_schwartz_eq_integral, intervalIntegral.integral_of_le zero_le_one]
  exact eNorm_integral_le_lintegral_eNorm _

/-- **Averages of translates along a segment**: for a measurable `φ : V → [0, ∞]` and `v ∈ V`,
`∫_V ∫_0^1 φ(x + t v) dt dx = ∫_V φ`, by Tonelli's theorem (Mathlib's `lintegral_lintegral_swap`)
and the translation invariance of Lebesgue measure. -/
theorem lintegral_lintegral_Ioc_add_smul {φ : V → ℝ≥0∞} (hφ : Measurable φ) (v : V) :
    ∫⁻ x, ∫⁻ t in Set.Ioc (0 : ℝ) 1, φ (x + t • v) = ∫⁻ x, φ x := by
  have hmeas : Measurable (Function.uncurry fun (x : V) (t : ℝ) => φ (x + t • v)) :=
    hφ.comp (continuous_fst.add (continuous_snd.smul continuous_const)).measurable
  calc ∫⁻ x, ∫⁻ t in Set.Ioc (0 : ℝ) 1, φ (x + t • v)
      = ∫⁻ t in Set.Ioc (0 : ℝ) 1, ∫⁻ x, φ (x + t • v) :=
        lintegral_lintegral_swap hmeas.aemeasurable
    _ = ∫⁻ _t in Set.Ioc (0 : ℝ) 1, ∫⁻ x, φ x :=
        lintegral_congr fun t => lintegral_add_right_eq_self φ (t • v)
    _ = ∫⁻ x, φ x := by
        rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero,
          ENNReal.ofReal_one, mul_one]

/-- **Jensen's inequality on the unit interval**: `(∫_0^1 φ)^p ≤ ∫_0^1 φ^p` for real `p ≥ 1` and
measurable `φ ≥ 0`. This is the weighted Jensen inequality `MeasureTheory.lintegral_mul_rpow_le`
with the weight `1`, since `(0, 1]` has length `1`. -/
theorem rpow_lintegral_Ioc_le {p : ℝ} (hp : 1 ≤ p) {φ : ℝ → ℝ≥0∞}
    (hφ : AEMeasurable φ (volume.restrict (Set.Ioc (0 : ℝ) 1))) :
    (∫⁻ t in Set.Ioc (0 : ℝ) 1, φ t) ^ p ≤ ∫⁻ t in Set.Ioc (0 : ℝ) 1, φ t ^ p := by
  have h := lintegral_mul_rpow_le (μ := volume.restrict (Set.Ioc (0 : ℝ) 1)) hp
    (a := fun _ => 1) aemeasurable_const hφ
  simpa only [one_mul, lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero,
    ENNReal.ofReal_one, ENNReal.one_rpow] using h

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **A difference by the line derivative, pointwise, in `p`-th powers**: for a Schwartz function
`G` and real `p ≥ 1`, `|G(x + v) - G(x)|^p ≤ ∫_0^1 |∂_v G(x + t v)|^p dt`
(`Rd.enorm_fwdDiff_schwartz_le_lintegral` and Jensen's inequality `Rd.rpow_lintegral_Ioc_le`). -/
theorem enorm_fwdDiff_schwartz_rpow_le {p : ℝ} (hp : 1 ≤ p) (v : V) (G : 𝓢(V, ℂ)) (x : V) :
    ‖fwdDiff v (G : V → ℂ) x‖ₑ ^ p ≤
      ∫⁻ t in Set.Ioc (0 : ℝ) 1, ‖(∂_{v} G : 𝓢(V, ℂ)) (x + t • v)‖ₑ ^ p := by
  have hcont : Continuous fun t : ℝ => (∂_{v} G : 𝓢(V, ℂ)) (x + t • v) :=
    (SchwartzMap.continuous _).comp (continuous_const.add (continuous_id.smul continuous_const))
  exact (ENNReal.rpow_le_rpow (enorm_fwdDiff_schwartz_le_lintegral v G x) (by linarith)).trans
    (rpow_lintegral_Ioc_le hp hcont.eNorm.aemeasurable)

/-- **A difference is bounded by the line derivative in `L_p`**: for a Schwartz function `G` and
real `p ≥ 1`, `∫ |Δ_v G|^p ≤ ∫ |∂_v G|^p`, that is `‖Δ_v G‖_p ≤ ‖∂_v G‖_p`. Integrate the
pointwise bound `Rd.enorm_fwdDiff_schwartz_rpow_le` over `x` and use
`Rd.lintegral_lintegral_Ioc_add_smul`. -/
theorem lintegral_enorm_fwdDiff_rpow_le {p : ℝ} (hp : 1 ≤ p) (v : V) (G : 𝓢(V, ℂ)) :
    ∫⁻ x, ‖fwdDiff v (G : V → ℂ) x‖ₑ ^ p ≤ ∫⁻ x, ‖(∂_{v} G : 𝓢(V, ℂ)) x‖ₑ ^ p :=
  (lintegral_mono fun x => enorm_fwdDiff_schwartz_rpow_le hp v G x).trans_eq
    (lintegral_lintegral_Ioc_add_smul (φ := fun y => ‖(∂_{v} G : 𝓢(V, ℂ)) y‖ₑ ^ p)
      ((SchwartzMap.continuous _).eNorm.measurable.pow_const p) v)

/-- **A difference is bounded by the line derivative in `L_1`**: `‖Δ_v G‖_1 ≤ ‖∂_v G‖_1` for a
Schwartz function `G`, the case `p = 1` of `Rd.lintegral_enorm_fwdDiff_rpow_le`. -/
theorem lintegral_enorm_fwdDiff_le (v : V) (G : 𝓢(V, ℂ)) :
    ∫⁻ x, ‖fwdDiff v (G : V → ℂ) x‖ₑ ≤ ∫⁻ x, ‖(∂_{v} G : 𝓢(V, ℂ)) x‖ₑ := by
  simpa using lintegral_enorm_fwdDiff_rpow_le le_rfl v G

/-- **A difference is bounded by the line derivative in `L_2`**: `‖Δ_v G‖_2 ≤ ‖∂_v G‖_2` for a
Schwartz function `G`, the case `p = 2` of `Rd.lintegral_enorm_fwdDiff_rpow_le` (Mathlib's
`MeasureTheory.eLpNorm_le_of_lintegral_le` for the `L_2` norm). -/
theorem eLpNorm_fwdDiff_schwartz_le (v : V) (G : 𝓢(V, ℂ)) :
    eLpNorm (fwdDiff v (G : V → ℂ)) 2 volume ≤
      eLpNorm ((∂_{v} G : 𝓢(V, ℂ)) : V → ℂ) 2 volume := by
  have hm : AEStronglyMeasurable (fwdDiff v (G : V → ℂ)) volume :=
    ((G.continuous.comp (continuous_id.add continuous_const)).sub G.continuous).aestronglyMeasurable
  refine eLpNorm_le_of_lintegral_le hm two_ne_zero ENNReal.ofNat_ne_top ?_
  rw [eLpNorm_rpow_eq (SchwartzMap.continuous _).aestronglyMeasurable two_ne_zero
    ENNReal.ofNat_ne_top]
  simpa using lintegral_enorm_fwdDiff_rpow_le one_le_two v G

/-! ### The difference operator on `L_2` -/

variable (V) in
/-- **The difference operator on `L_2(V)`**: `Δ_v f = f(· + v) - f`, a bounded linear operator,
the translation by `v` (Mathlib's `MeasureTheory.Lp.compMeasurePreservingₗᵢ`) minus the
identity. -/
noncomputable def fwdDiffL2 (v : V) :
    Lp ℂ 2 (volume : Measure V) →L[ℂ] Lp ℂ 2 (volume : Measure V) :=
  (Lp.compMeasurePreservingₗᵢ ℂ (· + v)
    (measurePreserving_add_right volume v)).toContinuousLinearMap - ContinuousLinearMap.id ℂ _

/-- `Δ_v f` is the forward difference `f(· + v) - f` almost everywhere. -/
theorem fwdDiffL2_ae_eq (v : V) (f : Lp ℂ 2 (volume : Measure V)) :
    fwdDiffL2 V v f =ᵐ[volume] fwdDiff v (f : V → ℂ) := by
  have h1 := Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right volume v)
  have h2 := Lp.coeFn_sub (Lp.compMeasurePreservingₗᵢ ℂ (· + v)
    (measurePreserving_add_right volume v) f) f
  filter_upwards [h1, h2] with x hx1 hx2
  change _ = (f : V → ℂ) (x + v) - f x
  refine hx2.trans ?_
  rw [Pi.sub_apply]
  exact congrArg (· - (f : V → ℂ) x) hx1

/-- `‖Δ_v f‖_2` is the `L_2` norm of the forward difference `f(· + v) - f`
(`Rd.fwdDiffL2_ae_eq`). -/
theorem enorm_fwdDiffL2 (v : V) (f : Lp ℂ 2 (volume : Measure V)) :
    ‖fwdDiffL2 V v f‖ₑ = eLpNorm (fwdDiff v (f : V → ℂ)) 2 volume := by
  rw [Lp.eNorm_def, eLpNorm_congr_ae (fwdDiffL2_ae_eq v f)]

/-- **Differences of Schwartz functions in `L_2(V)`**: `‖Δ_v G‖_2 ≤ ‖∂_v G‖_2`
(`Rd.eLpNorm_fwdDiff_schwartz_le`). -/
theorem enorm_fwdDiffL2_toLp_le (v : V) (G : 𝓢(V, ℂ)) :
    ‖fwdDiffL2 V v (G.toLp 2)‖ₑ ≤ ‖(∂_{v} G : 𝓢(V, ℂ)).toLp 2‖ₑ := by
  have hG : fwdDiff v ((G.toLp 2 : Lp ℂ 2 (volume : Measure V)) : V → ℂ) =ᵐ[volume]
      fwdDiff v (G : V → ℂ) :=
    higherDiff_congr_ae (G.coeFn_toLp 2 volume) 1 v
  rw [enorm_fwdDiffL2, eLpNorm_congr_ae hG, Lp.eNorm_def,
    eLpNorm_congr_ae ((∂_{v} G : 𝓢(V, ℂ)).coeFn_toLp 2 volume)]
  exact eLpNorm_fwdDiff_schwartz_le v G

/-! ### Higher differences of Schwartz functions -/

/-- **Differences of order `r` are bounded by line derivatives of order `r` in `L_1`**:
`‖Δ_v^r G‖_1 ≤ ‖∂_v^r G‖_1`. -/
theorem lintegral_enorm_higherDiff_le (v : V) (r : ℕ) (G : 𝓢(V, ℂ)) :
    ∫⁻ x, ‖(fwdDiff v)^[r] (G : V → ℂ) x‖ₑ ≤
      ∫⁻ x, ‖(∂^{fun _ : Fin r => v} G : 𝓢(V, ℂ)) x‖ₑ := by
  induction r generalizing G with
  | zero => exact le_rfl
  | succ r ih =>
    calc ∫⁻ x, ‖(fwdDiff v)^[r + 1] (G : V → ℂ) x‖ₑ
        = ∫⁻ x, ‖(fwdDiff v)^[r] (fwdDiffSchwartz v G : V → ℂ) x‖ₑ := by
          rw [Function.iterate_succ_apply, ← coe_fwdDiffSchwartz]
      _ ≤ ∫⁻ x, ‖(∂^{fun _ : Fin r => v} (fwdDiffSchwartz v G) : 𝓢(V, ℂ)) x‖ₑ := ih _
      _ = ∫⁻ x, ‖fwdDiff v ((∂^{fun _ : Fin r => v} G : 𝓢(V, ℂ)) : V → ℂ) x‖ₑ := by
          rw [iteratedLineDerivOp_fwdDiffSchwartz, coe_fwdDiffSchwartz]
      _ ≤ ∫⁻ x, ‖(∂_{v} (∂^{fun _ : Fin r => v} G) : 𝓢(V, ℂ)) x‖ₑ :=
          lintegral_enorm_fwdDiff_le v _
      _ = ∫⁻ x, ‖(∂^{fun _ : Fin (r + 1) => v} G : 𝓢(V, ℂ)) x‖ₑ := rfl

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- `|∂_v^r G(x)| ≤ ‖v‖^r ‖D^r G(x)‖`. -/
theorem enorm_iteratedLineDerivOp_le (v : V) (r : ℕ) (G : 𝓢(V, ℂ)) (x : V) :
    ‖(∂^{fun _ : Fin r => v} G : 𝓢(V, ℂ)) x‖ₑ ≤
      ‖v‖ₑ ^ r * ‖iteratedFDeriv ℝ r (G : V → ℂ) x‖ₑ := by
  rw [SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
  have h := (iteratedFDeriv ℝ r (G : V → ℂ) x).le_opNorm (fun _ => v)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  calc ‖iteratedFDeriv ℝ r (G : V → ℂ) x (fun _ => v)‖ₑ
      = ENNReal.ofReal ‖iteratedFDeriv ℝ r (G : V → ℂ) x (fun _ => v)‖ := (ofReal_norm _).symm
    _ ≤ ENNReal.ofReal (‖v‖ ^ r * ‖iteratedFDeriv ℝ r (G : V → ℂ) x‖) :=
        ENNReal.ofReal_le_ofReal (h.trans_eq (mul_comm _ _))
    _ = ‖v‖ₑ ^ r * ‖iteratedFDeriv ℝ r (G : V → ℂ) x‖ₑ := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm,
          ofReal_norm]

/-- **`L_1` norms of differences of Schwartz functions**: `‖Δ_v^r G‖_1 ≤ ‖v‖^r ‖D^r G‖_1`. -/
theorem lintegral_enorm_higherDiff_schwartz_le (v : V) (r : ℕ) (G : 𝓢(V, ℂ)) :
    ∫⁻ x, ‖(fwdDiff v)^[r] (G : V → ℂ) x‖ₑ ≤
      ‖v‖ₑ ^ r * ∫⁻ x, ‖iteratedFDeriv ℝ r (G : V → ℂ) x‖ₑ := by
  calc ∫⁻ x, ‖(fwdDiff v)^[r] (G : V → ℂ) x‖ₑ
      ≤ ∫⁻ x, ‖(∂^{fun _ : Fin r => v} G : 𝓢(V, ℂ)) x‖ₑ := lintegral_enorm_higherDiff_le v r G
    _ ≤ ∫⁻ x, ‖v‖ₑ ^ r * ‖iteratedFDeriv ℝ r (G : V → ℂ) x‖ₑ :=
        lintegral_mono fun x => enorm_iteratedLineDerivOp_le v r G x
    _ = ‖v‖ₑ ^ r * ∫⁻ x, ‖iteratedFDeriv ℝ r (G : V → ℂ) x‖ₑ :=
        lintegral_const_mul' _ _ (ENNReal.pow_ne_top eNorm_ne_top)

/-- The derivatives of a Schwartz function are integrable: `‖D^r G‖_1 < ∞`. -/
theorem lintegral_enorm_iteratedFDeriv_ne_top (r : ℕ) (G : 𝓢(V, ℂ)) :
    ∫⁻ x, ‖iteratedFDeriv ℝ r (G : V → ℂ) x‖ₑ ≠ ∞ := by
  have h := (SchwartzMap.integrable_pow_mul_iteratedFDeriv volume G 0 r).2
  simp only [pow_zero, one_mul, HasFiniteIntegral, eNorm_norm] at h
  exact h.ne

/-! ### The inverse inequality -/

variable (V) in
/-- The constant of the inverse inequality, `2^r + ‖D^r Θ‖_1`. -/
noncomputable def bandInverseConst (r : ℕ) : ℝ≥0∞ :=
  2 ^ r + ∫⁻ x, ‖iteratedFDeriv ℝ r (bandKernelS (V := V) : V → ℂ) x‖ₑ

/-- The constant of the inverse inequality is finite. -/
theorem bandInverseConst_ne_top (r : ℕ) : bandInverseConst V r ≠ ∞ :=
  ENNReal.add_ne_top.2 ⟨by simp, lintegral_enorm_iteratedFDeriv_ne_top r _⟩

/-- **Differences of the band-limiting kernels in `L_1`**: `‖Δ_h^r Θ_j‖_1 ≤ (2^j ‖h‖)^r ‖D^r Θ‖_1`,
by the dilation `Δ_h^r Θ_j = (Δ_{2^j h}^r Θ)_{2^j}`. -/
theorem eLpNorm_higherDiff_Theta_le (r j : ℕ) (h : V) :
    eLpNorm ((fwdDiff h)^[r] (Theta (V := V) j)) 1 volume ≤
      ENNReal.ofReal (2 ^ j * ‖h‖) ^ r *
        ∫⁻ x, ‖iteratedFDeriv ℝ r (bandKernelS (V := V) : V → ℂ) x‖ₑ := by
  have hint : Integrable ((fwdDiff ((2 : ℝ) ^ j • h))^[r] (bandKernel (V := V))) :=
    integrable_higherDiff integrable_bandKernel r _
  rw [Theta, higherDiff_dilate, eLpNorm_dilate_one hint (by positivity),
    eLpNorm_one_eq_lintegral_eNorm hint.aestronglyMeasurable]
  refine (lintegral_enorm_higherDiff_schwartz_le _ r bandKernelS).trans_eq ?_
  rw [← ofReal_norm, norm_smul, Real.norm_of_nonneg (by positivity)]

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The inverse inequality for band-limited functions**: for `a ∈ E_j`,
`ω_r(a, 2^(-k))_p ≤ C 2^(-(k-j) r) ‖a‖_p` with `C = 2^r + ‖D^r Θ‖_1` (and `k - j` truncated at
`0`). For `k ≥ j` and `‖h‖ ≤ 2^(-k)`, `Δ_h^r a = (Δ_h^r Θ_j) ⋆ a` and Young's inequality give
`‖Δ_h^r a‖_p ≤ (2^j ‖h‖)^r ‖D^r Θ‖_1 ‖a‖_p`. -/
theorem lpModulus_le_of_mem_bandSpace (hp : p ≠ ∞) (r : ℕ) {j k : ℕ}
    {a : Lp ℂ p (volume : Measure V)} (ha : a ∈ bandSpace hp j) :
    lpModulus p r a k ≤ bandInverseConst V r * dyadicWeight (-(r : ℝ)) (k - j) * ‖a‖ₑ := by
  rcases lt_or_ge k j with hkj | hjk
  · rw [Nat.sub_eq_zero_of_le hkj.le, ENNReal.dyadicWeight_zero_right, mul_one]
    exact (lpModulus_le r a k).trans (by gcongr; exact le_self_add)
  · rw [mem_bandSpace] at ha
    have hae : (a : V → ℂ) =ᵐ[volume] conv (Theta j) (a : V → ℂ) volume := by
      have h1 := convLp_apply_ae hp (integrable_Theta (V := V) j) a
      rw [ha] at h1
      exact h1
    set D := ∫⁻ x, ‖iteratedFDeriv ℝ r (bandKernelS (V := V) : V → ℂ) x‖ₑ
    rw [lpModulus, modulus_congr_ae hae]
    refine iSup₂_le fun h hh => ?_
    have h1 : eLpNorm ((fwdDiff h)^[r] (conv (Theta j) (a : V → ℂ) volume)) p volume ≤
        eLpNorm ((fwdDiff h)^[r] (Theta (V := V) j)) 1 volume * ‖a‖ₑ := by
      rw [eLpNorm_congr_ae (higherDiff_conv_ae Fact.out hp (integrable_Theta j) (Lp.memLp a) r h),
        Lp.eNorm_def]
      exact eLpNorm_conv_le Fact.out
        (integrable_higherDiff (integrable_Theta j) r h).aestronglyMeasurable
        (Lp.aestronglyMeasurable a)
    have h2 : ENNReal.ofReal (2 ^ j * ‖h‖) ^ r ≤ dyadicWeight (-(r : ℝ)) (k - j) := by
      rw [← ENNReal.rpow_natCast]
      exact ENNReal.ofReal_two_pow_mul_rpow_le hjk hh (Nat.cast_nonneg r)
    calc eLpNorm ((fwdDiff h)^[r] (conv (Theta j) (a : V → ℂ) volume)) p volume
        ≤ ENNReal.ofReal (2 ^ j * ‖h‖) ^ r * D * ‖a‖ₑ :=
          h1.trans (by gcongr; exact eLpNorm_higherDiff_Theta_le r j h)
      _ ≤ dyadicWeight (-(r : ℝ)) (k - j) * D * ‖a‖ₑ := by gcongr
      _ ≤ bandInverseConst V r * dyadicWeight (-(r : ℝ)) (k - j) * ‖a‖ₑ := by
          rw [mul_comm (dyadicWeight _ _) D]
          gcongr
          exact le_add_self

end Rd
