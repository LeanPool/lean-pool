/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Analysis.Fourier.ApproxIdentity
public import LeanPool.FunctionSpaces.Analysis.Differences.Differences

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Differences of convolutions and dilations

Differences commute with convolution and dilation: `Δ_h^r (K ⋆ f) = (Δ_h^r K) ⋆ f` almost
everywhere for an integrable `K` and `f ∈ L_p` (`Rd.higherDiff_conv_ae`), pointwise where
the convolutions with the translates of `K` converge absolutely (`Rd.higherDiff_conv_apply`), and
`Δ_h^r (Φ_c) = (Δ_{ch}^r Φ)_c` (`Rd.higherDiff_dilate`).  Young's inequality then bounds the modulus
of a convolution by the `L_1` norms of the differences of the kernel (`Rd.lpModulus_convLp_le`).
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {μ : Measure V} [μ.IsAddHaarMeasure]

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- **Translates of convolutions**: `(K ⋆ f)(x + c) = (K(· + c) ⋆ f)(x)`, by the substitution
`y ↦ y + c`. -/
theorem conv_comp_add (K f : V → ℂ) (c x : V) :
    conv K f μ (x + c) = conv (fun y => K (y + c)) f μ x := by
  rw [conv_apply, conv_apply, ← integral_add_right_eq_self (fun y => K y * f (x + c - y)) c]
  congr 1
  funext y
  rw [show x + c - (y + c) = x - y by abel]

/-- **Differences of convolutions**: `Δ_h^r (K ⋆ f) = (Δ_h^r K) ⋆ f` almost everywhere, for an
integrable `K` and `f ∈ L_p`, `1 ≤ p < ∞`. -/
theorem higherDiff_conv_ae {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {K f : V → ℂ}
    (hK : Integrable K μ) (hf : MemLp f p μ) (r : ℕ) (h : V) :
    (fwdDiff h)^[r] (conv K f μ) =ᵐ[μ] conv ((fwdDiff h)^[r] K) f μ := by
  induction r with
  | zero => exact Filter.EventuallyEq.rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', fwdDiff_eq_sub,
      fwdDiff_eq_sub]
    have hKr : Integrable ((fwdDiff h)^[r] K) μ := integrable_higherDiff hK r h
    have h1 : (fun x => (fwdDiff h)^[r] (conv K f μ) (x + h)) =ᵐ[μ]
        conv (fun y => (fwdDiff h)^[r] K (y + h)) f μ := by
      refine (ae_comp_add_right ih h).trans (Filter.EventuallyEq.of_eq ?_)
      funext x
      exact conv_comp_add _ _ h x
    exact (h1.sub ih).trans (sub_conv_ae hp1 hp (hKr.comp_add_right h) hKr hf).symm

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **Differences of dilations**: `Δ_h^r (Φ_c) = (Δ_{ch}^r Φ)_c`. -/
theorem higherDiff_dilate (r : ℕ) (c : ℝ) (h : V) (Φ : V → ℂ) :
    (fwdDiff h)^[r] (dilate c Φ) = dilate c ((fwdDiff (c • h))^[r] Φ) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    funext x
    simp only [fwdDiff, dilate, smul_add]
    ring

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The modulus of a convolution**: if `‖Δ_v^r K‖_1 ≤ B` for `‖v‖ ≤ 2^(-k)`, then
`ω_r(K ⋆ h, 2^(-k))_p ≤ B ‖h‖_p`, since `Δ_v^r (K ⋆ h) = (Δ_v^r K) ⋆ h` (Young's inequality). -/
theorem lpModulus_convLp_le (hp : p ≠ ∞) {K : V → ℂ} (hK : Integrable K μ) (r k : ℕ)
    {B : ℝ≥0∞} (hB : ∀ v : V, ‖v‖ ≤ 1 / 2 ^ k → eLpNorm ((fwdDiff v)^[r] K) 1 μ ≤ B)
    (h : Lp ℂ p μ) : lpModulus p r (convLp hp hK h) k ≤ B * ‖h‖ₑ := by
  rw [lpModulus, modulus_congr_ae (convLp_apply_ae hp hK h)]
  refine iSup₂_le fun v hv => ?_
  rw [eLpNorm_congr_ae (higherDiff_conv_ae Fact.out hp hK (Lp.memLp h) r v), Lp.eNorm_def]
  exact (eLpNorm_conv_le Fact.out (integrable_higherDiff hK r v).aestronglyMeasurable
    (Lp.aestronglyMeasurable h)).trans (by gcongr; exact hB v hv)

end Rd

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### Differences of convolutions, pointwise -/

/-- **Differences of convolutions**: `Δ_h^r (K ⋆ g) = (Δ_h^r K) ⋆ g` where the convolutions with
the translates of `K` converge absolutely. -/
theorem higherDiff_conv_apply {K g : V → ℂ}
    (hK : ∀ v x, Integrable (fun y => K (y + v) * g (x - y)) volume) (r : ℕ) (h x : V) :
    (fwdDiff h)^[r] (conv K g volume) x = conv ((fwdDiff h)^[r] K) g volume x := by
  rw [higherDiff_apply, conv_apply]
  simp_rw [higherDiff_apply, Finset.sum_mul]
  rw [integral_finsetSum _ fun l _ => ?_]
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [conv_add_apply, ← integral_const_mul]
    congr 1
    funext y
    ring
  · exact ((hK ((l : ℝ) • h) x).const_mul ((-1 : ℂ) ^ (r - l) * (r.choose l : ℂ))).congr
      (Eventually.of_forall fun y => by ring)

end Rd
