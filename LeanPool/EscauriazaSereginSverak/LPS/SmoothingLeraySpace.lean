/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingLerayConvolution
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# The solenoidal subspace of `L²(ℝ³; ℝ³)` and convolution operators

For `prop:lps-smoothing`: the weakly divergence-free fields form the orthogonal
complement of the test gradients in `L²(ℝ³; ℝ³)`, realised as three `L²(ℝ³)`
components. Convolution with a continuous compactly supported kernel acts
componentwise as a bounded operator whose adjoint is convolution with the
reflected kernel; it preserves the solenoidal subspace and therefore commutes
with the orthogonal projection onto it.
-/

public section

open MeasureTheory Set Filter
open scoped Convolution ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- `L²(ℝ³; ℝ³)` as three real `L²(ℝ³)` components (`prop:lps-smoothing`). -/
@[expose] abbrev LpsL2Field : Type :=
  PiLp 2 (fun _ : Fin 3 => Lp ℝ 2 (volume : Measure Vec3))

/-- Smooth compactly supported scalar test functions on `ℝ³`
(`prop:lps-smoothing`). -/
@[expose] abbrev LpsTestFunction : Type :=
  {φ : Vec3 → ℝ // ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ}

/-- Partial derivatives of test functions are square integrable
(`prop:lps-smoothing`). -/
theorem lpsLeray_memLp_spatialDeriv_test {φ : Vec3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (i : Fin 3) : MemLp (spatialDeriv φ i) 2 volume :=
  ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
    (hφc.fderiv_apply (𝕜 := ℝ) (basisVec i))

/-- The gradient of a test function as an element of `L²(ℝ³; ℝ³)`
(`prop:lps-smoothing`). -/
@[expose] def lpsTestGradient (φ : LpsTestFunction) : LpsL2Field :=
  WithLp.toLp 2 fun i =>
    (lpsLeray_memLp_spatialDeriv_test φ.2.1 φ.2.2 i).toLp (spatialDeriv φ.1 i)

/-- The weakly divergence-free fields in `L²(ℝ³; ℝ³)`: the orthogonal
complement of the test gradients (`prop:lps-smoothing`). -/
@[expose] def lpsSolenoidal : Submodule ℝ LpsL2Field :=
  (Submodule.span ℝ (Set.range lpsTestGradient))ᗮ

@[expose] instance : lpsSolenoidal.HasOrthogonalProjection := by
  unfold lpsSolenoidal
  infer_instance

/-- The `L²` pairing with a square-integrable function is the integral of the
product (`prop:lps-smoothing`). -/
theorem lpsLeray_inner_toLp (f : Lp ℝ 2 (volume : Measure Vec3)) {ψ : Vec3 → ℝ}
    (hψ : MemLp ψ 2 volume) : inner ℝ f (hψ.toLp ψ) = ∫ x, f x * ψ x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hψ.coeFn_toLp] with x hx
  rw [hx, Real.inner_apply]

/-- Pairing a field with a test gradient (`prop:lps-smoothing`). -/
theorem lpsLeray_inner_testGradient (g : LpsL2Field) (φ : LpsTestFunction) :
    inner ℝ g (lpsTestGradient φ) = ∑ i, ∫ x, g i x * spatialDeriv φ.1 i x := by
  rw [PiLp.inner_apply]
  exact Finset.sum_congr rfl fun i _ =>
    lpsLeray_inner_toLp (g i) (lpsLeray_memLp_spatialDeriv_test φ.2.1 φ.2.2 i)

/-- Membership in the solenoidal subspace, tested on test gradients
(`prop:lps-smoothing`). -/
theorem mem_lpsSolenoidal_iff_inner (g : LpsL2Field) :
    g ∈ lpsSolenoidal ↔ ∀ φ : LpsTestFunction, inner ℝ g (lpsTestGradient φ) = 0 := by
  constructor
  · intro hg φ
    exact Submodule.inner_left_of_mem_orthogonal
      (Submodule.subset_span (Set.mem_range_self φ)) hg
  · intro h
    rw [lpsSolenoidal, Submodule.mem_orthogonal']
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨φ, rfl⟩ := hx
      exact h φ
    | zero => simp
    | add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]
    | smul c x _ hx => rw [real_inner_smul_right, hx, mul_zero]

/-- Membership in the solenoidal subspace is the weak divergence-free
condition (`prop:lps-smoothing`). -/
theorem mem_lpsSolenoidal_iff (g : LpsL2Field) :
    g ∈ lpsSolenoidal ↔ ∀ φ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∑ i, ∫ x, g i x * spatialDeriv φ i x = 0 := by
  rw [mem_lpsSolenoidal_iff_inner]
  constructor
  · intro h φ hφ hφc
    rw [← lpsLeray_inner_testGradient g ⟨φ, hφ, hφc⟩]
    exact h _
  · intro h φ
    rw [lpsLeray_inner_testGradient]
    exact h φ.1 φ.2.1 φ.2.2

/-- Existence of convolutions of `L²` functions with continuous compactly
supported kernels. -/
theorem lpsLeray_convolutionExists {θ f : Vec3 → ℝ} (hθ : Continuous θ)
    (hθc : HasCompactSupport θ) (hf : MemLp f 2 volume) :
    ConvolutionExists θ f (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
  hθc.convolutionExists_left _ hθ (hf.locallyIntegrable (by norm_num))

/-- Convolution with a continuous compactly supported kernel as a bounded
operator on `L²(ℝ³)` (`prop:lps-smoothing`). -/
@[expose] def lpsConvL2 (θ : Vec3 → ℝ) (hθ : Continuous θ) (hθc : HasCompactSupport θ) :
    Lp ℝ 2 (volume : Measure Vec3) →L[ℝ] Lp ℝ 2 (volume : Measure Vec3) :=
  LinearMap.mkContinuous
    { toFun := fun f => (lpsLeray_memLp_conv hθ hθc (Lp.memLp f)).toLp
        (θ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] ⇑f)
      map_add' := fun f g => by
        rw [← MemLp.toLp_add]
        apply MemLp.toLp_congr
        have hcongr : θ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] ⇑(f + g) =
            θ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] (⇑f + ⇑g) :=
          convolution_congr (L := ContinuousLinearMap.lsmul ℝ ℝ) (h1 := EventuallyEq.rfl)
            (h2 := Lp.coeFn_add f g)
        rw [hcongr, (lpsLeray_convolutionExists hθ hθc (Lp.memLp f)).distrib_add
          (lpsLeray_convolutionExists hθ hθc (Lp.memLp g))]
      map_smul' := fun c f => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        apply MemLp.toLp_congr
        have hcongr : θ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] ⇑(c • f) =
            θ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] (c • ⇑f) :=
          convolution_congr (L := ContinuousLinearMap.lsmul ℝ ℝ) (h1 := EventuallyEq.rfl)
            (h2 := Lp.coeFn_smul c f)
        rw [hcongr, convolution_smul] }
    (∫ x, ‖θ x‖) fun f => by
      change ‖(lpsLeray_memLp_conv hθ hθc (Lp.memLp f)).toLp
        (θ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] ⇑f)‖ ≤ (∫ x, ‖θ x‖) * ‖f‖
      rw [Lp.norm_toLp, Lp.norm_def]
      have hc0 : 0 ≤ ∫ x, ‖θ x‖ := integral_nonneg fun x => norm_nonneg _
      calc (eLpNorm (θ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] ⇑f) 2 volume).toReal
          ≤ (ENNReal.ofReal (∫ x, ‖θ x‖) * eLpNorm (⇑f) 2 volume).toReal :=
            ENNReal.toReal_mono
              (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.memLp f).eLpNorm_ne_top)
              (lpsLeray_eLpNorm_conv_le hθ hθc (Lp.memLp f))
        _ = (∫ x, ‖θ x‖) * (eLpNorm (⇑f) 2 volume).toReal := by
            rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc0]

/-- The operator `lpsConvL2` is convolution almost everywhere
(`prop:lps-smoothing`). -/
theorem lpsConvL2_coeFn (θ : Vec3 → ℝ) (hθ : Continuous θ) (hθc : HasCompactSupport θ)
    (f : Lp ℝ 2 (volume : Measure Vec3)) :
    ⇑(lpsConvL2 θ hθ hθc f) =ᵐ[volume] θ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] ⇑f :=
  MemLp.coeFn_toLp (lpsLeray_memLp_conv hθ hθc (Lp.memLp f))

/-- The adjoint of convolution with `θ` on `L²(ℝ³)` is convolution with the
reflected kernel (`prop:lps-smoothing`). -/
theorem lpsConvL2_inner {θ θ' : Vec3 → ℝ} (hθ : Continuous θ) (hθc : HasCompactSupport θ)
    (hθ' : Continuous θ') (hθc' : HasCompactSupport θ') (hrefl : ∀ y, θ' y = θ (-y))
    (f h : Lp ℝ 2 (volume : Measure Vec3)) :
    inner ℝ (lpsConvL2 θ hθ hθc f) h = inner ℝ f (lpsConvL2 θ' hθ' hθc' h) := by
  have hθ'eq : θ' = fun y => θ (-y) := funext hrefl
  rw [L2.inner_def, L2.inner_def]
  calc ∫ x, inner ℝ ((lpsConvL2 θ hθ hθc f) x) (h x)
      = ∫ x, (θ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] ⇑f) x * h x := by
        apply integral_congr_ae
        filter_upwards [lpsConvL2_coeFn θ hθ hθc f] with x hx
        rw [hx, Real.inner_apply]
    _ = ∫ x, f x * (θ' ⋆[ContinuousLinearMap.lsmul ℝ ℝ] ⇑h) x := by
        rw [hθ'eq]
        exact lpsLeray_integral_conv_mul_eq hθ hθc (Lp.memLp f) (Lp.memLp h)
    _ = ∫ x, inner ℝ (f x) ((lpsConvL2 θ' hθ' hθc' h) x) := by
        apply integral_congr_ae
        filter_upwards [lpsConvL2_coeFn θ' hθ' hθc' h] with x hx
        rw [hx, Real.inner_apply]

/-- Componentwise convolution with a continuous compactly supported kernel on
`L²(ℝ³; ℝ³)` (`prop:lps-smoothing`). -/
@[expose] def lpsConvField (θ : Vec3 → ℝ) (hθ : Continuous θ) (hθc : HasCompactSupport θ) :
    LpsL2Field →L[ℝ] LpsL2Field :=
  (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Fin 3 => Lp ℝ 2 (volume : Measure Vec3))).symm.toContinuousLinearMap ∘L
    (ContinuousLinearMap.pi fun i => lpsConvL2 θ hθ hθc ∘L ContinuousLinearMap.proj i) ∘L
    (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Fin 3 => Lp ℝ 2 (volume : Measure Vec3))).toContinuousLinearMap

/-- Components of `lpsConvField` (`prop:lps-smoothing`). -/
theorem lpsConvField_apply (θ : Vec3 → ℝ) (hθ : Continuous θ) (hθc : HasCompactSupport θ)
    (g : LpsL2Field) (i : Fin 3) :
    lpsConvField θ hθ hθc g i = lpsConvL2 θ hθ hθc (g i) := rfl

/-- The adjoint of componentwise convolution is componentwise convolution with
the reflected kernel (`prop:lps-smoothing`). -/
theorem lpsConvField_inner {θ θ' : Vec3 → ℝ} (hθ : Continuous θ) (hθc : HasCompactSupport θ)
    (hθ' : Continuous θ') (hθc' : HasCompactSupport θ') (hrefl : ∀ y, θ' y = θ (-y))
    (f h : LpsL2Field) :
    inner ℝ (lpsConvField θ hθ hθc f) h = inner ℝ f (lpsConvField θ' hθ' hθc' h) := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  exact Finset.sum_congr rfl fun i _ => lpsConvL2_inner hθ hθc hθ' hθc' hrefl (f i) (h i)

/-- The reflection of a continuous kernel is continuous (`prop:lps-smoothing`). -/
theorem lpsLeray_continuous_reflect {θ : Vec3 → ℝ} (hθ : Continuous θ) :
    Continuous (fun y => θ (-y)) :=
  hθ.comp continuous_neg

/-- The reflection of a compactly supported kernel is compactly supported
(`prop:lps-smoothing`). -/
theorem lpsLeray_hasCompactSupport_reflect {θ : Vec3 → ℝ} (hθc : HasCompactSupport θ) :
    HasCompactSupport (fun y => θ (-y)) := by
  simpa [Function.comp_def] using hθc.comp_homeomorph (Homeomorph.neg Vec3)

/-- Convolution maps test gradients to test gradients (`prop:lps-smoothing`). -/
theorem lpsConvField_testGradient {θ : Vec3 → ℝ} (hθ : Continuous θ)
    (hθc : HasCompactSupport θ) (φ : LpsTestFunction) :
    lpsConvField θ hθ hθc (lpsTestGradient φ) =
      lpsTestGradient ⟨θ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] φ.1,
        lpsLeray_contDiff_conv_test hθ φ.2.1 φ.2.2,
        lpsLeray_hasCompactSupport_conv hθc φ.2.2⟩ := by
  ext i : 1
  rw [lpsConvField_apply]
  apply Lp.ext
  have hcongr : θ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] ⇑((lpsTestGradient φ) i) =
      θ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] spatialDeriv φ.1 i :=
    convolution_congr (L := ContinuousLinearMap.lsmul ℝ ℝ) (h1 := EventuallyEq.rfl)
      (h2 := MemLp.coeFn_toLp (lpsLeray_memLp_spatialDeriv_test φ.2.1 φ.2.2 i))
  filter_upwards [lpsConvL2_coeFn θ hθ hθc ((lpsTestGradient φ) i),
    MemLp.coeFn_toLp (lpsLeray_memLp_spatialDeriv_test
      (lpsLeray_contDiff_conv_test hθ φ.2.1 φ.2.2)
      (lpsLeray_hasCompactSupport_conv hθc φ.2.2) i)] with x hx hy
  change _ = ((lpsLeray_memLp_spatialDeriv_test
      (lpsLeray_contDiff_conv_test hθ φ.2.1 φ.2.2)
      (lpsLeray_hasCompactSupport_conv hθc φ.2.2) i).toLp _) x
  rw [hx, hy, hcongr, lpsLeray_spatialDeriv_conv_test hθ φ.2.1 φ.2.2 i x]

/-- Convolution with a continuous compactly supported kernel preserves the
solenoidal subspace (`prop:lps-smoothing`). -/
theorem lpsConvField_mem_lpsSolenoidal {θ : Vec3 → ℝ} (hθ : Continuous θ)
    (hθc : HasCompactSupport θ) {g : LpsL2Field} (hg : g ∈ lpsSolenoidal) :
    lpsConvField θ hθ hθc g ∈ lpsSolenoidal := by
  rw [mem_lpsSolenoidal_iff_inner] at hg ⊢
  intro φ
  rw [lpsConvField_inner hθ hθc (lpsLeray_continuous_reflect hθ)
    (lpsLeray_hasCompactSupport_reflect hθc) (fun y => rfl), lpsConvField_testGradient]
  exact hg _

/-- Convolution with a continuous compactly supported kernel commutes with the
orthogonal projection onto the solenoidal subspace (`prop:lps-smoothing`). -/
theorem lpsConvField_starProjection {θ : Vec3 → ℝ} (hθ : Continuous θ)
    (hθc : HasCompactSupport θ) (f : LpsL2Field) :
    lpsSolenoidal.starProjection (lpsConvField θ hθ hθc f) =
      lpsConvField θ hθ hθc (lpsSolenoidal.starProjection f) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact lpsConvField_mem_lpsSolenoidal hθ hθc (Submodule.starProjection_apply_mem _ _)
  · intro w hw
    rw [← map_sub, lpsConvField_inner hθ hθc (lpsLeray_continuous_reflect hθ)
      (lpsLeray_hasCompactSupport_reflect hθc) (fun y => rfl)]
    exact Submodule.inner_left_of_mem_orthogonal
      (lpsConvField_mem_lpsSolenoidal _ _ hw)
      (Submodule.sub_starProjection_mem_orthogonal f)

end ESS
