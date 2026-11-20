/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NonQuadraticWeyl.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.NonQuadraticHolomorphicMeanValue
public import LeanPool.GinibrePoincare.Analysis.LipschitzMollification

/-! # Holomorphic representatives of the actual weak ∂bar kernel
A fixed explicit radial smoothing kernel is used for mean-value reproduction;
Mathlib's arbitrary compact bump family supplies the approximate identity. -/

@[expose] public section
open MeasureTheory Set Real
open scoped ContDiff Convolution Topology
namespace GinibrePoincare
noncomputable section

/-- An explicit radial smooth bump; its choice does not use a chosen abstract bump base. -/
def planarRadialSmoothingBase (z : ℂ) : ℝ := smoothTransition (2 - Complex.normSq z)

theorem planarRadialSmoothingBase_contDiff : ContDiff ℝ ∞ planarRadialSmoothingBase := by
  have hn : ContDiff ℝ ∞ (fun z : ℂ => Complex.normSq z) := by
    simpa only [Complex.normSq_eq_norm_sq, id_eq] using (contDiff_id : ContDiff ℝ ∞ (id : ℂ →
        ℂ)).norm_sq ℝ
  exact smoothTransition.contDiff.comp (contDiff_const.sub hn)

theorem planarRadialSmoothingBase_compact : HasCompactSupport planarRadialSmoothingBase := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℂ) 2)
  intro z hz
  have hp : 0 < 2 - Complex.normSq z := by
    by_contra hn
    exact hz (smoothTransition.zero_of_nonpos (le_of_not_gt hn))
  rw [Metric.mem_closedBall, dist_zero_right]
  rw [Complex.normSq_eq_norm_sq] at hp
  nlinarith [norm_nonneg z]

theorem planarRadialSmoothingBase_integral_pos :
    0 < ∫ z, planarRadialSmoothingBase z := by
  apply
      planarRadialSmoothingBase_contDiff.continuous.integral_pos_of_hasCompactSupport_nonneg_ne_zero
    planarRadialSmoothingBase_compact
  · exact fun z => smoothTransition.nonneg _
  · exact (show planarRadialSmoothingBase 0 ≠ 0 by
      simp [planarRadialSmoothingBase, smoothTransition.zero_iff_nonpos])

/-- The actual normalized explicit radial kernel. -/
def planarRadialSmoothingKernel (z : ℂ) : ℝ :=
  planarRadialSmoothingBase z / ∫ w, planarRadialSmoothingBase w

theorem planarRadialSmoothingKernel_contDiff : ContDiff ℝ ∞ planarRadialSmoothingKernel := by
  convert planarRadialSmoothingBase_contDiff.mul
    (contDiff_const (c := (∫ w, planarRadialSmoothingBase w)⁻¹)) using 1
  rfl

theorem planarRadialSmoothingKernel_compact : HasCompactSupport planarRadialSmoothingKernel := by
  convert planarRadialSmoothingBase_compact.mul_right
    (f' := fun _ => (∫ w, planarRadialSmoothingBase w)⁻¹) using 1
  rfl

theorem planarRadialSmoothingKernel_integral : (∫ z, planarRadialSmoothingKernel z) = 1 := by
  unfold planarRadialSmoothingKernel
  rw [integral_div, div_self planarRadialSmoothingBase_integral_pos.ne']

theorem planarRadialSmoothingKernel_radial (z : ℂ) :
    planarRadialSmoothingKernel z = planarRadialSmoothingKernel (‖z‖ : ℂ) := by
  simp [planarRadialSmoothingKernel, planarRadialSmoothingBase, Complex.normSq_eq_norm_sq]

private theorem planar_real_kernel_convolution_assoc (f g : ℂ → ℝ) (U : ℂ → ℂ)
    (hf : Continuous f) (hg : Continuous g) (hfc : HasCompactSupport f) (hgc : HasCompactSupport g)
    (hu : LocallyIntegrable U volume) (x : ℂ) :
    ((f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] U) x =
      (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (g ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] U)) x := by
  have hUn : LocallyIntegrable (fun y => ‖U y‖) volume := by
    intro y
    obtain ⟨s, hs, hi⟩ := hu y
    exact ⟨s, hs, hi.norm⟩
  have hfcn : HasCompactSupport (fun y => ‖f y‖) := hfc.comp_left norm_zero
  have hgcn : HasCompactSupport (fun y => ‖g y‖) := hgc.comp_left norm_zero
  have hgn : ConvolutionExists (fun y => ‖g y‖) (fun y => ‖U y‖)
      (ContinuousLinearMap.mul ℝ ℝ) volume := hgcn.convolutionExists_left _ hg.norm hUn
  have hgnc : Continuous ((fun y => ‖g y‖) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (fun y => ‖U y‖))
      :=
    hgcn.continuous_convolution_left (ContinuousLinearMap.mul ℝ ℝ) hg.norm hUn
  apply convolution_assoc
    (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (L₂ := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ))
    (L₃ := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ))
    (L₄ := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ))
  · intros a b c
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, Complex.real_smul, Complex.ofReal_mul]
    ring
  · exact hf.aestronglyMeasurable
  · exact hg.aestronglyMeasurable
  · exact hu.aestronglyMeasurable
  · exact Filter.Eventually.of_forall (hfc.convolutionExists_left _ hf hg.locallyIntegrable)
  · exact Filter.Eventually.of_forall hgn
  · exact hfcn.convolutionExists_left _ hf.norm hgnc.locallyIntegrable x

private theorem planar_real_kernel_convolution_comm (f g : ℂ → ℝ) :
    (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) =
      (g ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) := by
  funext x
  rw [convolution_lsmul, convolution_lsmul_swap]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => mul_comm _ _)

/-- The two-component mollification is exactly the usual real-scalar
convolution of the actual complex function. -/
theorem planarComplexMollification_eq_convolution (φ : ℂ → ℝ) (U : ℂ → ℂ)
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (hu : LocallyIntegrable U volume) :
    planarComplexMollification φ U = (φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] U) := by
  funext x
  have hi := (hc.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) hφ hu x).integrable
  apply Complex.ext
  · have hr := Complex.reCLM.integral_comp_comm hi
    simp only [planarComplexMollification, convolution_lsmul, Complex.ofReal_re, Complex.ofReal_im,
      Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero,
          add_zero, smul_eq_mul]
    simpa only [ContinuousLinearMap.lsmul_apply, Complex.reCLM_apply, Complex.real_smul,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero] using hr
  · have hi' := Complex.imCLM.integral_comp_comm hi
    simp only [planarComplexMollification, convolution_lsmul, Complex.ofReal_re, Complex.ofReal_im,
      Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, zero_add, one_mul,
          smul_eq_mul]
    simpa only [ContinuousLinearMap.lsmul_apply, Complex.imCLM_apply, Complex.real_smul,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, add_zero] using hi'

/-- Weyl's lemma for the planar Cauchy–Riemann distribution: every locally
integrable weak solution has a genuinely entire representative. -/
theorem planarWeakCauchyRiemann_has_holomorphic_representative (U : ℂ → ℂ)
    (hu : LocallyIntegrable U volume)
    (htest : ∀ θ : ℂ → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      (∫ y, (U y).re * fderiv ℝ θ y 1 - (U y).im * fderiv ℝ θ y Complex.I) = 0 ∧
      (∫ y, (U y).im * fderiv ℝ θ y 1 + (U y).re * fderiv ℝ θ y Complex.I) = 0) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ U =ᵐ[volume] F := by
  let ψ := planarRadialSmoothingKernel
  have hψ : ContDiff ℝ ∞ ψ := planarRadialSmoothingKernel_contDiff
  have hψc : HasCompactSupport ψ := planarRadialSmoothingKernel_compact
  have hhol (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
      Differentiable ℂ (φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] U) := by
    rw [← planarComplexMollification_eq_convolution φ U hφ.continuous hc hu]
    exact planarComplexMollification_holomorphic U hu htest φ hφ hc
  let F := ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] U
  have hF : Differentiable ℂ F := hhol ψ hψ hψc
  have he (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
      (φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] U) =
        (φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] F) := by
    calc
      _ = ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          (φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] U) :=
        (radial_convolution_holomorphic_eq ψ hψ.continuous hψc
          planarRadialSmoothingKernel_radial planarRadialSmoothingKernel_integral _ (hhol φ hφ
              hc)).symm
      _ = (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] φ) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] U
          := by
        funext x
        exact (planar_real_kernel_convolution_assoc ψ φ U hψ.continuous hφ.continuous hψc hc hu
            x).symm
      _ = (φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] U
          := by
        rw [planar_real_kernel_convolution_comm]
      _ = _ := by
        funext x
        exact planar_real_kernel_convolution_assoc φ ψ U hφ.continuous hψ.continuous hc hψc hu x
  refine ⟨F, hF, ?_⟩
  have hb : ∀ᶠ m in Filter.atTop, (lsiMollifier ℂ m).rOut ≤ 2 * (lsiMollifier ℂ m).rIn := by
    exact Filter.Eventually.of_forall (fun m => by simp [lsiMollifier]; linarith)
  have ha := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (μ := volume) (lsiMollifier_radius_tendsto ℂ) hb hu
  filter_upwards [ha] with x hx
  have ht := ContDiffBump.convolution_tendsto_right_of_continuous
    (μ := volume) (lsiMollifier_radius_tendsto ℂ) hF.continuous x
  have ht' : Filter.Tendsto
      (fun m => ((lsiMollifier ℂ m).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] U) x)
      Filter.atTop (𝓝 (F x)) := ht.congr' (Filter.Eventually.of_forall (fun m =>
        (congrFun (he ((lsiMollifier ℂ m).normed volume)
          (lsiMollifier ℂ m).contDiff_normed (lsiMollifier ℂ m).hasCompactSupport_normed) x).symm))
  exact tendsto_nhds_unique hx ht'

/-- Every member of the actual nonquadratic weighted ∂bar kernel has a
genuinely entire representative after removing the square-root density. -/
theorem planarWeakDbarKernel_has_holomorphic_representative
    (n : ℕ) (V : ℂ → ℝ) (hV : ContDiff ℝ 2 V) (u : PlanarLebesgueL2)
    (hu : u ∈ planarWeakDbarKernel n V (hV.of_le (by norm_num))) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ planarUngaugedL2Function n V u =ᵐ[volume] F := by
  apply planarWeakCauchyRiemann_has_holomorphic_representative _
    (planarUngaugedL2Function_locallyIntegrable n V hV.continuous u)
  intro θ hθ hc
  exact planarWeakDbarKernel_cauchyRiemann_test_equations n V hV u hu θ
    (hθ.of_le (by decide)) hc

/-- The distributional kernel is exactly the genuine weighted Bergman space. -/
theorem mem_planarWeakDbarKernel_iff_holomorphic_representative
    (n : ℕ) (V : ℂ → ℝ) (hV : ContDiff ℝ 2 V) (u : PlanarLebesgueL2) :
    u ∈ planarWeakDbarKernel n V (hV.of_le (by norm_num)) ↔
      ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
        ∃ hF : MemLp (fun z => F z * planarPotentialHalfWeight n V z) 2 volume,
          hF.toLp _ = u := by
  constructor
  · intro hu
    obtain ⟨F, hF, he⟩ := planarWeakDbarKernel_has_holomorphic_representative n V hV u hu
    have hw : (fun z => F z * planarPotentialHalfWeight n V z) =ᵐ[volume] u := by
      filter_upwards [he] with z hz
      rw [← hz]
      unfold planarUngaugedL2Function planarPotentialHalfWeight
      rw [mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
      have hr : (n : ℝ) * V z / 2 + -(n : ℝ) * V z / 2 = 0 := by ring
      rw [hr]
      simp
    have hmem := (memLp_congr_ae hw).2 (Lp.memLp u)
    refine ⟨F, hF, hmem, ?_⟩
    apply Lp.ext
    exact hmem.coeFn_toLp.trans hw
  · rintro ⟨F, hF, hm, he⟩
    rw [← he]
    exact weighted_holomorphic_mem_weak_dbar_kernel n V (hV.of_le (by norm_num)) F hF hm

/-- The concrete Hörmander estimate approximates every compact C² function
by a genuinely entire weighted-square-integrable function. -/
theorem rhoSubharmonicPotential_compact_holomorphic_approximation
    (n : ℕ) (hn : 0 < n) (V : ℂ → ℝ) (ρ : ℝ) (hρpos : 0 < ρ)
    (hV : ContDiff ℝ 2 V) (hρ : IsRhoSubharmonicPotential ρ V) (f : PlanarCompactTest) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      ∃ hF : MemLp (fun z => F z * planarPotentialHalfWeight n V z) 2 volume,
        ‖planarWeightedTestL2 n V hV.continuous f - hF.toLp _‖ ^ 2 ≤
          (2 / ((n : ℝ) * ρ)) *
            ∫ z, Complex.normSq (planarDbar f z) * Real.exp (-(n : ℝ) * V z) := by
  let p := planarWeakDbarProjection n V (hV.of_le (by norm_num))
    (planarWeightedTestL2 n V hV.continuous f)
  have hp : p ∈ planarWeakDbarKernel n V (hV.of_le (by norm_num)) :=
    ((planarWeakDbarKernelClosed n V (hV.of_le (by norm_num))).orthogonalProjectionOnto
      (planarWeightedTestL2 n V hV.continuous f)).property
  obtain ⟨F, hF, hm, he⟩ :=
    (mem_planarWeakDbarKernel_iff_holomorphic_representative n V hV p).mp hp
  refine ⟨F, hF, hm, ?_⟩
  rw [he]
  exact rhoSubharmonicPotential_compact_dbar_projection_gap n hn V ρ hρpos hV hρ f

end
end GinibrePoincare
