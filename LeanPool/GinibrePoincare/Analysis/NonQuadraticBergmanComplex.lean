/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NonQuadraticBergmanComplex.lean.
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

public import LeanPool.GinibrePoincare.Analysis.NonQuadraticWeyl

/-! # Genuine complex weighted Bergman projection
The real distributional-kernel construction is a complex closed subspace,
so its projection can be transported through complex Hilbert tensors. -/

@[expose] public section
open MeasureTheory
open scoped ContDiff InnerProductSpace
namespace GinibrePoincare
noncomputable section

/-- The actual distributional kernel is stable under every complex scalar,
proved using its genuine entire representatives. -/
theorem planarWeakDbarKernel_complex_smul_mem (n : ℕ) (V : ℂ → ℝ)
    (hV : ContDiff ℝ 2 V) (c : ℂ) (u : PlanarLebesgueL2)
    (hu : u ∈ planarWeakDbarKernel n V (hV.of_le (by norm_num))) :
    c • u ∈ planarWeakDbarKernel n V (hV.of_le (by norm_num)) := by
  obtain ⟨F, hF, hm, he⟩ :=
    (mem_planarWeakDbarKernel_iff_holomorphic_representative n V hV u).mp hu
  have hcm : MemLp (fun z => (c * F z) * planarPotentialHalfWeight n V z) 2 volume := by
    convert hm.const_smul c using 1
    funext z
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hce : hcm.toLp _ = c • hm.toLp _ := by
    apply Lp.ext
    filter_upwards [hcm.coeFn_toLp, Lp.coeFn_smul c (hm.toLp _), hm.coeFn_toLp] with z hz hz' hzF
    rw [hz, hz']
    simp only [Pi.smul_apply]
    rw [hzF]
    simp only [smul_eq_mul]
    ring
  rw [← he, ← hce]
  exact weighted_holomorphic_mem_weak_dbar_kernel n V (hV.of_le (by norm_num)) _
    (differentiable_const c |>.mul hF) hcm

/-- The genuine weighted Bergman subspace as a complex linear space. -/
def planarBergmanKernel (n : ℕ) (V : ℂ → ℝ) (hV : ContDiff ℝ 2 V) :
    Submodule ℂ PlanarLebesgueL2 where
  carrier := planarWeakDbarKernel n V (hV.of_le (by norm_num))
  zero_mem' := (planarWeakDbarKernel n V _).zero_mem
  add_mem' := (planarWeakDbarKernel n V _).add_mem
  smul_mem' := fun c u hu => planarWeakDbarKernel_complex_smul_mem n V hV c u hu

/-- Closedness is inherited from the concrete real distributional kernel. -/
def planarBergmanKernelClosed (n : ℕ) (V : ℂ → ℝ) (hV : ContDiff ℝ 2 V) :
    ClosedSubmodule ℂ PlanarLebesgueL2 :=
  ⟨planarBergmanKernel n V hV,
    Submodule.isClosed_orthogonal (planarWeightedAdjointTestL2 n V (hV.of_le (by norm_num))).range⟩

/-- The actual complex linear orthogonal Bergman projection. -/
def planarBergmanProjection (n : ℕ) (V : ℂ → ℝ) (hV : ContDiff ℝ 2 V) :
    PlanarLebesgueL2 →L[ℂ] PlanarLebesgueL2 :=
  (planarBergmanKernelClosed n V hV).starProjection

private theorem planarL2_real_inner_eq_re_complex_inner (a b : PlanarLebesgueL2) :
    ⟪a, b⟫_ℝ = (⟪a, b⟫_ℂ).re := by
  rw [L2.inner_def, L2.inner_def]
  calc
    _ = ∫ z, (⟪a z, b z⟫_ℂ).re := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun z => by simp only [Complex.inner, RCLike.inner_apply])
    _ = _ := Complex.reCLM.integral_comp_comm (L2.integrable_inner (𝕜 := ℂ) a b)

/-- The complex Bergman projection is exactly the previously constructed
real weak-kernel projection, so the proved Hörmander estimate transfers. -/
theorem planarBergmanProjection_eq_weak_projection
    (n : ℕ) (V : ℂ → ℝ) (hV : ContDiff ℝ 2 V) (u : PlanarLebesgueL2) :
    planarBergmanProjection n V hV u = planarWeakDbarProjection n V (hV.of_le (by norm_num)) u := by
  let KC := planarBergmanKernelClosed n V hV
  let KR := planarWeakDbarKernelClosed n V (hV.of_le (by norm_num))
  have hp : KC.starProjection u ∈ KR := Submodule.starProjection_apply_mem KC.toSubmodule u
  have ho : ∀ w ∈ KR, ⟪u - KC.starProjection u, w⟫_ℝ = 0 := by
    intro w hw
    have hc : w ∈ KC := hw
    have hz := Submodule.starProjection_inner_eq_zero (K := KC.toSubmodule) u w hc
    rw [planarL2_real_inner_eq_re_complex_inner, hz]
    rfl
  exact (Submodule.eq_starProjection_of_mem_of_inner_eq_zero (K := KR.toSubmodule) hp ho).symm

/-- The actual complex Bergman projection satisfies the genuine sharp
compact-test Hörmander estimate. -/
theorem rhoSubharmonicPotential_compact_bergman_projection_gap
    (n : ℕ) (hn : 0 < n) (V : ℂ → ℝ) (ρ : ℝ) (hρpos : 0 < ρ)
    (hV : ContDiff ℝ 2 V) (hρ : IsRhoSubharmonicPotential ρ V) (f : PlanarCompactTest) :
    ‖planarWeightedTestL2 n V hV.continuous f -
      planarBergmanProjection n V hV (planarWeightedTestL2 n V hV.continuous f)‖ ^ 2 ≤
      (2 / ((n : ℝ) * ρ)) *
        ∫ z, Complex.normSq (planarDbar f z) * Real.exp (-(n : ℝ) * V z) := by
  rw [planarBergmanProjection_eq_weak_projection]
  exact rhoSubharmonicPotential_compact_dbar_projection_gap n hn V ρ hρpos hV hρ f

end
end GinibrePoincare
