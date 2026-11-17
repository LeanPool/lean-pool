/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/RadialL2Convolution.lean.
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

public import LeanPool.GinibrePoincare.Analysis.RadialL2MollifierAverage
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! # Concrete radial smooth compact convolution in ordinary L²

For compactly supported L² representatives, the actual normalized radial kernel
convolution represents the Bochner L² average. Consequently the concrete
smooth compact functions converge strongly in L² as the bump radius shrinks.
-/


@[expose] public section


open MeasureTheory Filter ContinuousLinearMap
open scoped Topology ContDiff Convolution
namespace GinibrePoincare
noncomputable section


theorem integral_radial_convolution_mul_test (n : ℕ) (m : ℕ)
    (f θ : Configuration n → ℝ) (hf : Integrable f volume)
    (hθ : Continuous θ) (hc : HasCompactSupport θ) :
    (∫ x, (radialMollifierKernel n m ⋆[lsmul ℝ ℝ, volume] f) x * θ x) =
      ∫ y, radialMollifierKernel n m y * (∫ x, f (x - y) * θ x) := by
  obtain ⟨C, hC⟩ := hθ.bounded_above_of_compact_support hc
  have hb : Integrable (fun p : Configuration n × Configuration n =>
      radialMollifierKernel n m p.2 * f (p.1 - p.2)) (volume.prod volume) := by
    simpa only [lsmul_apply, smul_eq_mul] using
      (radialMollifierKernel_properties n m).2.2.2.1.convolution_integrand (lsmul ℝ ℝ) hf
  have hi : Integrable (fun p : Configuration n × Configuration n =>
      radialMollifierKernel n m p.2 * f (p.1 - p.2) * θ p.1) (volume.prod volume) :=
    hb.mul_bdd (hθ.comp continuous_fst).aestronglyMeasurable
      (Eventually.of_forall (fun p => hC p.1))
  calc
    _ = ∫ x, ∫ y, radialMollifierKernel n m y * f (x - y) * θ x := by
      simp only [convolution_lsmul, smul_eq_mul, integral_mul_const]
    _ = ∫ y, ∫ x, radialMollifierKernel n m y * f (x - y) * θ x := integral_integral_swap hi
    _ = _ := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro y
      simp only [mul_assoc, integral_const_mul]

/-- Concrete convolution has an actual smooth compact representative in ordinary L². -/
theorem memLp_radial_convolution_compact (n : ℕ) (m : ℕ)
    (f : Configuration n → ℝ) (hf : MemLp f 2 volume) (hc : HasCompactSupport f) :
    MemLp (radialMollifierKernel n m ⋆[lsmul ℝ ℝ, volume] f) 2 volume :=
  ((radialMollifierKernel_properties n m).2.1.contDiff_convolution_left (lsmul ℝ ℝ)
    (radialMollifierKernel_properties n m).1 (hf.locallyIntegrable (by
      norm_num))).continuous.memLp_of_hasCompactSupport ((radialMollifierKernel_properties n
      m).2.1.convolution (lsmul ℝ ℝ) hc)

/-- The actual Bochner L² average is represented by the concrete normalized radial kernel
  convolution. -/
theorem radialL2MollifierAverage_convolution_ae (n : ℕ) (m : ℕ)
    (f : Configuration n → ℝ) (hf : MemLp f 2 volume) (hc : HasCompactSupport f) :
    (radialL2MollifierAverage n m (hf.toLp f) : Configuration n → ℝ) =ᵐ[volume]
      (radialMollifierKernel n m ⋆[lsmul ℝ ℝ, volume] f) := by
  have hfl := hf.locallyIntegrable (by norm_num)
  have hfi : Integrable f volume := by
    have hi : IntegrableOn f (tsupport f) volume := hfl.integrableOn_isCompact hc
    apply hi.integrable_of_forall_notMem_eq_zero
    exact fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hcl : LocallyIntegrable (radialMollifierKernel n m ⋆[lsmul ℝ ℝ, volume] f) volume :=
    (memLp_radial_convolution_compact n m f hf hc).locallyIntegrable (by norm_num)
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (radialL2MollifierAverage n m (hf.toLp f))).locallyIntegrable (by norm_num)) hcl
  intro θ hθ hθc
  have hθLp : MemLp θ 2 volume := hθ.continuous.memLp_of_hasCompactSupport hθc
  calc
    _ = ∫ x, radialL2MollifierAverage n m (hf.toLp f) x * θ x := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => by simp only [smul_eq_mul]; ring)
    _ = ∫ y, radialMollifierKernel n m y * (∫ x, (hf.toLp f) (x - y) * θ x) :=
      radialL2MollifierAverage_test_pairing n m (hf.toLp f) θ hθLp
    _ = ∫ y, radialMollifierKernel n m y * (∫ x, f (x - y) * θ x) := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro y
      dsimp only
      congr 1
      apply integral_congr_ae
      have he : ∀ᵐ x ∂(volume : Measure (Configuration n)),
          (hf.toLp f) (x + (-y)) = f (x + (-y)) :=
        (eventually_add_right_iff volume (-y)).mpr hf.coeFn_toLp
      filter_upwards [he] with x hx
      simpa only [sub_eq_add_neg] using congrArg (fun t => t * θ x) hx
    _ = ∫ x, (radialMollifierKernel n m ⋆[lsmul ℝ ℝ, volume] f) x * θ x :=
      (integral_radial_convolution_mul_test n m f θ hfi hθ.continuous hθc).symm
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => by simp only [smul_eq_mul]; ring)

def radialSmoothCompactMollification (n : ℕ) (m : ℕ)
    (f : Configuration n → ℝ) (hf : MemLp f 2 volume) (hc : HasCompactSupport f) :
    Lp ℝ 2 (volume : Measure (Configuration n)) :=
  (memLp_radial_convolution_compact n m f hf hc).toLp
    (radialMollifierKernel n m ⋆[lsmul ℝ ℝ, volume] f)

theorem radialSmoothCompactMollification_eq_average (n : ℕ)
    (m : ℕ) (f : Configuration n → ℝ)
    (hf : MemLp f 2 volume) (hc : HasCompactSupport f) :
    radialSmoothCompactMollification n m f hf hc = radialL2MollifierAverage n m (hf.toLp f) := by
  apply Lp.ext
  exact (memLp_radial_convolution_compact n m f hf hc).coeFn_toLp.trans
    (radialL2MollifierAverage_convolution_ae n m f hf hc).symm

/-- Actual smooth compact radial-kernel mollifications converge strongly in L². -/
theorem radialSmoothCompactMollification_tendsto (n : ℕ)
    (f : Configuration n → ℝ) (hf : MemLp f 2 volume) (hc : HasCompactSupport f) :
    Tendsto (fun m => radialSmoothCompactMollification n m f hf hc)
      atTop (𝓝 (hf.toLp f)) := by
  simp_rw [radialSmoothCompactMollification_eq_average]
  exact radialL2MollifierAverage_tendsto n (hf.toLp f)

end
end GinibrePoincare
