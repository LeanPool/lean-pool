/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceWeightedEllipticConvolution.lean.
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

public import LeanPool.GinibrePoincare.Analysis.CorrespondenceWeightedEllipticMollification
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! # Concrete smooth compact convolution in ordinary L²

For compactly supported L² representatives, the actual normalized bump
convolution represents the Bochner L² average. Consequently the concrete
smooth compact functions converge strongly in L² as the bump radius shrinks.
-/

@[expose] public section

open MeasureTheory Filter ContinuousLinearMap
open scoped Topology ContDiff Convolution
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem correspondenceWeighted_integral_bump_convolution_mul_test (φ : ContDiffBump (0 : E))
    (f θ : E → ℝ) (hf : Integrable f volume)
    (hθ : Continuous θ) (hc : HasCompactSupport θ) :
    (∫ x, (φ.normed volume ⋆[lsmul ℝ ℝ, volume] f) x * θ x) =
      ∫ y, φ.normed volume y * (∫ x, f (x - y) * θ x) := by
  obtain ⟨C, hC⟩ := hθ.bounded_above_of_compact_support hc
  have hb : Integrable (fun p : E × E =>
      φ.normed volume p.2 * f (p.1 - p.2)) (volume.prod volume) := by
    simpa only [lsmul_apply, smul_eq_mul] using
      φ.integrable_normed.convolution_integrand (lsmul ℝ ℝ) hf
  have hi : Integrable (fun p : E × E =>
      φ.normed volume p.2 * f (p.1 - p.2) * θ p.1) (volume.prod volume) :=
    hb.mul_bdd (hθ.comp continuous_fst).aestronglyMeasurable
      (Eventually.of_forall (fun p => hC p.1))
  calc
    _ = ∫ x, ∫ y, φ.normed volume y * f (x - y) * θ x := by
      simp only [convolution_lsmul, smul_eq_mul, integral_mul_const]
    _ = ∫ y, ∫ x, φ.normed volume y * f (x - y) * θ x := integral_integral_swap hi
    _ = _ := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro y
      simp only [mul_assoc, integral_const_mul]

/-- Concrete convolution has an actual smooth compact representative in ordinary L². -/
theorem correspondenceWeighted_memLp_bump_convolution_compact (φ : ContDiffBump (0 : E))
    (f : E → ℝ) (hf : MemLp f 2 volume) (hc : HasCompactSupport f) :
    MemLp (φ.normed volume ⋆[lsmul ℝ ℝ, volume] f) 2 volume :=
  (φ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
    (φ.contDiff_normed (n := ⊤)) (hf.locallyIntegrable (by
        norm_num))).continuous.memLp_of_hasCompactSupport (φ.hasCompactSupport_normed.convolution
            (lsmul ℝ ℝ) hc)

/-- The actual Bochner L² average is represented by the concrete normalized bump convolution. -/
theorem correspondenceWeighted_lebesgueL2BumpAverage_convolution_ae (φ : ContDiffBump (0 : E))
    (f : E → ℝ) (hf : MemLp f 2 volume) (hc : HasCompactSupport f) :
    (correspondenceWeightedLebesgueL2BumpAverage φ (hf.toLp f) : E → ℝ) =ᵐ[volume]
      (φ.normed volume ⋆[lsmul ℝ ℝ, volume] f) := by
  have hfl := hf.locallyIntegrable (by norm_num)
  have hfi : Integrable f volume := by
    have hi : IntegrableOn f (tsupport f) volume := hfl.integrableOn_isCompact hc
    apply hi.integrable_of_forall_notMem_eq_zero
    exact fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hcl : LocallyIntegrable (φ.normed volume ⋆[lsmul ℝ ℝ, volume] f) volume :=
    (correspondenceWeighted_memLp_bump_convolution_compact φ f hf hc).locallyIntegrable (by
        norm_num)
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (correspondenceWeightedLebesgueL2BumpAverage φ (hf.toLp f))).locallyIntegrable (by
        norm_num)) hcl
  intro θ hθ hθc
  have hθLp : MemLp θ 2 volume := hθ.continuous.memLp_of_hasCompactSupport hθc
  calc
    _ = ∫ x, correspondenceWeightedLebesgueL2BumpAverage φ (hf.toLp f) x * θ x := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => by simp only [smul_eq_mul]; ring)
    _ = ∫ y, φ.normed volume y * (∫ x, (hf.toLp f) (x - y) * θ x) :=
      correspondenceWeighted_lebesgueL2BumpAverage_test_pairing φ (hf.toLp f) θ hθLp
    _ = ∫ y, φ.normed volume y * (∫ x, f (x - y) * θ x) := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro y
      dsimp only
      congr 1
      apply integral_congr_ae
      have he : ∀ᵐ x ∂(volume : Measure (E)),
          (hf.toLp f) (x + (-y)) = f (x + (-y)) :=
        (eventually_add_right_iff volume (-y)).mpr hf.coeFn_toLp
      filter_upwards [he] with x hx
      simpa only [sub_eq_add_neg] using congrArg (fun t => t * θ x) hx
    _ = ∫ x, (φ.normed volume ⋆[lsmul ℝ ℝ, volume] f) x * θ x :=
      (correspondenceWeighted_integral_bump_convolution_mul_test φ f θ hfi hθ.continuous hθc).symm
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => by simp only [smul_eq_mul]; ring)

/-- The Lebesgue `L²` class of the mollification `φ.normed volume ⋆ f` of a compactly supported
`f ∈ L²`. -/
def correspondenceWeightedLebesgueSmoothCompactMollification (φ : ContDiffBump (0 : E))
    (f : E → ℝ) (hf : MemLp f 2 volume) (hc : HasCompactSupport f) :
    Lp ℝ 2 (volume : Measure (E)) :=
  (correspondenceWeighted_memLp_bump_convolution_compact φ f hf hc).toLp
    (φ.normed volume ⋆[lsmul ℝ ℝ, volume] f)

theorem correspondenceWeighted_lebesgueSmoothCompactMollification_eq_average
    (φ : ContDiffBump (0 : E)) (f : E → ℝ)
    (hf : MemLp f 2 volume) (hc : HasCompactSupport f) :
    correspondenceWeightedLebesgueSmoothCompactMollification φ f hf hc =
        correspondenceWeightedLebesgueL2BumpAverage φ (hf.toLp f) := by
  apply Lp.ext
  exact (correspondenceWeighted_memLp_bump_convolution_compact φ f hf hc).coeFn_toLp.trans
    (correspondenceWeighted_lebesgueL2BumpAverage_convolution_ae φ f hf hc).symm

/-- Actual smooth compact mollifications of a compact L² function converge strongly in L². -/
theorem correspondenceWeighted_lebesgueSmoothCompactMollification_tendsto
    (φ : ℕ → ContDiffBump (0 : E))
    (hφ : Tendsto (fun m => (φ m).rOut) atTop (𝓝 0))
    (f : E → ℝ) (hf : MemLp f 2 volume) (hc : HasCompactSupport f) :
    Tendsto (fun m => correspondenceWeightedLebesgueSmoothCompactMollification (φ m) f hf hc)
      atTop (𝓝 (hf.toLp f)) := by
  simp_rw [correspondenceWeighted_lebesgueSmoothCompactMollification_eq_average]
  exact correspondenceWeighted_lebesgueL2BumpAverage_tendsto φ hφ (hf.toLp f)

end
end GinibrePoincare
