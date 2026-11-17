/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreRadialInteriorMollification.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreInteriorWeakGradient
public import LeanPool.GinibrePoincare.Analysis.RadialL2MollifierMaps

/-! # Simultaneous interior weak-Sobolev mollification

For actual Ginibre weak pairs with compact representatives supported away from
collisions, the classical gradient of the concrete smooth convolution represents
the vector L² radial kernel average. Both values and gradients converge in Lebesgue L².
-/


@[expose] public section


open MeasureTheory Filter ContinuousLinearMap
open scoped Topology ContDiff Convolution
namespace GinibrePoincare
noncomputable section

variable (n : ℕ) (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreDistributionalGradient n u g)
    (f : Configuration n → ℝ)
    (h : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2))
    (hf : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f)
    (hh : (g : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2)) =ᵐ[ginibreMeasure n] h)
    (hfc : HasCompactSupport f) (hhc : HasCompactSupport h)
    (hfs : tsupport f ⊆ {z | CollisionFree z}) (hhs : tsupport h ⊆ {z | CollisionFree z})

include hn u g hg hf hh hfc hhc hfs hhs

/-- The vector L² average represents the actual classical gradient of mollification. -/
theorem ginibre_radial_interior_mollification_gradient_ae
    (m : ℕ) (hv : MemLp h 2 volume) :
    (radialL2MollifierAverage n m (hv.toLp h) :
      Configuration n → EuclideanSpace ℝ (Fin n × Fin 2)) =ᵐ[volume]
      ginibreEuclideanGradient (radialMollifierKernel n m ⋆[lsmul ℝ ℝ, volume] f) := by
  have hd := (ginibre_interior_weak_gradient_mollification n hn u g hg f h hf hh
    hfc hhc hfs hhs (radialMollifierKernel n m) (radialMollifierKernel_properties n m).1
    (radialMollifierKernel_properties n m).2.1).2
  have he (k : Fin n × Fin 2) : ∀ᵐ z ∂(volume : Measure (Configuration n)),
      radialL2MollifierAverage n m (hv.toLp h) z k =
        ginibreEuclideanGradient (radialMollifierKernel n m ⋆[lsmul ℝ ℝ, volume] f) z k := by
    let P : EuclideanSpace ℝ (Fin n × Fin 2) →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin n × Fin 2 => ℝ) k
    filter_upwards [P.coeFn_compLpL (radialL2MollifierAverage n m (hv.toLp h)),
      radialL2MollifierAverage_projection_convolution_ae n m P h hv hhc] with z hz hz'
    exact hz.symm.trans (hz'.trans (hd z k).symm)
  have hall := (ae_all_iff).mpr he
  filter_upwards [hall] with z hz
  ext k
  exact hz k

/-- The actual mollified classical gradient belongs to ordinary vector L². -/
theorem ginibre_radial_interior_mollification_gradient_memLp
    (m : ℕ) (hv : MemLp h 2 volume) :
    MemLp (ginibreEuclideanGradient (radialMollifierKernel n m ⋆[lsmul ℝ ℝ, volume] f))
      2 volume :=
  (Lp.memLp (radialL2MollifierAverage n m (hv.toLp h))).ae_eq
    (ginibre_radial_interior_mollification_gradient_ae n hn u g hg f h hf hh
      hfc hhc hfs hhs m hv)

/-- The L² class of the actual classical gradient is the vector radial kernel average. -/
theorem ginibre_radial_interior_mollification_gradient_toLp
    (m : ℕ) (hv : MemLp h 2 volume) :
    (ginibre_radial_interior_mollification_gradient_memLp n hn u g hg f h hf hh
      hfc hhc hfs hhs m hv).toLp
        (ginibreEuclideanGradient (radialMollifierKernel n m ⋆[lsmul ℝ ℝ, volume] f)) =
      radialL2MollifierAverage n m (hv.toLp h) := by
  apply Lp.ext
  exact (ginibre_radial_interior_mollification_gradient_memLp n hn u g hg f h hf hh
    hfc hhc hfs hhs m hv).coeFn_toLp.trans
      (ginibre_radial_interior_mollification_gradient_ae n hn u g hg f h hf hh
        hfc hhc hfs hhs m hv).symm

/-- Concrete smooth compact mollifications converge simultaneously in value and
classical gradient L² for interior compact representatives of actual weak pairs. -/
theorem ginibre_radial_interior_sobolev_mollification_tendsto
    (fv : MemLp f 2 volume) (hv : MemLp h 2 volume) :
    Tendsto (fun m =>
      (radialSmoothCompactMollification n m f fv hfc,
        (ginibre_radial_interior_mollification_gradient_memLp n hn u g hg f h hf hh
          hfc hhc hfs hhs m hv).toLp
            (ginibreEuclideanGradient (radialMollifierKernel n m ⋆[lsmul ℝ ℝ, volume] f))))
      atTop (𝓝 (fv.toLp f, hv.toLp h)) := by
  simp_rw [ginibre_radial_interior_mollification_gradient_toLp n hn u g hg f h hf hh
    hfc hhc hfs hhs _ hv]
  exact (radialSmoothCompactMollification_tendsto n f fv hfc).prodMk_nhds
    (radialL2MollifierAverage_tendsto n (hv.toLp h))

/-- The ordinary L² hypotheses of interior mollification follow from the actual
weighted weak pair. In particular no independent unweighted energy certificate
is required. -/
theorem ginibre_radial_interior_sobolev_mollification_exists
    :
    ∃ (fv : MemLp f 2 volume) (hv : MemLp h 2 volume),
      (∀ m, ContDiff ℝ ∞ (radialMollifierKernel n m ⋆[lsmul ℝ ℝ, volume] f) ∧
        HasCompactSupport (radialMollifierKernel n m ⋆[lsmul ℝ ℝ, volume] f)) ∧
      Tendsto (fun m =>
        (radialSmoothCompactMollification n m f fv hfc,
          (ginibre_radial_interior_mollification_gradient_memLp n hn u g hg f h hf hh
            hfc hhc hfs hhs m hv).toLp
              (ginibreEuclideanGradient (radialMollifierKernel n m ⋆[lsmul ℝ ℝ, volume] f))))
        atTop (𝓝 (fv.toLp f, hv.toLp h)) := by
  have fv : MemLp f 2 volume := ginibre_memLp_volume_of_interior_compactSupport hn f
    ((memLp_congr_ae hf).mp (Lp.memLp u)) hfc hfs
  have hv : MemLp h 2 volume := ginibre_memLp_volume_of_interior_compactSupport hn h
    ((memLp_congr_ae hh).mp (Lp.memLp g)) hhc hhs
  refine ⟨fv, hv, ?_, ginibre_radial_interior_sobolev_mollification_tendsto n hn u g hg f h hf hh
    hfc hhc hfs hhs fv hv⟩
  intro m
  exact ⟨((radialMollifierKernel_properties n m).2.1.contDiff_convolution_left (lsmul ℝ ℝ)
    (radialMollifierKernel_properties n m).1 (fv.locallyIntegrable (by norm_num))),
    (radialMollifierKernel_properties n m).2.1.convolution (lsmul ℝ ℝ) hfc⟩

end
end GinibrePoincare
