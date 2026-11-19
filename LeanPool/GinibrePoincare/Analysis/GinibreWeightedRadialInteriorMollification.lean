/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreWeightedRadialInteriorMollification.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreRadialInteriorMollification
public import LeanPool.GinibrePoincare.Analysis.GinibreLebesgueL2Transfer

/-! # Actual weighted value-and-gradient convergence of interior mollification

The density bound transfers the simultaneous ordinary L² convergence to the
actual Ginibre L² graph topology. The smooth functions are concrete normalized
bump convolutions, and their gradients are their actual classical gradients.
-/

@[expose] public section

open MeasureTheory Filter ContinuousLinearMap
open scoped Topology ContDiff Convolution
namespace GinibrePoincare
noncomputable section

/-- Actual interior compact weak pairs admit concrete smooth compact
mollifications converging in the Ginibre value-and-gradient L² topology.
The concrete kernels are radial and symmetric; the original value need not be. -/
theorem ginibre_weighted_radial_interior_mollification (n : ℕ) (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreDistributionalGradient n u g)
    (f : Configuration n → ℝ)
    (h : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2))
    (hf : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f)
    (hh : (g : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2)) =ᵐ[ginibreMeasure n] h)
    (hfc : HasCompactSupport f) (hhc : HasCompactSupport h)
    (hfs : tsupport f ⊆ {z | CollisionFree z}) (hhs : tsupport h ⊆ {z | CollisionFree z})
    :
    ∃ (v : ℕ → Lp ℝ 2 (ginibreMeasure n))
      (w : ℕ → Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n)),
      (∀ m, ContDiff ℝ ∞ (radialMollifierKernel n m ⋆[lsmul ℝ ℝ, volume] f) ∧
        HasCompactSupport (radialMollifierKernel n m ⋆[lsmul ℝ ℝ, volume] f) ∧
        (v m : Configuration n → ℝ) =ᵐ[ginibreMeasure n]
          (radialMollifierKernel n m ⋆[lsmul ℝ ℝ, volume] f) ∧
        (w m : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2)) =ᵐ[ginibreMeasure n]
          ginibreEuclideanGradient (radialMollifierKernel n m ⋆[lsmul ℝ ℝ, volume] f)) ∧
      Tendsto (fun m => (v m, w m)) atTop (𝓝 (u, g)) := by
  obtain ⟨fv, hv, hreg, ht⟩ := ginibre_radial_interior_sobolev_mollification_exists
    n hn u g hg f h hf hh hfc hhc hfs hhs
  let a m := radialSmoothCompactMollification n m f fv hfc
  let b m := (ginibre_radial_interior_mollification_gradient_memLp n hn u g hg f h hf hh
    hfc hhc hfs hhs m hv).toLp
      (ginibreEuclideanGradient (radialMollifierKernel n m ⋆[lsmul ℝ ℝ, volume] f))
  let v m := ginibreL2OfLebesgue n hn (a m)
  let w m := ginibreL2OfLebesgue n hn (b m)
  obtain ⟨c, hc, hm⟩ := ginibreMeasure_le_finite_smul_volume n hn
  have hac : ginibreMeasure n ≪ (volume : Measure (Configuration n)) :=
    Measure.absolutelyContinuous_of_le_smul hm
  have hu : ginibreL2OfLebesgue n hn (fv.toLp f) = u := by
    apply Lp.ext
    exact (ginibreL2OfLebesgue_ae n hn (fv.toLp f)).trans
      ((hac.ae_eq fv.coeFn_toLp).trans hf.symm)
  have hg' : ginibreL2OfLebesgue n hn (hv.toLp h) = g := by
    apply Lp.ext
    exact (ginibreL2OfLebesgue_ae n hn (hv.toLp h)).trans
      ((hac.ae_eq hv.coeFn_toLp).trans hh.symm)
  refine ⟨v, w, ?_, ?_⟩
  · intro m
    refine ⟨(hreg m).1, (hreg m).2, ?_, ?_⟩
    · exact (ginibreL2OfLebesgue_ae n hn (a m)).trans
        (hac.ae_eq (memLp_radial_convolution_compact n m f fv hfc).coeFn_toLp)
    · exact (ginibreL2OfLebesgue_ae n hn (b m)).trans
        (hac.ae_eq (ginibre_radial_interior_mollification_gradient_memLp n hn u g hg f h hf hh
          hfc hhc hfs hhs m hv).coeFn_toLp)
  · have ha := (ginibreL2OfLebesgue n hn (V := ℝ)).continuous.continuousAt.tendsto.comp
      (continuous_fst.tendsto _ |>.comp ht)
    have hb := (ginibreL2OfLebesgue n hn (V := EuclideanSpace ℝ (Fin n × Fin
        2))).continuous.continuousAt.tendsto.comp
      (continuous_snd.tendsto _ |>.comp ht)
    rw [hu] at ha
    rw [hg'] at hb
    exact ha.prodMk_nhds hb

end
end GinibrePoincare
