/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreComplexCoreClosureEquivalence.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreRealCoreClosureEquivalence
public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorComplexification
public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorSpectrum
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-! # Complex-valued smooth gradient cores
The gradient here is the actual real Fréchet derivative in each Euclidean
coordinate, with complex values. -/

@[expose] public section
open MeasureTheory
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section

/-- Complex gradient vectors, with one component per real coordinate direction. -/
abbrev GinibreComplexGradientSpace (n : ℕ) := EuclideanSpace ℂ (Fin n × Fin 2)
/-- Real gradient vectors, with one component per real coordinate direction. -/
abbrev GinibreRealGradientSpace (n : ℕ) := EuclideanSpace ℝ (Fin n × Fin 2)

/-- The gradient of a complex function: its real directional derivatives along the `2n` real
coordinate directions. -/
def ginibreComplexEuclideanGradient {n : ℕ} (f : Configuration n → ℂ)
    (z : Configuration n) : GinibreComplexGradientSpace n :=
  WithLp.toLp 2 (fun k => fderiv ℝ f z (ginibreCoordinateDirection k))

/-- Apply a real-linear scalar map to each Euclidean gradient coordinate. -/
def ginibreGradientScalarMap (n : ℕ) {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) :
    PiLp 2 (fun _ : Fin n × Fin 2 => E) →L[ℝ]
      PiLp 2 (fun _ : Fin n × Fin 2 => F) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n × Fin 2 => F)).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.pi fun k => L.comp (ContinuousLinearMap.proj k)).comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n × Fin 2 => E)).toContinuousLinearMap)

@[simp] theorem ginibreGradientScalarMap_apply (n : ℕ) {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F)
    (g : PiLp 2 (fun _ : Fin n × Fin 2 => E)) (k : Fin n × Fin 2) :
    ginibreGradientScalarMap n L g k = L (g k) := rfl

theorem ginibreComplexGradient_re {n : ℕ} (f : Configuration n → ℂ)
    (hf : Differentiable ℝ f) (z : Configuration n) :
    ginibreGradientScalarMap n Complex.reCLM (ginibreComplexEuclideanGradient f z) =
      ginibreEuclideanGradient (fun z => (f z).re) z := by
  ext k
  rw [ginibreGradientScalarMap_apply, ginibreEuclideanGradient_coordinate]
  have h := fderiv_comp z Complex.reCLM.differentiableAt (hf z)
  simpa [ginibreComplexEuclideanGradient, ContinuousLinearMap.fderiv, Function.comp_def] using
    congrArg (fun L => L (ginibreCoordinateDirection k)) h.symm

theorem ginibreComplexGradient_im {n : ℕ} (f : Configuration n → ℂ)
    (hf : Differentiable ℝ f) (z : Configuration n) :
    ginibreGradientScalarMap n Complex.imCLM (ginibreComplexEuclideanGradient f z) =
      ginibreEuclideanGradient (fun z => (f z).im) z := by
  ext k
  rw [ginibreGradientScalarMap_apply, ginibreEuclideanGradient_coordinate]
  have h := fderiv_comp z Complex.imCLM.differentiableAt (hf z)
  simpa [ginibreComplexEuclideanGradient, ContinuousLinearMap.fderiv, Function.comp_def] using
    congrArg (fun L => L (ginibreCoordinateDirection k)) h.symm

/-- Pairs of a complex Ginibre `L²` value and a complex `L²` gradient field. -/
abbrev GinibreComplexGradientPair (n : ℕ) :=
  Lp ℂ 2 (ginibreMeasure n) × Lp (GinibreComplexGradientSpace n) 2 (ginibreMeasure n)
/-- Pairs of a real Ginibre `L²` value and a real `L²` gradient field. -/
abbrev GinibreRealGradientPair (n : ℕ) :=
  Lp ℝ 2 (ginibreMeasure n) × Lp (GinibreRealGradientSpace n) 2 (ginibreMeasure n)

/-- Pairs represented almost everywhere by `(f, ∇f)` for a smooth compactly supported complex
function `f`. -/
def ginibreGlobalComplexSmoothPairs (n : ℕ) : Set (GinibreComplexGradientPair n) :=
  {p | ∃ f : Configuration n → ℂ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
    (p.1 : Configuration n → ℂ) =ᵐ[ginibreMeasure n] f ∧
    (p.2 : Configuration n → GinibreComplexGradientSpace n) =ᵐ[ginibreMeasure n]
      ginibreComplexEuclideanGradient f}

/-- Pairs represented almost everywhere by `(f, ∇f)` for a smooth compactly supported complex
function `f` whose support avoids the collision set. -/
def ginibreInteriorComplexSmoothPairs (n : ℕ) : Set (GinibreComplexGradientPair n) :=
  {p | ∃ f : Configuration n → ℂ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
    tsupport f ⊆ {z | CollisionFree z} ∧
    (p.1 : Configuration n → ℂ) =ᵐ[ginibreMeasure n] f ∧
    (p.2 : Configuration n → GinibreComplexGradientSpace n) =ᵐ[ginibreMeasure n]
      ginibreComplexEuclideanGradient f}

/-- The componentwise real part of a complex value–gradient pair, as a real-linear map. -/
def ginibreComplexPairRe (n : ℕ) :
    GinibreComplexGradientPair n →L[ℝ] GinibreRealGradientPair n :=
  (ginibreFullComplexRe n).prodMap
    ((ginibreGradientScalarMap n Complex.reCLM).compLpL 2 (ginibreMeasure n))
/-- The componentwise imaginary part of a complex value–gradient pair, as a real-linear map. -/
def ginibreComplexPairIm (n : ℕ) :
    GinibreComplexGradientPair n →L[ℝ] GinibreRealGradientPair n :=
  (ginibreFullComplexIm n).prodMap
    ((ginibreGradientScalarMap n Complex.imCLM).compLpL 2 (ginibreMeasure n))
/-- The embedding of real value–gradient pairs into complex ones, as a real-linear map. -/
def ginibreComplexPairOfReal (n : ℕ) :
    GinibreRealGradientPair n →L[ℝ] GinibreComplexGradientPair n :=
  (ginibreFullComplexOfReal n).prodMap
    ((ginibreGradientScalarMap n Complex.ofRealCLM).compLpL 2 (ginibreMeasure n))

/-- The complex pair `q.1 + I • q.2` built from a real part `q.1` and an imaginary part `q.2`. -/
def ginibreComplexPairCombine (n : ℕ)
    (q : GinibreRealGradientPair n × GinibreRealGradientPair n) :
    GinibreComplexGradientPair n :=
  ginibreComplexPairOfReal n q.1 + Complex.I • ginibreComplexPairOfReal n q.2

theorem ginibreComplexPairCombine_continuous (n : ℕ) :
    Continuous (ginibreComplexPairCombine n) :=
  ((ginibreComplexPairOfReal n).continuous.comp continuous_fst).add
    (((ginibreComplexPairOfReal n).continuous.comp continuous_snd).const_smul Complex.I)

theorem ginibreComplexPair_reconstruct (n : ℕ) (p : GinibreComplexGradientPair n) :
    ginibreComplexPairCombine n (ginibreComplexPairRe n p, ginibreComplexPairIm n p) = p := by
  apply Prod.ext
  · apply Lp.ext
    filter_upwards [ginibreFullComplexOfReal_ae n (ginibreFullComplexRe n p.1),
      ginibreFullComplexOfReal_ae n (ginibreFullComplexIm n p.1),
      ginibreFullComplexRe_ae n p.1, ginibreFullComplexIm_ae n p.1,
      Lp.coeFn_add (ginibreFullComplexOfReal n (ginibreFullComplexRe n p.1))
        (Complex.I • ginibreFullComplexOfReal n (ginibreFullComplexIm n p.1)),
      Lp.coeFn_smul Complex.I (ginibreFullComplexOfReal n (ginibreFullComplexIm n p.1))]
      with z hr hi hpr hpi ha hs
    change (ginibreFullComplexOfReal n (ginibreFullComplexRe n p.1) +
      Complex.I • ginibreFullComplexOfReal n (ginibreFullComplexIm n p.1)) z = p.1 z
    rw [ha]
    simp only [Pi.add_apply]
    rw [hs]
    simp only [Pi.smul_apply]
    rw [hr, hi, hpr, hpi]
    simpa [smul_eq_mul, mul_comm] using Complex.re_add_im (p.1 z)
  · apply Lp.ext
    let R := ginibreGradientScalarMap n Complex.reCLM
    let J := ginibreGradientScalarMap n Complex.imCLM
    let C := ginibreGradientScalarMap n Complex.ofRealCLM
    filter_upwards [C.coeFn_compLpL (R.compLpL 2 (ginibreMeasure n) p.2),
      C.coeFn_compLpL (J.compLpL 2 (ginibreMeasure n) p.2),
      R.coeFn_compLpL p.2, J.coeFn_compLpL p.2,
      Lp.coeFn_add (C.compLpL 2 (ginibreMeasure n) (R.compLpL 2 (ginibreMeasure n) p.2))
        (Complex.I • C.compLpL 2 (ginibreMeasure n) (J.compLpL 2 (ginibreMeasure n) p.2)),
      Lp.coeFn_smul Complex.I (C.compLpL 2 (ginibreMeasure n)
        (J.compLpL 2 (ginibreMeasure n) p.2))]
      with z hr hi hpr hpi ha hs
    change (C.compLpL 2 (ginibreMeasure n) (R.compLpL 2 (ginibreMeasure n) p.2) +
      Complex.I • C.compLpL 2 (ginibreMeasure n) (J.compLpL 2 (ginibreMeasure n) p.2)) z = p.2 z
    rw [ha]
    simp only [Pi.add_apply]
    rw [hs]
    simp only [Pi.smul_apply]
    rw [hr, hi, hpr, hpi]
    ext k
    simpa [R, J, C, smul_eq_mul, mul_comm] using Complex.re_add_im (p.2 z k)

theorem ginibreComplexPairRe_mem_global {n : ℕ} {p : GinibreComplexGradientPair n}
    (hp : p ∈ ginibreGlobalComplexSmoothPairs n) :
    ginibreComplexPairRe n p ∈ ginibreGlobalRealSmoothPairs n := by
  rcases hp with ⟨f, hf, hc, hu, hg⟩
  refine ⟨fun z => (f z).re, Complex.reCLM.contDiff.comp hf,
    hc.comp_left (map_zero Complex.reCLM), ?_, ?_⟩
  · filter_upwards [ginibreFullComplexRe_ae n p.1, hu] with z h h0
    exact h.trans (congrArg Complex.re h0)
  · filter_upwards [(ginibreGradientScalarMap n Complex.reCLM).coeFn_compLpL p.2, hg]
      with z h h0
    change (ginibreGradientScalarMap n Complex.reCLM).compLpL 2 (ginibreMeasure n) p.2 z = _
    rw [h, h0]
    exact ginibreComplexGradient_re f (hf.differentiable (by simp)) z

theorem ginibreComplexPairIm_mem_global {n : ℕ} {p : GinibreComplexGradientPair n}
    (hp : p ∈ ginibreGlobalComplexSmoothPairs n) :
    ginibreComplexPairIm n p ∈ ginibreGlobalRealSmoothPairs n := by
  rcases hp with ⟨f, hf, hc, hu, hg⟩
  refine ⟨fun z => (f z).im, Complex.imCLM.contDiff.comp hf,
    hc.comp_left (map_zero Complex.imCLM), ?_, ?_⟩
  · filter_upwards [ginibreFullComplexIm_ae n p.1, hu] with z h h0
    exact h.trans (congrArg Complex.im h0)
  · filter_upwards [(ginibreGradientScalarMap n Complex.imCLM).coeFn_compLpL p.2, hg]
      with z h h0
    change (ginibreGradientScalarMap n Complex.imCLM).compLpL 2 (ginibreMeasure n) p.2 z = _
    rw [h, h0]
    exact ginibreComplexGradient_im f (hf.differentiable (by simp)) z

theorem ginibreComplexGradient_combination {n : ℕ} (f g : Configuration n → ℝ)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (z : Configuration n) :
    ginibreComplexEuclideanGradient (fun z => (f z : ℂ) + Complex.I * (g z : ℂ)) z =
      ginibreGradientScalarMap n Complex.ofRealCLM (ginibreEuclideanGradient f z) +
        Complex.I • ginibreGradientScalarMap n Complex.ofRealCLM (ginibreEuclideanGradient g z) :=
            by
  have h1 := Complex.ofRealCLM.hasFDerivAt.comp z (hf z).hasFDerivAt
  have h2 := ((Complex.I • Complex.ofRealCLM).hasFDerivAt).comp z (hg z).hasFDerivAt
  have h := (h1.add h2).fderiv
  ext k
  simp only [PiLp.add_apply, PiLp.smul_apply]
  rw [ginibreGradientScalarMap_apply, ginibreGradientScalarMap_apply,
    ginibreEuclideanGradient_coordinate, ginibreEuclideanGradient_coordinate]
  change fderiv ℝ (fun z => (f z : ℂ) + Complex.I * (g z : ℂ)) z
    (ginibreCoordinateDirection k) = _
  simpa [Function.comp_def, smul_eq_mul, Pi.add_def] using
    congrArg (fun L => L (ginibreCoordinateDirection k)) h

theorem ginibreComplexPairCombine_mem_interior {n : ℕ}
    {p q : GinibreRealGradientPair n}
    (hp : p ∈ ginibreInteriorSmoothPair n) (hq : q ∈ ginibreInteriorSmoothPair n) :
    ginibreComplexPairCombine n (p, q) ∈ ginibreInteriorComplexSmoothPairs n := by
  rcases hp with ⟨f, hf, hc, hs, hu, hg⟩
  rcases hq with ⟨g, hf', hc', hs', hu', hg'⟩
  let F : Configuration n → ℂ := fun z => (f z : ℂ) + Complex.I * (g z : ℂ)
  have hF : ContDiff ℝ ∞ F :=
    (Complex.ofRealCLM.contDiff.comp hf).add
      ((Complex.I • Complex.ofRealCLM).contDiff.comp hf')
  have hFc : HasCompactSupport F :=
    (hc.comp_left (map_zero Complex.ofRealCLM)).add
      (hc'.comp_left (map_zero (Complex.I • Complex.ofRealCLM)))
  have hFs : tsupport F ⊆ {z | CollisionFree z} := by
    apply Set.Subset.trans (tsupport_add _ _)
    apply Set.union_subset
    · exact (tsupport_comp_subset (map_zero Complex.ofRealCLM) f).trans hs
    · exact (tsupport_comp_subset (map_zero (Complex.I • Complex.ofRealCLM)) g).trans hs'
  refine ⟨F, hF, hFc, hFs, ?_, ?_⟩
  · filter_upwards [ginibreFullComplexOfReal_ae n p.1,
      ginibreFullComplexOfReal_ae n q.1, hu, hu',
      Lp.coeFn_add (ginibreFullComplexOfReal n p.1) (Complex.I • ginibreFullComplexOfReal n q.1),
      Lp.coeFn_smul Complex.I (ginibreFullComplexOfReal n q.1)] with z h1 h2 h3 h4 h5 h6
    change (ginibreFullComplexOfReal n p.1 + Complex.I • ginibreFullComplexOfReal n q.1) z = F z
    rw [h5]
    simp only [Pi.add_apply]
    rw [h6]
    simp only [Pi.smul_apply]
    simp [h1, h2, h3, h4, F, smul_eq_mul]
  · let C := ginibreGradientScalarMap n Complex.ofRealCLM
    filter_upwards [C.coeFn_compLpL p.2, C.coeFn_compLpL q.2, hg, hg',
      Lp.coeFn_add (C.compLpL 2 (ginibreMeasure n) p.2)
        (Complex.I • C.compLpL 2 (ginibreMeasure n) q.2),
      Lp.coeFn_smul Complex.I (C.compLpL 2 (ginibreMeasure n) q.2)]
      with z h1 h2 h3 h4 h5 h6
    change (C.compLpL 2 (ginibreMeasure n) p.2 + Complex.I • C.compLpL 2 (ginibreMeasure n) q.2) z =
        _
    rw [h5]
    simp only [Pi.add_apply]
    rw [h6]
    simp only [Pi.smul_apply]
    rw [h1, h2, h3, h4]
    exact (ginibreComplexGradient_combination f g
      (hf.differentiable (by simp)) (hf'.differentiable (by simp)) z).symm

/-- Lemma A.2, complex-valued global versus collision-free smooth gradient cores. -/
theorem ginibreComplexSmoothCore_closure_equivalence (n : ℕ) (hn : 0 < n) :
    closure (ginibreGlobalComplexSmoothPairs n) =
      closure (ginibreInteriorComplexSmoothPairs n) := by
  apply Set.Subset.antisymm
  · apply closure_minimal _ isClosed_closure
    intro p hp
    have hr : ginibreComplexPairRe n p ∈ closure (ginibreInteriorSmoothPair n) := by
      rw [← ginibreRealSmoothCore_closure_equivalence n hn]
      exact subset_closure (ginibreComplexPairRe_mem_global hp)
    have hi : ginibreComplexPairIm n p ∈ closure (ginibreInteriorSmoothPair n) := by
      rw [← ginibreRealSmoothCore_closure_equivalence n hn]
      exact subset_closure (ginibreComplexPairIm_mem_global hp)
    have hpair : (ginibreComplexPairRe n p, ginibreComplexPairIm n p) ∈
        closure (ginibreInteriorSmoothPair n ×ˢ ginibreInteriorSmoothPair n) := by
      rw [closure_prod_eq]
      exact ⟨hr, hi⟩
    have hm := image_closure_subset_closure_image
      (ginibreComplexPairCombine_continuous n) ⟨_, hpair, rfl⟩
    rw [ginibreComplexPair_reconstruct n p] at hm
    apply (closure_mono ?_) hm
    rintro x ⟨⟨p, q⟩, ⟨hp, hq⟩, rfl⟩
    exact ginibreComplexPairCombine_mem_interior hp hq
  · apply closure_mono
    rintro p ⟨f, hf, hc, _, hu, hg⟩
    exact ⟨f, hf, hc, hu, hg⟩

end
end GinibrePoincare

