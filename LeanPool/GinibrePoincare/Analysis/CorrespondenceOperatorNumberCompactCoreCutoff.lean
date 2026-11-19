/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceOperatorNumberCompactCoreCutoff.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorNumberCompactCoreJets
/-!
# Correspondence operator number compact core cutoff

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondenceNumber_finite_cutoff_jets`.
-/

@[expose] public section
open MeasureTheory Filter
open scoped ContDiff ComplexConjugate BigOperators Topology
namespace GinibrePoincare
noncomputable section
open ComplexHermite

/-- The compact test function `z ↦ ginibreSpatialCutoff n m z * f z`. -/
def correspondenceNumberCutoff {n : ℕ} (f : Configuration n → ℂ)
    (hf : ContDiff ℝ ∞ f) (m : ℕ) : BKCompactTest n :=
  ⟨fun z=>(ginibreSpatialCutoff n m z : ℂ)*f z,
    (Complex.ofRealCLM.contDiff.comp (ginibreSpatialCutoff_smooth n m)).mul hf,
    ((ginibreSpatialCutoff_compact n m).comp_left Complex.ofReal_zero).mul_right⟩

theorem correspondenceNumberCutoff_second_tendsto {n : ℕ}
    (f : Configuration n → ℂ) (hf : ContDiff ℝ ∞ f) (j k : Fin n)
    (hQ : MemLp (dbarComponent (dbarComponent f j) k) 2 (complexGaussianMeasure n))
    (hR : MemLp (fun z => z j * dbarComponent f k z + z k * dbarComponent f j z) 2
        (complexGaussianMeasure
        n))
    (hZ : MemLp (fun z => z k * z j * f z) 2 (complexGaussianMeasure n)) :
    Tendsto (fun m=>(((correspondenceNumberCutoff f hf m).dbar j).dbar k).l2)
      atTop (𝓝 (hQ.toLp (dbarComponent (dbarComponent f j) k))) := by
  let A := fun m=>(gaussianSpatialCutoff_value_memLp _ hQ m).toLp
    (fun z=>(ginibreSpatialCutoff n m z : ℂ)*dbarComponent (dbarComponent f j) k z)
  let B := fun m=>(gaussianSpatialCutoff_derivativeTerm_memLp _ hR m).toLp
    (fun z=>((deriv (sobolevCutoff m) (configurationNormSq z) : ℝ) : ℂ)*(z j*dbarComponent f k z+z
        k*dbarComponent f j z))
  let C := fun m=>(correspondenceNumber_secondCutoff_memLp _ hZ m).toLp
    (fun z=>((deriv (deriv (sobolevCutoff m)) (configurationNormSq z) : ℝ) : ℂ)*(z k*z j*f z))
  have he m : (((correspondenceNumberCutoff f hf m).dbar j).dbar k).l2=A m+B m+C m := by
    apply Lp.ext
    filter_upwards [(((correspondenceNumberCutoff f hf m).dbar j).dbar k).l2_coe,
      Lp.coeFn_add (A m+B m) (C m), Lp.coeFn_add (A m) (B m),
      (gaussianSpatialCutoff_value_memLp _ hQ m).coeFn_toLp,
      (gaussianSpatialCutoff_derivativeTerm_memLp _ hR m).coeFn_toLp,
      (correspondenceNumber_secondCutoff_memLp _ hZ m).coeFn_toLp] with z h0 h1 h2 h3 h4 h5
    rw [h0, h1, Pi.add_apply, h2, Pi.add_apply, h3, h4, h5]
    change dbarComponent (dbarComponent (fun w=>(ginibreSpatialCutoff n m w : ℂ)*f w) j) k z=_
    rw [bkCutoff_product_second m hf j k z]
    ring
  have hA := gaussianSpatialCutoff_value_tendsto _ hQ (gaussianSpatialCutoff_value_memLp _ hQ)
  have hB := gaussianSpatialCutoff_derivativeTerm_tendsto _ hR
  have hC := correspondenceNumber_secondCutoff_tendsto _ hZ
  simpa only [he, add_zero] using (hA.add hB).add hC

theorem correspondenceNumber_finite_cutoff_jets (n : ℕ) (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) :
    let f:=finiteHermiteFunction n hn c
    let hf:=contDiff_finiteHermiteFunction_smooth n hn c
    Tendsto (fun m=>(correspondenceNumberCutoff f hf m).l2) atTop (𝓝 (finiteHermiteCombination n hn
        c)) ∧
    (∀j, Tendsto (fun m=>((correspondenceNumberCutoff f hf m).dbar j).l2) atTop (𝓝
        (finiteDbarComponentL2 n hn c j))) ∧
    (∀j k, Tendsto (fun m=>(((correspondenceNumberCutoff f hf m).dbar j).dbar k).l2)
      atTop (𝓝 (finiteHermiteCombination n hn (loweredCoefficients n (loweredCoefficients n c j)
          k)))) := by
  dsimp only
  let f:=finiteHermiteFunction n hn c
  let hf:=contDiff_finiteHermiteFunction_smooth n hn c
  have hv : MemLp f 2 (complexGaussianMeasure n) :=
    (Lp.memLp (finiteHermiteCombination n hn c)).ae_eq (finiteHermiteCombination_coeFn n hn c)
  have hd j : MemLp (dbarComponent f j) 2 (complexGaussianMeasure n) :=
    (Lp.memLp (finiteDbarComponentL2 n hn c j)).ae_eq (finiteDbarComponentL2_coeFn n hn c j)
  obtain ⟨hF, hFc, hvT, hdT⟩ := gaussianSpatialCutoff_graph_tendsto f hf hv hd
      (memLp_coordinate_mul_finiteHermiteFunction n hn c)
  have hve : hv.toLp f=finiteHermiteCombination n hn c := Lp.ext (hv.coeFn_toLp.trans
      (finiteHermiteCombination_coeFn n hn c).symm)
  have hde j : (hd j).toLp (dbarComponent f j)=finiteDbarComponentL2 n hn c j := Lp.ext ((hd
      j).coeFn_toLp.trans (finiteDbarComponentL2_coeFn n hn c j).symm)
  refine ⟨?_,?_,?_⟩
  · simpa [correspondenceNumberCutoff, BKCompactTest.l2, hve] using hvT
  · intro j
    have hed m : ((correspondenceNumberCutoff f hf m).dbar j).l2=
        smoothDbarComponentL2 (fun z=>(ginibreSpatialCutoff n m z : ℂ)*f z) (hF m) (hFc m) j := by
      apply Lp.ext
      exact ((correspondenceNumberCutoff f hf m).dbar j).l2_coe.trans
        (smoothDbarComponentL2_coeFn _ (hF m) (hFc m) j).symm
    have ht:=hdT j
    rw [hde j] at ht
    exact ht.congr (fun m=>(hed m).symm)
  · intro j k
    have he j : dbarComponent f j=finiteHermiteFunction n hn (loweredCoefficients n c j) :=
      funext (fun z=>dbarComponent_finiteHermiteFunction n hn c j z)
    have he2 : dbarComponent (dbarComponent f j) k=finiteHermiteFunction n hn (loweredCoefficients n
        (loweredCoefficients n c j) k) := by
      rw [he j]
      exact funext (fun z=>dbarComponent_finiteHermiteFunction n hn _ k z)
    have hQ : MemLp (dbarComponent (dbarComponent f j) k) 2 (complexGaussianMeasure n) := by
      rw [he2]
      exact (Lp.memLp (finiteHermiteCombination n hn _)).ae_eq (finiteHermiteCombination_coeFn n hn
          _)
    have hR : MemLp (fun z=>z j*dbarComponent f k z+z k*dbarComponent f j z) 2
        (complexGaussianMeasure n) := by
      simp_rw [he]
      exact (memLp_coordinate_mul_finiteHermiteFunction n hn _ j).add
          (memLp_coordinate_mul_finiteHermiteFunction n hn _ k)
    have ht := correspondenceNumberCutoff_second_tendsto f hf j k hQ hR
        (correspondenceNumber_double_coordinate_memLp n hn c j k)
    have hqe : hQ.toLp (dbarComponent (dbarComponent f j) k)=finiteHermiteCombination n hn
        (loweredCoefficients n (loweredCoefficients n c j) k) := by
      apply Lp.ext
      exact hQ.coeFn_toLp.trans (he2 ▸ (finiteHermiteCombination_coeFn n hn _).symm)
    rwa [hqe] at ht

end
end GinibrePoincare
