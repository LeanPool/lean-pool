/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSpectralSobolevCompactMollification.lean.
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

public import LeanPool.GinibrePoincare.Analysis.LebesgueL2Convolution
public import LeanPool.GinibrePoincare.Analysis.WeakDerivativeMollification
public import LeanPool.GinibrePoincare.Analysis.LipschitzMollification

/-! # Genuine simultaneous smooth approximation of compact weak gradient pairs -/

@[expose] public section
open MeasureTheory Filter ContinuousLinearMap
open scoped Topology Convolution ContDiff
namespace GinibrePoincare
noncomputable section

/-- The pairs in Lebesgue `L²` represented almost everywhere by a compactly supported `C¹`
function `f` and its directional derivatives `Df · v i`. -/
def configurationCompactDirectionalPairs (m : ℕ) (I : Type*)
    (v : I → Configuration m) :
    Set (Lp ℝ 2 (volume : Measure (Configuration m)) ×
      (I → Lp ℝ 2 (volume : Measure (Configuration m)))) :=
  {p | ∃ f : Configuration m → ℝ, ContDiff ℝ 1 f ∧ HasCompactSupport f ∧
    (p.1 : Configuration m → ℝ) =ᵐ[volume] f ∧
    ∀ i, (p.2 i : Configuration m → ℝ) =ᵐ[volume]
      (fun x => fderiv ℝ f x (v i))}

/-- Every genuine compact ordinary weak gradient pair admits simultaneous smooth
value/derivative approximation in the actual L² graph topology. -/
theorem configuration_compact_weak_pair_mem_directional_closure (m : ℕ)
    {I : Type*} (v : I → Configuration m)
    (f : Configuration m → ℝ) (g : I → Configuration m → ℝ)
    (hf : MemLp f 2 volume) (hg : ∀ i, MemLp (g i) 2 volume)
    (hfc : HasCompactSupport f) (hgc : ∀ i, HasCompactSupport (g i))
    (hw : ∀ i, ∀ θ : Configuration m → ℝ,
      ContDiff ℝ ∞ θ → HasCompactSupport θ →
      (∫ x, g i x * θ x) = -(∫ x, f x * fderiv ℝ θ x (v i))) :
    (hf.toLp f, fun i => (hg i).toLp (g i)) ∈
      closure (configurationCompactDirectionalPairs m I v) := by
  let φ := lsiMollifier (Configuration m)
  let a := fun k => lebesgueSmoothCompactMollification m (φ k) f hf hfc
  let b := fun k i => lebesgueSmoothCompactMollification m (φ k) (g i) (hg i) (hgc i)
  have hta : Tendsto a atTop (𝓝 (hf.toLp f)) :=
    lebesgueSmoothCompactMollification_tendsto m φ
      (lsiMollifier_radius_tendsto _) f hf hfc
  have htb : Tendsto b atTop (𝓝 (fun i => (hg i).toLp (g i))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    exact lebesgueSmoothCompactMollification_tendsto m φ
      (lsiMollifier_radius_tendsto _) (g i) (hg i) (hgc i)
  apply isClosed_closure.mem_of_tendsto (hta.prodMk_nhds htb)
  apply Eventually.of_forall
  intro k
  apply subset_closure
  let F := (φ k).normed volume ⋆[lsmul ℝ ℝ, volume] f
  have hF : ContDiff ℝ ∞ F := (φ k).hasCompactSupport_normed.contDiff_convolution_left _
    ((φ k).contDiff_normed (n := ⊤)) (hf.locallyIntegrable (by norm_num))
  refine ⟨F, hF.of_le (by simp), (φ k).hasCompactSupport_normed.convolution _ hfc, ?_, ?_⟩
  · exact (memLp_bump_convolution_compact m (φ k) f hf hfc).coeFn_toLp
  · intro i
    have hd := weakDirectionalDerivative_convolution volume f (g i)
      ((φ k).normed volume) (v i) (hf.locallyIntegrable (by norm_num))
      ((φ k).contDiff_normed (n := ⊤)) (φ k).hasCompactSupport_normed (hw i)
    filter_upwards [(memLp_bump_convolution_compact m (φ k) (g i) (hg i) (hgc i)).coeFn_toLp]
      with x hx
    exact hx.trans (hd x).symm

end
end GinibrePoincare
