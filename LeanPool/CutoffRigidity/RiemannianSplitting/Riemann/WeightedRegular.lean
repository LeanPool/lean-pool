/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedBochnerMain
import TauCeti.Geometry.Manifold.Riemannian.Hessian.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.GramSchmidt

/-! # G0: regularity of the Challenge operators on smooth functions

`theorem CutCur.weightedRegular`: for smooth `V`, `Γ(f,g)` and `𝓛 f` are smooth and `‖Hess f‖²`
is smooth (hence continuous) for smooth `f, g`.
-/

@[expose] public section
open Bundle Set
open TauCeti.Manifold
open scoped Manifold ContDiff Topology

namespace CutCur.WReg


variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]

/-- **(G0.4)** `‖Hess f‖²` is smooth (hence continuous) for smooth `f`. -/
theorem msmooth_mHessNormSq {f : M → ℝ} (hf : MSmooth F f) : MSmooth F (mHessNormSq F f) := by
  intro x
  obtain ⟨U, hU, hx, frame, hframe, horth⟩ := TauCeti.exists_isLocalFrameOn_orthonormal
    (I := 𝓘(ℝ, F)) (n := ∞) (F := F) (V := fun y : M ↦ TangentSpace 𝓘(ℝ, F) y) x
  have hsmooth : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞
      (fun y ↦ ∑ i, ∑ j, hessian 𝓘(ℝ, F) f y (frame i y) (frame j y) ^ 2) x := by
    refine contMDiffAt_finsetSum fun i _ ↦ contMDiffAt_finsetSum fun j _ ↦ ?_
    exact (contMDiffAt_hessian_pair (n := ∞) (m := ∞) (k := ∞) (γ := id)
      (by simp) (by simp) isOpen_univ
      ((hf.of_le (by simp)).contMDiffOn) (mem_univ x)
      (hframe.contMDiffAt hU hx i) (hframe.contMDiffAt hU hx j)).pow 2
  apply hsmooth.congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds hx] with y hy
  let b := OrthonormalBasis.mk (horth y hy) (hframe.generating hy).ge
  simpa only [b, OrthonormalBasis.coe_mk] using (mHessNormSq_eq_sum_hessian F f y b)

end CutCur.WReg

namespace CutCur

variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]

/-- **(G0)** Regularity of the Challenge operators on smooth functions. -/
theorem weightedRegular (V : M → ℝ) (hV : MSmooth F V) : WeightedRegular F V :=
  ⟨fun _ _ hf hg => WReg.msmooth_carre hf hg,
   fun _ hf => WReg.msmooth_mgenerator F hV hf,
   fun _ hf => (WReg.msmooth_mHessNormSq hf).continuous⟩

end CutCur
