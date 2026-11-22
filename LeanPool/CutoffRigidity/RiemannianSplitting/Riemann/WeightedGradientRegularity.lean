/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedInterface

/-! # Regularity of the weighted gradient pairing -/

@[expose] public section
open Bundle
open scoped Manifold ContDiff

namespace CutCur.WReg

variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]

open CutoffRigidity

/-- **(G0.1)** The Riesz gradient of a smooth function is a smooth section. -/
theorem contMDiff_manifoldGradient_top {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, F).tangent ∞
      (T% (manifoldGradient (𝓘(ℝ, F)) f)) := by
  rw [manifoldGradient_eq_mgradient]
  have horder : (∞ : ℕ∞ω) + 1 ≤ ∞ := by simp
  have : IsManifold 𝓘(ℝ, F) (∞ + 1) M := IsManifold.of_le horder
  exact TauCeti.Manifold.contMDiff_mgradient (hf.of_le horder)

theorem contMDiff_mgrad {f : M → ℝ} (hf : MSmooth F f) :
    ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, F).tangent ∞ (T% (mgrad F f)) :=
  contMDiff_manifoldGradient_top hf

/-- **(G0.2)** `Γ(f,g)` is smooth for smooth `f,g`. -/
theorem msmooth_carre {f g : M → ℝ} (hf : MSmooth F f) (hg : MSmooth F g) :
    MSmooth F (carre F f g) :=
  ContMDiff.inner_bundle (E := TangentSpace 𝓘(ℝ, F)) (contMDiff_mgrad hf) (contMDiff_mgrad hg)

end CutCur.WReg
