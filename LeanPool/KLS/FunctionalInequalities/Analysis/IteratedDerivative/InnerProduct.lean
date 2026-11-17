/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.IteratedDerivative.Bilinear
public import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Leibniz rule for an inner product with an operator

`iteratedFDeriv_inner_clm`: for globally `C^∞` maps `f g : D → E` into a real inner product space
and a continuous
linear `M : E →L[ℝ] E`, the `m`-th derivative of `y ↦ ⟪f y, M (g y)⟫` is the sum over all Boolean
subset allocations of
`⟪∂_{h_q} f, M ∂_{h_{¬q}} g⟫`, each with coefficient `1` (the raw bilinear Leibniz rule
`iteratedFDeriv_bilinear` for
the bundled form `(x, y) ↦ ⟪x, M y⟫`).
-/

@[expose] public section

noncomputable section
open scoped RealInnerProductSpace ContDiff

namespace FunctionalInequalities.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- Leibniz rule for `⟪f, M g⟫`: `Dᵐ⟪f, M g⟫(x)[h] = Σ_q ⟪∂_{h_q} f(x), M ∂_{h_{¬q}} g(x)⟫`. -/
theorem iteratedFDeriv_inner_clm {f g : D → E} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (M : E →L[ℝ] E) (m : ℕ) (h : Fin m → D) (x : D) :
    iteratedFDeriv ℝ m (fun y => ⟪f y, M (g y)⟫) x h =
      ∑ q : Fin m → Bool,
        ⟪directional (selected h q) f x, M (directional (selected h (fun i => !(q i))) g x)⟫ := by
    let B : E →L[ℝ] E →L[ℝ] ℝ :=
      (ContinuousLinearMap.compL ℝ E E ℝ).flip M ∘L
        (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ)
    have hB : ∀ a b : E, B a b = ⟪a, M b⟫ := fun a b => by
      change (⟪a, M b⟫ : ℝ) = ⟪a, M b⟫
      rfl
    have hfun : (fun y => B (f y) (g y)) = fun y => ⟪f y, M (g y)⟫ :=
      funext fun y => hB _ _
    rw [← hfun, iteratedFDeriv_bilinear B hf hg m h x]
    exact Finset.sum_congr rfl fun q _ => hB _ _

end FunctionalInequalities.Analysis
