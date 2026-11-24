/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.FormPullback
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.BottChern

/-!
# Pullback of closed real `(1,1)`-forms

This thin wrapper packages the already proved smooth-form pullback together
with preservation of closedness and real type `(1,1)`.
-/

@[expose] public section

namespace SGPT.Foundations.Analysis.FirstPass

noncomputable section

open scoped Manifold ContDiff

variable {k n : ℕ} {V M : Type*}
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

namespace ClosedRealOneOneForm

/-- Pullback of a closed real `(1,1)`-form by an actual holomorphic map. -/
def pullback {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    (a : ClosedRealOneOneForm n M) : ClosedRealOneOneForm k V :=
  ⟨SmoothRealForm.pullback hf a.val,
    a.property.1.pullback hf, a.property.2.pullback hf⟩

@[simp] theorem pullback_val {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    (a : ClosedRealOneOneForm n M) :
    (pullback hf a).val = SmoothRealForm.pullback hf a.val := rfl

theorem pullback_isSemipositive {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    {a : ClosedRealOneOneForm n M} (ha : a.val.IsSemipositive) :
    (pullback hf a).val.IsSemipositive :=
  ha.pullback hf

end ClosedRealOneOneForm

end

end SGPT.Foundations.Analysis.FirstPass
