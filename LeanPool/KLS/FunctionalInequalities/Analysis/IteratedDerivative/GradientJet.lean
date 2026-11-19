/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Iterated derivatives of a shifted map and of a gradient

Generic calculus supports for the jets of the centred cumulant-generating-function gradient
(Bizeul–Klartag–Lehec arXiv:2610.05474v1, p. 20, the sentence before (74); consumer
`Analysis/BakryEmery/Cumulant/Local.lean` section `GradientJets`):

* `iteratedFDeriv_sub_const_of_pos`: for `r ≥ 1`, subtracting a constant does not change the `r`-th
  iterated derivative of a smooth map between real normed spaces (no inner product, dimension,
  completeness or measure assumption);
* `inner_iteratedFDeriv_gradient_apply`: on a complete real inner product space,
  `⟪Dʳ(∇f)(x)[h], w⟫ = Dʳ⁺¹f(x)[h, w]` with `w` in the last slot.
-/

@[expose] public section

noncomputable section

open scoped RealInnerProductSpace ContDiff

namespace FunctionalInequalities.Analysis

section Shift

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- **Shift invariance of higher iterated derivatives**: for `r ≥ 1`,
`Dʳ(f − c)(x) = Dʳf(x)`. -/
theorem iteratedFDeriv_sub_const_of_pos {f : E → F} (hf : ContDiff ℝ ∞ f) (c : F) {r : ℕ}
    (hr : 1 ≤ r) (x : E) : iteratedFDeriv ℝ r (fun z => f z - c) x = iteratedFDeriv ℝ r f x := by
  have hf' : ContDiff ℝ r f := hf.of_le (WithTop.coe_le_coe.mpr (le_top : r ≤ (⊤ : ℕ∞)))
  have hc' : ContDiff ℝ r (fun _ : E => c) := contDiff_const
  calc
    iteratedFDeriv ℝ r (fun z => f z - c) x =
        iteratedFDeriv ℝ r f x - iteratedFDeriv ℝ r (fun _ : E => c) x := by
      exact
        (iteratedFDeriv_sub_apply (𝕜 := ℝ) (i := r) (f := f) (g := fun _ : E => c)
          hf'.contDiffAt hc'.contDiffAt)
    _ = iteratedFDeriv ℝ r f x := by
      rw [iteratedFDeriv_const_of_ne (by omega : r ≠ 0) c]
      simp

end Shift

section GradientJet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **Jets of the gradient pair with the next derivative**:
`⟪Dʳ(∇f)(x)[h], w⟫ = Dʳ⁺¹f(x)[h, w]`, the new direction `w` in the last slot. -/
theorem inner_iteratedFDeriv_gradient_apply {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (r : ℕ) (x : E)
    (h : Fin r → E) (w : E) :
    ⟪iteratedFDeriv ℝ r (gradient f) x h, w⟫ = iteratedFDeriv ℝ (r + 1) f x (Fin.snoc h w) := by
    have _hf : ContDiff ℝ ∞ f := hf
    let L : (E →L[ℝ] ℝ) ≃L[ℝ] E :=
      (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv
    have hpoint :
        iteratedFDeriv ℝ r (gradient f) x h =
          L (iteratedFDeriv ℝ r (fderiv ℝ f) x h) := by
      have hc :=
        L.iteratedFDeriv_comp_left
          (f := fderiv ℝ f) (x := x) (i := r)
      have hc' := congrArg (fun q => q h) hc
      change
        iteratedFDeriv ℝ r
            (fun y => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f y)) x h =
          (InnerProductSpace.toDual ℝ E).symm
            (iteratedFDeriv ℝ r (fderiv ℝ f) x h)
      simpa [L, Function.comp_def] using hc'
    calc
      ⟪iteratedFDeriv ℝ r (gradient f) x h, w⟫ =
          ⟪L (iteratedFDeriv ℝ r (fderiv ℝ f) x h), w⟫ := by
            rw [hpoint]
      _ = iteratedFDeriv ℝ (r + 1) f x (Fin.snoc h w) := by
        rw [iteratedFDeriv_succ_apply_right]
        simp [L]

end GradientJet

end FunctionalInequalities.Analysis
