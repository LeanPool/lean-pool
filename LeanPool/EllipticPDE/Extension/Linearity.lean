/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Extension.BoundaryChart


/-!
# Linearity of the chart extension

Evans states the extension as a bounded linear operator, where Guo's proof produces an
extension for each class. The three maps the chart extension runs on are all precomposition
or multiplication by a fixed function, so the extension is linear in the class once the chart
and its graph are fixed. This file records that.

Each statement is written with an explicit lambda on both sides rather than `Pi.add`, because
the shear and the reflection are applied to the function argument and a goal written with
`Pi.add` does not match one written with a lambda.

## Main declarations

* `EllipticPdes.Extension.evenExt_add` and `evenExt_smul`: the even reflection is linear.
* `EllipticPdes.Extension.evenExtGrad_add` and `evenExtGrad_smul`: so is its gradient.
* `EllipticPdes.Extension.shearGrad_add` and `shearGrad_smul`: so is the shear's gradient.
* `EllipticPdes.Extension.chartExt_add` and `chartExt_smul`: so is the chart extension.
* `EllipticPdes.Extension.chartExtGrad_add` and `chartExtGrad_smul`: so is its gradient.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), §5.4 Theorem 1 (p. 253).
-/

@[expose] public section

open MeasureTheory Metric Set

noncomputable section

namespace EllipticPdes.Extension

open EllipticPdes.Sobolev (partialD)

variable {d : ℕ}

/-! ### The even reflection -/

/-- The even reflection is additive in the class. -/
theorem evenExt_add (j : Fin d) (u v : EuclideanSpace ℝ (Fin d) → ℝ) :
    evenExt j (fun x => u x + v x) = fun x => evenExt j u x + evenExt j v x := by
  funext x
  simp only [evenExt]
  split <;> rfl

/-- The even reflection commutes with a scalar. -/
theorem evenExt_smul (j : Fin d) (c : ℝ) (u : EuclideanSpace ℝ (Fin d) → ℝ) :
    evenExt j (fun x => c * u x) = fun x => c * evenExt j u x := by
  funext x
  simp only [evenExt]
  split <;> rfl

/-- The reflected gradient is additive in the gradient. -/
theorem evenExtGrad_add (j : Fin d) (g h : Fin d → EuclideanSpace ℝ (Fin d) → ℝ) (k : Fin d) :
    evenExtGrad j (fun i x => g i x + h i x) k
      = fun x => evenExtGrad j g k x + evenExtGrad j h k x := by
  funext x
  simp only [evenExtGrad]
  split
  · rfl
  · ring

/-- The reflected gradient commutes with a scalar. -/
theorem evenExtGrad_smul (j : Fin d) (c : ℝ) (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ)
    (k : Fin d) :
    evenExtGrad j (fun i x => c * g i x) k = fun x => c * evenExtGrad j g k x := by
  funext x
  simp only [evenExtGrad]
  split
  · rfl
  · ring

/-! ### The shear -/

/-- The shear's gradient is additive in the gradient. The statement is at the family, not at
one of its components, because the reflection takes the whole family as its argument. -/
theorem shearGrad_add (j : Fin d) (γ : EuclideanSpace ℝ (Fin d) → ℝ)
    (g h : Fin d → EuclideanSpace ℝ (Fin d) → ℝ) :
    shearGrad j γ (fun i x => g i x + h i x)
      = fun k x => shearGrad j γ g k x + shearGrad j γ h k x := by
  funext k x
  simp only [shearGrad]
  ring

/-- The shear's gradient commutes with a scalar. -/
theorem shearGrad_smul (j : Fin d) (γ : EuclideanSpace ℝ (Fin d) → ℝ) (c : ℝ)
    (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ) :
    shearGrad j γ (fun i x => c * g i x) = fun k x => c * shearGrad j γ g k x := by
  funext k x
  simp only [shearGrad]
  ring

/-! ### The chart extension -/

/-- **Chart extension is additive in the class.** -/
theorem chartExt_add (j : Fin d) (γ u v : EuclideanSpace ℝ (Fin d) → ℝ) :
    chartExt j γ (fun x => u x + v x) = fun y => chartExt j γ u y + chartExt j γ v y := by
  funext y
  simp only [chartExt]
  have h : (fun x => u (shear j γ x) + v (shear j γ x))
      = fun x => (fun z => u (shear j γ z)) x + (fun z => v (shear j γ z)) x := rfl
  rw [h, evenExt_add]

/-- **Chart extension commutes with a scalar.** -/
theorem chartExt_smul (j : Fin d) (γ : EuclideanSpace ℝ (Fin d) → ℝ) (c : ℝ)
    (u : EuclideanSpace ℝ (Fin d) → ℝ) :
    chartExt j γ (fun x => c * u x) = fun y => c * chartExt j γ u y := by
  funext y
  simp only [chartExt]
  have h : (fun x => c * u (shear j γ x))
      = fun x => c * (fun z => u (shear j γ z)) x := rfl
  rw [h, evenExt_smul]

/-- **Gradient of the chart extension is additive in the gradient.** -/
theorem chartExtGrad_add (j : Fin d) (γ : EuclideanSpace ℝ (Fin d) → ℝ)
    (g h : Fin d → EuclideanSpace ℝ (Fin d) → ℝ) (k : Fin d) :
    chartExtGrad j γ (fun i x => g i x + h i x) k
      = fun y => chartExtGrad j γ g k y + chartExtGrad j γ h k y := by
  funext y
  simp only [chartExtGrad, shearGrad_add, evenExtGrad_add]
  ring

/-- **Gradient of the chart extension commutes with a scalar.** -/
theorem chartExtGrad_smul (j : Fin d) (γ : EuclideanSpace ℝ (Fin d) → ℝ) (c : ℝ)
    (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ) (k : Fin d) :
    chartExtGrad j γ (fun i x => c * g i x) k = fun y => c * chartExtGrad j γ g k y := by
  funext y
  simp only [chartExtGrad, shearGrad_smul, evenExtGrad_smul]
  ring

end EllipticPdes.Extension
