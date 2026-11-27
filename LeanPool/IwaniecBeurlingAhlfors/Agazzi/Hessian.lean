/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.Agazzi.Corollary2.Quasiconvexity
public import LeanPool.IwaniecBeurlingAhlfors.CalculusOfVariations.Quasiconvex.Hessian
import LeanPool.IwaniecBeurlingAhlfors.CalculusOfVariations.Lipschitz.Gradient

/-!
# Theorem 1 for Hessians (TeX line 285)

"In the case where `φ = Du` for some `u ∈ C^∞_per (Q)` this result had been proved in
[Guerra2026b]."

* `theorem1_hessian`: the Hessian case of Theorem 1, `∫_Q [L (A + D²u) − L (A)] ≥ 0` for every `A`
  and every `u ∈ C^∞_per (Q)`. It is Theorem 1 for `φ = Du`, which is smooth and periodic.
* `theorem1_hessian_iff`: at every `A`, this periodic inequality for all `u ∈ C^∞_per (Q)` is
  equivalent to `∫_{ℝ²} [L (A + D²u) − L (A)] ≥ 0` for all `u ∈ C_c^∞ (ℝ²)`, the form in which
  Guerra states the Hessian case (arXiv:2608.23388, Theorem 1.1, `External.Guerra.theorem1_1`;
  report, E1). This is the second-order form of Dacorogna, *Direct Methods in the Calculus of
  Variations*, Prop. 5.13, proved for every Borel, locally bounded integrand in the package
  `CalculusOfVariations` (`CalculusOfVariations.hessian_periodic_iff_hasCompactSupport`).

`D²u (x)` is `jacobian (fun y i => fderiv ℝ u y (Pi.single i 1)) x`, the derivative matrix of the
gradient `Du = (∂₁u, ∂₂u)`; it is the package's `CalculusOfVariations.hessian u x`
(`jacobian_gradient_eq_hessian`).
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace Agazzi

/-- `D²u` is the package's Hessian. -/
theorem jacobian_gradient_eq_hessian (u : (Fin 2 → ℝ) → ℝ) (x : Fin 2 → ℝ) :
    jacobian (fun y i => fderiv ℝ u y (Pi.single i 1)) x = CalculusOfVariations.hessian u x :=
  rfl

/-- The gradient of a smooth function is smooth. -/
private theorem contDiff_gradient {u : (Fin 2 → ℝ) → ℝ} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ fun y (i : Fin 2) => fderiv ℝ u y (Pi.single i 1) :=
  contDiff_pi.2 fun _ => (hu.fderiv_right le_rfl).clm_apply contDiff_const

/-- The gradient of a periodic differentiable function is periodic. -/
private theorem isPeriodic_gradient {u : (Fin 2 → ℝ) → ℝ} (hper : IsPeriodic u) :
    IsPeriodic fun y (i : Fin 2) => fderiv ℝ u y (Pi.single i 1) := by
  intro x k
  have h : (fun y => u (y + fun i => (k i : ℝ))) = u := funext fun y => hper y k
  have e := fderiv_comp_add_right (𝕜 := ℝ) (f := u) (fun i => (k i : ℝ)) (x := x)
  rw [h] at e
  funext i
  simp only [← e]

/-- **Theorem 1 for Hessians** (TeX line 285): for all `A ∈ ℝ^{2×2}` and all `u ∈ C^∞_per (Q)`,
`∫_Q [L (A + D²u) − L (A)] dx ≥ 0`.

Proof: Theorem 1 (`theorem1`) for `φ = Du`, which is `C^∞` and periodic. -/
theorem theorem1_hessian (A : Matrix (Fin 2) (Fin 2) ℝ) {u : (Fin 2 → ℝ) → ℝ}
    (hu : ContDiff ℝ ∞ u) (hper : IsPeriodic u) :
    0 ≤ ∫ x in unitSquare,
      (integrandL (A + jacobian (fun y i => fderiv ℝ u y (Pi.single i 1)) x) - integrandL A) :=
  theorem1 A (contDiff_gradient hu) (isPeriodic_gradient hper)

/-- **The periodic and the compactly supported forms of the Hessian case are equivalent** (report,
E1): at every `A`, `∫_Q [L (A + D²u) − L (A)] ≥ 0` for all `u ∈ C^∞_per (Q)` if and only if
`∫_{ℝ²} [L (A + D²u) − L (A)] ≥ 0` for all `u ∈ C_c^∞ (ℝ²)`.

Proof: `L` is continuous, hence Borel and locally bounded, and the package's second-order form of
Dacorogna's Prop. 5.13 applies (`CalculusOfVariations.hessian_periodic_iff_hasCompactSupport`). -/
theorem theorem1_hessian_iff (A : Matrix (Fin 2) (Fin 2) ℝ) :
    (∀ u : (Fin 2 → ℝ) → ℝ, ContDiff ℝ ∞ u → IsPeriodic u →
      0 ≤ ∫ x in unitSquare,
        (integrandL (A + jacobian (fun y i => fderiv ℝ u y (Pi.single i 1)) x) - integrandL A)) ↔
    ∀ u : (Fin 2 → ℝ) → ℝ, ContDiff ℝ ∞ u → HasCompactSupport u →
      0 ≤ ∫ x,
        (integrandL (A + jacobian (fun y i => fderiv ℝ u y (Pi.single i 1)) x) - integrandL A) :=
  CalculusOfVariations.hessian_periodic_iff_hasCompactSupport continuous_integrandL.measurable
    (CalculusOfVariations.isLocallyBounded_of_continuous continuous_integrandL) A

end Agazzi
