/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Local.PonomarenkoCrossNormalizedAxial

/-!
# Real-radial boundary derivatives for the cross-normalized branches

The cross-normalized Ponomarenko modules formulate their local boundary calculations using the
complex derivative in the radial variable.  The physical radial variable is real.  This file
bridges those two formulations by restricting a complex-differentiable function to the real
axis and applying the ordinary real derivative to the resulting map `ℝ → ℂ`.

Only pointwise interface identities at `r = 1` are recorded here.  In particular, there is no
claim about Sobolev regularity or about a globally defined eigenmode.
-/

@[expose] public section

noncomputable section

namespace FastDynamo
namespace PonomarenkoRealRadialBridge

open Complex
open PonomarenkoCrossNormalizedJump
open PonomarenkoCrossNormalizedAxial

/-! ## Generic restriction bridge -/

/-- Restricting a complex-differentiable scalar function to the real axis preserves its
derivative.  This is the chain rule for the real-linear inclusion `ℝ → ℂ`. -/
theorem hasDerivAt_realRestriction
    {f : ℂ → ℂ} {f' : ℂ} {x : ℝ} (hf : HasDerivAt f f' (x : ℂ)) :
    HasDerivAt (fun r : ℝ ↦ f (r : ℂ)) f' x :=
  hf.comp_ofReal

/-- The literal derivative of the real restriction agrees with the complex derivative at a
real point. -/
theorem deriv_realRestriction_eq
    {f : ℂ → ℂ} {x : ℝ} (hf : DifferentiableAt ℂ f (x : ℂ)) :
    deriv (fun r : ℝ ↦ f (r : ℂ)) x = deriv f (x : ℂ) :=
  (hasDerivAt_realRestriction hf.hasDerivAt).deriv

/-- Consequently, a boundary derivative jump computed after literal restriction to `ℝ` is the
same jump as the one computed using the complex derivative. -/
theorem realDerivativeJump_eq_boundaryDerivativeJump
    {inside outside : ℂ → ℂ}
    (hinside : DifferentiableAt ℂ inside (1 : ℂ))
    (houtside : DifferentiableAt ℂ outside (1 : ℂ)) :
    deriv (fun r : ℝ ↦ outside (r : ℂ)) 1 -
        deriv (fun r : ℝ ↦ inside (r : ℂ)) 1 =
      boundaryDerivativeJump inside outside := by
  rw [deriv_realRestriction_eq houtside, deriv_realRestriction_eq hinside]
  rfl

/-- If `f` is complex differentiable at `κ`, then `r ↦ c · f (κ r)` is complex differentiable at the
interface radius `r = 1`.  This is the common shape of every cross-normalized branch. -/
private theorem differentiableAt_const_mul_comp_one
    {f : ℂ → ℂ} {κ c : ℂ} (hf : DifferentiableAt ℂ f κ) :
    DifferentiableAt ℂ (fun r : ℂ ↦ c * f (κ * r)) 1 := by
  simpa only [Function.comp_apply] using
    ((hf.hasDerivAt.comp_of_eq (1 : ℂ) (κ_mul_hasDerivAt κ) (by simp)).const_mul c).differentiableAt

/-- The regular order-two branch `r ↦ K₂(κ) I₂(κr)` is complex differentiable at `r = 1`, since
`I₂` is entire. -/
private theorem differentiableAt_plusInside_one (κ : ℂ) :
    DifferentiableAt ℂ (plusInside κ) 1 := by
  unfold plusInside
  exact differentiableAt_const_mul_comp_one
    (ModifiedBessel.I2_analyticAt κ).differentiableAt

/-- The decaying order-two branch `r ↦ I₂(κ) K₂(κr)` is complex differentiable at `r = 1` when
`0 < κ.re`. -/
private theorem differentiableAt_plusOutside_one {κ : ℂ} (hκ : 0 < κ.re) :
    DifferentiableAt ℂ (plusOutside κ) 1 := by
  unfold plusOutside
  exact differentiableAt_const_mul_comp_one
    (ModifiedBessel.hasDerivAt_K2 hκ).differentiableAt

/-- The signed regular order-zero branch `r ↦ -K₀(κ) I₀(κr)` is complex differentiable at `r = 1`,
since `I₀` is entire. -/
private theorem differentiableAt_minusInside_one (κ : ℂ) :
    DifferentiableAt ℂ (minusInside κ) 1 := by
  unfold minusInside
  exact differentiableAt_const_mul_comp_one
    (ModifiedBessel.I0_analyticAt κ).differentiableAt

/-- The signed decaying order-zero branch `r ↦ -I₀(κ) K₀(κr)` is complex differentiable at `r = 1`
when `0 < κ.re`. -/
private theorem differentiableAt_minusOutside_one {κ : ℂ} (hκ : 0 < κ.re) :
    DifferentiableAt ℂ (minusOutside κ) 1 := by
  unfold minusOutside
  exact differentiableAt_const_mul_comp_one
    (ModifiedBessel.hasDerivAt_K0 hκ).differentiableAt

/-! ## Literal real-radial jumps -/

/-- The literal real-radial order-two derivative jump is `-1`. -/
theorem plus_realDerivativeJump {κ : ℂ} (hκ : 0 < κ.re) :
    deriv (fun r : ℝ ↦ plusOutside κ (r : ℂ)) 1 -
        deriv (fun r : ℝ ↦ plusInside κ (r : ℂ)) 1 = -1 := by
  calc
    _ = boundaryDerivativeJump (plusInside κ) (plusOutside κ) :=
      realDerivativeJump_eq_boundaryDerivativeJump
        (differentiableAt_plusInside_one κ) (differentiableAt_plusOutside_one hκ)
    _ = -1 := plus_boundaryDerivativeJump hκ

/-- The literal real-radial signed order-zero derivative jump is `+1`. -/
theorem minus_realDerivativeJump {κ : ℂ} (hκ : 0 < κ.re) :
    deriv (fun r : ℝ ↦ minusOutside κ (r : ℂ)) 1 -
        deriv (fun r : ℝ ↦ minusInside κ (r : ℂ)) 1 = 1 := by
  calc
    _ = boundaryDerivativeJump (minusInside κ) (minusOutside κ) :=
      realDerivativeJump_eq_boundaryDerivativeJump
        (differentiableAt_minusInside_one κ) (differentiableAt_minusOutside_one hκ)
    _ = 1 := minus_boundaryDerivativeJump hκ

end PonomarenkoRealRadialBridge
end FastDynamo
