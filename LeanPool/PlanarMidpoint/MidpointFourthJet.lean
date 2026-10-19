/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/
module

public import LeanPool.PlanarMidpoint.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Fourth-order geodesic midpoint algebra

This file checks the Dirichlet polynomial normalization and the cancellation
between opposite Christoffel tensors. The coefficients use divided derivatives:
`u_j = (1/j!) ∂ε^j γ`. No analytic expansion is assumed in these identities.
-/

@[expose] public section

noncomputable section

namespace PlanarMidpoint

private theorem jet_K_neg_coeff (c : Coeff) (u v : E) :
    K (-c) u v = -K c u v := by
  apply vec_ext <;> simp [K] <;> ring

private theorem jet_K_neg_left (c : Coeff) (u v : E) :
    K c (-u) v = -K c u v := by
  apply vec_ext <;> simp [K] <;> ring

private theorem jet_K_neg_right (c : Coeff) (u v : E) :
    K c u (-v) = -K c u v := by
  apply vec_ext <;> simp [K] <;> ring

/-- The obstruction is even when the connection and its spatial derivative
are simultaneously negated. -/
theorem obstruction_neg (c : Coeff) (J : E →L[ℝ] Coeff) (h : E) :
    obstruction (-c) (-J) h = obstruction c J h := by
  simp [obstruction, jet_K_neg_coeff, jet_K_neg_right]

/-- The second and fourth even Dirichlet primitives of `B₀ + B₂(t-1/2)²`. -/
def fourthDirichlet (B₀ B₂ : E) (t : ℝ) : E :=
  (((t - 1 / 2) ^ 2 - 1 / 4) / 2) • B₀ + (((t - 1 / 2) ^ 4 - 1 / 16) / 12) • B₂

@[simp] theorem fourthDirichlet_zero (B₀ B₂ : E) :
    fourthDirichlet B₀ B₂ 0 = 0 := by
  norm_num [fourthDirichlet]

@[simp] theorem fourthDirichlet_one (B₀ B₂ : E) :
    fourthDirichlet B₀ B₂ 1 = 0 := by
  norm_num [fourthDirichlet]

theorem fourthDirichlet_midpoint (B₀ B₂ : E) :
    fourthDirichlet B₀ B₂ (1 / 2) = -(1 / 8 : ℝ) • B₀ - (1 / 192 : ℝ) • B₂ := by
  norm_num [fourthDirichlet, sub_eq_add_neg, ← neg_smul]

theorem hasDerivAt_fourthDirichlet (B₀ B₂ : E) (t : ℝ) :
    HasDerivAt (fourthDirichlet B₀ B₂)
      ((t - 1 / 2) • B₀ + ((t - 1 / 2) ^ 3 / 3) • B₂) t := by
  have hs := (hasDerivAt_id t).sub_const (1 / 2 : ℝ)
  convert ((((hs.pow 2).sub_const (1 / 4)).div_const 2).smul_const B₀).add
    ((((hs.pow 4).sub_const (1 / 16)).div_const 12).smul_const B₂) using 1 <;>
      ext <;> simp [fourthDirichlet]; ring_nf; simp

theorem hasDerivAt_fourthDirichlet_velocity (B₀ B₂ : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ (s - 1 / 2) • B₀ + ((s - 1 / 2) ^ 3 / 3) • B₂)
      (B₀ + (t - 1 / 2) ^ 2 • B₂) t := by
  have hs := (hasDerivAt_id t).sub_const (1 / 2 : ℝ)
  convert (hs.smul_const B₀).add (((hs.pow 3).div_const 3).smul_const B₂) using 1 <;>
    ext <;> simp

/-- The quartic midpoint coefficient after solving the Dirichlet jet equations.
`H` denotes `(D_h²K)` in coefficient coordinates. -/
def fourthMidpointCoefficient (c : Coeff) (J : E →L[ℝ] Coeff)
    (H : Coeff) (h : E) : E :=
  (1 / 384 : ℝ) • (-4 • K c h (K c h (K c h h)) + 2 • K c (K c h h) (K c h h) + K H h h +
      obstruction c J h)

/-- The cubic jet vector `n = 2K(h,K(h,h)) - (D_hK)(h,h)`. -/
def cubicJetVector (c : Coeff) (J : E →L[ℝ] Coeff) (h : E) : E :=
  2 • K c h (K c h h) - K (J h) h h

/-- Constant term of the fourth jet's acceleration in centered time. -/
def fourthAccelerationZero (c : Coeff) (J : E →L[ℝ] Coeff) (h : E) : E :=
  (1 / 12 : ℝ) • K c h (cubicJetVector c J h) - (1 / 8 : ℝ) • K (J (K c h h)) h h

/-- Quadratic term of the fourth jet's acceleration in centered time. -/
def fourthAccelerationTwo (c : Coeff) (J : E →L[ℝ] Coeff) (H : Coeff) (h : E) : E :=
  -K c h (cubicJetVector c J h) - K c (K c h h) (K c h h) + 2 • K (J h) h (K c h h) + (1 / 2 : ℝ)
      • K (J (K c h h)) h h - (1 / 2 : ℝ) • K H h h

/-- Solving the quartic Dirichlet equation gives the exact coefficient. -/
theorem fourthDirichlet_coefficient (c : Coeff) (J : E →L[ℝ] Coeff)
    (H : Coeff) (h : E) :
    fourthDirichlet (fourthAccelerationZero c J h)
      (fourthAccelerationTwo c J H h) (1 / 2) = fourthMidpointCoefficient c J H h := by
  rw [fourthDirichlet_midpoint]
  apply vec_ext <;> simp [fourthAccelerationZero, fourthAccelerationTwo,
    fourthMidpointCoefficient, cubicJetVector, obstruction, K] <;> ring

/-- Opposite connections cancel every quartic contribution except the
first-order obstruction. -/
theorem fourthMidpointCoefficient_add_opposite (c : Coeff)
    (J : E →L[ℝ] Coeff) (H : Coeff) (h : E) :
    fourthMidpointCoefficient c J H h + fourthMidpointCoefficient (-c) (-J) (-H) h =
      (1 / 192 : ℝ) • obstruction c J h := by
  simp only [fourthMidpointCoefficient, jet_K_neg_coeff, jet_K_neg_left,
    jet_K_neg_right, neg_neg, obstruction_neg]
  module

/-- Multiplication by `4!` converts the sum of divided quartic coefficients
into the fourth derivative of the midpoint defect. -/
theorem fourth_defect_factor (c : Coeff) (J : E →L[ℝ] Coeff) (H : Coeff) (h : E) :
    (24 : ℝ) • (fourthMidpointCoefficient c J H h + fourthMidpointCoefficient (-c) (-J) (-H) h) =
        (1 / 8 : ℝ) • obstruction c J h := by
  rw [fourthMidpointCoefficient_add_opposite, smul_smul]
  norm_num

end PlanarMidpoint
