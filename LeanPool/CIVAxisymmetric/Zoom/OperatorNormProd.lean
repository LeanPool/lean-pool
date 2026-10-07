/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# Operator-norm bounds on `ℝ × ℝ` from directional components

`ℝ × ℝ` carries the sup norm `‖(a, b)‖ = max |a| |b|` (`Prod.norm_def`), whose dual is the
`ℓ¹` norm: a continuous linear functional on `ℝ × ℝ` is controlled by the sum of its two
directional values. This file records that fact, once for a functional into any normed
space, and derives the analogous bound for a bilinear form (a continuous linear map into a
space of continuous linear maps) by applying it twice. Neither theorem mentions any
zoomed field; both are used to convert the pointwise radial/axial derivative bounds of
`eq:aniso:zoom:derivatives` into the operator-norm bounds the finite-axis closures of
`FiniteContradictionClosure.lean` consume.
-/

public section

open Set

noncomputable section

namespace CIV

/-- A continuous linear functional out of `ℝ × ℝ` (sup norm) is bounded by the sum of the
absolute values of its two directional values `L (1, 0)` and `L (0, 1)`: every vector's
coordinates are each bounded by its sup norm. -/
theorem norm_clm_le_norm_apply_add_norm_apply {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (L : (ℝ × ℝ) →L[ℝ] F) :
    ‖L‖ ≤ ‖L (1, 0)‖ + ‖L (0, 1)‖ := by
  refine L.opNorm_le_bound (by positivity) (fun v => ?_)
  have hv : v = v.1 • ((1 : ℝ), (0 : ℝ)) + v.2 • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  have hLv : L v = v.1 • L (1, 0) + v.2 • L (0, 1) := by
    conv_lhs => rw [hv]
    rw [L.map_add, L.map_smul, L.map_smul]
  have h1 : |v.1| ≤ ‖v‖ := by
    rw [Prod.norm_def, ← Real.norm_eq_abs]
    exact le_max_left _ _
  have h2 : |v.2| ≤ ‖v‖ := by
    rw [Prod.norm_def, ← Real.norm_eq_abs]
    exact le_max_right _ _
  calc
    ‖L v‖ = ‖v.1 • L (1, 0) + v.2 • L (0, 1)‖ := by rw [hLv]
    _ ≤ ‖v.1 • L (1, 0)‖ + ‖v.2 • L (0, 1)‖ := norm_add_le _ _
    _ = |v.1| * ‖L (1, 0)‖ + |v.2| * ‖L (0, 1)‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ ‖v‖ * ‖L (1, 0)‖ + ‖v‖ * ‖L (0, 1)‖ := by
        gcongr
    _ = (‖L (1, 0)‖ + ‖L (0, 1)‖) * ‖v‖ := by ring

/-- The bilinear-form analogue, specialised to an iterated Fréchet derivative: the operator
norm of the second derivative of `g : ℝ × ℝ → ℝ` at `y` is bounded, by applying
`norm_clm_le_norm_apply_add_norm_apply` twice (once to the second derivative itself, valued
in the functionals `(ℝ × ℝ) →L[ℝ] ℝ`, and once to each of the two resulting functionals), by
the sum of the absolute values of its four directional entries. Stating the bound at
`fderiv ℝ (fderiv ℝ g) y` itself, rather than at a bare universally quantified continuous
linear map, keeps every instance on the operator-norm topology that `fderiv` itself installs;
a free variable of the bare bilinear type picks up a competing (defeq but not syntactically
equal) topology instance from the plain continuous-linear-map arrow and the two do not unify. -/
theorem norm_fderiv_fderiv_le_of_apply (g : ℝ × ℝ → ℝ) (y : ℝ × ℝ) :
    ‖fderiv ℝ (fderiv ℝ g) y‖ ≤
      |fderiv ℝ (fderiv ℝ g) y (1, 0) (1, 0)| + |fderiv ℝ (fderiv ℝ g) y (1, 0) (0, 1)|
        + |fderiv ℝ (fderiv ℝ g) y (0, 1) (1, 0)| + |fderiv ℝ (fderiv ℝ g) y (0, 1) (0, 1)| := by
  set B := fderiv ℝ (fderiv ℝ g) y with hB
  have hB1 : ‖B (1, 0)‖ ≤ |B (1, 0) (1, 0)| + |B (1, 0) (0, 1)| := by
    refine (B (1, 0)).opNorm_le_bound (by positivity) (fun v => ?_)
    have hv : v = v.1 • ((1 : ℝ), (0 : ℝ)) + v.2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
    have hLv : B (1, 0) v = v.1 * B (1, 0) (1, 0) + v.2 * B (1, 0) (0, 1) := by
      conv_lhs => rw [hv]
      rw [(B (1, 0)).map_add, (B (1, 0)).map_smul, (B (1, 0)).map_smul, smul_eq_mul, smul_eq_mul]
    have h1 : |v.1| ≤ ‖v‖ := by rw [Prod.norm_def, ← Real.norm_eq_abs]; exact le_max_left _ _
    have h2 : |v.2| ≤ ‖v‖ := by rw [Prod.norm_def, ← Real.norm_eq_abs]; exact le_max_right _ _
    rw [Real.norm_eq_abs, hLv]
    calc
      |v.1 * B (1, 0) (1, 0) + v.2 * B (1, 0) (0, 1)|
          ≤ |v.1 * B (1, 0) (1, 0)| + |v.2 * B (1, 0) (0, 1)| := abs_add_le _ _
      _ = |v.1| * |B (1, 0) (1, 0)| + |v.2| * |B (1, 0) (0, 1)| := by rw [abs_mul, abs_mul]
      _ ≤ ‖v‖ * |B (1, 0) (1, 0)| + ‖v‖ * |B (1, 0) (0, 1)| := by gcongr
      _ = (|B (1, 0) (1, 0)| + |B (1, 0) (0, 1)|) * ‖v‖ := by ring
  have hB2 : ‖B (0, 1)‖ ≤ |B (0, 1) (1, 0)| + |B (0, 1) (0, 1)| := by
    refine (B (0, 1)).opNorm_le_bound (by positivity) (fun v => ?_)
    have hv : v = v.1 • ((1 : ℝ), (0 : ℝ)) + v.2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
    have hLv : B (0, 1) v = v.1 * B (0, 1) (1, 0) + v.2 * B (0, 1) (0, 1) := by
      conv_lhs => rw [hv]
      rw [(B (0, 1)).map_add, (B (0, 1)).map_smul, (B (0, 1)).map_smul, smul_eq_mul, smul_eq_mul]
    have h1 : |v.1| ≤ ‖v‖ := by rw [Prod.norm_def, ← Real.norm_eq_abs]; exact le_max_left _ _
    have h2 : |v.2| ≤ ‖v‖ := by rw [Prod.norm_def, ← Real.norm_eq_abs]; exact le_max_right _ _
    rw [Real.norm_eq_abs, hLv]
    calc
      |v.1 * B (0, 1) (1, 0) + v.2 * B (0, 1) (0, 1)|
          ≤ |v.1 * B (0, 1) (1, 0)| + |v.2 * B (0, 1) (0, 1)| := abs_add_le _ _
      _ = |v.1| * |B (0, 1) (1, 0)| + |v.2| * |B (0, 1) (0, 1)| := by rw [abs_mul, abs_mul]
      _ ≤ ‖v‖ * |B (0, 1) (1, 0)| + ‖v‖ * |B (0, 1) (0, 1)| := by gcongr
      _ = (|B (0, 1) (1, 0)| + |B (0, 1) (0, 1)|) * ‖v‖ := by ring
  have hB0 : ‖B‖ ≤ ‖B (1, 0)‖ + ‖B (0, 1)‖ := by
    refine B.opNorm_le_bound (by positivity) (fun v => ?_)
    have hv : v = v.1 • ((1 : ℝ), (0 : ℝ)) + v.2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
    have hLv : B v = v.1 • B (1, 0) + v.2 • B (0, 1) := by
      conv_lhs => rw [hv]
      rw [B.map_add, B.map_smul, B.map_smul]
    have h1 : |v.1| ≤ ‖v‖ := by rw [Prod.norm_def, ← Real.norm_eq_abs]; exact le_max_left _ _
    have h2 : |v.2| ≤ ‖v‖ := by rw [Prod.norm_def, ← Real.norm_eq_abs]; exact le_max_right _ _
    calc
      ‖B v‖ = ‖v.1 • B (1, 0) + v.2 • B (0, 1)‖ := by rw [hLv]
      _ ≤ ‖v.1 • B (1, 0)‖ + ‖v.2 • B (0, 1)‖ := norm_add_le _ _
      _ = |v.1| * ‖B (1, 0)‖ + |v.2| * ‖B (0, 1)‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ ‖v‖ * ‖B (1, 0)‖ + ‖v‖ * ‖B (0, 1)‖ := by gcongr
      _ = (‖B (1, 0)‖ + ‖B (0, 1)‖) * ‖v‖ := by ring
  linarith only [hB0, hB1, hB2]

end CIV
