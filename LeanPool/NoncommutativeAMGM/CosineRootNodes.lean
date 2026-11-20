/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.CosineGap
public import LeanPool.NoncommutativeAMGM.ChebyshevRootAverage

/-! # Explicit complex root nodes and their Chebyshev cosine coordinates -/

@[expose] public section
namespace NoncommutativeAMGM

/-- The unit complex number of angle `2π / m` used for the even-indexed cosine nodes. -/
noncomputable def cosineRoot (m : ℕ) : ℂ :=
  Complex.exp (((2 * Real.pi / m : ℝ) : ℂ) * Complex.I)

/-- The unit complex number of angle `π / m` used to shift to the odd-indexed nodes. -/
noncomputable def cosineHalfRoot (m : ℕ) : ℂ :=
  Complex.exp (((Real.pi / m : ℝ) : ℂ) * Complex.I)

theorem cosineRoot_primitive {m : ℕ} (hm : 0 < m) : IsPrimitiveRoot (cosineRoot m) m := by
  have he : cosineRoot m = Complex.exp (2 * Real.pi * Complex.I / (m : ℂ)) := by
    unfold cosineRoot
    congr 1
    push_cast
    ring
  rw [he]
  exact Complex.isPrimitiveRoot_exp m hm.ne'

theorem cosineHalfRoot_pow {m : ℕ} (hm : 0 < m) : cosineHalfRoot m ^ m = -1 := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [cosineHalfRoot, ← Complex.exp_nat_mul]
  calc
    _ = Complex.exp (Real.pi * Complex.I) := by
      congr 1
      push_cast
      field_simp
    _ = -1 := Complex.exp_pi_mul_I

theorem cosineRoot_pow_re (m j : ℕ) : (cosineRoot m ^ j).re = chebyshevNode m (2 * j) := by
  rw [cosineRoot, ← Complex.exp_nat_mul]
  have he : (j : ℂ) * (((2 * Real.pi / m : ℝ) : ℂ) * Complex.I) =
      ((((2 * j : ℕ) : ℝ) * Real.pi / m : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [he]
  simp [Complex.exp_re, chebyshevNode]

theorem cosineHalfRoot_mul_pow_re (m j : ℕ) :
    (cosineHalfRoot m * cosineRoot m ^ j).re = chebyshevNode m (2 * j + 1) := by
  rw [cosineHalfRoot, cosineRoot, ← Complex.exp_nat_mul, ← Complex.exp_add]
  have he : (((Real.pi / m : ℝ) : ℂ) * Complex.I) +
      (j : ℂ) * (((2 * Real.pi / m : ℝ) : ℂ) * Complex.I) =
        ((((2 * j + 1 : ℕ) : ℝ) * Real.pi / m : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [he]
  simp [Complex.exp_re, chebyshevNode]

theorem chebyshevNode_reflect {m j : ℕ} (hm : 0 < m) (hj : j ≤ 2 * m) :
    chebyshevNode m (2 * m - j) = chebyshevNode m j := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  unfold chebyshevNode
  have he : ((2 * m - j : ℕ) : ℝ) * Real.pi / m = 2 * Real.pi - (j : ℝ) * Real.pi / m := by
    rw [Nat.cast_sub hj, Nat.cast_mul, Nat.cast_ofNat]
    field_simp
  rw [he, Real.cos_two_pi_sub]

end NoncommutativeAMGM
