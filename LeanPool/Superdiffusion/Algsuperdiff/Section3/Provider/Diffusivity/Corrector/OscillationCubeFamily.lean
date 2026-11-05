/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MatrixOperatorNorm
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Definitions
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# OscillationCubeFamily

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The concentric triadic cube family of `e.nablaw.oscillations`

`e.nablaw.oscillations` is stated for a mesh point `z in 3^n Zd ∩ cu_K` with `z
+ cu_{m-h} ⊆ cu_K`, and compares the oscillation of `grad w` on `z + cu_n` with
its size on `z + cu_{m-h}`.  Its proof passes through every intermediate scale.
The carrier is therefore the family of **concentric** open cubes

```
  U_j := z + cu_{n+j} = openCubeAtScale z (n + j) ,   0 ≤ j ≤ m - h - n ,
```

all centred at the same `z`.  Only `U_0` is a triadic cube in the lattice sense
(`z ∈ 3^n Zd`); the coarser members `U_j`, `j ≥ 1`, are cubes of side `3^{n+j}`
centred at a point of the *finer* lattice, so they are **not** members of
`Homogenization.TriadicCube` at their own scale.  This is why the whole argument
must be run on `Homogenization.openCubeAtScale`, and why this module exists.

CoarseGraining supplies `openCubeAtScale` together with openness,
measurability, the product description, the translation identity and the
dilation identity, but no nesting, no volume and no convexity.  Those three
facts are what the nested-recentring route consumes from the cube family
itself, and they are proved here.

## Contents

* `openCubeAtScale_subset_of_forall_abs_add_le` -- the general concentric /
  off-centre containment criterion, from which both `z + cu_n ⊆ z + cu_{n+j}`
  and `z + cu_{m-h} ⊆ cu_K` follow.
* `openCubeAtScale_subset_of_le` -- nesting in the scale.
* `volume_openCubeAtScale`, `volume_openCubeAtScale_toReal` -- the exact volume
  `(3^m)^d`, with positivity and finiteness.
* `convex_openCubeAtScale` -- convexity, the hypothesis of the mean-value
  inequality used to convert `sup |grad h|` into an oscillation bound.

## References

* ABK26, `e.nablaw.oscillations`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.Corrector

open HCPolySupport HCPolySupport.Book.Ch03 MeasureTheory

variable {d : ℕ}

/-- The half-width appearing in `openCubeAtScale` is the ordinary integer power
`3 ^ m`; this removes `Real.rpow` from every downstream computation. -/
theorem rpow_three_intCast (m : ℤ) :
    Real.rpow (3 : ℝ) ((m : ℤ) : ℝ) = (3 : ℝ) ^ m :=
  Real.rpow_intCast 3 m

theorem zpow_three_pos (m : ℤ) : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m

/-- Membership in the concentric cube `z + cu_m`, with the half-width written as
an integer power of three. -/
theorem mem_openCubeAtScale_iff (z : Vec d) (m : ℤ) (y : Vec d) :
    y ∈ openCubeAtScale z m ↔ ∀ i : Fin d, |y i - z i| < (3 : ℝ) ^ m / 2 := by
  simp only [openCubeAtScale, Set.mem_ofPred_eq, rpow_three_intCast]

/-- **The containment criterion.**

If every coordinate of the offset `z - w` is small enough to fit the cube of
scale `m` inside the cube of scale `n`, then it does.  Taking `z = w` gives the
concentric nesting `z + cu_m ⊆ z + cu_n` for `m ≤ n`; taking `w = 0`, `n = K`
gives the interior-mesh hypothesis `z + cu_{m-h} ⊆ cu_K` of
`e.nablaw.oscillations`. -/
theorem openCubeAtScale_subset_of_forall_abs_add_le {z w : Vec d} {m n : ℤ}
    (h : ∀ i : Fin d, |z i - w i| + (3 : ℝ) ^ m / 2 ≤ (3 : ℝ) ^ n / 2) :
    openCubeAtScale z m ⊆ openCubeAtScale w n := by
  intro y hy
  rw [mem_openCubeAtScale_iff] at hy ⊢
  intro i
  have hyi : |y i - z i| < (3 : ℝ) ^ m / 2 := hy i
  have htri : |y i - w i| ≤ |y i - z i| + |z i - w i| := abs_sub_le (y i) (z i) (w i)
  linarith [h i]

/-- Concentric nesting: the cube family `U_j = z + cu_{n+j}` is increasing. -/
theorem openCubeAtScale_subset_of_le (z : Vec d) {m n : ℤ} (hmn : m ≤ n) :
    openCubeAtScale z m ⊆ openCubeAtScale z n := by
  refine openCubeAtScale_subset_of_forall_abs_add_le ?_
  intro i
  have hpow : (3 : ℝ) ^ m ≤ (3 : ℝ) ^ n :=
    zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hmn
  simp only [sub_self, abs_zero, zero_add]
  linarith

/-- The exact Lebesgue volume of a concentric triadic cube. -/
theorem volume_openCubeAtScale (z : Vec d) (m : ℤ) :
    volume (openCubeAtScale z m) = ENNReal.ofReal ((3 : ℝ) ^ m) ^ d := by
  rw [openCubeAtScale_eq_pi_Ioo, volume_pi_pi]
  simp only [Real.volume_Ioo, rpow_three_intCast]
  have hbody : ∀ i : Fin d,
      ENNReal.ofReal (z i + (3 : ℝ) ^ m / 2 - (z i - (3 : ℝ) ^ m / 2)) =
        ENNReal.ofReal ((3 : ℝ) ^ m) := by
    intro i
    congr 1
    ring
  rw [Finset.prod_congr rfl fun i (_ : i ∈ Finset.univ) => hbody i, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

theorem volume_openCubeAtScale_ne_top (z : Vec d) (m : ℤ) :
    volume (openCubeAtScale z m) ≠ ⊤ := by
  rw [volume_openCubeAtScale]
  exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top

theorem volume_openCubeAtScale_toReal (z : Vec d) (m : ℤ) :
    (volume (openCubeAtScale z m)).toReal = ((3 : ℝ) ^ m) ^ d := by
  rw [volume_openCubeAtScale, ENNReal.toReal_pow, ENNReal.toReal_ofReal
    (zpow_three_pos m).le]

theorem volume_openCubeAtScale_toReal_pos (z : Vec d) (m : ℤ) :
    0 < (volume (openCubeAtScale z m)).toReal := by
  rw [volume_openCubeAtScale_toReal]
  exact pow_pos (zpow_three_pos m) d

/-- Convexity of the concentric cube, the hypothesis under which the mean-value
inequality turns a bound on `sup |grad h|` into the birth-scale forcing size. -/
theorem convex_openCubeAtScale (z : Vec d) (m : ℤ) :
    Convex ℝ (openCubeAtScale z m) := by
  rw [openCubeAtScale_eq_pi_Ioo]
  exact convex_pi fun i _ => convex_Ioo _ _

end Algsuperdiff.Section3.Provider.Diffusivity.Corrector
