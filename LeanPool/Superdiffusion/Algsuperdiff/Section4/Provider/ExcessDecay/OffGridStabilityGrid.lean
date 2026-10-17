/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.HighContrastHomogenization.Support.Geometry.BoundaryLayer
public import LeanPool.HighContrastHomogenization.Support.Geometry.CubeMeasure

/-!
# OffGridStabilityGrid

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The triadic grid as a tiling: the addressing lemmas for the covering geometry

The printed proof of `l.lambdas.stability` (ABK26) decomposes an **off-grid**
cube `x + □_k` by *grid* triadic cubes, using the greedy family

```
𝒢_n(U) = { z ∈ 3^n ℤ^d ∖ (already covered) : z + □_{n+1} ⊆ U } .
```

Everything about that family rests on three facts about CoarseGraining's
triadic cubes which CoarseGraining itself only records *relative to a fixed
root cube* (`descendantsAtDepth`, `pairwiseDisjoint_descendantsAtDepth`.):

* at each scale the half-open cubes **tile** `ℝ^d` — every point lies in exactly
  one, and its address is a floor;
* every cube sits inside its `parentCube`;
* two arbitrary half-open triadic cubes are **nested or disjoint**, with no
  common root assumed.

This module proves those three, which is the addressing half of the covering
geometry.  Nothing here mentions the homogenization error, coefficients, or
measures of anything but cubes: it is pure grid combinatorics on `Vec d = Fin d
→ ℝ`.

## Why CoarseGraining's lemmas do not already give this

`Homogenization.pairwiseDisjoint_descendantsAtDepth` and
`Homogenization.cubeSet_eq_iUnion_descendantsAtDepth` are indexed by a *root*
cube `Q` and describe only the sub-tree below it.  The greedy family of an
off-grid cube contains cubes of unboundedly many scales that have **no common
triadic ancestor inside the off-grid cube**, so the sub-tree A cannot express
its disjointness.  `cubeAt` below supplies the missing global address map.

## Main results

* `mem_cubeSet_cubeAt`, `eq_cubeAt_of_mem_cubeSet` — the tiling and its address.
* `cubeSet_subset_cubeSet_parentCube` — a cube sits in its parent.
* `cubeSet_subset_of_le_of_mem_of_mem` — nested-or-disjoint, root-free.

## References

* ABK26, `l.lambdas.stability`, (the greedy family `𝒢_n(U)`).
* ABK26, `e.mathcalE.stability.applied`, (the consumer).
* CoarseGraining, `Homogenization/Geometry/TriadicCube.lean`,
  `Homogenization/Geometry/TriadicPartition.lean`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport

noncomputable section

variable {d : ℕ}

/-! ## 1. The scale factor -/

theorem cubeScaleFactor_pos' (Q : TriadicCube d) : 0 < cubeScaleFactor Q := by
  exact zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale

/-! ## 2. The address map -/

/-- **The triadic address of a point at a given scale.**  This is the unique
half-open triadic cube of scale `m` containing `x`; its index is the floor
`⌊x i / 3^m + 1/2⌋`. -/
def cubeAt (m : ℤ) (x : Vec d) : TriadicCube d where
  scale := m
  index := fun i => ⌊x i / (3 : ℝ) ^ m + (1 / 2 : ℝ)⌋

@[simp] theorem cubeAt_scale (m : ℤ) (x : Vec d) : (cubeAt m x).scale = m := rfl

@[simp] theorem cubeScaleFactor_cubeAt (m : ℤ) (x : Vec d) :
    cubeScaleFactor (cubeAt (d := d) m x) = (3 : ℝ) ^ m := rfl

/-- **The grid covers.** -/
theorem mem_cubeSet_cubeAt (m : ℤ) (x : Vec d) : x ∈ cubeSet (cubeAt m x) := by
  intro i
  have hs : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  have hfl := Int.floor_le (x i / (3 : ℝ) ^ m + (1 / 2 : ℝ))
  have hfl' := Int.lt_floor_add_one (x i / (3 : ℝ) ^ m + (1 / 2 : ℝ))
  constructor
  · have h : ((⌊x i / (3 : ℝ) ^ m + (1 / 2 : ℝ)⌋ : ℝ) - (1 / 2 : ℝ)) ≤ x i / (3 : ℝ) ^ m := by
      linarith only [hfl]
    have := mul_le_mul_of_nonneg_right h hs.le
    rwa [div_mul_cancel₀ _ hs.ne'] at this
  · have h : x i / (3 : ℝ) ^ m < ((⌊x i / (3 : ℝ) ^ m + (1 / 2 : ℝ)⌋ : ℝ) + (1 / 2 : ℝ)) := by
      linarith only [hfl']
    have := mul_lt_mul_of_pos_right h hs
    rwa [div_mul_cancel₀ _ hs.ne'] at this

/-- **The grid is a tiling**: membership determines the address. -/
theorem eq_cubeAt_of_mem_cubeSet {Q : TriadicCube d} {x : Vec d} (hx : x ∈ cubeSet Q) :
    Q = cubeAt Q.scale x := by
  have hs : (0 : ℝ) < (3 : ℝ) ^ Q.scale := zpow_pos (by norm_num) Q.scale
  have hidx : ∀ i, Q.index i = ⌊x i / (3 : ℝ) ^ Q.scale + (1 / 2 : ℝ)⌋ := by
    intro i
    obtain ⟨hlo, hhi⟩ := hx i
    have hscale : cubeScaleFactor Q = (3 : ℝ) ^ Q.scale := rfl
    rw [hscale] at hlo hhi
    have hlo' : ((Q.index i : ℝ) - (1 / 2 : ℝ)) ≤ x i / (3 : ℝ) ^ Q.scale :=
      (le_div_iff₀ hs).2 hlo
    have hhi' : x i / (3 : ℝ) ^ Q.scale < ((Q.index i : ℝ) + (1 / 2 : ℝ)) :=
      (div_lt_iff₀ hs).2 hhi
    have h1 : (Q.index i : ℝ) ≤ x i / (3 : ℝ) ^ Q.scale + (1 / 2 : ℝ) := by
      linarith only [hlo']
    have h2 : x i / (3 : ℝ) ^ Q.scale + (1 / 2 : ℝ) < (Q.index i : ℝ) + 1 := by
      linarith only [hhi']
    exact (Int.floor_eq_iff.2 ⟨h1, by exact_mod_cast h2⟩).symm
  cases Q with
  | mk scale index =>
      refine congrArg₂ TriadicCube.mk rfl ?_
      funext i
      exact hidx i

/-- Two triadic cubes of the same scale sharing a point are equal. -/
theorem eq_of_scale_eq_of_mem_of_mem {Q R : TriadicCube d} {x : Vec d}
    (hscale : Q.scale = R.scale) (hQ : x ∈ cubeSet Q) (hR : x ∈ cubeSet R) : Q = R := by
  rw [eq_cubeAt_of_mem_cubeSet hQ, eq_cubeAt_of_mem_cubeSet hR, hscale]

/-! ## 3. The parent inclusion -/

@[simp] theorem cubeScaleFactor_parentCube (Q : TriadicCube d) :
    cubeScaleFactor (parentCube Q) = 3 * cubeScaleFactor Q := by
  have h3 : (3 : ℝ) ≠ 0 := by norm_num
  simp [cubeScaleFactor, parentCube, zpow_add₀ h3, mul_comm]

/-- **A triadic cube sits inside its parent.**

Proved directly from the coordinate description: with
`r i = (Q.index i + 1) % 3 ∈ {0, 1, 2}` one has
`3 * (parentCube Q).index i = Q.index i + 1 - r i`, so the parent's coordinate
window `[(p - 1/2)·3^{m+1}, (p + 1/2)·3^{m+1})` contains
`[(q - 1/2)·3^m, (q + 1/2)·3^m)`. -/
theorem cubeSet_subset_cubeSet_parentCube (Q : TriadicCube d) :
    cubeSet Q ⊆ cubeSet (parentCube Q) := by
  intro x hx i
  have hs : (0 : ℝ) < cubeScaleFactor Q := cubeScaleFactor_pos' Q
  obtain ⟨hlo, hhi⟩ := hx i
  set q : ℤ := Q.index i with hq
  set p : ℤ := (parentCube Q).index i with hp
  have hpdef : p = (q + 1) / 3 := rfl
  set r : ℤ := (q + 1) % 3 with hr
  have hdiv : 3 * p + r = q + 1 := by
    rw [hpdef, hr]; omega
  have hr0 : (0 : ℤ) ≤ r := by rw [hr]; omega
  have hr3 : r < 3 := by rw [hr]; omega
  have hr0' : (0 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr0
  have hr3' : (r : ℝ) ≤ 2 := by
    have : r ≤ 2 := by omega
    exact_mod_cast this
  have hdiv' : 3 * (p : ℝ) + (r : ℝ) = (q : ℝ) + 1 := by exact_mod_cast hdiv
  rw [cubeScaleFactor_parentCube]
  constructor
  · have hstep : ((p : ℝ) - (1 / 2 : ℝ)) * (3 * cubeScaleFactor Q) ≤
        ((q : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q := by
      have hcoef : ((p : ℝ) - (1 / 2 : ℝ)) * 3 ≤ ((q : ℝ) - (1 / 2 : ℝ)) := by
        linarith only [hdiv', hr0']
      calc ((p : ℝ) - (1 / 2 : ℝ)) * (3 * cubeScaleFactor Q)
            = (((p : ℝ) - (1 / 2 : ℝ)) * 3) * cubeScaleFactor Q := by ring
        _ ≤ ((q : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q :=
            mul_le_mul_of_nonneg_right hcoef hs.le
    exact le_trans hstep hlo
  · have hstep : ((q : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q ≤
        ((p : ℝ) + (1 / 2 : ℝ)) * (3 * cubeScaleFactor Q) := by
      have hcoef : ((q : ℝ) + (1 / 2 : ℝ)) ≤ ((p : ℝ) + (1 / 2 : ℝ)) * 3 := by
        linarith only [hdiv', hr3']
      calc ((q : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q
            ≤ (((p : ℝ) + (1 / 2 : ℝ)) * 3) * cubeScaleFactor Q :=
            mul_le_mul_of_nonneg_right hcoef hs.le
        _ = ((p : ℝ) + (1 / 2 : ℝ)) * (3 * cubeScaleFactor Q) := by ring
    exact lt_of_lt_of_le hhi hstep

/-- The parent of the address cube at scale `m` is the address cube at `m + 1`. -/
theorem parentCube_cubeAt (m : ℤ) (x : Vec d) :
    parentCube (cubeAt m x) = cubeAt (m + 1) x := by
  have hmem : x ∈ cubeSet (parentCube (cubeAt m x)) :=
    cubeSet_subset_cubeSet_parentCube _ (mem_cubeSet_cubeAt m x)
  have hscale : (parentCube (cubeAt (d := d) m x)).scale = m + 1 := rfl
  rw [eq_cubeAt_of_mem_cubeSet hmem, hscale]

/-! ## 4. Iterated parents and the nested-or-disjoint dichotomy -/

/-- The `j`-fold parent of a cube. -/
def ancestorCube (j : ℕ) (Q : TriadicCube d) : TriadicCube d :=
  parentCube^[j] Q

@[simp] theorem ancestorCube_zero (Q : TriadicCube d) : ancestorCube 0 Q = Q := rfl

theorem ancestorCube_succ (j : ℕ) (Q : TriadicCube d) :
    ancestorCube (j + 1) Q = parentCube (ancestorCube j Q) := by
  simp [ancestorCube, Function.iterate_succ_apply']

theorem ancestorCube_scale (j : ℕ) (Q : TriadicCube d) :
    (ancestorCube j Q).scale = Q.scale + (j : ℤ) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [ancestorCube_succ, parentCube_scale, ih]
      push_cast
      ring

theorem cubeSet_subset_cubeSet_ancestorCube (j : ℕ) (Q : TriadicCube d) :
    cubeSet Q ⊆ cubeSet (ancestorCube j Q) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [ancestorCube_succ]
      exact ih.trans (cubeSet_subset_cubeSet_parentCube _)

/-- **Nested or disjoint, without a common root.**

If a point lies in two half-open triadic cubes and the first has the smaller
scale, then the first is contained in the second.  This is the root-free
replacement for CoarseGraining's `pairwiseDisjoint_descendantsAtDepth`. -/
theorem cubeSet_subset_of_le_of_mem_of_mem {Q R : TriadicCube d} {x : Vec d}
    (hle : Q.scale ≤ R.scale) (hQ : x ∈ cubeSet Q) (hR : x ∈ cubeSet R) :
    cubeSet Q ⊆ cubeSet R := by
  set j : ℕ := (R.scale - Q.scale).toNat with hj
  have hjeq : (j : ℤ) = R.scale - Q.scale := Int.toNat_of_nonneg (sub_nonneg.2 hle)
  have hAscale : (ancestorCube j Q).scale = R.scale := by
    rw [ancestorCube_scale, hjeq]
    ring
  have hxA : x ∈ cubeSet (ancestorCube j Q) := cubeSet_subset_cubeSet_ancestorCube j Q hQ
  have hAR : ancestorCube j Q = R := eq_of_scale_eq_of_mem_of_mem hAscale hxA hR
  have := cubeSet_subset_cubeSet_ancestorCube j Q
  rwa [hAR] at this

end

end Algsuperdiff.Section4.Provider.ExcessDecay
