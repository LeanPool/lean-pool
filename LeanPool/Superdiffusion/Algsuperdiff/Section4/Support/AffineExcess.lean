/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.NormalizedL2

/-!
# AffineExcess

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The affine excess `E(u,W)` and the best-affine slope

ABK26, §4.3 opens with two displays.  With `𝕃` the affine functions on `ℝ^d`,

```
E(u,W) := |W|^{-1/d} min_{ℓ ∈ 𝕃} ‖u − ℓ‖_{L²(W)},   ℓ(u,W) := argmin_{ℓ ∈ 𝕃} …   (e.excess.def)
E(u,□_m) := 3^{-m} min_{ℓ ∈ 𝕃} ‖u − ℓ‖_{L²(□_m)}                              (e.excess.def.cubes)
```

Both normalizers are consumed downstream --- the iteration lemma runs `E_j` at
the `|U_j|^{-1/d}` normalizer on truncated windows, while the §4.4 setup and
the reabsorption constant read `E_j` at `3^{-j}`.  This module defines both
normalizations and records the volume estimates used by their downstream
comparisons on sandwiched windows.

## Naming

The identifier `excess` is already taken in this repository: `cgExcess` and its
relatives are the §4.2 *coarse-grained ellipticity* excess `(σλ^{-1} −
C_cg)₊`, an unrelated object.  Everything here is therefore named
`affineExcess…` / `affineMinimizer…`, and no declaration in this tree is called
`excess`.

## Attainment, honestly

The source writes `min` and `argmin` and never argues attainment.  This module
defines the excess by `sInf` over the affine parameter space, which is
unconditional and agrees with the source wherever the minimum exists, and
supplies

* the projection inequality `affineExcessRaw_le_affineDistOn` (the `≤`-half of
  `min`, which is what every excess *estimate* is read off against), and
* the predicate `IsAffineMinimizer` --- the source's `ℓ(u,W)` as a property of a
  parameter pair, not as a chosen value.

Attainment itself is a separate theorem in
`Section4/Provider/ExcessDecay/AffineMinimizerExistence.lean`, with its
hypotheses visible.  No uniqueness statement is claimed anywhere: the source's
`argmin` notation is not backed by an argument, and none of the §4.3 estimates
needs one.

## Scope

Like `Section4/Support/Dirichlet.lean`, this module serves frozen statements
and is importable anywhere in the Section-4 tree.

## References

* ABK26, `e.excess.def`, `e.excess.def.cubes`.
-/

namespace Algsuperdiff.Section4.Support

open MeasureTheory
open HCPolySupport (Vec vecDot vecNormSq openCubeSet TriadicCube)

noncomputable section

variable {d : ℕ}

/-! ### Affine functions and the affine distance -/

/-- The affine function `x ↦ c + g · x` with intercept `c` and slope `g = ∇ℓ`. -/
def affineEval (c : ℝ) (g : Vec d) (x : Vec d) : ℝ := c + vecDot g x

/-- The difference of two affine functions is affine in the parameter
difference. -/
theorem affineEval_sub (c c' : ℝ) (g g' : Vec d) (x : Vec d) :
    affineEval c g x - affineEval c' g' x = affineEval (c - c') (g - g') x := by
  have hdot : vecDot (g - g') x = vecDot g x - vecDot g' x := by
    simp only [vecDot, Pi.sub_apply]
    rw [eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [affineEval, hdot]
  ring

theorem affineEval_zero (x : Vec d) : affineEval (0 : ℝ) (0 : Vec d) x = 0 := by
  simp [affineEval, vecDot]

/-- `‖u − ℓ‖_{L²(W)}` for the affine function `ℓ = (c, g)`. -/
def affineDistOn (W : Set (Vec d)) (u : Vec d → ℝ) (c : ℝ) (g : Vec d) : ℝ :=
  normalizedL2On W fun x => u x - affineEval c g x

theorem affineDistOn_nonneg (W : Set (Vec d)) (u : Vec d → ℝ) (c : ℝ) (g : Vec d) :
    0 ≤ affineDistOn W u c g :=
  normalizedL2On_nonneg _ _

/-! ### The excess as an infimum over affine competitors -/

/-- The competitor set `{‖u − ℓ‖_{L²(W)} : ℓ ∈ 𝕃}`, indexed by the parameter
pair `(c, g) ∈ ℝ × Vec d`. -/
def affineDistSet (W : Set (Vec d)) (u : Vec d → ℝ) : Set ℝ :=
  Set.range fun p : ℝ × Vec d => affineDistOn W u p.1 p.2

theorem affineDistSet_nonneg (W : Set (Vec d)) (u : Vec d → ℝ) :
    ∀ y ∈ affineDistSet W u, 0 ≤ y := by
  rintro y ⟨p, rfl⟩
  exact affineDistOn_nonneg _ _ _ _

theorem affineDistSet_bddBelow (W : Set (Vec d)) (u : Vec d → ℝ) :
    BddBelow (affineDistSet W u) :=
  ⟨0, fun y hy => affineDistSet_nonneg W u y hy⟩

theorem affineDistSet_nonempty (W : Set (Vec d)) (u : Vec d → ℝ) :
    (affineDistSet W u).Nonempty :=
  ⟨affineDistOn W u 0 0, ⟨(0, 0), rfl⟩⟩

/-- The **unnormalized excess** `min_{ℓ ∈ 𝕃} ‖u − ℓ‖_{L²(W)}`, taken as an
infimum. -/
def affineExcessRaw (W : Set (Vec d)) (u : Vec d → ℝ) : ℝ :=
  sInf (affineDistSet W u)

/-- The **excess** `E(u,W) = |W|^{-1/d} min_{ℓ ∈ 𝕃} ‖u − ℓ‖_{L²(W)}` of
`e.excess.def`. -/
def affineExcess (W : Set (Vec d)) (u : Vec d → ℝ) : ℝ :=
  ((volume W).toReal) ^ (-(d : ℝ)⁻¹) * affineExcessRaw W u

/-- The **scale-normalized excess** `3^{-j} min_{ℓ ∈ 𝕃} ‖u − ℓ‖_{L²(W)}`: the
normalizer of `e.excess.def.cubes`, read on an arbitrary window at the declared
scale `j`.  On `W = □_j` it agrees with `affineExcess`
(`affineExcess_openCubeSet`). -/
def affineExcessScaled (j : ℤ) (W : Set (Vec d)) (u : Vec d → ℝ) : ℝ :=
  (3 : ℝ) ^ (-j) * affineExcessRaw W u

theorem affineExcessRaw_nonneg (W : Set (Vec d)) (u : Vec d → ℝ) :
    0 ≤ affineExcessRaw W u :=
  Real.sInf_nonneg (affineDistSet_nonneg W u)

theorem affineExcess_nonneg (W : Set (Vec d)) (u : Vec d → ℝ) :
    0 ≤ affineExcess W u :=
  mul_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _) (affineExcessRaw_nonneg W u)

/-- **The projection inequality.**  The excess minimum is at most the distance to
*any* affine competitor.  This is the `≤`-half of the source's `min`, and it is
the inequality every excess estimate is read off against. -/
theorem affineExcessRaw_le_affineDistOn (W : Set (Vec d)) (u : Vec d → ℝ) (c : ℝ)
    (g : Vec d) : affineExcessRaw W u ≤ affineDistOn W u c g :=
  csInf_le (affineDistSet_bddBelow W u) ⟨(c, g), rfl⟩

/-- The zero-slope competitor: the excess is at most the deviation of `u` from any
constant. -/
theorem affineExcessRaw_le_normalizedL2On_sub_const (W : Set (Vec d)) (u : Vec d → ℝ)
    (c : ℝ) : affineExcessRaw W u ≤ normalizedL2On W fun x => u x - c := by
  have h := affineExcessRaw_le_affineDistOn W u c (0 : Vec d)
  have hfun : (fun x => u x - affineEval c (0 : Vec d) x) = fun x => u x - c := by
    funext x
    rw [affineEval]
    simp [vecDot]
  rwa [affineDistOn, hfun] at h

/-! ### The best-affine map `ℓ(u,W)` and its slope -/

/-- `(c, g)` **attains** the excess minimum: the source's `ℓ(u,W) = argmin`, as a
property of a parameter pair.  No uniqueness is claimed. -/
def IsAffineMinimizer (W : Set (Vec d)) (u : Vec d → ℝ) (c : ℝ) (g : Vec d) : Prop :=
  affineDistOn W u c g = affineExcessRaw W u

/-- The euclidean slope magnitude `|∇ℓ| = ‖g‖₂`: the quantity
`p_j = |∇ℓ(u,U_j)|` of the iteration lemma. -/
def slopeMagnitude (g : Vec d) : ℝ := Real.sqrt (vecNormSq g)

theorem slopeMagnitude_nonneg (g : Vec d) : 0 ≤ slopeMagnitude g := Real.sqrt_nonneg _

/-! ### The two normalizers -/

/-- For `x > 0` and `d ≠ 0`, the `d`-th power composed with the `(-1/d)` rpow is
inversion.  This is the arithmetic content of the normalizer `|W|^{-1/d}`. -/
private theorem rpow_neg_inv_pow {x : ℝ} (hx : 0 < x) (hd : d ≠ 0) :
    (x ^ d) ^ (-(d : ℝ)⁻¹) = x⁻¹ := by
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hd
  rw [← Real.rpow_natCast x d, ← Real.rpow_mul hx.le]
  rw [show (d : ℝ) * -(d : ℝ)⁻¹ = -1 by field_simp]
  rw [Real.rpow_neg_one]

/-- **`e.excess.def.cubes`.**  On the triadic cube `□_m` the general normalizer
`|W|^{-1/d}` *is* the cube normalizer `3^{-m}`; the two displays agree there.
This is the whole content of the specialization. -/
theorem affineExcess_openCubeSet (hd : d ≠ 0) (Q : TriadicCube d)
    (u : Vec d → ℝ) :
    affineExcess (openCubeSet Q) u = affineExcessScaled Q.scale (openCubeSet Q) u := by
  have hpos : (0 : ℝ) < (3 : ℝ) ^ Q.scale := zpow_pos (by norm_num) _
  have hvol : (volume (openCubeSet Q)).toReal = ((3 : ℝ) ^ Q.scale) ^ d := by
    rw [HCPolySupport.volume_openCubeSet_toReal, HCPolySupport.cubeVolume_eq_pow_scale]
  rw [affineExcess, affineExcessScaled, hvol, rpow_neg_inv_pow hpos hd, ← zpow_neg]

/-- The normalizer comparison on a window whose volume is sandwiched between the
volumes of the triadic cubes at scales `j-2` and `j` --- the aspect ratio
`3^{-2}` pinned by the source (: the sharper ratio `1/2` available for the
paper's own truncated windows is *not* used; constants stay at the printed
`3^{-2}`). -/
theorem rpow_normalizer_bounds (hd : d ≠ 0) {V : ℝ} {j : ℤ}
    (hlo : ((3 : ℝ) ^ (j - 2)) ^ d ≤ V) (hhi : V ≤ ((3 : ℝ) ^ j) ^ d) :
    (3 : ℝ) ^ (-j) ≤ V ^ (-(d : ℝ)⁻¹)
      ∧ V ^ (-(d : ℝ)⁻¹) ≤ 9 * (3 : ℝ) ^ (-j) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hposj : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos h3 _
  have hposj2 : (0 : ℝ) < (3 : ℝ) ^ (j - 2) := zpow_pos h3 _
  have hVpos : (0 : ℝ) < V := lt_of_lt_of_le (by positivity) hlo
  have hexp : -(d : ℝ)⁻¹ ≤ 0 := by
    have : (0 : ℝ) ≤ (d : ℝ)⁻¹ := by positivity
    linarith only [this]
  constructor
  · have h := Real.rpow_le_rpow_of_nonpos hVpos hhi hexp
    rwa [rpow_neg_inv_pow hposj hd, ← zpow_neg] at h
  · have h := Real.rpow_le_rpow_of_nonpos (by positivity) hlo hexp
    rw [rpow_neg_inv_pow hposj2 hd] at h
    have h9 : ((3 : ℝ) ^ (2 : ℤ)) = 9 := by norm_num
    have hid : ((3 : ℝ) ^ (j - 2))⁻¹ = 9 * (3 : ℝ) ^ (-j) := by
      rw [← zpow_neg, show -(j - 2) = -j + 2 by ring,
        zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), h9, mul_comm]
    rwa [hid] at h

end

end Algsuperdiff.Section4.Support
