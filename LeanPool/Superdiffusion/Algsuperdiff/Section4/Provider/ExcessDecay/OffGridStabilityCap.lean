/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OffGridStabilityGrid
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.StabilityIndexCube

/-!
# OffGridStabilityCap

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The per-cube cap the covering consumes

The printed proof of `l.lambdas.stability` (ABK26) feeds the greedy covering
with `e.bound.one.cube.by.lambdas`: *every* grid cube inside the big cube has
its one-cube quantity bounded by `3^{2s·depth}` times the multiscale quantity
of the big cube.

This module proves the `𝓔_{·,∞,2}` form of that input:

```
max_{|e|=1} 𝐉(Q, …)  ≤  3^{2u·(P.scale − Q.scale)} · 𝓔_{u,∞,2}(P; a, a₀)²
```

for **any** grid cube `Q` whose half-open realization is contained in `P`'s —
no descendant hypothesis is assumed, it is *derived* — and the recognition
lemma that supplies it.

Two ingredients, both from already-proved material:

* `mem_descendantsAtScale_of_cubeSet_subset` (new here) — containment of
  half-open realizations plus a scale inequality already *forces* descendancy.
  This is what turns the covering geometry's maximal cubes, which are only known
  to sit inside a *real translate* of a cube, into descendants of the enclosing
  grid cube once the printed containment `x + □_n ⊆ z + □_{n+2}` is supplied.
* `normalizedBlockResponseMax_le_homogenizationErrorOnCube_sq` (new here) — the
  `q = 2` sibling of CoarseGraining's
  `Ch02.scaleResponseAtScale_infinity_self_le_homogenizationErrorOnCube_infinity_one`,
  proved by the same route through
  `Homogenization.self_le_tsum_geometricWeight_of_monotone`; there is **no**
  normalization constant, because the shell sequence is monotone and the
  weights sum to `1`.  That last point matters: the naive route through the
  single weight `c_{2u}3^{-2uj}` would cost a spurious `(1 - 3^{-2u})^{-1} ≍
  u^{-1}`, i.e. an `s`-power, and the printed `e.bound.one.cube.by.lambdas` —
  which carries no such factor — is therefore correct as printed.

## Main results

* `mem_descendantsAtScale_of_cubeSet_subset` — containment forces descendancy.
* `normalizedBlockResponseMax_le_homogenizationErrorOnCube_sq` — the one-cube
  bound at zero depth, constant `1`.
* `normalizedBlockResponseMax_le_rpow_mul_homogenizationErrorOnCube_sq` — the
  displayed per-cube cap.

## References

* ABK26, `e.bound.one.cube.by.lambdas`.
* ABK26, `l.lambdas.stability`.
* CoarseGraining,
  `Homogenization/Deterministic/MultiscaleQuantitiesBasic/Foundation/Geometric.lean`
  (`self_le_tsum_geometricWeight_of_monotone`),
  `Homogenization/Book/Ch02/Theorems/HomogenizationError/ResponseBounds.lean`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02

noncomputable section

variable {d : ℕ}

/-! ## 1. Containment forces descendancy -/

/-- The centre of a triadic cube lies in its half-open realization. -/
theorem cubeCenter_mem_cubeSet (Q : TriadicCube d) : cubeCenter Q ∈ cubeSet Q := by
  intro i
  have hs : (0 : ℝ) < cubeScaleFactor Q := cubeScaleFactor_pos' Q
  have hc : cubeCenter Q i = (Q.index i : ℝ) * cubeScaleFactor Q := rfl
  rw [hc]
  constructor <;> nlinarith only [hs]

/-- **Containment forces descendancy.**

If the half-open realization of `Q` sits inside that of `P` and `Q` is not
coarser, then `Q` is a triadic descendant of `P`.  No common-root hypothesis is
needed: the address map of `OffGridStabilityGrid.lean` recovers it. -/
theorem mem_descendantsAtScale_of_cubeSet_subset {P Q : TriadicCube d}
    (hsub : cubeSet Q ⊆ cubeSet P) (hscale : Q.scale ≤ P.scale) :
    Q ∈ descendantsAtScale P Q.scale := by
  classical
  have hx : cubeCenter Q ∈ cubeSet Q := cubeCenter_mem_cubeSet Q
  have hxP : cubeCenter Q ∈ cubeSet P := hsub hx
  rw [descendantsAtScale_eq_descendantsAtDepth P hscale]
  obtain ⟨R, hR, hxR⟩ :=
    exists_mem_descendantsAtDepth_of_mem_cubeSet (Q := P) (x := cubeCenter Q)
      (Int.toNat (P.scale - Q.scale)) hxP
  have hRscale : R.scale = P.scale - (Int.toNat (P.scale - Q.scale) : ℤ) :=
    scale_eq_sub_of_mem_descendantsAtDepth hR
  have htoNat : ((Int.toNat (P.scale - Q.scale) : ℤ)) = P.scale - Q.scale :=
    Int.toNat_of_nonneg (sub_nonneg.2 hscale)
  have hRQ : R.scale = Q.scale := by
    rw [hRscale, htoNat]
    ring
  have hQR : Q = R := eq_of_scale_eq_of_mem_of_mem hRQ.symm hx hxR
  rw [hQR, hRQ]
  exact hR

/-! ## 2. The one-cube bound at zero depth -/

variable [NeZero d]

/-- Duplicate of `StabilityIndexCube`'s `private shell_nonneg`. -/
private theorem shell_nonneg' (Q : TriadicCube d) (a : TriadicCoeffFamily d) (a0 : Mat d)
    (l : ℕ) :
    0 ≤ maxDescendantNormalizedBlockResponseAtScale Q (Q.scale - (l : ℤ)) a a0 :=
  maxDescendantNormalizedBlockResponseAtScale_nonneg Q
    (sub_le_self _ (Int.natCast_nonneg l)) a a0

/-- Duplicate of `StabilityIndexCube`'s `private shell_monotone`. -/
private theorem shell_monotone' (Q : TriadicCube d) (a : TriadicCoeffFamily d) (a0 : Mat d) :
    Monotone fun l : ℕ =>
      maxDescendantNormalizedBlockResponseAtScale Q (Q.scale - (l : ℤ)) a a0 := by
  intro m n hmn
  have hmnz : (m : ℤ) ≤ (n : ℤ) := by exact_mod_cast hmn
  exact maxDescendantNormalizedBlockResponseAtScale_le_of_le Q
    (by linarith only [hmnz] : Q.scale - (n : ℤ) ≤ Q.scale - (m : ℤ))
    (sub_le_self _ (Int.natCast_nonneg m)) a a0

/-- Duplicate of `StabilityIndexCube`'s `private summable_shell`. -/
private theorem summable_shell' (Q : TriadicCube d) (a : TriadicCoeffFamily d) (a0 : Mat d)
    {s : ℝ} (hs : 0 < s) :
    Summable fun l : ℕ =>
      HCPolySupport.geometricWeight s 2 l *
        maxDescendantNormalizedBlockResponseAtScale Q (Q.scale - (l : ℤ)) a a0 :=
  HCPolySupport.summable_geometricWeight_mul_of_nonneg_of_le
    (s := s) (q := 2) (C := normalizedBlockResponseUniformBound Q a a0)
    (by linarith only [hs]) (fun l => shell_nonneg' Q a a0 l)
    (fun l => maxDescendantNormalizedBlockResponseAtScale_le_uniform Q
      (sub_le_self _ (Int.natCast_nonneg l)) a a0)

/-- Duplicate of `StabilityIndexCube`'s `private rpow_three_sq`. -/
private theorem rpow_three_sq' (y : ℝ) :
    Real.rpow (3 : ℝ) y ^ 2 = Real.rpow (3 : ℝ) (y * 2) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hadd : Real.rpow (3 : ℝ) (y + y) = Real.rpow (3 : ℝ) y * Real.rpow (3 : ℝ) y := by
    exact Real.rpow_add h3 y y
  have hy : y * 2 = y + y := by ring
  rw [hy, hadd]
  ring

/-- **The one-cube bound at zero depth, with constant `1`.**

```
max_{|e|=1} 𝐉(Q, …)  ≤  𝓔_{u,∞,2}(Q; a, a₀)² .
```

There is no `(1 - 3^{-2u})^{-1}`: the shell sequence is nondecreasing and the
geometric weights sum to `1`, so the *whole* weighted average dominates the
zeroth shell.  This is why `e.bound.one.cube.by.lambdas` is correct as printed
and no `s`-power is lost at this step. -/
theorem normalizedBlockResponseMax_le_homogenizationErrorOnCube_sq (Q : TriadicCube d)
    (a : TriadicCoeffFamily d) (a0 : Mat d) {u : ℝ} (hu : 0 < u) :
    normalizedBlockResponseMax Q a a0 ≤
      HomogenizationErrorOnCube Q u .infinity (.finite 2) a a0 ^ 2 := by
  have hself : normalizedBlockResponseMax Q a a0 ≤
      maxDescendantNormalizedBlockResponseAtScale Q Q.scale a a0 :=
    normalizedBlockResponseMax_le_maxDescendantNormalizedBlockResponseAtScale_of_le Q
      (le_refl Q.scale) a a0
  have hkey : maxDescendantNormalizedBlockResponseAtScale Q Q.scale a a0 ≤
      ∑' l : ℕ, HCPolySupport.geometricWeight u 2 l *
        maxDescendantNormalizedBlockResponseAtScale Q (Q.scale - (l : ℤ)) a a0 := by
    have h := HCPolySupport.self_le_tsum_geometricWeight_of_monotone
      (H := fun l : ℕ => maxDescendantNormalizedBlockResponseAtScale Q (Q.scale - (l : ℤ)) a a0)
      (shell_monotone' Q a a0) (s := u) (q := 2) (by linarith only [hu])
      (summable_shell' Q a a0 hu)
    simpa only [Nat.cast_zero, sub_zero] using h
  rw [homogenizationErrorOnCube_infinity_two_sq_eq_tsum Q hu a a0]
  simp only [Ch02.geometricWeight_eq_old]
  exact le_trans hself hkey

/-! ## 3. The per-cube cap -/

/-- **The per-cube cap of the printed covering argument.**

For every grid cube `Q` contained in `P`,

```
max_{|e|=1} 𝐉(Q, …)  ≤  3^{2u·(P.scale − Q.scale)} · 𝓔_{u,∞,2}(P; a, a₀)² .
```

This is `e.bound.one.cube.by.lambdas` in the `𝓔_{·,∞,2}` normalization, and it
is what the countable subadditivity's majorant `B` is instantiated with. -/
theorem normalizedBlockResponseMax_le_rpow_mul_homogenizationErrorOnCube_sq
    {P Q : TriadicCube d} (a : TriadicCoeffFamily d) (a0 : Mat d) {u : ℝ} (hu : 0 < u)
    (hsub : cubeSet Q ⊆ cubeSet P) (hscale : Q.scale ≤ P.scale) :
    normalizedBlockResponseMax Q a a0 ≤
      Real.rpow (3 : ℝ) (u * (Int.toNat (P.scale - Q.scale) : ℝ) * 2) *
        HomogenizationErrorOnCube P u .infinity (.finite 2) a a0 ^ 2 := by
  have hQdesc : Q ∈ descendantsAtScale P Q.scale :=
    mem_descendantsAtScale_of_cubeSet_subset hsub hscale
  have hdescent := homogenizationErrorOnCube_infinity_two_le_of_mem_descendantsAtScale
    (Q := P) (R := Q) (k := Q.scale) a a0 hu hQdesc
  have hQnonneg : 0 ≤ HomogenizationErrorOnCube Q u .infinity (.finite 2) a a0 :=
    homogenizationErrorOnCube_infinity_two_nonneg Q a a0 hu
  have hsq : HomogenizationErrorOnCube Q u .infinity (.finite 2) a a0 ^ 2 ≤
      (Real.rpow (3 : ℝ) (u * (Int.toNat (P.scale - Q.scale) : ℝ)) *
        HomogenizationErrorOnCube P u .infinity (.finite 2) a a0) ^ 2 :=
    pow_le_pow_left₀ hQnonneg hdescent 2
  have hexpand : (Real.rpow (3 : ℝ) (u * (Int.toNat (P.scale - Q.scale) : ℝ)) *
      HomogenizationErrorOnCube P u .infinity (.finite 2) a a0) ^ 2 =
      Real.rpow (3 : ℝ) (u * (Int.toNat (P.scale - Q.scale) : ℝ) * 2) *
        HomogenizationErrorOnCube P u .infinity (.finite 2) a a0 ^ 2 := by
    rw [mul_pow, rpow_three_sq']
  calc normalizedBlockResponseMax Q a a0
      ≤ HomogenizationErrorOnCube Q u .infinity (.finite 2) a a0 ^ 2 :=
        normalizedBlockResponseMax_le_homogenizationErrorOnCube_sq Q a a0 hu
    _ ≤ (Real.rpow (3 : ℝ) (u * (Int.toNat (P.scale - Q.scale) : ℝ)) *
          HomogenizationErrorOnCube P u .infinity (.finite 2) a a0) ^ 2 := hsq
    _ = Real.rpow (3 : ℝ) (u * (Int.toNat (P.scale - Q.scale) : ℝ) * 2) *
          HomogenizationErrorOnCube P u .infinity (.finite 2) a a0 ^ 2 := hexpand

end

end Algsuperdiff.Section4.Provider.ExcessDecay
