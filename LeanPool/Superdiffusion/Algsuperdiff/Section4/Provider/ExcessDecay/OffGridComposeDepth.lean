/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OffGridStabilityGeometry
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OffGridStabilityArith

/-!
# OffGridComposeDepth

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The depth reindexing: the packing count into the geometric sum

The printed proof of `l.lambdas.stability` (ABK26) sums the per-cube cap
`3^{2s·depth}` against the packing count of the greedy family.  The two halves
are proved: the covering geometry gives, for each scale, the packing count

```
∑_{Q maximal, scale Q = k − n} |Q|  ≤  2d·3^{1−n}·|w + □_k| ,
```

and the exponent bookkeeping gives the geometric sum `∑_n W(n)·3^{2un} ≤
2C/(1−2u)` for `W(n) ≤ C·3^{−n}`.  What is missing is the **reindexing**: the
covering is one countable family of cubes of unboundedly many scales, while the
arithmetic is a series over the depth `n`.

This module supplies it, by fibering the maximal-cube family over
`maximalCubeDepth` (`Equiv.sigmaFiberEquiv`), identifying each fibre with
`maximalCubesAtScale` (`maximalCubesFiberEquiv`), and applying
`summable_sigma_of_nonneg` / `Summable.tsum_sigma`.  Summability is *not*
assumed: it is produced here, and it is exactly what the countable subadditivity
and the covering step need as their majorant obligation.  (The trivial
cardinality bound `3^{dn}` on the depth-`n` cubes would make the series diverge;
only the covering geometry's boundary-layer packing count `6d·3^{−n}` makes it
converge.  Summability is therefore genuine content, not bookkeeping.)

The volume sums are done in `ℝ≥0∞`, where the fibre volumes need no summability
side condition, and converted at the end
through `ENNReal.summable_toReal` and `ENNReal.tsum_toReal_eq`.

## Main results

* `maximalCubeDepth` — the depth of a maximal cube below the shape cube.
* `summable_and_tsum_maximalCubes_depth_le` — the reindexed geometric sum, with
  the explicit constant `12d/(1−2u)`.
* `summable_and_tsum_maximalCubes_cap_le` — the same with the constant factor
  the per-cube cap carries.

## References

* ABK26, `l.lambdas.stability`, (the double sum).
* Repo, `Provider/ExcessDecay/OffGridStabilityGeometry.lean`,
  `Provider/ExcessDecay/OffGridStabilityArith.lean`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport HCPolySupport.Book MeasureTheory

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## 1. The depth fibration of the maximal-cube family -/

omit [NeZero d] in
/-- The **depth** of a maximal grid cube of the off-grid cube `w + R` below the
shape cube `R`.  Well-defined as a natural number because every maximal cube has
scale at most `R.scale` (`scale_le_of_maximalCubeIn_offGridCube`). -/
def maximalCubeDepth (w : Vec d) (R : TriadicCube d)
    (Q : maximalCubes (offGridCube w R)) : ℕ :=
  (R.scale - (Q : TriadicCube d).scale).toNat

omit [NeZero d] in
/-- The depth-`n` fibre of the maximal-cube family is the scale-`(k − n)` part
of it.  Pure bookkeeping: the two subtypes have the same underlying cubes. -/
def maximalCubesFiberEquiv (w : Vec d) (R : TriadicCube d) (n : ℕ) :
    {Q : maximalCubes (offGridCube w R) // maximalCubeDepth w R Q = n} ≃
      maximalCubesAtScale (offGridCube w R) (R.scale - (n : ℤ)) where
  toFun x := ⟨((x.1 : maximalCubes (offGridCube w R)) : TriadicCube d), ⟨x.1.2, by
    have hle : ((x.1 : maximalCubes (offGridCube w R)) : TriadicCube d).scale ≤ R.scale :=
      scale_le_of_maximalCubeIn_offGridCube x.1.2
    have hx : (R.scale -
      ((x.1 : maximalCubes (offGridCube w R)) : TriadicCube d).scale).toNat = n := x.2
    omega⟩⟩
  invFun y := ⟨⟨((y : maximalCubesAtScale (offGridCube w R) (R.scale - (n : ℤ))) :
      TriadicCube d), y.2.1⟩, by
    have hy : ((y : maximalCubesAtScale (offGridCube w R) (R.scale - (n : ℤ))) :
      TriadicCube d).scale = R.scale - (n : ℤ) := y.2.2
    show (R.scale -
      ((y : maximalCubesAtScale (offGridCube w R) (R.scale - (n : ℤ))) :
        TriadicCube d).scale).toNat = n
    omega⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-! ## 2. The shell volumes -/

omit [NeZero d] in
/-- The total volume of the depth-`n` maximal cubes of `w + R`. -/
def shellVolume (w : Vec d) (R : TriadicCube d) (n : ℕ) : ℝ :=
  (∑' Q : maximalCubesAtScale (offGridCube w R) (R.scale - (n : ℤ)),
    volume (cubeSet (Q : TriadicCube d))).toReal

omit [NeZero d] in
private theorem shellVolume_nonneg (w : Vec d) (R : TriadicCube d) (n : ℕ) :
    0 ≤ shellVolume w R n :=
  ENNReal.toReal_nonneg

omit [NeZero d] in
private theorem tsum_volume_shell_ne_top (w : Vec d) (R : TriadicCube d) (n : ℕ) :
    (∑' Q : maximalCubesAtScale (offGridCube w R) (R.scale - (n : ℤ)),
      volume (cubeSet (Q : TriadicCube d))) ≠ ⊤ := by
  rw [← tsum_volume_maximalCubesAtScale]
  exact volume_iUnion_maximalCubesAtScale_ne_top w R (R.scale - (n : ℤ))

omit [NeZero d] in
private theorem summable_cubeVolume_shell (w : Vec d) (R : TriadicCube d) (n : ℕ) :
    Summable fun Q : maximalCubesAtScale (offGridCube w R) (R.scale - (n : ℤ)) =>
      cubeVolume (Q : TriadicCube d) := by
  refine (ENNReal.summable_toReal (tsum_volume_shell_ne_top w R n)).congr ?_
  intro Q
  exact volume_cubeSet_toReal _

omit [NeZero d] in
private theorem tsum_cubeVolume_shell (w : Vec d) (R : TriadicCube d) (n : ℕ) :
    (∑' Q : maximalCubesAtScale (offGridCube w R) (R.scale - (n : ℤ)),
      cubeVolume (Q : TriadicCube d)) = shellVolume w R n := by
  rw [shellVolume, ENNReal.tsum_toReal_eq (fun Q => (volume_cubeSet_lt_top _).ne)]
  exact tsum_congr fun Q => (volume_cubeSet_toReal _).symm

/-- **The packing count in the depth variable.**  `W(n) ≤ 6d·3^{−n}·|w+R|`, the
formalized `∑_{z ∈ 𝒢_n} |□_n|/|U| ≤^{n−k}` with `C = 6d`. -/
private theorem shellVolume_le (w : Vec d) (R : TriadicCube d) (n : ℕ) :
    shellVolume w R n ≤ 6 * (d : ℝ) * cubeVolume R * (3 : ℝ) ^ (-(n : ℝ)) := by
  have hpack := tsum_volume_maximalCubesAtScale_toReal_le w R (R.scale - (n : ℤ))
  have hexp : R.scale - (n : ℤ) + 1 - R.scale = 1 - (n : ℤ) := by ring
  rw [hexp] at hpack
  have hzpow : (3 : ℝ) ^ ((1 : ℤ) - (n : ℤ)) = 3 * (3 : ℝ) ^ (-(n : ℝ)) := by
    have h3 : (3 : ℝ) ≠ 0 := by norm_num
    have hcast : (((n : ℤ) : ℝ)) = (n : ℝ) := by push_cast; ring
    rw [zpow_sub₀ h3, zpow_one, ← Real.rpow_intCast (3 : ℝ) (n : ℤ), hcast,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), div_eq_mul_inv]
  rw [hzpow] at hpack
  rw [shellVolume]
  calc (∑' Q : maximalCubesAtScale (offGridCube w R) (R.scale - (n : ℤ)),
        volume (cubeSet (Q : TriadicCube d))).toReal
      ≤ 2 * (d : ℝ) * (3 * (3 : ℝ) ^ (-(n : ℝ))) * cubeVolume R := hpack
    _ = 6 * (d : ℝ) * cubeVolume R * (3 : ℝ) ^ (-(n : ℝ)) := by ring

/-! ## 3. The reindexed sum -/

/-- **The depth sum of the covering.**

Both the summability and the value of the multi-scale series over the maximal
cubes of an arbitrary real translate, at the explicit constant `12d/(1−2u)` of
the exponent bookkeeping's table. -/
theorem summable_and_tsum_maximalCubes_depth_le (w : Vec d) (R : TriadicCube d) {u : ℝ}
    (hu0 : 0 < u) (hu : u < 1 / 2) :
    (Summable fun Q : maximalCubes (offGridCube w R) =>
        cubeVolume (Q : TriadicCube d) *
          (3 : ℝ) ^ (2 * u * ((maximalCubeDepth w R Q : ℕ) : ℝ))) ∧
      (∑' Q : maximalCubes (offGridCube w R), cubeVolume (Q : TriadicCube d) *
          (3 : ℝ) ^ (2 * u * ((maximalCubeDepth w R Q : ℕ) : ℝ))) ≤
        12 * (d : ℝ) * cubeVolume R / (1 - 2 * u) := by
  classical
  set G : maximalCubes (offGridCube w R) → ℝ :=
    fun Q => cubeVolume (Q : TriadicCube d) *
      (3 : ℝ) ^ (2 * u * ((maximalCubeDepth w R Q : ℕ) : ℝ)) with hG
  have hCnn : (0 : ℝ) ≤ 6 * (d : ℝ) * cubeVolume R := by
    have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    have hv : (0 : ℝ) ≤ cubeVolume R := cubeVolume_nonneg R
    positivity
  obtain ⟨hWsum, hWle⟩ := tsum_depth_le (u := u) (C := 6 * (d : ℝ) * cubeVolume R) hu0 hu hCnn
    (shellVolume w R) (shellVolume_nonneg w R) (shellVolume_le w R)
  have hfib : ∀ n : ℕ,
      (Summable fun y : {Q : maximalCubes (offGridCube w R) // maximalCubeDepth w R Q = n} =>
          G (y : maximalCubes (offGridCube w R))) ∧
        (∑' y : {Q : maximalCubes (offGridCube w R) // maximalCubeDepth w R Q = n},
          G (y : maximalCubes (offGridCube w R))) =
            shellVolume w R n * (3 : ℝ) ^ (2 * u * (n : ℝ)) := by
    intro n
    have hval : ∀ y : {Q : maximalCubes (offGridCube w R) // maximalCubeDepth w R Q = n},
        G (y : maximalCubes (offGridCube w R)) =
          cubeVolume (((y : maximalCubes (offGridCube w R)) : TriadicCube d)) *
            (3 : ℝ) ^ (2 * u * (n : ℝ)) := by
      intro y
      have hy : maximalCubeDepth w R (y : maximalCubes (offGridCube w R)) = n := y.2
      simp only [hG, hy]
    have hbase : Summable fun z : maximalCubesAtScale (offGridCube w R) (R.scale - (n : ℤ)) =>
        cubeVolume (z : TriadicCube d) * (3 : ℝ) ^ (2 * u * (n : ℝ)) :=
      (summable_cubeVolume_shell w R n).mul_right _
    have htrans := ((maximalCubesFiberEquiv w R n).summable_iff
      (f := fun z : maximalCubesAtScale (offGridCube w R) (R.scale - (n : ℤ)) =>
        cubeVolume (z : TriadicCube d) * (3 : ℝ) ^ (2 * u * (n : ℝ)))).2 hbase
    refine ⟨htrans.congr fun y => (hval y).symm, ?_⟩
    calc (∑' y : {Q : maximalCubes (offGridCube w R) // maximalCubeDepth w R Q = n},
          G (y : maximalCubes (offGridCube w R)))
        = ∑' y : {Q : maximalCubes (offGridCube w R) // maximalCubeDepth w R Q = n},
            (fun z : maximalCubesAtScale (offGridCube w R) (R.scale - (n : ℤ)) =>
              cubeVolume (z : TriadicCube d) * (3 : ℝ) ^ (2 * u * (n : ℝ)))
                (maximalCubesFiberEquiv w R n y) := tsum_congr hval
      _ = ∑' z : maximalCubesAtScale (offGridCube w R) (R.scale - (n : ℤ)),
            cubeVolume (z : TriadicCube d) * (3 : ℝ) ^ (2 * u * (n : ℝ)) :=
          Equiv.tsum_eq (maximalCubesFiberEquiv w R n)
            (fun z : maximalCubesAtScale (offGridCube w R) (R.scale - (n : ℤ)) =>
              cubeVolume (z : TriadicCube d) * (3 : ℝ) ^ (2 * u * (n : ℝ)))
      _ = (∑' z : maximalCubesAtScale (offGridCube w R) (R.scale - (n : ℤ)),
            cubeVolume (z : TriadicCube d)) * (3 : ℝ) ^ (2 * u * (n : ℝ)) :=
          (summable_cubeVolume_shell w R n).tsum_mul_right _
      _ = shellVolume w R n * (3 : ℝ) ^ (2 * u * (n : ℝ)) := by
          rw [tsum_cubeVolume_shell]
  have hGnonneg : ∀ Q : maximalCubes (offGridCube w R), 0 ≤ G Q := by
    intro Q
    rw [hG]
    exact mul_nonneg (cubeVolume_nonneg _) (Real.rpow_nonneg (by norm_num) _)
  have hsigma : Summable
      fun p : Σ n : ℕ, {Q : maximalCubes (offGridCube w R) // maximalCubeDepth w R Q = n} =>
        G ((p.2 : maximalCubes (offGridCube w R))) := by
    refine (summable_sigma_of_nonneg (fun p => hGnonneg _)).2 ⟨fun n => (hfib n).1, ?_⟩
    exact hWsum.congr fun n => ((hfib n).2).symm
  have hsum : Summable G :=
    ((Equiv.sigmaFiberEquiv (maximalCubeDepth w R)).summable_iff (f := G)).1 hsigma
  refine ⟨hsum, ?_⟩
  have hval : (∑' Q : maximalCubes (offGridCube w R), G Q) =
      ∑' n : ℕ, shellVolume w R n * (3 : ℝ) ^ (2 * u * (n : ℝ)) := by
    have h1 : (∑' Q : maximalCubes (offGridCube w R), G Q) =
        ∑' p : Σ n : ℕ, {Q : maximalCubes (offGridCube w R) // maximalCubeDepth w R Q = n},
          G ((p.2 : maximalCubes (offGridCube w R))) :=
      (Equiv.tsum_eq (Equiv.sigmaFiberEquiv (maximalCubeDepth w R)) G).symm
    rw [h1, hsigma.tsum_sigma]
    exact tsum_congr fun n => (hfib n).2
  rw [hval]
  have hnum : 2 * (6 * (d : ℝ) * cubeVolume R) = 12 * (d : ℝ) * cubeVolume R := by ring
  rw [hnum] at hWle
  exact hWle

/-- The depth sum with the constant factor the per-cube cap carries. -/
theorem summable_and_tsum_maximalCubes_cap_le (w : Vec d) (R : TriadicCube d) {u c : ℝ}
    (hu0 : 0 < u) (hu : u < 1 / 2) (hc : 0 ≤ c) :
    (Summable fun Q : maximalCubes (offGridCube w R) =>
        cubeVolume (Q : TriadicCube d) *
          (c * (3 : ℝ) ^ (2 * u * ((maximalCubeDepth w R Q : ℕ) : ℝ)))) ∧
      (∑' Q : maximalCubes (offGridCube w R), cubeVolume (Q : TriadicCube d) *
          (c * (3 : ℝ) ^ (2 * u * ((maximalCubeDepth w R Q : ℕ) : ℝ)))) ≤
        c * (12 * (d : ℝ) * cubeVolume R / (1 - 2 * u)) := by
  obtain ⟨hsum, hle⟩ := summable_and_tsum_maximalCubes_depth_le w R hu0 hu
  have hcongr : ∀ Q : maximalCubes (offGridCube w R),
      c * (cubeVolume (Q : TriadicCube d) *
        (3 : ℝ) ^ (2 * u * ((maximalCubeDepth w R Q : ℕ) : ℝ))) =
      cubeVolume (Q : TriadicCube d) *
        (c * (3 : ℝ) ^ (2 * u * ((maximalCubeDepth w R Q : ℕ) : ℝ))) := by
    intro Q
    ring
  refine ⟨(hsum.mul_left c).congr hcongr, ?_⟩
  rw [← tsum_congr hcongr, hsum.tsum_mul_left]
  exact mul_le_mul_of_nonneg_left hle hc

end

end Algsuperdiff.Section4.Provider.ExcessDecay
