/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryDatumTransport
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryPoincareWindow
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryWindowNormalized
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.L2Bridge

/-!
# BoundarySplit

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The boundary Caccioppoli's `L²` object, split

`BoundaryOuterAssembly.exists_boundaryWindowEnergy_le_dirichletDatumRHS` reads its
`L²` object on the covering cube, in that cube's own frame:

```text
  ‖u(·+c) − v‖²_{L²(□_{n+2})} ,   c = wellPlacedCentre x m (n+2) ,
```

where `v` is the Dirichlet solution on `□_{n+2}` carrying the **transported**
boundary datum `h(·+c)`.  The frozen right-hand side prices nothing of that
shape, so the object must be split against the two zero-trace data the boundary
lane actually holds:

```text
  u(·+c) − v  =  (u − h)(·+c)  −  (v − h(·+c)) ,
                 ↑ H¹₀(□_m)               ↑ H¹₀(□_{n+2}) by construction
```

* the **second** summand is an `H¹₀(□_{n+2})` datum, so the *Dirichlet* Poincaré
  applies at the cube's own scale.

The Dirichlet leg is proved here from the proved zero-set core rather than
imported from CoarseGraining: the zero extension of an `H¹₀(□_{n+2})` datum to
the enclosing cube `□_{n+3}` vanishes on the upper slab `{½·3^{n+2} ≤ yᵢ}`,
which the proved three-translate covering shows carries at least a third of
`□_{n+3}`.

**What this module does not do.**  It does not price the second leg's gradient:
the output keeps the honest coordinate sum `Σᵢ ‖∂ᵢσ‖`.

## References

* ABK26, `l.harmonic.approximation.good.scales`, Step 2;
  `l.coarse.grained.Caccioppoli.RHS`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport HCPolySupport.Book MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The origin cube as an axis cube -/

/-- An origin triadic cube is its own lower-corner axis cube. -/
theorem openCubeSet_originCube_eq_axisCube (j : ℤ) :
    openCubeSet (originCube d j) =
      axisCube (fun _ => -(1 / 2 : ℝ) * (3 : ℝ) ^ j) ((3 : ℝ) ^ j) := by
  ext y
  rw [mem_openCubeSet_originCube_iff, mem_axisCube_iff]
  constructor
  · intro h i
    obtain ⟨h1, h2⟩ := h i
    exact ⟨by linarith only [h1], by linarith only [h2]⟩
  · intro h i
    obtain ⟨h1, h2⟩ := h i
    exact ⟨by linarith only [h1], by linarith only [h2]⟩

/-- The origin cube sits inside its triadic parent, in the axis realization. -/
theorem openCubeSet_originCube_subset_axisCube_succ (j : ℤ) :
    openCubeSet (originCube d j) ⊆
      axisCube ((fun _ => -(1 / 2 : ℝ) * (3 : ℝ) ^ (j + 1) : Vec d))
        ((3 : ℝ) ^ (j + 1)) := by
  intro y hy
  rw [mem_openCubeSet_originCube_iff] at hy
  rw [mem_axisCube_iff]
  have hstep : (3 : ℝ) ^ (j + 1) = 3 * (3 : ℝ) ^ j := by
    rw [zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0)]
    ring
  have hpos : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) j
  intro i
  obtain ⟨h1, h2⟩ := hy i
  exact ⟨by linarith only [h1, hstep, hpos], by linarith only [h2, hstep, hpos]⟩

/-! ## 2. The upper slab of the parent cube -/

/-- **The parent's upper slab carries a third of the parent.**

The level `½·3^j` — the upper face of the *child* `□_j` — cuts the parent cube
`□_{j+1}` so that the part above it is at least a third of the parent.  Landed
`volume_le_three_mul_slab` at `lo = -½·3^{j+1}`, `hi = ½·3^{j+1}`, `a = ½·3^j`,
where `a − 2(hi − a) = lo` exactly. -/
theorem volume_axisCube_succ_le_three_mul_upperSlab (j : ℤ) (i : Fin d) :
    volume (axisCube ((fun _ => -(1 / 2 : ℝ) * (3 : ℝ) ^ (j + 1) : Vec d))
        ((3 : ℝ) ^ (j + 1))) ≤
      3 * volume ((axisCube ((fun _ => -(1 / 2 : ℝ) * (3 : ℝ) ^ (j + 1) : Vec d))
          ((3 : ℝ) ^ (j + 1))) ∩ {y | (1 / 2 : ℝ) * (3 : ℝ) ^ j ≤ y i}) := by
  have hstep : (3 : ℝ) ^ (j + 1) = 3 * (3 : ℝ) ^ j := by
    rw [zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0)]
    ring
  have hpos : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) j
  refine volume_le_three_mul_slab (g := fun y => y i) (e := basisVec i)
    (lo := -(1 / 2 : ℝ) * (3 : ℝ) ^ (j + 1))
    (hi := (1 / 2 : ℝ) * (3 : ℝ) ^ (j + 1)) ?_ ?_ ?_ ?_ ?_
  · intro y s
    simp [basisVec_apply]
  · intro y hy
    rw [mem_axisCube_iff] at hy
    obtain ⟨h1, h2⟩ := hy i
    exact ⟨by linarith only [h1], by linarith only [h2]⟩
  · intro y hy s hs1 hs2
    rw [mem_axisCube_iff] at hy ⊢
    intro k
    by_cases hk : k = i
    · subst hk
      have hcoord : (y + s • basisVec k) k = y k + s := by simp [basisVec_apply]
      rw [hcoord]
      exact ⟨by linarith only [hs1], by linarith only [hs2]⟩
    · have hcoord : (y + s • basisVec i) k = y k := by simp [basisVec_apply, hk]
      rw [hcoord]
      exact hy k
  · linarith only [hstep, hpos]
  · linarith only [hstep, hpos]

/-! ## 3. The Dirichlet Poincaré on an origin cube -/

/-- The coefficient-free constant of the Dirichlet Poincaré on an origin triadic
cube: `3(1 + √3)` times the `d`-only mean-zero constant of the unit corner
cube. -/
def dirichletCubePoincareConst (d : ℕ) : ℝ :=
  (1 + Real.sqrt 3) * (unitMeanZeroPoincareConst d * 3)

theorem dirichletCubePoincareConst_nonneg (d : ℕ) :
    0 ≤ dirichletCubePoincareConst d := by
  have h1 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have h2 : 0 ≤ unitMeanZeroPoincareConst d := unitMeanZeroPoincareConst_nonneg d
  exact mul_nonneg (by linarith only [h1]) (by linarith only [h2])

/-- **The Dirichlet Poincaré inequality on an origin triadic cube.**

An `H¹₀(□_j)` datum obeys the un-subtracted `L²` Poincaré inequality at the
cube's own scale, with a constant depending on `d` alone. -/
theorem eLpNorm_le_dirichletCubePoincare [NeZero d] (j : ℤ)
    (sigma : H10Function (openCubeSet (originCube d j))) :
    (eLpNorm sigma.toFun 2
        (volume.restrict (openCubeSet (originCube d j)))).toReal ≤
      dirichletCubePoincareConst d * (3 : ℝ) ^ j *
        ∑ i : Fin d,
          (eLpNorm (fun x => sigma.grad x i) 2
            (volume.restrict (openCubeSet (originCube d j)))).toReal := by
  classical
  obtain ⟨i⟩ : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩
  set A : Set (Vec d) :=
    axisCube ((fun _ => -(1 / 2 : ℝ) * (3 : ℝ) ^ (j + 1) : Vec d))
      ((3 : ℝ) ^ (j + 1)) with hA
  have hVmeas : MeasurableSet (openCubeSet (originCube d j)) :=
    (isOpen_openCubeSet (originCube d j)).measurableSet
  have hVA : (openCubeSet (originCube d j)) ⊆ A :=
    openCubeSet_originCube_subset_axisCube_succ j
  have hLpos : (0 : ℝ) < (3 : ℝ) ^ (j + 1) := zpow_pos (by norm_num) _
  have hEmeas : MeasurableSet (A ∩ {y | (1 / 2 : ℝ) * (3 : ℝ) ^ j ≤ y i}) :=
    (isOpen_axisCube _ _).measurableSet.inter
      (measurableSet_le measurable_const (measurable_pi_apply i))
  have hzeroE : ∀ y ∈ A ∩ {y | (1 / 2 : ℝ) * (3 : ℝ) ^ j ≤ y i},
      (zeroExtendH1 hVmeas sigma A).toFun y = 0 := by
    intro y hy
    refine zeroExtendH1_eq_zero_of_notMem hVmeas sigma _ ?_
    intro hmem
    rw [mem_openCubeSet_originCube_iff] at hmem
    obtain ⟨_, h2⟩ := hmem i
    have hy2 : (1 / 2 : ℝ) * (3 : ℝ) ^ j ≤ y i := hy.2
    linarith only [h2, hy2]
  have hvolE : volume A ≤
      ENNReal.ofReal 3 * volume (A ∩ {y | (1 / 2 : ℝ) * (3 : ℝ) ^ j ≤ y i}) := by
    have h3 : ENNReal.ofReal (3 : ℝ) = 3 := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, ENNReal.ofReal_natCast]
      norm_num
    rw [h3, hA]
    exact volume_axisCube_succ_le_three_mul_upperSlab j i
  have hcore := eLpNorm_le_of_zeroSet_of_volume_le
    (fun _ => -(1 / 2 : ℝ) * (3 : ℝ) ^ (j + 1)) hLpos (by norm_num : (0 : ℝ) ≤ 3)
    (zeroExtendH1 hVmeas sigma A) Set.inter_subset_left hEmeas hzeroE hvolE
  have hinter : A ∩ (openCubeSet (originCube d j)) = openCubeSet (originCube d j) :=
    Set.inter_eq_self_of_subset_right hVA
  have hvalue : eLpNorm (zeroExtendH1 hVmeas sigma A).toFun 2 (volumeMeasureOn A) =
      eLpNorm sigma.toFun 2 (volume.restrict (openCubeSet (originCube d j))) := by
    change eLpNorm (zeroExtend (openCubeSet (originCube d j)) sigma.toFun) 2
      (volume.restrict A) = _
    rw [eLpNorm_zeroExtend_eq hVmeas, hinter]
  have hgrads : ∀ k : Fin d,
      eLpNorm (fun x => (zeroExtendH1 hVmeas sigma A).grad x k) 2 (volumeMeasureOn A) =
        eLpNorm (fun x => sigma.grad x k) 2
          (volume.restrict (openCubeSet (originCube d j))) := by
    intro k
    change eLpNorm (fun x =>
      zeroExtendGrad (openCubeSet (originCube d j)) sigma.grad x k) 2
        (volume.restrict A) = _
    rw [eLpNorm_zeroExtendGrad_eq hVmeas, hinter]
  have hsumeq : (∑ i : Fin d,
      (eLpNorm (fun x => (zeroExtendH1 hVmeas sigma A).grad x i) 2
        (volumeMeasureOn A)).toReal) =
      ∑ i : Fin d, (eLpNorm (fun x => sigma.grad x i) 2
        (volume.restrict (openCubeSet (originCube d j)))).toReal :=
    Finset.sum_congr rfl fun i _ => by rw [hgrads i]
  rw [hvalue, hsumeq] at hcore
  have hconst : (1 + Real.sqrt 3) *
      (unitMeanZeroPoincareConst d * (3 : ℝ) ^ (j + 1)) =
      dirichletCubePoincareConst d * (3 : ℝ) ^ j := by
    rw [dirichletCubePoincareConst, zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0)]
    ring
  rw [← hconst]
  exact hcore

/-- **The Dirichlet Poincaré on an origin cube, volume-normalized.**

The normalization cancels exactly: the same cube carries both sides. -/
theorem eLpNorm_normalized_le_dirichletCubePoincare [NeZero d] (j : ℤ)
    (sigma : H10Function (openCubeSet (originCube d j))) :
    (eLpNorm sigma.toFun 2
        (Support.normalizedVolumeMeasureOn (openCubeSet (originCube d j)))).toReal ≤
      dirichletCubePoincareConst d * (3 : ℝ) ^ j *
        ∑ i : Fin d,
          (eLpNorm (fun x => sigma.grad x i) 2
            (Support.normalizedVolumeMeasureOn
              (openCubeSet (originCube d j)))).toReal := by
  classical
  have hbase := eLpNorm_le_dirichletCubePoincare j sigma
  simp only [eLpNorm_normalizedVolumeMeasureOn_eq, ENNReal.toReal_mul]
  have hr : (0 : ℝ) ≤
      (((volume (openCubeSet (originCube d j)))⁻¹) ^ (1 / 2 : ℝ)).toReal :=
    ENNReal.toReal_nonneg
  calc (((volume (openCubeSet (originCube d j)))⁻¹) ^ (1 / 2 : ℝ)).toReal *
        (eLpNorm sigma.toFun 2
          (volume.restrict (openCubeSet (originCube d j)))).toReal
      ≤ (((volume (openCubeSet (originCube d j)))⁻¹) ^ (1 / 2 : ℝ)).toReal *
          (dirichletCubePoincareConst d * (3 : ℝ) ^ j *
            ∑ i : Fin d,
              (eLpNorm (fun x => sigma.grad x i) 2
                (volume.restrict (openCubeSet (originCube d j)))).toReal) :=
        mul_le_mul_of_nonneg_left hbase hr
    _ = dirichletCubePoincareConst d * (3 : ℝ) ^ j *
          ∑ i : Fin d,
            (((volume (openCubeSet (originCube d j)))⁻¹) ^ (1 / 2 : ℝ)).toReal *
              (eLpNorm (fun x => sigma.grad x i) 2
                (volume.restrict (openCubeSet (originCube d j)))).toReal := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i _
        ring

end

end Algsuperdiff.Section4.Provider.ExcessDecay
