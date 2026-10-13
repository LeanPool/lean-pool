/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryWindowPoincare

/-!
# CubeSchauderPoincare

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Cube Schauder: the Dirichlet Poincaré on an inscribed window

```text
  ‖σ‖_{L²(W)} ≤ C(d) · 3^n · Σᵢ ‖∂ᵢσ‖_{L²(W)} ,   σ ∈ H¹₀(W) ,
```

for every window `W` inscribed in a translated triadic cube `c + □_n`.

`ExcessDecay.BoundarySplit.eLpNorm_le_dirichletCubePoincare` proves the
special case `W = □_n`, but that module's import cone reaches
`Algsuperdiff.Frozen`, which the Schauder cone must not.  The statement is
therefore re-proved here, from the two genuinely needed leaves
(`BoundaryPoincareCore`'s zero-set core and `BoundaryTraceMeasure`'s zero
extension and slab covering, both `Frozen`-free), and at the same time
**generalized off the cube**: the truncated windows `(x + □_n) ∩ □_m` of the
§4 lane are inscribed in `x + □_n` but are not cubes, and it is those windows the
composition needs.

The mechanism is unchanged: the zero extension of `σ` to the parent cube
`c + □_{n+1}` vanishes on the upper slab `{yᵢ ≥ cᵢ + ½·3^n}`, which carries at
least a third of the parent (three translates of the slab cover it), so the
zero-set Poincaré inequality applies at the parent's scale `3^{n+1}`.

## Main results

* `schauderDirichletPoincareConst` — the constant `3(1+√3)·C_meanzero(d)`.
* `eLpNorm_le_schauderDirichletPoincare` — the inequality above.

## References

* ABK26; `Algsuperdiff/Frozen/External/CubeSchauder.lean`.
-/

namespace Algsuperdiff.Section4.Provider.Schauder

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. The constant -/

/-- The coefficient-free constant of the inscribed-window Dirichlet Poincaré
inequality: `3(1 + √3)` times the `d`-only mean-zero constant of the unit
corner cube. -/
def schauderDirichletPoincareConst (d : ℕ) : ℝ :=
  (1 + Real.sqrt 3) * (unitMeanZeroPoincareConst d * 3)

theorem schauderDirichletPoincareConst_nonneg (d : ℕ) :
    0 ≤ schauderDirichletPoincareConst d := by
  have h1 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have h2 : 0 ≤ unitMeanZeroPoincareConst d := unitMeanZeroPoincareConst_nonneg d
  exact mul_nonneg (by linarith only [h1]) (by linarith only [h2])

/-! ## 2. The parent cube and its upper slab -/

/-- **The parent's upper slab carries a third of the parent.**

The level `cᵢ + ½·3^n` — the upper face of the inscribing cube `c + □_n` — cuts
the parent cube `c + □_{n+1}` so that the part above it is at least a third of
the parent.  This is `volume_le_three_mul_slab` at `lo = cᵢ - ½·3^{n+1}`,
`hi = cᵢ + ½·3^{n+1}`, `a = cᵢ + ½·3^n`, where `a - 2(hi - a) = lo` exactly. -/
theorem volume_parentCube_le_three_mul_upperSlab (c : Vec d) (n : ℤ) (i : Fin d) :
    volume (axisCube (fun j => c j - (1 / 2 : ℝ) * (3 : ℝ) ^ (n + 1)) ((3 : ℝ) ^ (n + 1))) ≤
      3 * volume ((axisCube (fun j => c j - (1 / 2 : ℝ) * (3 : ℝ) ^ (n + 1))
          ((3 : ℝ) ^ (n + 1))) ∩ {y | c i + (1 / 2 : ℝ) * (3 : ℝ) ^ n ≤ y i}) := by
  have hstep : (3 : ℝ) ^ (n + 1) = 3 * (3 : ℝ) ^ n := by
    rw [zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0)]
    ring
  have hpos : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
  refine volume_le_three_mul_slab (g := fun y => y i) (e := basisVec i)
    (lo := c i - (1 / 2 : ℝ) * (3 : ℝ) ^ (n + 1))
    (hi := c i + (1 / 2 : ℝ) * (3 : ℝ) ^ (n + 1)) ?_ ?_ ?_ ?_ ?_
  · intro y s
    simp [basisVec_apply]
  · intro y hy
    rw [mem_axisCube_iff] at hy
    obtain ⟨h1, h2⟩ := hy i
    exact ⟨by linarith only [h1], by linarith only [h2]⟩
  · intro y hy s hs1 hs2
    rw [mem_axisCube_iff] at hy ⊢
    intro j
    by_cases hj : j = i
    · subst hj
      have hcoord : (y + s • basisVec j) j = y j + s := by simp [basisVec_apply]
      rw [hcoord]
      exact ⟨by linarith only [hs1], by linarith only [hs2]⟩
    · have hcoord : (y + s • basisVec i) j = y j := by simp [basisVec_apply, hj]
      rw [hcoord]
      exact hy j
  · linarith only [hstep, hpos]
  · linarith only [hstep, hpos]

/-! ## 3. The Dirichlet Poincaré on an inscribed window -/

/-- **The Dirichlet Poincaré inequality on an inscribed window.**

An `H¹₀(W)` datum on a measurable window `W ⊆ c + □_n` obeys the *un-subtracted*
`L²` Poincaré inequality at the inscribing cube's scale `3^n`, with a constant
depending on `d` alone.

This is the converter of the §4.5 Campanato composition: the freezing step of
`CubeSchauderFreezing` delivers `Σᵢ ‖∂ᵢw‖_{L²}`, and the one-step contraction
consumes `‖u − v‖_{L²}`. -/
theorem eLpNorm_le_schauderDirichletPoincare [NeZero d] {W : Set (Vec d)}
    (hWmeas : MeasurableSet W) (c : Vec d) (n : ℤ)
    (hWsub : ∀ y ∈ W, ∀ j : Fin d,
      c j - (1 / 2 : ℝ) * (3 : ℝ) ^ n < y j ∧ y j < c j + (1 / 2 : ℝ) * (3 : ℝ) ^ n)
    (sigma : H10Function W) :
    (eLpNorm sigma.toFun 2 (volume.restrict W)).toReal ≤
      schauderDirichletPoincareConst d * (3 : ℝ) ^ n *
        ∑ i : Fin d,
          (eLpNorm (fun y => sigma.grad y i) 2 (volume.restrict W)).toReal := by
  classical
  obtain ⟨i⟩ : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩
  have hstep : (3 : ℝ) ^ (n + 1) = 3 * (3 : ℝ) ^ n := by
    rw [zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0)]
    ring
  have hpos : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
  have hLpos : (0 : ℝ) < (3 : ℝ) ^ (n + 1) := zpow_pos (by norm_num) _
  set z : Vec d := fun j => c j - (1 / 2 : ℝ) * (3 : ℝ) ^ (n + 1) with hzdef
  set A : Set (Vec d) := axisCube z ((3 : ℝ) ^ (n + 1)) with hA
  have hWA : W ⊆ A := by
    intro y hy
    rw [hA, mem_axisCube_iff]
    intro j
    obtain ⟨h1, h2⟩ := hWsub y hy j
    refine ⟨?_, ?_⟩
    · show c j - (1 / 2 : ℝ) * (3 : ℝ) ^ (n + 1) < y j
      linarith only [h1, hstep, hpos]
    · show y j < c j - (1 / 2 : ℝ) * (3 : ℝ) ^ (n + 1) + (3 : ℝ) ^ (n + 1)
      linarith only [h2, hstep, hpos]
  have hEmeas : MeasurableSet (A ∩ {y | c i + (1 / 2 : ℝ) * (3 : ℝ) ^ n ≤ y i}) :=
    (isOpen_axisCube _ _).measurableSet.inter
      (measurableSet_le measurable_const (measurable_pi_apply i))
  have hzeroE : ∀ y ∈ A ∩ {y | c i + (1 / 2 : ℝ) * (3 : ℝ) ^ n ≤ y i},
      (zeroExtendH1 hWmeas sigma A).toFun y = 0 := by
    intro y hy
    refine zeroExtendH1_eq_zero_of_notMem hWmeas sigma _ ?_
    intro hmem
    have h2 := (hWsub y hmem i).2
    have hy2 : c i + (1 / 2 : ℝ) * (3 : ℝ) ^ n ≤ y i := hy.2
    linarith only [h2, hy2]
  have hvolE : volume A ≤
      ENNReal.ofReal 3 * volume (A ∩ {y | c i + (1 / 2 : ℝ) * (3 : ℝ) ^ n ≤ y i}) := by
    have h3 : ENNReal.ofReal (3 : ℝ) = 3 := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, ENNReal.ofReal_natCast]
      norm_num
    rw [h3, hA]
    exact volume_parentCube_le_three_mul_upperSlab c n i
  have hcore := eLpNorm_le_of_zeroSet_of_volume_le z hLpos (by norm_num : (0 : ℝ) ≤ 3)
    (zeroExtendH1 hWmeas sigma A) Set.inter_subset_left hEmeas hzeroE hvolE
  have hinter : A ∩ W = W := Set.inter_eq_self_of_subset_right hWA
  have hvalue : eLpNorm (zeroExtendH1 hWmeas sigma A).toFun 2 (volumeMeasureOn A) =
      eLpNorm sigma.toFun 2 (volume.restrict W) := by
    show eLpNorm (zeroExtend W sigma.toFun) 2 (volume.restrict A) = _
    rw [eLpNorm_zeroExtend_eq hWmeas, hinter]
  have hgrads : ∀ j : Fin d,
      eLpNorm (fun y => (zeroExtendH1 hWmeas sigma A).grad y j) 2 (volumeMeasureOn A) =
        eLpNorm (fun y => sigma.grad y j) 2 (volume.restrict W) := by
    intro j
    show eLpNorm (fun y => zeroExtendGrad W sigma.grad y j) 2 (volume.restrict A) = _
    rw [eLpNorm_zeroExtendGrad_eq hWmeas, hinter]
  have hsumeq : (∑ j : Fin d,
      (eLpNorm (fun y => (zeroExtendH1 hWmeas sigma A).grad y j) 2
        (volumeMeasureOn A)).toReal) =
      ∑ j : Fin d, (eLpNorm (fun y => sigma.grad y j) 2 (volume.restrict W)).toReal :=
    Finset.sum_congr rfl fun j _ => by rw [hgrads j]
  rw [hvalue, hsumeq] at hcore
  have hconst : (1 + Real.sqrt 3) * (unitMeanZeroPoincareConst d * (3 : ℝ) ^ (n + 1)) =
      schauderDirichletPoincareConst d * (3 : ℝ) ^ n := by
    rw [schauderDirichletPoincareConst, hstep]
    ring
  rw [← hconst]
  exact hcore

end

end Algsuperdiff.Section4.Provider.Schauder
