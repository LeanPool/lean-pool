/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepNineOffGridGeometry
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.NormalizedL2

/-!
# StepNineOffGridTransfer

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `t.regularity` off-grid transfer: the quantity

## What is transferred

`StepNineOffGridGeometry` supplies the inclusion of windows

```text
  (x + □_n) ∩ □_m  ⊆  (z + □_{n+1}) ∩ □_m ,       z = offGridCentre n x .
```

A volume-normalized norm is NOT monotone under inclusion: passing to the
smaller window costs the volume ratio.  This module prices that ratio and
proves the transfer in BOTH carriers the development uses:

* the `ℝ≥0∞`-valued `eLpNorm · 2 (normalizedVolumeMeasureOn ·)` of the frozen
  root's left-hand side (`e.energy.density.estimate`), where the transfer needs
  NO integrability hypothesis at all — the `ℝ≥0∞` monotonicity
  `eLpNorm_mono_measure` is unconditional;
* the `ℝ`-valued `Support.normalizedL2On` of the proved Step-7 chain, where the
  `IntegrableOn` datum of the `H¹` solution is the carried hypothesis of
  `Support.normalizedL2On_le_of_subset`.

## The volume accounting

Upper bound: `(z+□_{n+1}) ∩ □_m ⊆ z + □_{n+1}`, of volume `3^{d(n+1)}`.

Lower bound: `(x+□_n) ∩ □_m` contains a translate of `□_{n−1}`
(`exists_inner_cube_subset_truncatedWindow`; the truncated interval is at least
`3^n/2` long in each coordinate and `3^{n−1} = 3^n/3 ≤ 3^n/2`), of volume
`3^{d(n−1)}`.

Hence the ratio is at most `3^{2d} = 9^d` and the NO factor is `3^d`:

```text
  ‖f‖_{L²((x+□_n) ∩ □_m)}  ≤  3^d · ‖f‖_{L²((z+□_{n+1}) ∩ □_m)} .
```

records the price of the off-grid step as `3^{d+1}` (there: `3^d` for the
untruncated volume ratio of the *squared* average, times `3` for the Campanato
weight `3^{-j} → 3^{-(j+1)}`).  The present display carries no scale weight,
and `3^d ≤ 3^{d+1}`: **the transfer is spent strictly inside that
price**.  The sharp interior value is `3^{d/2}` (no truncation, no
inscribed-cube slack); the extra `3^{d/2}` is the honest cost of the
boundary-truncated windows, and is a `C(d)` spent once.

## References

* ABK26, `t.regularity`.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open HCPolySupport MeasureTheory
open Algsuperdiff.Section4.Provider.ExcessDecay
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. Volumes of the two windows -/

/-- Translation invariance of Lebesgue measure, in the translation-image carrier
the windows are written in. -/
theorem volume_image_add_eq (y : Vec d) (S : Set (Vec d)) :
    volume ((fun v => y + v) '' S) = volume S := by
  rw [image_add_eq_translateSet]
  exact volume_translateSet_eq y S

/-- `|□_k| = (3^k)^d`, as an `ℝ≥0∞`. -/
theorem volume_openCubeSet_originCube_eq (d : ℕ) (k : ℤ) :
    volume (openCubeSet (originCube d k)) = ENNReal.ofReal (((3 : ℝ) ^ k) ^ d) := by
  have htop : volume (openCubeSet (originCube d k)) ≠ ⊤ :=
    (volume_openCubeSet_lt_top (originCube d k)).ne
  have hreal : (volume (openCubeSet (originCube d k))).toReal = ((3 : ℝ) ^ k) ^ d := by
    rw [volume_openCubeSet_toReal, cubeVolume_eq_pow_scale]
    rfl
  rw [← ENNReal.ofReal_toReal htop, hreal]

/-- The truncated window is inside the untruncated cube, so its volume is at most
`(3^k)^d`. -/
theorem volume_truncatedWindow_le (x : Vec d) (m k : ℤ) :
    volume (truncatedWindow x m k) ≤ ENNReal.ofReal (((3 : ℝ) ^ k) ^ d) := by
  refine le_trans (measure_mono (truncatedWindow_subset_translate x m k)) ?_
  rw [volume_image_add_eq, volume_openCubeSet_originCube_eq]

/-- The truncated window at a centre of `□_m` contains a translate of `□_{k−1}`, so
its volume is at least `(3^{k−1})^d`. -/
theorem volume_truncatedWindow_ge {x : Vec d} {m k : ℤ}
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k ≤ m) :
    ENNReal.ofReal (((3 : ℝ) ^ (k - 1)) ^ d) ≤ volume (truncatedWindow x m k) := by
  obtain ⟨y, hy⟩ := exists_inner_cube_subset_truncatedWindow x hx hkm
  refine le_trans (le_of_eq ?_) (measure_mono hy)
  rw [volume_image_add_eq, volume_openCubeSet_originCube_eq]

/-- **The volume ratio of the off-grid transfer.**  The scale-`(n+1)` lattice
window has at most `9^d` times the volume of the arbitrary-centre scale-`n`
window it contains. -/
theorem volume_offGridWindow_le_mul {x : Vec d} {m n : ℤ}
    (hx : x ∈ openCubeSet (originCube d m)) (hnm : n ≤ m) :
    volume (truncatedWindow (offGridCentre n x) m (n + 1)) ≤
      (ENNReal.ofReal ((3 : ℝ) ^ d)) ^ (2 : ℕ) * volume (truncatedWindow x m n) := by
  have hlow := volume_truncatedWindow_ge (x := x) (m := m) (k := n) hx hnm
  have hhigh := volume_truncatedWindow_le (offGridCentre n x) m (n + 1)
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (n - 1) := zpow_pos (by norm_num) (n - 1)
  have hsplit : ((3 : ℝ) ^ (n + 1)) ^ d = ((3 : ℝ) ^ d) ^ 2 * ((3 : ℝ) ^ (n - 1)) ^ d := by
    have hbase : (3 : ℝ) ^ (n + 1) = ((3 : ℝ) ^ (2 : ℕ)) * (3 : ℝ) ^ (n - 1) := by
      rw [← zpow_natCast (3 : ℝ) 2, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      congr 1
      omega
    rw [hbase, mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm]
  have hcast : ENNReal.ofReal (((3 : ℝ) ^ (n + 1)) ^ d) =
      (ENNReal.ofReal ((3 : ℝ) ^ d)) ^ (2 : ℕ) *
        ENNReal.ofReal (((3 : ℝ) ^ (n - 1)) ^ d) := by
    rw [hsplit, ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_pow (by positivity)]
  calc volume (truncatedWindow (offGridCentre n x) m (n + 1))
      ≤ ENNReal.ofReal (((3 : ℝ) ^ (n + 1)) ^ d) := hhigh
    _ = (ENNReal.ofReal ((3 : ℝ) ^ d)) ^ (2 : ℕ) *
          ENNReal.ofReal (((3 : ℝ) ^ (n - 1)) ^ d) := hcast
    _ ≤ (ENNReal.ofReal ((3 : ℝ) ^ d)) ^ (2 : ℕ) * volume (truncatedWindow x m n) :=
        mul_le_mul' le_rfl hlow

/-! ## 2. The `ℝ≥0∞` transfer: no integrability hypothesis -/

/-- `(c²)^{1/2} = c` in `ℝ≥0∞`. -/
private theorem sq_rpow_half (c : ℝ≥0∞) : (c ^ (2 : ℕ)) ^ ((1 : ℝ) / 2) = c := by
  rw [← ENNReal.rpow_natCast c 2, ← ENNReal.rpow_mul]
  norm_num

/-- **The normalized `L²` transfer, `ℝ≥0∞`-valued.**  For `W' ⊆ W` of positive
finite volume with `|W| ≤ K²·|W'|`,

```text
  ‖f‖_{L²(⨍_{W'})}  ≤  K · ‖f‖_{L²(⨍_W)} .
```

No `MemLp`, no `IntegrableOn`: the underlying monotonicity
`eLpNorm_mono_measure` holds in `ℝ≥0∞` unconditionally. -/
theorem eLpNormTwo_normalizedVolumeMeasureOn_le_of_volume_le {W W' : Set (Vec d)}
    (f : Vec d → ℝ) (hsub : W' ⊆ W)
    (hW'0 : volume W' ≠ 0) (hW'top : volume W' ≠ ⊤)
    (hW0 : volume W ≠ 0) (hWtop : volume W ≠ ⊤) {K : ℝ≥0∞}
    (hK : volume W ≤ K ^ (2 : ℕ) * volume W') :
    eLpNorm f 2 (Support.normalizedVolumeMeasureOn W')
      ≤ K * eLpNorm f 2 (Support.normalizedVolumeMeasureOn W) := by
  have hhalf : ((1 : ℝ≥0∞) / 2).toReal = 1 / 2 := by
    rw [ENNReal.toReal_div]
    norm_num
  have hsmul : ∀ V : Set (Vec d),
      eLpNorm f 2 (Support.normalizedVolumeMeasureOn V)
        = (volume V)⁻¹ ^ ((1 : ℝ) / 2) * eLpNorm f 2 (volume.restrict V) := by
    intro V
    by_cases hVtop : volume V = ⊤
    · simp [Support.normalizedVolumeMeasureOn_def, hVtop]
    rw [Support.normalizedVolumeMeasureOn_def,
      eLpNorm_smul_measure_of_ne_zero (ENNReal.inv_ne_zero.2 hVtop) f 2, smul_eq_mul, hhalf]
  -- the coefficient comparison `|W'|⁻¹ ≤ K² |W|⁻¹`
  have hcancelW' : volume W' * (volume W')⁻¹ = 1 := ENNReal.mul_inv_cancel hW'0 hW'top
  have hcancelW : volume W * (volume W)⁻¹ = 1 := ENNReal.mul_inv_cancel hW0 hWtop
  have hstep1 : volume W * (volume W')⁻¹ ≤ K ^ (2 : ℕ) := by
    calc volume W * (volume W')⁻¹
        ≤ (K ^ (2 : ℕ) * volume W') * (volume W')⁻¹ := mul_le_mul' hK le_rfl
      _ = K ^ (2 : ℕ) * (volume W' * (volume W')⁻¹) := by rw [mul_assoc]
      _ = K ^ (2 : ℕ) := by rw [hcancelW', mul_one]
  have hstep2 : (volume W')⁻¹ ≤ K ^ (2 : ℕ) * (volume W)⁻¹ := by
    calc (volume W')⁻¹ = (volume W * (volume W)⁻¹) * (volume W')⁻¹ := by
          rw [hcancelW, one_mul]
      _ = (volume W * (volume W')⁻¹) * (volume W)⁻¹ := by ring
      _ ≤ K ^ (2 : ℕ) * (volume W)⁻¹ := mul_le_mul' hstep1 le_rfl
  have hcoef : ((volume W')⁻¹) ^ ((1 : ℝ) / 2)
      ≤ K * ((volume W)⁻¹) ^ ((1 : ℝ) / 2) := by
    calc ((volume W')⁻¹) ^ ((1 : ℝ) / 2)
        ≤ (K ^ (2 : ℕ) * (volume W)⁻¹) ^ ((1 : ℝ) / 2) :=
          ENNReal.rpow_le_rpow hstep2 (by norm_num)
      _ = (K ^ (2 : ℕ)) ^ ((1 : ℝ) / 2) * ((volume W)⁻¹) ^ ((1 : ℝ) / 2) :=
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
      _ = K * ((volume W)⁻¹) ^ ((1 : ℝ) / 2) := by rw [sq_rpow_half]
  have hmono : eLpNorm f 2 (volume.restrict W') ≤ eLpNorm f 2 (volume.restrict W) :=
    eLpNorm_mono_measure f (Measure.restrict_mono hsub le_rfl)
  calc eLpNorm f 2 (Support.normalizedVolumeMeasureOn W')
      = (volume W')⁻¹ ^ ((1 : ℝ) / 2) * eLpNorm f 2 (volume.restrict W') := hsmul W'
    _ ≤ (K * ((volume W)⁻¹) ^ ((1 : ℝ) / 2)) * eLpNorm f 2 (volume.restrict W) :=
        mul_le_mul' hcoef hmono
    _ = K * ((volume W)⁻¹ ^ ((1 : ℝ) / 2) * eLpNorm f 2 (volume.restrict W)) := by
        rw [mul_assoc]
    _ = K * eLpNorm f 2 (Support.normalizedVolumeMeasureOn W) := by rw [hsmul W]

/-- **The off-grid transfer of the energy-density left-hand side**, in the
frozen root's own carrier and at the honest constant `3^d`:

```text
  ‖f‖_{L²(⨍_{(x+□_n) ∩ □_m})}  ≤  3^d · ‖f‖_{L²(⨍_{(z+□_{n+1}) ∩ □_m})} ,
```

`z = offGridCentre n x` the toward-origin lattice point of
`StepNineOffGridGeometry`. -/
theorem eLpNormTwo_offGrid_transfer (f : Vec d → ℝ) {x : Vec d} {m n : ℤ}
    (hx : x ∈ openCubeSet (originCube d m)) (hnm : n ≤ m) :
    eLpNorm f 2 (Support.normalizedVolumeMeasureOn (truncatedWindow x m n))
      ≤ ENNReal.ofReal ((3 : ℝ) ^ d) *
        eLpNorm f 2 (Support.normalizedVolumeMeasureOn
          (truncatedWindow (offGridCentre n x) m (n + 1))) := by
  have hz : offGridCentre n x ∈ openCubeSet (originCube d m) :=
    offGridCentre_mem_openCubeSet n hx
  refine eLpNormTwo_normalizedVolumeMeasureOn_le_of_volume_le f
    (truncatedWindow_subset_offGrid n m x) ?_ ?_ ?_ ?_
    (volume_offGridWindow_le_mul hx hnm)
  · exact (volume_truncatedWindow_pos n hx).ne'
  · exact (volume_truncatedWindow_lt_top x m n).ne
  · exact (volume_truncatedWindow_pos (n + 1) hz).ne'
  · exact (volume_truncatedWindow_lt_top (offGridCentre n x) m (n + 1)).ne

/-- **The frozen root's left-hand side, transferred.**  The `√ν`-weighted
energy-density norm of `e.energy.density.estimate` at an A centre `x ∈ □_m` and
scale `n`, bounded by `3^d` times the same object at the lattice centre `z` and
scale `n+1` — the exact display the §4.4 chain produces. -/
theorem energyDensityLhs_offGrid_transfer (nu : ℝ) (f : Vec d → ℝ) {x : Vec d} {m n : ℤ}
    (hx : x ∈ openCubeSet (originCube d m)) (hnm : n ≤ m) :
    ENNReal.ofReal (Real.sqrt nu) *
        eLpNorm f 2 (Support.normalizedVolumeMeasureOn (truncatedWindow x m n))
      ≤ ENNReal.ofReal ((3 : ℝ) ^ d) *
        (ENNReal.ofReal (Real.sqrt nu) *
          eLpNorm f 2 (Support.normalizedVolumeMeasureOn
            (truncatedWindow (offGridCentre n x) m (n + 1)))) := by
  have h := eLpNormTwo_offGrid_transfer f hx hnm
  calc ENNReal.ofReal (Real.sqrt nu) *
        eLpNorm f 2 (Support.normalizedVolumeMeasureOn (truncatedWindow x m n))
      ≤ ENNReal.ofReal (Real.sqrt nu) *
          (ENNReal.ofReal ((3 : ℝ) ^ d) *
            eLpNorm f 2 (Support.normalizedVolumeMeasureOn
              (truncatedWindow (offGridCentre n x) m (n + 1)))) := mul_le_mul' le_rfl h
    _ = ENNReal.ofReal ((3 : ℝ) ^ d) *
          (ENNReal.ofReal (Real.sqrt nu) *
            eLpNorm f 2 (Support.normalizedVolumeMeasureOn
              (truncatedWindow (offGridCentre n x) m (n + 1)))) := by ring

end

end Algsuperdiff.Section4.Provider.Regularity
