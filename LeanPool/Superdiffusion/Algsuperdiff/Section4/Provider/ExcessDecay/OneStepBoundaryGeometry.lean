/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OddReflectionVolume
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepSchauderWindow

/-!
# OneStepBoundaryGeometry

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The boundary ball family: the Schauder geometry on the doubled window

`OneStepSchauderWindow.metricBall_subset_truncatedWindow_of_interior` supplies the
ball family the Schauder atom consumes on the **interior** branch: every point of
the Hölder window `U_3 = (x + □_{n-3}) ∩ □_m` carries a sup-ball of radius
`3^{n-3}/2` inside the replacement window `U_2 = (x + □_{n-2}) ∩ □_m`.  That
inclusion needs the interior hypothesis `x + □_{n-2} ⊆ □_m`, because a point of
`U_3` may sit at *zero* distance from a met face of `∂□_m`.

On the **boundary** branch the harmonicity domain is not `U_2` but its partial
reflection `reflectedWindow x m (n-2)` (`OddReflectionWindow`), across every met
face of `∂□_m` at once.  This module records that **the same radius works there,
with no interior hypothesis and with no restriction on the number of met faces**:

```text
  p ∈ (x + □_{n-3}) ∩ □_m   ⟹   ball p (3^{n-3}/2) ⊆ reflectedWindow x m (n-2) .
```

## Why the unmet coordinates are free (the machine-checked point)

The apparent difficulty — "along an unmet coordinate the window is still cut by
`∂□_m`" — does not exist: *being cut in coordinate `i` is the definition of
meeting the `i`-face*.  `MeetsUpperFace x m k i` is literally
`½·3^m ≤ xᵢ + ½·3^k`, i.e. `windowHi x m k i = ½·3^m`; if the face is **not** met
then `windowHi x m k i = xᵢ + ½·3^k` and the window has its full triadic edge in
that coordinate.  So on an unmet coordinate the margin is the interior margin
`3^{n-2}/2 − 3^{n-3}/2 = 3^{n-3}` of one full triadic scale, and on a met
coordinate the reflection supplies the same margin on the far side.  Both cases
are already discharged, coordinate by coordinate, by
`OddReflectionWindow.image_add_openCubeSet_subset_reflectedWindow`, which is
proved by a three-way `by_cases` on `MeetsUpperFace` / `MeetsLowerFace` /
neither; the present module only converts its cube conclusion `p + □_{n-3}` into
the ball shape the atom consumes and adds the volume bookkeeping.

**Consequence for the multi-met-face question.**  The *geometry* of the boundary
branch is uniform in the met set `S ⊆ Fin d`: nothing here assumes `#S ≤ 1`.  The
one-met-face restriction of `OddReflectionAssembly` is a restriction on the
*analytic* transfer (the harmonicity of the odd extension), not on the ball
family.

## The volume ratio

`|reflectedWindow x m (n-2)| ≤ 2^d · |U_2| ≤ (2·3^{n-2})^d`
(`OddReflectionVolume.volume_reflectedWindow_le`, then the window sandwich), and
`|euclideanBall p ρ| ≥ (ρ/(d+1))^d` at `ρ = 3^{n-3}/4`, so the ratio is bounded
by the **scale-free** constant `(24(d+1))^d` — exactly twice the interior base
`12(d+1)`, the reflection's `2^d` spread over the `d` factors.

## References

* ABK26, `l.excess.decay.good.scales`, the Schauder gradient-Hölder estimate.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

open MeasureTheory InnerProductSpace
open HCPolySupport (Vec euclideanBall openCubeSet originCube mem_openCubeSet_originCube_iff)
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. Sup-balls are triadic cubes -/

/-- The sup-ball of radius `3^k/2` centred at `p` **is** the translated open cube
`p + □_k`; only the inclusion `⊆` is needed downstream. -/
theorem metricBall_subset_image_add_openCubeSet (k : ℤ) (p : Vec d) :
    Metric.ball p ((3 : ℝ) ^ k / 2) ⊆ (fun y => p + y) '' openCubeSet (originCube d k) := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
  have hR : (0 : ℝ) < (3 : ℝ) ^ k / 2 := by linarith only [h3]
  intro q hq
  rw [Metric.mem_ball, dist_pi_lt_iff hR] at hq
  refine ⟨q - p, ?_, ?_⟩
  · rw [mem_openCubeSet_originCube_iff]
    intro i
    have h1 : |q i - p i| < (3 : ℝ) ^ k / 2 := by
      have := hq i
      rwa [Real.dist_eq] at this
    have h := abs_lt.1 h1
    exact ⟨by simpa using (by linarith only [h.1] :
        (-(1 / 2 : ℝ)) * (3 : ℝ) ^ k < q i - p i),
      by simpa using (by linarith only [h.2] : q i - p i < (1 / 2 : ℝ) * (3 : ℝ) ^ k)⟩
  · funext i
    change p i + (q i - p i) = q i
    ring

/-! ## 2. The boundary ball family -/

/-- **The boundary ball family.**  Every point of the Hölder window
`(x + □_{n-3}) ∩ □_m` carries a sup-ball of radius `3^{n-3}/2` inside the
partially reflected window `reflectedWindow x m (n-2)` — the *same* radius as the
interior family of `metricBall_subset_truncatedWindow_of_interior`, with the
interior hypothesis `x + □_{n-2} ⊆ □_m` **removed** and with no restriction on
which, or on how many, faces of `∂□_m` are met. -/
theorem metricBall_subset_reflectedWindow {m n : ℤ} {x : Vec d}
    (hmn : n - 2 < m) (hx : x ∈ openCubeSet (originCube d m))
    {p : Vec d} (hp : p ∈ truncatedWindow x m (n - 3)) :
    Metric.ball p ((3 : ℝ) ^ (n - 3) / 2) ⊆ reflectedWindow x m (n - 2) :=
  subset_trans (metricBall_subset_image_add_openCubeSet (n - 3) p)
    (image_add_openCubeSet_subset_reflectedWindow hmn hx hp)

/-- The Euclidean-ball form of the boundary family, at any admissible radius. -/
theorem euclideanBall_subset_reflectedWindow {m n : ℤ} {x : Vec d}
    (hmn : n - 2 < m) (hx : x ∈ openCubeSet (originCube d m))
    {p : Vec d} (hp : p ∈ truncatedWindow x m (n - 3)) {rho : ℝ} (hrho : 0 < rho)
    (hle : rho ≤ (3 : ℝ) ^ (n - 3) / 2) :
    euclideanBall p rho ⊆ reflectedWindow x m (n - 2) :=
  subset_trans
    (subset_trans (HCPolySupport.euclideanBall_subset_metricBall hrho)
      (Metric.ball_subset_ball hle))
    (metricBall_subset_reflectedWindow hmn hx hp)

/-- The `toEuc`-image form of the boundary family, as the Schauder atom consumes
it. -/
theorem metricBall_toEuc_subset_image_reflectedWindow {m n : ℤ} {x : Vec d}
    (hmn : n - 2 < m) (hx : x ∈ openCubeSet (originCube d m))
    {p : Vec d} (hp : p ∈ truncatedWindow x m (n - 3)) :
    Metric.ball (toEuc p) ((3 : ℝ) ^ (n - 3) / 2) ⊆
      (toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' reflectedWindow x m (n - 2) := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (n - 3) := zpow_pos (by norm_num) _
  have hR : (0 : ℝ) < (3 : ℝ) ^ (n - 3) / 2 := by linarith only [h3]
  intro w hw
  have hq : toEuc (toEuc.symm w) ∈ Metric.ball (toEuc p) ((3 : ℝ) ^ (n - 3) / 2) := by
    rwa [ContinuousLinearEquiv.apply_symm_apply]
  have hmem : toEuc.symm w ∈ euclideanBall p ((3 : ℝ) ^ (n - 3) / 2) :=
    (mem_euclideanBall_toEuc_iff (toEuc.symm w) p hR).1 hq
  exact ⟨toEuc.symm w,
    euclideanBall_subset_reflectedWindow hmn hx hp hR le_rfl hmem,
    ContinuousLinearEquiv.apply_symm_apply _ _⟩

/-! ## 3. The volume of the reflected window -/

theorem volume_reflectedWindow_ne_top (x : Vec d) (m k : ℤ) :
    volume (reflectedWindow x m k) ≠ ⊤ :=
  ne_of_lt (lt_of_le_of_lt (measure_mono (reflectedWindow_subset_openCubeSet x m k))
    (HCPolySupport.volume_openCubeSet_lt_top _))

theorem volume_toReal_reflectedWindow_pos {m k : ℤ} (x : Vec d)
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k - 1 ≤ m) :
    0 < (volume (reflectedWindow x m k)).toReal :=
  lt_of_lt_of_le (volume_toReal_truncatedWindow_pos x hx hkm)
    (ENNReal.toReal_mono (volume_reflectedWindow_ne_top x m k)
      (volume_truncatedWindow_le_volume_reflectedWindow x m k))

/-- **The reflected window's volume, from above.**  The partial reflection costs
a factor `2^d` (exactly `2^{#S}`), and the window itself is inside a cube of side
`3^k`. -/
theorem volume_toReal_reflectedWindow_le {m k : ℤ} (x : Vec d)
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k - 1 ≤ m) (hkm' : k < m) :
    (volume (reflectedWindow x m k)).toReal ≤ (2 * (3 : ℝ) ^ k) ^ d := by
  have hfin : (2 : ℝ≥0∞) ^ d * volume (truncatedWindow x m k) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top (by simp))
      (ne_of_lt (volume_truncatedWindow_lt_top x m k))
  have h2 := ENNReal.toReal_mono hfin (volume_reflectedWindow_le x hkm')
  have hc : ((2 : ℝ≥0∞) ^ d).toReal = (2 : ℝ) ^ d := by
    rw [ENNReal.toReal_pow]
    norm_num
  rw [ENNReal.toReal_mul, hc] at h2
  have hW := (volume_toReal_truncatedWindow_bounds x hx hkm).2
  calc (volume (reflectedWindow x m k)).toReal
      ≤ 2 ^ d * (volume (truncatedWindow x m k)).toReal := h2
    _ ≤ 2 ^ d * ((3 : ℝ) ^ k) ^ d := mul_le_mul_of_nonneg_left hW (by positivity)
    _ = (2 * (3 : ℝ) ^ k) ^ d := (mul_pow 2 ((3 : ℝ) ^ k) d).symm

/-! ## 4. The scale-free volume ratio of the boundary family -/

/-- The ratio constant of the boundary gap: `√((24(d+1))^d)` — the interior
constant `√((12(d+1))^d)` with the reflection's factor `2^d` folded in. -/
def boundarySchauderRatioConst (d : ℕ) : ℝ := Real.sqrt ((24 * ((d : ℝ) + 1)) ^ d)

theorem boundarySchauderRatioConst_nonneg (d : ℕ) : 0 ≤ boundarySchauderRatioConst d :=
  Real.sqrt_nonneg _

/-- **The boundary volume ratio is scale free.**  The ratio of the reflected
window's volume to the volume of any of the atom's half-balls is at most
`(24(d+1))^d`, independently of `n`, `m` and `x`. -/
theorem sqrt_volume_ratio_reflected_le {m n : ℤ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) (hmn : n - 2 < m) (p : Vec d) :
    Real.sqrt ((volume (reflectedWindow x m (n - 2))).toReal /
        (volume (euclideanBall p ((3 : ℝ) ^ (n - 3) / 2 / 2))).toReal)
      ≤ boundarySchauderRatioConst d := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (n - 3) := zpow_pos (by norm_num) _
  have hrho : (0 : ℝ) < (3 : ℝ) ^ (n - 3) / 2 / 2 := by linarith only [h3]
  have hd1 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have hnum : (volume (reflectedWindow x m (n - 2))).toReal ≤ (2 * (3 : ℝ) ^ (n - 2)) ^ d :=
    volume_toReal_reflectedWindow_le x hx (by omega) hmn
  have hden := volume_toReal_euclideanBall_ge p hrho
  have hdenpos : (0 : ℝ) < ((3 : ℝ) ^ (n - 3) / 2 / 2 / ((d : ℝ) + 1)) ^ d := by positivity
  have hdenpos' : (0 : ℝ) < (volume (euclideanBall p ((3 : ℝ) ^ (n - 3) / 2 / 2))).toReal :=
    lt_of_lt_of_le hdenpos hden
  have hquot : (2 * (3 : ℝ) ^ (n - 2)) ^ d / ((3 : ℝ) ^ (n - 3) / 2 / 2 / ((d : ℝ) + 1)) ^ d
      = (24 * ((d : ℝ) + 1)) ^ d := by
    rw [← div_pow]
    congr 1
    have hscale : (3 : ℝ) ^ (n - 2) = 3 * (3 : ℝ) ^ (n - 3) := by
      rw [show n - 2 = (n - 3) + 1 by ring, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_one]
      ring
    rw [hscale]
    field_simp
    ring
  have hstep : (volume (reflectedWindow x m (n - 2))).toReal /
      (volume (euclideanBall p ((3 : ℝ) ^ (n - 3) / 2 / 2))).toReal
      ≤ (24 * ((d : ℝ) + 1)) ^ d := by
    rw [← hquot]
    calc (volume (reflectedWindow x m (n - 2))).toReal /
          (volume (euclideanBall p ((3 : ℝ) ^ (n - 3) / 2 / 2))).toReal
        ≤ (2 * (3 : ℝ) ^ (n - 2)) ^ d /
            (volume (euclideanBall p ((3 : ℝ) ^ (n - 3) / 2 / 2))).toReal :=
          div_le_div_of_nonneg_right hnum hdenpos'.le
      _ ≤ (2 * (3 : ℝ) ^ (n - 2)) ^ d / ((3 : ℝ) ^ (n - 3) / 2 / 2 / ((d : ℝ) + 1)) ^ d :=
          div_le_div_of_nonneg_left (by positivity) hdenpos hden
  exact Real.sqrt_le_sqrt hstep

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
