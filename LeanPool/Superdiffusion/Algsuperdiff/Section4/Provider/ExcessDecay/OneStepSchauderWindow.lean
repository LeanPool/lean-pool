/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepSchauderInterior
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepWindows

/-!
# OneStepSchauderWindow

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The interior gap: instantiating the Schauder atom at the §4 windows

`OneStepSchauderInterior.gradField_holderHalf_of_harmonic` is stated for an
abstract convex window `W` inside an enveloping window `W₂`.  Here it is
instantiated at the §4 pair

```text
  W  = (x + □_{n-3}) ∩ □_m ,    W₂ = (x + □_{n-2}) ∩ □_m ,
```

on the **interior branch**, i.e. under the hypothesis `x + □_{n-2} ⊆ □_m` (the
replacement cube is a full translated cube, so `W₂ = x + □_{n-2}`), which is the
branch on which the boundary datum contributes nothing.

## The interior gap, quantified

For `p ∈ W` the sup-distance from `p` to `∂(x + □_{n-2})` is at least

```text
  (3^{n-2} − 3^{n-3}) / 2  =  3^{n-3} ,
```

one full triadic scale.  Taking `R := 3^{n-3}/2` therefore gives
`euclideanBall p R ⊆ Metric.ball p R ⊆ x + □_{n-2}` for **every** `p ∈ W`, with a
factor-`2` margin.  This is the ball family the atom consumes; note that a
*single* ball centred at `x` would not do (see `OneStepSchauderInterior`).

## The volume ratio

```text
  |euclideanBall p (R/2)| ≥ ((R/2)/(d+1))^d = (3^{n-3}/(4(d+1)))^d ,
```

so the ratio is bounded by the **scale-free** constant `(12(d+1))^d`.

## The resulting constant

```text
  Csch(d) = schauderWindowConst d = 48 · 3^{3/2} · schauderConst d · √((12(d+1))^d) ,
```

`schauderConst d = d · C_native(d)` being the constant of the transplanted native
interior Hessian estimate.  The bound produced is

```text
  [∇v]_{C^{0,1/2}(W)} ≤ Csch(d) · (3^{-n})^{1/2} · E(v, W₂) ,
```

i.e. exactly the Schauder display with `K_h = 0` — the interior
branch carries no boundary-datum contribution.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

open MeasureTheory InnerProductSpace
open HCPolySupport (Vec euclideanBall openCubeSet originCube mem_openCubeSet_originCube_iff)
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. The ball family inside the enveloping window -/

/-- **The interior gap.**  On the interior branch every point of the window at
scale `n-3` carries a sup-ball of radius `3^{n-3}/2` inside the replacement cube
at scale `n-2`. -/
theorem metricBall_subset_truncatedWindow_of_interior {x : Vec d} {m n : ℤ}
    (hcube : (fun y => x + y) '' openCubeSet (originCube d (n - 2)) ⊆
      openCubeSet (originCube d m))
    {p : Vec d} (hp : p ∈ truncatedWindow x m (n - 3)) :
    Metric.ball p ((3 : ℝ) ^ (n - 3) / 2) ⊆ truncatedWindow x m (n - 2) := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (n - 3) := zpow_pos (by norm_num) _
  have hR : (0 : ℝ) < (3 : ℝ) ^ (n - 3) / 2 := by linarith only [h3]
  have hpx : ∀ i, |p i - x i| < (3 : ℝ) ^ (n - 3) / 2 := by
    obtain ⟨y, hy, hpy⟩ := hp.1
    rw [mem_openCubeSet_originCube_iff] at hy
    intro i
    have hyi := hy i
    have hpi : p i - x i = y i := by
      rw [← hpy]
      change x i + y i - x i = y i
      ring
    rw [hpi, abs_lt]
    exact ⟨by linarith only [hyi.1], by linarith only [hyi.2]⟩
  have hscale : (3 : ℝ) ^ (n - 2) = 3 * (3 : ℝ) ^ (n - 3) := by
    rw [show n - 2 = (n - 3) + 1 by ring, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_one]
    ring
  intro q hq
  rw [Metric.mem_ball, dist_pi_lt_iff hR] at hq
  have hqx : ∀ i, |q i - x i| < (1 / 2 : ℝ) * (3 : ℝ) ^ (n - 2) := by
    intro i
    have h1 : |q i - p i| < (3 : ℝ) ^ (n - 3) / 2 := by
      have := hq i
      rwa [Real.dist_eq] at this
    have h2 := hpx i
    have habs1 := abs_lt.1 h1
    have habs2 := abs_lt.1 h2
    rw [abs_lt, hscale]
    constructor <;> linarith only [habs1.1, habs1.2, habs2.1, habs2.2]
  have hmem : q ∈ (fun y => x + y) '' openCubeSet (originCube d (n - 2)) := by
    refine ⟨q - x, ?_, ?_⟩
    · rw [mem_openCubeSet_originCube_iff]
      intro i
      have h := abs_lt.1 (hqx i)
      exact ⟨by simpa using (by linarith only [h.1] :
          (-(1 / 2 : ℝ)) * (3 : ℝ) ^ (n - 2) < q i - x i),
        by simpa using (by linarith only [h.2] :
          q i - x i < (1 / 2 : ℝ) * (3 : ℝ) ^ (n - 2))⟩
    · funext i
      change x i + (q i - x i) = q i
      ring
  exact ⟨hmem, hcube hmem⟩

theorem euclideanBall_subset_truncatedWindow_of_interior {x : Vec d} {m n : ℤ}
    (hcube : (fun y => x + y) '' openCubeSet (originCube d (n - 2)) ⊆
      openCubeSet (originCube d m))
    {p : Vec d} (hp : p ∈ truncatedWindow x m (n - 3)) {rho : ℝ} (hrho : 0 < rho)
    (hle : rho ≤ (3 : ℝ) ^ (n - 3) / 2) :
    euclideanBall p rho ⊆ truncatedWindow x m (n - 2) := by
  refine subset_trans ?_ (metricBall_subset_truncatedWindow_of_interior hcube hp)
  exact subset_trans (HCPolySupport.euclideanBall_subset_metricBall hrho)
    (Metric.ball_subset_ball hle)

/-- The `toEuc`-image form of the ball family, as the atom consumes it. -/
theorem metricBall_toEuc_subset_image_of_interior {x : Vec d} {m n : ℤ}
    (hcube : (fun y => x + y) '' openCubeSet (originCube d (n - 2)) ⊆
      openCubeSet (originCube d m))
    {p : Vec d} (hp : p ∈ truncatedWindow x m (n - 3)) :
    Metric.ball (toEuc p) ((3 : ℝ) ^ (n - 3) / 2) ⊆
      (toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' truncatedWindow x m (n - 2) := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (n - 3) := zpow_pos (by norm_num) _
  have hR : (0 : ℝ) < (3 : ℝ) ^ (n - 3) / 2 := by linarith only [h3]
  intro w hw
  have hq : toEuc (toEuc.symm w) ∈ Metric.ball (toEuc p) ((3 : ℝ) ^ (n - 3) / 2) := by
    rwa [ContinuousLinearEquiv.apply_symm_apply]
  have hmem : toEuc.symm w ∈ euclideanBall p ((3 : ℝ) ^ (n - 3) / 2) :=
    (mem_euclideanBall_toEuc_iff (toEuc.symm w) p hR).1 hq
  refine ⟨toEuc.symm w, ?_, ?_⟩
  · exact euclideanBall_subset_truncatedWindow_of_interior hcube hp hR le_rfl hmem
  · exact ContinuousLinearEquiv.apply_symm_apply _ _

/-! ## 2. The volume of the Euclidean ball, from below -/

/-- **A scale-free lower bound for the Euclidean ball volume.**  CoarseGraining's
conservative inclusion `closedBall p (ρ/(2(d+1))) ⊆ euclideanBall p ρ` and the
product-measure formula give `|euclideanBall p ρ| ≥ (ρ/(d+1))^d`. -/
theorem volume_toReal_euclideanBall_ge (p : Vec d) {rho : ℝ} (hrho : 0 < rho) :
    (rho / ((d : ℝ) + 1)) ^ d ≤ (volume (euclideanBall p rho)).toReal := by
  have hden : (0 : ℝ) < 2 * ((d : ℝ) + 1) := by positivity
  have hs : (0 : ℝ) ≤ rho / (2 * ((d : ℝ) + 1)) := by positivity
  have hsub : Metric.closedBall p (rho / (2 * ((d : ℝ) + 1))) ⊆ euclideanBall p rho :=
    HCPolySupport.metricClosedBall_div_two_natCast_succ_subset_euclideanBall hrho
  have hvolball : volume (Metric.closedBall p (rho / (2 * ((d : ℝ) + 1))))
      = ENNReal.ofReal ((2 * (rho / (2 * ((d : ℝ) + 1)))) ^ Fintype.card (Fin d)) :=
    Real.volume_pi_closedBall p hs
  have hcard : Fintype.card (Fin d) = d := Fintype.card_fin d
  have hcoef : 2 * (rho / (2 * ((d : ℝ) + 1))) = rho / ((d : ℝ) + 1) := by
    field_simp
  have hmono : volume (Metric.closedBall p (rho / (2 * ((d : ℝ) + 1))))
      ≤ volume (euclideanBall p rho) := measure_mono hsub
  have htop : volume (euclideanBall p rho) ≠ ⊤ :=
    HCPolySupport.Book.Ch01.volume_euclideanBall_ne_top p rho
  have hle := ENNReal.toReal_mono htop hmono
  rw [hvolball, hcard, hcoef, ENNReal.toReal_ofReal (by positivity)] at hle
  exact hle

/-! ## 3. The scale-free volume ratio -/

/-- The ratio constant of the interior gap: `√((12(d+1))^d)`. -/
def schauderRatioConst (d : ℕ) : ℝ := Real.sqrt ((12 * ((d : ℝ) + 1)) ^ d)

theorem schauderRatioConst_nonneg (d : ℕ) : 0 ≤ schauderRatioConst d := Real.sqrt_nonneg _

/-- **The volume ratio is scale free.**  On the interior branch the ratio of the
enveloping window's volume to the volume of any of the atom's balls is at most
`(12(d+1))^d`, independently of `n`. -/
theorem sqrt_volume_ratio_le {x : Vec d} {m n : ℤ}
    (hx : x ∈ openCubeSet (originCube d m)) (hnm : n - 3 ≤ m) (p : Vec d) :
    Real.sqrt ((volume (truncatedWindow x m (n - 2))).toReal /
        (volume (euclideanBall p ((3 : ℝ) ^ (n - 3) / 2 / 2))).toReal)
      ≤ schauderRatioConst d := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (n - 3) := zpow_pos (by norm_num) _
  have hrho : (0 : ℝ) < (3 : ℝ) ^ (n - 3) / 2 / 2 := by linarith only [h3]
  have hd1 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  -- numerator
  have hnum : (volume (truncatedWindow x m (n - 2))).toReal ≤ ((3 : ℝ) ^ (n - 2)) ^ d :=
    (volume_toReal_truncatedWindow_bounds x hx (by omega : n - 2 - 1 ≤ m)).2
  -- denominator
  have hden := volume_toReal_euclideanBall_ge p hrho
  have hdenpos : (0 : ℝ) < ((3 : ℝ) ^ (n - 3) / 2 / 2 / ((d : ℝ) + 1)) ^ d := by positivity
  have hdenpos' : (0 : ℝ) < (volume (euclideanBall p ((3 : ℝ) ^ (n - 3) / 2 / 2))).toReal :=
    lt_of_lt_of_le hdenpos hden
  -- the quotient of the two explicit powers
  have hquot : ((3 : ℝ) ^ (n - 2)) ^ d / ((3 : ℝ) ^ (n - 3) / 2 / 2 / ((d : ℝ) + 1)) ^ d
      = (12 * ((d : ℝ) + 1)) ^ d := by
    rw [← div_pow]
    congr 1
    have hscale : (3 : ℝ) ^ (n - 2) = 3 * (3 : ℝ) ^ (n - 3) := by
      rw [show n - 2 = (n - 3) + 1 by ring, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_one]
      ring
    rw [hscale]
    field_simp
    ring
  have hstep : (volume (truncatedWindow x m (n - 2))).toReal /
      (volume (euclideanBall p ((3 : ℝ) ^ (n - 3) / 2 / 2))).toReal
      ≤ (12 * ((d : ℝ) + 1)) ^ d := by
    rw [← hquot]
    calc (volume (truncatedWindow x m (n - 2))).toReal /
          (volume (euclideanBall p ((3 : ℝ) ^ (n - 3) / 2 / 2))).toReal
        ≤ ((3 : ℝ) ^ (n - 2)) ^ d /
            (volume (euclideanBall p ((3 : ℝ) ^ (n - 3) / 2 / 2))).toReal :=
          div_le_div_of_nonneg_right hnum hdenpos'.le
      _ ≤ ((3 : ℝ) ^ (n - 2)) ^ d / ((3 : ℝ) ^ (n - 3) / 2 / 2 / ((d : ℝ) + 1)) ^ d :=
          div_le_div_of_nonneg_left (by positivity) hdenpos hden
  exact Real.sqrt_le_sqrt hstep

/-! ## 4. The window diameter -/

theorem norm_sub_le_of_mem_truncatedWindow_pair {x : Vec d} {m k : ℤ} {p q : Vec d}
    (hp : p ∈ truncatedWindow x m k) (hq : q ∈ truncatedWindow x m k) :
    ‖p - q‖ ≤ (3 : ℝ) ^ k := by
  have h1 := norm_sub_le_of_mem_truncatedWindow hp
  have h2 := norm_sub_le_of_mem_truncatedWindow hq
  have htri : ‖p - q‖ ≤ ‖p - x‖ + ‖x - q‖ := by
    have := norm_sub_le_norm_sub_add_norm_sub p x q
    simpa using this
  have h2' : ‖x - q‖ ≤ (3 : ℝ) ^ k / 2 := by rwa [norm_sub_rev]
  linarith only [htri, h1, h2']

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
