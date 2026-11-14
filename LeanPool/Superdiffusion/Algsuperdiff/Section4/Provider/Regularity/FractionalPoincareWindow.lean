/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.FractionalPoincare
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryLaneWindows
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.CubeMoments

/-!
# FractionalPoincareWindow

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The mean-zero fractional Poincaré inequality on the §4.3/§4.4 windows

## The estimate

On the truncated window `U_k = (x + □_k) ∩ □_m` of a centre `x ∈ □_m`, at any
scale `k ≤ m` and any `0 ≤ s`,

```text
  ‖f - ⨍_{U_k} f‖_{L²(U_k)}  ≤  2^{d/2} · 3^{ks} · [f]_{H^s(U_k)} .
```

At the anchor's own window `k = n+3` and the development's range `0 ≤ s ≤ 1`
this is the numeral `2^{d/2}·27·3^{ns}` (`…_anchorWindow_le`): a **dimensional,
`s`-uniform** constant.  Nothing degenerates at either endpoint of the `s`
range.

## The two geometric inputs, both sharp

* **the diameter** — `truncatedWindow_dist_le`: `U_k` sits in a cube of side
  `3^k`, so any two of its points are within `3^k` in the ambient supremum
  metric.  Exactly the side, no loss.
* **the volume** — `volume_toReal_truncatedWindow_half_ge`: every coordinate
  slice of `U_k` keeps at least *half* the small interval, so `U_k` contains an
  axis cube of side `3^k/2` and `|U_k| ≥ (3^k/2)^d`.  This is the sharp lower
  bound; the inscribed-cube route already proved (`volume_truncatedWindow_ge`
  at `(3^{k-1})^d`, `volume_toReal_truncatedWindow_bounds` at `(3^{k-2})^d`)
  costs `(3/2)^d` resp.  `(9/2)^d` more, which is why the corner is computed
  here instead.  The corner is the coordinatewise clamp `max(xᵢ - 3^k/2,
  -3^m/2)`.

Their combination is the only place the constant is produced: the general
estimate's factor is `D^{s+d/2}/|W|^{1/2}`, and

```text
  (3^k)^{s+d/2} / ((3^k/2)^d)^{1/2}  =  2^{d/2}·(3^k)^s .
```

## References

* ABK26, (`L²`), (`H^s`).
* `Algsuperdiff/Section4/Provider/Regularity/FractionalPoincare.lean`.
* `Algsuperdiff/Section4/Provider/ExcessDecay/BoundaryLaneWindows.lean`
  (`truncatedWindow`).
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The diameter of a truncated window -/

/-- Two points of `U_k = (x+□_k) ∩ □_m` are within `3^k` in the ambient
supremum metric. -/
theorem truncatedWindow_dist_le {x : Vec d} {m k : ℤ} {p q : Vec d}
    (hp : p ∈ truncatedWindow x m k) (hq : q ∈ truncatedWindow x m k) :
    dist p q ≤ (3 : ℝ) ^ k := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) k
  have hpc := mem_openCubeSet_originCube_iff.mp (sub_mem_openCubeSet_of_mem_truncatedWindow hp)
  have hqc := mem_openCubeSet_originCube_iff.mp (sub_mem_openCubeSet_of_mem_truncatedWindow hq)
  simp only [Pi.sub_apply] at hpc hqc
  rw [dist_pi_le_iff h3.le]
  intro i
  have hpi := hpc i
  have hqi := hqc i
  rw [Real.dist_eq, abs_le]
  constructor
  · linarith only [hpi.1, hqi.2]
  · linarith only [hpi.2, hqi.1]

/-! ## 2. The sharp volume lower bound -/

/-- The lower corner of the inscribed half-side axis cube: the coordinatewise
clamp of `xᵢ - 3^k/2` into `□_m`. -/
def halfWindowCorner (x : Vec d) (m k : ℤ) : Vec d :=
  fun i => max (x i - (1 / 2 : ℝ) * (3 : ℝ) ^ k) (-(1 / 2 : ℝ) * (3 : ℝ) ^ m)

/-- **The inscribed half-side cube.**  Every coordinate slice of `U_k` keeps at
least half the small interval, so the axis cube of side `3^k/2` at the clamped
corner sits inside `U_k`. -/
theorem axisCube_halfWindowCorner_subset_truncatedWindow {x : Vec d} {m k : ℤ}
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k ≤ m) :
    axisCube (halfWindowCorner x m k) ((1 / 2 : ℝ) * (3 : ℝ) ^ k) ⊆ truncatedWindow x m k := by
  have h3k : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) k
  have h3m : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  have hkm3 : (3 : ℝ) ^ k ≤ (3 : ℝ) ^ m := zpow_le_zpow_right₀ (by norm_num) hkm
  have hxc := mem_openCubeSet_originCube_iff.mp hx
  intro p hp
  rw [axisCube, Set.mem_univ_pi] at hp
  have hpi : ∀ i, halfWindowCorner x m k i < p i ∧
      p i < halfWindowCorner x m k i + (1 / 2 : ℝ) * (3 : ℝ) ^ k := fun i => hp i
  refine ⟨⟨p - x, ?_, by simp⟩, ?_⟩
  · rw [mem_openCubeSet_originCube_iff]
    intro i
    have hi := hpi i
    have hxi := hxc i
    simp only [Pi.sub_apply]
    rcases max_cases (x i - (1 / 2 : ℝ) * (3 : ℝ) ^ k) (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) with
      ⟨heq, hcmp⟩ | ⟨heq, hcmp⟩ <;>
      rw [halfWindowCorner, heq] at hi
    · exact ⟨by linarith only [hi.1], by linarith only [hi.2, h3k]⟩
    · exact ⟨by linarith only [hi.1, hcmp], by linarith only [hi.2, hxi.1]⟩
  · rw [mem_openCubeSet_originCube_iff]
    intro i
    have hi := hpi i
    have hxi := hxc i
    rcases max_cases (x i - (1 / 2 : ℝ) * (3 : ℝ) ^ k) (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) with
      ⟨heq, hcmp⟩ | ⟨heq, _⟩ <;>
      rw [halfWindowCorner, heq] at hi
    · exact ⟨by linarith only [hi.1, hcmp], by linarith only [hi.2, hxi.2]⟩
    · exact ⟨by linarith only [hi.1], by linarith only [hi.2, hkm3, h3m]⟩

/-- **The sharp window volume.**  `|U_k| ≥ (3^k/2)^d`. -/
theorem volume_toReal_truncatedWindow_half_ge {x : Vec d} {m k : ℤ}
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k ≤ m) :
    ((1 / 2 : ℝ) * (3 : ℝ) ^ k) ^ d ≤ (volume (truncatedWindow x m k)).toReal := by
  have h3k : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) k
  have hhalf : (0 : ℝ) ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ k := by linarith only [h3k]
  have hmono := measure_mono (μ := (volume : Measure (Vec d)))
    (axisCube_halfWindowCorner_subset_truncatedWindow hx hkm)
  have hcube := volume_axisCube_toReal (halfWindowCorner x m k) hhalf
  rw [← hcube]
  exact ENNReal.toReal_mono (volume_truncatedWindow_lt_top x m k).ne hmono

/-! ## 3. The constant arithmetic (abstract reals) -/

private theorem side_rpow_div_sqrt_le (d : ℕ) {L V s : ℝ} (hL : 0 < L)
    (hV : ((1 / 2 : ℝ) * L) ^ d ≤ V) :
    L ^ (s + (d : ℝ) / 2) / Real.sqrt V ≤ (2 : ℝ) ^ ((d : ℝ) / 2) * L ^ s := by
  have hhalf : (0 : ℝ) < (1 / 2 : ℝ) * L := by linarith only [hL]
  have hVpos : (0 : ℝ) < V := lt_of_lt_of_le (pow_pos hhalf d) hV
  have hA : (2 : ℝ) ^ ((d : ℝ) / 2) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
  have hK : (0 : ℝ) ≤ (2 : ℝ) ^ ((d : ℝ) / 2) * L ^ s :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hL.le _)
  have hsq : Real.sqrt (((1 / 2 : ℝ) * L) ^ d) = ((1 / 2 : ℝ) * L) ^ ((d : ℝ) / 2) := by
    rw [← Real.rpow_natCast ((1 / 2 : ℝ) * L) d, Real.sqrt_eq_rpow, ← Real.rpow_mul hhalf.le]
    congr 1
    ring
  have hle : ((1 / 2 : ℝ) * L) ^ ((d : ℝ) / 2) ≤ Real.sqrt V := by
    rw [← hsq]
    exact Real.sqrt_le_sqrt hV
  have hid : ((2 : ℝ) ^ ((d : ℝ) / 2) * L ^ s) * ((1 / 2 : ℝ) * L) ^ ((d : ℝ) / 2)
      = L ^ (s + (d : ℝ) / 2) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 2) hL.le, Real.rpow_add hL,
      show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
      Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2)]
    have hswap : ((2 : ℝ) ^ ((d : ℝ) / 2) * L ^ s) *
        (((2 : ℝ) ^ ((d : ℝ) / 2))⁻¹ * L ^ ((d : ℝ) / 2))
        = ((2 : ℝ) ^ ((d : ℝ) / 2) * ((2 : ℝ) ^ ((d : ℝ) / 2))⁻¹) *
            (L ^ s * L ^ ((d : ℝ) / 2)) := by ring
    rw [hswap, mul_inv_cancel₀ hA, one_mul]
  rw [← hid, div_le_iff₀ (Real.sqrt_pos.mpr hVpos)]
  exact mul_le_mul_of_nonneg_left hle hK

private theorem side_rpow_eq (k : ℤ) (s : ℝ) :
    ((3 : ℝ) ^ k) ^ s = (3 : ℝ) ^ ((k : ℝ) * s) := by
  rw [← Real.rpow_intCast (3 : ℝ) k, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]

/-! ## 4. The estimate on a truncated window -/

/-- **The mean-zero fractional Poincaré inequality on `U_k = (x+□_k) ∩ □_m`.**

```text
  ‖f - ⨍_{U_k} f‖_{L²(U_k)}  ≤  2^{d/2}·3^{ks}·[f]_{H^s(U_k)} ,
```

with a dimensional, `s`-uniform constant. -/
theorem eLpNorm_sub_integral_truncatedWindow_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {x : Vec d} {m k : ℤ} {s : ℝ} {f : Vec d → E}
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k ≤ m) (hs : 0 ≤ s)
    (hf : Integrable f (volume.restrict (truncatedWindow x m k))) :
    eLpNorm (fun y => f y -
          ∫ p, f p ∂(normalizedVolumeMeasureOn (truncatedWindow x m k))) 2
        (normalizedVolumeMeasureOn (truncatedWindow x m k))
      ≤ ENNReal.ofReal ((2 : ℝ) ^ ((d : ℝ) / 2) * (3 : ℝ) ^ ((k : ℝ) * s))
          * normalizedGagliardoESeminormOn (truncatedWindow x m k) s f := by
  have h3k : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) k
  have hmain := eLpNorm_sub_integral_le_normalizedGagliardoESeminormOn
    (E := E) (W := truncatedWindow x m k) (s := s) (D := (3 : ℝ) ^ k) (f := f)
    (isOpen_truncatedWindow x m k).measurableSet (volume_truncatedWindow_pos k hx)
    (volume_truncatedWindow_lt_top x m k).ne hs
    (fun p hp q hq => truncatedWindow_dist_le hp hq) hf
  refine hmain.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
  rw [← side_rpow_eq k s]
  exact side_rpow_div_sqrt_le (L := (3 : ℝ) ^ k) (s := s)
    (V := (volume (truncatedWindow x m k)).toReal) d h3k
    (volume_toReal_truncatedWindow_half_ge hx hkm)

/-! ## 5. The development's `Vec d`-valued carrier -/

/-- The same estimate with the average written as CoarseGraining's
`volumeAverageVec` — the shape in which the frozen Section-4 surface carries a
vector field's window mean. -/
theorem eLpNorm_sub_volumeAverageVec_truncatedWindow_le
    {x : Vec d} {m k : ℤ} {s : ℝ} {f : Vec d → Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k ≤ m) (hs : 0 ≤ s)
    (hf : Integrable f (volume.restrict (truncatedWindow x m k))) :
    eLpNorm (fun y => f y - volumeAverageVec (truncatedWindow x m k) f) 2
        (normalizedVolumeMeasureOn (truncatedWindow x m k))
      ≤ ENNReal.ofReal ((2 : ℝ) ^ ((d : ℝ) / 2) * (3 : ℝ) ^ ((k : ℝ) * s))
          * normalizedGagliardoESeminormOn (truncatedWindow x m k) s f := by
  have hav := integral_normalizedVolumeMeasureOn_eq_volumeAverageVec hf
  rw [← hav]
  exact eLpNorm_sub_integral_truncatedWindow_le hx hkm hs hf

end

end Algsuperdiff.Section4.Provider.Regularity
