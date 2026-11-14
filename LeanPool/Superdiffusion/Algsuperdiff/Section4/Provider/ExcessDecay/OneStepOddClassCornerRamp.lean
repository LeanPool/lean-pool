/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepOddClassCorner

/-!
# OneStepOddClassCornerRamp

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Corner pricing: the normal ramp and the residual fold

The `L²` bookkeeping of the corner absorption, split off from the assembly
for elaboration budget:

* `abs_slope_mul_delta_le` — the box-moment lower bound: the normal ramp
  `oddᵢ = Aᵢ(yᵢ − a)` satisfies `|Aᵢ|·delta ≤ 7t·‖oddᵢ‖_{L²(U₂)}` at depth
  `delta = t·3^{n−2}`, because the window's `i`-edge exceeds half the triadic
  side and the sharp moment identity gives `‖oddᵢ‖ ≥ |Aᵢ|·edge/√12`.
* `normalizedL2On_oddRamp_cornerPairSlab_le` /
  `..._cornerPairSlabPushed_le` — on the corner slab (and its inward
  `j`-translate) the ramp is pointwise at most `|Aᵢ|·delta`.
* `normalizedL2On_reflected_residual_le` — the fold: the residual
  `V − ℓ` on the doubled window is priced by `(2^d + Crefl)·(E + P)`, via the
  full-met-set odd fold of the competitor and the affine moment comparison of
  the doubled window against the window.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

open MeasureTheory InnerProductSpace
open HCPolySupport (Vec vecDot openCubeSet originCube coordFaceReflection basisVec)
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- **The moment lower bound for the normal ramp**:
`|Aᵢ|·delta ≤ 7t·‖oddᵢ‖_{L²(U₂)}` at `delta = t·3^{n−2}`. -/
theorem abs_slope_mul_delta_le {m n : ℤ} {x : Vec d} {i : Fin d} {A : Vec d}
    {tt delta : ℝ} (hx : x ∈ openCubeSet (originCube d m)) (hmn : n - 2 < m)
    (htt0 : 0 < tt) (hdeltadef : delta = tt * (3 : ℝ) ^ (n - 2)) :
    |A i| * delta
      ≤ 7 * tt * normalizedL2On (truncatedWindow x m (n - 2))
          (oddAffinePart x m i A) := by
  have hw0 : (0 : ℝ) < (3 : ℝ) ^ (n - 2) := zpow_pos (by norm_num) _
  have hdelta0 : 0 < delta := by
    rw [hdeltadef]
    exact mul_pos htt0 hw0
  have hltW := windowLo_lt_windowHi_of_mem hx hmn
  have hsq : normalizedL2On (truncatedWindow x m (n - 2))
      (oddAffinePart x m i A) ^ 2
      = affineEval (oddAffineIntercept x m i A - vecDot (oddAffineSlope i A) x)
          (oddAffineSlope i A)
          (boxCenter (windowLo x m (n - 2)) (windowHi x m (n - 2))) ^ 2
        + ∑ l, (oddAffineSlope i A l) ^ 2
            * ((windowHi x m (n - 2) l - windowLo x m (n - 2) l) ^ 2 / 12) := by
    rw [truncatedWindow_eq_coordBox, oddAffinePart]
    exact normalizedL2On_coordBox_affineEval_sq hltW _ _
  have hterm : (A i) ^ 2
        * ((windowHi x m (n - 2) i - windowLo x m (n - 2) i) ^ 2 / 12)
      ≤ ∑ l, (oddAffineSlope i A l) ^ 2
          * ((windowHi x m (n - 2) l - windowLo x m (n - 2) l) ^ 2 / 12) := by
    have h := Finset.single_le_sum
      (f := fun l => (oddAffineSlope i A l) ^ 2
        * ((windowHi x m (n - 2) l - windowLo x m (n - 2) l) ^ 2 / 12))
      (fun l _ => by positivity) (Finset.mem_univ i)
    simp only [oddAffineSlope_apply_self] at h
    exact h
  have hedge := half_zpow_lt_window_edge hx hmn i
  have hsq48 : (A i) ^ 2 * ((3 : ℝ) ^ (n - 2)) ^ 2 / 48
      ≤ normalizedL2On (truncatedWindow x m (n - 2)) (oddAffinePart x m i A) ^ 2 := by
    have he2 : ((1 / 2 : ℝ) * (3 : ℝ) ^ (n - 2)) ^ 2
        ≤ (windowHi x m (n - 2) i - windowLo x m (n - 2) i) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hedge.le 2
    have hgeom : (A i) ^ 2 * ((3 : ℝ) ^ (n - 2)) ^ 2 / 48
        ≤ (A i) ^ 2
          * ((windowHi x m (n - 2) i - windowLo x m (n - 2) i) ^ 2 / 12) := by
      have hmul : (A i) ^ 2 * (((1 / 2 : ℝ) * (3 : ℝ) ^ (n - 2)) ^ 2 / 12)
          ≤ (A i) ^ 2
            * ((windowHi x m (n - 2) i - windowLo x m (n - 2) i) ^ 2 / 12) := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        linarith only [he2]
      calc (A i) ^ 2 * ((3 : ℝ) ^ (n - 2)) ^ 2 / 48
          = (A i) ^ 2 * (((1 / 2 : ℝ) * (3 : ℝ) ^ (n - 2)) ^ 2 / 12) := by ring
        _ ≤ (A i) ^ 2
            * ((windowHi x m (n - 2) i - windowLo x m (n - 2) i) ^ 2 / 12) := hmul
    have hcen : 0 ≤ affineEval
        (oddAffineIntercept x m i A - vecDot (oddAffineSlope i A) x)
        (oddAffineSlope i A)
        (boxCenter (windowLo x m (n - 2)) (windowHi x m (n - 2))) ^ 2 :=
      sq_nonneg _
    linarith only [hsq, hterm, hgeom, hcen]
  have hq2 : (|A i| * delta) ^ 2
      ≤ (7 * tt * normalizedL2On (truncatedWindow x m (n - 2))
          (oddAffinePart x m i A)) ^ 2 := by
    have hql : (|A i| * delta) ^ 2
        = 48 * tt ^ 2 * ((A i) ^ 2 * ((3 : ℝ) ^ (n - 2)) ^ 2 / 48) := by
      calc (|A i| * delta) ^ 2 = |A i| ^ 2 * delta ^ 2 := by ring
        _ = (A i) ^ 2 * delta ^ 2 := by rw [sq_abs]
        _ = 48 * tt ^ 2 * ((A i) ^ 2 * ((3 : ℝ) ^ (n - 2)) ^ 2 / 48) := by
            rw [hdeltadef]
            ring
    have h48 : 48 * tt ^ 2 * ((A i) ^ 2 * ((3 : ℝ) ^ (n - 2)) ^ 2 / 48)
        ≤ 48 * tt ^ 2 * normalizedL2On (truncatedWindow x m (n - 2))
            (oddAffinePart x m i A) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq48 (by positivity)
    have h4849 : 48 * tt ^ 2 * normalizedL2On (truncatedWindow x m (n - 2))
          (oddAffinePart x m i A) ^ 2
        ≤ 49 * tt ^ 2 * normalizedL2On (truncatedWindow x m (n - 2))
            (oddAffinePart x m i A) ^ 2 := by
      have hp : 0 ≤ tt ^ 2 * normalizedL2On (truncatedWindow x m (n - 2))
          (oddAffinePart x m i A) ^ 2 := by positivity
      linarith only [hp]
    have hqr : (7 * tt * normalizedL2On (truncatedWindow x m (n - 2))
          (oddAffinePart x m i A)) ^ 2
        = 49 * tt ^ 2 * normalizedL2On (truncatedWindow x m (n - 2))
            (oddAffinePart x m i A) ^ 2 := by ring
    linarith only [hql, h48, h4849, hqr]
  have hq0 : 0 ≤ |A i| * delta := mul_nonneg (abs_nonneg _) hdelta0.le
  have hNnn : 0 ≤ normalizedL2On (truncatedWindow x m (n - 2))
      (oddAffinePart x m i A) := normalizedL2On_nonneg _ _
  have hr0 : 0 ≤ 7 * tt * normalizedL2On (truncatedWindow x m (n - 2))
      (oddAffinePart x m i A) := by positivity
  have h := Real.sqrt_le_sqrt hq2
  rwa [Real.sqrt_sq hq0, Real.sqrt_sq hr0] at h

/-- **The ramp on the corner slab is pointwise small**:
`‖oddᵢ‖_{L²(Q)} ≤ |Aᵢ|·delta`. -/
theorem normalizedL2On_oddRamp_cornerPairSlab_le {m k : ℤ} {x : Vec d} {i j : Fin d}
    {A : Vec d} {delta : ℝ} (hdelta0 : 0 < delta)
    (hQpos : 0 < (volume (coordBox (cornerPairSlabLo x m k i j delta)
      (cornerPairSlabHi x m k i j))).toReal) :
    normalizedL2On (coordBox (cornerPairSlabLo x m k i j delta)
      (cornerPairSlabHi x m k i j)) (oddAffinePart x m i A)
      ≤ |A i| * delta := by
  have hoddmem : MemLp (oddAffinePart x m i A) 2
      (volume.restrict (coordBox (cornerPairSlabLo x m k i j delta)
        (cornerPairSlabHi x m k i j))) := by
    rw [oddAffinePart]
    exact memLp_affineEval_coordBox _ _ _ _
  have hptw : ∀ y ∈ coordBox (cornerPairSlabLo x m k i j delta)
      (cornerPairSlabHi x m k i j),
      |oddAffinePart x m i A y| ≤ |A i| * delta := by
    intro y hy
    have hdep := (cornerPairSlab_depth hy).1
    rw [oddAffinePart_apply, abs_mul]
    have habs : |y i - (1 / 2 : ℝ) * (3 : ℝ) ^ m| ≤ delta := by
      rw [abs_le]
      constructor
      · linarith only [hdep.1]
      · linarith only [hdep.2, hdelta0]
    exact mul_le_mul_of_nonneg_left habs (abs_nonneg _)
  have h := normalizedL2On_mono_of_abs_le (measurableSet_coordBox _ _)
    hoddmem.integrable_sq
    (integrableOn_coordBox_of_continuous
      (continuous_const : Continuous fun _ : Vec d => ((|A i| * delta) ^ 2 : ℝ))
      _ _) hptw
  rwa [normalizedL2On_const_of_toReal_pos hQpos,
    abs_of_nonneg (mul_nonneg (abs_nonneg _) hdelta0.le)] at h

/-- **The ramp on the `j`-pushed corner slab is pointwise small.** -/
theorem normalizedL2On_oddRamp_cornerPairSlabPushed_le {m k : ℤ} {x : Vec d}
    {i j : Fin d} {A : Vec d} {delta : ℝ} (hij : i ≠ j) (hdelta0 : 0 < delta)
    (hD3pos : 0 < (volume (coordBox
      (fun l => cornerPairSlabLo x m k i j delta l
        - (delta • (basisVec j : Vec d)) l)
      (fun l => cornerPairSlabHi x m k i j l
        - (delta • (basisVec j : Vec d)) l))).toReal) :
    normalizedL2On (coordBox
      (fun l => cornerPairSlabLo x m k i j delta l
        - (delta • (basisVec j : Vec d)) l)
      (fun l => cornerPairSlabHi x m k i j l
        - (delta • (basisVec j : Vec d)) l)) (oddAffinePart x m i A)
      ≤ |A i| * delta := by
  have hD3depth : ∀ y ∈ coordBox
      (fun l => cornerPairSlabLo x m k i j delta l
        - (delta • (basisVec j : Vec d)) l)
      (fun l => cornerPairSlabHi x m k i j l
        - (delta • (basisVec j : Vec d)) l),
      (1 / 2 : ℝ) * (3 : ℝ) ^ m - delta < y i
        ∧ y i < (1 / 2 : ℝ) * (3 : ℝ) ^ m := by
    intro y hy
    have h := (mem_coordBox_iff.1 hy) i
    have hsm : (delta • (basisVec j : Vec d)) i = 0 := by
      rw [smul_basisVec_apply, ite_eq_right hij]
    have hlo : cornerPairSlabLo x m k i j delta i
        = (1 / 2 : ℝ) * (3 : ℝ) ^ m - delta := by
      rw [cornerPairSlabLo]
      rw [ite_eq_left (Or.inl rfl)]
    have hhi : cornerPairSlabHi x m k i j i = (1 / 2 : ℝ) * (3 : ℝ) ^ m := by
      rw [cornerPairSlabHi]
      rw [ite_eq_left (Or.inl rfl)]
    rw [hlo, hhi, hsm] at h
    constructor
    · linarith only [h.1]
    · linarith only [h.2]
  have hoddmem : MemLp (oddAffinePart x m i A) 2
      (volume.restrict (coordBox
        (fun l => cornerPairSlabLo x m k i j delta l
          - (delta • (basisVec j : Vec d)) l)
        (fun l => cornerPairSlabHi x m k i j l
          - (delta • (basisVec j : Vec d)) l))) := by
    rw [oddAffinePart]
    exact memLp_affineEval_coordBox _ _ _ _
  have hptw : ∀ y ∈ coordBox
      (fun l => cornerPairSlabLo x m k i j delta l
        - (delta • (basisVec j : Vec d)) l)
      (fun l => cornerPairSlabHi x m k i j l
        - (delta • (basisVec j : Vec d)) l),
      |oddAffinePart x m i A y| ≤ |A i| * delta := by
    intro y hy
    have hdep := hD3depth y hy
    rw [oddAffinePart_apply, abs_mul]
    have habs : |y i - (1 / 2 : ℝ) * (3 : ℝ) ^ m| ≤ delta := by
      rw [abs_le]
      constructor
      · linarith only [hdep.1]
      · linarith only [hdep.2, hdelta0]
    exact mul_le_mul_of_nonneg_left habs (abs_nonneg _)
  have h := normalizedL2On_mono_of_abs_le (measurableSet_coordBox _ _)
    hoddmem.integrable_sq
    (integrableOn_coordBox_of_continuous
      (continuous_const : Continuous fun _ : Vec d => ((|A i| * delta) ^ 2 : ℝ))
      _ _) hptw
  rwa [normalizedL2On_const_of_toReal_pos hD3pos,
    abs_of_nonneg (mul_nonneg (abs_nonneg _) hdelta0.le)] at h

/-- **The fold of the residual onto the window**:
`‖V − ℓ‖_{L²(R)} ≤ (2^d + Crefl)(E + P)` for a competitor odd under every met
reflection. -/
theorem normalizedL2On_reflected_residual_le {m n : ℤ} {x : Vec d}
    {V : Vec d → ℝ} {c : ℝ} {A : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) (hmn : n - 2 < m)
    (hupV : ∀ l : Fin d, MeetsUpperFace x m (n - 2) l → ∀ z : Vec d,
      V (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) l z) = -V z)
    (hlowV : ∀ l : Fin d, MeetsLowerFace x m (n - 2) l → ∀ z : Vec d,
      V (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) l z) = -V z)
    (hVR : MemLp V 2 (volume.restrict (reflectedWindow x m (n - 2)))) :
    normalizedL2On (reflectedWindow x m (n - 2))
      (fun y => V y - affineEval (c - vecDot A x) A y)
      ≤ ((2 : ℝ) ^ d + Real.sqrt ((24 * (d : ℝ) + 1) * 2 ^ 2 + 2))
          * (normalizedL2On (truncatedWindow x m (n - 2))
              (fun y => V y - affineEval (c - vecDot A x) A y)
            + normalizedL2On (truncatedWindow x m (n - 2))
                (affineEval (c - vecDot A x) A)) := by
  have hUR := truncatedWindow_subset_reflectedWindow x m (n - 2)
  have hlR : MemLp (affineEval (c - vecDot A x) A) 2
      (volume.restrict (reflectedWindow x m (n - 2))) :=
    memLp_affineEval_reflectedWindow x m (n - 2) _ _
  have hfU : MemLp (fun y => V y - affineEval (c - vecDot A x) A y) 2
      (volume.restrict (truncatedWindow x m (n - 2))) :=
    (hVR.sub hlR).mono_measure (Measure.restrict_mono hUR le_rfl)
  have hlU : MemLp (affineEval (c - vecDot A x) A) 2
      (volume.restrict (truncatedWindow x m (n - 2))) :=
    memLp_affineEval_truncatedWindow x m (n - 2) _ _
  have hE0 : 0 ≤ normalizedL2On (truncatedWindow x m (n - 2))
      (fun y => V y - affineEval (c - vecDot A x) A y) := normalizedL2On_nonneg _ _
  have hVsplit : normalizedL2On (truncatedWindow x m (n - 2)) V
      ≤ normalizedL2On (truncatedWindow x m (n - 2))
          (fun y => V y - affineEval (c - vecDot A x) A y)
        + normalizedL2On (truncatedWindow x m (n - 2))
            (affineEval (c - vecDot A x) A) := by
    have hcongr : normalizedL2On (truncatedWindow x m (n - 2)) V
        = normalizedL2On (truncatedWindow x m (n - 2))
          (fun y => (V y - affineEval (c - vecDot A x) A y)
            + affineEval (c - vecDot A x) A y) := by
      congr 1
      funext y
      ring
    rw [hcongr]
    exact normalizedL2On_add_le hfU hlU
  have hfold := normalizedL2On_reflectedWindow_le_of_faceOdd_forall hx hmn
    hupV hlowV hVR
  have hlRle := normalizedL2On_reflectedWindow_affineEval_le hx hmn
    (c - vecDot A x) A
  have hb1 := normalizedL2On_sub_le hVR hlR
  have hb5 : (2 : ℝ) ^ d * normalizedL2On (truncatedWindow x m (n - 2)) V
      ≤ (2 : ℝ) ^ d * (normalizedL2On (truncatedWindow x m (n - 2))
            (fun y => V y - affineEval (c - vecDot A x) A y)
          + normalizedL2On (truncatedWindow x m (n - 2))
              (affineEval (c - vecDot A x) A)) :=
    mul_le_mul_of_nonneg_left hVsplit (by positivity)
  have hb6 : Real.sqrt ((24 * (d : ℝ) + 1) * 2 ^ 2 + 2)
        * normalizedL2On (truncatedWindow x m (n - 2))
            (affineEval (c - vecDot A x) A)
      ≤ Real.sqrt ((24 * (d : ℝ) + 1) * 2 ^ 2 + 2)
          * (normalizedL2On (truncatedWindow x m (n - 2))
              (fun y => V y - affineEval (c - vecDot A x) A y)
            + normalizedL2On (truncatedWindow x m (n - 2))
                (affineEval (c - vecDot A x) A)) :=
    mul_le_mul_of_nonneg_left (by linarith only [hE0]) (Real.sqrt_nonneg _)
  have hb7 : ((2 : ℝ) ^ d + Real.sqrt ((24 * (d : ℝ) + 1) * 2 ^ 2 + 2))
        * (normalizedL2On (truncatedWindow x m (n - 2))
            (fun y => V y - affineEval (c - vecDot A x) A y)
          + normalizedL2On (truncatedWindow x m (n - 2))
              (affineEval (c - vecDot A x) A))
      = (2 : ℝ) ^ d * (normalizedL2On (truncatedWindow x m (n - 2))
            (fun y => V y - affineEval (c - vecDot A x) A y)
          + normalizedL2On (truncatedWindow x m (n - 2))
              (affineEval (c - vecDot A x) A))
        + Real.sqrt ((24 * (d : ℝ) + 1) * 2 ^ 2 + 2)
          * (normalizedL2On (truncatedWindow x m (n - 2))
              (fun y => V y - affineEval (c - vecDot A x) A y)
            + normalizedL2On (truncatedWindow x m (n - 2))
                (affineEval (c - vecDot A x) A)) := by
    ring
  linarith only [hb1, hfold, hb5, hb6, hlRle, hb7]

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
