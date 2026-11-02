/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Field.FreezingRadius

/-!
# CutoffLimit

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The full field as the limit of the normalized cutoff fields

The truncated coefficient field of ABK26 is `a_L = ν I + k_L` with
`k_L = Σ_{n ≤ L} j_n`, and the untruncated field is `a = ν I + k` with
`k(x) = Σ_{n ∈ ℤ} (j_n(x) - j_n(0))`.  The two are **not** related by a
convergent limit as they stand: the constant matrix `k_L(0) = Σ_{n ≤ L} j_n(0)`
grows with `L`.  The object that does converge is the cutoff field normalized at
the origin,

```text
  ã_L(x) = a_L(x) - k_L(0) = ν I + (k_L(x) - k_L(0)) ,
```

whose distance to `a` on a cube is exactly the ascending tail

```text
  a(x) - ã_L(x) = k(x) - (k_L(x) - k_L(0)) = Σ_{n > L} ( j_n(x) - j_n(0) ) .
```

Since `k_L(0)` is a constant skew matrix, `ã_L` and `a_L` have the same
divergence-form weak solutions, so nothing is lost by the normalization.

On the sharp carrier the ascending shell gradients obey
`‖∇ j_n‖_{L^∞(□_ℓ)} ≤ C 3^{(γ-1)n} (2 + |n| + |ℓ|)`, so the tail above is
bounded on `□_ℓ` by a geometric factor `3^{(γ-1)(L+1)}` times a weight linear in
`L`, and tends to zero as `L → ∞`.

## Main definitions

* `normalizedCutoff L ω` — the cutoff field normalized at the origin,
  `k_L - k_L(0)`.
* `normalizedCoefficientCutoff ν L ω` — the coefficient field `ã_L`.
* `largeScaleRatio γ` — the geometric ratio `3^{γ-1}`.
* `largeScaleTailSum γ` — the arithmetico-geometric constant
  `Σ_{r ≥ 0} (r+1) 3^{(γ-1)r} = (1 - 3^{γ-1})^{-2}`.
* `cutoffLimitGap d γ C ℓ L` — the explicit entrywise gap on `□_ℓ`.

## Main results

* `streamField_sub_normalizedCutoff_entry` — the exact relation above.
* `abs_streamField_sub_normalizedCutoff_le` — the geometric bound at a point of
  `□_ℓ`.
* `abs_streamCoefficient_sub_normalizedCoefficientCutoff_le_gap` — the same for
  the coefficient fields, in the entrywise supremum form the energy estimate
  consumes.
* `tendsto_cutoffLimitGap_atTop` — the gap tends to zero as `L → ∞`.

## References

* ABK26, the stream matrix and the truncated fields `a_L`; the proof of the
  homogenization theorem, where the equation is noted to be unchanged when `a_L`
  is replaced by `a_L` minus the average of `k_L - k_m` on the cube.
-/

namespace Algsuperdiff.Section5.Field

open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Stream
open Filter HCPolySupport MeasureTheory
open scoped Topology

noncomputable section

variable {d : ℕ} {gamma : ℝ}

/-! ## 1. The geometric ratio of the large-scale increments -/

/-- The geometric ratio `3^{γ-1}` of the ascending shell gradient rate. -/
def largeScaleRatio (gamma : ℝ) : ℝ := Real.rpow 3 (gamma - 1)

theorem largeScaleRatio_pos (gamma : ℝ) : 0 < largeScaleRatio gamma :=
  Real.rpow_pos_of_pos (by norm_num) _

theorem largeScaleRatio_lt_one {gamma : ℝ} (hgamma : gamma < 1) :
    largeScaleRatio gamma < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hgamma])

/-- The arithmetico-geometric constant `Σ_{r ≥ 0} (r+1) 3^{(γ-1)r}` of the
ascending tail. -/
def largeScaleTailSum (gamma : ℝ) : ℝ :=
  ∑' r : ℕ, ((r : ℝ) + 1) * largeScaleRatio gamma ^ r

theorem summable_largeScaleTail {gamma : ℝ} (hgamma : gamma < 1) :
    Summable fun r : ℕ => ((r : ℝ) + 1) * largeScaleRatio gamma ^ r :=
  Section4.Provider.Annular.summable_poly1_geom (largeScaleRatio_pos gamma).le
    (largeScaleRatio_lt_one hgamma)

theorem largeScaleTailSum_nonneg (gamma : ℝ) : 0 ≤ largeScaleTailSum gamma :=
  tsum_nonneg fun r =>
    mul_nonneg (by positivity) (pow_nonneg (largeScaleRatio_pos gamma).le r)

/-! ## 2. The normalized cutoff fields -/

/-- **The cutoff field normalized at the origin**, `k_L - k_L(0)`. -/
def normalizedCutoff (L : ℤ) (omega : CutoffSample d) (x : Vec d) : Mat d :=
  cutoff L omega x - cutoff L omega 0

@[simp]
theorem normalizedCutoff_apply_entry (L : ℤ) (omega : CutoffSample d) (x : Vec d)
    (i k : Fin d) :
    normalizedCutoff L omega x i k = cutoff L omega x i k - cutoff L omega 0 i k :=
  rfl

@[simp]
theorem normalizedCutoff_zero (L : ℤ) (omega : CutoffSample d) :
    normalizedCutoff L omega 0 = 0 := by
  simp only [normalizedCutoff, sub_self]

/-- The constant skew matrix by which the normalized cutoff differs from the
cutoff. -/
theorem cutoff_zero_skew (L : ℤ) (omega : CutoffSample d) :
    matTranspose (cutoff L omega 0) = -cutoff L omega 0 :=
  cutoff_skew L omega 0

theorem continuous_normalizedCutoff_entry (L : ℤ) (omega : CutoffSample d)
    (i k : Fin d) :
    Continuous fun x : Vec d => normalizedCutoff L omega x i k :=
  (continuous_cutoff_entry L omega i k).sub continuous_const

/-- **The normalized coefficient cutoff** `ã_L = a_L - k_L(0) = ν I + (k_L - k_L(0))`.
It has the same divergence-form weak solutions as `a_L`, because `k_L(0)` is a
constant skew matrix. -/
def normalizedCoefficientCutoff (nu : ℝ) (L : ℤ) (omega : CutoffSample d) :
    CoeffField d :=
  fun x => coefficientCutoff nu L omega x - cutoff L omega 0

theorem normalizedCoefficientCutoff_apply (nu : ℝ) (L : ℤ) (omega : CutoffSample d)
    (x : Vec d) :
    normalizedCoefficientCutoff nu L omega x =
      nu • (1 : Mat d) + normalizedCutoff L omega x := by
  simp only [normalizedCoefficientCutoff, coefficientCutoff_apply, normalizedCutoff]
  abel

theorem normalizedCoefficientCutoff_eq_sub (nu : ℝ) (L : ℤ) (omega : CutoffSample d)
    (x : Vec d) :
    normalizedCoefficientCutoff nu L omega x =
      (coefficientCutoff nu L omega).toCoeffField x - cutoff L omega 0 :=
  rfl

theorem symmPart_normalizedCoefficientCutoff (nu : ℝ) (L : ℤ)
    (omega : CutoffSample d) (x : Vec d) :
    symmPart (normalizedCoefficientCutoff nu L omega x) = nu • (1 : Mat d) := by
  rw [normalizedCoefficientCutoff_eq_sub,
    Section4.Provider.ExcessDecay.symmPart_sub_const_of_skew (cutoff_zero_skew L omega)]
  exact symmPart_coefficientCutoff nu L omega x

theorem continuous_normalizedCoefficientCutoff_sub (nu : ℝ) (L : ℤ)
    (omega : CutoffSample d) :
    Continuous fun x : Vec d =>
      normalizedCoefficientCutoff nu L omega x - nu • (1 : Mat d) := by
  refine continuous_pi fun i => continuous_pi fun k => ?_
  have hrw : (fun x : Vec d =>
      (normalizedCoefficientCutoff nu L omega x - nu • (1 : Mat d)) i k) =
      fun x : Vec d => normalizedCutoff L omega x i k := by
    funext x
    rw [normalizedCoefficientCutoff_apply]
    simp only [Matrix.sub_apply, Matrix.add_apply]
    ring
  rw [hrw]
  exact continuous_normalizedCutoff_entry L omega i k

/-! ## 3. The exact relation with the full field -/

/-- **The exact relation between the full field and its normalized cutoffs**:
their difference is the ascending tail `Σ_{n > L} (j_n(x) - j_n(0))`. -/
theorem streamField_sub_normalizedCutoff_entry (omega : FullSample d gamma) (L : ℤ)
    (x : Vec d) (i k : Fin d) :
    streamField omega x i k - normalizedCutoff L omega.1 x i k =
      ∑' r : ℕ, (omega.1.1 (L + 1 + (r : ℤ)) x i k -
        omega.1.1 (L + 1 + (r : ℤ)) 0 i k) := by
  rw [← streamField_sub_cutoff_sub_eq omega L x i k, normalizedCutoff_apply_entry]
  ring

/-- The same relation for the coefficient fields. -/
theorem streamCoefficient_sub_normalizedCoefficientCutoff_entry (nu : ℝ)
    (omega : FullSample d gamma) (L : ℤ) (x : Vec d) (i k : Fin d) :
    streamCoefficient nu omega x i k - normalizedCoefficientCutoff nu L omega.1 x i k =
      streamField omega x i k - normalizedCutoff L omega.1 x i k := by
  rw [normalizedCoefficientCutoff_apply]
  simp only [streamCoefficient, Matrix.add_apply]
  ring

/-! ## 4. The geometric rate on an origin cube -/

private theorem localCubeDerivNorm_le_gauge (ell n : ℤ) (omega : CutoffSample d) :
    localCubeDerivNorm ell (omega.1 n) ≤ sharpGradientGauge ell n omega := by
  rw [sharpGradientGauge_eq]
  exact le_add_of_nonneg_right
    (mul_nonneg (zpow_pos (by norm_num) _).le (localCubeSecondDerivNorm_nonneg _ _))

private theorem sharpTailWeight_shift_le (L ell : ℤ) (r : ℕ) :
    sharpTailWeight (L + 1 + (r : ℤ)) ell ≤
      3 * sharpTailWeight L ell * ((r : ℝ) + 1) := by
  have habs : (L + 1 + (r : ℤ)).natAbs ≤ L.natAbs + 1 + r := by
    have h1 := Int.natAbs_add_le L (1 : ℤ)
    have h2 := Int.natAbs_add_le (L + 1) (r : ℤ)
    simp only [Int.natAbs_one, Int.natAbs_natCast] at h1 h2
    omega
  unfold sharpTailWeight
  have habsR : ((L + 1 + (r : ℤ)).natAbs : ℝ) ≤ (L.natAbs : ℝ) + 1 + (r : ℝ) := by
    exact_mod_cast habs
  have hL0 : (0 : ℝ) ≤ (L.natAbs : ℝ) := Nat.cast_nonneg _
  have he0 : (0 : ℝ) ≤ (ell.natAbs : ℝ) := Nat.cast_nonneg _
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg _
  push_cast
  nlinarith only [habsR, hL0, he0, hr0]

private theorem rpow3_shift (gamma : ℝ) (L : ℤ) (r : ℕ) :
    Real.rpow 3 ((gamma - 1) * ((L + 1 + (r : ℤ) : ℤ) : ℝ)) =
      Real.rpow 3 ((gamma - 1) * ((L : ℝ) + 1)) * largeScaleRatio gamma ^ r := by
  rw [show (gamma - 1) * ((L + 1 + (r : ℤ) : ℤ) : ℝ) =
      (gamma - 1) * ((L : ℝ) + 1) + (gamma - 1) * (r : ℝ) by push_cast; ring,
    Section4.Provider.BoundsEaL.rpow3_add]
  congr 1
  exact Section4.Provider.BoundsEaL.rpow3_mul_natCast (gamma - 1) r

private theorem summable_cutoffLimitMajorant (d : ℕ) {gamma : ℝ} (hgamma : gamma < 1)
    (C : ℕ) (L ell : ℤ) (R : ℝ) :
    Summable fun r : ℕ =>
      3 * (d : ℝ) * (C : ℝ) * sharpTailWeight L ell * R *
        Real.rpow 3 ((gamma - 1) * ((L : ℝ) + 1)) *
          (((r : ℝ) + 1) * largeScaleRatio gamma ^ r) :=
  ((summable_largeScaleTail hgamma).mul_left
    (3 * (d : ℝ) * (C : ℝ) * sharpTailWeight L ell * R *
      Real.rpow 3 ((gamma - 1) * ((L : ℝ) + 1)))).congr fun r => by ring

/-- **The explicit geometric bound on the entrywise distance** between the full
field and its `L`-th normalized cutoff, at a point of the origin cube of scale
`ℓ`. -/
theorem abs_streamField_sub_normalizedCutoff_le {C : ℕ} (hgamma : gamma < 1)
    (omega : FullSample d gamma) (hC : SharpTailBounded gamma C omega.1)
    (ell L : ℤ) {x : Vec d} (hx : x ∈ openCubeSet (originCube d ell)) (i k : Fin d) :
    |streamField omega x i k - normalizedCutoff L omega.1 x i k| ≤
      3 * (d : ℝ) * (C : ℝ) * sharpTailWeight L ell * ‖x‖ *
        Real.rpow 3 ((gamma - 1) * ((L : ℝ) + 1)) * largeScaleTailSum gamma := by
  have hmaj : ∀ r : ℕ,
      |omega.1.1 (L + 1 + (r : ℤ)) x i k - omega.1.1 (L + 1 + (r : ℤ)) 0 i k| ≤
        3 * (d : ℝ) * (C : ℝ) * sharpTailWeight L ell * ‖x‖ *
          Real.rpow 3 ((gamma - 1) * ((L : ℝ) + 1)) *
            (((r : ℝ) + 1) * largeScaleRatio gamma ^ r) := by
    intro r
    have hmv := abs_entry_sub_le_of_mem_openOriginCube ell
      (omega.1.1 (L + 1 + (r : ℤ))) hx i k
    have hgrad := localCubeDerivNorm_le_gauge ell (L + 1 + (r : ℤ)) omega.1
    have hshell := (hC (L + 1 + (r : ℤ)) ell).2
    have hw := sharpTailWeight_shift_le L ell r
    calc
      |omega.1.1 (L + 1 + (r : ℤ)) x i k - omega.1.1 (L + 1 + (r : ℤ)) 0 i k| ≤
          (d : ℝ) * localCubeDerivNorm ell (omega.1.1 (L + 1 + (r : ℤ))) * ‖x‖ := hmv
      _ ≤ (d : ℝ) * sharpGradientGauge ell (L + 1 + (r : ℤ)) omega.1 * ‖x‖ := by gcongr
      _ ≤ (d : ℝ) * ((C : ℝ) *
            Real.rpow 3 ((gamma - 1) * ((L + 1 + (r : ℤ) : ℤ) : ℝ)) *
              sharpTailWeight (L + 1 + (r : ℤ)) ell) * ‖x‖ := by gcongr
      _ = (d : ℝ) * ((C : ℝ) *
            (Real.rpow 3 ((gamma - 1) * ((L : ℝ) + 1)) * largeScaleRatio gamma ^ r) *
              sharpTailWeight (L + 1 + (r : ℤ)) ell) * ‖x‖ := by
          rw [rpow3_shift]
      _ ≤ (d : ℝ) * ((C : ℝ) *
            (Real.rpow 3 ((gamma - 1) * ((L : ℝ) + 1)) * largeScaleRatio gamma ^ r) *
              (3 * sharpTailWeight L ell * ((r : ℝ) + 1))) * ‖x‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg d)
          refine mul_le_mul_of_nonneg_left hw ?_
          exact mul_nonneg (Nat.cast_nonneg C)
            (mul_nonneg (Real.rpow_pos_of_pos (by norm_num) _).le
              (pow_nonneg (largeScaleRatio_pos gamma).le _))
      _ = 3 * (d : ℝ) * (C : ℝ) * sharpTailWeight L ell * ‖x‖ *
            Real.rpow 3 ((gamma - 1) * ((L : ℝ) + 1)) *
              (((r : ℝ) + 1) * largeScaleRatio gamma ^ r) := by ring
  have hsummableAbs : Summable fun r : ℕ =>
      |omega.1.1 (L + 1 + (r : ℤ)) x i k - omega.1.1 (L + 1 + (r : ℤ)) 0 i k| :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hmaj
      (summable_cutoffLimitMajorant d hgamma C L ell ‖x‖)
  have hsummableNorm : Summable fun r : ℕ =>
      ‖omega.1.1 (L + 1 + (r : ℤ)) x i k - omega.1.1 (L + 1 + (r : ℤ)) 0 i k‖ := by
    simpa only [Real.norm_eq_abs] using hsummableAbs
  rw [streamField_sub_normalizedCutoff_entry omega L x i k]
  calc
    |∑' r : ℕ, (omega.1.1 (L + 1 + (r : ℤ)) x i k -
        omega.1.1 (L + 1 + (r : ℤ)) 0 i k)| ≤
        ∑' r : ℕ, |omega.1.1 (L + 1 + (r : ℤ)) x i k -
          omega.1.1 (L + 1 + (r : ℤ)) 0 i k| := by
      rw [← Real.norm_eq_abs]
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hsummableNorm
    _ ≤ ∑' r : ℕ, 3 * (d : ℝ) * (C : ℝ) * sharpTailWeight L ell * ‖x‖ *
          Real.rpow 3 ((gamma - 1) * ((L : ℝ) + 1)) *
            (((r : ℝ) + 1) * largeScaleRatio gamma ^ r) :=
        hsummableAbs.tsum_le_tsum hmaj (summable_cutoffLimitMajorant d hgamma C L ell ‖x‖)
    _ = 3 * (d : ℝ) * (C : ℝ) * sharpTailWeight L ell * ‖x‖ *
          Real.rpow 3 ((gamma - 1) * ((L : ℝ) + 1)) * largeScaleTailSum gamma := by
        unfold largeScaleTailSum
        rw [← tsum_mul_left]

/-! ## 5. The gap on a cube, and its vanishing as `L → ∞` -/

/-- **The explicit geometric gap** between the full field and its `L`-th
normalized cutoff, entrywise on the origin cube of scale `ℓ`.  When `γ < 1`,
its closed form is

```text
  3 d C (2 + |L| + |ℓ|) · (3^ℓ / 2) · 3^{(γ-1)(L+1)} · (1 - 3^{γ-1})^{-2} .
```
-/
def cutoffLimitGap (d : ℕ) (gamma : ℝ) (C : ℕ) (ell L : ℤ) : ℝ :=
  3 * (d : ℝ) * (C : ℝ) * sharpTailWeight L ell * ((1 / 2 : ℝ) * (3 : ℝ) ^ ell) *
    Real.rpow 3 ((gamma - 1) * ((L : ℝ) + 1)) * largeScaleTailSum gamma

theorem cutoffLimitGap_nonneg (d : ℕ) (gamma : ℝ) (C : ℕ) (ell L : ℤ) :
    0 ≤ cutoffLimitGap d gamma C ell L := by
  have hw : (0 : ℝ) ≤ sharpTailWeight L ell := (sharpTailWeight_pos L ell).le
  have hR : (0 : ℝ) ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ ell := by positivity
  have hrp : (0 : ℝ) ≤ Real.rpow 3 ((gamma - 1) * ((L : ℝ) + 1)) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hS : (0 : ℝ) ≤ largeScaleTailSum gamma := largeScaleTailSum_nonneg gamma
  have hdC : (0 : ℝ) ≤ 3 * (d : ℝ) * (C : ℝ) := by positivity
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hdC hw) hR) hrp) hS

/-- **The entrywise geometric bound on the origin cube of scale `ℓ`.** -/
theorem abs_streamField_sub_normalizedCutoff_le_gap {C : ℕ} (hgamma : gamma < 1)
    (omega : FullSample d gamma) (hC : SharpTailBounded gamma C omega.1)
    (ell L : ℤ) {x : Vec d} (hx : x ∈ openCubeSet (originCube d ell)) (i k : Fin d) :
    |streamField omega x i k - normalizedCutoff L omega.1 x i k| ≤
      cutoffLimitGap d gamma C ell L := by
  refine (abs_streamField_sub_normalizedCutoff_le hgamma omega hC ell L hx i k).trans ?_
  have hxnorm : ‖x‖ ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ ell := norm_le_of_mem_openOriginCube hx
  have hw : (0 : ℝ) ≤ sharpTailWeight L ell := (sharpTailWeight_pos L ell).le
  have hrp : (0 : ℝ) ≤ Real.rpow 3 ((gamma - 1) * ((L : ℝ) + 1)) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hS : (0 : ℝ) ≤ largeScaleTailSum gamma := largeScaleTailSum_nonneg gamma
  have hdC : (0 : ℝ) ≤ 3 * (d : ℝ) * (C : ℝ) := by positivity
  have hstep : 3 * (d : ℝ) * (C : ℝ) * sharpTailWeight L ell * ‖x‖ ≤
      3 * (d : ℝ) * (C : ℝ) * sharpTailWeight L ell * ((1 / 2 : ℝ) * (3 : ℝ) ^ ell) :=
    mul_le_mul_of_nonneg_left hxnorm (mul_nonneg hdC hw)
  unfold cutoffLimitGap
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hstep hrp) hS

/-- **The entrywise geometric bound for the coefficient fields.**  This is the
supremum distance `‖a - ã_L‖_∞` that the energy estimate consumes. -/
theorem abs_streamCoefficient_sub_normalizedCoefficientCutoff_le_gap (nu : ℝ)
    {C : ℕ} (hgamma : gamma < 1) (omega : FullSample d gamma)
    (hC : SharpTailBounded gamma C omega.1) (ell L : ℤ)
    {x : Vec d} (hx : x ∈ openCubeSet (originCube d ell)) (i k : Fin d) :
    |streamCoefficient nu omega x i k -
        normalizedCoefficientCutoff nu L omega.1 x i k| ≤
      cutoffLimitGap d gamma C ell L := by
  rw [streamCoefficient_sub_normalizedCoefficientCutoff_entry]
  exact abs_streamField_sub_normalizedCutoff_le_gap hgamma omega hC ell L hx i k

private theorem tendsto_weight_mul_ratio_pow {gamma : ℝ} (hgamma : gamma < 1) {a : ℝ}
    (ha : 0 ≤ a) :
    Tendsto (fun m : ℕ => (2 + (m : ℝ) + a) * largeScaleRatio gamma ^ m) atTop (𝓝 0) := by
  have hterm : Tendsto (fun m : ℕ => ((m : ℝ) + 1) * largeScaleRatio gamma ^ m)
      atTop (𝓝 0) := (summable_largeScaleTail hgamma).tendsto_atTop_zero
  have hlim : Tendsto
      (fun m : ℕ => (2 + a) * (((m : ℝ) + 1) * largeScaleRatio gamma ^ m))
      atTop (𝓝 0) := by
    simpa using hterm.const_mul (2 + a)
  refine squeeze_zero (fun m => ?_) (fun m => ?_) hlim
  · have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    exact mul_nonneg (by linarith only [hm, ha])
      (pow_nonneg (largeScaleRatio_pos gamma).le m)
  · have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hle : 2 + (m : ℝ) + a ≤ (2 + a) * ((m : ℝ) + 1) := by nlinarith only [hm, ha]
    have := mul_le_mul_of_nonneg_right hle
      (pow_nonneg (largeScaleRatio_pos gamma).le m)
    calc (2 + (m : ℝ) + a) * largeScaleRatio gamma ^ m
        ≤ (2 + a) * ((m : ℝ) + 1) * largeScaleRatio gamma ^ m := this
      _ = (2 + a) * (((m : ℝ) + 1) * largeScaleRatio gamma ^ m) := by ring

/-- **The gap vanishes as `L → ∞`**: on every fixed cube the full field is the
uniform limit of its normalized cutoffs, at the geometric rate `3^{(γ-1)L}`
times a weight linear in `L`. -/
theorem tendsto_cutoffLimitGap_atTop (d : ℕ) {gamma : ℝ} (hgamma : gamma < 1)
    (C : ℕ) (ell : ℤ) :
    Tendsto (fun L : ℤ => cutoffLimitGap d gamma C ell L) atTop (𝓝 0) := by
  have ha : (0 : ℝ) ≤ (ell.natAbs : ℝ) := Nat.cast_nonneg _
  have hnat := tendsto_weight_mul_ratio_pow hgamma ha
  set K : ℝ := 3 * (d : ℝ) * (C : ℝ) * ((1 / 2 : ℝ) * (3 : ℝ) ^ ell) *
    largeScaleRatio gamma * largeScaleTailSum gamma with hK_def
  have hKnat : Tendsto
      (fun m : ℕ => K * ((2 + (m : ℝ) + (ell.natAbs : ℝ)) * largeScaleRatio gamma ^ m))
      atTop (𝓝 0) := by
    simpa using hnat.const_mul K
  rw [Metric.tendsto_atTop] at hKnat ⊢
  intro eps heps
  obtain ⟨N, hN⟩ := hKnat eps heps
  refine ⟨max (N : ℤ) 0, fun L hL => ?_⟩
  have hLN : (N : ℤ) ≤ L := le_trans (le_max_left _ _) hL
  have hL0 : (0 : ℤ) ≤ L := le_trans (le_max_right _ _) hL
  have hidx : N ≤ L.toNat := by omega
  have hw : sharpTailWeight L ell = 2 + (L.toNat : ℝ) + (ell.natAbs : ℝ) := by
    have hnatAbs : L.natAbs = L.toNat := by omega
    unfold sharpTailWeight
    rw [hnatAbs]
    push_cast
    ring
  have hLcast : (L : ℝ) = (L.toNat : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) (Int.toNat_of_nonneg hL0).symm
  have hrp : Real.rpow 3 ((gamma - 1) * ((L : ℝ) + 1)) =
      largeScaleRatio gamma * largeScaleRatio gamma ^ L.toNat := by
    rw [hLcast, show (gamma - 1) * ((L.toNat : ℝ) + 1) =
        (gamma - 1) + (gamma - 1) * (L.toNat : ℝ) by ring,
      Section4.Provider.BoundsEaL.rpow3_add,
      Section4.Provider.BoundsEaL.rpow3_mul_natCast]
    rfl
  have hgap : cutoffLimitGap d gamma C ell L =
      K * ((2 + (L.toNat : ℝ) + (ell.natAbs : ℝ)) * largeScaleRatio gamma ^ L.toNat) := by
    unfold cutoffLimitGap
    rw [hw, hrp, hK_def]
    ring
  rw [hgap]
  exact hN _ hidx

end

end Algsuperdiff.Section5.Field
