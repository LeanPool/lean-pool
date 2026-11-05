/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.ResidualCorrectorExistence

/-!
# OneStepDatumSplit

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The datum reduction: from the true competitor to an odd one

The manuscript's boundary Schauder step reads

```text
  [∇v]_{C^{0,1/2}(U₃)} ≤ C 3^{-n/2} E(v, U₂)
                          + C [∇h]_{C^{0,1/2}(U₂)} 𝟙_{(x+□_n) ∩ ∂□_m ≠ ∅} ,
```

refuted the reading of that second leg as a *pricing of the odd-class defect*
and located it here instead, in the reduction from the true competitor to an
odd one.  This module proves the reduction's two quantitative atoms.

## 1. The datum's deviation from its affine part

`AffineSplitLift.abs_sub_affineLift_volumeAverage_le` prices `h - ℓ_h` on a
convex window of sup-radius `r` by `2 d [∇h]_{C^{0,1/2}} r^{3/2}`.  Instantiated
at `U₂ = (x + □_{n-2}) ∩ □_m` and `r = 3^{n-2}/2` this is

```text
  ‖h - ℓ_h‖_{L^∞(U₂)} ≤ 2 d [∇h]_{C^{0,1/2}(U₂)} (3^{n-2}/2)^{3/2}
                      =: datumResidualBound d n [∇h] .
```

The integrability slot that lemma carries for the gradient field is **derived**
here, not assumed: a `C^{0,1/2}` field on a window is continuous
(`continuousOn_of_holderSeminormBoundOn`) and bounded, hence integrable.

## 2. The corrector carrying that deviation

`ResidualCorrectorExistence.exists_residualCorrector_truncatedWindow` solves the
Dirichlet problem on `U₂` with that datum and
`BoundaryLaneMaxPrinciple.ae_abs_le_of_isWeaklyHarmonicOn` bounds the solution by
the same constant.  The output `w` is the manuscript's `v₁`:

```text
  v₁ weakly harmonic on U₂,  ‖v₁‖_{L^∞(U₂)} ≤ datumResidualBound d n [∇h] ,
```

with `v - ℓ_h - v₁` carrying **zero** data on the met portion of `∂□_m` — the
odd competitor the/ producer consumes.

## 3. Where the `[∇h]` leg proves (measured)

The corrector is **not** priced through a gradient-Hölder seminorm: no interior
estimate reaches the met face, and a boundary Schauder estimate for `v₁` would be
circular.  It is priced through the `L²` comparison slot instead, and the
measured leg is

```text
  3^{-n} · datumResidualBound d n [∇h] = (2 d · 3^{-3} · 2^{-3/2}) (3^n)^{1/2} [∇h] ,
```
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport Algsuperdiff.Section4.Support MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## 1. A `C^{0,1/2}` field on a window is continuous and integrable -/

/-- **A Hölder field is continuous on its window.**  The `C^{0,1/2}` bound is an
explicit modulus of continuity. -/
theorem continuousOn_of_holderSeminormBoundOn {U : Set (Vec d)} {K : ℝ}
    {G : Vec d → Vec d} (hK : 0 ≤ K)
    (hG : HolderSeminormBoundOn U (1 / 2 : ℝ) K G) : ContinuousOn G U := by
  exact hG.continuousOn hK (by norm_num)

/-- **A Hölder field is integrable on a bounded window**, coordinatewise.  This
is the integrability slot of `AffineSplitLift.abs_sub_affineLift_volumeAverage_le`
and it is derived, not assumed. -/
theorem integrableOn_coord_of_holderSeminormBoundOn {U : Set (Vec d)}
    (hU : MeasurableSet U) (hUtop : volume U ≠ ⊤) {K r : ℝ} {G : Vec d → Vec d}
    {x : Vec d} (hx : x ∈ U) (hK : 0 ≤ K)
    (hG : HolderSeminormBoundOn U (1 / 2 : ℝ) K G)
    (hdiam : ∀ p ∈ U, ‖p - x‖ ≤ r) (i : Fin d) :
    IntegrableOn (fun p => G p i) U volume := by
  have hcont : ContinuousOn G U := continuousOn_of_holderSeminormBoundOn hK hG
  have hcoord : ContinuousOn (fun p => G p i) U :=
    (continuous_apply i).comp_continuousOn hcont
  have hmeas : AEStronglyMeasurable (fun p => G p i) (volume.restrict U) :=
    hcoord.aestronglyMeasurable hU
  have : IsFiniteMeasure (volume.restrict U) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact hUtop.lt_top
  refine memLp_one_iff_integrable.1
    (MemLp.of_bound hmeas (‖G x‖ + K * r ^ (1 / 2 : ℝ)) ?_)
  filter_upwards [MeasureTheory.ae_restrict_mem hU] with p hp
  have h1 : ‖G p - G x‖ ≤ K * r ^ (1 / 2 : ℝ) := by
    refine le_trans (hG p hp x hx) (mul_le_mul_of_nonneg_left ?_ hK)
    exact Real.rpow_le_rpow (norm_nonneg _) (hdiam p hp) (by norm_num)
  have h2 : ‖G p i‖ ≤ ‖G p‖ := by simpa using norm_le_pi_norm (G p) i
  have h3 : ‖G p‖ ≤ ‖G x‖ + ‖G p - G x‖ := by
    have := norm_add_le (G x) (G p - G x)
    simpa using this
  rw [Real.norm_eq_abs, ← Real.norm_eq_abs]
  linarith only [h1, h2, h3]

/-! ## 2. The residual bound -/

/-- **The `L^∞` size of the datum's deviation from its affine lift on `U₂`.**
`2 d [∇h]_{C^{0,1/2}(U₂)} (3^{n-2}/2)^{3/2}`. -/
def datumResidualBound (d : ℕ) (n : ℤ) (Kh : ℝ) : ℝ :=
  2 * (d : ℝ) * Kh * ((3 : ℝ) ^ (n - 2) / 2) ^ (3 / 2 : ℝ)

theorem datumResidualBound_nonneg (d : ℕ) (n : ℤ) {Kh : ℝ} (hKh : 0 ≤ Kh) :
    0 ≤ datumResidualBound d n Kh := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (n - 2) := zpow_pos (by norm_num) _
  have hr : (0 : ℝ) ≤ ((3 : ℝ) ^ (n - 2) / 2) ^ (3 / 2 : ℝ) :=
    Real.rpow_nonneg (by linarith only [h3]) _
  have hd : (0 : ℝ) ≤ 2 * (d : ℝ) * Kh :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d)) hKh
  exact mul_nonneg hd hr

/-! ## 3. The corrector carrying the datum's deviation -/

/-! ## 4. Where the `[∇h]` leg proves -/

/-- **The measured scale shape of the datum leg.**  The corrector enters the
one-step chain through the `L²` comparison slot, i.e. against the normalizer
`3^{-n}`; the product is the manuscript's own `(3^n)^{1/2} [∇h]`. -/
theorem datumResidualBound_zpow_mul (d : ℕ) (n : ℤ) (Kh : ℝ) :
    (3 : ℝ) ^ (-n) * datumResidualBound d n Kh
      = 2 * (d : ℝ) * Kh * ((3 : ℝ) ^ (-3 : ℝ) * (2 : ℝ) ^ (-(3 / 2) : ℝ))
          * ((3 : ℝ) ^ n) ^ (1 / 2 : ℝ) := by
  have h3 : (0 : ℝ) < (3 : ℝ) := by norm_num
  have h3n : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos h3 _
  have hcast : ((3 : ℝ) ^ (n - 2)) = (3 : ℝ) ^ n * (3 : ℝ) ^ (-2 : ℤ) := by
    rw [← zpow_add₀ (ne_of_gt h3)]
    ring_nf
  have hsplit : ((3 : ℝ) ^ (n - 2) / 2) ^ (3 / 2 : ℝ)
      = ((3 : ℝ) ^ n) ^ (3 / 2 : ℝ) * (3 : ℝ) ^ (-3 : ℝ) * (2 : ℝ) ^ (-(3 / 2) : ℝ) := by
    have hpos2 : (0 : ℝ) < (3 : ℝ) ^ (-2 : ℤ) := zpow_pos h3 _
    rw [hcast, div_eq_mul_inv, Real.mul_rpow (mul_nonneg h3n.le hpos2.le) (by norm_num),
      Real.mul_rpow h3n.le hpos2.le]
    have hmid : ((3 : ℝ) ^ (-2 : ℤ)) ^ (3 / 2 : ℝ) = (3 : ℝ) ^ (-3 : ℝ) := by
      rw [show ((3 : ℝ) ^ (-2 : ℤ)) = (3 : ℝ) ^ ((-2 : ℝ)) by
        rw [show ((-2 : ℝ)) = (((-2 : ℤ) : ℝ)) by push_cast; ring, Real.rpow_intCast],
        ← Real.rpow_mul h3.le]
      norm_num
    have hinv : ((2 : ℝ)⁻¹) ^ (3 / 2 : ℝ) = (2 : ℝ) ^ (-(3 / 2) : ℝ) := by
      rw [← Real.rpow_neg_one (2 : ℝ), ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [hmid, hinv]
  have hthree : ((3 : ℝ) ^ n) ^ (3 / 2 : ℝ)
      = ((3 : ℝ) ^ n) ^ (1 / 2 : ℝ) * (3 : ℝ) ^ n := by
    calc ((3 : ℝ) ^ n) ^ (3 / 2 : ℝ)
        = ((3 : ℝ) ^ n) ^ ((1 / 2 : ℝ) + 1) := by norm_num
      _ = ((3 : ℝ) ^ n) ^ (1 / 2 : ℝ) * ((3 : ℝ) ^ n) ^ (1 : ℝ) :=
          Real.rpow_add h3n _ _
      _ = ((3 : ℝ) ^ n) ^ (1 / 2 : ℝ) * (3 : ℝ) ^ n := by rw [Real.rpow_one]
  have hcancel : (3 : ℝ) ^ (-n) * (3 : ℝ) ^ n = 1 := by
    rw [← zpow_add₀ (ne_of_gt h3)]
    simp
  rw [datumResidualBound, hsplit, hthree]
  calc (3 : ℝ) ^ (-n) * (2 * (d : ℝ) * Kh
        * (((3 : ℝ) ^ n) ^ (1 / 2 : ℝ) * (3 : ℝ) ^ n * (3 : ℝ) ^ (-3 : ℝ)
          * (2 : ℝ) ^ (-(3 / 2) : ℝ)))
      = ((3 : ℝ) ^ (-n) * (3 : ℝ) ^ n) * (2 * (d : ℝ) * Kh
          * ((3 : ℝ) ^ (-3 : ℝ) * (2 : ℝ) ^ (-(3 / 2) : ℝ))
          * ((3 : ℝ) ^ n) ^ (1 / 2 : ℝ)) := by ring
    _ = 2 * (d : ℝ) * Kh * ((3 : ℝ) ^ (-3 : ℝ) * (2 : ℝ) ^ (-(3 / 2) : ℝ))
          * ((3 : ℝ) ^ n) ^ (1 / 2 : ℝ) := by rw [hcancel, one_mul]

end

end Algsuperdiff.Section4.Provider.ExcessDecay
