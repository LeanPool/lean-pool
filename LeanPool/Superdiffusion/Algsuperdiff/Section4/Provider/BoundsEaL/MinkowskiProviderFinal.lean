/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.BoundsEaL.MinkowskiTransport
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.BoundsEaL.MinkowskiScaleClosure
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.BoundsEaL.SigmaBarLandmark

/-!
# MinkowskiProviderFinal

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `bounds_mathcal_E_aL`: the provider-final at the corrected ordering

## What this module delivers

Composing

* `MinkowskiScaleClosure.minkowskiScaleSum_total_le` and
  `sqrt_minkowskiScaleSum_le` (the three per-scale shapes evaluated and rooted),
* `SigmaBarLandmark.exists_pos_forall_model_of_two_le_dimension` (the `2 ≤ d`
  binder removal, which is what lets the provider match the anchor's binder
  order `∃ C` before `∀ M`),

gives the anchor's frozen block from a single per-cube `L^{p/2}`-moment
obligation in the named shape `minkowskiScaleMajorant`.

## The remaining obligation

`hcube` is the ONLY hypothesis beyond the anchor's own binders.  It asks, for
every positive Step-3 display constant, for a constant `K` such that the
`p/2`-th moment of the `L`-free Step-3 majorant at a descendant cube of scale
`n − l` is at most

```
K p ( γ s^{-2} + γ((m−n)+l) 3^{2γ((m−n)+l)} + γ 3^{2γ((m−n)+l)} )
```

raised to the `p/2`.  The obligation is stated at an arbitrary display constant
because `step3DisplayAt` is linear in that constant and every proved per-cube
moment is already stated at an arbitrary one.

## References

* ABK26, `l.bounds.mathcal.E.aL`, Step 5.
-/

namespace Algsuperdiff.Section4.Provider.BoundsEaL

open HCPolySupport HCPolySupport.Book MeasureTheory
open Algsuperdiff.Section3
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The per-scale majorant of the obligation -/

/-- **The three per-scale shapes, named.**  `K p γ (s^{-2} + (D+l)3^{2γ(D+l)} +
3^{2γ(D+l)})`, with `D = m − n` and `l` the descendant depth below `n`. -/
def minkowskiScaleMajorant (K p gam s D : ℝ) (l : ℕ) : ℝ :=
  K * p * (gam * (s⁻¹ * s⁻¹) +
    (gam * (D + (l : ℝ)) * Real.rpow 3 (2 * gam * (D + (l : ℝ))) +
      gam * Real.rpow 3 (2 * gam * (D + (l : ℝ)))))

theorem minkowskiScaleMajorant_nonneg {K p gam s D : ℝ} (hK : 0 ≤ K) (hp : 0 ≤ p)
    (hgam : 0 ≤ gam) (hD : 0 ≤ D) (l : ℕ) : 0 ≤ minkowskiScaleMajorant K p gam s D l := by
  have hl0 : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
  have h1 : (0 : ℝ) ≤ gam * (s⁻¹ * s⁻¹) := mul_nonneg hgam (mul_self_nonneg _)
  have h2 : (0 : ℝ) ≤ gam * (D + (l : ℝ)) * Real.rpow 3 (2 * gam * (D + (l : ℝ))) :=
    mul_nonneg (mul_nonneg hgam (by linarith only [hD, hl0]))
      (Real.rpow_nonneg (by norm_num) _)
  have h3 : (0 : ℝ) ≤ gam * Real.rpow 3 (2 * gam * (D + (l : ℝ))) :=
    mul_nonneg hgam (Real.rpow_nonneg (by norm_num) _)
  exact mul_nonneg (mul_nonneg hK hp) (by linarith only [h1, h2, h3])

/-- The prefix spelling `Real.rpow x y` and the notation `x ^ y` are the same
term.  Local re-derivation of `Step5GeometricClosure`'s `private
rpowBridge`. -/
private theorem rpowBridgeFinal (x y : ℝ) : Real.rpow x y = x ^ y := rfl

/-- The transport's per-scale term IS the closure's, at the named majorant. -/
private theorem scaleTermBridge {s : ℝ} (K p gam D : ℝ) (l : ℕ) :
    Ch02.geometricDiscount s 2 *
        (Real.rpow 3 (-s * (l : ℝ)) * minkowskiScaleMajorant K p gam s D l) =
      (1 - (3 : ℝ) ^ (-(2 * s))) * ((3 : ℝ) ^ (-(s * (l : ℝ))) *
        (K * p * (gam * (s⁻¹ * s⁻¹) +
          (gam * (D + (l : ℝ)) * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ))) +
            gam * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ))))))) := by
  have h1 : Ch02.geometricDiscount s 2 = 1 - (3 : ℝ) ^ (-(2 * s)) := by
    show 1 - Real.rpow 3 (-s * 2) = 1 - (3 : ℝ) ^ (-(2 * s))
    rw [show -s * 2 = -(2 * s) from by ring, rpowBridgeFinal]
  have h2 : Real.rpow 3 (-s * (l : ℝ)) = (3 : ℝ) ^ (-(s * (l : ℝ))) := by
    rw [rpowBridgeFinal, show -s * (l : ℝ) = -(s * (l : ℝ)) from by ring]
  rw [h1, h2, minkowskiScaleMajorant]
  simp only [rpowBridgeFinal]

/-- Summability of the named per-scale majorant against the geometric weight. -/
private theorem summableScaleMajorant {K p gam s D : ℝ} (hs : 0 < s) (hgam : 0 ≤ gam)
    (h4gam : 4 * gam ≤ s) (hD : 0 ≤ D) (hgamD : gam * D ≤ 1) :
    Summable fun l : ℕ => (3 : ℝ) ^ (-(s * (l : ℝ))) *
      (K * p * (gam * (s⁻¹ * s⁻¹) +
        (gam * (D + (l : ℝ)) * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ))) +
          gam * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ)))))) := by
  have h1 := summable_constScaleTerm (s := s) (c := gam * (s⁻¹ * s⁻¹)) hs
  have h2 := summable_linearScaleTerm (s := s) (gam := gam) (D := D) hs hgam h4gam hD hgamD
  have h3 := summable_flatScaleTerm (s := s) (gam := gam) (D := D) hs hgam h4gam hgamD
  refine ((h1.add (h2.add h3)).mul_left (K * p)).congr fun l => ?_
  ring

/-- **The transport's scale sum, closed at the named majorant** (in `ℝ≥0∞`). -/
theorem tsum_ofReal_scaleMajorant_le {K p gam s D : ℝ} (hK : 0 ≤ K) (hp : 0 ≤ p)
    (hs : 0 < s) (hs1 : s ≤ 1) (hgam : 0 ≤ gam) (h4gam : 4 * gam ≤ s) (hD : 0 ≤ D)
    (hgamD : gam * D ≤ 1) :
    (∑' l : ℕ, ENNReal.ofReal (Ch02.geometricDiscount s 2 *
        (Real.rpow 3 (-s * (l : ℝ)) * minkowskiScaleMajorant K p gam s D l))) ≤
      ENNReal.ofReal (K * p * (gam * (2 * (s⁻¹ * s⁻¹) + 36 * D + 180 / s))) := by
  have hcss0 : (0 : ℝ) ≤ 1 - (3 : ℝ) ^ (-(2 * s)) := by
    have h1 : (3 : ℝ) ^ (-(2 * s)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith only [hs])
    linarith only [h1]
  have hsum := summableScaleMajorant (K := K) (p := p) hs hgam h4gam hD hgamD
  have hsumScaled : Summable fun l : ℕ => (1 - (3 : ℝ) ^ (-(2 * s))) *
      ((3 : ℝ) ^ (-(s * (l : ℝ))) *
        (K * p * (gam * (s⁻¹ * s⁻¹) +
          (gam * (D + (l : ℝ)) * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ))) +
            gam * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ))))))) := hsum.mul_left _
  have hnn : ∀ l : ℕ, (0 : ℝ) ≤ (1 - (3 : ℝ) ^ (-(2 * s))) *
      ((3 : ℝ) ^ (-(s * (l : ℝ))) *
        (K * p * (gam * (s⁻¹ * s⁻¹) +
          (gam * (D + (l : ℝ)) * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ))) +
            gam * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ))))))) := by
    intro l
    have hl0 : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
    have h1 : (0 : ℝ) ≤ gam * (s⁻¹ * s⁻¹) := mul_nonneg hgam (mul_self_nonneg _)
    have h2 : (0 : ℝ) ≤ gam * (D + (l : ℝ)) * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ))) :=
      mul_nonneg (mul_nonneg hgam (by linarith only [hD, hl0]))
        (Real.rpow_nonneg (by norm_num) _)
    have h3 : (0 : ℝ) ≤ gam * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ))) :=
      mul_nonneg hgam (Real.rpow_nonneg (by norm_num) _)
    refine mul_nonneg hcss0 (mul_nonneg (Real.rpow_nonneg (by norm_num) _) ?_)
    exact mul_nonneg (mul_nonneg hK hp) (by linarith only [h1, h2, h3])
  have hbound : (∑' l : ℕ, (1 - (3 : ℝ) ^ (-(2 * s))) *
      ((3 : ℝ) ^ (-(s * (l : ℝ))) *
        (K * p * (gam * (s⁻¹ * s⁻¹) +
          (gam * (D + (l : ℝ)) * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ))) +
            gam * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ)))))))) ≤
      K * p * (gam * (2 * (s⁻¹ * s⁻¹) + 36 * D + 180 / s)) := by
    have hcong : ∀ l : ℕ, (1 - (3 : ℝ) ^ (-(2 * s))) *
        ((3 : ℝ) ^ (-(s * (l : ℝ))) *
          (K * p * (gam * (s⁻¹ * s⁻¹) +
            (gam * (D + (l : ℝ)) * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ))) +
              gam * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ))))))) =
        K * p * ((1 - (3 : ℝ) ^ (-(2 * s))) *
          ((3 : ℝ) ^ (-(s * (l : ℝ))) *
            (gam * (s⁻¹ * s⁻¹) +
              (gam * (D + (l : ℝ)) * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ))) +
                gam * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ))))))) := by
      intro l
      ring
    rw [tsum_congr hcong, tsum_mul_left]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hK hp)
    have hcore := minkowskiScaleSum_total_le (s := s) (gam := gam) (D := D)
      (A := s⁻¹ * s⁻¹) hs hs1 hgam h4gam hD hgamD (mul_self_nonneg _)
    rw [← tsum_mul_left] at hcore
    exact hcore
  calc (∑' l : ℕ, ENNReal.ofReal (Ch02.geometricDiscount s 2 *
        (Real.rpow 3 (-s * (l : ℝ)) * minkowskiScaleMajorant K p gam s D l)))
      = ∑' l : ℕ, ENNReal.ofReal ((1 - (3 : ℝ) ^ (-(2 * s))) *
          ((3 : ℝ) ^ (-(s * (l : ℝ))) *
            (K * p * (gam * (s⁻¹ * s⁻¹) +
              (gam * (D + (l : ℝ)) * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ))) +
                gam * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ)))))))) :=
        tsum_congr fun l => congrArg ENNReal.ofReal (scaleTermBridge K p gam D l)
    _ = ENNReal.ofReal (∑' l : ℕ, (1 - (3 : ℝ) ^ (-(2 * s))) *
          ((3 : ℝ) ^ (-(s * (l : ℝ))) *
            (K * p * (gam * (s⁻¹ * s⁻¹) +
              (gam * (D + (l : ℝ)) * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ))) +
                gam * (3 : ℝ) ^ (2 * gam * (D + (l : ℝ))))))))  :=
        (ENNReal.ofReal_tsum_of_nonneg hnn hsumScaled).symm
    _ ≤ ENNReal.ofReal (K * p * (gam * (2 * (s⁻¹ * s⁻¹) + 36 * D + 180 / s))) :=
        ENNReal.ofReal_le_ofReal hbound

end

/-! ## 2. The provider-final -/

/-- **The provider-final, at the corrected ordering.**

Everything outside `hcube` is proved here: the `2 ≤ d` binder removal, the
window arithmetic (`γ ≤ 1/8`, `4γ ≤ s`, `γ(m−n) ≤ 1` -- all from the anchor's
own `γ ≤ C^{-10}`, `s ≥ C²√γ` and `m ≤ n + γ^{-1}`), the Minkowski-ordered
transport, the three-shape scale sum, and the square root against the anchor's
printed scalar. -/
theorem bounds_mathcal_E_aL_provider_of_perCubeMoments
    (d : ℕ) (cstar : ℝ) (_hcstar : 0 < cstar)
    (hcube : ∀ _hd : 2 ≤ d, letI : NeZero d := ⟨by omega⟩
      ∀ Cd : ℝ, 0 < Cd → ∃ K : ℝ, 0 < K ∧
        ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ (K⁻¹) ^ (10 : ℕ) →
          ∀ m n : ℤ, n ≤ m → (m : ℝ) ≤ (n : ℝ) + M.gamma⁻¹ →
            ∀ s : ℝ, s ∈ Set.Icc (K ^ (2 : ℕ) * Real.sqrt M.gamma) (1 / 4) →
              ∀ p : ℝ, p ∈ Set.Icc (2 * (d : ℝ) * s⁻¹) (K⁻¹ * M.gamma⁻¹ * s) →
                ∀ (l : ℕ) (R : TriadicCube d),
                  R ∈ descendantsAtScale (originCube d m) (n - (l : ℤ)) →
                  (∫⁻ omega, ENNReal.ofReal (lFreeStep3Majorant Cd M m s
                        (lFreeGradSlot m (tailSeriesGauge m))
                        (lFreeValueSlot m (tailSeriesGauge m)) R omega) ^ (p / 2)
                      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
                    ENNReal.ofReal (minkowskiScaleMajorant K p M.gamma s
                      ((m : ℝ) - (n : ℝ)) l) ^ (p / 2)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar →
        M.gamma ≤ (C⁻¹) ^ (10 : ℕ) →
        ∀ m n : ℤ, n ≤ m → (m : ℝ) ≤ (n : ℝ) + M.gamma⁻¹ →
          ∀ s : ℝ, s ∈ Set.Icc (C ^ (2 : ℕ) * Real.sqrt M.gamma) (1 / 4) →
            ∀ hs : 0 < s,
              ∀ p : ℝ, p ∈ Set.Icc (2 * (d : ℝ) * s⁻¹) (C⁻¹ * M.gamma⁻¹ * s) →
                (∫⁻ omega,
                    Algsuperdiff.Section4.Support.fluxCorrectedTwoScaleErrorObservableSup
                        M m n ⟨s, hs⟩ omega ^ p
                      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
                  ENNReal.ofReal
                      (C * Real.rpow (3 : ℝ) (1 / 2 * s * ((m : ℝ) - (n : ℝ))) *
                        Real.sqrt p *
                        (s⁻¹ + Real.sqrt ((m : ℝ) - (n : ℝ))) *
                        Real.sqrt M.gamma) ^ p := by
  refine exists_pos_forall_model_of_two_le_dimension (fun hd => ?_)
  have : NeZero d := ⟨by omega⟩
  obtain ⟨C0, hC0, htrans⟩ := lintegral_observableSup_rpow_le_minkowskiScaleSum d hd
  obtain ⟨K, hK, hmoment⟩ := hcube hd C0 hC0
  have hsqK : (0 : ℝ) ≤ Real.sqrt K := Real.sqrt_nonneg K
  refine ⟨max (max K 2) (16 * Real.sqrt K), ?_, ?_⟩
  · exact lt_of_lt_of_le (by norm_num) (le_trans (le_max_right K 2) (le_max_left _ _))
  intro M hcs hreg m n hnm hwin s hsmem hs p hpmem
  set C : ℝ := max (max K 2) (16 * Real.sqrt K) with hCdef
  have hKC : K ≤ C := le_trans (le_max_left K 2) (le_max_left _ _)
  have h2C : (2 : ℝ) ≤ C := le_trans (le_max_right K 2) (le_max_left _ _)
  have h16C : 16 * Real.sqrt K ≤ C := le_max_right _ _
  have hC0' : (0 : ℝ) < C := lt_of_lt_of_le (by norm_num) h2C
  have hgam0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hs1 : s ≤ 1 / 4 := hsmem.2
  have hs1' : s ≤ 1 := le_trans hs1 (by norm_num)
  have hsinv0 : (0 : ℝ) ≤ s⁻¹ := (inv_pos.mpr hs).le
  have hp1 : 2 * (d : ℝ) * s⁻¹ ≤ p := hpmem.1
  have hd0 : (0 : ℝ) < (d : ℝ) := by
    have hdn : (0 : ℕ) < d := by omega
    exact_mod_cast hdn
  have hp0 : (0 : ℝ) < p :=
    lt_of_lt_of_le (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hd0) (inv_pos.mpr hs)) hp1
  -- the window arithmetic
  have hinvle : C⁻¹ ≤ K⁻¹ := inv_anti₀ hK hKC
  have hregK : M.gamma ≤ (K⁻¹) ^ (10 : ℕ) :=
    le_trans hreg (pow_le_pow_left₀ (inv_pos.mpr hC0').le hinvle 10)
  have hgam18 : M.gamma ≤ 1 / 8 := by
    have hhalf : C⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h2C
    have hstep : (C⁻¹) ^ (10 : ℕ) ≤ ((2 : ℝ)⁻¹) ^ (10 : ℕ) :=
      pow_le_pow_left₀ (inv_pos.mpr hC0').le hhalf 10
    have hnum : ((2 : ℝ)⁻¹) ^ (10 : ℕ) ≤ 1 / 8 := by norm_num
    linarith only [hreg, hstep, hnum]
  have hgam1 : M.gamma ≤ 1 := by linarith only [hgam18]
  have hsqgam : Real.sqrt M.gamma ≤ 1 := by
    have h1 : Real.sqrt M.gamma ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hgam1
    have h2 : Real.sqrt (1 : ℝ) = 1 := Real.sqrt_one
    linarith only [h1, h2]
  have hgamsq : M.gamma ≤ Real.sqrt M.gamma := by
    have hid : Real.sqrt M.gamma * Real.sqrt M.gamma = M.gamma :=
      Real.mul_self_sqrt hgam0.le
    have hstep := mul_le_mul_of_nonneg_left hsqgam (Real.sqrt_nonneg M.gamma)
    rw [mul_one] at hstep
    linarith only [hid, hstep]
  have h4gam : 4 * M.gamma ≤ s := by
    have hC2 : (4 : ℝ) ≤ C ^ (2 : ℕ) := by
      have h := mul_le_mul h2C h2C (by norm_num) (by linarith only [h2C])
      have hid : C ^ (2 : ℕ) = C * C := by ring
      linarith only [h, hid]
    have hstep : 4 * Real.sqrt M.gamma ≤ C ^ (2 : ℕ) * Real.sqrt M.gamma :=
      mul_le_mul_of_nonneg_right hC2 (Real.sqrt_nonneg _)
    have hstep2 : 4 * M.gamma ≤ 4 * Real.sqrt M.gamma := by linarith only [hgamsq]
    linarith only [hstep, hstep2, hsmem.1]
  have hD0 : (0 : ℝ) ≤ (m : ℝ) - (n : ℝ) := by
    have h : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
    linarith only [h]
  have hgamD : M.gamma * ((m : ℝ) - (n : ℝ)) ≤ 1 := by
    have hstep : M.gamma * ((m : ℝ) - (n : ℝ)) ≤ M.gamma * M.gamma⁻¹ :=
      mul_le_mul_of_nonneg_left (by linarith only [hwin]) hgam0.le
    rw [mul_inv_cancel₀ (ne_of_gt hgam0)] at hstep
    exact hstep
  -- the obligation, at the anchor's own parameters
  have hsmemK : s ∈ Set.Icc (K ^ (2 : ℕ) * Real.sqrt M.gamma) (1 / 4) := by
    refine ⟨le_trans ?_ hsmem.1, hs1⟩
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hK.le hKC 2) (Real.sqrt_nonneg _)
  have hpmemK : p ∈ Set.Icc (2 * (d : ℝ) * s⁻¹) (K⁻¹ * M.gamma⁻¹ * s) := by
    refine ⟨hp1, le_trans hpmem.2 ?_⟩
    have hnn : (0 : ℝ) ≤ M.gamma⁻¹ * s := mul_nonneg (inv_pos.mpr hgam0).le hs.le
    have hstep := mul_le_mul_of_nonneg_right hinvle hnn
    have hidL : C⁻¹ * (M.gamma⁻¹ * s) = C⁻¹ * M.gamma⁻¹ * s := by ring
    have hidR : K⁻¹ * (M.gamma⁻¹ * s) = K⁻¹ * M.gamma⁻¹ * s := by ring
    linarith only [hstep, hidL, hidR]
  have hmom := hmoment M hcs hregK m n hnm hwin s hsmemK p hpmemK
  -- the scale sum, closed
  have hsum := tsum_ofReal_scaleMajorant_le (K := K) (p := p) (gam := M.gamma) (s := s)
    (D := (m : ℝ) - (n : ℝ)) hK.le hp0.le hs hs1' hgam0.le h4gam hD0 hgamD
  set V : ℝ := K * p * (M.gamma * (2 * (s⁻¹ * s⁻¹) + 36 * ((m : ℝ) - (n : ℝ)) + 180 / s))
    with hVdef
  have hV0 : (0 : ℝ) ≤ V := by
    have hbr : (0 : ℝ) ≤ 2 * (s⁻¹ * s⁻¹) + 36 * ((m : ℝ) - (n : ℝ)) + 180 / s := by
      have h1 : (0 : ℝ) ≤ 2 * (s⁻¹ * s⁻¹) := by positivity
      have h2 : (0 : ℝ) ≤ 36 * ((m : ℝ) - (n : ℝ)) := by linarith only [hD0]
      have h3 : (0 : ℝ) ≤ 180 / s := by positivity
      linarith only [h1, h2, h3]
    rw [hVdef]
    exact mul_nonneg (mul_nonneg hK.le hp0.le) (mul_nonneg hgam0.le hbr)
  -- the square root, against the anchor's printed scalar
  have hVsq : Real.sqrt V ^ (2 : ℝ) = V := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast,
      Real.sq_sqrt hV0]
  have hconv : (ENNReal.ofReal V) ^ (p / 2) = (ENNReal.ofReal (Real.sqrt V)) ^ p := by
    have h1 : ENNReal.ofReal (Real.sqrt V) ^ p =
        ENNReal.ofReal (Real.sqrt V) ^ ((2 : ℝ) * (p / 2)) := by
      congr 1
      ring
    rw [h1, ENNReal.rpow_mul,
      ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg V) (by norm_num : (0 : ℝ) ≤ 2), hVsq]
  have hreal : Real.rpow (3 : ℝ) (1 / 2 * s * ((m : ℝ) - (n : ℝ))) * Real.sqrt V ≤
      C * Real.rpow (3 : ℝ) (1 / 2 * s * ((m : ℝ) - (n : ℝ))) * Real.sqrt p *
        (s⁻¹ + Real.sqrt ((m : ℝ) - (n : ℝ))) * Real.sqrt M.gamma := by
    have hgauge0 : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (1 / 2 * s * ((m : ℝ) - (n : ℝ))) :=
      Real.rpow_nonneg (by norm_num) _
    have hVsplit : Real.sqrt V = Real.sqrt K * Real.sqrt p *
        Real.sqrt (M.gamma * (2 * (s⁻¹ * s⁻¹) + 36 * ((m : ℝ) - (n : ℝ)) + 180 / s)) := by
      rw [hVdef, Real.sqrt_mul (mul_nonneg hK.le hp0.le), Real.sqrt_mul hK.le]
    have hcore := sqrt_minkowskiScaleSum_le (s := s) (gam := M.gamma)
      (D := (m : ℝ) - (n : ℝ)) hs hs1' hgam0.le hD0
    have hBnn : (0 : ℝ) ≤ Real.sqrt K * Real.sqrt p :=
      mul_nonneg hsqK (Real.sqrt_nonneg _)
    have hZnn : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (1 / 2 * s * ((m : ℝ) - (n : ℝ))) *
        Real.sqrt p * (s⁻¹ + Real.sqrt ((m : ℝ) - (n : ℝ))) * Real.sqrt M.gamma := by
      have hsum0 : (0 : ℝ) ≤ s⁻¹ + Real.sqrt ((m : ℝ) - (n : ℝ)) := by
        have := Real.sqrt_nonneg ((m : ℝ) - (n : ℝ))
        linarith only [hsinv0, this]
      exact mul_nonneg (mul_nonneg (mul_nonneg hgauge0 (Real.sqrt_nonneg _)) hsum0)
        (Real.sqrt_nonneg _)
    calc Real.rpow (3 : ℝ) (1 / 2 * s * ((m : ℝ) - (n : ℝ))) * Real.sqrt V
        = Real.rpow (3 : ℝ) (1 / 2 * s * ((m : ℝ) - (n : ℝ))) *
            (Real.sqrt K * Real.sqrt p *
              Real.sqrt (M.gamma *
                (2 * (s⁻¹ * s⁻¹) + 36 * ((m : ℝ) - (n : ℝ)) + 180 / s))) := by
          rw [hVsplit]
      _ ≤ Real.rpow (3 : ℝ) (1 / 2 * s * ((m : ℝ) - (n : ℝ))) *
            (Real.sqrt K * Real.sqrt p *
              (16 * Real.sqrt M.gamma * (s⁻¹ + Real.sqrt ((m : ℝ) - (n : ℝ))))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcore hBnn) hgauge0
      _ = 16 * Real.sqrt K *
            (Real.rpow (3 : ℝ) (1 / 2 * s * ((m : ℝ) - (n : ℝ))) * Real.sqrt p *
              (s⁻¹ + Real.sqrt ((m : ℝ) - (n : ℝ))) * Real.sqrt M.gamma) := by ring
      _ ≤ C * (Real.rpow (3 : ℝ) (1 / 2 * s * ((m : ℝ) - (n : ℝ))) * Real.sqrt p *
            (s⁻¹ + Real.sqrt ((m : ℝ) - (n : ℝ))) * Real.sqrt M.gamma) :=
          mul_le_mul_of_nonneg_right h16C hZnn
      _ = C * Real.rpow (3 : ℝ) (1 / 2 * s * ((m : ℝ) - (n : ℝ))) * Real.sqrt p *
            (s⁻¹ + Real.sqrt ((m : ℝ) - (n : ℝ))) * Real.sqrt M.gamma := by ring
  have hfinal : ENNReal.ofReal (Real.rpow 3 (1 / 2 * s * ((m : ℝ) - (n : ℝ)))) ^ p *
      (ENNReal.ofReal V) ^ (p / 2) ≤
      ENNReal.ofReal
        (C * Real.rpow (3 : ℝ) (1 / 2 * s * ((m : ℝ) - (n : ℝ))) * Real.sqrt p *
          (s⁻¹ + Real.sqrt ((m : ℝ) - (n : ℝ))) * Real.sqrt M.gamma) ^ p := by
    have hg0 : (0 : ℝ) ≤ Real.rpow 3 (1 / 2 * s * ((m : ℝ) - (n : ℝ))) :=
      Real.rpow_nonneg (show (0 : ℝ) ≤ 3 by norm_num) _
    rw [hconv, ← ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.ofReal_mul hg0]
    exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hreal) hp0.le
  refine le_trans (le_trans (htrans M m n hnm ⟨s, hs⟩ hs1 hgam18 p hp1
    (fun l => minkowskiScaleMajorant K p M.gamma s ((m : ℝ) - (n : ℝ)) l)
    (fun l => minkowskiScaleMajorant_nonneg hK.le hp0.le hgam0.le hD0 l)
    (fun l R hR => hmom l R hR)) ?_) hfinal
  exact mul_le_mul_right (ENNReal.rpow_le_rpow hsum (by positivity)) _

end Algsuperdiff.Section4.Provider.BoundsEaL
