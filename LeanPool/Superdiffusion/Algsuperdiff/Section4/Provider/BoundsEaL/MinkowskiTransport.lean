/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.BoundsEaL.MinkowskiLp
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.BoundsEaL.MajorantMeasurability
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.BoundsEaL.MajorantTransport
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.FluxCorrectedTwoScale

/-!
# MinkowskiTransport

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The `q = 2` scale sum, transported at the MINKOWSKI ordering

## Why this module exists

`AeMeasurableTransport`/`Step5PerCube`/`WeightedScaleClosure` transport the
anchor's left-hand side through Step 1's **Jensen** ordering: the geometric
scale weight sits INSIDE the `p`-th power, so after the `p`-th root it acts at
the rate `s/p`.

```
𝓔(ω) = ( ∑_{l ≥ 0} 𝔠_{2s} 3^{-2sl} · max_{R ∈ desc(□_m, n-l)} J(R; ã_{L,m}) )^{1/2}
```

(`Support.fluxCorrectedTwoScaleErrorFunctional`, literally) presents the scale
sum OUTSIDE the `p`-th power, so the per-scale `L^{p/2}` moments combine by
MINKOWSKI in `L^{p/2}` (`MinkowskiLp.lean`), not by Jensen.

This module performs that transport, and only that:

```
E[ (sup_{L ≥ m} 𝓔)^p ]  ≤  ( 3^{½ s(m-n)} )^p · ( ∑'_l 𝔠_{2s} 3^{-sl} G_l )^{p/2} ,
```

where `G_l` is any per-cube `p/2`-moment majorant at the descendant scale
`n − l`.  Three ingredients:

1. the a.e.  `L`-free majorization of the carrier's per-scale slots (the proved
   `MajorantTransport` split, read through the carrier's own representative
   identification, so that the `sup_L` passes INSIDE the weighted sum);
2. countable Minkowski in `L^{p/2}` (`MinkowskiLp.lean`);
3. the descendant-count conversion **at the norm level**: `max_R ≤ (∑_R
   (·)^{p/2})^{2/p}` costs `(3^{d(m-n+l)})^{2/p} ≤ 3^{s(m-n+l)}`, which is
   exactly the anchor's own floor `p ≥ 2ds^{-1}`.  The geometric weight
   `3^{-2sl}` absorbs the `3^{sl}` and leaves `3^{-sl}`; the residual
   `3^{s(m-n)}` becomes the printed prefactor `3^{½ s(m-n)}` after the square
   root.

No `γ`-power, no `s`-power and no `p`-range is moved: the only inequality on
parameters used below is the anchor's floor `p ≥ 2ds^{-1}`.

## References

* ABK26, `l.bounds.mathcal.E.aL`, Step 1, Step 2, Step 5; `d.mathcal.E`.
-/

namespace Algsuperdiff.Section4.Provider.BoundsEaL

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch04 MeasureTheory
open Algsuperdiff.Section3
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. Four elementary helpers -/

/-- `ENNReal.ofReal` of a nonnegative real `tsum` is at most the `tsum` of the terms,
unconditionally.  Local re-derivation of the `private`
`ofReal_tsum_le_tsum_ofReal_of_nonneg'` of `AeMeasurableTransport.lean`. -/
private theorem ofRealTsumLe {f : ℕ → ℝ} (hf : ∀ l, 0 ≤ f l) :
    ENNReal.ofReal (∑' l, f l) ≤ ∑' l, ENNReal.ofReal (f l) := by
  by_cases h : Summable f
  · exact le_of_eq (ENNReal.ofReal_tsum_of_nonneg hf h)
  · rw [tsum_eq_zero_of_not_summable h, ENNReal.ofReal_zero]
    exact zero_le

/-- Every scale-`k` descendant family of `□_m` with `k ≤ m` is nonempty. -/
private theorem descNonempty (d : ℕ) {m k : ℤ} (hk : k ≤ m) :
    (descendantsAtScale (originCube d m) k).Nonempty := by
  have hs : (originCube d m).scale = m := rfl
  have hpos : 0 < (descendantsAtScale (originCube d m) k).card := by
    rw [descendantsAtScale_eq_descendantsAtDepth (originCube d m) (by rw [hs]; exact hk),
      descendantsAtDepth_card]
    exact pow_pos (pow_pos (by norm_num) d) _
  exact Finset.card_pos.mp hpos

/-- **The descendant count, as a real power of three**: `#desc(□_m, k) = 3^{d(m−k)}`
for `k ≤ m`.  This is the object the anchor's floor `p ≥ 2ds^{-1}` prices. -/
theorem card_descendantsAtScale_originCube_eq_rpow (d : ℕ) {m k : ℤ} (hk : k ≤ m) :
    (((descendantsAtScale (originCube d m) k).card : ℕ) : ℝ) =
      Real.rpow 3 ((d : ℝ) * ((m : ℝ) - (k : ℝ))) := by
  have hs : (originCube d m).scale = m := rfl
  have hcard : (descendantsAtScale (originCube d m) k).card =
      (3 ^ d) ^ (Int.toNat (m - k)) := by
    rw [descendantsAtScale_eq_descendantsAtDepth (originCube d m) (by rw [hs]; exact hk),
      descendantsAtDepth_card, hs]
  have hN : ((Int.toNat (m - k) : ℕ) : ℝ) = (m : ℝ) - (k : ℝ) := by
    have hz : ((Int.toNat (m - k) : ℕ) : ℤ) = m - k := Int.toNat_of_nonneg (by omega)
    have hcast : (((Int.toNat (m - k) : ℕ) : ℤ) : ℝ) = ((m - k : ℤ) : ℝ) :=
      congrArg (fun z : ℤ => (z : ℝ)) hz
    rw [Int.cast_sub] at hcast
    exact_mod_cast hcast
  have hc : ((3 ^ (d * Int.toNat (m - k)) : ℕ) : ℝ) =
      (3 : ℝ) ^ (d * Int.toNat (m - k)) := by
    push_cast
    ring
  rw [hcard, ← pow_mul, hc,
    ← Real.rpow_natCast (3 : ℝ) (d * Int.toNat (m - k)), Nat.cast_mul, hN]
  rfl

/-- Local re-derivation of `Step5GeometricClosure`'s `private rpowBridge`. -/
private theorem rpowBridgeMink (x y : ℝ) : Real.rpow x y = x ^ y := rfl

/-- `(3^x)^y = 3^{xy}` in the `ENNReal.ofReal` spelling, for `y ≥ 0`. -/
private theorem ofRealRpowThree {x y : ℝ} (hy : 0 ≤ y) :
    ENNReal.ofReal (Real.rpow 3 x) ^ y = ENNReal.ofReal (Real.rpow 3 (x * y)) := by
  simp only [rpowBridgeMink]
  rw [ENNReal.ofReal_rpow_of_nonneg
      (Real.rpow_nonneg (show (0 : ℝ) ≤ 3 by norm_num) x) hy,
    ← Real.rpow_mul (show (0 : ℝ) ≤ 3 by norm_num)]

/-- The `q = 2` geometric weight, written out. -/
private theorem geometricWeightTwo (t : ℝ) (l : ℕ) :
    Ch02.geometricWeight t 2 l =
      Ch02.geometricDiscount t 2 * Real.rpow 3 (-t * 2 * (l : ℝ)) := rfl

/-! ## 2. The transport, at an abstract per-cube majorant -/

private theorem minkowski_error_observable_bound :
    ∀ {d : ℕ} (M : ABKModel d) {m n : ℤ},
      n ≤ m →
        ∀ (s : { s : ℝ // (0 : ℝ) < s }) {p : ℝ},
          (2 : ℝ) * (↑d : ℝ) * (↑s : ℝ)⁻¹ ≤ p →
            ∀ (Maj : TriadicCube d → Cutoff.CutoffSample d → ℝ),
              (∀ (R : TriadicCube d),
                  AEMeasurable (Maj R) (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d))) →
                ∀ (G : ℕ → ℝ),
                  (∀ (l : ℕ), (0 : ℝ) ≤ G l) →
                    (∀ (l : ℕ),
                        ∀ R ∈ descendantsAtScale (originCube d m) (n - (↑l : ℤ)),
                          ∫⁻ (omega : Cutoff.CutoffSample d),
                              ENNReal.ofReal (Maj R omega) ^
                                (p / (2 : ℝ)) ∂(↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d)) ≤
                            ENNReal.ofReal (G l) ^ (p / (2 : ℝ))) →
                      (0 : ℝ) < (↑s : ℝ) →
                        (0 : ℝ) < p / (2 : ℝ) →
                          (0 : ℝ) < (1 : ℝ) / (p / (2 : ℝ)) →
                            (∀ (l : ℕ), (0 : ℝ) ≤ Ch02.geometricWeight (↑s : ℝ) (2 : ℝ) l) →
                              (∀ (l : ℕ), n - (↑l : ℤ) ≤ m) →
                                let F : ℕ → Cutoff.CutoffSample d → ℝ≥0∞ := fun (l : ℕ) (omega : Cutoff.CutoffSample d) =>
                                  ENNReal.ofReal (Ch02.geometricWeight (↑s : ℝ) (2 : ℝ) l) *
                                    (∑ R ∈ descendantsAtScale (originCube d m) (n - (↑l : ℤ)),
                                        ENNReal.ofReal (Maj R omega) ^ (p / (2 : ℝ))) ^
                                      ((1 : ℝ) / (p / (2 : ℝ)));
                                (F = fun (l : ℕ) (omega : Cutoff.CutoffSample d) =>
                                    ENNReal.ofReal (Ch02.geometricWeight (↑s : ℝ) (2 : ℝ) l) *
                                      (∑ R ∈ descendantsAtScale (originCube d m) (n - (↑l : ℤ)),
                                          ENNReal.ofReal (Maj R omega) ^ (p / (2 : ℝ))) ^
                                        ((1 : ℝ) / (p / (2 : ℝ)))) →
                                  ∀ (l : ℕ),
                                    (∫⁻ (omega : Cutoff.CutoffSample d),
                                          F l omega ^
                                            (p /
                                              (2 : ℝ)) ∂(↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d))) ^
                                        ((1 : ℝ) / (p / (2 : ℝ))) ≤
                                      ENNReal.ofReal (Real.rpow (3 : ℝ) ((↑s : ℝ) * ((↑m : ℝ) - (↑n : ℝ)))) *
                                        ENNReal.ofReal
                                          (Ch02.geometricDiscount (↑s : ℝ) (2 : ℝ) *
                                            (Real.rpow (3 : ℝ) (-(↑s : ℝ) * (↑l : ℝ)) * G l)) := by
  intro d M m n hnm s p hp Maj hMajMeas G hG hcube hs0 hq0 hqinv hw0 hscale F hF l
  have hcardR := card_descendantsAtScale_originCube_eq_rpow d (hscale l)
  -- the integral of the `p/2`-th power
  have hpow : ∀ omega : Cutoff.CutoffSample d, F l omega ^ (p / 2) =
      ENNReal.ofReal (Ch02.geometricWeight (s : ℝ) 2 l) ^ (p / 2) *
        ∑ R ∈ descendantsAtScale (originCube d m) (n - (l : ℤ)),
          ENNReal.ofReal (Maj R omega) ^ (p / 2) := by
    intro omega
    rw [hF, ENNReal.mul_rpow_of_nonneg _ _ hq0.le, ← ENNReal.rpow_mul,
      one_div_mul_cancel (ne_of_gt hq0), ENNReal.rpow_one]
  have hmeasR : ∀ R : TriadicCube d,
      AEMeasurable (fun omega : Cutoff.CutoffSample d =>
        ENNReal.ofReal (Maj R omega) ^ (p / 2))
        (Cutoff.cutoffSampleLaw M).toMeasure := fun R =>
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable (hMajMeas R).ennreal_ofReal
  have hconstNeTop : ENNReal.ofReal (Ch02.geometricWeight (s : ℝ) 2 l) ^ (p / 2) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg hq0.le ENNReal.ofReal_ne_top
  have hint : (∫⁻ omega, F l omega ^ (p / 2) ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
      ENNReal.ofReal (Ch02.geometricWeight (s : ℝ) 2 l) ^ (p / 2) *
        ∑ R ∈ descendantsAtScale (originCube d m) (n - (l : ℤ)),
          ∫⁻ omega, ENNReal.ofReal (Maj R omega) ^ (p / 2)
            ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
    rw [lintegral_congr hpow, lintegral_const_mul' _ _ hconstNeTop,
      lintegral_finsetSum' _ fun R _ => hmeasR R]
  have hsumle : (∑ R ∈ descendantsAtScale (originCube d m) (n - (l : ℤ)),
        ∫⁻ omega, ENNReal.ofReal (Maj R omega) ^ (p / 2)
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      (((descendantsAtScale (originCube d m) (n - (l : ℤ))).card : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (G l) ^ (p / 2) := by
    refine le_trans (Finset.sum_le_card_nsmul _ _ _ fun R hR => hcube l R hR) ?_
    rw [nsmul_eq_mul]
  have hbound : (∫⁻ omega, F l omega ^ (p / 2)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      (ENNReal.ofReal (Ch02.geometricWeight (s : ℝ) 2 l) *
        ((((descendantsAtScale (originCube d m) (n - (l : ℤ))).card : ℕ) : ℝ≥0∞) ^
          (1 / (p / 2)) * ENNReal.ofReal (G l))) ^ (p / 2) := by
    rw [hint]
    refine le_trans (mul_le_mul_right hsumle _) (le_of_eq ?_)
    rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le, ENNReal.mul_rpow_of_nonneg _ _ hq0.le,
      ← ENNReal.rpow_mul, one_div_mul_cancel (ne_of_gt hq0), ENNReal.rpow_one]
  have h3nn : (0 : ℝ) ≤ Real.rpow 3 ((d : ℝ) * ((m : ℝ) - ((n - (l : ℤ) : ℤ) : ℝ))) :=
    Real.rpow_nonneg (show (0 : ℝ) ≤ 3 by norm_num) _
  have hXnn : (0 : ℝ) ≤ Real.rpow 3 ((d : ℝ) * ((m : ℝ) - ((n - (l : ℤ) : ℤ) : ℝ))) ^
      (1 / (p / 2)) := Real.rpow_nonneg h3nn _
  have hSnn : (0 : ℝ) ≤ Real.rpow 3 ((s : ℝ) * ((m : ℝ) - (n : ℝ))) :=
    Real.rpow_nonneg (show (0 : ℝ) ≤ 3 by norm_num) _
  have hcardE : ((((descendantsAtScale (originCube d m) (n - (l : ℤ))).card : ℕ) : ℝ≥0∞)) ^
      (1 / (p / 2)) =
      ENNReal.ofReal (Real.rpow 3 ((d : ℝ) * ((m : ℝ) - ((n - (l : ℤ) : ℤ) : ℝ))) ^
        (1 / (p / 2))) := by
    rw [← ENNReal.ofReal_natCast, hcardR, ENNReal.ofReal_rpow_of_nonneg h3nn hqinv.le]
  rw [hcardE] at hbound
  refine le_trans (ENNReal.rpow_le_rpow hbound hqinv.le) ?_
  rw [← ENNReal.rpow_mul, mul_one_div_cancel (ne_of_gt hq0), ENNReal.rpow_one,
    ← ENNReal.ofReal_mul hXnn, ← ENNReal.ofReal_mul (hw0 l),
    ← ENNReal.ofReal_mul hSnn]
  -- the real arithmetic: the count is paid by the floor `p ≥ 2ds⁻¹`
  refine ENNReal.ofReal_le_ofReal ?_
  have hdl : (0 : ℝ) ≤ ((m : ℝ) - (n : ℝ)) + (l : ℝ) := by
    have h1 : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
    have h2 : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
    linarith only [h1, h2]
  have hshift : (m : ℝ) - ((n - (l : ℤ) : ℤ) : ℝ) = ((m : ℝ) - (n : ℝ)) + (l : ℝ) := by
    push_cast
    ring
  have hexp : (d : ℝ) * (((m : ℝ) - (n : ℝ)) + (l : ℝ)) * (1 / (p / 2)) ≤
      (s : ℝ) * (((m : ℝ) - (n : ℝ)) + (l : ℝ)) := by
    have hps : 2 * (d : ℝ) ≤ p * (s : ℝ) := by
      have h := mul_le_mul_of_nonneg_right hp hs0.le
      rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt hs0), mul_one] at h
      exact h
    have hratio : (d : ℝ) * (1 / (p / 2)) ≤ (s : ℝ) := by
      rw [one_div, ← div_eq_mul_inv, div_le_iff₀ hq0]
      linarith only [hps]
    have hstep := mul_le_mul_of_nonneg_left hratio hdl
    linarith only [hstep]
  have hcount : Real.rpow 3 ((d : ℝ) * ((m : ℝ) - ((n - (l : ℤ) : ℤ) : ℝ))) ^
      (1 / (p / 2)) ≤
      Real.rpow 3 ((s : ℝ) * ((m : ℝ) - (n : ℝ)) + (s : ℝ) * (l : ℝ)) := by
    simp only [rpowBridgeMink]
    rw [hshift, ← Real.rpow_mul (show (0 : ℝ) ≤ 3 by norm_num)]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hid : (s : ℝ) * (((m : ℝ) - (n : ℝ)) + (l : ℝ)) =
        (s : ℝ) * ((m : ℝ) - (n : ℝ)) + (s : ℝ) * (l : ℝ) := by ring
    linarith only [hexp, hid]
  have e1 : Real.rpow 3 (-(s : ℝ) * 2 * (l : ℝ)) *
      Real.rpow 3 ((s : ℝ) * ((m : ℝ) - (n : ℝ)) + (s : ℝ) * (l : ℝ)) =
      Real.rpow 3 ((s : ℝ) * ((m : ℝ) - (n : ℝ)) + -(s : ℝ) * (l : ℝ)) := by
    simp only [rpowBridgeMink]
    rw [← Real.rpow_add (show (0 : ℝ) < 3 by norm_num)]
    congr 1
    ring
  have e2 : Real.rpow 3 ((s : ℝ) * ((m : ℝ) - (n : ℝ))) *
      Real.rpow 3 (-(s : ℝ) * (l : ℝ)) =
      Real.rpow 3 ((s : ℝ) * ((m : ℝ) - (n : ℝ)) + -(s : ℝ) * (l : ℝ)) := by
    simp only [rpowBridgeMink]
    rw [← Real.rpow_add (show (0 : ℝ) < 3 by norm_num)]
  have hwid : Ch02.geometricWeight (s : ℝ) 2 l =
      Ch02.geometricDiscount (s : ℝ) 2 * Real.rpow 3 (-(s : ℝ) * 2 * (l : ℝ)) :=
    geometricWeightTwo (s : ℝ) l
  have hkey : Ch02.geometricWeight (s : ℝ) 2 l *
      Real.rpow 3 ((d : ℝ) * ((m : ℝ) - ((n - (l : ℤ) : ℤ) : ℝ))) ^ (1 / (p / 2)) ≤
      Real.rpow 3 ((s : ℝ) * ((m : ℝ) - (n : ℝ))) *
        (Ch02.geometricDiscount (s : ℝ) 2 * Real.rpow 3 (-(s : ℝ) * (l : ℝ))) := by
    refine le_trans (mul_le_mul_of_nonneg_left hcount (hw0 l)) (le_of_eq ?_)
    rw [hwid, mul_assoc, e1, ← e2]
    ring
  have hGl : (0 : ℝ) ≤ G l := hG l
  have hfinal := mul_le_mul_of_nonneg_right hkey hGl
  have hlhs : Ch02.geometricWeight (s : ℝ) 2 l *
      Real.rpow 3 ((d : ℝ) * ((m : ℝ) - ((n - (l : ℤ) : ℤ) : ℝ))) ^ (1 / (p / 2)) * G l =
    Ch02.geometricWeight (s : ℝ) 2 l *
      (Real.rpow 3 ((d : ℝ) * ((m : ℝ) - ((n - (l : ℤ) : ℤ) : ℝ))) ^ (1 / (p / 2)) *
        G l) := by ring
  have hrhs : Real.rpow 3 ((s : ℝ) * ((m : ℝ) - (n : ℝ))) *
      (Ch02.geometricDiscount (s : ℝ) 2 * Real.rpow 3 (-(s : ℝ) * (l : ℝ))) * G l =
    Real.rpow 3 ((s : ℝ) * ((m : ℝ) - (n : ℝ))) *
      (Ch02.geometricDiscount (s : ℝ) 2 * (Real.rpow 3 (-(s : ℝ) * (l : ℝ)) * G l)) := by
    ring
  linarith only [hfinal, hlhs, hrhs]

/-- **The Minkowski-ordered transport.**

`Maj` is any per-cube majorant of the Step-1 endpoint's per-cube object,
uniformly in the truncation index `L ≥ m`; `G l` is any bound for its
`L^{p/2}`-norm at the descendant scale `n − l`.  The conclusion carries the
scale sum OUTSIDE the `p`-th power.

The proof is the three-line mathematical argument of the module docstring:
the `sup_L` passes inside the weighted sum (a.e., by the carrier's own
representative identification), the per-scale `L^{p/2}`-norms combine by
countable Minkowski, and each descendant maximum is paid at the norm level by
the descendant count against the anchor's floor. -/
private theorem observableSup_rpow_le_minkowski_core [NeZero d] (M : ABKModel d) {m n : ℤ}
    (hnm : n ≤ m) (s : {s : ℝ // 0 < s}) {p : ℝ}
    (hp : 2 * (d : ℝ) * (s : ℝ)⁻¹ ≤ p) (hq : 1 ≤ p / 2)
    (Maj : TriadicCube d → Cutoff.CutoffSample d → ℝ)
    (hMajMeas : ∀ R : TriadicCube d,
      AEMeasurable (Maj R) (Cutoff.cutoffSampleLaw M).toMeasure)
    (hMajAe : ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ L : ℤ, m ≤ L → ∀ (l : ℕ) (R : TriadicCube d),
        R ∈ descendantsAtScale (originCube d m) (n - (l : ℤ)) →
          Ch02.normalizedBlockResponseMax R
              (Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega)
              (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)) ≤
            Maj R omega)
    (G : ℕ → ℝ) (hG : ∀ l, 0 ≤ G l)
    (hcube : ∀ (l : ℕ) (R : TriadicCube d),
      R ∈ descendantsAtScale (originCube d m) (n - (l : ℤ)) →
      (∫⁻ omega, ENNReal.ofReal (Maj R omega) ^ (p / 2)
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ ENNReal.ofReal (G l) ^ (p / 2)) :
    (∫⁻ omega, Support.fluxCorrectedTwoScaleErrorObservableSup M m n s omega ^ p
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      ENNReal.ofReal (Real.rpow 3 (1 / 2 * (s : ℝ) * ((m : ℝ) - (n : ℝ)))) ^ p *
        (∑' l : ℕ, ENNReal.ofReal (Ch02.geometricDiscount (s : ℝ) 2 *
          (Real.rpow 3 (-(s : ℝ) * (l : ℝ)) * G l))) ^ (p / 2) := by
  classical
  have hs0 : (0 : ℝ) < (s : ℝ) := s.2
  have hq0 : (0 : ℝ) < p / 2 := lt_of_lt_of_le zero_lt_one hq
  have hp0 : (0 : ℝ) < p := by linarith only [hq0]
  have hqinv : (0 : ℝ) < 1 / (p / 2) := one_div_pos.mpr hq0
  have hdisc : (0 : ℝ) < Ch02.geometricDiscount (s : ℝ) 2 := by
    rw [Ch02.geometricDiscount_eq_old]
    exact HCPolySupport.geometricDiscount_pos (by positivity)
  have hw0 : ∀ l : ℕ, (0 : ℝ) ≤ Ch02.geometricWeight (s : ℝ) 2 l := by
    intro l
    rw [geometricWeightTwo]
    exact mul_nonneg hdisc.le (Real.rpow_nonneg (by norm_num) _)
  have hscale : ∀ l : ℕ, n - (l : ℤ) ≤ m := fun l =>
    le_trans (sub_le_self n (by exact_mod_cast Nat.zero_le l)) hnm
  -- the per-scale `ℝ≥0∞` majorant family
  set F : ℕ → Cutoff.CutoffSample d → ℝ≥0∞ := fun l omega =>
    ENNReal.ofReal (Ch02.geometricWeight (s : ℝ) 2 l) *
      (∑ R ∈ descendantsAtScale (originCube d m) (n - (l : ℤ)),
        ENNReal.ofReal (Maj R omega) ^ (p / 2)) ^ (1 / (p / 2)) with hF
  have hFmeas : ∀ l : ℕ, AEMeasurable (F l) (Cutoff.cutoffSampleLaw M).toMeasure := by
    intro l
    refine AEMeasurable.const_mul ?_ _
    refine ENNReal.continuous_rpow_const.measurable.comp_aemeasurable ?_
    refine Finset.aemeasurable_fun_sum _ fun R _ => ?_
    exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      (hMajMeas R).ennreal_ofReal
  -- STEP A: the a.e. pointwise bound, with the `sup_L` inside the weighted sum
  have hrepAll : ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ L : {L : ℤ // m ≤ L}, ∀ R : TriadicCube d,
        Ch02.normalizedBlockResponseMax R
            (Support.fluxCorrectedCoeffFamily M L.1 m (originCube d m) omega)
            (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)) =
          Support.fluxCorrectedNormalizedBlockResponseRepresentative M L.1 m
            (originCube d m) R
            (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)) omega :=
    MeasureTheory.ae_all_iff.2 fun L =>
      Support.ae_forall_normalizedBlockResponseMax_fluxCorrected_eq_representative M L.1 m
        (originCube d m) (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m))
  have hae : ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      Support.fluxCorrectedTwoScaleErrorObservableSup M m n s omega ^ p ≤
        (∑' l : ℕ, F l omega) ^ (p / 2) := by
    filter_upwards [hrepAll, hMajAe] with omega hrep hmaj
    have hobs : Support.fluxCorrectedTwoScaleErrorObservableSup M m n s omega =
        ⨆ L : {L : ℤ // m ≤ L}, ENNReal.ofReal
          (Support.fluxCorrectedTwoScaleErrorRepresentative M L.1 m n s omega) := rfl
    rw [hobs, iSup_rpow_of_pos _ hp0]
    refine iSup_le fun L => ?_
    have hterm0 : ∀ l : ℕ, 0 ≤ Ch02.geometricWeight (s : ℝ) 2 l *
        Support.fluxCorrectedMaxDescendantNormalizedBlockResponseRepresentative M L.1 m
          (originCube d m) (n - (l : ℤ))
          (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)) omega := fun l =>
      mul_nonneg (hw0 l)
        (Support.fluxCorrectedMaxDescendantNormalizedBlockResponseRepresentative_nonneg
          M L.1 m (originCube d m) (n - (l : ℤ)) _ omega)
    have hA0 : (0 : ℝ) ≤ ∑' l : ℕ, Ch02.geometricWeight (s : ℝ) 2 l *
        Support.fluxCorrectedMaxDescendantNormalizedBlockResponseRepresentative M L.1 m
          (originCube d m) (n - (l : ℤ))
          (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)) omega :=
      tsum_nonneg hterm0
    have hrepA : Support.fluxCorrectedTwoScaleErrorRepresentative M L.1 m n s omega =
        Real.sqrt (∑' l : ℕ, Ch02.geometricWeight (s : ℝ) 2 l *
          Support.fluxCorrectedMaxDescendantNormalizedBlockResponseRepresentative M L.1 m
            (originCube d m) (n - (l : ℤ))
            (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)) omega) := rfl
    rw [hrepA, Real.sqrt_eq_rpow,
      ← ENNReal.ofReal_rpow_of_nonneg hA0 (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ← ENNReal.rpow_mul, show (1 : ℝ) / 2 * p = p / 2 from by ring]
    refine ENNReal.rpow_le_rpow (le_trans (ofRealTsumLe hterm0) ?_) hq0.le
    refine ENNReal.tsum_le_tsum fun l => ?_
    rw [hF, ENNReal.ofReal_mul (hw0 l)]
    refine mul_le_mul_right ?_ _
    -- the descendant maximum, paid at the norm level
    have hne := descNonempty d (hscale l)
    obtain ⟨R0, hR0, hR0eq⟩ := Finset.exists_mem_eq_sup' hne
      (fun R => Support.fluxCorrectedNormalizedBlockResponseRepresentative M L.1 m
        (originCube d m) R
        (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)) omega)
    have hsupdef : Support.fluxCorrectedMaxDescendantNormalizedBlockResponseRepresentative
          M L.1 m (originCube d m) (n - (l : ℤ))
          (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)) omega =
        Ch02.finsetSupReal (descendantsAtScale (originCube d m) (n - (l : ℤ)))
          (fun R => Support.fluxCorrectedNormalizedBlockResponseRepresentative M L.1 m
            (originCube d m) R
            (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)) omega) := rfl
    rw [hsupdef, RestrictionLawCarrier.finsetSupReal_eq_sup' _ hne, hR0eq]
    have hle : Support.fluxCorrectedNormalizedBlockResponseRepresentative M L.1 m
        (originCube d m) R0
        (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M m)) omega ≤
        Maj R0 omega := by
      rw [← hrep L R0]
      exact hmaj L.1 L.2 l R0 hR0
    refine le_trans (ENNReal.ofReal_le_ofReal hle) ?_
    have hsingle : ENNReal.ofReal (Maj R0 omega) ^ (p / 2) ≤
        ∑ R ∈ descendantsAtScale (originCube d m) (n - (l : ℤ)),
          ENNReal.ofReal (Maj R omega) ^ (p / 2) :=
      Finset.single_le_sum
        (f := fun R => ENNReal.ofReal (Maj R omega) ^ (p / 2)) (fun _ _ => zero_le) hR0
    have hraise := ENNReal.rpow_le_rpow hsingle hqinv.le
    rwa [← ENNReal.rpow_mul, mul_one_div_cancel (ne_of_gt hq0), ENNReal.rpow_one] at hraise
  -- STEP B: countable Minkowski in `L^{p/2}`
  have hstepB : (∫⁻ omega, Support.fluxCorrectedTwoScaleErrorObservableSup M m n s omega ^ p
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      (∑' l : ℕ, (∫⁻ omega, F l omega ^ (p / 2)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ^ (1 / (p / 2))) ^ (p / 2) :=
    le_trans (lintegral_mono_ae hae) (lintegral_rpow_tsum_le_rpow_tsum hq F hFmeas)
  -- STEP C: the per-scale evaluation, with the count paid against the anchor's floor
  have hper := @minkowski_error_observable_bound (d) (M) (m) (n) (hnm) (s) (p) (hp) (Maj)
    (hMajMeas) (G) (hG) (hcube) (hs0) (hq0) (hqinv) (hw0) (hscale) (hF)
  -- STEP D: assembly
  refine le_trans hstepB (le_trans (ENNReal.rpow_le_rpow
    (ENNReal.tsum_le_tsum hper) hq0.le) (le_of_eq ?_))
  rw [ENNReal.tsum_mul_left, ENNReal.mul_rpow_of_nonneg _ _ hq0.le, ofRealRpowThree hq0.le,
    ofRealRpowThree hp0.le]
  congr 3
  ring

/-! ## 3. The transport at the `L`-free majorant -/

/-- **The anchor's left-hand side at the Minkowski ordering.**

If at every scale `n − l` and every descendant cube `R` of `□_m` at that scale
the `p/2`-th moment of the `L`-free Step-3 majorant is at most
`(ofReal (G l))^{p/2}`, then

```
E[ (sup_{L ≥ m} 𝓔_{s,∞,2}(□_m, n))^p ]
    ≤ (3^{½ s(m−n)})^p · ( ∑'_l 𝔠_{2s} · 3^{−sl} · G_l )^{p/2} .
```

The printed prefactor `3^{½ s(m−n)}` comes out, and no constraint on `p` beyond
the anchor's own floor `p ≥ 2ds^{-1}` is used.

The per-cube hypothesis is a conditional API obligation: it is Step 5's inner
(Hölder) half, which this module does not prove. -/
theorem lintegral_observableSup_rpow_le_minkowskiScaleSum (d : ℕ) (dimension : 2 ≤ d) :
    letI : NeZero d := ⟨by omega⟩
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (m n : ℤ), n ≤ m → ∀ (s : {s : ℝ // 0 < s}),
        (s : ℝ) ≤ 1 / 4 → M.gamma ≤ 1 / 8 →
        ∀ p : ℝ, 2 * (d : ℝ) * (s : ℝ)⁻¹ ≤ p → ∀ G : ℕ → ℝ, (∀ l, 0 ≤ G l) →
          (∀ (l : ℕ) (R : TriadicCube d),
              R ∈ descendantsAtScale (originCube d m) (n - (l : ℤ)) →
              (∫⁻ omega, ENNReal.ofReal
                    (lFreeStep3Majorant C M m (s : ℝ) (lFreeGradSlot m (tailSeriesGauge m))
                      (lFreeValueSlot m (tailSeriesGauge m)) R omega) ^ (p / 2)
                  ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
                ENNReal.ofReal (G l) ^ (p / 2)) →
          (∫⁻ omega, Support.fluxCorrectedTwoScaleErrorObservableSup M m n s omega ^ p
              ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
            ENNReal.ofReal (Real.rpow 3 (1 / 2 * (s : ℝ) * ((m : ℝ) - (n : ℝ)))) ^ p *
              (∑' l : ℕ, ENNReal.ofReal (Ch02.geometricDiscount (s : ℝ) 2 *
                (Real.rpow 3 (-(s : ℝ) * (l : ℝ)) * G l))) ^ (p / 2) := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨C, hC, hmaj⟩ :=
    exists_normalizedBlockResponseMax_le_lFreeStep3Majorant_of_tail d dimension
  refine ⟨C, hC, ?_⟩
  intro M m n hnm s hs1 hgam p hp G hG hcube
  have hs0 : (0 : ℝ) < (s : ℝ) := s.2
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast dimension
  have hsinv : (4 : ℝ) ≤ (s : ℝ)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hs0]
    exact le_trans hs1 (by norm_num)
  have hq : (1 : ℝ) ≤ p / 2 := by
    have h1 : (2 : ℝ) * 2 * 4 ≤ 2 * (d : ℝ) * 4 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd2 (by norm_num)) (by norm_num)
    have h2 : (2 : ℝ) * (d : ℝ) * 4 ≤ 2 * (d : ℝ) * (s : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left hsinv (by positivity)
    linarith only [h1, h2, hp]
  refine observableSup_rpow_le_minkowski_core M hnm s hp hq
    (fun R omega => lFreeStep3Majorant C M m (s : ℝ) (lFreeGradSlot m (tailSeriesGauge m))
      (lFreeValueSlot m (tailSeriesGauge m)) R omega)
    (fun R => aemeasurable_lFreeStep3Majorant M C m s hgam (tailSeriesGauge m)
      (fun k v => measurable_tailSeriesGauge m k v) R) ?_ G hG hcube
  filter_upwards [ae_tailLayerSum_le_tailSeriesGauge M m] with omega hT
  intro L hL l R hR
  exact hmaj M m n hnm (s : ℝ) hs0 hs1 hgam (tailSeriesGauge m) omega hT.1 hT.2 L hL l R hR

end

end Algsuperdiff.Section4.Provider.BoundsEaL
