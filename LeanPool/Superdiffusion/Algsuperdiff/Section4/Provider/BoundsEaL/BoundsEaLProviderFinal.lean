/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.BoundsEaL.MinkowskiProviderFinal
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.BoundsEaL.PerCubeSixWay
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.BoundsEaL.PerCubeSlotSecond

/-!
# BoundsEaLProviderFinal

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `bounds_mathcal_E_aL`: the unconditional provider-final

## What this module delivers

`MinkowskiProviderFinal.bounds_mathcal_E_aL_provider_of_perCubeMoments` reduces
the anchor to ONE per-cube `L^{p/2}`-moment obligation `hcube` at the
three-shape majorant `minkowskiScaleMajorant`.  This module discharges it:

1. `PerCubeSixWay.lintegral_rpow_lFreeStep3Majorant_le_of_summands` splits the
   `L`-free Step-3 majorant into its three named summands at the absolute cost
   `2` (the negated leg, priced by the proved negation invariance of the law);
2. each summand is bounded at the anchor's own slots -- the FIRST and THIRD at
   `K p γ s^{-2}` (`PerCubeSlotFirst`, `PerCubeSlotThird`), the SECOND at
   `K p (γ(m−j) + γ) 3^{2γ(m−j)}` (`PerCubeSlotSecond`);
3. the anchor's own window (`γ ≤ C^{-10}`, `s ∈ [C²√γ, 1/4]`,
   `p ≤ C^{-1}γ^{-1}s`) supplies the four scalar facts the slot bounds need:
   `γ ≤ 1/8`, `8γ ≤ s`, `1 ≤ p/2` and `8(p/2) ≤ γ^{-1}`.  NOTHING else about
   `p` is used: the anchor's printed range stands unchanged.

## References

* ABK26, `l.bounds.mathcal.E.aL`, Steps 1--5.
-/

namespace Algsuperdiff.Section4.Provider.BoundsEaL

open HCPolySupport HCPolySupport.Book HCPolySupport.IndependentSums MeasureTheory
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Frozen.Section24
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open Algsuperdiff.Section3.Provider.Stream
open Algsuperdiff.Section4.Provider.Annular
open scoped ENNReal

noncomputable section

/-! ## 1. The per-cube obligation, discharged -/

private theorem perCubeMoments_admissibleExponent :
    ∀ (d : ℕ) (Cd Cr1 A1 Cr2 A2 Cr3 A3 : ℝ) (M : ABKModel d) (s p : ℝ),
      p ∈
          Set.Icc ((2 : ℝ) * (↑d : ℝ) * s⁻¹)
            ((max (max (max Cr1 Cr2) (max Cr3 (3 : ℝ))) (max (Cd * (A1 + A3)) (Cd * A2)))⁻¹ *
              M.gamma⁻¹ * s) →
        (0 : ℝ) < M.gamma →
          (3 : ℝ) ≤ max (max (max Cr1 Cr2) (max Cr3 (3 : ℝ))) (max (Cd * (A1 + A3)) (Cd * A2)) →
            s ≤ (1 / 4 : ℝ) → (0 : ℝ) < s → (8 : ℝ) * (p / (2 : ℝ)) ≤ M.gamma⁻¹ := by
  intro _ Cd Cr1 A1 Cr2 A2 Cr3 A3 M s p hpmem hgam0 h3le hs1 hs
  have hKinv : (max (max (max Cr1 Cr2) (max Cr3 3))
      (max (Cd * (A1 + A3)) (Cd * A2)))⁻¹ ≤ (3 : ℝ)⁻¹ :=
    inv_anti₀ (by norm_num) h3le
  have hnn : (0 : ℝ) ≤ M.gamma⁻¹ * s := mul_nonneg (inv_pos.mpr hgam0).le hs.le
  have hstep := mul_le_mul_of_nonneg_right hKinv hnn
  have hid : (max (max (max Cr1 Cr2) (max Cr3 3))
      (max (Cd * (A1 + A3)) (Cd * A2)))⁻¹ * (M.gamma⁻¹ * s) =
      (max (max (max Cr1 Cr2) (max Cr3 3))
        (max (Cd * (A1 + A3)) (Cd * A2)))⁻¹ * M.gamma⁻¹ * s := by ring
  have hple : p ≤ (3 : ℝ)⁻¹ * (M.gamma⁻¹ * s) := by
    linarith only [hpmem.2, hstep, hid]
  have hsle : (3 : ℝ)⁻¹ * (M.gamma⁻¹ * s) ≤ (3 : ℝ)⁻¹ * (M.gamma⁻¹ * (1 / 4)) := by
    have h := mul_le_mul_of_nonneg_left hs1 (inv_pos.mpr hgam0).le
    have h2 := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ (3 : ℝ)⁻¹)
    linarith only [h2]
  have hfin : (3 : ℝ)⁻¹ * (M.gamma⁻¹ * (1 / 4)) ≤ M.gamma⁻¹ / 4 := by
    have hgi : (0 : ℝ) ≤ M.gamma⁻¹ := (inv_pos.mpr hgam0).le
    have hid2 : (3 : ℝ)⁻¹ * (M.gamma⁻¹ * (1 / 4)) = M.gamma⁻¹ / 12 := by ring
    have hid3 : M.gamma⁻¹ / 4 - M.gamma⁻¹ / 12 = M.gamma⁻¹ / 6 := by ring
    have h6 : (0 : ℝ) ≤ M.gamma⁻¹ / 6 := by linarith only [hgi]
    linarith only [hid2, hid3, h6]
  linarith only [hple, hsle, hfin]

private theorem boundsEaLProviderFinal_comparisonBounds1 :
    ∀ (d : ℕ) [NeZero d] (cstar Cd : ℝ) (_ : (0 : ℝ) < Cd) (Cr1 A1 : ℝ) (_ : (0 : ℝ) < Cr1)
      (_ : (0 : ℝ) < A1)
      (_ :
        ∀ (M : ABKModel d),
          Disorder.cstar M = cstar →
            M.gamma ≤ Cr1⁻¹ ^ (10 : ℕ) →
              M.gamma ≤ (1 / 8 : ℝ) →
                ∀ (Cd : ℝ),
                  (0 : ℝ) ≤ Cd →
                    ∀ (s : ℝ),
                      (0 : ℝ) < s →
                        s ≤ (1 / 4 : ℝ) →
                          (8 : ℝ) * M.gamma ≤ s →
                            ∀ (m : ℤ) (R : TriadicCube d),
                              R.scale ≤ m →
                                ∀ (q : ℝ),
                                  (1 : ℝ) ≤ q →
                                    (8 : ℝ) * q ≤ M.gamma⁻¹ →
                                      ∫⁻ (omega : Cutoff.CutoffSample d),
                                          ENNReal.ofReal
                                              (step3FirstTerm Cd M m R omega s
                                                (lFreeGradSlot m (tailSeriesGauge m) R omega)) ^
                                            q ∂(↑(Cutoff.cutoffSampleLaw M) : Measure
                                              (Cutoff.CutoffSample d)) ≤
                                        ENNReal.ofReal (Cd * A1 * (q * (M.gamma * (s⁻¹ * s⁻¹)))) ^
                                          q)
      (Cr2 A2 : ℝ) (_ : (0 : ℝ) < Cr2)
      (_ :
        ∀ (M : ABKModel d),
          Disorder.cstar M = cstar →
            M.gamma ≤ Cr2⁻¹ ^ (10 : ℕ) →
              M.gamma ≤ (1 / 8 : ℝ) →
                ∀ (Cd : ℝ),
                  (0 : ℝ) ≤ Cd →
                    ∀ (m : ℤ) (R : TriadicCube d),
                      R.scale ≤ m →
                        ∀ (q : ℝ),
                          (1 : ℝ) ≤ q →
                            (8 : ℝ) * q ≤ M.gamma⁻¹ →
                              ∫⁻ (omega : Cutoff.CutoffSample d),
                                  ENNReal.ofReal
                                      (step3SecondTerm Cd M m R omega (lFreeGradSlot m
                                        (tailSeriesGauge m) R omega)
                                        (lFreeValueSlot m (tailSeriesGauge m) R omega)) ^
                                    q ∂(↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample
                                      d)) ≤
                                ENNReal.ofReal
                                    (Cd * A2 *
                                      (q *
                                        ((M.gamma * ((↑m : ℝ) - (↑R.scale : ℝ)) + M.gamma) *
                                          (3 : ℝ) ^ ((2 : ℝ) * (M.gamma * ((↑m : ℝ) - (↑R.scale :
                                            ℝ))))))) ^
                                  q)
      (Cr3 A3 : ℝ) (_ : (0 : ℝ) < Cr3)
      (_ :
        ∀ (M : ABKModel d),
          Disorder.cstar M = cstar →
            M.gamma ≤ Cr3⁻¹ ^ (10 : ℕ) →
              M.gamma ≤ (1 / 8 : ℝ) →
                ∀ (Cd : ℝ),
                  (0 : ℝ) ≤ Cd →
                    ∀ (m : ℤ) (R : TriadicCube d),
                      R.scale ≤ m →
                        ∀ (q : ℝ),
                          (1 : ℝ) ≤ q →
                            (8 : ℝ) * q ≤ M.gamma⁻¹ →
                              ∫⁻ (omega : Cutoff.CutoffSample d),
                                  ENNReal.ofReal
                                      (step3ThirdTerm Cd M m R omega (lFreeGradSlot m
                                        (tailSeriesGauge m) R omega)) ^
                                    q ∂(↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample
                                      d)) ≤
                                ENNReal.ofReal (Cd * A3 * (q * M.gamma)) ^ q)
      (M : ABKModel d) (_ : Disorder.cstar M = cstar)
      (_ : M.gamma ≤ (max (max (max Cr1 Cr2) (max Cr3 (3 : ℝ))) (max (Cd * (A1 + A3)) (Cd *
        A2)))⁻¹ ^ (10 : ℕ)) (m n : ℤ)
      (_ : n ≤ m) (s : ℝ)
      (_ :
        s ∈
          Set.Icc (max (max (max Cr1 Cr2) (max Cr3 (3 : ℝ))) (max (Cd * (A1 + A3)) (Cd * A2)) ^ (2
            : ℕ) * √M.gamma)
            (1 / 4 : ℝ))
      (p : ℝ)
      (_ :
        p ∈
          Set.Icc ((2 : ℝ) * (↑d : ℝ) * s⁻¹)
            ((max (max (max Cr1 Cr2) (max Cr3 (3 : ℝ))) (max (Cd * (A1 + A3)) (Cd * A2)))⁻¹ *
              M.gamma⁻¹ * s))
      (l : ℕ) (R : TriadicCube d) (_ : R ∈ descendantsAtScale (originCube d m) (n - (↑l : ℤ))) (_
        : (2 : ℕ) ≤ d),
      (0 : ℝ) < M.gamma ∧
        M.gamma ≤ (1 / 8 : ℝ) ∧
          (0 : ℝ) < s ∧
            (4 : ℝ) ≤ s⁻¹ ∧
              (1 : ℝ) ≤ p / (2 : ℝ) ∧
                (0 : ℝ) < p / (2 : ℝ) ∧
                  (↑m : ℝ) - (↑R.scale : ℝ) = (↑m : ℝ) - (↑n : ℝ) + (↑l : ℝ) ∧
                    (0 : ℝ) ≤ (↑m : ℝ) - (↑R.scale : ℝ) ∧
                      ∫⁻ (omega : Cutoff.CutoffSample d),
                            ENNReal.ofReal (step3FirstTerm Cd M m R omega s (lFreeGradSlot m
                              (tailSeriesGauge m) R omega)) ^
                              (p / (2 : ℝ)) ∂(↑(Cutoff.cutoffSampleLaw M) : Measure
                                (Cutoff.CutoffSample d)) ≤
                          ENNReal.ofReal (Cd * A1 * (p / (2 : ℝ) * (M.gamma * (s⁻¹ * s⁻¹)))) ^ (p
                            / (2 : ℝ)) ∧
                        ∫⁻ (omega : Cutoff.CutoffSample d),
                              ENNReal.ofReal
                                  (step3SecondTerm Cd M m R omega (lFreeGradSlot m
                                    (tailSeriesGauge m) R omega)
                                    (lFreeValueSlot m (tailSeriesGauge m) R omega)) ^
                                (p / (2 : ℝ)) ∂(↑(Cutoff.cutoffSampleLaw M) : Measure
                                  (Cutoff.CutoffSample d)) ≤
                            ENNReal.ofReal
                                (Cd * A2 *
                                  (p / (2 : ℝ) *
                                    ((M.gamma * ((↑m : ℝ) - (↑R.scale : ℝ)) + M.gamma) *
                                      (3 : ℝ) ^ ((2 : ℝ) * (M.gamma * ((↑m : ℝ) - (↑R.scale :
                                        ℝ))))))) ^
                              (p / (2 : ℝ)) ∧
                          ∫⁻ (omega : Cutoff.CutoffSample d),
                                ENNReal.ofReal
                                    (step3ThirdTerm Cd M m R omega (lFreeGradSlot m
                                      (tailSeriesGauge m) R omega)) ^
                                  (p / (2 : ℝ)) ∂(↑(Cutoff.cutoffSampleLaw M) : Measure
                                    (Cutoff.CutoffSample d)) ≤
                              ENNReal.ofReal (Cd * A3 * (p / (2 : ℝ) * M.gamma)) ^ (p / (2 : ℝ)) ∧
                            (0 : ℝ) ≤ Cd * A1 * (p / (2 : ℝ) * (M.gamma * (s⁻¹ * s⁻¹))) ∧
                              (0 : ℝ) ≤ (3 : ℝ) ^ ((2 : ℝ) * (M.gamma * ((↑m : ℝ) - (↑R.scale :
                                ℝ)))) := by
  intro d _ _ Cd hCd Cr1 A1 hCr1 hA1 hfirst Cr2 A2 hCr2 hsecond Cr3 A3 hCr3 hthird M hcs hreg m n
    _ s hsmem p hpmem l R hR hd2
  have hgam0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have h3le : (3 : ℝ) ≤ max (max (max Cr1 Cr2) (max Cr3 3))
      (max (Cd * (A1 + A3)) (Cd * A2)) :=
    le_trans (le_trans (le_max_right Cr3 3) (le_max_right _ _)) (le_max_left _ _)
  -- the window arithmetic
  have hK0 : (0 : ℝ) < max (max (max Cr1 Cr2) (max Cr3 3))
      (max (Cd * (A1 + A3)) (Cd * A2)) := by linarith only [h3le]
  have hgam18 : M.gamma ≤ 1 / 8 := by
    have hinv : (max (max (max Cr1 Cr2) (max Cr3 3))
        (max (Cd * (A1 + A3)) (Cd * A2)))⁻¹ ≤ (3 : ℝ)⁻¹ :=
      inv_anti₀ (by norm_num) h3le
    have hpow : ((max (max (max Cr1 Cr2) (max Cr3 3))
        (max (Cd * (A1 + A3)) (Cd * A2)))⁻¹) ^ (10 : ℕ) ≤ ((3 : ℝ)⁻¹) ^ (10 : ℕ) :=
      pow_le_pow_left₀ (inv_nonneg.mpr hK0.le) hinv 10
    have hnum : ((3 : ℝ)⁻¹) ^ (10 : ℕ) ≤ 1 / 8 := by norm_num
    linarith only [hreg, hpow, hnum]
  have hgam1 : M.gamma ≤ 1 := by linarith only [hgam18]
  have hs1 : s ≤ 1 / 4 := hsmem.2
  have hsqgam : M.gamma ≤ Real.sqrt M.gamma := by
    have h1 : Real.sqrt M.gamma ≤ 1 := by
      have h := Real.sqrt_le_sqrt hgam1
      rwa [Real.sqrt_one] at h
    have hid : Real.sqrt M.gamma * Real.sqrt M.gamma = M.gamma :=
      Real.mul_self_sqrt hgam0.le
    have hstep := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg M.gamma)
    rw [mul_one] at hstep
    linarith only [hid, hstep]
  have h8gam : 8 * M.gamma ≤ s := by
    have hK2 : (9 : ℝ) ≤ (max (max (max Cr1 Cr2) (max Cr3 3))
        (max (Cd * (A1 + A3)) (Cd * A2))) ^ (2 : ℕ) := by
      have h := mul_le_mul h3le h3le (by norm_num) (by linarith only [h3le])
      have hid : (max (max (max Cr1 Cr2) (max Cr3 3))
          (max (Cd * (A1 + A3)) (Cd * A2))) ^ (2 : ℕ) =
          max (max (max Cr1 Cr2) (max Cr3 3)) (max (Cd * (A1 + A3)) (Cd * A2)) *
            max (max (max Cr1 Cr2) (max Cr3 3)) (max (Cd * (A1 + A3)) (Cd * A2)) := by
        ring
      linarith only [h, hid]
    have hstep : (9 : ℝ) * Real.sqrt M.gamma ≤
        (max (max (max Cr1 Cr2) (max Cr3 3))
          (max (Cd * (A1 + A3)) (Cd * A2))) ^ (2 : ℕ) * Real.sqrt M.gamma :=
      mul_le_mul_of_nonneg_right hK2 (Real.sqrt_nonneg _)
    have hstep2 : (8 : ℝ) * M.gamma ≤ 9 * Real.sqrt M.gamma := by
      linarith only [hsqgam, Real.sqrt_nonneg M.gamma]
    linarith only [hstep, hstep2, hsmem.1]
  have hs : (0 : ℝ) < s := by linarith only [h8gam, hgam0]
  have hsinv : (4 : ℝ) ≤ s⁻¹ := by
    have h := mul_le_mul_of_nonneg_left hs1 (inv_pos.mpr hs).le
    rw [inv_mul_cancel₀ (ne_of_gt hs)] at h
    have h2 : s⁻¹ * (1 / 4) ≤ s⁻¹ * (1 / 4) := le_rfl
    have h3 : (1 : ℝ) ≤ s⁻¹ * (1 / 4) := h
    linarith only [h3]
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd2
  have hp1 : 2 * (d : ℝ) * s⁻¹ ≤ p := hpmem.1
  have hq : (1 : ℝ) ≤ p / 2 := by
    have hstep : (2 : ℝ) * 2 * 4 ≤ 2 * (d : ℝ) * s⁻¹ := by
      have ha : (2 : ℝ) * 2 ≤ 2 * (d : ℝ) := by linarith only [hdR]
      have hb := mul_le_mul ha hsinv (by norm_num) (by linarith only [hdR])
      linarith only [hb]
    linarith only [hp1, hstep]
  have hq0 : (0 : ℝ) < p / 2 := by linarith only [hq]
  have hp0 : (0 : ℝ) < p := by linarith only [hq0]
  have h8q := @perCubeMoments_admissibleExponent (d) (Cd) (Cr1) (A1) (Cr2) (A2) (Cr3) (A3) (M) (s)
    (p) (hpmem) (hgam0) (h3le) (hs1) (hs)
  -- the descendant cube's scale
  have hscale : R.scale = n - (l : ℤ) := scale_eq_of_mem_descendantsAtScale hR
  have hkm : R.scale ≤ m := by
    rw [hscale]
    omega
  have ht : (m : ℝ) - (R.scale : ℝ) = ((m : ℝ) - (n : ℝ)) + (l : ℝ) := by
    rw [hscale]
    push_cast
    ring
  have ht0 : (0 : ℝ) ≤ (m : ℝ) - (R.scale : ℝ) := by
    have hcast : (R.scale : ℝ) ≤ (m : ℝ) := by exact_mod_cast hkm
    linarith only [hcast]
  -- the three regimes
  have hregOf : ∀ C : ℝ, 0 < C →
      C ≤ max (max (max Cr1 Cr2) (max Cr3 3)) (max (Cd * (A1 + A3)) (Cd * A2)) →
      M.gamma ≤ (C⁻¹) ^ (10 : ℕ) := by
    intro C hC hCle
    refine le_trans hreg ?_
    exact pow_le_pow_left₀ (inv_nonneg.mpr hK0.le) (inv_anti₀ hC hCle) 10
  have hreg1 := hregOf Cr1 hCr1
    (le_trans (le_trans (le_max_left Cr1 Cr2) (le_max_left _ _)) (le_max_left _ _))
  have hreg2 := hregOf Cr2 hCr2
    (le_trans (le_trans (le_max_right Cr1 Cr2) (le_max_left _ _)) (le_max_left _ _))
  have hreg3 := hregOf Cr3 hCr3
    (le_trans (le_trans (le_max_left Cr3 3) (le_max_right _ _)) (le_max_left _ _))
  -- the three per-summand moments
  have hm1 := hfirst M hcs hreg1 hgam18 Cd hCd.le s hs hs1 h8gam m R hkm (p / 2) hq h8q
  have hm2 := hsecond M hcs hreg2 hgam18 Cd hCd.le m R hkm (p / 2) hq h8q
  have hm3 := hthird M hcs hreg3 hgam18 Cd hCd.le m R hkm (p / 2) hq h8q
  -- the six-way split
  have hR1nn : (0 : ℝ) ≤ Cd * A1 * (p / 2 * (M.gamma * (s⁻¹ * s⁻¹))) := by
    have hsi : (0 : ℝ) < s⁻¹ := inv_pos.mpr hs
    have h1 : (0 : ℝ) ≤ Cd * A1 := mul_nonneg hCd.le hA1.le
    have h2 : (0 : ℝ) ≤ p / 2 * (M.gamma * (s⁻¹ * s⁻¹)) := by positivity
    exact mul_nonneg h1 h2
  have hwt0 : (0 : ℝ) ≤ (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (R.scale : ℝ)))) :=
    Real.rpow_nonneg (by norm_num) _
  exact ⟨hgam0, hgam18, hs, hsinv, hq, hq0, ht, ht0, hm1, hm2, hm3, hR1nn, hwt0⟩

/-- **`hcube`, discharged.**

For every positive Step-3 display constant there is a constant `K` such that, in
the anchor's own window, the `p/2`-th moment of the `L`-free Step-3 majorant at
every descendant cube is at most the three-shape majorant
`minkowskiScaleMajorant K p γ s (m−n) l` raised to the `p/2`.

This is Step 5's inner (Hölder) half, in full. -/
theorem exists_perCubeMoments (d : ℕ) [NeZero d] (cstar : ℝ) (hcstar : 0 < cstar)
    (Cd : ℝ) (hCd : 0 < Cd) :
    ∃ K : ℝ, 0 < K ∧
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
                    ((m : ℝ) - (n : ℝ)) l) ^ (p / 2) := by
  classical
  obtain ⟨Cr1, A1, hCr1, hA1, hfirst⟩ :=
    exists_lintegral_rpow_step3FirstTerm_slot d cstar hcstar
  obtain ⟨Cr2, A2, hCr2, hA2, hsecond⟩ :=
    exists_lintegral_rpow_step3SecondTerm_slot d cstar hcstar
  obtain ⟨Cr3, A3, hCr3, hA3, hthird⟩ :=
    exists_lintegral_rpow_step3ThirdTerm_slot d cstar hcstar
  refine ⟨max (max (max Cr1 Cr2) (max Cr3 3)) (max (Cd * (A1 + A3)) (Cd * A2)), ?_, ?_⟩
  · exact lt_of_lt_of_le hCr1
      (le_trans (le_trans (le_max_left Cr1 Cr2) (le_max_left _ _)) (le_max_left _ _))
  intro M hcs hreg m n hnm hwin s hsmem p hpmem l R hR
  have hd2 : (2 : ℕ) ≤ d := M.shellPrefix.dimension
  obtain ⟨hgam0, hgam18, hs, hsinv, hq, hq0, ht, ht0, hm1, hm2, hm3, hR1nn, hwt0⟩ :=
    @boundsEaLProviderFinal_comparisonBounds1 (d) (by infer_instance) (cstar) (Cd) (hCd) (Cr1)
      (A1) (hCr1) (hA1) (hfirst) (Cr2) (A2) (hCr2) (hsecond) (Cr3) (A3) (hCr3) (hthird) (M) (hcs)
        (hreg) (m) (n) (hnm) (s) (hsmem) (p) (hpmem) (l) (R) (hR) (hd2)
  have hR2nn : (0 : ℝ) ≤ Cd * A2 * (p / 2 *
      ((M.gamma * ((m : ℝ) - (R.scale : ℝ)) + M.gamma) *
        (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (R.scale : ℝ)))))) := by
    have h1 : (0 : ℝ) ≤ Cd * A2 := mul_nonneg hCd.le hA2.le
    have hslot : (0 : ℝ) ≤ (M.gamma * ((m : ℝ) - (R.scale : ℝ)) + M.gamma) *
        (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (R.scale : ℝ)))) := by
      refine mul_nonneg ?_ hwt0
      have := mul_nonneg hgam0.le ht0
      linarith only [this, hgam0]
    exact mul_nonneg h1 (mul_nonneg (by linarith only [hq0]) hslot)
  have hR3nn : (0 : ℝ) ≤ Cd * A3 * (p / 2 * M.gamma) := by
    have h1 : (0 : ℝ) ≤ Cd * A3 := mul_nonneg hCd.le hA3.le
    exact mul_nonneg h1 (mul_nonneg (by linarith only [hq0]) hgam0.le)
  have hsix := lintegral_rpow_lFreeStep3Majorant_le_of_summands M Cd m R s hq
    (lFreeGradSlot m (tailSeriesGauge m)) (lFreeValueSlot m (tailSeriesGauge m))
    hR1nn hR2nn hR3nn
    (aemeasurable_step3FirstTerm M Cd m R hs hgam18)
    (aemeasurable_step3SecondTerm M Cd m R hgam18)
    (aemeasurable_step3ThirdTerm M Cd m R) hm1 hm2 hm3
  refine le_trans hsix ?_
  refine ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal ?_) hq0.le
  -- the scalar comparison against the three named shapes
  have hKA13 : Cd * (A1 + A3) ≤ max (max (max Cr1 Cr2) (max Cr3 3))
      (max (Cd * (A1 + A3)) (Cd * A2)) :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hKA2 : Cd * A2 ≤ max (max (max Cr1 Cr2) (max Cr3 3))
      (max (Cd * (A1 + A3)) (Cd * A2)) :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have hsi : (0 : ℝ) < s⁻¹ := inv_pos.mpr hs
  have hsq1 : (1 : ℝ) ≤ s⁻¹ * s⁻¹ := by
    have h := mul_le_mul hsinv hsinv (by norm_num) (by linarith only [hsinv])
    linarith only [h]
  have hweight : Real.rpow 3 (2 * M.gamma * (((m : ℝ) - (n : ℝ)) + (l : ℝ))) =
      (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (R.scale : ℝ)))) := by
    change (3 : ℝ) ^ (2 * M.gamma * (((m : ℝ) - (n : ℝ)) + (l : ℝ))) =
      (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (R.scale : ℝ))))
    rw [ht]
    congr 1
    ring
  rw [minkowskiScaleMajorant, hweight]
  have hthirdSlot : Cd * A3 * (p / 2 * M.gamma) ≤
      Cd * A3 * (p / 2 * (M.gamma * (s⁻¹ * s⁻¹))) := by
    have hbase : (0 : ℝ) ≤ Cd * A3 * (p / 2) * M.gamma :=
      mul_nonneg (mul_nonneg (mul_nonneg hCd.le hA3.le) (by linarith only [hq0])) hgam0.le
    have hstep := mul_le_mul_of_nonneg_left hsq1 hbase
    have hid1 : Cd * A3 * (p / 2) * M.gamma * 1 = Cd * A3 * (p / 2 * M.gamma) := by ring
    have hid2 : Cd * A3 * (p / 2) * M.gamma * (s⁻¹ * s⁻¹) =
        Cd * A3 * (p / 2 * (M.gamma * (s⁻¹ * s⁻¹))) := by ring
    linarith only [hstep, hid1, hid2]
  have hbig1 : Cd * A1 * (p / 2 * (M.gamma * (s⁻¹ * s⁻¹))) +
      Cd * A3 * (p / 2 * (M.gamma * (s⁻¹ * s⁻¹))) ≤
      max (max (max Cr1 Cr2) (max Cr3 3)) (max (Cd * (A1 + A3)) (Cd * A2)) *
        (p / 2) * (M.gamma * (s⁻¹ * s⁻¹)) := by
    have hbase : (0 : ℝ) ≤ p / 2 * (M.gamma * (s⁻¹ * s⁻¹)) := by positivity
    have hstep := mul_le_mul_of_nonneg_right hKA13 hbase
    have hid : Cd * (A1 + A3) * (p / 2 * (M.gamma * (s⁻¹ * s⁻¹))) =
        Cd * A1 * (p / 2 * (M.gamma * (s⁻¹ * s⁻¹))) +
          Cd * A3 * (p / 2 * (M.gamma * (s⁻¹ * s⁻¹))) := by ring
    have hid2 : max (max (max Cr1 Cr2) (max Cr3 3))
        (max (Cd * (A1 + A3)) (Cd * A2)) * (p / 2 * (M.gamma * (s⁻¹ * s⁻¹))) =
        max (max (max Cr1 Cr2) (max Cr3 3)) (max (Cd * (A1 + A3)) (Cd * A2)) *
          (p / 2) * (M.gamma * (s⁻¹ * s⁻¹)) := by ring
    linarith only [hstep, hid, hid2]
  have hbig2 : Cd * A2 * (p / 2 *
      ((M.gamma * ((m : ℝ) - (R.scale : ℝ)) + M.gamma) *
        (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (R.scale : ℝ)))))) ≤
      max (max (max Cr1 Cr2) (max Cr3 3)) (max (Cd * (A1 + A3)) (Cd * A2)) *
        (p / 2) *
        (M.gamma * ((m : ℝ) - (R.scale : ℝ)) *
            (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (R.scale : ℝ)))) +
          M.gamma * (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (R.scale : ℝ))))) := by
    have hslot : (0 : ℝ) ≤ p / 2 *
        ((M.gamma * ((m : ℝ) - (R.scale : ℝ)) + M.gamma) *
          (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (R.scale : ℝ))))) := by
      refine mul_nonneg (by linarith only [hq0]) (mul_nonneg ?_ hwt0)
      have := mul_nonneg hgam0.le ht0
      linarith only [this, hgam0]
    have hstep := mul_le_mul_of_nonneg_right hKA2 hslot
    have hid : max (max (max Cr1 Cr2) (max Cr3 3))
        (max (Cd * (A1 + A3)) (Cd * A2)) *
        (p / 2 * ((M.gamma * ((m : ℝ) - (R.scale : ℝ)) + M.gamma) *
          (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (R.scale : ℝ)))))) =
        max (max (max Cr1 Cr2) (max Cr3 3)) (max (Cd * (A1 + A3)) (Cd * A2)) *
          (p / 2) *
          (M.gamma * ((m : ℝ) - (R.scale : ℝ)) *
              (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (R.scale : ℝ)))) +
            M.gamma * (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (R.scale : ℝ))))) := by ring
    linarith only [hstep, hid]
  have hfinal : 2 * (max (max (max Cr1 Cr2) (max Cr3 3))
      (max (Cd * (A1 + A3)) (Cd * A2)) * (p / 2) * (M.gamma * (s⁻¹ * s⁻¹)) +
      max (max (max Cr1 Cr2) (max Cr3 3)) (max (Cd * (A1 + A3)) (Cd * A2)) *
        (p / 2) *
        (M.gamma * ((m : ℝ) - (R.scale : ℝ)) *
            (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (R.scale : ℝ)))) +
          M.gamma * (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (R.scale : ℝ)))))) =
      max (max (max Cr1 Cr2) (max Cr3 3)) (max (Cd * (A1 + A3)) (Cd * A2)) * p *
        (M.gamma * (s⁻¹ * s⁻¹) +
          (M.gamma * (((m : ℝ) - (n : ℝ)) + (l : ℝ)) *
              (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (R.scale : ℝ)))) +
            M.gamma * (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (R.scale : ℝ)))))) := by
    rw [← ht]
    ring
  linarith only [hbig1, hbig2, hthirdSlot, hfinal]

/-! ## 2. The provider-final -/

/-- **The provider-final, unconditional.** -/
theorem bounds_mathcal_E_aL_provider
    (d : ℕ) (cstar : ℝ) (_hcstar : 0 < cstar) :
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
                        Real.sqrt M.gamma) ^ p
    := by
  refine bounds_mathcal_E_aL_provider_of_perCubeMoments d cstar _hcstar (fun hd => ?_)
  have : NeZero d := ⟨by omega⟩
  exact fun Cd hCd => exists_perCubeMoments d cstar _hcstar Cd hCd

end

end Algsuperdiff.Section4.Provider.BoundsEaL
