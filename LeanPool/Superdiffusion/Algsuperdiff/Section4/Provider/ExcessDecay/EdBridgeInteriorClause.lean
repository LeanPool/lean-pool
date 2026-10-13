/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.EdBridgeFolds

/-!
# EdBridgeInteriorClause

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The one-step off the anchor's interior clause (two legs only)

The anchored interior one-step consumes the anchor's general clause,
which keeps the `∇h` terms because the boundary regime needs them.  On the
interior branch those terms are dead weight, and worse: the flat ungated leg
`C s^{-6} 3^{n-2} ‖∇h‖_{L²}` has **no decay in `n`**, so its window sum is
`(m-n+1)`-linear and the Step-5 `δ`-budget cannot absorb it.

The anchor's second clause — the frontier-empty specialization — carries **no
`∇h` legs at all**:

```text
   1_{𝒢(n+2,z; s/8, 1/2)} ‖u − v‖_{L²(x+□_n)}
     ≤ C s^{-4} 𝓔_{n+2} ‖u − (u)_{(z+□_{n+2})∩□_m}‖_{L²((z+□_{n+2})∩□_m)}
       + C s^{-19/2} σ_n^{-1} 3^{(1+s)n} [g]_{H^s((z+□_{n+2})∩□_m)} ,
```

gated at the bare parent image `((z+□_{n+2}) ∩ ∂□_m = ∅)`.  This module consumes
that clause at the excess-decay window choice and delivers the **two-leg**
one-step display, which removes that obstruction on the interior branch.

## The three indices this route fixes

At the excess-decay instantiation (anchor index `n-2`, clamped centre `y`) the interior clause
reads its event, its flux representative and its display window all at `n - 2 + 2 = n`:

* the supply event is `𝒢(n, z; s/8, (s/8)√δ)` — **the printed gate of
  `l.excess.decay.good.scales` itself**, not the general clause's `n+1`;
* the oscillation leg lives on `(z+□_n) ∩ □_m` — the **same** window the
  contraction's excess is read on when `x := z`, so no window move arises at
  all on this branch;
* the flux representative is at index `n`, the `σ` weight and the `3`-powers at `n-2`.

## The gate, and what it costs

The clause's gate is on the bare parent image, `(z+□_n) ∩ ∂□_m = ∅`.  It is
strictly stronger than the one-step's own interior gate `(x+□_{n-2}) ⊆ □_m` (which it implies,
via `x ∈ (z+□_{n-3}) ∩ □_m` and `3^{n-3}/2 + 3^{n-2}/2 < 3^n/2`), and it is
exactly the gate the frozen statement's own design note names: the terminal
consumer supplies it from `z ∈ □_{m-1}`, matching the manuscript's indicator
`1_{z ∉ □_{m-1}}`.

## The event-free entry

Nothing about the analysis changes — the event enters the proved chain only
through `le_of_indicator_goodEventAt_le`, and this module strips the indicator
at its own (printed) index instead of the general clause's.

## References

* ABK26, `l.harmonic.approximation.good.scales`, (the anchor; the interior
  clause); `l.excess.decay.good.scales`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open HCPolySupport Algsuperdiff.Section4.Support MeasureTheory InnerProductSpace
open Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The two-leg `B.toReal` expansion -/

/-- The two-leg twin of the four-leg `B.toReal` expansion: the interior
clause's display has no in-bracket companion and no `∇h` legs.  Unconditional. -/
theorem toReal_ofReal_mul_add_two_le {c₁ c₂ : ℝ} (X Y : ℝ≥0∞) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) :
    (ENNReal.ofReal c₁ * X + ENNReal.ofReal c₂ * Y).toReal ≤ c₁ * X.toReal + c₂ * Y.toReal := by
  have hX : (ENNReal.ofReal c₁ * X).toReal = c₁ * X.toReal := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc₁]
  have hY : (ENNReal.ofReal c₂ * Y).toReal = c₂ * Y.toReal := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc₂]
  have h : (ENNReal.ofReal c₁ * X + ENNReal.ofReal c₂ * Y).toReal
      ≤ (ENNReal.ofReal c₁ * X).toReal + (ENNReal.ofReal c₂ * Y).toReal :=
    ENNReal.toReal_add_le
  linarith only [h, hX, hY]

/-- Finiteness of the two-leg display, from the finiteness of its two carriers. -/
theorem ofReal_mul_add_two_ne_top {c₁ c₂ : ℝ} {X Y : ℝ≥0∞} (hX : X ≠ ⊤) (hY : Y ≠ ⊤) :
    ENNReal.ofReal c₁ * X + ENNReal.ofReal c₂ * Y ≠ ⊤ :=
  ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hX,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hY⟩

/-! ## 2. The event-free interior one-step -/

/-- `OneStepSchauderComposeInterior.excessDecay_oneStep_interior_of_weaklyHarmonic` with its `(hmem,
hharm)`
pair replaced by the bound they exist to produce.  The event plays no analytic role in the
chain; stripping the indicator is the caller's business, and this module's caller does it at the
interior clause's own (printed) index. -/
theorem excessDecay_oneStep_interior_of_pathwiseBound [NeZero d] (hd : d ≠ 0) {m n : ℤ}
    {k : ℕ} (hk : 3 ≤ k) {x : Vec d} (hx : x ∈ openCubeSet (originCube d m)) (hnm : n - 1 ≤ m)
    (hcube : (fun y => x + y) '' openCubeSet (originCube d (n - 2)) ⊆
      openCubeSet (originCube d m))
    {u : Vec d → ℝ} (hu : MemLp u 2 (volume.restrict (truncatedWindow x m n)))
    {w : H1Function ((fun y => wellPlacedCentre x m (n - 2) + y) ''
      openCubeSet (originCube d (n - 2)))}
    (hw : IsWeaklyHarmonicOn ((fun y => wellPlacedCentre x m (n - 2) + y) ''
      openCubeSet (originCube d (n - 2))) w)
    {B : ℝ≥0∞} (hB : B ≠ ⊤)
    (hnorm : MeasureTheory.eLpNorm (fun y => u y - w.toFun y) 2
        (Support.normalizedVolumeMeasureOn
          ((fun y => wellPlacedCentre x m (n - 2) + y) ''
            openCubeSet (originCube d (n - 2)))) ≤ B) :
    affineExcess (truncatedWindow x m (n - (k : ℤ))) u
      ≤ taylorContractionConst d * schauderWindowConst d * windowRatioConst d 2
            * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ)
            * affineExcess (truncatedWindow x m n) u
        + triangleRemainderConst d (schauderWindowConst d) k
            * ((3 : ℝ) ^ (-n) * (Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) * B.toReal))
        + taylorContractionConst d * ((3 : ℝ) ^ (n - (k : ℤ))) ^ (1 / 2 : ℝ) * 0 := by
  have hnm2 : n - 2 ≤ m := by omega
  obtain ⟨v, hvharm, hvmem, hvae⟩ := exists_classicalCompetitor_movedReplacementCube x m n hw
  have hRsub : movedReplacementCube x m n ⊆ truncatedWindow x m n :=
    movedReplacementCube_subset_truncatedWindow hx hnm2
  have hv : MemLp v 2 (volume.restrict (truncatedWindow x m n)) := hvmem.restrict _
  have huR : MemLp u 2 (volume.restrict (movedReplacementCube x m n)) :=
    hu.mono_measure (Measure.restrict_mono hRsub le_rfl)
  have hvR : MemLp v 2 (volume.restrict (movedReplacementCube x m n)) := hvmem.restrict _
  have huv : MemLp (fun y => u y - v y) 2 (volume.restrict (movedReplacementCube x m n)) :=
    huR.sub hvR
  have hharmclass : HarmonicOnNhd (v ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
      ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' truncatedWindow x m (n - 2)) :=
    hvharm.mono (Set.image_mono (truncatedWindow_subset_movedReplacementCube x hnm2))
  -- transfer the pathwise bound from the variational competitor to its representative
  have hN : (fun y => u y - v y)
      =ᵐ[Support.normalizedVolumeMeasureOn (movedReplacementCube x m n)]
        (fun y => u y - w.toFun y) := by
    rw [Support.normalizedVolumeMeasureOn_def]
    refine MeasureTheory.Measure.ae_smul_measure ?_ _
    filter_upwards [hvae] with p hp
    rw [hp]
  have heLp : MeasureTheory.eLpNorm (fun y => u y - v y) 2
        (Support.normalizedVolumeMeasureOn (movedReplacementCube x m n))
      = MeasureTheory.eLpNorm (fun y => u y - w.toFun y) 2
        (Support.normalizedVolumeMeasureOn (movedReplacementCube x m n)) :=
    MeasureTheory.eLpNorm_congr_ae hN
  have hnorm' : MeasureTheory.eLpNorm (fun y => u y - v y) 2
      (Support.normalizedVolumeMeasureOn (movedReplacementCube x m n)) ≤ B := by
    rw [heLp, movedReplacementCube]
    exact hnorm
  have hD : normalizedL2On (movedReplacementCube x m n) (fun y => u y - v y) ≤ B.toReal :=
    normalizedL2On_le_toReal_of_eLpNorm_le (volume_movedReplacementCube_pos x m n)
      (volume_movedReplacementCube_ne_top x m n) huv hB hnorm'
  -- the interior Schauder producer, at `K_h = 0`
  have hsub : truncatedWindow x m (n - 2) ⊆ truncatedWindow x m n :=
    truncatedWindow_mono x m (by omega : n - 2 ≤ n)
  have hvsub : MemLp v 2 (volume.restrict (truncatedWindow x m (n - 2))) :=
    hv.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hintsq : ∀ (c : ℝ) (g : Vec d),
      IntegrableOn (fun y => (v y - affineEval c g y) ^ 2)
        (truncatedWindow x m (n - 2)) volume :=
    fun c g => integrableOn_sub_affineEval_sq_truncatedWindow x hvsub c g
  obtain ⟨K, hK, hint, hgrad, hhol, hschauder⟩ :=
    Schauder.exists_gradientHolder_interior hd hx (by omega : n - 3 ≤ m) hcube hharmclass hintsq
  exact excessDecay_oneStep_of_movedCubeBound hd hk hx hnm hu hv huv hK
    (schauderWindowConst_nonneg d) hint hgrad hhol hschauder hD

/-! ## 3. The anchor's interior clause, applied at the one-step window choice -/

/-- **The anchor's frontier-empty (interior) clause, at the one-step window
choice.**

Same instantiation as the harmonic-approximation anchor bound — anchor
index `n-2`, anchor centre the clamped `wellPlacedCentre x m (n-2)`, both
geometric obligations discharged — but the second conjunct is taken.  Its event, its
flux representative and its display window all read at `n - 2 + 2 = n`, and it
carries **two legs only**: the mean-subtracted oscillation and the force
seminorm.  The gate is the frozen statement's own, on the bare parent image. -/
theorem exists_oneStepAnchorBound_interior (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (s : ℝ), s ∈ Set.Icc (64 * M.gamma) 1 →
        M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
            Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) *
              (C⁻¹ * s ^ (4 : ℕ)) →
        ∀ hs : 0 < s,
        ∀ L m n : ℤ, m ≤ L → n - 2 + 3 ≤ m →
          ∀ x z : Vec d,
            x ∈ truncatedWindow z m (n - 3) →
            z ∈ openCubeSet (originCube d m) →
            ((fun y' => z + y') '' openCubeSet (originCube d n)) ∩
                frontier (openCubeSet (originCube d m)) = ∅ →
            ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
              ∀ (u hdat : H1Function (openCubeSet (originCube d m)))
                (g : Vec d → Vec d),
                IsDirichletSolutionOn
                    (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                    (originCube d m) u hdat g →
                MemLp g 2
                    (normalizedVolumeMeasureOn (openCubeSet (originCube d m))) →
                MemLp (Gagliardo.gagliardoKernel s 2 g) 2
                    (normalizedGagliardoMeasureOn (openCubeSet (originCube d m))) →
                MemLp (Gagliardo.gagliardoKernel s 2 hdat.grad) 2
                    (normalizedGagliardoMeasureOn (openCubeSet (originCube d m))) →
                ∀ (v : H1Function ((fun y => wellPlacedCentre x m (n - 2) + y) ''
                        openCubeSet (originCube d (n - 2))))
                  (w : H10Function ((fun y => wellPlacedCentre x m (n - 2) + y) ''
                        openCubeSet (originCube d (n - 2)))),
                  IsWeaklyHarmonicOn ((fun y => wellPlacedCentre x m (n - 2) + y) ''
                    openCubeSet (originCube d (n - 2))) v →
                  (∀ y, v.toFun y = u.toFun y - w.toH1Function.toFun y) →
                  (∀ y, v.grad y = u.grad y - w.toH1Function.grad y) →
                  ∃ B : ℝ≥0∞, B ≠ ⊤ ∧
                    Set.indicator
                        (Algsuperdiff.Frozen.Section4.goodEventAt M
                          (cgEllipLowerConstant d) n z
                          ⟨s / 8, by linarith only [hs]⟩ (1 / 2))
                        (fun _omega' =>
                          MeasureTheory.eLpNorm (fun y => u.toFun y - v.toFun y) 2
                            (normalizedVolumeMeasureOn
                              ((fun y => wellPlacedCentre x m (n - 2) + y) ''
                                openCubeSet (originCube d (n - 2)))))
                        omega ≤ B ∧
                    B.toReal ≤
                      C * Real.rpow s (-(4 : ℝ)) *
                          fluxCorrectedErrorRepresentative M L n
                            ⟨s / 8, by linarith only [hs]⟩
                            (Cutoff.translateCutoffSample z omega) *
                          (MeasureTheory.eLpNorm
                              (fun y => u.toFun y -
                                HCPolySupport.volumeAverage
                                  (((fun y' => z + y') ''
                                      openCubeSet (originCube d n)) ∩
                                    openCubeSet (originCube d m)) u.toFun) 2
                              (normalizedVolumeMeasureOn
                                (((fun y' => z + y') ''
                                    openCubeSet (originCube d n)) ∩
                                  openCubeSet (originCube d m)))).toReal +
                        C * Real.rpow s (-(19 / 2 : ℝ)) *
                            (Annealed.sigmaBar M (n - 2) : ℝ)⁻¹ *
                            Real.rpow (3 : ℝ) ((1 + s) * ((n - 2 : ℤ) : ℝ)) *
                          (normalizedGagliardoESeminormOn
                            (((fun y' => z + y') ''
                                openCubeSet (originCube d n)) ∩
                              openCubeSet (originCube d m)) s g).toReal := by
  classical
  obtain ⟨C, hC, hclause⟩ :=
    Algsuperdiff.Section4.Provider.ExcessDecay.harmonic_approximation_provider_epsFree d
  refine ⟨C, hC, ?_⟩
  intro M s hsrange hregime hfund hs L m n hmL hnm x z hxz hz hgate
  have hnm2 : n - 2 ≤ m := by omega
  have hym : wellPlacedCentre x m (n - 2) ∈ openCubeSet (originCube d m) :=
    image_add_wellPlacedCentre_subset_openCubeSet x hnm2
      ⟨0, zero_mem_openCubeSet_originCube d (n - 2), by simp⟩
  have hgeom : (fun y => wellPlacedCentre x m (n - 2) + y) ''
      openCubeSet (originCube d (n - 2)) ⊆
      ((fun y => z + y) '' openCubeSet (originCube d (n - 2 + 1))) ∩
        openCubeSet (originCube d m) := by
    have h := image_add_wellPlacedCentre_subset_windowChoice hxz hnm2
    rw [truncatedWindow] at h
    rw [show n - 2 + 1 = n - 1 by ring]
    exact h
  have hWtop := volume_anchorWindow_ne_top (n - 2 + 2) m z
  have hW20 : volume ((((fun y' => z + y') ''
      openCubeSet (originCube d (n - 2 + 2))) ∩
      openCubeSet (originCube d m))) ≠ 0 := volume_anchorWindowInner_ne_zero hgeom
  have := isProbabilityMeasure_normalizedVolumeMeasureOn hW20 hWtop
  have hS4 : (0 : ℝ) ≤ Real.rpow s (-(4 : ℝ)) := Real.rpow_nonneg hs.le _
  have hS192 : (0 : ℝ) ≤ Real.rpow s (-(19 / 2 : ℝ)) := Real.rpow_nonneg hs.le _
  have h3sn : (0 : ℝ) ≤ Real.rpow (3 : ℝ) ((1 + s) * ((n - 2 : ℤ) : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hsgn : (0 : ℝ) ≤ ((Annealed.sigmaBar M (n - 2) : ℝ))⁻¹ :=
    inv_nonneg.mpr (Annealed.sigmaBar M (n - 2)).2.le
  have hgate' : (((fun y' => z + y') ''
        openCubeSet (originCube d (n - 2 + 2))) ∩
      frontier (openCubeSet (originCube d m))) = ∅ := by
    rw [show n - 2 + 2 = n from by ring]
    exact hgate
  filter_upwards [hclause M s hsrange hregime hfund hs L m (n - 2) hmL hnm
    (wellPlacedCentre x m (n - 2)) z hym hz hgeom] with omega hom
  intro u hdat g hsol hgL2 hgW hhW v w hharmv hval hgradv
  obtain ⟨-, hint⟩ := hom u hdat g hsol hgL2 hgW hhW v w hharmv hval hgradv
  have hclauseInt := hint hgate'
  rw [show n - 2 + 2 = n from by ring] at hclauseInt
  -- the anchor's clause (iv) and `H¹` data, read on the interior display window
  have hum : MemLp u.toFun 2
      (normalizedVolumeMeasureOn (openCubeSet (originCube d m))) :=
    memLp_normalizedVolumeMeasureOn_of_restrict
      (volume_openCubeSet_ne_zero (originCube d m)) u.memL2
  have hW2n : volume ((((fun y' => z + y') ''
      openCubeSet (originCube d n)) ∩ openCubeSet (originCube d m))) ≠ 0 := by
    rw [show (n : ℤ) = n - 2 + 2 from by ring]
    exact hW20
  have hu2 : MemLp u.toFun 2
      (normalizedVolumeMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d n)) ∩
          openCubeSet (originCube d m)))) :=
    memLp_normalizedVolumeMeasureOn_subset Set.inter_subset_right
      (volume_openCubeSet_ne_zero (originCube d m))
      (volume_openCubeSet_ne_top (originCube d m)) hW2n hum
  have hg2 : MemLp (Gagliardo.gagliardoKernel s 2 g) 2
      (normalizedGagliardoMeasureOn
        ((((fun y' => z + y') '' openCubeSet (originCube d n)) ∩
          openCubeSet (originCube d m)))) :=
    memLp_normalizedGagliardoMeasureOn_subset Set.inter_subset_right
      (volume_openCubeSet_ne_zero (originCube d m))
      (volume_openCubeSet_ne_top (originCube d m)) hW2n hgW
  have := isProbabilityMeasure_normalizedVolumeMeasureOn hW2n
    (volume_anchorWindow_ne_top n m z)
  refine ⟨_, ofReal_mul_add_two_ne_top
    (hu2.sub (memLp_const _)).eLpNorm_ne_top hg2.eLpNorm_ne_top, hclauseInt, ?_⟩
  exact toReal_ofReal_mul_add_two_le _ _
    (mul_nonneg (mul_nonneg hC.le hS4)
      (fluxCorrectedErrorRepresentative_nonneg _ _ _ _ _))
    (mul_nonneg (mul_nonneg (mul_nonneg hC.le hS192) hsgn) h3sn)

/-! ## 4. The oscillation fold at the interior clause's window -/

/-- ** residue 2 at the interior clause's own window — the `hOsc` slot, T.**

The interior clause reads its oscillation on `(z+□_n) ∩ □_m`, which at the
excess-decay instantiation `x := z` is the very window the contraction's excess
is read on.  The fold is therefore the proved endpoint comparison with the
`3^{-n}` normalizer cancelling the window's own `3^n`:

```text
   3^{-n} ‖u − (u)_{(z+□_n)∩□_m}‖_{L²((z+□_n)∩□_m)} ≤ C_i(d) ( E(u,U_n) + |∇ℓ(u,U_n)| ) .
```

This is exactly the shape
`StepFourCollapseInterface.stepFourDecay_of_edOneStep` asks for in its `hOsc`
binder, at `C_osc := endpointConst d (1/9)`.  On the G route the same slot is
**not** available: there the oscillation lives one scale up, on `(z+□_{n+1}) ∩
□_m`, and no bound by `E(u,U_n) + |∇ℓ(u,U_n)|` can hold (a bump supported in
`U_{n+1} ∖ U_n` leaves the right side unchanged).  See
`EdBridgeStepFour.oscLeg_normalized_le` for the general-clause route's own
(re-indexed) form. -/
theorem oscLeg_normalized_le_interior (hd : d ≠ 0) {m n : ℤ} {z : Vec d}
    (hz : z ∈ openCubeSet (originCube d m)) (hnm : n - 1 ≤ m) {u : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict (truncatedWindow z m n))) {c : ℝ} {g : Vec d}
    (hmin : IsAffineMinimizer (truncatedWindow z m n) u c g) :
    (3 : ℝ) ^ (-n) *
        (eLpNorm (fun y => u y - volumeAverage (truncatedWindow z m n) u) 2
          (normalizedVolumeMeasureOn (truncatedWindow z m n))).toReal
      ≤ endpointConst d (1 / 9 : ℝ)
        * (affineExcess (truncatedWindow z m n) u + slopeMagnitude g) := by
  have h := eLpNorm_sub_average_truncatedWindow_le hd hz hnm hu hmin
  have hid : (3 : ℝ) ^ (-n) * (3 : ℝ) ^ n = 1 := by
    rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
  calc (3 : ℝ) ^ (-n) *
        (eLpNorm (fun y => u y - volumeAverage (truncatedWindow z m n) u) 2
          (normalizedVolumeMeasureOn (truncatedWindow z m n))).toReal
      ≤ (3 : ℝ) ^ (-n) * ((3 : ℝ) ^ n * (endpointConst d (1 / 9 : ℝ) *
          (affineExcess (truncatedWindow z m n) u + slopeMagnitude g))) :=
        mul_le_mul_of_nonneg_left h (zpow_nonneg (by norm_num) _)
    _ = ((3 : ℝ) ^ (-n) * (3 : ℝ) ^ n) * (endpointConst d (1 / 9 : ℝ) *
          (affineExcess (truncatedWindow z m n) u + slopeMagnitude g)) := by ring
    _ = endpointConst d (1 / 9 : ℝ)
          * (affineExcess (truncatedWindow z m n) u + slopeMagnitude g) := by
        rw [hid]; ring

/-! ## 5. The composed two-leg interior one-step -/

/-- **The interior one-step excess-decay contraction off the anchor's interior clause.**

No `hharm`, no `B`, no `∇h` legs, and — unlike the general-clause route — no
`δ` re-pricing: the interior clause's own threshold is the frozen `1/2`, which
the printed supply event `𝒢(n, z; s/8, (s/8)√δ)` reaches from `δ ≤ 1` and `s ≤
1` alone.

The two gates are carried separately: `hgate` is the frozen statement's own frontier-empty
condition on the bare parent image, `hcube` the one-step's interior inclusion.  `hgate` implies
`hcube` mathematically (a connected set meeting `□_m` and missing `∂□_m` lies in `□_m`, and
`x + □_{n-2} ⊆ z + □_n` from `x ∈ z + □_{n-3}`); the implication is NOT formalized here — the
connectedness step is a topological detour with no bearing on the display — so both are
hypotheses. -/
theorem excessDecay_oneStep_interior_anchored_twoLeg (d : ℕ) [NeZero d] (hd : d ≠ 0) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (s : ℝ), s ∈ Set.Icc (64 * M.gamma) 1 →
        M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
            Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) *
              (C⁻¹ * s ^ (4 : ℕ)) →
        ∀ hs : 0 < s,
        ∀ delta : ℝ, delta ≤ 1 →
        ∀ L m n : ℤ, m ≤ L → n - 2 + 3 ≤ m →
          ∀ x z : Vec d,
            x ∈ truncatedWindow z m (n - 3) →
            z ∈ openCubeSet (originCube d m) →
            ((fun y' => z + y') '' openCubeSet (originCube d n)) ∩
                frontier (openCubeSet (originCube d m)) = ∅ →
            (fun y => x + y) '' openCubeSet (originCube d (n - 2)) ⊆
              openCubeSet (originCube d m) →
            ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
              omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
                  (cgEllipLowerConstant d) n z
                  ⟨s / 8, by linarith only [hs]⟩ (s / 8 * Real.sqrt delta) →
                ∀ (u hdat : H1Function (openCubeSet (originCube d m)))
                  (g : Vec d → Vec d),
                  IsDirichletSolutionOn
                      (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                      (originCube d m) u hdat g →
                  MemLp g 2
                      (normalizedVolumeMeasureOn (openCubeSet (originCube d m))) →
                  MemLp (Gagliardo.gagliardoKernel s 2 g) 2
                      (normalizedGagliardoMeasureOn (openCubeSet (originCube d m))) →
                  MemLp (Gagliardo.gagliardoKernel s 2 hdat.grad) 2
                      (normalizedGagliardoMeasureOn (openCubeSet (originCube d m))) →
                  ∀ (v : H1Function ((fun y => wellPlacedCentre x m (n - 2) + y) ''
                          openCubeSet (originCube d (n - 2))))
                    (w : H10Function ((fun y => wellPlacedCentre x m (n - 2) + y) ''
                          openCubeSet (originCube d (n - 2)))),
                    IsWeaklyHarmonicOn ((fun y => wellPlacedCentre x m (n - 2) + y) ''
                      openCubeSet (originCube d (n - 2))) v →
                    (∀ y, v.toFun y = u.toFun y - w.toH1Function.toFun y) →
                    (∀ y, v.grad y = u.grad y - w.toH1Function.grad y) →
                    ∀ k : ℕ, 3 ≤ k →
                      affineExcess (truncatedWindow x m (n - (k : ℤ))) u.toFun ≤
                        taylorContractionConst d * schauderWindowConst d
                            * windowRatioConst d 2
                            * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ)
                            * affineExcess (truncatedWindow x m n) u.toFun
                          + triangleRemainderConst d (schauderWindowConst d) k
                            * ((3 : ℝ) ^ (-n) *
                              (Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) *
                                (C * Real.rpow s (-(4 : ℝ)) *
                                    fluxCorrectedErrorRepresentative M L n
                                      ⟨s / 8, by linarith only [hs]⟩
                                      (Cutoff.translateCutoffSample z omega) *
                                    (MeasureTheory.eLpNorm
                                        (fun y => u.toFun y -
                                          HCPolySupport.volumeAverage
                                            (((fun y' => z + y') ''
                                                openCubeSet (originCube d n)) ∩
                                              openCubeSet (originCube d m))
                                            u.toFun) 2
                                        (normalizedVolumeMeasureOn
                                          (((fun y' => z + y') ''
                                              openCubeSet (originCube d n)) ∩
                                            openCubeSet (originCube d m)))).toReal +
                                  C * Real.rpow s (-(19 / 2 : ℝ)) *
                                      (Annealed.sigmaBar M (n - 2) : ℝ)⁻¹ *
                                      Real.rpow (3 : ℝ)
                                        ((1 + s) * ((n - 2 : ℤ) : ℝ)) *
                                    (normalizedGagliardoESeminormOn
                                      (((fun y' => z + y') ''
                                          openCubeSet (originCube d n)) ∩
                                        openCubeSet (originCube d m)) s g).toReal))) := by
  classical
  obtain ⟨C, hC, hanchor⟩ := exists_oneStepAnchorBound_interior d
  refine ⟨C, hC, ?_⟩
  intro M s hsrange hregime hfund hs delta hdelta1 L m n hmL hnm x z hxz hz hgate hcube
  have hs1 : s ≤ 1 := hsrange.2
  have hxm : x ∈ openCubeSet (originCube d m) :=
    truncatedWindow_subset_domain z m (n - 3) hxz
  have hnm1 : n - 1 ≤ m := by omega
  have hsqrtnn : (0 : ℝ) ≤ Real.sqrt delta := Real.sqrt_nonneg _
  have hsqrtle : Real.sqrt delta ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt hdelta1
  have hep0 : (0 : ℝ) ≤ s / 8 * Real.sqrt delta :=
    mul_nonneg (by linarith only [hs]) hsqrtnn
  have hhalf : s / 8 * Real.sqrt delta ≤ 1 / 2 := by
    have h1 : s / 8 ≤ 1 / 8 := by linarith only [hs1]
    calc s / 8 * Real.sqrt delta ≤ (1 / 8 : ℝ) * 1 :=
          mul_le_mul h1 hsqrtle hsqrtnn (by norm_num)
      _ ≤ 1 / 2 := by norm_num
  filter_upwards [hanchor M s hsrange hregime hfund hs L m n hmL hnm x z hxz hz hgate]
    with omega hom
  intro hmem u hdat g hsol hgL2 hgW hhW v w hharmv hval hgradv k hk
  obtain ⟨B, hB, hharm, hexp⟩ := hom u hdat g hsol hgL2 hgW hhW v w hharmv hval hgradv
  have hnorm := le_of_indicator_goodEventAt_le_of_le hep0 hhalf hmem hharm
  have hu : MemLp u.toFun 2 (volume.restrict (truncatedWindow x m n)) :=
    u.memL2.mono_measure
      (Measure.restrict_mono (truncatedWindow_subset_domain x m n) le_rfl)
  have hmain := excessDecay_oneStep_interior_of_pathwiseBound hd hk hxm hnm1 hcube hu
    hharmv hB hnorm
  have hmain' := (by simpa only [mul_zero, add_zero] using hmain :
    affineExcess (truncatedWindow x m (n - (k : ℤ))) u.toFun ≤
      taylorContractionConst d * schauderWindowConst d * windowRatioConst d 2
          * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ)
          * affineExcess (truncatedWindow x m n) u.toFun
        + triangleRemainderConst d (schauderWindowConst d) k
          * ((3 : ℝ) ^ (-n) * (Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) * B.toReal)))
  exact hmain'.trans
    (add_le_add le_rfl (oneStepRemainder_mono d (schauderWindowConst_nonneg d) k n hexp))

end

end Algsuperdiff.Section4.Provider.ExcessDecay
