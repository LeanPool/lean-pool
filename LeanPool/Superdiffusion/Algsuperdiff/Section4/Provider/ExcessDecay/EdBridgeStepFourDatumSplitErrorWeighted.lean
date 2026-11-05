/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.EdBridgeStepFourDatumSplit
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.EdAssemblyJoinDatumSplitErrorWeighted

/-!
# EdBridgeStepFourDatumSplitErrorWeighted

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The Step-4 bridge's `δ` slot at the error-weighted five-leg expansion

`EdBridgeStepFourDatumSplit.excessDecay_stepFour_slot_general_datumSplit`
runs the residue chain against the datum-split join and packages the remainder
into `EdBridgeStepFour.edBridgeDelta`.  The error-weighted sibling of that join,
`EdAssemblyJoinDatumSplitErrorWeighted.excessDecay_oneStep_anchored_datumSplit_errorWeighted`,
carries as its fifth leg the `𝓔`-multiplied flat `∇h` average in place of
the normalized `L²` datum.  This module is the matching `δ` packaging and
slot:

* `edBridgeDeltaBracketErrorWeighted` — `edBridgeDeltaBracket` with its fourth summand
  replaced by the error-weighted leg
  ```text
     C s^{-6} · 𝓔_{n+1}(τ_z ω) · 3^{n-2} · ‖(∇h)_{U_n}‖ ,
  ```
  every other byte unchanged;
* `edBridgeDeltaErrorWeighted` — the same weight-and-normalizer wrapper `W · (3^{-n} · bracket)`;
* `excessDecay_stepFour_slot_general_datumSplit_errorWeighted` — the Step-4 decay slot at
  every centre, off the error-weighted join, in the shape the error-weighted
  Step-4 collapse and the proved budget composition
  `stepFourDeltaOutErrorWeighted_add_datumLeg_le_boundaryThreeLegs` consume: contraction,
  `ε·|∇ℓ|`, and `δ + datum leg`.

## Why the swap is free

`edBridge_recombine_datum` is generic in the remainder `Rhat`: the datum leg
`Leg` and the four-leg bracket enter only additively, and the `k₀` selection of
`exists_edBridgeStepGen` touches neither.  The error-weighted leg sits in the
bracket's fourth slot on BOTH sides of the recombination's `hBig`, so it cancels
there; the `δ`-gate `hgate`, the `ε` identity and the contraction absorption are
unchanged character for character.

## References

* ABK26, `l.excess.decay.good.scales`; `t.regularity` Step 4.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open HCPolySupport Algsuperdiff.Section4.Support MeasureTheory InnerProductSpace
open Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The error-weighted four-leg bracket and its `δ` -/

/-- The four-leg bracket of the bridge's `δ_j` at the error-weighted clause.

`EdBridgeStepFour.edBridgeDeltaBracket` with the fourth summand — the flat `∇h`
datum leg — carrying the clause's own `𝓔` factor and reading the AV
`‖(∇h)_{U_n}‖` in place of the normalized `L²` norm on `U_{n+1}`.  The
first three summands are unchanged. -/
def edBridgeDeltaBracketErrorWeighted (M : ABKModel d) (C : ℝ) (L m : ℤ) (s : ℝ) (t : {t : ℝ // 0
  < t})
    (z : Vec d) (gflux gradh : Vec d → Vec d) (omega : Cutoff.CutoffSample d) (n : ℤ) : ℝ :=
  C * Real.rpow s (-(4 : ℝ)) *
        fluxCorrectedErrorRepresentative M L (n + 1) t (Cutoff.translateCutoffSample z omega) *
        (Real.rpow s (-(3 / 2 : ℝ)) * Real.rpow (3 : ℝ) ((n - 2 : ℤ) : ℝ) *
          ‖volumeAverageVec (truncatedWindow z m n) gradh‖) +
      C * Real.rpow s (-(7 : ℝ)) * (Annealed.sigmaBar M (n - 2) : ℝ)⁻¹ *
          Real.rpow (3 : ℝ) ((1 + s) * ((n - 2 : ℤ) : ℝ)) *
          (normalizedGagliardoESeminormOn (truncatedWindow z m (n + 1)) s gflux).toReal +
      C * Real.rpow s (-(6 : ℝ)) * Real.rpow (3 : ℝ) ((1 + s) * ((n - 2 : ℤ) : ℝ)) *
          (normalizedGagliardoESeminormOn (truncatedWindow z m (n + 1)) s gradh).toReal +
      C * Real.rpow s (-(6 : ℝ)) *
          fluxCorrectedErrorRepresentative M L (n + 1) t (Cutoff.translateCutoffSample z omega) *
          Real.rpow (3 : ℝ) ((n - 2 : ℤ) : ℝ) *
          ‖volumeAverageVec (truncatedWindow z m n) gradh‖

/-- **The bridge's `δ_j` at `j = n+1`, at the error-weighted clause**: the
error-weighted four-leg bracket at the one-step's own remainder weight and scale
normalizer `3^{-n}`. -/
def edBridgeDeltaErrorWeighted (M : ABKModel d) (C W : ℝ) (L m : ℤ) (s : ℝ) (t : {t : ℝ // 0 < t})
    (z : Vec d) (gflux gradh : Vec d → Vec d) (omega : Cutoff.CutoffSample d) (n : ℤ) : ℝ :=
  W * ((3 : ℝ) ^ (-n) * edBridgeDeltaBracketErrorWeighted M C L m s t z gflux gradh omega n)

/-! ## 2. The Step-4 slot at the error-weighted join -/

/-- **The Step-4 decay slot at every centre, with the printed datum leg,
off the error-weighted anchor.**

`EdBridgeStepFourDatumSplit.excessDecay_stepFour_slot_general_datumSplit` run
against the error-weighted join.  The window hypothesis is the join's own disjunction's
honest binders; the conclusion is the interior slot's, with the `δ` leg now
`edBridgeDeltaErrorWeighted` — the `𝓔`-multiplied flat `∇h` average in the fourth slot —
plus the additive datum summand `edBridgeDatumLeg d (max (schauderWindowConst
d) C_b) k n K_h`. -/
theorem excessDecay_stepFour_slot_general_datumSplit_errorWeighted (d : ℕ) [NeZero d] (hd : d ≠ 0) :
    ∃ C Ccap Cb : ℝ, 0 < C ∧ 0 < Ccap ∧ 0 ≤ Cb ∧ ∃ k₀ : ℕ, 3 ≤ k₀ ∧
      ∀ k : ℕ, k₀ ≤ k →
        ∀ (M : ABKModel d) (s : ℝ), s ∈ Set.Icc (64 * M.gamma) 1 →
          M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
          M.gamma ≤ Ccap⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
          ∀ hs : 0 < s,
          ∀ delta : ℝ, delta ∈ Set.Ioc (0 : ℝ) 1 →
            delta ≤ 64 * (C ^ (2 : ℕ))⁻¹ * s ^ (6 : ℕ) →
            M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
                Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) *
                  (s / 8 * Real.sqrt delta) →
            edBridgeEpsConstGen d (max (schauderWindowConst d) Cb) C k * Ccap *
                  Real.rpow s (-(3 : ℝ)) * Real.sqrt delta ≤
                (1 / 2 : ℝ) * (3 : ℝ) ^ (-(1 / 4 : ℝ) * ((k : ℝ) + 1)) →
            ∀ L m : ℤ, m ≤ L →
              ∀ z : Vec d, z ∈ openCubeSet (originCube d m) →
                ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
                  ∀ n : ℤ, n + 1 ≤ m →
                    omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
                        (cgEllipLowerConstant d) (n + 1) z ⟨s / 8, by linarith only [hs]⟩
                        (s / 8 * Real.sqrt delta) →
                    ∀ (u hdat : H1Function (openCubeSet (originCube d m)))
                      (gflux : Vec d → Vec d),
                      IsDirichletSolutionOn
                          (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                          (originCube d m) u hdat gflux →
                      MemLp gflux 2
                          (normalizedVolumeMeasureOn (openCubeSet (originCube d m))) →
                      MemLp (Gagliardo.gagliardoKernel s 2 gflux) 2
                          (normalizedGagliardoMeasureOn (openCubeSet (originCube d m))) →
                      MemLp (Gagliardo.gagliardoKernel s 2 hdat.grad) 2
                          (normalizedGagliardoMeasureOn (openCubeSet (originCube d m))) →
                      ∀ (v : H1Function ((fun y => wellPlacedCentre z m (n - 2) + y) ''
                              openCubeSet (originCube d (n - 2))))
                        (w : H10Function ((fun y => wellPlacedCentre z m (n - 2) + y) ''
                              openCubeSet (originCube d (n - 2)))),
                        IsWeaklyHarmonicOn ((fun y => wellPlacedCentre z m (n - 2) + y) ''
                          openCubeSet (originCube d (n - 2))) v →
                        (∀ y, v.toFun y = u.toFun y - w.toH1Function.toFun y) →
                        (∀ y, v.grad y = u.grad y - w.toH1Function.grad y) →
                        ∀ Kh : ℝ, 0 ≤ Kh →
                        ((fun y => z + y) '' openCubeSet (originCube d (n - 2)) ⊆
                            openCubeSet (originCube d m) ∨
                          (∃ (i : Fin d) (V v₁ : Vec d → ℝ) (cl : ℝ) (Al : Vec d),
                            (MeetsUpperFace z m (n - 2) i ∨
                              MeetsLowerFace z m (n - 2) i) ∧
                            MemLp v.toFun 2 (volume.restrict (truncatedWindow z m n)) ∧
                            MemLp V 2
                              (volume.restrict (reflectedWindow z m (n - 2))) ∧
                            V =ᵐ[volume.restrict (truncatedWindow z m (n - 2))]
                              (fun y => v.toFun y - affineLift z cl Al y - v₁ y) ∧
                            (∀ᵐ y ∂(volume.restrict (truncatedWindow z m (n - 2))),
                              |v₁ y| ≤ datumResidualBound d n Kh) ∧
                            (∀ l : Fin d, MeetsUpperFace z m (n - 2) l →
                              ∀ y ∈ reflectedWindow z m (n - 2),
                                V (coordFaceReflection
                                  ((1 / 2 : ℝ) * (3 : ℝ) ^ m) l y) = -V y) ∧
                            (∀ l : Fin d, MeetsLowerFace z m (n - 2) l →
                              ∀ y ∈ reflectedWindow z m (n - 2),
                                V (coordFaceReflection
                                  (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) l y) = -V y) ∧
                            HarmonicOnNhd
                              (V ∘
                                (Schauder.toEuc.symm :
                                  EuclideanSpace ℝ (Fin d) → Vec d))
                              ((Schauder.toEuc : Vec d → EuclideanSpace ℝ (Fin d)) ''
                                reflectedWindow z m (n - 2)))) →
                        ∀ (c : ℝ) (gmin : Vec d),
                          IsAffineMinimizer (truncatedWindow z m (n + 1)) u.toFun c gmin →
                          affineExcess (truncatedWindow z m (n + 1 - ((k + 1 : ℕ) : ℤ)))
                              u.toFun ≤
                            (3 : ℝ) ^ (-(1 / 4 : ℝ) * ((k : ℝ) + 1)) *
                                affineExcess (truncatedWindow z m (n + 1)) u.toFun +
                              edBridgeEps M
                                    (edBridgeEpsConstGen d
                                      (max (schauderWindowConst d) Cb) C k) L s
                                    ⟨s / 8, by linarith only [hs]⟩ z omega n *
                                  slopeMagnitude gmin +
                              (edBridgeDeltaErrorWeighted M C
                                  (edBridgeRemWeightGen d
                                    (max (schauderWindowConst d) Cb) k) L m s
                                  ⟨s / 8, by linarith only [hs]⟩ z gflux hdat.grad omega n
                                + edBridgeDatumLeg d
                                    (max (schauderWindowConst d) Cb) k n Kh) := by
  classical
  obtain ⟨C, Cb, hC, hCb, hjoin⟩ := excessDecay_oneStep_anchored_datumSplit_errorWeighted d hd
  obtain ⟨Ccap, hCcap, hcapAe⟩ := ae_errorRepresentative_le_goodEventDeltaSlot d
  obtain ⟨k₀, hk₀, habsorb⟩ := exists_edBridgeStepGen d (max (schauderWindowConst d) Cb)
  refine ⟨C, Ccap, Cb, hC, hCcap, hCb, k₀, hk₀, ?_⟩
  intro k hk M s hsrange hregime hregimecap hs delta hdelta hprice hfundcap hgate L m hmL z hz
  set Cs : ℝ := max (schauderWindowConst d) Cb with hCsdef
  have hCsnn : (0 : ℝ) ≤ Cs :=
    le_trans (schauderWindowConst_nonneg d) (le_max_left _ _)
  have hk3 : 3 ≤ k := le_trans hk₀ hk
  have hrep : s / 8 * Real.sqrt delta ≤ C⁻¹ * s ^ (4 : ℕ) :=
    excessDecayDelta_repriced hC hs.le hprice
  have hpre : (0 : ℝ) ≤ Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) :=
    mul_nonneg (Real.rpow_nonneg (by linarith only [hs]) _) (sq_nonneg _)
  have hfund : M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
      Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * (C⁻¹ * s ^ (4 : ℕ)) :=
    le_trans hfundcap (mul_le_mul_of_nonneg_left hrep hpre)
  rw [ae_all_iff]
  intro n
  by_cases hnm : n + 1 ≤ m
  · have hnm3 : n - 2 + 3 ≤ m := by omega
    have hzmem : z ∈ truncatedWindow z m (n - 3) := mem_truncatedWindow_self (n - 3) hz
    filter_upwards [hjoin M s hsrange hregime hfund hs delta hdelta.2 hprice L m n hmL hnm3
      z z hzmem hz,
      hcapAe M hregimecap s hsrange hs delta hdelta hfundcap (n + 1) z] with omega hom hcapOm
    intro _hnm hmem u hdat gflux hsol hgL2 hgW hhW v w hharmv hval hgradv Kh hKh hwin c gmin hmin
    -- the good-event cap at the supply index, and the join at `x := z`
    have hEcap := hcapOm hmem L (by omega)
    have hmem' : omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
        (cgEllipLowerConstant d) (n - 2 + 3) z ⟨s / 8, by linarith only [hs]⟩
        (s / 8 * Real.sqrt delta) := by
      rw [show n - 2 + 3 = n + 1 from by ring]
      exact hmem
    have hmain := hom hmem' u hdat gflux hsol hgL2 hgW hhW v w hharmv hval hgradv Kh hKh
      hwin k hk3
    simp only [show n - 2 + 3 = n + 1 from by ring, show n - 2 + 2 = n from by ring,
      show (((fun y' : Vec d => z + y') '' openCubeSet (originCube d (n + 1))) ∩
          openCubeSet (originCube d m)) = truncatedWindow z m (n + 1) from rfl,
      show (((fun y' : Vec d => z + y') '' openCubeSet (originCube d n)) ∩
          openCubeSet (originCube d m)) = truncatedWindow z m n from rfl] at hmain
    -- the data of the two windows
    have hu1 : MemLp u.toFun 2 (volume.restrict (truncatedWindow z m (n + 1))) :=
      u.memL2.mono_measure
        (Measure.restrict_mono (truncatedWindow_subset_domain z m (n + 1)) le_rfl)
    have hEj : (0 : ℝ) ≤ affineExcess (truncatedWindow z m (n + 1)) u.toFun :=
      affineExcess_nonneg _ _
    have hCi : (1 : ℝ) ≤ endpointConst d (1 / 9 : ℝ) := one_le_endpointConst (by norm_num)
    have hEcalnn : (0 : ℝ) ≤ fluxCorrectedErrorRepresentative M L (n + 1)
        ⟨s / 8, by linarith only [hs]⟩ (Cutoff.translateCutoffSample z omega) :=
      fluxCorrectedErrorRepresentative_nonneg _ _ _ _ _
    have hCEnn : (0 : ℝ) ≤ C * Real.rpow s (-(4 : ℝ)) *
        fluxCorrectedErrorRepresentative M L (n + 1) ⟨s / 8, by linarith only [hs]⟩
          (Cutoff.translateCutoffSample z omega) :=
      mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg hs.le _)) hEcalnn
    -- residue 2: the oscillation-to-excess fold on `U_{n+1}`
    have hOSC := eLpNorm_sub_average_truncatedWindow_le hd hz (by omega : n + 1 - 1 ≤ m)
      hu1 hmin
    -- residue 3: the one-scale window move
    have hqm := affineExcess_reindex_le z hz (by omega : n + 1 - 1 ≤ m) hu1
    -- residue 4: the contraction absorption at the join's constant
    have hrate : (0 : ℝ) ≤ ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) :=
      Real.rpow_nonneg (zpow_pos (by norm_num) _).le _
    have hAcon : taylorContractionConst d * Cs * windowRatioConst d 2 *
          ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) * affineExcess (truncatedWindow z m n) u.toFun
        ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ (-(1 / 4 : ℝ) * ((k : ℝ) + 1)) *
            affineExcess (truncatedWindow z m (n + 1)) u.toFun := by
      have hpos : (0 : ℝ) ≤ taylorContractionConst d * Cs *
          windowRatioConst d 2 * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) :=
        mul_nonneg (mul_nonneg (mul_nonneg (taylorContractionConst_nonneg d)
          hCsnn) (windowRatioConst_nonneg d 2)) hrate
      have h1 := mul_le_mul_of_nonneg_left hqm hpos
      have h2 := mul_le_mul_of_nonneg_right (habsorb k hk) hEj
      have hid : taylorContractionConst d * Cs * windowRatioConst d 2 *
            ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) *
            (windowRatioConst d 1 * affineExcess (truncatedWindow z m (n + 1)) u.toFun)
          = taylorContractionConst d * Cs * windowRatioConst d 2 *
            windowRatioConst d 1 * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) *
            affineExcess (truncatedWindow z m (n + 1)) u.toFun := by ring
      linarith only [h1, h2, hid]
    -- the two bookkeeping identities and the gate, all through `3^{-n}·3^{n+1}=3`
    have hz3 := zpow_reindex n
    rw [show n + 1 - ((k + 1 : ℕ) : ℤ) = n - (k : ℤ) from by push_cast; ring,
      edBridgeEps, edBridgeEpsConstGen, edBridgeDeltaErrorWeighted, edBridgeRemWeightGen,
      edBridgeDatumLeg]
    refine edBridge_recombine_datum
      (B₁ := C * Ccap * Real.rpow s (-(3 : ℝ)) * Real.sqrt delta *
        ((3 : ℝ) ^ (n + 1) * endpointConst d (1 / 9 : ℝ)))
      (B₂ := C * Real.rpow s (-(4 : ℝ)) *
        fluxCorrectedErrorRepresentative M L (n + 1) ⟨s / 8, by linarith only [hs]⟩
          (Cutoff.translateCutoffSample z omega) *
        ((3 : ℝ) ^ (n + 1) * endpointConst d (1 / 9 : ℝ)))
      (Rhat := edBridgeDeltaBracketErrorWeighted M C L m s ⟨s / 8, by linarith only [hs]⟩ z gflux
        hdat.grad omega n)
      (th₂ := (1 / 2 : ℝ) * (3 : ℝ) ^ (-(1 / 4 : ℝ) * ((k : ℝ) + 1)))
      (triangleRemainderConst_nonneg d hCsnn k)
      (Real.sqrt_nonneg _) (zpow_nonneg (by norm_num) (-n)) hEj hmain ?_ hAcon ?_ ?_ ?_ ?_
    · -- residues 1 and 2 folded into the four-leg bracket
      rw [edBridgeDeltaBracketErrorWeighted]
      have hXnn : (0 : ℝ) ≤ (3 : ℝ) ^ (n + 1) *
          (endpointConst d (1 / 9 : ℝ) * affineExcess (truncatedWindow z m (n + 1)) u.toFun) :=
        mul_nonneg (zpow_nonneg (by norm_num) _)
          (mul_nonneg (by linarith only [hCi]) hEj)
      have hcapmul := rpow_neg_four_mul_le_of_cap (Cc := C) hs hEcap hXnn hC.le
      have hA0 : C * Real.rpow s (-(4 : ℝ)) *
            fluxCorrectedErrorRepresentative M L (n + 1) ⟨s / 8, by linarith only [hs]⟩
              (Cutoff.translateCutoffSample z omega) *
            ((eLpNorm (fun y => u.toFun y -
                  volumeAverage (truncatedWindow z m (n + 1)) u.toFun) 2
                (normalizedVolumeMeasureOn (truncatedWindow z m (n + 1)))).toReal +
              Real.rpow s (-(3 / 2 : ℝ)) * Real.rpow (3 : ℝ) ((n - 2 : ℤ) : ℝ) *
                ‖volumeAverageVec (truncatedWindow z m n) hdat.grad‖)
          ≤ C * Real.rpow s (-(4 : ℝ)) *
            fluxCorrectedErrorRepresentative M L (n + 1) ⟨s / 8, by linarith only [hs]⟩
              (Cutoff.translateCutoffSample z omega) *
            ((3 : ℝ) ^ (n + 1) * (endpointConst d (1 / 9 : ℝ) *
                (affineExcess (truncatedWindow z m (n + 1)) u.toFun + slopeMagnitude gmin)) +
              Real.rpow s (-(3 / 2 : ℝ)) * Real.rpow (3 : ℝ) ((n - 2 : ℤ) : ℝ) *
                ‖volumeAverageVec (truncatedWindow z m n) hdat.grad‖) :=
        mul_le_mul_of_nonneg_left (by linarith only [hOSC]) hCEnn
      have hid1 : C * Real.rpow s (-(4 : ℝ)) *
            fluxCorrectedErrorRepresentative M L (n + 1) ⟨s / 8, by linarith only [hs]⟩
              (Cutoff.translateCutoffSample z omega) *
            ((3 : ℝ) ^ (n + 1) * (endpointConst d (1 / 9 : ℝ) *
                (affineExcess (truncatedWindow z m (n + 1)) u.toFun + slopeMagnitude gmin)) +
              Real.rpow s (-(3 / 2 : ℝ)) * Real.rpow (3 : ℝ) ((n - 2 : ℤ) : ℝ) *
                ‖volumeAverageVec (truncatedWindow z m n) hdat.grad‖)
          = C * Real.rpow s (-(4 : ℝ)) *
              fluxCorrectedErrorRepresentative M L (n + 1) ⟨s / 8, by linarith only [hs]⟩
                (Cutoff.translateCutoffSample z omega) *
              ((3 : ℝ) ^ (n + 1) * (endpointConst d (1 / 9 : ℝ) *
                affineExcess (truncatedWindow z m (n + 1)) u.toFun))
            + (C * Real.rpow s (-(4 : ℝ)) *
                fluxCorrectedErrorRepresentative M L (n + 1) ⟨s / 8, by linarith only [hs]⟩
                  (Cutoff.translateCutoffSample z omega) *
                ((3 : ℝ) ^ (n + 1) * endpointConst d (1 / 9 : ℝ))) * slopeMagnitude gmin
            + C * Real.rpow s (-(4 : ℝ)) *
                fluxCorrectedErrorRepresentative M L (n + 1) ⟨s / 8, by linarith only [hs]⟩
                  (Cutoff.translateCutoffSample z omega) *
                (Real.rpow s (-(3 / 2 : ℝ)) * Real.rpow (3 : ℝ) ((n - 2 : ℤ) : ℝ) *
                  ‖volumeAverageVec (truncatedWindow z m n) hdat.grad‖) := by ring
      have hid2 : C * Ccap * Real.rpow s (-(3 : ℝ)) * Real.sqrt delta *
            ((3 : ℝ) ^ (n + 1) * (endpointConst d (1 / 9 : ℝ) *
              affineExcess (truncatedWindow z m (n + 1)) u.toFun))
          = (C * Ccap * Real.rpow s (-(3 : ℝ)) * Real.sqrt delta *
              ((3 : ℝ) ^ (n + 1) * endpointConst d (1 / 9 : ℝ))) *
            affineExcess (truncatedWindow z m (n + 1)) u.toFun := by ring
      linarith only [hA0, hcapmul, hid1, hid2]
    · -- the `δ`-gate: neither the datum leg nor the error-weighted flat leg appears here
      have hlin : triangleRemainderConst d Cs k *
            ((3 : ℝ) ^ (-n) * (Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) *
              (C * Ccap * Real.rpow s (-(3 : ℝ)) * Real.sqrt delta *
                ((3 : ℝ) ^ (n + 1) * endpointConst d (1 / 9 : ℝ)))))
          = ((3 : ℝ) ^ (-n) * (3 : ℝ) ^ (n + 1)) *
            (triangleRemainderConst d Cs k *
              Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) * C * endpointConst d (1 / 9 : ℝ) * Ccap *
              Real.rpow s (-(3 : ℝ)) * Real.sqrt delta) := by ring
      rw [hlin, hz3]
      rw [edBridgeEpsConstGen, edBridgeRemWeightGen] at hgate
      linarith only [hgate]
    · -- the `ε` identity
      have hlin : triangleRemainderConst d Cs k *
            ((3 : ℝ) ^ (-n) * (Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) *
              (C * Real.rpow s (-(4 : ℝ)) *
                fluxCorrectedErrorRepresentative M L (n + 1)
                  ⟨s / 8, by linarith only [hs]⟩ (Cutoff.translateCutoffSample z omega) *
                ((3 : ℝ) ^ (n + 1) * endpointConst d (1 / 9 : ℝ)))))
          = ((3 : ℝ) ^ (-n) * (3 : ℝ) ^ (n + 1)) *
            (triangleRemainderConst d Cs k *
              Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) * C * endpointConst d (1 / 9 : ℝ) *
              Real.rpow s (-(4 : ℝ)) *
              fluxCorrectedErrorRepresentative M L (n + 1) ⟨s / 8, by linarith only [hs]⟩
                (Cutoff.translateCutoffSample z omega)) := by ring
      rw [hlin, hz3]
      ring
    · -- the `δ` identity
      ring
    · -- the two halves of `θ^{k+1}`
      exact le_of_eq (by ring)
  · exact Filter.Eventually.of_forall fun _ hc => absurd hc hnm

end

end Algsuperdiff.Section4.Provider.ExcessDecay
