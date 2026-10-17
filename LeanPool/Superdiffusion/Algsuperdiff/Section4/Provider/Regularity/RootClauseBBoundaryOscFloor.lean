/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootClauseBFloorRecut
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSixBoundaryIterationC1

/-!
# RootClauseBBoundaryOscFloor

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


namespace Algsuperdiff.Section4.Provider.Regularity

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03 MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay
open Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

noncomputable section

variable {d : ℕ}

/-- **`e.oscillation.Holder.bound` on the boundary branch, at the root's frame, on
ONE null set, with `C_edos` free above this lane's own floor.**

The boundary Step-6 endpoint with its entire parameter prefix discharged, its
scale pair inside the a.e. block, and its windows written in the carrier the
clause-(B) payload reads.  No interiority guard. -/
theorem exists_rootClauseBOsc_boundary_floor (d : ℕ) [NeZero d] (hd : d ≠ 0) :
    ∃ (C Ccap Cann Cb Cfl Citer Cosc : ℝ) (k : ℕ),
      0 < C ∧ 0 < Ccap ∧ 0 < Cann ∧ 0 ≤ Cb ∧ 1 ≤ Cfl ∧ 0 ≤ Cosc ∧ 10 ≤ k ∧
      ∀ Cedos : ℝ, Cfl ≤ Cedos →
      ∀ (M : ABKModel d) (m0 : ℤ) (Ecap : {E : ℝ // 1 ≤ E}),
        Algsuperdiff.Frozen.Section3.inductionState M m0 Ecap →
        M.gamma < 1 / 2 →
        M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma ≤ Ccap⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma ≤ Cann⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma ≤ 1 / 256 →
        ∀ alpha : ℝ, 0 < alpha → alpha < 1 →
          M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
              Real.rpow stepOneSEighth (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) *
                stepOneEp (stepOneDelta (stepOneC1 d Cedos 1 Citer (k + 1)) alpha) →
          ∀ m : ℤ, m ≤ m0 →
            ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
              ∀ (L n : ℤ) (v : Fin d → ℤ), m ≤ L → (14 : ℤ) ≤ m - n →
                v ∈ Support.latticeCubeSet d n m →
                  RootWindowPayload M (stepOneC1 d Cedos 1 Citer (k + 1)) alpha n m
                      omega →
                    ∀ (uglob hdat : H1Function (openCubeSet (originCube d m)))
                      (gsrc : Vec d → Vec d) (Khol Kh : ℝ), 0 ≤ Khol → 0 ≤ Kh →
                      IsDirichletSolutionOn
                          (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                          (originCube d m) uglob hdat gsrc →
                      HolderSeminormBoundOn (openCubeSet (originCube d m))
                          (1 / 2) Khol gsrc →
                      HolderSeminormBoundOn (openCubeSet (originCube d m))
                          (1 / 2) Kh hdat.grad →
                      (∀ y ∈ openCubeSet (originCube d m),
                        ‖hdat.grad y‖ ≤ Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh) →
                      Support.HasGradientOn (openCubeSet (originCube d m))
                        hdat.toFun hdat.grad →
                      ∀ n' kc : ℤ, n ≤ n' → n' ≤ kc → kc ≤ m →
                        (3 : ℝ) ^ (-n') *
                            normalizedL2On
                              (truncatedWindow (Support.triadicLatticePoint n v) m n')
                              (fun y => uglob.toFun y -
                                volumeAverage
                                  (truncatedWindow
                                    (Support.triadicLatticePoint n v) m n')
                                  uglob.toFun) ≤
                          Cosc *
                              Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) *
                              ((3 : ℝ) ^ (-kc) *
                                normalizedL2On
                                  (truncatedWindow
                                    (Support.triadicLatticePoint n v) m kc)
                                  (fun y => uglob.toFun y -
                                    volumeAverage
                                      (truncatedWindow
                                        (Support.triadicLatticePoint n v) m kc)
                                      uglob.toFun)) +
                            Cosc *
                              Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) *
                              (edFinalDataG M (edBoundaryCbd d Cb C k)
                                  (Khol * stepFourGagliardoConst d stepOneS) m +
                                edBoundaryDataHPrinted d Cb C k Kh m) := by
  classical
  obtain ⟨C, Ccap, Cb, Cann, hC, hCcap, hCb, hCann, k0, hk0, hres⟩ :=
    edFinal_oscillationHolderBound_boundaryC1 d hd
  have hk0k : k0 ≤ max k0 10 := le_max_left _ _
  have hk10 : 10 ≤ max k0 10 := le_max_right _ _
  obtain ⟨Cout, Citer, hCout, hCiter, hres'⟩ := hres (max k0 10) hk0k
  have hs0 : (0 : ℝ) < stepOneS := by rw [stepOneS]; norm_num
  have hs2 : stepOneS < 1 / 2 := by rw [stepOneS]; norm_num
  have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hCoutSq : (0 : ℝ) ≤ Cout * Cout := mul_nonneg hCout.le hCout.le
  refine ⟨C, Ccap, Cann, Cb,
    max 1 (max (64 * C ^ (2 : ℕ)) (edBoundaryFundFloor d Cb C Ccap (max k0 10))),
    Citer, Cout + Cout * Cout, max k0 10, hC, hCcap, hCann, hCb, le_max_left _ _,
    by linarith only [hCout, hCoutSq], hk10, ?_⟩
  intro Cedos hfloor M m0 Ecap hS hgamma hregC hregCap hregAnn hg256 alpha halpha0
    halpha1 hsmall m hmm0
  have hCedos1 : (1 : ℝ) ≤ Cedos := le_trans (le_max_left _ _) hfloor
  have hC1two : (2 : ℝ) ≤ stepOneC1 d Cedos 1 Citer (max k0 10 + 1) :=
    two_le_stepOneC1 d _ _ _ _
  have hC1pos : (0 : ℝ) < stepOneC1 d Cedos 1 Citer (max k0 10 + 1) := by
    linarith only [hC1two]
  have hdeltamem := stepOneDelta_mem hC1two halpha0 halpha1
  have hprice : stepOneDelta (stepOneC1 d Cedos 1 Citer (max k0 10 + 1)) alpha ≤
      64 * (C ^ (2 : ℕ))⁻¹ * stepOneS ^ (6 : ℕ) :=
    edBoundary_deltaCap_of_c1_floor hC halpha0.le hC1pos
      (le_stepOneC1_of_le_cedos d hCedos1
        (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hfloor) Citer
        (max k0 10 + 1))
  have hgate : edBridgeEpsConstGen d (max (schauderWindowConst d) Cb) C (max k0 10) *
        Ccap * Real.rpow stepOneS (-(3 : ℝ)) *
        Real.sqrt (stepOneDelta (stepOneC1 d Cedos 1 Citer (max k0 10 + 1)) alpha) ≤
      (1 / 2 : ℝ) * (3 : ℝ) ^ (-(1 / 4 : ℝ) * (((max k0 10 : ℕ) : ℝ) + 1)) :=
    edBoundaryFunding_of_c1_floor d hC.le hCcap.le halpha0.le hC1pos
      (le_stepOneC1_of_le_cedos d hCedos1
        (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hfloor) Citer
        (max k0 10 + 1))
  have hmerge := ae_forall_of_forall_ae_of_countable
    (μ := (Cutoff.cutoffSampleLaw M).toMeasure)
    (Q := fun p : ℤ × ℤ × (Fin d → ℤ) =>
      m ≤ p.1 ∧ (14 : ℤ) ≤ m - p.2.1 ∧
        p.2.2 ∈ Support.latticeCubeSet d p.2.1 m)
    (fun p hp => hres' M m0 Ecap hS hgamma hregC hregCap hregAnn hg256
      Cedos 1 alpha (le_of_lt halpha1) hdeltamem hprice hsmall hgate p.1 m p.2.1 hp.1
      hmm0 hp.2.1 p.2.2 hp.2.2)
  filter_upwards [hmerge] with omega hom
  intro L n v hL hwin hv hpay uglob hdat gsrc Khol Kh hKhol hKh hsol hgHol hhHol hsup
    hgradh n' kc hn' hn'kc hkc
  have hnm : n ≤ m := by omega
  have hbudget := (hpay.2.2.1 v hv).2.2.1
  rw [toNat_sub_cast_real hnm] at hbudget
  obtain ⟨hgL2, hgW⟩ := memLp_pair_of_holderHalf hd1 hKhol hgHol
  have hhW := memLp_two_gagliardoKernel_of_holderHalf hd1 hs0 hs2 hKh hhHol
  obtain ⟨cfam, slope, hmin⟩ :=
    exists_stepThreeWindow_affineMinimizerFamily
      (mem_openCubeSet_of_mem_latticeCubeSet hv) uglob
  exact hom (L, n, v) ⟨hL, hwin, hv⟩ hpay.1 hbudget uglob hdat gsrc Khol Kh hKhol hKh
    hsol hgL2 hgW hhW hgHol hhHol hsup hgradh cfam slope hmin n' kc hn' hn'kc hkc

end

end Algsuperdiff.Section4.Provider.Regularity
