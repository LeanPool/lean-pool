/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepFourBoundaryPairTrim
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepFourFinalIteration
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepFourFinalBudget
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepFiveBoundaryDelta
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.ClassicalGradient

/-!
# StepFourBoundaryDecayC1

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


namespace Algsuperdiff.Section4.Provider.Regularity

open Algsuperdiff.Section3
open HCPolySupport Algsuperdiff.Section4.Support MeasureTheory
open Algsuperdiff.Section4.Provider.ExcessDecay
open Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

noncomputable section

variable {d : ℕ}

/-! ## 1. The boundary `δ` in the `α`-free three-leg grouping -/

/-- **The boundary Step-4 output, three-leg grouping.**

`A^g_p + (A^h_p + ε_j·H)` with `H = 2 C_bd K_{h,∞}`: the `α`-free shape, with
the `∇h` flat leg `ε`-funded and no `ε`-free summand. -/
def stepFourBoundaryDeltaC1 (M : ABKModel d) (Cbd Cah Khinf Kg Kh epsj : ℝ)
    (p : ℤ) : ℝ :=
  Cbd * ((3 : ℝ) ^ ((p : ℝ) / 2) * ((Annealed.sigmaBar M p : ℝ))⁻¹ * Kg) +
    (Cah * ((3 : ℝ) ^ ((p : ℝ) / 2) * Kh) + epsj * (2 * Cbd * Khinf))

/-! ## 2. The two restrictions of the root's datum binders -/

/-- **The classical `C¹` half descends to a truncated window.**  The root's
binder, restricted to the corrector's carrier (one carrier only:
`Support.HasGradientOn`). -/
theorem hasGradientOn_truncatedWindow_of_root {m p : ℤ} {z : Vec d}
    {f : Vec d → ℝ} {G : Vec d → Vec d}
    (h : Support.HasGradientOn (openCubeSet (originCube d m)) f G) :
    Support.HasGradientOn (truncatedWindow z m p) f G :=
  fun y hy =>
    (h y (truncatedWindow_subset_domain z m p hy)).mono
      (truncatedWindow_subset_domain z m p)

theorem norm_volumeAverageVec_le_of_root_sup {m p : ℤ} {z : Vec d}
    (hz : z ∈ openCubeSet (originCube d m))
    (hdat : H1Function (openCubeSet (originCube d m))) {Kh : ℝ} (hKh : 0 ≤ Kh)
    (hsup : ∀ y ∈ openCubeSet (originCube d m),
      ‖hdat.grad y‖ ≤ Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh) :
    ‖volumeAverageVec (truncatedWindow z m p) hdat.grad‖ ≤
      Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh := by
  refine norm_volumeAverageVec_truncatedWindow_le_of_bound hz
    (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hKh) (fun i => ?_) hsup
  exact (integrableOn_grad_coord hdat i).mono_set
    (truncatedWindow_subset_domain z m p)

/-! ## 3. `hstep4` on the boundary branch -/

/-- **`hstep4` on the boundary branch, discharged.**

For one `omega`, every centre `z ∈ □_m` (NO interiority, NO lattice condition) and
every scale `j ∈ [n+k+1, m-1]` outside the Step-3 bad set `𝓑_z`, the Step-4 per-scale
excess decay at the concrete windows `U_j = stepThreeWindow z m j`, the Step-5 slot
`ε_j` (times the slot's own coefficient) and the boundary three-leg `δ^∂_{j-1}`.

Every hypothesis is either the trimmed slot's own, the annular producer's own,
or a binder of the root's printed datum block; there is no
harmonic-approximation hypothesis, no competitor package, no `MemLp` residue
and no interiority. -/
theorem stepFourDecay_boundary_pinned (d : ℕ) [NeZero d] (hd : d ≠ 0) :
    ∃ C Ccap Cb Cann : ℝ, 0 < C ∧ 0 < Ccap ∧ 0 ≤ Cb ∧ 0 < Cann ∧ ∃ k₀ : ℕ, 3 ≤ k₀ ∧
      ∀ k : ℕ, k₀ ≤ k →
        ∀ (M : ABKModel d) (m0 : ℤ) (Ecap : {E : ℝ // 1 ≤ E}),
          Algsuperdiff.Frozen.Section3.inductionState M m0 Ecap →
          M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
          M.gamma ≤ Ccap⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
          M.gamma ≤ Cann⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
          M.gamma ≤ 1 / 256 →
          ∀ delta : ℝ, delta ∈ Set.Ioc (0 : ℝ) (1 / 2) →
            delta ≤ 64 * (C ^ (2 : ℕ))⁻¹ * stepOneS ^ (6 : ℕ) →
            M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
                Real.rpow stepOneSEighth (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) *
                  stepOneEp delta →
            edBridgeEpsConstGen d (max (schauderWindowConst d) Cb) C k * Ccap *
                  Real.rpow stepOneS (-(3 : ℝ)) * Real.sqrt delta ≤
                (1 / 2 : ℝ) * (3 : ℝ) ^ (-(1 / 4 : ℝ) * ((k : ℝ) + 1)) →
            ∀ L m : ℤ, m ≤ L → m ≤ m0 →
              ∀ z : Vec d, z ∈ openCubeSet (originCube d m) →
                ∀ n : ℤ,
                  ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
                    ∀ (u hdat : H1Function (openCubeSet (originCube d m)))
                      (g : Vec d → Vec d) (Kg Kh : ℝ), 0 ≤ Kg → 0 ≤ Kh →
                      IsDirichletSolutionOn
                          (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                          (originCube d m) u hdat g →
                      MemLp g 2
                          (normalizedVolumeMeasureOn (openCubeSet (originCube d m))) →
                      MemLp (Gagliardo.gagliardoKernel stepOneS 2 g) 2
                          (normalizedGagliardoMeasureOn
                            (openCubeSet (originCube d m))) →
                      MemLp (Gagliardo.gagliardoKernel stepOneS 2 hdat.grad) 2
                          (normalizedGagliardoMeasureOn
                            (openCubeSet (originCube d m))) →
                      HolderSeminormBoundOn (openCubeSet (originCube d m))
                          (1 / 2) Kg g →
                      HolderSeminormBoundOn (openCubeSet (originCube d m))
                          (1 / 2) Kh hdat.grad →
                      (∀ y ∈ openCubeSet (originCube d m),
                        ‖hdat.grad y‖ ≤ Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh) →
                      Support.HasGradientOn (openCubeSet (originCube d m))
                        hdat.toFun hdat.grad →
                      ∀ (c : ℤ → ℝ) (slope : ℤ → Vec d),
                        (∀ j : ℤ, j ≤ m →
                          IsAffineMinimizer (stepThreeWindow z m j) u.toFun (c j)
                            (slope j)) →
                        ∀ j : ℤ, n + ((k : ℤ) + 1) ≤ j → j ≤ m - 1 →
                          j ∉ stepThreeBadSet M delta n m z omega →
                            affineExcess
                                (stepThreeWindow z m (j - ((k : ℤ) + 1))) u.toFun ≤
                              stepFiveTheta ^ (k + 1) *
                                  affineExcess (stepThreeWindow z m j) u.toFun +
                                (edBridgeEpsConstGen d
                                      (max (schauderWindowConst d) Cb) C k *
                                    Real.rpow stepOneS (-(4 : ℝ)) *
                                  stepFiveEps M j z delta omega) *
                                  slopeMagnitude (slope j) +
                                stepFourBoundaryDeltaC1 M
                                  (stepFourBoundaryDeltaConst
                                    (edBridgeRemWeightGen d
                                      (max (schauderWindowConst d) Cb) k) 1 C stepOneS)
                                  (stepFourBoundaryDeltaConst
                                      (edBridgeRemWeightGen d
                                        (max (schauderWindowConst d) Cb) k) 1 C stepOneS
                                    + edBridgeDatumLegConst d
                                        (max (schauderWindowConst d) Cb) k *
                                      (3 : ℝ) ^ ((1 : ℝ) / 2))
                                  (Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh)
                                  (Kg * stepFourGagliardoConst d stepOneS)
                                  (Kh * (1 + stepFourGagliardoConst d stepOneS))
                                  (stepFiveEps M j z delta omega) (j - 1) := by
  classical
  obtain ⟨C, Ccap, Cb, hC, hCcap, hCb, k₀, hk₀, hslot⟩ :=
    excessDecay_stepFour_decay_allCentres_datumSplit_trimmed d hd
  obtain ⟨Cann, hCann, hepsbnd⟩ := ae_stepOneEpsJ_le d
  refine ⟨C, Ccap, Cb, Cann, hC, hCcap, hCb, hCann, k₀, hk₀, ?_⟩
  intro k hk M m0 Ecap hS hregime hregimecap hregimeAnn hgamma delta hdelta hprice
    hsmall hgate L m hmL hmm0 z hz n
  have hs : (0 : ℝ) < stepOneS := stepOneS_pos
  have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd
  have hgamma4 : M.gamma ≤ 1 / 4 := by linarith only [hgamma]
  have hCV : (0 : ℝ) ≤ edBridgeRemWeightGen d (max (schauderWindowConst d) Cb) k * 1 := by
    rw [mul_one, edBridgeRemWeightGen]
    exact mul_nonneg
      (triangleRemainderConst_nonneg d
        (le_trans (schauderWindowConst_nonneg d) (le_max_left _ _)) k)
      (Real.sqrt_nonneg _)
  have hcapAll : ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ p : ℤ, stepOneEpsJ M p z delta omega ≤
        ENNReal.ofReal (Cann * stepOneEp delta) := by
    rw [ae_all_iff]
    intro p
    exact hepsbnd M hregimeAnn hgamma delta hdelta hsmall p z
  filter_upwards [hslot k hk M stepOneS (stepOneS_mem_Icc hgamma) hregime hregimecap hs
      delta ⟨hdelta.1, by linarith only [hdelta.2]⟩ hprice hsmall hgate L m hmL z hz,
    hcapAll] with omega hom hcap
  intro u hdat g Kg Kh hKg0 hKh0 hsol hgL2 hgW hhW hgHol hhHol hsup hgradh c slope hmin
    j hjn hjm hjB
  obtain ⟨p, rfl⟩ : ∃ p : ℤ, j = p + 1 := ⟨j - 1, by ring⟩
  simp only [show p + 1 - 1 = p from by ring]
  -- the good event at the slot's own index
  have hev : omega ∈ stepThreeGoodEvent M delta (p + 1) z := by
    by_contra hc
    exact hjB ((mem_stepThreeBadSet_iff M delta n m z omega (p + 1)).mpr
      ⟨⟨by omega, hjm⟩, hc⟩)
  -- the slot, at `n := p`
  have hslotp := hom p (by omega) hev u hdat g hsol hgL2 hgW hhW Kh hKh0
    (hhHol.mono_set (truncatedWindow_subset_domain z m (p - 2)))
    (hasGradientOn_truncatedWindow_of_root hgradh) (c (p + 1)) (slope (p + 1))
    (hmin (p + 1) (by omega))
  -- the `ε` thread
  have hEfl : Support.fluxCorrectedErrorRepresentative M L (p + 1)
      ⟨stepOneSEighth, stepOneSEighth_pos⟩ (Cutoff.translateCutoffSample z omega) ≤
      stepFiveEps M (p + 1) z delta omega :=
    fluxCorrectedErrorRepresentative_le_stepFiveEps (by omega) hev (hcap (p + 1))
  have heps0 : (0 : ℝ) ≤ stepFiveEps M (p + 1) z delta omega :=
    stepFiveEps_nonneg M (p + 1) z delta omega
  -- the four data legs of the collapse
  have hGav : ‖volumeAverageVec (truncatedWindow z m p) hdat.grad‖ ≤
      Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh :=
    norm_volumeAverageVec_le_of_root_sup hz hdat hKh0 hsup
  have hSig : ((Annealed.sigmaBar M (p - 2) : ℝ))⁻¹ ≤
      8 * ((Annealed.sigmaBar M p : ℝ))⁻¹ :=
    inv_sigmaBar_sub_two_le_eight_mul_inv_sigmaBar hS hgamma4 (by omega)
  have hGsem := stepFourGsemLeg_le (z := z) (m := m) (j := p + 1) (g := g) (K := Kg)
    (s := stepOneS) hd1 hz hs stepOneS_lt_half hKg0 hgHol
  have hGag0 : (0 : ℝ) ≤ stepFourGagliardoConst d stepOneS :=
    stepFourGagliardoConst_nonneg d stepOneS
  have hHsem0 := stepFourGsemLeg_le (z := z) (m := m) (j := p + 1) (g := hdat.grad)
    (K := Kh) (s := stepOneS) hd1 hz hs stepOneS_lt_half hKh0 hhHol
  have hHwiden : Kh * stepFourGagliardoConst d stepOneS ≤
      Kh * (1 + stepFourGagliardoConst d stepOneS) :=
    mul_le_mul_of_nonneg_left (by linarith only []) hKh0
  have hHsem : (normalizedGagliardoESeminormOn (stepThreeWindow z m (p + 1)) stepOneS
        hdat.grad).toReal ≤
      Kh * (1 + stepFourGagliardoConst d stepOneS) *
        (3 : ℝ) ^ (((p + 1 : ℤ) : ℝ) * (1 / 2 - stepOneS)) :=
    le_trans hHsem0
      (mul_le_mul_of_nonneg_right hHwiden (Real.rpow_nonneg (by norm_num) _))
  -- the datum leg is monotone in its Hölder constant
  have hlegmono : edBridgeDatumLeg d (max (schauderWindowConst d) Cb) k p Kh ≤
      edBridgeDatumLeg d (max (schauderWindowConst d) Cb) k p
        (Kh * (1 + stepFourGagliardoConst d stepOneS)) := by
    rw [edBridgeDatumLeg_eq, edBridgeDatumLeg_eq]
    refine mul_le_mul_of_nonneg_left ?_
      (edBridgeDatumLegConst_nonneg d
        (le_trans (schauderWindowConst_nonneg d) (le_max_left _ _)) k)
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by norm_num) _)
    linarith only [hKh0, hGag0, mul_nonneg hKh0 hGag0]
  -- the `δ`-side into the three-leg grouping
  have hbud := edBridgeDeltaErrorWeighted_add_datumLeg_le_boundaryThreeLegs (M := M) (C := C)
    (Crem := edBridgeRemWeightGen d (max (schauderWindowConst d) Cb) k) (Vd := 1)
    (s := stepOneS) (epsj := stepFiveEps M (p + 1) z delta omega)
    (Khinf := Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh)
    (SigInvN := ((Annealed.sigmaBar M p : ℝ))⁻¹)
    (Kg := Kg * stepFourGagliardoConst d stepOneS)
    (Kh := Kh * (1 + stepFourGagliardoConst d stepOneS))
    (Cs := max (schauderWindowConst d) Cb) (k := k) (L := L) (m := m) (n := p)
    (t := ⟨stepOneS / 8, by linarith only [hs]⟩) (z := z) (gflux := g)
    (gradh := hdat.grad) (omega := omega) hCV hC.le hs heps0 hEfl hGav hSig
    (inv_nonneg.mpr (Annealed.sigmaBar M p).2.le)
    (mul_nonneg hKg0 (stepFourGagliardoConst_nonneg d stepOneS)) hGsem
    (mul_nonneg hKh0 (by linarith only [hGag0])) hHsem
  rw [mul_one] at hbud
  -- the `ε`-leg's coefficient
  have hEpsCoef0 : (0 : ℝ) ≤
      edBridgeEpsConstGen d (max (schauderWindowConst d) Cb) C k *
        Real.rpow stepOneS (-(4 : ℝ)) :=
    mul_nonneg
      (by
        rw [edBridgeEpsConstGen]
        have hrw : (0 : ℝ) ≤ edBridgeRemWeightGen d (max (schauderWindowConst d) Cb) k :=
          edBridgeRemWeightGen_nonneg d
            (le_trans (schauderWindowConst_nonneg d) (le_max_left _ _)) k
        have hep : (1 : ℝ) ≤ endpointConst d (1 / 9 : ℝ) :=
          one_le_endpointConst (by norm_num)
        exact mul_nonneg (mul_nonneg (by linarith only [hrw]) hC.le)
          (by linarith only [hep]))
      (Real.rpow_nonneg hs.le _)
  have hEpsLeg : edBridgeEps M
        (edBridgeEpsConstGen d (max (schauderWindowConst d) Cb) C k) L stepOneS
        ⟨stepOneS / 8, by linarith only [hs]⟩ z omega p ≤
      edBridgeEpsConstGen d (max (schauderWindowConst d) Cb) C k *
          Real.rpow stepOneS (-(4 : ℝ)) *
        stepFiveEps M (p + 1) z delta omega := by
    rw [edBridgeEps]
    exact mul_le_mul_of_nonneg_left hEfl hEpsCoef0
  have hSlp0 : (0 : ℝ) ≤ slopeMagnitude (slope (p + 1)) := slopeMagnitude_nonneg _
  have hEpsMul := mul_le_mul_of_nonneg_right hEpsLeg hSlp0
  -- the contraction factor and the window index
  have hcast : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
  have htheta : stepFiveTheta ^ (k + 1) =
      (3 : ℝ) ^ (-(1 / 4 : ℝ) * ((k : ℝ) + 1)) := by
    rw [stepFiveTheta_pow]
    congr 1
    push_cast
    ring
  rw [hcast] at hslotp
  rw [htheta, stepFourBoundaryDeltaC1, stepThreeWindow, stepThreeWindow]
  linarith only [hslotp, hEpsMul, hbud, hlegmono]

/-! ## 4. The boundary `δ`-budget over the iteration window -/

/-- **`e.sum.delta.j.bound` for the boundary family.**

The window sum of `stepFourBoundaryDeltaC1` at the slot's own index shift, in the
`α`-free grouping `dataG + dataH_∂`:

```text
   ∑_{j=n}^{m} δ^∂_{j-1}
     ≤ edFinalDataG(C_bd, K_g)  +  ( C_ah 3^{m/2} K_h / (1-r₂)  +  S_ε·(2 C_bd K_{h,∞}) ) ,
```

with `r₂ = 3^{-1/2}` and NO `W`-linear summand — the `∇h` flat leg is
`ε`-funded, so's `α`-free absorption
`StepSixBoundaryEndpoint.stepSixBoundary_holderBound_ epsFunded` consumes
`dataH_∂` directly. -/
theorem sum_Icc_top_stepFourBoundaryDeltaC1_le {M : ABKModel d} {m0 : ℤ}
    {Ecap : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 Ecap)
    (hgamma : M.gamma < 1 / 2) {Cbd Cah Khinf Kg Kh Se delta : ℝ} {n m : ℤ}
    {z : Vec d} {omega : Cutoff.CutoffSample d} (hnm : n ≤ m) (hm : m ≤ m0)
    (hCbd : 0 ≤ Cbd) (hCah : 0 ≤ Cah) (hKhinf : 0 ≤ Khinf) (hKg : 0 ≤ Kg)
    (hKh : 0 ≤ Kh)
    (hSe : ∑ j ∈ Finset.Icc n m, stepFiveEps M j z delta omega ≤ Se) :
    ∑ j ∈ Finset.Icc n m,
        stepFourBoundaryDeltaC1 M Cbd Cah Khinf Kg Kh
          (stepFiveEps M j z delta omega) (j - 1) ≤
      edFinalDataG M Cbd Kg m +
        (Cah * ((3 : ℝ) ^ ((m : ℝ) / 2) * Kh) / (1 - stepFiveRatioH) +
          Se * (2 * Cbd * Khinf)) := by
  have hr1pos : (0 : ℝ) < stepFiveRatioG M := stepFiveRatioG_pos M
  have hr1lt : stepFiveRatioG M < 1 := stepFiveRatioG_lt_one hgamma
  have hr2pos : (0 : ℝ) < stepFiveRatioH := stepFiveRatioH_pos
  have hr2lt : stepFiveRatioH < 1 := stepFiveRatioH_lt_one
  have hKtop0 : (0 : ℝ) ≤ edFinalKgTop M Cbd Kg m := by
    rw [edFinalKgTop]
    exact mul_nonneg (mul_nonneg (by linarith only [hCbd])
      (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (inv_nonneg.mpr (Annealed.sigmaBar M m).2.le))) hKg
  have hAtop0 : (0 : ℝ) ≤ Cah * ((3 : ℝ) ^ ((m : ℝ) / 2) * Kh) :=
    mul_nonneg hCah (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hKh)
  -- the `g`-leg, one scale down
  have hAgd : ∀ j : ℤ, j ≤ m →
      edFinalDelta M Cbd Kg (j - 1) ≤
        edFinalKgTop M Cbd Kg m * stepFiveRatioG M ^ (m - j) := by
    intro j hj
    have hbase := edFinalDelta_le_zpow hS hCbd hKg (show j - 1 ≤ m by omega) hm
    have hpow0 : (0 : ℝ) < stepFiveRatioG M ^ (m - j) := zpow_pos hr1pos _
    have hsplit : stepFiveRatioG M ^ (m - (j - 1)) =
        stepFiveRatioG M ^ (m - j) * stepFiveRatioG M := by
      rw [show m - (j - 1) = (m - j) + 1 by ring,
        zpow_add_one₀ (ne_of_gt hr1pos)]
    have hstep : stepFiveRatioG M ^ (m - (j - 1)) ≤ stepFiveRatioG M ^ (m - j) := by
      have h := mul_le_mul_of_nonneg_left hr1lt.le hpow0.le
      rw [hsplit]
      linarith only [h]
    exact hbase.trans (mul_le_mul_of_nonneg_left hstep hKtop0)
  -- the `∇h`-leg, one scale down
  have hAhd : ∀ j : ℤ, j ≤ m →
      Cah * ((3 : ℝ) ^ (((j - 1 : ℤ) : ℝ) / 2) * Kh) ≤
        Cah * ((3 : ℝ) ^ ((m : ℝ) / 2) * Kh) * stepFiveRatioH ^ (m - j) := by
    intro j hj
    have hpow0 : (0 : ℝ) < stepFiveRatioH ^ (m - j) := zpow_pos hr2pos _
    have hsplit : stepFiveRatioH ^ (m - (j - 1)) =
        stepFiveRatioH ^ (m - j) * stepFiveRatioH := by
      rw [show m - (j - 1) = (m - j) + 1 by ring,
        zpow_add_one₀ (ne_of_gt hr2pos)]
    have hstep : stepFiveRatioH ^ (m - (j - 1)) ≤ stepFiveRatioH ^ (m - j) := by
      have h := mul_le_mul_of_nonneg_left hr2lt.le hpow0.le
      rw [hsplit]
      linarith only [h]
    have hid : Cah * ((3 : ℝ) ^ ((m : ℝ) / 2) * stepFiveRatioH ^ (m - (j - 1)) * Kh)
        = Cah * ((3 : ℝ) ^ ((m : ℝ) / 2) * Kh) * stepFiveRatioH ^ (m - (j - 1)) := by
      ring
    rw [three_rpow_half_eq_mul_ratioH_zpow m (j - 1), hid]
    exact mul_le_mul_of_nonneg_left hstep hAtop0
  have hkit := sum_Icc_top_boundaryDelta_le_of_legs
    (δ := fun j => stepFourBoundaryDeltaC1 M Cbd Cah Khinf Kg Kh
      (stepFiveEps M j z delta omega) (j - 1))
    (Ag := fun j => edFinalDelta M Cbd Kg (j - 1))
    (Ah := fun j => Cah * ((3 : ℝ) ^ (((j - 1 : ℤ) : ℝ) / 2) * Kh))
    (ε := fun j => stepFiveEps M j z delta omega)
    (Kg := edFinalKgTop M Cbd Kg m) (Kh := Cah * ((3 : ℝ) ^ ((m : ℝ) / 2) * Kh))
    (Hinf := 2 * Cbd * Khinf) (Flat := 0) (Se := Se)
    (W := ((m : ℝ) - (n : ℝ)) + 1) (ind := 1) hnm hr1pos hr1lt hr2pos hr2lt
    (edFinalDelta_nonneg hCbd hKg _) hAgd
    (mul_nonneg hCah (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hKh)) hAhd hSe
    (mul_nonneg (by linarith only [hCbd]) hKhinf) zero_le_one rfl
    (fun j => by simp only [stepFourBoundaryDeltaC1, edFinalDelta]; ring)
  have hid : edFinalKgTop M Cbd Kg m / (1 - stepFiveRatioG M) +
      (Cah * ((3 : ℝ) ^ ((m : ℝ) / 2) * Kh) / (1 - stepFiveRatioH) +
          Se * (2 * Cbd * Khinf) + (((m : ℝ) - (n : ℝ)) + 1) * 0) * 1 =
      edFinalDataG M Cbd Kg m +
        (Cah * ((3 : ℝ) ^ ((m : ℝ) / 2) * Kh) / (1 - stepFiveRatioH) +
          Se * (2 * Cbd * Khinf)) := by
    rw [edFinalDataG]
    ring
  linarith only [hkit, hid]

end

end Algsuperdiff.Section4.Provider.Regularity
