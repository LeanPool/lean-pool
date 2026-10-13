/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepFourBoundaryDecayC1
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepFourFinalEndpoint
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSixBoundaryEndpoint

/-!
# StepSixBoundaryIterationC1

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

/-! ## 1. The three constants of the boundary Step-4 output -/

/-- The boundary `δ`'s `g`-leg constant `C_bd` produced's slot. -/
def edBoundaryCbd (d : ℕ) [NeZero d] (Cb C : ℝ) (k : ℕ) : ℝ :=
  stepFourBoundaryDeltaConst
    (edBridgeRemWeightGen d (max (schauderWindowConst d) Cb) k) 1 C stepOneS

/-- The boundary `δ`'s `∇h`-leg constant `C_ah`. -/
def edBoundaryCah (d : ℕ) [NeZero d] (Cb C : ℝ) (k : ℕ) : ℝ :=
  edBoundaryCbd d Cb C k +
    edBridgeDatumLegConst d (max (schauderWindowConst d) Cb) k * (3 : ℝ) ^ ((1 : ℝ) / 2)

/-- The boundary `ε`-leg coefficient `C_ε`. -/
def edBoundaryCeps (d : ℕ) [NeZero d] (Cb C : ℝ) (k : ℕ) : ℝ :=
  edBridgeEpsConstGen d (max (schauderWindowConst d) Cb) C k *
    Real.rpow stepOneS (-(4 : ℝ))

theorem edBoundaryCbd_nonneg (d : ℕ) [NeZero d] (Cb : ℝ) {C : ℝ} (hC : 0 ≤ C)
    (k : ℕ) : 0 ≤ edBoundaryCbd d Cb C k := by
  have hrw : (0 : ℝ) ≤
      edBridgeRemWeightGen d (max (schauderWindowConst d) Cb) k * 1 := by
    rw [mul_one]
    exact edBridgeRemWeightGen_nonneg d
      (le_trans (schauderWindowConst_nonneg d) (le_max_left _ _)) k
  rw [edBoundaryCbd]
  exact stepFourBoundaryDeltaConst_nonneg hrw hC stepOneS_pos

theorem edBoundaryCah_nonneg (d : ℕ) [NeZero d] (Cb : ℝ) {C : ℝ} (hC : 0 ≤ C)
    (k : ℕ) : 0 ≤ edBoundaryCah d Cb C k := by
  have h1 : (0 : ℝ) ≤ edBoundaryCbd d Cb C k := edBoundaryCbd_nonneg d Cb hC k
  have h2 : (0 : ℝ) ≤
      edBridgeDatumLegConst d (max (schauderWindowConst d) Cb) k *
        (3 : ℝ) ^ ((1 : ℝ) / 2) :=
    mul_nonneg
      (edBridgeDatumLegConst_nonneg d
        (le_trans (schauderWindowConst_nonneg d) (le_max_left _ _)) k)
      (Real.rpow_nonneg (by norm_num) _)
  rw [edBoundaryCah]
  linarith only [h1, h2]

theorem edBoundaryCeps_nonneg (d : ℕ) [NeZero d] (Cb : ℝ) {C : ℝ} (hC : 0 ≤ C)
    (k : ℕ) : 0 ≤ edBoundaryCeps d Cb C k := by
  have hrw : (0 : ℝ) ≤ edBridgeRemWeightGen d (max (schauderWindowConst d) Cb) k :=
    edBridgeRemWeightGen_nonneg d
      (le_trans (schauderWindowConst_nonneg d) (le_max_left _ _)) k
  have hep : (1 : ℝ) ≤ endpointConst d (1 / 9 : ℝ) := one_le_endpointConst (by norm_num)
  rw [edBoundaryCeps, edBridgeEpsConstGen]
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (by linarith only [hrw]) hC) (by linarith only [hep]))
    (Real.rpow_nonneg stepOneS_pos.le _)

/-! ## 2. The boundary `dataH`, and its two Step-6 legs -/

/-- **The boundary `∇h` leg of `e.sum.delta.j.bound`** —'s `α`-free grouping, with
NO `ε`-free flat summand:

```text
   dataH_∂ = C_ah·3^{m/2}(1+C_gag)K_h/(1-3^{-1/2})  +  S_ε·(2 C_bd 3^{m/2} K_h) .
``` -/
def edBoundaryDataH (d : ℕ) [NeZero d] (Cb C : ℝ) (k : ℕ) (Kh Se : ℝ) (m : ℤ) : ℝ :=
  edBoundaryCah d Cb C k *
      ((3 : ℝ) ^ ((m : ℝ) / 2) * (Kh * (1 + stepFourGagliardoConst d stepOneS))) /
    (1 - stepFiveRatioH) +
  Se * (2 * edBoundaryCbd d Cb C k * (Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh))

theorem edBoundaryKhleg_nonneg (d : ℕ) [NeZero d] (Cb : ℝ) {C Kh : ℝ}
    (hC : 0 ≤ C) (k : ℕ) (hKh : 0 ≤ Kh) (m : ℤ) :
    (0 : ℝ) ≤ edBoundaryCah d Cb C k *
        ((3 : ℝ) ^ ((m : ℝ) / 2) * (Kh * (1 + stepFourGagliardoConst d stepOneS))) /
      (1 - stepFiveRatioH) := by
  have hr : (0 : ℝ) < 1 - stepFiveRatioH := by linarith only [stepFiveRatioH_lt_one]
  have hgag : (0 : ℝ) ≤ stepFourGagliardoConst d stepOneS :=
    stepFourGagliardoConst_nonneg d stepOneS
  refine div_nonneg (mul_nonneg (edBoundaryCah_nonneg d Cb hC k)
    (mul_nonneg (Real.rpow_nonneg (by norm_num) _) ?_)) hr.le
  exact mul_nonneg hKh (by linarith only [hgag])

theorem edBoundaryHinf_nonneg (d : ℕ) [NeZero d] (Cb : ℝ) {C Kh : ℝ}
    (hC : 0 ≤ C) (k : ℕ) (hKh : 0 ≤ Kh) (m : ℤ) :
    (0 : ℝ) ≤ 2 * edBoundaryCbd d Cb C k * (Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh) := by
  have h1 : (0 : ℝ) ≤ edBoundaryCbd d Cb C k := edBoundaryCbd_nonneg d Cb hC k
  exact mul_nonneg (by linarith only [h1])
    (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hKh)

theorem edBoundaryDataH_nonneg (d : ℕ) [NeZero d] (Cb : ℝ) {C Kh Se : ℝ}
    (hC : 0 ≤ C) (k : ℕ) (hKh : 0 ≤ Kh) (hSe : 0 ≤ Se) (m : ℤ) :
    (0 : ℝ) ≤ edBoundaryDataH d Cb C k Kh Se m := by
  have h1 := edBoundaryKhleg_nonneg d Cb (C := C) (Kh := Kh) hC k hKh m
  have h2 := mul_nonneg hSe
    (edBoundaryHinf_nonneg d Cb (C := C) (Kh := Kh) hC k hKh m)
  rw [edBoundaryDataH]
  linarith only [h1, h2]

/-! ## 3. `e.oscillation.iteration.result` on the boundary branch -/

/-- **`e.oscillation.iteration.result` printed lattice centre, `hstep4` GONE.**

The interior endpoint's sibling off's boundary Step-4 slot: no interiority
gate, the contraction over `k+1` scales, and the nonzero boundary `dataH_∂`. -/
theorem edFinal_oscillationIterationResult_boundaryC1 (d : ℕ) [NeZero d] (hd : d ≠ 0) :
    ∃ C Ccap Cb Cann : ℝ, 0 < C ∧ 0 < Ccap ∧ 0 ≤ Cb ∧ 0 < Cann ∧ ∃ k₀ : ℕ, 3 ≤ k₀ ∧
      ∀ k : ℕ, k₀ ≤ k →
        ∃ Cout Citer : ℝ, 0 < Cout ∧ 0 ≤ Citer ∧
          ∀ (M : ABKModel d) (m0 : ℤ) (Ecap : {E : ℝ // 1 ≤ E}),
            Algsuperdiff.Frozen.Section3.inductionState M m0 Ecap →
            M.gamma < 1 / 2 →
            M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
            M.gamma ≤ Ccap⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
            M.gamma ≤ Cann⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
            M.gamma ≤ 1 / 256 →
            ∀ (Cedos Cannp alpha : ℝ), alpha ≤ 1 →
              stepOneDelta (stepOneC1 d Cedos Cannp Citer (k + 1)) alpha ∈
                  Set.Ioc (0 : ℝ) (1 / 2) →
              stepOneDelta (stepOneC1 d Cedos Cannp Citer (k + 1)) alpha ≤
                  64 * (C ^ (2 : ℕ))⁻¹ * stepOneS ^ (6 : ℕ) →
              M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
                  Real.rpow stepOneSEighth (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) *
                    stepOneEp (stepOneDelta (stepOneC1 d Cedos Cannp Citer (k + 1))
                      alpha) →
              edBridgeEpsConstGen d (max (schauderWindowConst d) Cb) C k * Ccap *
                    Real.rpow stepOneS (-(3 : ℝ)) *
                    Real.sqrt (stepOneDelta (stepOneC1 d Cedos Cannp Citer (k + 1))
                      alpha) ≤
                  (1 / 2 : ℝ) * (3 : ℝ) ^ (-(1 / 4 : ℝ) * ((k : ℝ) + 1)) →
              ∀ L m n : ℤ, m ≤ L → m ≤ m0 → (14 : ℤ) ≤ m - n →
                ∀ v : Fin d → ℤ, v ∈ Support.latticeCubeSet d n m →
                  ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
                    GoodScaleWindows M stepOneSEighth
                        (stepOneDelta (stepOneC1 d Cedos Cannp Citer (k + 1)) alpha)
                        stepOneSEighth_pos n m omega →
                    (((stepThreeBadSet M
                          (stepOneDelta (stepOneC1 d Cedos Cannp Citer (k + 1)) alpha)
                          n m (Support.triadicLatticePoint n v) omega).card : ℝ)) ≤
                        stepOneDelta (stepOneC1 d Cedos Cannp Citer (k + 1)) alpha *
                          (((m : ℝ) - (n : ℝ)) + 1) →
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
                          IsAffineMinimizer
                            (stepThreeWindow (Support.triadicLatticePoint n v) m j)
                            u.toFun (c j) (slope j)) →
                        ∀ n' m' : ℤ, n ≤ n' → n' ≤ m' → m' ≤ m →
                          (3 : ℝ) ^ (-n') *
                              normalizedL2On
                                (stepThreeWindow
                                  (Support.triadicLatticePoint n v) m n')
                                (fun x => u.toFun x -
                                  volumeAverage
                                    (stepThreeWindow
                                      (Support.triadicLatticePoint n v) m n')
                                    u.toFun) ≤
                            Cout *
                                Real.exp
                                  ((stepOneC1 d Cedos Cannp Citer (k + 1))⁻¹ * Citer *
                                    stepSixExponent alpha n m) *
                                ((3 : ℝ) ^ (-m') *
                                    normalizedL2On
                                      (stepThreeWindow
                                        (Support.triadicLatticePoint n v) m m')
                                      (fun x => u.toFun x -
                                        volumeAverage
                                          (stepThreeWindow
                                            (Support.triadicLatticePoint n v) m m')
                                          u.toFun) +
                                  Cout *
                                    edFinalDataG M (edBoundaryCbd d Cb C k)
                                      (Kg * stepFourGagliardoConst d stepOneS) m) +
                              Cout *
                                Real.exp
                                  ((stepOneC1 d Cedos Cannp Citer (k + 1))⁻¹ * Citer *
                                    stepSixExponent alpha n m) *
                                edBoundaryDataH d Cb C k Kh
                                  (2 *
                                    stepOneDelta
                                      (stepOneC1 d Cedos Cannp Citer (k + 1)) alpha *
                                    ((m : ℝ) - (n : ℝ))) m := by
  classical
  obtain ⟨C, Ccap, Cb, Cann, hC, hCcap, hCb, hCann, k₀, hk₀, hpin⟩ :=
    stepFourDecay_boundary_pinned d hd
  refine ⟨C, Ccap, Cb, Cann, hC, hCcap, hCb, hCann, k₀, hk₀, ?_⟩
  intro k hk
  obtain ⟨Cout, Citer, hCout, hCiter, hiter⟩ :=
    oscillationIterationResult_of_stepFourDecay_generic d hd (k + 1) (by omega)
      (edBoundaryCeps_nonneg d Cb hC.le k)
  refine ⟨Cout, Citer, hCout, hCiter, ?_⟩
  intro M m0 Ecap hS hgamma hregime hregimecap hregimeAnn hgamma256 Cedos Cannp alpha
    halpha hdelta hprice hsmall hgate L m n hmL hmm0 hwin v hv
  set delta := stepOneDelta (stepOneC1 d Cedos Cannp Citer (k + 1)) alpha with hdeltadef
  set z := Support.triadicLatticePoint n v with hzdef
  have hzm : z ∈ openCubeSet (originCube d m) :=
    mem_openCubeSet_of_mem_latticeCubeSet hv
  have hnm : n ≤ m := by omega
  have hmnR : (0 : ℝ) ≤ (m : ℝ) - (n : ℝ) := by
    have hcast : ((n : ℤ) : ℝ) ≤ ((m : ℤ) : ℝ) := Int.cast_le.mpr hnm
    linarith only [hcast]
  have hCbd : (0 : ℝ) ≤ edBoundaryCbd d Cb C k := edBoundaryCbd_nonneg d Cb hC.le k
  have hCah : (0 : ℝ) ≤ edBoundaryCah d Cb C k := edBoundaryCah_nonneg d Cb hC.le k
  have hCeps : (0 : ℝ) ≤ edBoundaryCeps d Cb C k := edBoundaryCeps_nonneg d Cb hC.le k
  have hSeNN : (0 : ℝ) ≤ 2 * delta * ((m : ℝ) - (n : ℝ)) := by
    have h := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hdelta.1.le) hmnR
    linarith only [h]
  filter_upwards [hpin k hk M m0 Ecap hS hregime hregimecap hregimeAnn hgamma256 delta
    hdelta hprice hsmall hgate L m hmL hmm0 z hzm n] with omega hstep
  intro hgood hBz u hdat g Kg Kh hKg0 hKh0 hsol hgL2 hgW hhW hgHol hhHol hsup hgradh
    c slope hmin n' m' hn' hn'm' hm'm
  have hKgT : (0 : ℝ) ≤ Kg * stepFourGagliardoConst d stepOneS :=
    mul_nonneg hKg0 (stepFourGagliardoConst_nonneg d stepOneS)
  have hKhT : (0 : ℝ) ≤ Kh * (1 + stepFourGagliardoConst d stepOneS) := by
    have hgag : (0 : ℝ) ≤ stepFourGagliardoConst d stepOneS :=
      stepFourGagliardoConst_nonneg d stepOneS
    exact mul_nonneg hKh0 (by linarith only [hgag])
  have hKhinf : (0 : ℝ) ≤ Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) hKh0
  have hu : MemLp u.toFun 2 (volume.restrict (stepThreeWindow z m m)) :=
    u.memL2.mono_measure
      (Measure.restrict_mono (truncatedWindow_subset_domain z m m) le_rfl)
  have hSe := sum_stepFiveEps_le_two_mul_delta_mul_window hdelta.1.le hwin hgood hv
  have hSd := sum_Icc_top_stepFourBoundaryDeltaC1_le (M := M) (Cbd := edBoundaryCbd d Cb C k)
    (Cah := edBoundaryCah d Cb C k)
    (Khinf := Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh)
    (Kg := Kg * stepFourGagliardoConst d stepOneS)
    (Kh := Kh * (1 + stepFourGagliardoConst d stepOneS))
    (Se := 2 * delta * ((m : ℝ) - (n : ℝ))) (delta := delta) (z := z) (omega := omega)
    hS hgamma hnm hmm0 hCbd hCah hKhinf hKgT hKhT hSe
  have hcast : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
  refine hiter Cedos Cannp alpha halpha n m (by omega) (stepThreeWindow z m)
    (iterationWindowFamily_stepThreeWindow z m hzm) u.toFun hu c slope hmin
    (stepThreeBadSet M delta n m z omega) hBz
    (fun j => edBoundaryCeps d Cb C k * stepFiveEps M j z delta omega)
    (fun j => stepFourBoundaryDeltaC1 M (edBoundaryCbd d Cb C k)
      (edBoundaryCah d Cb C k) (Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh)
      (Kg * stepFourGagliardoConst d stepOneS)
      (Kh * (1 + stepFourGagliardoConst d stepOneS))
      (stepFiveEps M j z delta omega) (j - 1))
    (fun j _ _ => mul_nonneg hCeps (stepFiveEps_nonneg M j z delta omega))
    (fun j _ _ => ?_)
    (sum_Icc_edFinalEps_le hCeps hdelta.1.le hwin hgood hv)
    (edFinalDataG M (edBoundaryCbd d Cb C k)
      (Kg * stepFourGagliardoConst d stepOneS) m)
    (edBoundaryDataH d Cb C k Kh (2 * delta * ((m : ℝ) - (n : ℝ))) m)
    (edFinalDataG_nonneg hgamma hCbd hKgT m)
    (edBoundaryDataH_nonneg d Cb hC.le k hKh0 hSeNN m)
    (by simp only [edBoundaryDataH]; linarith only [hSd]) (fun j hj1 hj2 hj3 => ?_)
    n' m' hn' hn'm' hm'm
  · -- the `δ`-family is nonnegative
    have hSig : (0 : ℝ) ≤ ((Annealed.sigmaBar M (j - 1) : ℝ))⁻¹ :=
      inv_nonneg.mpr (Annealed.sigmaBar M (j - 1)).2.le
    have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ (((j - 1 : ℤ) : ℝ) / 2) :=
      Real.rpow_nonneg (by norm_num) _
    have hleg1 : (0 : ℝ) ≤ edBoundaryCbd d Cb C k *
        ((3 : ℝ) ^ (((j - 1 : ℤ) : ℝ) / 2) * ((Annealed.sigmaBar M (j - 1) : ℝ))⁻¹ *
          (Kg * stepFourGagliardoConst d stepOneS)) :=
      mul_nonneg hCbd (mul_nonneg (mul_nonneg h3 hSig) hKgT)
    have hleg2 : (0 : ℝ) ≤ edBoundaryCah d Cb C k *
        ((3 : ℝ) ^ (((j - 1 : ℤ) : ℝ) / 2) *
          (Kh * (1 + stepFourGagliardoConst d stepOneS))) :=
      mul_nonneg hCah (mul_nonneg h3 hKhT)
    have hleg3 : (0 : ℝ) ≤ stepFiveEps M j z delta omega *
        (2 * edBoundaryCbd d Cb C k * (Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh)) :=
      mul_nonneg (stepFiveEps_nonneg M j z delta omega)
        (mul_nonneg (by linarith only [hCbd]) hKhinf)
    simp only [stepFourBoundaryDeltaC1]
    linarith only [hleg1, hleg2, hleg3]
  · -- `hstep4` on the boundary branch, at the shifted index
    rw [hcast] at hj1 ⊢
    exact hstep u hdat g Kg Kh hKg0 hKh0 hsol hgL2 hgW hhW hgHol hhHol hsup hgradh c
      slope hmin j hj1 hj2 hj3

/-! ## 4. The boundary Step 6, in the chain's `hosc` shape -/

/-- **The printed boundary `∇h` datum leg** — `α`-free, `γ`-free, `δ`-free, and a
multiple of `3^{m/2} K_h`:

```text
   dataH^print_∂ = C_ah·3^{m/2}(1+C_gag)K_h/(1-3^{-1/2})
                     + (4/log 3)·(2 C_bd 3^{m/2} K_h) .
```

The absolute constant `4/log 3` is the price's `ε`-funded absorption; no
`(1-α)^{-1}` occurs, because's boundary `δ` carries no `ε`-free flat summand. -/
def edBoundaryDataHPrinted (d : ℕ) [NeZero d] (Cb C : ℝ) (k : ℕ) (Kh : ℝ) (m : ℤ) :
    ℝ :=
  edBoundaryCah d Cb C k *
      ((3 : ℝ) ^ ((m : ℝ) / 2) * (Kh * (1 + stepFourGagliardoConst d stepOneS))) /
    (1 - stepFiveRatioH) +
  4 / Real.log 3 *
    (2 * edBoundaryCbd d Cb C k * (Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh))

/-- **`t.regularity` Step 6 on the boundary branch, in the Step-7 chain's own
`hosc` slot.**

The `ε`-funded absorption at `ind := 1`, re-grouped so the produced data leg is
a single `dataG + dataH^print_∂` bracket at one constant `C + C²` — exactly the
shape `StepSevenCaccFinalChain`'s `hosc` reads (there at `H = 0`). -/
theorem stepSixBoundary_oscSlot_of_epsFunded (d : ℕ) {Cedos Cann Citer C alpha : ℝ}
    {k : ℕ} {n m : ℤ} {oscLo oscHi dataG Khleg Hinf Se : ℝ} (hC : 0 ≤ C)
    (hCiter : 0 ≤ Citer) (halpha : alpha ≤ 1) (hnm : n ≤ m) (hoscHi : 0 ≤ oscHi)
    (hdataG : 0 ≤ dataG) (hKhleg : 0 ≤ Khleg) (hHinf : 0 ≤ Hinf) (hSe0 : 0 ≤ Se)
    (hSe : Se ≤ 2 * stepOneDelta (stepOneC1 d Cedos Cann Citer k) alpha *
      ((m : ℝ) - (n : ℝ)))
    (hiter : oscLo ≤
        C * Real.exp ((stepOneC1 d Cedos Cann Citer k)⁻¹ * Citer *
              stepSixExponent alpha n m) * (oscHi + C * dataG) +
          C * Real.exp ((stepOneC1 d Cedos Cann Citer k)⁻¹ * Citer *
              stepSixExponent alpha n m) * (Khleg + Se * Hinf)) :
    oscLo ≤
      (C + C * C) * Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) * oscHi +
        (C + C * C) * Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) *
          (dataG + (Khleg + 4 / Real.log 3 * Hinf)) := by
  have hlog : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hR : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) :=
    Real.rpow_nonneg (by norm_num) _
  have hbase := stepSixBoundary_holderBound_epsFunded d (Cedos := Cedos) (Cann := Cann)
    (Citer := Citer) (k := k) (ind := 1) hC hCiter halpha hnm hoscHi hdataG hKhleg
    hHinf zero_le_one hSe0 hSe (oscLo := oscLo) (by simpa only [mul_one] using hiter)
  have hslack : (0 : ℝ) ≤ C * C *
      (Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) *
        (4 / Real.log 3 * Hinf)) :=
    mul_nonneg (mul_nonneg hC hC)
      (mul_nonneg hR (mul_nonneg (le_of_lt (div_pos (by norm_num) hlog)) hHinf))
  have hid : (C + C * C) *
        Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) *
          (oscHi + dataG + Khleg * 1) +
        C * (4 / Real.log 3 *
          Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) * (Hinf * 1)) +
        C * C * (Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) *
          (4 / Real.log 3 * Hinf))
      = (C + C * C) * Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) * oscHi +
        (C + C * C) * Real.rpow (3 : ℝ) (1 / 2 * stepSixExponent alpha n m) *
          (dataG + (Khleg + 4 / Real.log 3 * Hinf)) := by
    ring
  linarith only [hbase, hslack, hid]

/-- **`e.oscillation.Holder.bound` printed lattice centre.**

`edFinal_oscillationIterationResult_boundaryC1` composed with the boundary
Step 6: the interior endpoint's shape with the same `dataG` and a nonzero
printed `dataH^print_∂`. -/
theorem edFinal_oscillationHolderBound_boundaryC1 (d : ℕ) [NeZero d] (hd : d ≠ 0) :
    ∃ C Ccap Cb Cann : ℝ, 0 < C ∧ 0 < Ccap ∧ 0 ≤ Cb ∧ 0 < Cann ∧ ∃ k₀ : ℕ, 3 ≤ k₀ ∧
      ∀ k : ℕ, k₀ ≤ k →
        ∃ Cout Citer : ℝ, 0 < Cout ∧ 0 ≤ Citer ∧
          ∀ (M : ABKModel d) (m0 : ℤ) (Ecap : {E : ℝ // 1 ≤ E}),
            Algsuperdiff.Frozen.Section3.inductionState M m0 Ecap →
            M.gamma < 1 / 2 →
            M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
            M.gamma ≤ Ccap⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
            M.gamma ≤ Cann⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
            M.gamma ≤ 1 / 256 →
            ∀ (Cedos Cannp alpha : ℝ), alpha ≤ 1 →
              stepOneDelta (stepOneC1 d Cedos Cannp Citer (k + 1)) alpha ∈
                  Set.Ioc (0 : ℝ) (1 / 2) →
              stepOneDelta (stepOneC1 d Cedos Cannp Citer (k + 1)) alpha ≤
                  64 * (C ^ (2 : ℕ))⁻¹ * stepOneS ^ (6 : ℕ) →
              M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
                  Real.rpow stepOneSEighth (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) *
                    stepOneEp (stepOneDelta (stepOneC1 d Cedos Cannp Citer (k + 1))
                      alpha) →
              edBridgeEpsConstGen d (max (schauderWindowConst d) Cb) C k * Ccap *
                    Real.rpow stepOneS (-(3 : ℝ)) *
                    Real.sqrt (stepOneDelta (stepOneC1 d Cedos Cannp Citer (k + 1))
                      alpha) ≤
                  (1 / 2 : ℝ) * (3 : ℝ) ^ (-(1 / 4 : ℝ) * ((k : ℝ) + 1)) →
              ∀ L m n : ℤ, m ≤ L → m ≤ m0 → (14 : ℤ) ≤ m - n →
                ∀ v : Fin d → ℤ, v ∈ Support.latticeCubeSet d n m →
                  ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
                    GoodScaleWindows M stepOneSEighth
                        (stepOneDelta (stepOneC1 d Cedos Cannp Citer (k + 1)) alpha)
                        stepOneSEighth_pos n m omega →
                    (((stepThreeBadSet M
                          (stepOneDelta (stepOneC1 d Cedos Cannp Citer (k + 1)) alpha)
                          n m (Support.triadicLatticePoint n v) omega).card : ℝ)) ≤
                        stepOneDelta (stepOneC1 d Cedos Cannp Citer (k + 1)) alpha *
                          (((m : ℝ) - (n : ℝ)) + 1) →
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
                          IsAffineMinimizer
                            (stepThreeWindow (Support.triadicLatticePoint n v) m j)
                            u.toFun (c j) (slope j)) →
                        ∀ n' m' : ℤ, n ≤ n' → n' ≤ m' → m' ≤ m →
                          (3 : ℝ) ^ (-n') *
                              normalizedL2On
                                (truncatedWindow
                                  (Support.triadicLatticePoint n v) m n')
                                (fun x => u.toFun x -
                                  volumeAverage
                                    (truncatedWindow
                                      (Support.triadicLatticePoint n v) m n')
                                    u.toFun) ≤
                            (Cout + Cout * Cout) *
                                Real.rpow (3 : ℝ)
                                  (1 / 2 * stepSixExponent alpha n m) *
                                ((3 : ℝ) ^ (-m') *
                                  normalizedL2On
                                    (truncatedWindow
                                      (Support.triadicLatticePoint n v) m m')
                                    (fun x => u.toFun x -
                                      volumeAverage
                                        (truncatedWindow
                                          (Support.triadicLatticePoint n v) m m')
                                        u.toFun)) +
                              (Cout + Cout * Cout) *
                                Real.rpow (3 : ℝ)
                                  (1 / 2 * stepSixExponent alpha n m) *
                                (edFinalDataG M (edBoundaryCbd d Cb C k)
                                    (Kg * stepFourGagliardoConst d stepOneS) m +
                                  edBoundaryDataHPrinted d Cb C k Kh m) := by
  classical
  obtain ⟨C, Ccap, Cb, Cann, hC, hCcap, hCb, hCann, k₀, hk₀, hiterres⟩ :=
    edFinal_oscillationIterationResult_boundaryC1 d hd
  refine ⟨C, Ccap, Cb, Cann, hC, hCcap, hCb, hCann, k₀, hk₀, ?_⟩
  intro k hk
  obtain ⟨Cout, Citer, hCout, hCiter, hres⟩ := hiterres k hk
  refine ⟨Cout, Citer, hCout, hCiter, ?_⟩
  intro M m0 Ecap hS hgamma hregime hregimecap hregimeAnn hgamma256 Cedos Cannp alpha
    halpha hdelta hprice hsmall hgate L m n hmL hmm0 hwin v hv
  set delta := stepOneDelta (stepOneC1 d Cedos Cannp Citer (k + 1)) alpha with hdeltadef
  have hnm : n ≤ m := by omega
  have hmnR : (0 : ℝ) ≤ (m : ℝ) - (n : ℝ) := by
    have hcast : ((n : ℤ) : ℝ) ≤ ((m : ℤ) : ℝ) := Int.cast_le.mpr hnm
    linarith only [hcast]
  have hSeNN : (0 : ℝ) ≤ 2 * delta * ((m : ℝ) - (n : ℝ)) := by
    have h := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hdelta.1.le) hmnR
    linarith only [h]
  filter_upwards [hres M m0 Ecap hS hgamma hregime hregimecap hregimeAnn hgamma256
    Cedos Cannp alpha halpha hdelta hprice hsmall hgate L m n hmL hmm0 hwin v hv]
    with omega hom
  intro hgood hBz u hdat g Kg Kh hKg0 hKh0 hsol hgL2 hgW hhW hgHol hhHol hsup hgradh
    c slope hmin n' m' hn' hn'm' hm'm
  have hbase := hom hgood hBz u hdat g Kg Kh hKg0 hKh0 hsol hgL2 hgW hhW hgHol hhHol
    hsup hgradh c slope hmin n' m' hn' hn'm' hm'm
  have hKgT : (0 : ℝ) ≤ Kg * stepFourGagliardoConst d stepOneS :=
    mul_nonneg hKg0 (stepFourGagliardoConst_nonneg d stepOneS)
  have hoscHi : (0 : ℝ) ≤ (3 : ℝ) ^ (-m') *
      normalizedL2On
        (truncatedWindow (Support.triadicLatticePoint n v) m m')
        (fun x => u.toFun x -
          volumeAverage
            (truncatedWindow (Support.triadicLatticePoint n v) m m') u.toFun) :=
    mul_nonneg (zpow_nonneg (by norm_num) _) (normalizedL2On_nonneg _ _)
  refine stepSixBoundary_oscSlot_of_epsFunded d (Cedos := Cedos) (Cann := Cannp)
    (Citer := Citer) (k := k + 1) hCout.le hCiter halpha hnm hoscHi
    (edFinalDataG_nonneg hgamma (edBoundaryCbd_nonneg d Cb hC.le k) hKgT m)
    (edBoundaryKhleg_nonneg d Cb (C := C) (Kh := Kh) hC.le k hKh0 m)
    (edBoundaryHinf_nonneg d Cb (C := C) (Kh := Kh) hC.le k hKh0 m) hSeNN
    (le_refl _) ?_
  simpa only [edBoundaryDataH, stepThreeWindow] using hbase

/-! ## 5. The two boundary funding floors -/

/-- **The boundary Step-4 `δ`-cap, from a pure `C₁`-floor.**

`stepFourDecay_boundary_pinned`'s `δ`-cap `δ ≤ 64C^{-2}s^6` is met by every `δ
= C₁^{-1}(1-α)` with `α ≥ 0` once `C₁ ≥ 64C²`, because `s = 1/4` makes the cap
exactly `(64C²)^{-1}`. -/
theorem edBoundary_deltaCap_of_c1_floor {C C1 alpha : ℝ} (hC : 0 < C)
    (halpha0 : 0 ≤ alpha) (hC1 : 0 < C1) (hfloor : 64 * C ^ (2 : ℕ) ≤ C1) :
    stepOneDelta C1 alpha ≤ 64 * (C ^ (2 : ℕ))⁻¹ * stepOneS ^ (6 : ℕ) := by
  have hCsq : (0 : ℝ) < C ^ (2 : ℕ) := pow_pos hC 2
  have hfl : (0 : ℝ) < 64 * C ^ (2 : ℕ) := by linarith only [hCsq]
  have hdle : stepOneDelta C1 alpha ≤ C1⁻¹ := by
    rw [stepOneDelta]
    have h1 : (1 : ℝ) - alpha ≤ 1 := by linarith only [halpha0]
    have h2 := mul_le_mul_of_nonneg_left h1 (inv_pos.mpr hC1).le
    rw [mul_one] at h2
    exact h2
  have hinv : C1⁻¹ ≤ (64 * C ^ (2 : ℕ))⁻¹ := by
    exact inv_anti₀ hfl hfloor
  have hval : 64 * (C ^ (2 : ℕ))⁻¹ * stepOneS ^ (6 : ℕ) = (64 * C ^ (2 : ℕ))⁻¹ := by
    have hs : stepOneS ^ (6 : ℕ) = 1 / 4096 := by rw [stepOneS]; norm_num
    rw [hs]
    field_simp
    ring
  linarith only [hdle, hinv, hval]

theorem edBridgeEpsConstGen_nonneg' (d : ℕ) [NeZero d] {Cs C : ℝ} (hCs : 0 ≤ Cs)
    (hC : 0 ≤ C) (k : ℕ) : 0 ≤ edBridgeEpsConstGen d Cs C k := by
  have hrw : (0 : ℝ) ≤ edBridgeRemWeightGen d Cs k := edBridgeRemWeightGen_nonneg d hCs k
  have hep : (1 : ℝ) ≤ endpointConst d (1 / 9 : ℝ) := one_le_endpointConst (by norm_num)
  rw [edBridgeEpsConstGen]
  exact mul_nonneg (mul_nonneg (by linarith only [hrw]) hC) (by linarith only [hep])

/-- **The boundary Step-4 smallness gate, from a pure `C₁`-floor.**

`RootClauseBFinalFunding.edFunding_of_c1_floor`'s sibling for the boundary lane:
the gate

```text
   C_{eps,gen}(d,C_s,C,k)·C_cap·s^{-3}·√δ  ≤  ½·3^{-(k+1)/4}
```

holds at every `δ = C₁^{-1}(1-α)` with `α ≥ 0` once `C₁` clears the explicit
floor `(2·C_{eps,gen}·C_cap·s^{-3}·3^{(k+1)/4})²`.  No division and no
positivity of the constant is needed — the argument is `√δ ≤ (√C₁)^{-1}` and
one cross multiplication. -/
def edBoundaryFundFloor (d : ℕ) [NeZero d] (Cb C Ccap : ℝ) (k : ℕ) : ℝ :=
  (2 * (edBridgeEpsConstGen d (max (schauderWindowConst d) Cb) C k * Ccap *
      Real.rpow stepOneS (-(3 : ℝ))) *
    Real.rpow (3 : ℝ) (1 / 4 * ((k : ℝ) + 1))) ^ (2 : ℕ)

theorem edBoundaryFunding_of_c1_floor (d : ℕ) [NeZero d] {Cb C Ccap C1 alpha : ℝ}
    {k : ℕ} (hC : 0 ≤ C) (hCcap : 0 ≤ Ccap) (halpha0 : 0 ≤ alpha) (hC1 : 0 < C1)
    (hfloor : edBoundaryFundFloor d Cb C Ccap k ≤ C1) :
    edBridgeEpsConstGen d (max (schauderWindowConst d) Cb) C k * Ccap *
        Real.rpow stepOneS (-(3 : ℝ)) * Real.sqrt (stepOneDelta C1 alpha) ≤
      (1 / 2 : ℝ) * (3 : ℝ) ^ (-(1 / 4 : ℝ) * ((k : ℝ) + 1)) := by
  set T : ℝ := Real.rpow (3 : ℝ) (1 / 4 * ((k : ℝ) + 1)) with hTdef
  set Q : ℝ := edBridgeEpsConstGen d (max (schauderWindowConst d) Cb) C k * Ccap *
    Real.rpow stepOneS (-(3 : ℝ)) with hQdef
  have hT : (0 : ℝ) < T := Real.rpow_pos_of_pos (by norm_num) _
  have hQ : (0 : ℝ) ≤ Q := by
    rw [hQdef]
    exact mul_nonneg (mul_nonneg (edBridgeEpsConstGen_nonneg' d
      (le_trans (schauderWindowConst_nonneg d) (le_max_left _ _)) hC k) hCcap)
      (Real.rpow_nonneg stepOneS_pos.le _)
  have hfl2 : (2 * Q * T) ^ (2 : ℕ) ≤ C1 := by
    rw [hQdef, hTdef]
    exact hfloor
  have hsc : (0 : ℝ) < Real.sqrt C1 := Real.sqrt_pos.mpr hC1
  have hdle : stepOneDelta C1 alpha ≤ C1⁻¹ := by
    rw [stepOneDelta]
    have h1 : (1 : ℝ) - alpha ≤ 1 := by linarith only [halpha0]
    have h2 := mul_le_mul_of_nonneg_left h1 (inv_pos.mpr hC1).le
    rw [mul_one] at h2
    exact h2
  have hsq : Real.sqrt (stepOneDelta C1 alpha) ≤ (Real.sqrt C1)⁻¹ := by
    have h := Real.sqrt_le_sqrt hdle
    rwa [Real.sqrt_inv] at h
  have hfl : 2 * Q * T ≤ Real.sqrt C1 := by
    have h0 : (0 : ℝ) ≤ 2 * Q * T := mul_nonneg (by linarith only [hQ]) hT.le
    have h := Real.sqrt_le_sqrt hfl2
    rwa [Real.sqrt_sq h0] at h
  have hmul : (0 : ℝ) ≤ (Real.sqrt C1)⁻¹ * (2 * T)⁻¹ :=
    mul_nonneg (inv_nonneg.mpr hsc.le) (inv_nonneg.mpr (by linarith only [hT]))
  have hcross := mul_le_mul_of_nonneg_right hfl hmul
  have e1 : 2 * Q * T * ((Real.sqrt C1)⁻¹ * (2 * T)⁻¹) = Q * (Real.sqrt C1)⁻¹ := by
    field_simp
  have e2 : Real.sqrt C1 * ((Real.sqrt C1)⁻¹ * (2 * T)⁻¹) = 1 / 2 * T⁻¹ := by
    field_simp
  rw [e1, e2] at hcross
  have hexp : (3 : ℝ) ^ (-(1 / 4 : ℝ) * ((k : ℝ) + 1)) = T⁻¹ := by
    rw [hTdef, show (-(1 / 4 : ℝ) * ((k : ℝ) + 1)) = -(1 / 4 * ((k : ℝ) + 1)) from by
      ring]
    exact Real.rpow_neg (by norm_num) _
  rw [hexp]
  calc Q * Real.sqrt (stepOneDelta C1 alpha)
      ≤ Q * (Real.sqrt C1)⁻¹ := mul_le_mul_of_nonneg_left hsq hQ
    _ ≤ 1 / 2 * T⁻¹ := hcross


end

end Algsuperdiff.Section4.Provider.Regularity
