/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootClauseBBoundaryOscFloor

/-!
# OscillationFamily

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The truncated-window oscillation family at triadic lattice centres

This module assembles, below the frozen surface, the two-parameter oscillation
estimate of [ABK] `e.oscillation.Holder.bound` for the zero-boundary-datum
Dirichlet problem of the cutoff field on the cube `□_m`.

For a scale `m`, a truncation index `L ≥ m`, a bottom scale `n` admissible for
the minimal scale `X` and a lattice centre `z = 3 ^ n v ∈ 3 ^ n ℤ^d ∩ □_m`, the
family is stated on the truncated windows `U_j = (z + □_j) ∩ □_m` and reads, for
every `n ≤ n' ≤ m' ≤ m`,

```text
   3 ^ (-n') ‖u - (u)_{U_{n'}}‖_{L²(U_{n'})}
     ≤ Cosc · 3 ^ ((1/2)(1-α)(m-n))
         ( 3 ^ (-m') ‖u - (u)_{U_{m'}}‖_{L²(U_{m'})}
           + Cdata · σ_m⁻¹ 3 ^ (m/2) K_g ) ,
```

with `K_g` a `C^{0,1/2}` seminorm bound for the force on `□_m`.  The exponent
`1/2` is the source's `β`.  There is no boundary-datum leg: at zero datum the
`∇h` term of the source's `δ_j` budget vanishes identically.

The minimal scale is the one the excess-decay chain builds, `X = Z + k + 3` at
the Step-1 parameters, and it is returned with the same measurability and the
same exponential tail that the regularity theorem of Section 4 carries, so a
consumer may read the tail from either.

## Main definitions

* `oscillationDataConst` — the model-free amplitude of the force leg.

## Main results

* `oscillationHolderBound_zeroDatum` — the family, almost surely, at every
  truncation index, every admissible bottom scale, every lattice centre of the
  cube, and every intermediate pair of scales.

## References

* [ABK], `ss.proof.regularity` Steps 4--6, display `e.oscillation.Holder.bound`.
-/

namespace Algsuperdiff.Section4.Provider.Holder

open HCPolySupport MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.Regularity
open Algsuperdiff.Section4.Provider.ExcessDecay
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The zero boundary datum -/

/-- The zero element of `H¹` has the zero value field. -/
theorem zeroH1_toFun {U : Set (Vec d)} :
    (0 : H1Function U).toFun = (0 : Vec d → ℝ) := rfl

/-- At the zero datum every Hölder seminorm bound holds with constant `0`. -/
theorem holderSeminormBoundOn_zeroH1_grad {U : Set (Vec d)} (alpha : ℝ) :
    HolderSeminormBoundOn U alpha 0 (0 : H1Function U).grad := by
  intro x _ y _
  simp

/-- At the zero datum the pointwise gradient cap holds with constant `0`. -/
theorem norm_zeroH1_grad_le {U : Set (Vec d)} (m : ℤ) :
    ∀ y ∈ U, ‖(0 : H1Function U).grad y‖ ≤ Real.rpow (3 : ℝ) ((m : ℝ) / 2) * 0 := by
  intro y _
  simp

/-- The zero datum is classically differentiable with the zero gradient field. -/
theorem hasGradientOn_zeroH1 {U : Set (Vec d)} :
    HasGradientOn U (0 : H1Function U).toFun (0 : H1Function U).grad := by
  intro y _
  have hz : slopeCLM ((0 : H1Function U).grad y) = (0 : Vec d →L[ℝ] ℝ) := by
    refine ContinuousLinearMap.ext ?_
    intro v
    simp [vecDot]
  rw [zeroH1_toFun, hz]
  exact hasFDerivWithinAt_const (0 : ℝ) y U

/-- The printed boundary `∇h` datum leg vanishes at the zero datum: both of its
summands carry the factor `K_h`. -/
theorem edBoundaryDataHPrinted_zero (d : ℕ) [NeZero d] (Cb C : ℝ) (k : ℕ) (m : ℤ) :
    edBoundaryDataHPrinted d Cb C k 0 m = 0 := by
  simp [edBoundaryDataHPrinted]

/-! ## 2. The amplitude of the force leg -/

/-- **The model-free amplitude of the force leg.**  The Step-5 budget's weight
`4 C_δ / (1 - 3 ^ (-(1/2 - γ)))` is enlarged to the `γ`-free
`4 C_δ / (1 - 3 ^ (-1/4))` and multiplied by the Step-4 Gagliardo constant that
converts the printed `C^{0,1/2}` seminorm of the force into the fractional
seminorm the excess-decay lane reads. -/
def oscillationDataConst (d : ℕ) [NeZero d] (Cb C : ℝ) (k : ℕ) : ℝ :=
  rootClauseBOscWUniform (edBoundaryCbd d Cb C k) * stepFourGagliardoConst d stepOneS

theorem oscillationDataConst_nonneg (d : ℕ) [NeZero d] (Cb : ℝ) {C : ℝ} (hC : 0 ≤ C)
    (k : ℕ) : 0 ≤ oscillationDataConst d Cb C k :=
  mul_nonneg (rootClauseBOscWUniform_nonneg (edBoundaryCbd_nonneg d Cb hC k))
    (stepFourGagliardoConst_nonneg d stepOneS)

/-- **The force leg, in the gauge the source prints.**  The excess-decay lane's
own data leg is at most the amplitude times `σ_m⁻¹ 3 ^ (m/2) K_g`. -/
theorem edFinalDataG_le_oscillationDataConst (d : ℕ) [NeZero d] {M : ABKModel d}
    (hgamma : M.gamma < 1 / 2) (hquarter : M.gamma ≤ 1 / 4) (Cb : ℝ) {C Kg : ℝ}
    (hC : 0 ≤ C) (hKg : 0 ≤ Kg) (k : ℕ) (m : ℤ) :
    edFinalDataG M (edBoundaryCbd d Cb C k) (Kg * stepFourGagliardoConst d stepOneS) m ≤
      oscillationDataConst d Cb C k *
        (((Annealed.sigmaBar M m : ℝ))⁻¹ * Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg) := by
  have hCbd : (0 : ℝ) ≤ edBoundaryCbd d Cb C k := edBoundaryCbd_nonneg d Cb hC k
  have hgag : (0 : ℝ) ≤ stepFourGagliardoConst d stepOneS :=
    stepFourGagliardoConst_nonneg d stepOneS
  have hleg : (0 : ℝ) ≤
      ((Annealed.sigmaBar M m : ℝ))⁻¹ * Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg :=
    mul_nonneg (mul_nonneg (inv_nonneg.mpr (Annealed.sigmaBar M m).2.le)
      (Real.rpow_nonneg (by norm_num) _)) hKg
  have hW : edFinalDataOscW M (edBoundaryCbd d Cb C k) * stepFourGagliardoConst d stepOneS ≤
      oscillationDataConst d Cb C k := by
    rw [oscillationDataConst]
    exact mul_le_mul_of_nonneg_right
      (edFinalDataOscW_le_uniform hgamma hquarter hCbd) hgag
  have hid : edFinalDataG M (edBoundaryCbd d Cb C k)
        (Kg * stepFourGagliardoConst d stepOneS) m =
      (edFinalDataOscW M (edBoundaryCbd d Cb C k) * stepFourGagliardoConst d stepOneS) *
        (((Annealed.sigmaBar M m : ℝ))⁻¹ * Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg) := by
    have h := edFinalDataG_eq_dataOsc_scaled M (edBoundaryCbd d Cb C k) Kg
      (stepFourGagliardoConst d stepOneS) m
    rw [edFinalDataOscG] at h
    have h' : edFinalDataG M (edBoundaryCbd d Cb C k)
        (Kg * stepFourGagliardoConst d stepOneS) m + 0 =
        (edFinalDataOscW M (edBoundaryCbd d Cb C k) *
            stepFourGagliardoConst d stepOneS) *
          (((Annealed.sigmaBar M m : ℝ))⁻¹ *
            (Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg) + 0) := h
    rw [add_zero, add_zero] at h'
    rw [h']
    ring
  rw [hid]
  exact mul_le_mul_of_nonneg_right hW hleg

/-! ## 3. The oscillation family -/

/-- **[ABK] `e.oscillation.Holder.bound` at zero boundary datum.**

For a disorder model of strength `gamma` small enough and every Hölder exponent
`alpha` below `1 - C sqrt gamma`, and for every scale `m`, there is a minimal
scale `X` -- measurable, with the exponential tail of the regularity theorem --
such that, almost surely, for every truncation index `L ≥ m`, every bottom scale
`n ≤ m` admissible for `X`, every lattice centre `z = 3 ^ n v` of the cube, every
zero-datum Dirichlet solution `u` on `□_m` with force `g` of `C^{0,1/2}`
seminorm at most `K_g`, and every pair of scales `n ≤ n' ≤ m' ≤ m`, the
normalized oscillation on the truncated window `U_{n'} = (z + □_{n'}) ∩ □_m` is
bounded by `3 ^ ((1/2)(1-alpha)(m-n))` times the oscillation on `U_{m'}` plus
the force leg `σ_m⁻¹ 3 ^ (m/2) K_g`.

The exponent `1/2` is the source's `β`; the boundary-datum leg of the source's
display vanishes at zero datum. -/
theorem oscillationHolderBound_zeroDatum (d : ℕ) [NeZero d] (hd : d ≠ 0)
    (cstar : ℝ) (hcstar : 0 < cstar) :
    ∃ gamma0 C Cosc Cdata : ℝ, 0 < gamma0 ∧ 0 < C ∧ 0 ≤ Cosc ∧ 0 ≤ Cdata ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ 1 - C * Real.sqrt M.gamma →
          ∀ m : ℤ, ∃ X : Cutoff.CutoffSample d → ℕ∞,
            Measurable X ∧
            (∀ N : ℕ,
                (Cutoff.cutoffSampleLaw M).toMeasure {omega | (N : ℕ∞) ≤ X omega} ≤
                  ENNReal.ofReal
                    (C * Real.exp
                      (-((1 - alpha) ^ (2 : ℕ) * ((N : ℝ) - C)) / (C * M.gamma)))) ∧
            ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
              ∀ L n : ℤ, m ≤ L → n ≤ m →
                X omega ≤ (((m - n).toNat : ℕ) : ℕ∞) →
                ∀ v : Fin d → ℤ, v ∈ latticeCubeSet d n m →
                  ∀ (u : H1Function (openCubeSet (originCube d m)))
                    (g : Vec d → Vec d) (Kg : ℝ), 0 ≤ Kg →
                    IsDirichletSolutionOn
                        (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                        (originCube d m) u 0 g →
                    HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kg g →
                    ∀ n' m' : ℤ, n ≤ n' → n' ≤ m' → m' ≤ m →
                      (3 : ℝ) ^ (-n') *
                          normalizedL2On
                            (truncatedWindow (triadicLatticePoint n v) m n')
                            (fun y => u.toFun y -
                              volumeAverage
                                (truncatedWindow (triadicLatticePoint n v) m n')
                                u.toFun) ≤
                        Cosc *
                            Real.rpow (3 : ℝ)
                              (1 / 2 * ((1 - alpha) * ((m : ℝ) - (n : ℝ)))) *
                          ((3 : ℝ) ^ (-m') *
                              normalizedL2On
                                (truncatedWindow (triadicLatticePoint n v) m m')
                                (fun y => u.toFun y -
                                  volumeAverage
                                    (truncatedWindow (triadicLatticePoint n v) m m')
                                    u.toFun) +
                            Cdata *
                              (((Annealed.sigmaBar M m : ℝ))⁻¹ *
                                Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg)) := by
  classical
  obtain ⟨Cstep, Ccap, Cann, Cb, Cfl, Citer, Cosc, kb, hCstep, hCcap, hCann, hCb,
    hCfl, hCosc, hk10, hoscprod⟩ := exists_rootClauseBOsc_boundary_floor d hd
  obtain ⟨Cind, hCind6, -, hind⟩ :=
    Algsuperdiff.Section4.Provider.GoodEvents.exists_allScalesInductionState_ge d 0
  have hCindpos : (0 : ℝ) < Cind := by linarith only [hCind6]
  obtain ⟨g0P, CP, hg0P, hCP, -, -, -, hpack⟩ :=
    rootAssembly_aePackage d cstar hcstar Cfl Citer 1 (kb + 1) (by omega)
  have hC1two : (2 : ℝ) ≤ stepOneC1 d Cfl 1 Citer (kb + 1) :=
    two_le_stepOneC1 d Cfl 1 Citer (kb + 1)
  have hC1pos : (0 : ℝ) < stepOneC1 d Cfl 1 Citer (kb + 1) := by linarith only [hC1two]
  have hCmaxpos : (0 : ℝ) < max Cstep Ccap := lt_of_lt_of_le hCstep (le_max_left _ _)
  obtain ⟨g0F, hg0F, hfacts⟩ :=
    exists_rootClauseBGammaFacts d (C := max Cstep Ccap) (Cann := Cann) (Cind := Cind)
      (C1 := stepOneC1 d Cfl 1 Citer (kb + 1)) (Crg := CP) hcstar hCmaxpos hCann
      hCindpos hC1pos hCP
  refine ⟨min g0P g0F, CP, Cosc, oscillationDataConst d Cb Cstep kb,
    lt_min hg0P hg0F, hCP, hCosc,
    oscillationDataConst_nonneg d Cb hCstep.le kb, ?_⟩
  intro M hcs hgamma alpha halpha0 halpha m
  have hfact := hfacts M hcs (le_trans hgamma (min_le_right _ _))
  have hgpos : 0 < M.gamma := M.shellPrefix.gamma_pos
  have halpha1 : alpha < 1 := by
    have h : 0 < CP * Real.sqrt M.gamma := mul_pos hCP (Real.sqrt_pos.mpr hgpos)
    linarith only [halpha, h]
  have hcs10 : (0 : ℝ) ≤ Disorder.cstar M ^ (10 : ℕ) :=
    pow_nonneg ((Disorder.cstar_characterization M).1).le 10
  have hregC : M.gamma ≤ Cstep⁻¹ * Disorder.cstar M ^ (10 : ℕ) :=
    le_trans hfact.regimeC
      (mul_le_mul_of_nonneg_right (inv_anti₀ hCstep (le_max_left _ _)) hcs10)
  have hregCap : M.gamma ≤ Ccap⁻¹ * Disorder.cstar M ^ (10 : ℕ) :=
    le_trans hfact.regimeC
      (mul_le_mul_of_nonneg_right (inv_anti₀ hCcap (le_max_right _ _)) hcs10)
  obtain ⟨Ecap, -, -, hstate⟩ := hind M hfact.regimeInd
  obtain ⟨Z, hXmeas, hXtail, hXpay⟩ :=
    hpack M hcs (le_trans hgamma (min_le_left _ _)) alpha halpha0 halpha m
  refine ⟨minimalScaleX Z (kb + 1), hXmeas, hXtail, ?_⟩
  have haeOsc := hoscprod Cfl le_rfl M m Ecap (hstate m) hfact.ltHalf hregC hregCap
    hfact.regimeAnn hfact.le256 alpha halpha0 halpha1
    (hfact.smallEp alpha halpha0 halpha) m le_rfl
  filter_upwards [haeOsc, hXpay] with omega hOsc hPay
  intro L n hmL hnm hgate v hv u g Kg hKg hsol hgHol n' m' hn' hn'm' hm'm
  have hpay := hPay n hnm hgate
  have hbase := hOsc L n v hmL hpay.2.1 hv hpay u 0 g Kg 0 hKg le_rfl hsol hgHol
    (holderSeminormBoundOn_zeroH1_grad (1 / 2)) (norm_zeroH1_grad_le m)
    hasGradientOn_zeroH1 n' m' hn' hn'm' hm'm
  simp only [stepSixExponent, edBoundaryDataHPrinted_zero d Cb Cstep kb m,
    add_zero] at hbase
  have hP : (0 : ℝ) ≤
      Real.rpow (3 : ℝ) (1 / 2 * ((1 - alpha) * ((m : ℝ) - (n : ℝ)))) :=
    Real.rpow_nonneg (by norm_num) _
  have hdataG := edFinalDataG_le_oscillationDataConst d hfact.ltHalf hfact.leQuarter
    Cb hCstep.le hKg kb m
  have hmul := mul_le_mul_of_nonneg_left hdataG (mul_nonneg hCosc hP)
  linarith only [hbase, hmul]

end

end Algsuperdiff.Section4.Provider.Holder
