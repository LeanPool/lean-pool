/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepFourFinalInterior
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepFiveDeltaSum
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepFiveIterationResult

/-!
# StepFourFinalIteration

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `hstep4`, discharged on the interior branch

## What this module is

`StepFiveIterationResult.iterationDecay_of_stepFourDecay` takes one
mathematical input, `hstep4`.  This module produces it on the interior branch,
from the frozen statements and the supply events alone:

```text
   ∀ j ∈ [n+k, m-1] ∖ 𝓑_z ,
     E(u, U_{j-k}) ≤ θ^k E(u, U_j) + C_ε ε_j(z,ω) |∇ℓ_j| + δ_j ,
   U_j = stepThreeWindow z m j ,  θ = 3^{-1/4} ,
   δ_j = C_δ 3^{j/2} σ_j^{-1} ( K_g C_{S4.4}(d,s) ) .
```

`ε_j` is `StepFiveBudgetSums.stepFiveEps` — the Step-5 slot itself, at the
unshifted index `j` (the interior clause reads its event and its flux
representative at the printed index), carrying the coefficient
`C_ε = edFinalEpsCoeff`.  `δ_j` is the `g`-leg of the Step-5 family at the
root's own Hölder datum `K_g`: there is no `∇h` leg and no boundary indicator, so the
ungated non-decaying flat leg does not arise either.

## The three pins

* **`s := 1/4`** (`stepOneS`).  At that value the excess-decay supply event
  `𝒢(j, z; s/8, (s/8)√δ)` and the Step-3/Step-1 good event `𝒢(j, z; s/8, ε(δ))`
  are the same term — `event_pin` is `rfl`.  It is also what makes `γ ≤ 1/256`
  deliver the excess-decay binder `s ∈ [64γ, 1]` and `s < 1/2` deliver the
  Gagliardo index range.
* **the bad set** is `StepThreeBadSet.stepThreeBadSet` verbatim: `j ∉ 𝓑_z` with
  `n ≤ j ≤ m-1` is the supply event at `j`.
* **the `δ`-gate** (`hgate`) is the absorption inequality at the annular cap
  `ε_j ≤ C_ann ε(δ)`: an explicit hypothesis on `(k, δ)`, and the inequality
  `δ` is chosen to satisfy after `k`.  It is a hypothesis, not a smuggled fact.

## References

* ABK26, `t.regularity` Steps 1--5; `l.excess.decay.good.scales`.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open Algsuperdiff.Section3
open HCPolySupport Algsuperdiff.Section4.Support MeasureTheory
open Algsuperdiff.Section4.Provider.ExcessDecay
open Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

noncomputable section

/-! ## 1. The composed per-scale display -/

/-- **The Step-4 collapse composed at one scale, on the interior branch.**

The two-leg one-step contraction off the anchor's frontier-empty clause, at
`x := z`, with all its carried items discharged from `EdFinalInputs` (the two
gates from `z ∈ □_{m-1}`, the harmonic replacement pair from `u`), and the
Step-4 collapse applied. -/
theorem stepFourDecay_interior_of_anchors (d : ℕ) [NeZero d] (hd : d ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∃ k₀ : ℕ, 3 ≤ k₀ ∧
      ∀ k : ℕ, k₀ ≤ k →
        ∀ (M : ABKModel d) (m0 : ℤ) (Ecap : {E : ℝ // 1 ≤ E}),
          Algsuperdiff.Frozen.Section3.inductionState M m0 Ecap →
          M.gamma ≤ 1 / 4 →
        ∀ s : ℝ, s ∈ Set.Icc (64 * M.gamma) 1 → s < 1 / 2 →
          M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
          M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
              Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) *
                (C⁻¹ * s ^ (4 : ℕ)) →
          ∀ hs : 0 < s,
          ∀ delta : ℝ, delta ≤ 1 →
          ∀ L m : ℤ, m ≤ L → m ≤ m0 →
            ∀ z : Vec d, z ∈ openCubeSet (originCube d (m - 1)) →
              ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
                ∀ n : ℤ, n + 1 ≤ m →
                  omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
                      (cgEllipLowerConstant d) n z ⟨s / 8, by linarith only [hs]⟩
                      (s / 8 * Real.sqrt delta) →
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
                    ∀ Kg epsj : ℝ, 0 ≤ Kg → 0 ≤ epsj →
                      HolderSeminormBoundOn (openCubeSet (originCube d m))
                          (1 / 2) Kg g →
                      fluxCorrectedErrorRepresentative M L n
                          ⟨s / 8, by linarith only [hs]⟩
                          (Cutoff.translateCutoffSample z omega) ≤ epsj →
                      edFinalEpsCoeff d C k s * epsj ≤
                          (1 / 2 : ℝ) * (3 : ℝ) ^ (-(1 / 4 : ℝ) * (k : ℝ)) →
                      ∀ (c : ℝ) (gmin : Vec d),
                        IsAffineMinimizer (stepThreeWindow z m n) u.toFun c gmin →
                        affineExcess (stepThreeWindow z m (n - (k : ℤ))) u.toFun ≤
                          (3 : ℝ) ^ (-(1 / 4 : ℝ) * (k : ℝ)) *
                              affineExcess (stepThreeWindow z m n) u.toFun +
                            edFinalEpsCoeff d C k s * epsj * slopeMagnitude gmin +
                            edFinalDelta M (edFinalDeltaConst d C k s)
                              (Kg * stepFourGagliardoConst d s) n := by
  classical
  obtain ⟨C, hC, htwo⟩ := excessDecay_oneStep_interior_anchored_twoLeg d hd
  obtain ⟨k₀, hk₀, habsorb⟩ := exists_edFinalStep d
  refine ⟨C, hC, k₀, hk₀, ?_⟩
  intro k hk M m0 Ecap hS hgamma s hsrange hshalf hregime hfund hs delta hdelta1 L m
    hmL hmm0 z hzin
  have hk3 : 3 ≤ k := le_trans hk₀ hk
  have hzm : z ∈ openCubeSet (originCube d m) :=
    Algsuperdiff.Section4.Provider.ExcessDecay.openCubeSet_originCube_subset_of_le
      (by omega : m - 1 ≤ m) hzin
  rw [ae_all_iff]
  intro n
  by_cases hnm : n + 1 ≤ m
  · have hgate : ((fun y' : Vec d => z + y') '' openCubeSet (originCube d n)) ∩
        frontier (openCubeSet (originCube d m)) = ∅ :=
      frontier_gate_of_mem_inner hzin (by omega)
    have hcube : (fun y => z + y) '' openCubeSet (originCube d (n - 2)) ⊆
        openCubeSet (originCube d m) :=
      image_add_subset_openCubeSet_of_mem_inner hzin (by omega)
    have hzself : z ∈ truncatedWindow z m (n - 3) := mem_truncatedWindow_self (n - 3) hzm
    filter_upwards [htwo M s hsrange hregime hfund hs delta hdelta1 L m n hmL
      (by omega : n - 2 + 3 ≤ m) z z hzself hzm hgate hcube] with omega hom
    intro _hnm hmem u hdat g hsol hgL2 hgW hhW Kg epsj hKg0 heps0 hhol hEfl hgate2 c gmin hmin
    obtain ⟨v, w, hvharm, hval, hgradv⟩ :=
      exists_harmonicReplacementPair_movedCube (z := z) (by omega : n - 2 ≤ m) u
    have hed := hom hmem u hdat g hsol hgL2 hgW hhW v w hvharm hval hgradv k hk3
    have hu : MemLp u.toFun 2 (volume.restrict (truncatedWindow z m n)) :=
      u.memL2.mono_measure
        (Measure.restrict_mono (truncatedWindow_subset_domain z m n) le_rfl)
    have hOsc := oscLeg_normalized_le_interior hd hzm (by omega : n - 1 ≤ m) hu hmin
    have hSig := sigmaBar_shift_weighted hS hgamma (by omega : n ≤ m0) hs
    have hGsem := stepFourGsemLeg_shift_le (E := Vec d) (z := z) (m := m) (n := n)
      (g := g) (K := Kg) (s := s) (Nat.one_le_iff_ne_zero.mpr hd) hzm hs hshalf hKg0 hhol
    have hres := stepFourDecay_of_twoLegDisplay
      (Exc := fun j => affineExcess (stepThreeWindow z m j) u.toFun)
      (Slp := fun _ => slopeMagnitude gmin) (n := n) (k := k) (d := d)
      (Crem := triangleRemainderConst d (schauderWindowConst d) k)
      (Vd := Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d)) (C := C) (s := s)
      (Efl := fluxCorrectedErrorRepresentative M L n ⟨s / 8, by linarith only [hs]⟩
        (Cutoff.translateCutoffSample z omega))
      (Osc := (MeasureTheory.eLpNorm (fun y => u.toFun y -
          HCPolySupport.volumeAverage (stepThreeWindow z m n) u.toFun) 2
        (normalizedVolumeMeasureOn (stepThreeWindow z m n))).toReal)
      (Gsem := (normalizedGagliardoESeminormOn (stepThreeWindow z m n) s g).toReal)
      (SigInv2 := ((Annealed.sigmaBar M (n - 2) : ℝ))⁻¹)
      (SigInvN2 := ((Annealed.sigmaBar M n : ℝ))⁻¹)
      (epsj := epsj) (Kg := Kg * stepFourGagliardoConst d s)
      (thetaK := (3 : ℝ) ^ (-(1 / 4 : ℝ) * (k : ℝ)))
      (mul_nonneg (triangleRemainderConst_nonneg d (schauderWindowConst_nonneg d) k)
        (Real.sqrt_nonneg _)) hs
      (mul_nonneg hC.le (Real.rpow_nonneg hs.le _))
      (mul_nonneg hC.le (Real.rpow_nonneg hs.le _))
      (mul_nonneg hC.le (Real.rpow_nonneg hs.le _))
      (Real.rpow_nonneg hs.le _) (affineExcess_nonneg _ _) hEfl heps0
      (mul_nonneg (zpow_nonneg (by norm_num) _) ENNReal.toReal_nonneg) hOsc hSig
      (mul_nonneg (Real.rpow_nonneg hs.le _)
        (inv_nonneg.mpr (Annealed.sigmaBar M n).2.le))
      ENNReal.toReal_nonneg (mul_nonneg hKg0 (stepFourGagliardoConst_nonneg d s)) hGsem
      (by
        have h := habsorb k hk
        linarith only [h])
      (by
        rw [edFinalEpsCoeff] at hgate2
        linarith only [hgate2]) hed
    rw [stepFourDeltaOut_interior_eq (M := M) hs k n] at hres
    rw [edFinalEpsCoeff]
    exact hres
  · exact Filter.Eventually.of_forall (fun _ h => absurd h hnm)


/-! ## 2. The Step-1 pin `s = 1/4`, and the identification of the two events -/

theorem stepOneS_mem_Icc {d : ℕ} {M : ABKModel d} (hgamma : M.gamma ≤ 1 / 256) :
    stepOneS ∈ Set.Icc (64 * M.gamma) 1 := by
  rw [stepOneS]
  exact ⟨by linarith only [hgamma], by norm_num⟩

theorem stepOneS_lt_half : stepOneS < 1 / 2 := by
  rw [stepOneS]; norm_num

/-! ## 3. `hstep4`, discharged -/

/-- **`hstep4` on the interior branch, discharged.**

For one `omega` and every scale `j ∈ [n+k, m-1]` outside the Step-3 bad set
`𝓑_z`, the Step-4 per-scale excess decay holds at the concrete windows `U_j =
stepThreeWindow z m j`, the Step-5 slot `ε_j` (times the collapse's
coefficient) and the `g`-leg `δ_j` — with NO harmonic-approximation hypothesis,
NO `∇h` leg, NO boundary indicator, and no conditional beyond the annular
producer's own premises and the explicit `δ`-gate.  This is the input of
`StepFiveIterationResult.iterationDecay_of_stepFourDecay`. -/
theorem stepFourDecay_interior_pinned (d : ℕ) [NeZero d] (hd : d ≠ 0) :
    ∃ C Cann : ℝ, 0 < C ∧ 0 < Cann ∧ ∃ k₀ : ℕ, 3 ≤ k₀ ∧
      ∀ k : ℕ, k₀ ≤ k →
        ∀ (M : ABKModel d) (m0 : ℤ) (Ecap : {E : ℝ // 1 ≤ E}),
          Algsuperdiff.Frozen.Section3.inductionState M m0 Ecap →
          M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
          M.gamma ≤ Cann⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
          M.gamma ≤ 1 / 256 →
          M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
              Real.rpow (stepOneS / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) *
                (C⁻¹ * stepOneS ^ (4 : ℕ)) →
          ∀ delta : ℝ, delta ∈ Set.Ioc (0 : ℝ) (1 / 2) →
            M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
                Real.rpow stepOneSEighth (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) *
                  stepOneEp delta →
            edFinalEpsCoeff d C k stepOneS * (Cann * stepOneEp delta) ≤
                (1 / 2 : ℝ) * (3 : ℝ) ^ (-(1 / 4 : ℝ) * (k : ℝ)) →
            ∀ L m : ℤ, m ≤ L → m ≤ m0 →
              ∀ z : Vec d, z ∈ openCubeSet (originCube d (m - 1)) →
                ∀ n : ℤ,
                  ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
                    ∀ (u hdat : H1Function (openCubeSet (originCube d m)))
                      (g : Vec d → Vec d) (Kg : ℝ), 0 ≤ Kg →
                      IsDirichletSolutionOn
                          (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                          (originCube d m) u hdat g →
                      MemLp g 2
                          (normalizedVolumeMeasureOn (openCubeSet (originCube d m))) →
                      MemLp (Gagliardo.gagliardoKernel stepOneS 2 g) 2
                          (normalizedGagliardoMeasureOn (openCubeSet (originCube d m))) →
                      MemLp (Gagliardo.gagliardoKernel stepOneS 2 hdat.grad) 2
                          (normalizedGagliardoMeasureOn (openCubeSet (originCube d m))) →
                      HolderSeminormBoundOn (openCubeSet (originCube d m))
                          (1 / 2) Kg g →
                      ∀ (c : ℤ → ℝ) (slope : ℤ → Vec d),
                        (∀ j : ℤ, j ≤ m →
                          IsAffineMinimizer (stepThreeWindow z m j) u.toFun (c j)
                            (slope j)) →
                        ∀ j : ℤ, n + (k : ℤ) ≤ j → j ≤ m - 1 →
                          j ∉ stepThreeBadSet M delta n m z omega →
                            affineExcess (stepThreeWindow z m (j - (k : ℤ))) u.toFun ≤
                              stepFiveTheta ^ k *
                                  affineExcess (stepThreeWindow z m j) u.toFun +
                                (edFinalEpsCoeff d C k stepOneS *
                                    stepFiveEps M j z delta omega) *
                                  slopeMagnitude (slope j) +
                                edFinalDelta M (edFinalDeltaConst d C k stepOneS)
                                  (Kg * stepFourGagliardoConst d stepOneS) j := by
  classical
  obtain ⟨C, hC, k₀, hk₀, hcomp⟩ := stepFourDecay_interior_of_anchors d hd
  obtain ⟨Cann, hCann, hepsbnd⟩ := ae_stepOneEpsJ_le d
  refine ⟨C, Cann, hC, hCann, k₀, hk₀, ?_⟩
  intro k hk M m0 Ecap hS hregime hregimeAnn hgamma hfund delta hdelta hsmall hgate L m
    hmL hmm0 z hzin n
  have hs : (0 : ℝ) < stepOneS := stepOneS_pos
  have hgamma4 : M.gamma ≤ 1 / 4 := by linarith only [hgamma]
  have hcapAll : ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ j : ℤ, stepOneEpsJ M j z delta omega ≤
        ENNReal.ofReal (Cann * stepOneEp delta) := by
    rw [ae_all_iff]
    intro j
    exact hepsbnd M hregimeAnn hgamma delta hdelta hsmall j z
  have hepNN : (0 : ℝ) ≤ Cann * stepOneEp delta :=
    mul_nonneg hCann.le
      (mul_nonneg stepOneSEighth_pos.le (Real.sqrt_nonneg _))
  filter_upwards [hcomp k hk M m0 Ecap hS hgamma4 stepOneS (stepOneS_mem_Icc hgamma)
      stepOneS_lt_half hregime hfund hs delta (by linarith only [hdelta.2]) L m hmL hmm0
      z hzin, hcapAll] with omega hcom hcap
  intro u hdat g Kg hKg0 hsol hgL2 hgW hhW hhol c slope hmin j hjn hjm hjB
  have hev : omega ∈ stepThreeGoodEvent M delta j z := by
    by_contra hc
    exact hjB ((mem_stepThreeBadSet_iff M delta n m z omega j).mpr
      ⟨⟨by omega, hjm⟩, hc⟩)
  have hEfl := fluxCorrectedErrorRepresentative_le_stepFiveEps
    (M := M) (j := j) (L := L) (z := z) (delta := delta) (omega := omega)
    (B := Cann * stepOneEp delta) (by omega) hev (hcap j)
  have hres := hcom j (by omega) hev u hdat g hsol hgL2 hgW hhW Kg
    (stepFiveEps M j z delta omega) hKg0
    (stepFiveEps_nonneg M j z delta omega) hhol hEfl
    (le_trans (mul_le_mul_of_nonneg_left (stepFiveEps_le_of_cap hepNN (hcap j))
      (edFinalEpsCoeff_nonneg d hC.le k hs.le)) hgate)
    (c j) (slope j) (hmin j (by omega))
  rw [stepFiveTheta_pow]
  exact hres

end

end Algsuperdiff.Section4.Provider.Regularity
