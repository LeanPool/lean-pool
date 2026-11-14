/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepFourFinalIteration

/-!
# StepFourFinalBudget

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

/-- **`e.oscillation.iteration.result` with the `ε`-budget slot generic** ('s
mismatch (1), fixed's own price): the `ε`-sum is allowed the constant `2 C_ε`
and the produced iteration constant becomes `C_iter = 2 C₀ (k + 1 + C_ε)`.  At
`C_ε = 1` this is the pinned iteration result verbatim. -/
theorem oscillationIterationResult_of_stepFourDecay_generic (d : ℕ) (hd : d ≠ 0)
    (k : ℕ) (hk : 2 ≤ k) {Ceps : ℝ} (hCeps : 0 ≤ Ceps) :
    ∃ C Citer : ℝ, 0 < C ∧ 0 ≤ Citer ∧
      ∀ (Cedos Cann alpha : ℝ), alpha ≤ 1 →
        ∀ n m : ℤ, (1 : ℤ) ≤ m - n →
          ∀ U : ℤ → Set (Vec d), IterationWindowFamily U m →
            ∀ u : Vec d → ℝ, MemLp u 2 (volume.restrict (U m)) →
              ∀ (c : ℤ → ℝ) (g : ℤ → Vec d),
                (∀ j : ℤ, j ≤ m → IsAffineMinimizer (U j) u (c j) (g j)) →
                  ∀ Bz : Finset ℤ,
                    (Bz.card : ℝ) ≤
                        stepOneDelta (stepOneC1 d Cedos Cann Citer k) alpha *
                          (((m : ℝ) - (n : ℝ)) + 1) →
                      ∀ ε δ : ℤ → ℝ,
                        (∀ j : ℤ, n ≤ j → j ≤ m → 0 ≤ ε j) →
                        (∀ j : ℤ, n ≤ j → j ≤ m → 0 ≤ δ j) →
                        (∑ j ∈ Finset.Icc n m, ε j ≤
                          2 * Ceps *
                            stepOneDelta (stepOneC1 d Cedos Cann Citer k) alpha *
                            ((m : ℝ) - (n : ℝ))) →
                        ∀ dataG dataH : ℝ, 0 ≤ dataG → 0 ≤ dataH →
                          (∑ j ∈ Finset.Icc n m, δ j ≤ dataG + dataH) →
                          (∀ j : ℤ, n + (k : ℤ) ≤ j → j ≤ m - 1 → j ∉ Bz →
                            affineExcess (U (j - (k : ℤ))) u ≤
                              stepFiveTheta ^ k * affineExcess (U j) u +
                                ε j * slopeMagnitude (g j) + δ j) →
                          ∀ n' m' : ℤ, n ≤ n' → n' ≤ m' → m' ≤ m →
                            (3 : ℝ) ^ (-n') *
                                normalizedL2On (U n')
                                  (fun x => u x - volumeAverage (U n') u) ≤
                              C *
                                  Real.exp
                                    ((stepOneC1 d Cedos Cann Citer k)⁻¹ * Citer *
                                      stepSixExponent alpha n m) *
                                  ((3 : ℝ) ^ (-m') *
                                      normalizedL2On (U m')
                                        (fun x => u x - volumeAverage (U m') u) +
                                    C * dataG) +
                                C *
                                  Real.exp
                                    ((stepOneC1 d Cedos Cann Citer k)⁻¹ * Citer *
                                      stepSixExponent alpha n m) * dataH := by
  obtain ⟨C0, hC0, hsub⟩ := exists_oscillation_subwindow_of_iterationLemma d hd
  have hkR : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  refine ⟨max 1 (Real.exp (C0 * ((k : ℝ) + 1) * ((k : ℝ) + 2))),
    2 * C0 * ((k : ℝ) + 1 + Ceps),
    lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    mul_nonneg (mul_nonneg (by norm_num) hC0.le)
      (by linarith only [hkR, hCeps]), ?_⟩
  intro Cedos Cann alpha halpha n m hwin U hU u hu c g hmin Bz hBz ε δ hε hδ hSe
    dataG dataH hdataG hdataH hSd hstep4 n' m' hn' hn'm' hm'm
  have hnm : n ≤ m := by omega
  have hmnR : (1 : ℝ) ≤ (m : ℝ) - (n : ℝ) := by
    have hcast : ((1 : ℤ) : ℝ) ≤ ((m - n : ℤ) : ℝ) := Int.cast_le.mpr hwin
    push_cast at hcast
    linarith only [hcast]
  have hC1pos : 0 < stepOneC1 d Cedos Cann (2 * C0 * ((k : ℝ) + 1 + Ceps)) k :=
    stepOneC1_pos d Cedos Cann (2 * C0 * ((k : ℝ) + 1 + Ceps)) k
  have hdpar : 0 ≤
      stepOneDelta (stepOneC1 d Cedos Cann (2 * C0 * ((k : ℝ) + 1 + Ceps)) k) alpha := by
    simp only [stepOneDelta]
    exact mul_nonneg (inv_nonneg.mpr hC1pos.le) (by linarith only [halpha])
  -- the Step-6 exponent slot, and the abbreviation `X` for `δ (m-n)`
  have hXnn : 0 ≤ stepOneDelta (stepOneC1 d Cedos Cann (2 * C0 * ((k : ℝ) + 1 + Ceps)) k) alpha *
      ((m : ℝ) - (n : ℝ)) := mul_nonneg hdpar (by linarith only [hmnR])
  have hcardR : (((stepFiveBadSet Bz n m k).card : ℝ)) ≤ (Bz.card : ℝ) + (k : ℝ) + 1 := by
    have h := stepFiveBadSet_card_le Bz n m k
    exact_mod_cast h
  have hgrow : stepOneDelta (stepOneC1 d Cedos Cann (2 * C0 * ((k : ℝ) + 1 + Ceps)) k) alpha *
      (((m : ℝ) - (n : ℝ)) + 1) ≤
      2 * (stepOneDelta (stepOneC1 d Cedos Cann (2 * C0 * ((k : ℝ) + 1 + Ceps)) k) alpha *
        ((m : ℝ) - (n : ℝ))) := by
    have h := mul_le_mul_of_nonneg_left
      (show ((m : ℝ) - (n : ℝ)) + 1 ≤ 2 * ((m : ℝ) - (n : ℝ)) by linarith only [hmnR]) hdpar
    linarith only [h]
  have hBc : (((stepFiveBadSet Bz n m k).card : ℝ)) + 1 ≤
      ((k : ℝ) + 2) +
        2 * (stepOneDelta (stepOneC1 d Cedos Cann (2 * C0 * ((k : ℝ) + 1 + Ceps)) k) alpha *
          ((m : ℝ) - (n : ℝ))) := by
    linarith only [hcardR, hBz, hgrow]
  have hSeX : (∑ j ∈ Finset.Icc n m, ε j) ≤
      2 * Ceps *
        (stepOneDelta (stepOneC1 d Cedos Cann (2 * C0 * ((k : ℝ) + 1 + Ceps)) k) alpha *
          ((m : ℝ) - (n : ℝ))) := by
    have hid : 2 * Ceps *
        stepOneDelta (stepOneC1 d Cedos Cann (2 * C0 * ((k : ℝ) + 1 + Ceps)) k) alpha *
        ((m : ℝ) - (n : ℝ)) =
        2 * Ceps *
          (stepOneDelta (stepOneC1 d Cedos Cann (2 * C0 * ((k : ℝ) + 1 + Ceps)) k) alpha *
            ((m : ℝ) - (n : ℝ))) := by ring
    linarith only [hSe, hid]
  -- the sub-window run of the anchor, at the enlarged bad set
  have hrun := hsub k stepFiveTheta stepFiveTheta_mem (stepFiveTheta_pow_mem hk) n m hnm U hU
    u hu (stepFiveBadSet Bz n m k) (stepFiveBadSet_subset Bz n m k) ε δ hε hδ c g hmin
    (iterationDecay_of_stepFourDecay hstep4) n' m' hn' hn'm' hm'm
  -- the prefactor conversion
  have hpre0 := exp_budget_le_mul_exp (C0 := C0) (hR := (k : ℝ))
    (Bc := ((stepFiveBadSet Bz n m k).card : ℝ))
    (Se := ∑ j ∈ Finset.Icc n m, ε j) (K1 := (k : ℝ) + 2) (K2 := 2) (K3 := 2 * Ceps)
    (X := stepOneDelta (stepOneC1 d Cedos Cann (2 * C0 * ((k : ℝ) + 1 + Ceps)) k) alpha *
      ((m : ℝ) - (n : ℝ))) hC0.le hkR hBc hSeX
  have hQeq : (C0 * ((k : ℝ) + 1) * 2 + C0 * (2 * Ceps)) *
      (stepOneDelta (stepOneC1 d Cedos Cann (2 * C0 * ((k : ℝ) + 1 + Ceps)) k) alpha *
        ((m : ℝ) - (n : ℝ)))
      = (stepOneC1 d Cedos Cann (2 * C0 * ((k : ℝ) + 1 + Ceps)) k)⁻¹ *
          (2 * C0 * ((k : ℝ) + 1 + Ceps)) * stepSixExponent alpha n m := by
    simp only [stepOneDelta, stepSixExponent]
    ring
  rw [hQeq] at hpre0
  refine oscillation_shape_aux (Cg := 1) (Ch := 1)
    (Cpre := Real.exp (C0 * ((k : ℝ) + 1) * ((k : ℝ) + 2)))
    (Real.exp_pos _).le (Real.exp_pos _).le
    (mul_nonneg (zpow_nonneg (by norm_num) _) (normalizedL2On_nonneg _ _))
    hdataG hdataH zero_le_one zero_le_one (by linarith only [hSd]) hpre0
    (le_max_right _ _) ?_ ?_ hrun
  · have h1 : (1 : ℝ) ≤ max 1 (Real.exp (C0 * ((k : ℝ) + 1) * ((k : ℝ) + 2))) :=
      le_max_left _ _
    have h2 : Real.exp (C0 * ((k : ℝ) + 1) * ((k : ℝ) + 2)) ≤
        max 1 (Real.exp (C0 * ((k : ℝ) + 1) * ((k : ℝ) + 2))) := le_max_right _ _
    have h3 := mul_le_mul_of_nonneg_left h1
      (show (0 : ℝ) ≤ max 1 (Real.exp (C0 * ((k : ℝ) + 1) * ((k : ℝ) + 2))) by
        linarith only [h1])
    linarith only [h2, h3]
  · have h2 : Real.exp (C0 * ((k : ℝ) + 1) * ((k : ℝ) + 2)) ≤
        max 1 (Real.exp (C0 * ((k : ℝ) + 1) * ((k : ℝ) + 2))) := le_max_right _ _
    linarith only [h2]


/-! ## 2. The `δ`-budget of the interior family -/

theorem edFinalDeltaConst_nonneg (d : ℕ) [NeZero d] {C : ℝ} (hC : 0 ≤ C) (k : ℕ)
    {s : ℝ} (hs : 0 ≤ s) : 0 ≤ edFinalDeltaConst d C k s := by
  rw [edFinalDeltaConst]
  exact mul_nonneg (by norm_num)
    (mul_nonneg (mul_nonneg
      (triangleRemainderConst_nonneg d (schauderWindowConst_nonneg d) k)
      (Real.sqrt_nonneg _)) (mul_nonneg hC (Real.rpow_nonneg hs _)))

/-- The top-scale constant of the interior `δ`-budget, `4 C_δ 3^{m/2} σ_m^{-1}
K_g`. -/
def edFinalKgTop {d : ℕ} (M : ABKModel d) (Cdel Kg : ℝ) (m : ℤ) : ℝ :=
  4 * Cdel * ((3 : ℝ) ^ ((m : ℝ) / 2) * ((Annealed.sigmaBar M m : ℝ))⁻¹) * Kg

/-- **`dataG` for the interior branch**: `4 C_δ 3^{m/2} σ_m^{-1} K_g / (1 -
3^{-(1/2-γ)})`.  There is no `dataH` — the interior clause has no `∇h` leg. -/
def edFinalDataG {d : ℕ} (M : ABKModel d) (Cdel Kg : ℝ) (m : ℤ) : ℝ :=
  edFinalKgTop M Cdel Kg m / (1 - stepFiveRatioG M)

theorem edFinalDataG_nonneg {d : ℕ} {M : ABKModel d} (hgamma : M.gamma < 1 / 2)
    {Cdel Kg : ℝ} (hC : 0 ≤ Cdel) (hK : 0 ≤ Kg) (m : ℤ) :
    0 ≤ edFinalDataG M Cdel Kg m := by
  have h1 : (0 : ℝ) < 1 - stepFiveRatioG M := by
    linarith only [stepFiveRatioG_lt_one hgamma]
  have h2 : (0 : ℝ) ≤ edFinalKgTop M Cdel Kg m := by
    rw [edFinalKgTop]
    exact mul_nonneg (mul_nonneg (by linarith only [hC])
      (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (inv_nonneg.mpr (Annealed.sigmaBar M m).2.le))) hK
  exact div_nonneg h2 h1.le

theorem edFinalDelta_le_zpow {d : ℕ} {M : ABKModel d} {m0 : ℤ}
    {Ecap : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 Ecap) {Cdel Kg : ℝ}
    (hC : 0 ≤ Cdel) (hK : 0 ≤ Kg) {j m : ℤ} (hjm : j ≤ m) (hm : m ≤ m0) :
    edFinalDelta M Cdel Kg j ≤
      edFinalKgTop M Cdel Kg m * stepFiveRatioG M ^ (m - j) := by
  have hcomp := three_rpow_half_mul_inv_sigmaBar_le_of_inductionState hS hjm hm
  have hfac : (0 : ℝ) ≤ Cdel * Kg := mul_nonneg hC hK
  have h := mul_le_mul_of_nonneg_left hcomp hfac
  have hL : Cdel * Kg * ((3 : ℝ) ^ ((j : ℝ) / 2) * ((Annealed.sigmaBar M j : ℝ))⁻¹)
      = edFinalDelta M Cdel Kg j := by
    rw [edFinalDelta]; ring
  have hR : Cdel * Kg * (4 * ((3 : ℝ) ^ (-(1 / 2 - M.gamma))) ^ (m - j) *
        ((3 : ℝ) ^ ((m : ℝ) / 2) * ((Annealed.sigmaBar M m : ℝ))⁻¹))
      = edFinalKgTop M Cdel Kg m * stepFiveRatioG M ^ (m - j) := by
    rw [edFinalKgTop, stepFiveRatioG]; ring
  rw [← hL, ← hR]
  exact h

/-- **`e.sum.delta.j.bound` for the interior family**, on the anchor's own window
`[n,m]`. -/
theorem sum_Icc_top_edFinalDelta_le {d : ℕ} {M : ABKModel d} {m0 : ℤ}
    {Ecap : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 Ecap)
    (hgamma : M.gamma < 1 / 2) {Cdel Kg : ℝ} (hC : 0 ≤ Cdel) (hK : 0 ≤ Kg)
    {n m : ℤ} (hnm : n ≤ m) (hm : m ≤ m0) :
    ∑ j ∈ Finset.Icc n m, edFinalDelta M Cdel Kg j ≤ edFinalDataG M Cdel Kg m := by
  rw [edFinalDataG]
  exact sum_Icc_top_le_of_zpow_dominated (stepFiveRatioG_pos M)
    (stepFiveRatioG_lt_one hgamma) hnm (edFinalDelta_nonneg hC hK m)
    (fun j hj => edFinalDelta_le_zpow hS hC hK hj hm)

/-! ## 3. The `ε`-budget at the produced coefficient -/

/-- **`e.sum.eps.j.bound` at the collapse's own coefficient**: `∑ C_ε ε_j ≤ 2 C_ε δ
(m-n)`, the slot of the generic re-run. -/
theorem sum_Icc_edFinalEps_le {d : ℕ} {M : ABKModel d} {delta Ceps : ℝ} {n m : ℤ}
    {omega : Cutoff.CutoffSample d} (hCeps : 0 ≤ Ceps) (hdelta : 0 ≤ delta)
    (hwin : (14 : ℤ) ≤ m - n)
    (hgood : GoodScaleWindows M stepOneSEighth delta stepOneSEighth_pos n m omega)
    {v : Fin d → ℤ} (hv : v ∈ Support.latticeCubeSet d n m) :
    ∑ j ∈ Finset.Icc n m,
        Ceps * stepFiveEps M j (Support.triadicLatticePoint n v) delta omega ≤
      2 * Ceps * delta * ((m : ℝ) - (n : ℝ)) := by
  have hbase := sum_stepFiveEps_le_two_mul_delta_mul_window hdelta hwin hgood hv
  have hmul := mul_le_mul_of_nonneg_left hbase hCeps
  rw [← Finset.mul_sum]
  have hid : Ceps * (2 * delta * ((m : ℝ) - (n : ℝ)))
      = 2 * Ceps * delta * ((m : ℝ) - (n : ℝ)) := by ring
  linarith only [hmul, hid]

end

end Algsuperdiff.Section4.Provider.Regularity
