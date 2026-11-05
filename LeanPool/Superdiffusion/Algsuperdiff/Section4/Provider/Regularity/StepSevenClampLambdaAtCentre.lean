/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.ShellWindowEnergyCentre
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenAeMerge
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenClampCaps

/-!
# StepSevenClampLambdaAtCentre

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


namespace Algsuperdiff.Section4.Provider.Regularity

open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Observable
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

private theorem isotropicComparator_eq_scalarMatrix_diag (sigma : PositiveScalar) :
    isotropicComparatorMatrix (d := d) sigma = scalarMatrix (d := d) (sigma : ℝ) :=
  rfl

private theorem originCube_scale_gap_one_diag (n : ℤ) :
    ((originCube d (n + 3)).scale - (originCube d (n + 2)).scale).toNat = 1 := by
  have h : (originCube d (n + 3)).scale - (originCube d (n + 2)).scale = 1 := by
    simp only [originCube]
    ring
  rw [h]
  rfl

private theorem clamp_le_mul_inv_of_mul_le_diag {sigma x K : ℝ} (hsigma : 0 < sigma)
    (h : sigma * x ≤ K) : x ≤ K * sigma⁻¹ := by
  have hmul := mul_le_mul_of_nonneg_right h (inv_nonneg.mpr hsigma.le)
  rwa [mul_comm sigma, mul_assoc, mul_inv_cancel₀ hsigma.ne', mul_one] at hmul

/-! ## 1. The off-grid transport at the diagonal -/

/-- **The covering cube's coarse-graining error against the anchor's
representative, at the DIAGONAL.**
`BoundaryCoveringSlot.ae_coveringCubeError_le_representative` with the
anchor-geometry binder replaced by `z ∈ □_m`: the half-open containment is
`ShellWindowEnergyCentre.translateSet_cubeSet_coveringCube_subset_anchorParent_self`,
and everything else is the parent's script verbatim. -/
theorem ae_coveringCubeError_le_representative_atCentre [NeZero d] (M : ABKModel d)
    (L n m : ℤ) (z : Vec d) {s t : ℝ} (hs : 0 < s) (hst : s / 8 < t) (ht : t ≤ 1 / 2) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      n + 2 ≤ m → z ∈ openCubeSet (originCube d m) →
        Ch02.HomogenizationErrorOnCube (originCube d (n + 2)) t .infinity (.finite 2)
            (parentRebasedFamily M L (n + 3) (wellPlacedCentre z m (n + 2)) z omega)
            (isotropicComparatorMatrix (Annealed.sigmaBar M (n + 3))) ≤
          Real.sqrt (offGridStabilityConst d t (s / 8)) *
            ((3 : ℝ) ^ (s / 8) *
              fluxCorrectedErrorRepresentative M L (n + 3)
                ⟨s / 8, by linarith only [hs]⟩
                (Cutoff.translateCutoffSample z omega)) := by
  have hbase := (GoodEvents.measurePreserving_translateCutoffSample M
      z).quasiMeasurePreserving.ae
    (ae_offGridErrorFunctional_le_fluxCorrectedErrorFunctionalAtRoot
      M L (n + 3) (originCube d (n + 3))
      (isotropicComparatorMatrix (Annealed.sigmaBar M (n + 3)))
      (by linarith only [hs] : (0 : ℝ) < s / 8) hst ht)
  filter_upwards [hbase] with omega hall
  intro hnm hz
  have hstep := hall (wellPlacedCentre z m (n + 2) - z) (originCube d (n + 2))
    (originCube d (n + 3))
    (translateSet_cubeSet_coveringCube_subset_anchorParent_self hnm hz)
  rw [originCube_scale_gap_one_diag (d := d) n,
    fluxCorrectedErrorFunctionalAtRoot_eq_representative M L (n + 3)
      ⟨s / 8, by linarith only [hs]⟩] at hstep
  have hexp : (s / 8 * ((1 : ℕ) : ℝ)) = s / 8 := by
    push_cast
    ring
  rw [hexp] at hstep
  rwa [homogenizationErrorOnCube_parentRebasedFamily_eq_offGrid M L (n + 3) (n + 2)
    (wellPlacedCentre z m (n + 2)) z omega (by linarith only [hs, hst] : (0 : ℝ) < t)
    (isotropicComparatorMatrix (Annealed.sigmaBar M (n + 3)))]

/-! ## 2. The `hlambda` slot at the diagonal -/

/-- **The seventh coarse slot, produced at the diagonal.**

Almost surely, on the §4.4 good event `𝒢(n+3, z; s/8, (s/8)δ^{1/2})` centre `z
∈ □_m` — interior, boundary or flush — the Step-7 chain's `hlambda` quantity
`λ_{1/8,2}^{-1}` of the `(n+3)`-re-based family on the covering cube `□_{n+2}`
at the clamped centre `wellPlacedCentre z m (n+2)` is capped by one `d`-only
constant against `σ_{n+3}^{-1}`.  This is the print's
`e.lambda.stability.applied` at the covering cube's own scale, in the
presentation the well-placed Step-7 chain reads. -/
theorem ae_stepSevenClampLambdaSlot_atCentre (d : ℕ) [NeZero d] :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ M : ABKModel d, M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        ∀ delta : ℝ, delta ∈ Set.Ioc (0 : ℝ) (1 / 2) →
          8 * M.gamma ≤ stepOneSEighth →
          M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
              Real.rpow stepOneSEighth (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) *
                stepOneEp delta →
            ∀ L m n : ℤ, ∀ z : Vec d,
              ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
                omega ∈ stepThreeGoodEvent M delta (n + 3) z →
                  n + 2 ≤ m → n + 3 ≤ L → z ∈ openCubeSet (originCube d m) →
                    stepSevenCgLamInv (originCube d (n + 2))
                        (parentRebasedFamily M L (n + 3)
                          (wellPlacedCentre z m (n + 2)) z omega) stepSevenCgS ≤
                      K * ((Annealed.sigmaBar M (n + 3) : ℝ))⁻¹ := by
  obtain ⟨C, hCpos, hC⟩ := ae_errorRepresentative_le_of_mem_goodEventAt d
  have hd : (0 : ℝ) < (d : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  set kappa : ℝ := Real.sqrt (96 * (d : ℝ)) * 3 with hkappadef
  refine ⟨C, 2 * (d : ℝ) * ((kappa * (C * (1 / 2))) ^ 2 + 1), hCpos, ?_, ?_⟩
  · have h1 : (0 : ℝ) < (kappa * (C * (1 / 2))) ^ 2 + 1 := by positivity
    have h2 : (0 : ℝ) < 2 * (d : ℝ) := by linarith only [hd]
    exact mul_pos h2 h1
  intro M hregime delta hdelta hfloor hsmall L m n z
  have hsig : (0 : ℝ) < (Annealed.sigmaBar M (n + 3) : ℝ) :=
    (Annealed.sigmaBar M (n + 3)).2
  have hslot :
      ((⟨stepOneSEighth, stepOneSEighth_pos⟩ : {t : ℝ // 0 < t}) : ℝ) ∈
        Set.Icc (8 * M.gamma) (1 / 4 : ℝ) := by
    refine ⟨hfloor, ?_⟩
    change stepOneSEighth ≤ (1 : ℝ) / 4
    rw [stepOneSEighth_eq]; norm_num
  have hepHalf : stepOneEp delta ≤ 1 / 2 := (stepOneEp_mem_Ioc hdelta).2
  filter_upwards [hC M hregime ⟨stepOneSEighth, stepOneSEighth_pos⟩ hslot
      (stepOneEp delta) (stepOneEp_mem_Ioc hdelta) hsmall (n + 3) z,
    ae_coveringCubeError_le_representative_atCentre (s := stepOneS)
      (t := stepSevenCaccS / 2) M L n m z stepOneS_pos
      (by rw [stepOneS_div_eight_eq, stepSevenCaccS_half_eq]; norm_num)
      (by rw [stepSevenCaccS_half_eq]; norm_num)]
    with omega hcap herr
  intro hmem hnm hnL hz
  -- the representative at the good-event slot, capped by the event
  have hErep0 : (0 : ℝ) ≤ fluxCorrectedErrorRepresentative M L (n + 3)
      ⟨stepOneS / 8, by rw [stepOneS_div_eight_eq]; norm_num⟩
      (Cutoff.translateCutoffSample z omega) :=
    fluxCorrectedErrorRepresentative_nonneg _ _ _ _ _
  have hErepCap : fluxCorrectedErrorRepresentative M L (n + 3)
      ⟨stepOneS / 8, by rw [stepOneS_div_eight_eq]; norm_num⟩
      (Cutoff.translateCutoffSample z omega) ≤ C * (1 / 2) := by
    have hraw := hcap hmem L hnL
    have hstep : C * stepOneEp delta ≤ C * (1 / 2) :=
      mul_le_mul_of_nonneg_left hepHalf hCpos.le
    exact le_trans hraw hstep
  have h3s8 : ((3 : ℝ) ^ (stepOneS / 8)) ≤ 3 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
      (by rw [stepOneS_div_eight_eq]; norm_num : stepOneS / 8 ≤ (1 : ℝ))
    rwa [Real.rpow_one] at h
  have h3nn : (0 : ℝ) ≤ (3 : ℝ) ^ (stepOneS / 8) *
      fluxCorrectedErrorRepresentative M L (n + 3)
        ⟨stepOneS / 8, by rw [stepOneS_div_eight_eq]; norm_num⟩
        (Cutoff.translateCutoffSample z omega) :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) hErep0
  have h3 : (3 : ℝ) ^ (stepOneS / 8) *
      fluxCorrectedErrorRepresentative M L (n + 3)
        ⟨stepOneS / 8, by rw [stepOneS_div_eight_eq]; norm_num⟩
        (Cutoff.translateCutoffSample z omega) ≤ 3 * (C * (1 / 2)) := by
    have hstepa := mul_le_mul_of_nonneg_right h3s8 hErep0
    have hstepb : (3 : ℝ) * fluxCorrectedErrorRepresentative M L (n + 3)
        ⟨stepOneS / 8, by rw [stepOneS_div_eight_eq]; norm_num⟩
        (Cutoff.translateCutoffSample z omega) ≤ 3 * (C * (1 / 2)) := by
      linarith only [hErepCap]
    linarith only [hstepa, hstepb]
  -- the coarse-graining error at the upper ratio index `1/8`
  have hEUp : Ch02.HomogenizationErrorOnCube (originCube d (n + 2))
      (stepSevenCaccS / 2) .infinity (.finite 2)
      (parentRebasedFamily M L (n + 3) (wellPlacedCentre z m (n + 2)) z omega)
      (isotropicComparatorMatrix (Annealed.sigmaBar M (n + 3))) ≤
      kappa * (C * (1 / 2)) := by
    refine (herr hnm hz).trans ?_
    have h1 : Real.sqrt (offGridStabilityConst d (stepSevenCaccS / 2) (stepOneS / 8)) ≤
        Real.sqrt (96 * (d : ℝ)) := by
      refine Real.sqrt_le_sqrt ?_
      rw [stepSevenCaccS_half_eq, stepOneS_div_eight_eq]
      exact offGridStabilityConst_stepSevenUpper_le d
    calc Real.sqrt (offGridStabilityConst d (stepSevenCaccS / 2) (stepOneS / 8)) *
          ((3 : ℝ) ^ (stepOneS / 8) *
            fluxCorrectedErrorRepresentative M L (n + 3)
              ⟨stepOneS / 8, by rw [stepOneS_div_eight_eq]; norm_num⟩
              (Cutoff.translateCutoffSample z omega))
        ≤ Real.sqrt (96 * (d : ℝ)) * (3 * (C * (1 / 2))) :=
          mul_le_mul h1 h3 h3nn (Real.sqrt_nonneg _)
      _ = kappa * (C * (1 / 2)) := by rw [hkappadef]; ring
  -- the `q = 2` ratio pair at `1/8`, and row 1
  have hUpPos : (0 : ℝ) < stepSevenCaccS / 2 := by
    rw [stepSevenCaccS_half_eq]; norm_num
  have hEUpnn : 0 ≤ Ch02.HomogenizationErrorOnCube (originCube d (n + 2))
      (stepSevenCaccS / 2) .infinity (.finite 2)
      (parentRebasedFamily M L (n + 3) (wellPlacedCentre z m (n + 2)) z omega)
      (isotropicComparatorMatrix (Annealed.sigmaBar M (n + 3))) :=
    homogenizationErrorOnCube_infinity_two_nonneg (originCube d (n + 2))
      (parentRebasedFamily M L (n + 3) (wellPlacedCentre z m (n + 2)) z omega)
      (isotropicComparatorMatrix (Annealed.sigmaBar M (n + 3))) hUpPos
  have hratioUp := max_ellipticityRatio_le_homogenizationError (d := d)
    (originCube d (n + 2))
    (parentRebasedFamily M L (n + 3) (wellPlacedCentre z m (n + 2)) z omega) hUpPos hsig
  rw [← isotropicComparator_eq_scalarMatrix_diag] at hratioUp
  have hmaxUp := hratioUp.trans (two_mul_dim_mul_sq_add_one_le_of_le hEUpnn hEUp)
  have hLo8 := le_trans (le_max_right _ _) hmaxUp
  rw [stepSevenCgLamInv_eq_inv, stepSevenCgS_half_eq]
  refine clamp_le_mul_inv_of_mul_le_diag hsig ?_
  rw [← stepSevenCaccS_half_eq]
  exact hLo8

/-! ## 3. The countable merge -/

/-- **The seventh slot, merged: one null set for every scale, every printed lattice
centre, every truncation and every ambient scale.**  `Mathlib`'s `ae_all_iff`
through `StepSevenAeMerge`, over the countable index `ℤ × ℤ × (Fin d → ℤ) × ℤ
× ℤ`.  The event scale `j` reads the per-instance statement at `n:= j - 3`. -/
theorem ae_stepSevenClampLambdaSlot_merged (d : ℕ) [NeZero d] :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ M : ABKModel d, M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        ∀ delta : ℝ, delta ∈ Set.Ioc (0 : ℝ) (1 / 2) →
          8 * M.gamma ≤ stepOneSEighth →
          M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
              Real.rpow stepOneSEighth (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) *
                stepOneEp delta →
            ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
              ∀ (j nl : ℤ) (v : Fin d → ℤ),
                omega ∈ stepThreeGoodEvent M delta j
                    (Support.triadicLatticePoint nl v) →
                  ∀ L m : ℤ, j ≤ L → j - 1 ≤ m →
                    Support.triadicLatticePoint nl v ∈
                        openCubeSet (originCube d m) →
                      stepSevenCgLamInv (originCube d (j - 1))
                          (parentRebasedFamily M L j
                            (wellPlacedCentre (Support.triadicLatticePoint nl v)
                              m (j - 1))
                            (Support.triadicLatticePoint nl v) omega)
                          stepSevenCgS ≤
                        K * ((Annealed.sigmaBar M j : ℝ))⁻¹ := by
  obtain ⟨C, K, hCpos, hKpos, hper⟩ := ae_stepSevenClampLambdaSlot_atCentre d
  refine ⟨C, K, hCpos, hKpos, ?_⟩
  intro M hregime delta hdelta hfloor hsmall
  have hpair : ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ p : ℤ × ℤ × (Fin d → ℤ) × ℤ × ℤ, True →
        (omega ∈ stepThreeGoodEvent M delta p.1
            (Support.triadicLatticePoint p.2.1 p.2.2.1) →
          p.1 - 1 ≤ p.2.2.2.2 → p.1 ≤ p.2.2.2.1 →
            Support.triadicLatticePoint p.2.1 p.2.2.1 ∈
                openCubeSet (originCube d p.2.2.2.2) →
              stepSevenCgLamInv (originCube d (p.1 - 1))
                  (parentRebasedFamily M p.2.2.2.1 p.1
                    (wellPlacedCentre (Support.triadicLatticePoint p.2.1 p.2.2.1)
                      p.2.2.2.2 (p.1 - 1))
                    (Support.triadicLatticePoint p.2.1 p.2.2.1) omega)
                  stepSevenCgS ≤
                K * ((Annealed.sigmaBar M p.1 : ℝ))⁻¹) := by
    refine ae_forall_of_forall_ae_of_countable
      (Q := fun _ : ℤ × ℤ × (Fin d → ℤ) × ℤ × ℤ => True) ?_
    rintro ⟨j, nl, v, L, m⟩ -
    have hbase := hper M hregime delta hdelta hfloor hsmall L m (j - 3)
      (Support.triadicLatticePoint nl v)
    have e3 : j - 3 + 3 = j := by ring
    have e2 : j - 3 + 2 = j - 1 := by ring
    rw [e3, e2] at hbase
    exact hbase.mono fun omega h hmem hm hL hz => h hmem hm hL hz
  exact hpair.mono fun omega h j nl v hmem L m hL hm hz =>
    h (j, nl, v, L, m) trivial hmem hm hL hz

end

end Algsuperdiff.Section4.Provider.Regularity
