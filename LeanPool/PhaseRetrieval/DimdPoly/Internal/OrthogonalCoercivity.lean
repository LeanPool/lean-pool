/-
Copyright (c) 2026 Susanna Bertolini, Jaume de Dios Pont. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Susanna Bertolini, Jaume de Dios Pont
-/
module

public import LeanPool.PhaseRetrieval.DimdPoly.Internal.Definitions
import LeanPool.PhaseRetrieval.DimdPoly.Internal.CoefficientLimitRigidity
import LeanPool.PhaseRetrieval.DimdPoly.Internal.FiniteBaseAnnulusEstimate
import LeanPool.PhaseRetrieval.DimdPoly.Internal.Hermite1Dimd.ImportedAnalyticInputs
import LeanPool.PhaseRetrieval.DimdPoly.Internal.Hermitek.TrueLevelBasis
import LeanPool.PhaseRetrieval.DimdPoly.Internal.ProductAnnulusLocalization
import LeanPool.PhaseRetrieval.DimdPoly.Internal.TensorBasis
import Mathlib.Tactic.NormNum.Parity

/-! # OrthogonalCoercivity -/

@[expose] public section


open MeasureTheory Complex
open scoped BigOperators

noncomputable section

namespace DimdPolyLEAN

/-!
# OrthogonalCoercivity

Terminal finite assembly scaffold. This file should expose one coercivity
theorem and no new analytic content.
-/

section

variable {d : Nat} (kappa : MultiIndex d)

local notation "Pk" => Pkappa d kappa

/-- `coeffPk`: coeff Pk. -/
def coeffPk (H : Pk) (alpha : Idx d) : ℂ := coeffPkappa H alpha

/-- `OrthogonalToPk`: Orthogonal To Pk. -/
def OrthogonalToPk (F G : Pk) : Prop := orthogonalToPk F G

/-- `defectPk`: defect Pk. -/
def defectPk (F G : Pk) : ℝ := defect F G

/-- `lowAnnulusMassPk`: low Annulus Mass Pk. -/
def lowAnnulusMassPk (J : Nat) (H : Pk) : ℝ := lowAnnulusMass J (ofPkappa kappa H)

/-- `highAnnulusMassPk`: high Annulus Mass Pk. -/
def highAnnulusMassPk (J : Nat) (H : Pk) : ℝ := highAnnulusMass J (ofPkappa kappa H)

private theorem defect_nonneg_wip
    (hd : 0 < d) {kappa : MultiIndex d}
    (F G : Pkappa d kappa) :
    0 ≤ defect F G := by
  let _ := hd
  exact Real.sqrt_nonneg _

private theorem norm_zero_pkappa_wip
    (hd : 0 < d) {kappa : MultiIndex d} :
    ‖(0 : Pkappa d kappa)‖ = 0 := by
  let _ := hd
  change
    Real.sqrt
      (Finset.sum (0 : Pkappa d kappa).support
        (fun alpha => ‖(0 : Pkappa d kappa) alpha‖ ^ 2)) = 0
  simp

private theorem norm_nonneg_pkappa_wip
    (hd : 0 < d) {kappa : MultiIndex d}
    (F : Pkappa d kappa) :
    0 ≤ ‖F‖ := by
  let _ := hd
  exact Real.sqrt_nonneg _

private theorem norm_ne_zero_of_ne_zero_pkappa_wip
    (hd : 0 < d) {kappa : MultiIndex d}
    {F : Pkappa d kappa} (hF : F ≠ 0) :
    ‖F‖ ≠ 0 := by
  let _ := hd
  intro hnorm
  apply hF
  ext alpha
  by_cases hmem : alpha ∈ F.support
  · have hcoeff_ne : F alpha ≠ 0 := Finsupp.mem_support_iff.mp hmem
    have hle :
        ‖F alpha‖ ^ 2 ≤ Finset.sum F.support (fun a : Idx d => ‖F a‖ ^ 2) := by
      exact
        (Finset.single_le_sum (f := fun a : Idx d => ‖F a‖ ^ 2) (s := F.support) (a := alpha)
          (fun a _ => by positivity) hmem)
    have hterm_pos : 0 < ‖F alpha‖ ^ 2 := pow_pos (norm_pos_iff.mpr hcoeff_ne) 2
    have hsum_pos : 0 < Finset.sum F.support (fun a : Idx d => ‖F a‖ ^ 2) :=
      lt_of_lt_of_le hterm_pos hle
    change Real.sqrt (Finset.sum F.support (fun a : Idx d => ‖F a‖ ^ 2)) = 0 at hnorm
    have hsqrt_pos :
        0 < Real.sqrt (Finset.sum F.support (fun a : Idx d => ‖F a‖ ^ 2) ) :=
      Real.sqrt_pos.mpr hsum_pos
    linarith only [hnorm, hsqrt_pos]
  · exact Finsupp.notMem_support_iff.mp hmem

private theorem norm_smul_pkappa_wip
    (hd : 0 < d) {kappa : MultiIndex d}
    (c : ℂ) (F : Pkappa d kappa) :
    ‖c • F‖ = ‖c‖ * ‖F‖ := by
  let _ := hd
  by_cases hc : c = 0
  · subst hc
    rw [zero_smul, norm_zero_pkappa_wip hd]
    simp
  · change
      Real.sqrt (Finset.sum (c • F).support (fun alpha => ‖(c • F) alpha‖ ^ 2)) =
        ‖c‖ * Real.sqrt (Finset.sum F.support (fun alpha => ‖F alpha‖ ^ 2))
    rw [Finsupp.support_smul_eq hc]
    have hsum :
        Finset.sum F.support (fun alpha => ‖(c • F) alpha‖ ^ 2) =
          ‖c‖ ^ 2 * Finset.sum F.support (fun alpha => ‖F alpha‖ ^ 2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro alpha halpha
      simp [Finsupp.smul_apply, mul_pow]
    simp_all

private theorem orthogonalToPk_smul_right_wip
    (hd : 0 < d) {kappa : MultiIndex d}
    (F G : Pkappa d kappa) (c : ℂ) :
    orthogonalToPk F G ->
      orthogonalToPk F (c • G) := by
  let _ := hd
  intro horth
  dsimp [orthogonalToPk, pkappaInner] at horth ⊢
  by_cases hc : c = 0
  · simp [hc]
  · simp only [Finsupp.sum, Finsupp.smul_apply] at horth ⊢
    rw [Finsupp.support_smul_eq hc]
    calc
      Finset.sum G.support (fun alpha => c * G alpha * star (F alpha))
          = c * Finset.sum G.support (fun alpha => G alpha * star (F alpha)) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro alpha halpha
            ring
      _ = 0 := by simp [horth]

private theorem norm_le_defect_add_two_wip
    (hd : 0 < d) (kappa : MultiIndex d)
    (F G : Pkappa d kappa) (hF_norm : ‖F‖ = 1) :
    ‖G‖ ≤ defect F G + 2 := by
  exact norm_le_defect_add_two_of_norm_one hd kappa F G hF_norm

theorem orthogonal_coercivity
    (hd : 0 < d) (F : Pk) (hF_ne : F ≠ 0) (hF_norm : ‖F‖ = 1) :
    ∃ C_F_perp : ℝ, 0 < C_F_perp ∧
      ∀ G : Pk, OrthogonalToPk kappa F G ->
        ‖G‖ <= C_F_perp * defectPk kappa F G := by
  let _ := hd
  obtain ⟨J, delta_high, hdelta_high_pos, hhigh⟩ :=
    highAnnulusControl hd kappa F hF_ne hF_norm
  obtain ⟨delta_low, hdelta_low_pos, hlow⟩ :=
    lowAnnulusDefectControl hd kappa F hF_ne hF_norm J
  let delta : ℝ := min delta_high delta_low
  let C_F_perp : ℝ := max 2 delta⁻¹
  have hdelta_pos : 0 < delta := by
    dsimp [delta]
    exact lt_min hdelta_high_pos hdelta_low_pos
  have hC_F_perp_pos : 0 < C_F_perp := by
    dsimp [C_F_perp]
    exact lt_of_lt_of_le zero_lt_two (le_max_left _ _)
  refine ⟨C_F_perp, hC_F_perp_pos, ?_⟩
  intro G horth
  by_cases hG : G = 0
  · rw [hG, norm_zero_pkappa_wip hd]
    exact mul_nonneg (le_of_lt hC_F_perp_pos) (defect_nonneg_wip hd F 0)
  · let t : ℝ := ‖G‖
    let H : Pk := (((t : ℂ)⁻¹) : ℂ) • G
    have ht_ne : t ≠ 0 := norm_ne_zero_of_ne_zero_pkappa_wip hd hG
    have ht_pos : 0 < t := lt_of_le_of_ne (norm_nonneg_pkappa_wip hd G) ht_ne.symm
    have hH_orth : OrthogonalToPk kappa F H := by
      simpa [OrthogonalToPk, H] using
        orthogonalToPk_smul_right_wip hd F G (((t : ℂ)⁻¹) : ℂ) horth
    have hH_norm : ‖H‖ = 1 := by
      dsimp [H, t]
      rw [norm_smul_pkappa_wip hd]
      have htinv : t⁻¹ * t = 1 := by field_simp [ht_ne]
      simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht_pos,
        abs_of_nonneg (inv_nonneg.mpr (le_of_lt ht_pos)), t] using htinv
    have hG_eq : G = t • H := by
      ext alpha
      change G alpha = ((t : ℂ) * (((t : ℂ)⁻¹) * G alpha))
      field_simp [ht_ne]
    have hlarge_bridge : t ≤ defectPk kappa F G + 2 := by
      simpa [t, defectPk] using norm_le_defect_add_two_wip hd kappa F G hF_norm
    by_cases hlt4 : t < 4
    · by_cases hsmall : defectPk kappa F G ≤ delta * t
      · have hdelta_le_high : delta ≤ delta_high := by
          dsimp [delta]
          exact min_le_left _ _
        have hdelta_le_low : delta ≤ delta_low := by
          dsimp [delta]
          exact min_le_right _ _
        have hdefect_high : defect F (t • H) ≤ delta_high * t := by
          have hstep : defectPk kappa F G ≤ delta_high * t := by
            refine le_trans hsmall ?_
            exact mul_le_mul_of_nonneg_right hdelta_le_high (le_of_lt ht_pos)
          simpa [defectPk, hG_eq] using hstep
        have hdefect_low : defect F (t • H) ≤ delta_low * t := by
          have hstep : defectPk kappa F G ≤ delta_low * t := by
            refine le_trans hsmall ?_
            exact mul_le_mul_of_nonneg_right hdelta_le_low (le_of_lt ht_pos)
          simpa [defectPk, hG_eq] using hstep
        have hhigh_mass : highAnnulusMass J (ofPkappa kappa H) ≤ 1 / 4 :=
          hhigh hH_orth hH_norm ht_pos (le_of_lt hlt4) hdefect_high
        have hlow_mass : lowAnnulusMass J (ofPkappa kappa H) ≤ 1 / 4 :=
          hlow hH_orth hH_norm ht_pos (le_of_lt hlt4) hhigh_mass hdefect_low
        have hpartition := annulusMassPartition hd kappa J H
        have hsum_le :
            lowAnnulusMass J (ofPkappa kappa H) + highAnnulusMass J (ofPkappa kappa H) ≤ 1 / 2 := by
          linarith only [hhigh_mass, hlow_mass]
        have hnorm_sq : ‖H‖ ^ 2 = 1 := by
          simp_all
        linarith only [hhigh_mass, hlow_mass, hpartition, hnorm_sq]
      · have hdelta_inv_le : delta⁻¹ ≤ C_F_perp := by
          dsimp [C_F_perp]
          exact le_max_right _ _
        have hstrict : delta * t < defectPk kappa F G := lt_of_not_ge hsmall
        have ht_le_delta : t ≤ delta⁻¹ * defectPk kappa F G := by
          have haux : t ≤ defectPk kappa F G / delta := by
            rw [le_div_iff₀ hdelta_pos]
            exact le_of_lt (by simpa [mul_comm] using hstrict)
          simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using haux
        calc
          ‖G‖ = t := rfl
          _ ≤ delta⁻¹ * defectPk kappa F G := ht_le_delta
          _ ≤ C_F_perp * defectPk kappa F G :=
            mul_le_mul_of_nonneg_right hdelta_inv_le (defect_nonneg_wip hd F G)
    · have hge4 : 4 ≤ t := le_of_not_gt hlt4
      have htwo_defect : t ≤ 2 * defectPk kappa F G := by
        linarith only [hlarge_bridge, hlt4, defect_nonneg_wip hd F G]
      have htwo_le_C : 2 ≤ C_F_perp := by
        dsimp [C_F_perp]
        exact le_max_left _ _
      calc
        ‖G‖ = t := rfl
        _ ≤ 2 * defectPk kappa F G := htwo_defect
        _ ≤ C_F_perp * defectPk kappa F G :=
          mul_le_mul_of_nonneg_right htwo_le_C (defect_nonneg_wip hd F G)

end

end DimdPolyLEAN
