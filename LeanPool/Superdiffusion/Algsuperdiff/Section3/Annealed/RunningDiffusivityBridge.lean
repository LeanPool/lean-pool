/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.Theorems.DilationLaw
public import LeanPool.HighContrastHomogenization.Support.Book.Ch05.Theorems.Section54.VarianceBoundGoodScale.NormalizedBlocks
public import LeanPool.HighContrastHomogenization.Support.Book.Ch05.Theorems.Section57.AnnealedLimit

/-!
# RunningDiffusivityBridge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# construction of the infinite-volume annealed diffusivity

CoarseGraining defines `barSigmaLimit` as the infimum of the scalarized
annealed upper coefficients.  Its Section 5.7 public positivity and primal/dual
identification lemmas are stated under the stronger
`GammaSigmaCoarseGrainedEllipticity` input.  This file records that
non-circular route for the Section 3 cutoff law.

The last theorem transports the resulting limit back across the triadic
normalization used to obtain CoarseGraining's unit-range structural law.  The
conclusion is stated for the honest full matrices, since the auxiliary
`BlockMat` record does not carry a topology.
-/

namespace Algsuperdiff.Section3.Annealed

open Filter HCPolySupport Set
open HCPolySupport.Book
open scoped Topology

noncomputable section

private theorem le_of_forall_le_one_add_mul
    {a b : ℝ} (hb : 0 ≤ b)
    (h : ∀ ε > 0, a ≤ (1 + ε) * b) :
    a ≤ b := by
  by_contra hle
  have hlt : b < a := lt_of_not_ge hle
  by_cases hb_zero : b = 0
  · have hbound := h 1 (by norm_num : (0 : ℝ) < 1)
    nlinarith [hb_zero]
  · have hb_pos : 0 < b := lt_of_le_of_ne' hb hb_zero
    let ε : ℝ := (a - b) / (2 * b)
    have hε_pos : 0 < ε := by
      dsimp [ε]
      exact div_pos (sub_pos.mpr hlt) (mul_pos (by norm_num) hb_pos)
    have hbound := h ε hε_pos
    have hmul_eq : (1 + ε) * b = (a + b) / 2 := by
      dsimp [ε]
      field_simp [hb_pos.ne']
      ring
    nlinarith [hbound, hmul_eq]

private theorem exponentialDecay_tendsto_zero {alpha : ℝ} (halpha : 0 < alpha) :
    Tendsto (fun n : ℕ => Real.rpow (3 : ℝ) (-alpha * (n : ℝ)))
      atTop (nhds (0 : ℝ)) := by
  have hlinear :
      Tendsto (fun n : ℕ => (-alpha) * (n : ℝ)) atTop atBot :=
    tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (by linarith)
  have hpow :
      Tendsto (fun x : ℝ => Real.rpow (3 : ℝ) x) atBot (nhds (0 : ℝ)) :=
    tendsto_rpow_atBot_of_base_gt_one (3 : ℝ) (by norm_num : (1 : ℝ) < 3)
  simpa [mul_comm] using! hpow.comp hlinear

private theorem barSigma_range_bddBelow_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : Ch05.QuantitativeCoarseGrainedEllipticity P) :
    BddBelow (range fun n : ℕ => hP.barSigmaAtScale hStruct (n : ℤ)) := by
  refine ⟨0, ?_⟩
  rintro x ⟨n, rfl⟩
  exact (Ch05.Section54.Pigeonhole.barSigmaAtScale_pos_of_P4
    hP hStruct hP4 n).le

private theorem barSigmaStar_range_bddAbove_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : Ch05.QuantitativeCoarseGrainedEllipticity P) :
    BddAbove (range fun n : ℕ => hP.barSigmaStarAtScale hStruct (n : ℤ)) := by
  refine ⟨hP.barSigmaAtScale hStruct (0 : ℤ), ?_⟩
  rintro x ⟨n, rfl⟩
  have hstar_le_at_n :
      hP.barSigmaStarAtScale hStruct (n : ℤ) ≤
        hP.barSigmaAtScale hStruct (n : ℤ) :=
    Ch05.Section54.VarianceBoundGoodScale.barSigmaStarAtScale_le_barSigmaAtScale_of_P4
      hP hStruct hP4 n
  have hb_n_le_b0 :
      hP.barSigmaAtScale hStruct (n : ℤ) ≤
        hP.barSigmaAtScale hStruct (0 : ℤ) :=
    (Ch05.Section54.Pigeonhole.scalarChain_of_P4 hP hStruct hP4
      (Nat.zero_le n)).2.2
  exact hstar_le_at_n.trans hb_n_le_b0

/-- Under `(P4)`, the scalarized upper annealed coefficients converge to
CoarseGraining's `barSigmaLimit`. -/
theorem barSigmaAtScale_tendsto_barSigmaLimit_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : Ch05.QuantitativeCoarseGrainedEllipticity P) :
    Tendsto (fun n : ℕ => hP.barSigmaAtScale hStruct (n : ℤ)) atTop
      (nhds (Ch05.Section57.barSigmaLimit hP hStruct)) := by
  simpa [Ch05.Section57.barSigmaLimit] using!
    tendsto_atTop_ciInf
      (fun _ _ hnm =>
        (Ch05.Section54.Pigeonhole.scalarChain_of_P4
          hP hStruct hP4 hnm).2.2)
      (barSigma_range_bddBelow_of_P4 hP hStruct hP4)

/-- Under `(P4)`, the scalarized starred annealed coefficients converge to
CoarseGraining's `barSigmaStarLimit`. -/
theorem barSigmaStarAtScale_tendsto_barSigmaStarLimit_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : Ch05.QuantitativeCoarseGrainedEllipticity P) :
    Tendsto (fun n : ℕ => hP.barSigmaStarAtScale hStruct (n : ℤ)) atTop
      (nhds (Ch05.Section57.barSigmaStarLimit hP hStruct)) := by
  simpa [Ch05.Section57.barSigmaStarLimit] using!
    tendsto_atTop_ciSup
      (fun _ _ hnm =>
        (Ch05.Section54.Pigeonhole.scalarChain_of_P4
          hP hStruct hP4 hnm).1)
      (barSigmaStar_range_bddAbove_of_P4 hP hStruct hP4)

private theorem barSigmaStarAtScale_le_barSigmaLimit_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : Ch05.QuantitativeCoarseGrainedEllipticity P) (n : ℕ) :
    hP.barSigmaStarAtScale hStruct (n : ℤ) ≤
      Ch05.Section57.barSigmaLimit hP hStruct := by
  refine le_csInf (range_nonempty _) ?_
  rintro y ⟨m, rfl⟩
  by_cases hnm : n ≤ m
  · have hstar_nm :
        hP.barSigmaStarAtScale hStruct (n : ℤ) ≤
          hP.barSigmaStarAtScale hStruct (m : ℤ) :=
      (Ch05.Section54.Pigeonhole.scalarChain_of_P4
        hP hStruct hP4 hnm).1
    have hstar_m_b_m :
        hP.barSigmaStarAtScale hStruct (m : ℤ) ≤
          hP.barSigmaAtScale hStruct (m : ℤ) :=
      Ch05.Section54.VarianceBoundGoodScale.barSigmaStarAtScale_le_barSigmaAtScale_of_P4
        hP hStruct hP4 m
    exact hstar_nm.trans hstar_m_b_m
  · have hmn : m ≤ n := by omega
    have hstar_n_b_n :
        hP.barSigmaStarAtScale hStruct (n : ℤ) ≤
          hP.barSigmaAtScale hStruct (n : ℤ) :=
      Ch05.Section54.VarianceBoundGoodScale.barSigmaStarAtScale_le_barSigmaAtScale_of_P4
        hP hStruct hP4 n
    have hb_n_m :
        hP.barSigmaAtScale hStruct (n : ℤ) ≤
          hP.barSigmaAtScale hStruct (m : ℤ) :=
      (Ch05.Section54.Pigeonhole.scalarChain_of_P4
        hP hStruct hP4 hmn).2.2
    exact hstar_n_b_n.trans hb_n_m

private theorem barSigmaStarLimit_le_barSigmaLimit_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : Ch05.QuantitativeCoarseGrainedEllipticity P) :
    Ch05.Section57.barSigmaStarLimit hP hStruct ≤
      Ch05.Section57.barSigmaLimit hP hStruct := by
  refine csSup_le (range_nonempty _) ?_
  rintro x ⟨n, rfl⟩
  exact barSigmaStarAtScale_le_barSigmaLimit_of_P4 hP hStruct hP4 n

private theorem barSigmaStarLimit_pos_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : Ch05.QuantitativeCoarseGrainedEllipticity P) :
    0 < Ch05.Section57.barSigmaStarLimit hP hStruct := by
  have h0_pos : 0 < hP.barSigmaStarAtScale hStruct (0 : ℤ) :=
    Ch05.Section54.Pigeonhole.barSigmaStarAtScale_pos_of_P4
      hP hStruct hP4 0
  exact lt_of_lt_of_le h0_pos <|
    le_csSup (barSigmaStar_range_bddAbove_of_P4 hP hStruct hP4) ⟨0, rfl⟩

/-- `(P4)` already makes CoarseGraining's limiting upper scalar strictly positive. -/
theorem barSigmaLimit_pos_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : Ch05.QuantitativeCoarseGrainedEllipticity P) :
    0 < Ch05.Section57.barSigmaLimit hP hStruct :=
  lt_of_lt_of_le (barSigmaStarLimit_pos_of_P4 hP hStruct hP4)
    (barSigmaStarLimit_le_barSigmaLimit_of_P4 hP hStruct hP4)

private theorem barSigmaLimit_le_one_add_mul_barSigmaStarLimit_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : Ch05.QuantitativeCoarseGrainedEllipticity P)
    {ε : ℝ} (hε : 0 < ε) :
    Ch05.Section57.barSigmaLimit hP hStruct ≤
      (1 + ε) * Ch05.Section57.barSigmaStarLimit hP hStruct := by
  obtain ⟨C, alpha, _hC_pos, halpha_pos, hconv⟩ :=
    Ch05.Section51.annealedConvergence_homogenizationScale hP4.params
  let N : ℕ := Ch05.annealedAlgebraicEntryScale P hP4 C
  have hsmall_event :
      ∀ᶠ n : ℕ in atTop,
        Real.rpow (3 : ℝ) (-alpha * (n : ℝ)) < ε :=
    (exponentialDecay_tendsto_zero halpha_pos) (Iio_mem_nhds hε)
  rcases eventually_atTop.1 hsmall_event with ⟨n, hn⟩
  let m : ℕ := N + n
  have htheta :
      Ch05.thetaAtScale hP hStruct (m : ℤ) ≤
        1 + Real.rpow (3 : ℝ) (-alpha * (n : ℝ)) := by
    have h := hconv hP hStruct hP4 rfl n
    simpa [N, m] using h
  have htheta_eps : Ch05.thetaAtScale hP hStruct (m : ℤ) ≤ 1 + ε := by
    have hdecay_le : Real.rpow (3 : ℝ) (-alpha * (n : ℝ)) ≤ ε :=
      (hn n le_rfl).le
    linarith
  let bm : ℝ := hP.barSigmaAtScale hStruct (m : ℤ)
  let cm : ℝ := hP.barSigmaStarAtScale hStruct (m : ℤ)
  have hcm_pos : 0 < cm := by
    simpa [cm] using
      Ch05.Section54.Pigeonhole.barSigmaStarAtScale_pos_of_P4
        hP hStruct hP4 m
  have htheta_def : bm * cm⁻¹ ≤ 1 + ε := by
    simpa [Ch05.thetaAtScale, Ch04.RestrictionLawCarrier.thetaAtScale, bm, cm] using
      htheta_eps
  have hb_le : bm ≤ (1 + ε) * cm := by
    have hmul := mul_le_mul_of_nonneg_right htheta_def hcm_pos.le
    calc
      bm = bm * cm⁻¹ * cm := by field_simp [hcm_pos.ne']
      _ ≤ (1 + ε) * cm := hmul
  calc
    Ch05.Section57.barSigmaLimit hP hStruct ≤ bm := by
      exact csInf_le (barSigma_range_bddBelow_of_P4 hP hStruct hP4) ⟨m, rfl⟩
    _ ≤ (1 + ε) * cm := hb_le
    _ ≤ (1 + ε) * Ch05.Section57.barSigmaStarLimit hP hStruct := by
      exact mul_le_mul_of_nonneg_left
        (le_csSup (barSigmaStar_range_bddAbove_of_P4 hP hStruct hP4) ⟨m, rfl⟩)
        (by linarith)

/-- Under `(P4)`, the upper and starred annealed scalar limits coincide. -/
theorem barSigmaLimit_eq_barSigmaStarLimit_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : Ch05.QuantitativeCoarseGrainedEllipticity P) :
    Ch05.Section57.barSigmaLimit hP hStruct =
      Ch05.Section57.barSigmaStarLimit hP hStruct := by
  refine le_antisymm ?_
    (barSigmaStarLimit_le_barSigmaLimit_of_P4 hP hStruct hP4)
  exact le_of_forall_le_one_add_mul
    (barSigmaStarLimit_pos_of_P4 hP hStruct hP4).le
    (fun ε hε =>
      barSigmaLimit_le_one_add_mul_barSigmaStarLimit_of_P4
        hP hStruct hP4 hε)

/-- Under `(P4)`, the starred scalar coefficients converge to the same positive scalar
as the upper coefficients. -/
theorem barSigmaStarAtScale_tendsto_barSigmaLimit_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : Ch05.QuantitativeCoarseGrainedEllipticity P) :
    Tendsto (fun n : ℕ => hP.barSigmaStarAtScale hStruct (n : ℤ)) atTop
      (nhds (Ch05.Section57.barSigmaLimit hP hStruct)) := by
  simpa [barSigmaLimit_eq_barSigmaStarLimit_of_P4 hP hStruct hP4] using
    barSigmaStarAtScale_tendsto_barSigmaStarLimit_of_P4 hP hStruct hP4

/-- Under `(P4)`, the honest full annealed block matrices converge entrywise to the
block diagonal with the single positive scalar `barSigmaLimit` and its inverse. -/
theorem annealedFullBlockMatrixAtScale_tendsto_barSigmaLimit_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : Ch05.QuantitativeCoarseGrainedEllipticity P) :
    Tendsto
      (fun n : ℕ =>
        toFullBlockMat (Ch04.annealedBlockMatrixAtScale P (n : ℤ)))
      atTop
      (nhds (toFullBlockMat (Ch02.blockDiag
        (Ch05.Section57.barSigmaLimit hP hStruct • (1 : Mat d))
        ((Ch05.Section57.barSigmaLimit hP hStruct)⁻¹ • (1 : Mat d))))) := by
  let L : ℝ := Ch05.Section57.barSigmaLimit hP hStruct
  have hUpper :
      Tendsto (fun n : ℕ => hP.barSigmaAtScale hStruct (n : ℤ))
        atTop (nhds L) := by
    simpa [L] using barSigmaAtScale_tendsto_barSigmaLimit_of_P4 hP hStruct hP4
  have hStar :
      Tendsto (fun n : ℕ => hP.barSigmaStarAtScale hStruct (n : ℤ))
        atTop (nhds L) := by
    simpa [L] using barSigmaStarAtScale_tendsto_barSigmaLimit_of_P4 hP hStruct hP4
  have hStarInv :
      Tendsto (fun n : ℕ => (hP.barSigmaStarAtScale hStruct (n : ℤ))⁻¹)
        atTop (nhds L⁻¹) :=
    hStar.inv₀ (by
      exact (barSigmaLimit_pos_of_P4 hP hStruct hP4).ne')
  have hBlock (n : ℕ) :
      Ch04.annealedBlockMatrixAtScale P (n : ℤ) =
        Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct (n : ℤ) :=
    Ch05.Section54.VarianceBoundGoodScale.annealedBlockMatrixAtScale_eq_scalarAnnealedBlockMatrixAtScale
      hP hStruct (n : ℤ)
  refine tendsto_pi_nhds.2 fun alpha => ?_
  refine tendsto_pi_nhds.2 fun beta => ?_
  cases alpha with
  | inl i =>
      cases beta with
      | inl j =>
          simpa [L, toFullBlockMat, Ch02.blockDiag,
            Ch04.scalarAnnealedBlockMatrixAtScale,
            hBlock,
            Pi.smul_apply] using hUpper.mul_const ((1 : Mat d) i j)
      | inr j =>
          simp [toFullBlockMat, Ch02.blockDiag,
            Ch04.scalarAnnealedBlockMatrixAtScale,
            hBlock]
  | inr i =>
      cases beta with
      | inl j =>
          simp [toFullBlockMat, Ch02.blockDiag,
            Ch04.scalarAnnealedBlockMatrixAtScale,
            hBlock]
      | inr j =>
          simpa [L, toFullBlockMat, Ch02.blockDiag,
            Ch04.scalarAnnealedBlockMatrixAtScale,
            hBlock,
            Pi.smul_apply] using hStarInv.mul_const ((1 : Mat d) i j)

/-- Spatial normalization does not alter the infinite-volume coefficient.

If a triadically normalized pushforward of `P` satisfies CoarseGraining's
structural law and `(P4)`, then the *unnormalized* annealed matrices converge to
the same block diagonal.  This is the bridge needed when the original cutoff
has range `sqrt d * 3^m` rather than CoarseGraining's normalized unit range. -/
theorem annealedFullBlockMatrixAtScale_tendsto_of_scaleNormalized_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (k : ℕ)
    (hStruct : Ch04.RestrictionStructuralLaw
      (Ch04.restrictionScaleNormalizedLaw k P))
    (hP4 : Ch05.QuantitativeCoarseGrainedEllipticity
      (Ch04.restrictionScaleNormalizedLaw k P)) :
    Tendsto
      (fun n : ℕ =>
        toFullBlockMat (Ch04.annealedBlockMatrixAtScale P (n : ℤ)))
      atTop
      (nhds (toFullBlockMat (Ch02.blockDiag
        (Ch05.Section57.barSigmaLimit (hP.scaleNormalized k) hStruct •
          (1 : Mat d))
        ((Ch05.Section57.barSigmaLimit (hP.scaleNormalized k) hStruct)⁻¹ •
          (1 : Mat d))))) := by
  have hNormalized :=
    annealedFullBlockMatrixAtScale_tendsto_barSigmaLimit_of_P4
      (hP.scaleNormalized k) hStruct hP4
  have hTail :
      Tendsto
        (fun n : ℕ =>
          toFullBlockMat
            (Ch04.annealedBlockMatrixAtScale P ((n + k : ℕ) : ℤ)))
        atTop
        (nhds (toFullBlockMat (Ch02.blockDiag
          (Ch05.Section57.barSigmaLimit (hP.scaleNormalized k) hStruct •
            (1 : Mat d))
          ((Ch05.Section57.barSigmaLimit (hP.scaleNormalized k) hStruct)⁻¹ •
            (1 : Mat d))))) := by
    refine hNormalized.congr' (Eventually.of_forall fun n => ?_)
    rw [Ch04.annealedBlockMatrixAtScale_restrictionScaleNormalizedLaw hP k n]
    simp only [Nat.add_comm]
  exact (tendsto_add_atTop_iff_nat k).mp hTail

/-- The positive scalar in an infinite-volume block-diagonal limit is unique. -/
theorem scalar_eq_of_annealedFullBlockMatrixAtScale_tendsto
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d} {σ τ : ℝ}
    (hσ : Tendsto
      (fun n : ℕ =>
        toFullBlockMat (Ch04.annealedBlockMatrixAtScale P (n : ℤ)))
      atTop
      (nhds (toFullBlockMat (Ch02.blockDiag
        (σ • (1 : Mat d)) (σ⁻¹ • (1 : Mat d))))))
    (hτ : Tendsto
      (fun n : ℕ =>
        toFullBlockMat (Ch04.annealedBlockMatrixAtScale P (n : ℤ)))
      atTop
      (nhds (toFullBlockMat (Ch02.blockDiag
        (τ • (1 : Mat d)) (τ⁻¹ • (1 : Mat d)))))) :
    σ = τ := by
  have hlimit := tendsto_nhds_unique hσ hτ
  have hentry := congrArg
    (fun M : FullBlockMat d => M (Sum.inl (0 : Fin d)) (Sum.inl (0 : Fin d)))
    hlimit
  simpa [toFullBlockMat, Ch02.blockDiag, Pi.smul_apply] using hentry

/-- A normalized structural law with `(P4)` gives existence and uniqueness of the
positive scalar describing the *unnormalized* infinite-volume annealed block
limit. -/
theorem existsUnique_pos_annealedFullBlockMatrixAtScale_limit_of_scaleNormalized_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (k : ℕ)
    (hStruct : Ch04.RestrictionStructuralLaw
      (Ch04.restrictionScaleNormalizedLaw k P))
    (hP4 : Ch05.QuantitativeCoarseGrainedEllipticity
      (Ch04.restrictionScaleNormalizedLaw k P)) :
    ∃! σ : ℝ,
      0 < σ ∧
        Tendsto
          (fun n : ℕ =>
            toFullBlockMat (Ch04.annealedBlockMatrixAtScale P (n : ℤ)))
          atTop
          (nhds (toFullBlockMat (Ch02.blockDiag
            (σ • (1 : Mat d)) (σ⁻¹ • (1 : Mat d))))) := by
  let L : ℝ := Ch05.Section57.barSigmaLimit (hP.scaleNormalized k) hStruct
  refine ⟨L, ?_, ?_⟩
  · exact ⟨by
      simpa [L] using
        barSigmaLimit_pos_of_P4 (hP.scaleNormalized k) hStruct hP4,
      by
        simpa [L] using
          annealedFullBlockMatrixAtScale_tendsto_of_scaleNormalized_P4
            hP k hStruct hP4⟩
  · intro σ hσ
    exact scalar_eq_of_annealedFullBlockMatrixAtScale_tendsto hσ.2 <| by
      simpa [L] using
        annealedFullBlockMatrixAtScale_tendsto_of_scaleNormalized_P4
          hP k hStruct hP4

end

end Algsuperdiff.Section3.Annealed
