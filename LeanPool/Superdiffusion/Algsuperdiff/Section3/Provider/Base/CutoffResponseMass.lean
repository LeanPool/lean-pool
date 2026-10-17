/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Observable.CutoffHomogenizationError
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Base.AnnealedPlateau
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Base.CutoffCoarseNormBounds
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Base.CutoffMassWeightedSum
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.ErrorComparison.ToLambdas
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.HomogenizationError.Finite

/-!
# CutoffResponseMass

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Cutoff response bound by the annealed plateau and descendant mass

This module proves the deterministic response bridge needed by the corrected
Section 3.2 base-case route.  The named normalized-response estimate bounds
each descendant response by the two coarse matrix norms.  The sharp cutoff
coarse-norm bounds then leave a deterministic annealed plateau amplitude and
the genuine squared Frobenius mass on that descendant.  CoarseGraining's
literal `p = infinity`, `q = 2` series identity aggregates these estimates
without replacing translated descendant masses by a root-cube supremum.
-/

namespace Algsuperdiff.Section3.Provider.Base

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-- The paper-wide dimension assumption stored in the model supplies
CoarseGraining's nonzero-dimension instance. -/
private theorem neZero_of_model_response (M : ABKModel d) : NeZero d :=
  ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩

/-- The deterministic plateau amplitude in `e.plateau.region.bound`. -/
noncomputable def cutoffPlateauAmplitude (M : ABKModel d) (m : ℤ) : ℝ :=
  Disorder.cstarPlus M * (2 * M.nu ^ 2)⁻¹ * M.gamma⁻¹ *
    (1 + 4 * M.gamma) * (3 : ℝ) ^ (2 * M.gamma * (m : ℝ))

/-- The deterministic cutoff plateau amplitude is strictly positive. -/
theorem cutoffPlateauAmplitude_pos (M : ABKModel d) (m : ℤ) :
    0 < cutoffPlateauAmplitude M m := by
  rw [cutoffPlateauAmplitude]
  exact mul_pos
    (mul_pos
      (mul_pos
        (mul_pos (Disorder.cstarPlus_pos M)
          (inv_pos.mpr (mul_pos (by norm_num) (pow_pos M.nu_pos 2))))
        (inv_pos.mpr M.shellPrefix.gamma_pos))
      (add_pos_of_pos_of_nonneg zero_lt_one
        (mul_nonneg (by norm_num) M.shellPrefix.gamma_pos.le)))
    (Real.rpow_pos_of_pos (by norm_num) _)

private theorem weighted_ratio_sub_two_le
    {nu sigma amplitude : ℝ} (hnu : 0 < nu) (hsigma : 0 < sigma)
    (hlower : nu ≤ sigma) (hupper : sigma ≤ nu * (1 + amplitude)) :
    sigma⁻¹ * nu + sigma * nu⁻¹ - 2 ≤ amplitude := by
  have hleft : sigma⁻¹ * nu ≤ 1 := (inv_mul_le_one₀ hsigma).2 hlower
  have hright : sigma * nu⁻¹ ≤ 1 + amplitude := by
    rw [mul_inv_le_iff₀ hnu]
    calc
      sigma ≤ nu * (1 + amplitude) := hupper
      _ = (1 + amplitude) * nu := mul_comm _ _
  linarith only [hleft, hright]

/-- The scalar mismatch between the annealed comparator and `nu` is bounded by
the deterministic plateau amplitude. -/
theorem sigmaBar_weighted_plateau_le_cutoffPlateauAmplitude
    (M : ABKModel d) (m : ℤ) :
    (Annealed.sigmaBar M m : ℝ)⁻¹ * M.nu +
        (Annealed.sigmaBar M m : ℝ) * M.nu⁻¹ - 2 ≤
      cutoffPlateauAmplitude M m := by
  obtain ⟨hlower, hupper⟩ := annealedPlateau M m
  exact weighted_ratio_sub_two_le M.nu_pos (Annealed.sigmaBar M m).2 hlower
    (by simpa only [cutoffPlateauAmplitude] using hupper)

private theorem cutoffFrobeniusMass_le_root_control
    (Q R : TriadicCube d) (hRQ : openCubeSet R ⊆ openCubeSet Q)
    (m : ℤ) (omega : CutoffSample d) :
    Stream.cutoffFrobeniusMass R m omega ≤
      (d : ℝ) ^ 2 * cutoffLocalControl (cubeOriginCoverScale Q) m omega ^ 2 := by
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet R)) := by
    simpa only [volumeMeasureOn] using
      (isOpenBoundedConvexDomain_openCubeSet R).isFiniteMeasure_restrict_volume
  have hintegrable : IntegrableOn
      (fun x : Vec d => Ch02.matrixFrobeniusNormSq (cutoff m omega x))
      (openCubeSet R) volume := by
    exact
      ((Stream.continuous_frobeniusMass_cutoff m omega).continuousOn.integrableOn_compact
        (isBounded_openCubeSet R).isCompact_closure).mono_set subset_closure
  rw [Stream.cutoffFrobeniusMass, Ch02.average, Ch02.cubeDomain_coe]
  refine volumeAverage_le_of_le_on (measurableSet_openCubeSet R) hintegrable ?_ ?_
  · rw [volume_openCubeSet_toReal]
    exact (cubeVolume_pos R).ne'
  · intro x hx
    exact Stream.matrixFrobeniusNormSq_le_of_abs_entry_le fun i j =>
      abs_cutoff_entry_le_cutoffLocalControl (cubeOriginCoverScale Q) m omega
        (openCubeSet_subset_originCover Q (hRQ hx)) i j

private theorem cutoffFrobeniusMassMaximum_le_root_control
    (Q : TriadicCube d) (m : ℤ) (n : ℕ) (omega : CutoffSample d) :
    Stream.cutoffFrobeniusMassMaximum Q m n omega ≤
      (d : ℝ) ^ 2 * cutoffLocalControl (cubeOriginCoverScale Q) m omega ^ 2 := by
  unfold Stream.cutoffFrobeniusMassMaximum
  refine Finset.sup'_le (descendantsAtDepth_nonempty Q n) _ ?_
  intro R hR
  exact cutoffFrobeniusMass_le_root_control Q R
    (openCubeSet_subset_of_mem_descendantsAtDepth hR) m omega

private theorem summable_geometricWeight_two_mul_cutoffFrobeniusMassMaximum
    (M : ABKModel d) (Q : TriadicCube d) (m : ℤ)
    (s : {s : ℝ // s ∈ Set.Ioo 0 1}) (omega : CutoffSample d) :
    Summable (fun n : ℕ => Ch02.geometricWeight (s : ℝ) 2 n *
      (M.nu⁻¹ ^ 2 * Stream.cutoffFrobeniusMassMaximum Q m n omega)) := by
  have hs : 0 < (s : ℝ) := (Set.mem_Ioo.mp s.2).1
  have hsum := HCPolySupport.summable_geometricWeight_mul_of_nonneg_of_le
    (s := (s : ℝ)) (q := 2)
    (C := M.nu⁻¹ ^ 2 *
      ((d : ℝ) ^ 2 * cutoffLocalControl (cubeOriginCoverScale Q) m omega ^ 2))
    (mul_pos hs (by norm_num))
    (fun n => mul_nonneg (sq_nonneg _)
      (Stream.cutoffFrobeniusMassMaximum_nonneg Q m n omega))
    (fun n => mul_le_mul_of_nonneg_left
      (cutoffFrobeniusMassMaximum_le_root_control Q m n omega) (sq_nonneg _))
  simpa only [Ch02.geometricWeight_eq_old] using hsum

/-- At every descendant depth, the normalized cutoff response is bounded by
the deterministic plateau amplitude plus the genuine descendant mass maximum. -/
theorem maxDescendantNormalizedBlockResponseAtScale_coefficientCutoff_le
    (M : ABKModel d) (Q : TriadicCube d) (m : ℤ) (n : ℕ)
    (omega : CutoffSample d) :
    @Ch02.maxDescendantNormalizedBlockResponseAtScale d
        Q (Q.scale - (n : ℤ))
        (coefficientCutoffTriadicCoeffFamily M m omega)
        (scalarMatrix (d := d) (Annealed.sigmaBar M m : ℝ)) ≤
      cutoffPlateauAmplitude M m +
        M.nu⁻¹ ^ 2 * Stream.cutoffFrobeniusMassMaximum Q m n omega := by
  let : NeZero d := neZero_of_model_response M
  have hn : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
  have hk : Q.scale - (n : ℤ) ≤ Q.scale := sub_le_self _ hn
  have hresponse :=
    ErrorComparison.maxDescendantNormalizedBlockResponseAtScale_scalarMatrix_le_sub_two
      Q hk (coefficientCutoffTriadicCoeffFamily M m omega)
        (Annealed.sigmaBar M m).2
  have hb := maxDescendantBMatrixNormAtScale_coefficientCutoff_le M Q m n omega
  have hsigma :=
    maxDescendantSigmaStarInvMatrixNormAtScale_coefficientCutoff_le M Q m n omega
  have hmass : 0 ≤ Stream.cutoffFrobeniusMassMaximum Q m n omega :=
    Stream.cutoffFrobeniusMassMaximum_nonneg Q m n omega
  have hsigmaInv : (Annealed.sigmaBar M m : ℝ)⁻¹ ≤ M.nu⁻¹ :=
    (inv_le_inv₀ (Annealed.sigmaBar M m).2 M.nu_pos).2 (annealedPlateau M m).1
  have hmassTerm :
      (Annealed.sigmaBar M m : ℝ)⁻¹ *
          (M.nu⁻¹ * Stream.cutoffFrobeniusMassMaximum Q m n omega) ≤
        M.nu⁻¹ ^ 2 * Stream.cutoffFrobeniusMassMaximum Q m n omega := by
    calc
      (Annealed.sigmaBar M m : ℝ)⁻¹ *
          (M.nu⁻¹ * Stream.cutoffFrobeniusMassMaximum Q m n omega) =
          ((Annealed.sigmaBar M m : ℝ)⁻¹ * M.nu⁻¹) *
            Stream.cutoffFrobeniusMassMaximum Q m n omega := by ring
      _ ≤ (M.nu⁻¹ * M.nu⁻¹) *
            Stream.cutoffFrobeniusMassMaximum Q m n omega := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hsigmaInv (inv_pos.mpr M.nu_pos).le) hmass
      _ = M.nu⁻¹ ^ 2 * Stream.cutoffFrobeniusMassMaximum Q m n omega := by ring
  calc
    Ch02.maxDescendantNormalizedBlockResponseAtScale Q (Q.scale - (n : ℤ))
        (coefficientCutoffTriadicCoeffFamily M m omega)
        (scalarMatrix (d := d) (Annealed.sigmaBar M m : ℝ))
        ≤ (Annealed.sigmaBar M m : ℝ)⁻¹ *
            Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ))
              (coefficientCutoffTriadicCoeffFamily M m omega) +
          (Annealed.sigmaBar M m : ℝ) *
            Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ))
              (coefficientCutoffTriadicCoeffFamily M m omega) - 2 := hresponse
    _ ≤ (Annealed.sigmaBar M m : ℝ)⁻¹ *
          (M.nu + M.nu⁻¹ * Stream.cutoffFrobeniusMassMaximum Q m n omega) +
        (Annealed.sigmaBar M m : ℝ) * M.nu⁻¹ - 2 := by
      exact sub_le_sub_right
        (add_le_add
          (mul_le_mul_of_nonneg_left hb
            (inv_pos.mpr (Annealed.sigmaBar M m).2).le)
          (mul_le_mul_of_nonneg_left hsigma (Annealed.sigmaBar M m).2.le)) 2
    _ = ((Annealed.sigmaBar M m : ℝ)⁻¹ * M.nu +
          (Annealed.sigmaBar M m : ℝ) * M.nu⁻¹ - 2) +
        (Annealed.sigmaBar M m : ℝ)⁻¹ *
          (M.nu⁻¹ * Stream.cutoffFrobeniusMassMaximum Q m n omega) := by ring
    _ ≤ cutoffPlateauAmplitude M m +
          M.nu⁻¹ ^ 2 * Stream.cutoffFrobeniusMassMaximum Q m n omega :=
      add_le_add (sigmaBar_weighted_plateau_le_cutoffPlateauAmplitude M m) hmassTerm

/-- On every cube and sample, the squared literal `p = infinity`, `q = 2`
cutoff homogenization error is bounded by the plateau and weighted mass sum. -/
theorem homogenizationErrorOnCube_coefficientCutoff_sq_le
    (M : ABKModel d) (Q : TriadicCube d) (m : ℤ)
    (s : {s : ℝ // s ∈ Set.Ioo 0 1}) (omega : CutoffSample d) :
    (@Ch02.HomogenizationErrorOnCube d Q (s : ℝ) .infinity (.finite 2)
        (coefficientCutoffTriadicCoeffFamily M m omega)
        (scalarMatrix (d := d) (Annealed.sigmaBar M m : ℝ))) ^ 2 ≤
      cutoffPlateauAmplitude M m +
        cutoffMassLinearWeightedSum M Q m s omega := by
  let : NeZero d := neZero_of_model_response M
  have hs : 0 < (s : ℝ) := (Set.mem_Ioo.mp s.2).1
  have hsq : 0 < (s : ℝ) * (2 : ℝ) := mul_pos hs (by norm_num)
  have hresponseSummable :=
    Ch02.summable_geometricWeight_two_mul_maxDescendantNormalizedBlockResponseAtScale
      Q (coefficientCutoffTriadicCoeffFamily M m omega)
        (scalarMatrix (d := d) (Annealed.sigmaBar M m : ℝ)) hs
  have hweightSummable :
      Summable (fun n : ℕ => Ch02.geometricWeight (s : ℝ) 2 n) := by
    simpa only [Ch02.geometricWeight_eq_old] using
      (HCPolySupport.summable_geometricWeight (s := (s : ℝ)) (q := 2) hsq)
  have hmassSummable :=
    summable_geometricWeight_two_mul_cutoffFrobeniusMassMaximum M Q m s omega
  have hrightSummable : Summable (fun n : ℕ =>
      Ch02.geometricWeight (s : ℝ) 2 n *
        (cutoffPlateauAmplitude M m +
          M.nu⁻¹ ^ 2 * Stream.cutoffFrobeniusMassMaximum Q m n omega)) := by
    exact ((hweightSummable.mul_right (cutoffPlateauAmplitude M m)).add
      hmassSummable).congr fun n => by ring
  have hterm : ∀ n : ℕ,
      Ch02.geometricWeight (s : ℝ) 2 n *
          Ch02.maxDescendantNormalizedBlockResponseAtScale Q
            (Q.scale - (n : ℤ)) (coefficientCutoffTriadicCoeffFamily M m omega)
            (scalarMatrix (d := d) (Annealed.sigmaBar M m : ℝ)) ≤
        Ch02.geometricWeight (s : ℝ) 2 n *
          (cutoffPlateauAmplitude M m +
            M.nu⁻¹ ^ 2 * Stream.cutoffFrobeniusMassMaximum Q m n omega) := by
    intro n
    refine mul_le_mul_of_nonneg_left
      (maxDescendantNormalizedBlockResponseAtScale_coefficientCutoff_le
        M Q m n omega) ?_
    simpa only [Ch02.geometricWeight_eq_old] using
      HCPolySupport.geometricWeight_nonneg n hsq.le
  have hseries := Summable.tsum_le_tsum hterm hresponseSummable hrightSummable
  have hweightOne :
      ∑' n : ℕ, Ch02.geometricWeight (s : ℝ) 2 n = 1 := by
    simpa only [Ch02.geometricWeight_eq_old] using
      (HCPolySupport.tsum_geometricWeight_eq_one (s := (s : ℝ)) (q := 2) hsq)
  calc
    (Ch02.HomogenizationErrorOnCube Q (s : ℝ) .infinity (.finite 2)
        (coefficientCutoffTriadicCoeffFamily M m omega)
        (scalarMatrix (d := d) (Annealed.sigmaBar M m : ℝ))) ^ 2 =
        ∑' n : ℕ, Ch02.geometricWeight (s : ℝ) 2 n *
          Ch02.maxDescendantNormalizedBlockResponseAtScale Q
            (Q.scale - (n : ℤ)) (coefficientCutoffTriadicCoeffFamily M m omega)
            (scalarMatrix (d := d) (Annealed.sigmaBar M m : ℝ)) :=
      Ch02.homogenizationErrorOnCube_infinity_two_sq_eq_tsum Q hs _ _
    _ ≤ ∑' n : ℕ, Ch02.geometricWeight (s : ℝ) 2 n *
        (cutoffPlateauAmplitude M m +
          M.nu⁻¹ ^ 2 * Stream.cutoffFrobeniusMassMaximum Q m n omega) := hseries
    _ = (∑' n : ℕ, Ch02.geometricWeight (s : ℝ) 2 n *
          cutoffPlateauAmplitude M m) +
        ∑' n : ℕ, Ch02.geometricWeight (s : ℝ) 2 n *
          (M.nu⁻¹ ^ 2 * Stream.cutoffFrobeniusMassMaximum Q m n omega) := by
      rw [← Summable.tsum_add (hweightSummable.mul_right (cutoffPlateauAmplitude M m))
        hmassSummable]
      apply tsum_congr
      intro n
      ring
    _ = cutoffPlateauAmplitude M m +
        cutoffMassLinearWeightedSum M Q m s omega := by
      rw [tsum_mul_right, hweightOne, one_mul]
      rfl

/-- The public measurable cutoff error satisfies the plateau-plus-mass bound
almost everywhere under the genuine cutoff-sample law. -/
theorem ae_cutoffHomogenizationError_sq_le_cutoffPlateauAmplitude_add_mass
    (M : ABKModel d) (m : ℤ) (s : {s : ℝ // s ∈ Set.Ioo 0 1}) :
    ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      Observable.cutoffHomogenizationError M m
          ⟨(s : ℝ), (Set.mem_Ioo.mp s.2).1⟩ omega ^ 2 ≤
        cutoffPlateauAmplitude M m +
          cutoffMassLinearWeightedSum M (originCube d m) m s omega := by
  have hrepresentative :=
    Observable.cutoffHomogenizationError_ae_eq_homogenizationErrorOnCube M m
      ⟨(s : ℝ), (Set.mem_Ioo.mp s.2).1⟩
  filter_upwards [hrepresentative] with omega homega
  rw [homega]
  simpa only [Observable.isotropicComparatorMatrix] using
    homogenizationErrorOnCube_coefficientCutoff_sq_le
      M (originCube d m) m s omega

end

end Algsuperdiff.Section3.Provider.Base
