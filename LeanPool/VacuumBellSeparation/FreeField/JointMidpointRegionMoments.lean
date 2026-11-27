/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.JointNormalizedMomentVectors
public import LeanPool.VacuumBellSeparation.FreeField.JointRegionMomentFamily

/-!
# Actual weighted moments in the midpoint ball of the joint region

The containing radius is s/2+1. After division by s, the growth base is
independent of the separation. The vectors belong to the original joint
source completion and represent the literal normalized test moments.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation

open Gaussian Gaussian.HilbertComplexification Set Metric

theorem spatialAxisDisplacement_zero_eq_single (t : ℝ) :
    spatialAxisDisplacement t 0 = PiLp.single 2 (0 : Fin 3) t := by
  ext j
  simp [spatialAxisDisplacement, PiLp.single_apply]

theorem norm_spatialAxisDisplacement_zero (t : ℝ) :
    ‖spatialAxisDisplacement t 0‖ = |t| := by
  rw [spatialAxisDisplacement_zero_eq_single, PiLp.norm_single, Real.norm_eq_abs]

/-- Joint midpoint moment radius given by `s / 2 + 1`. -/
def jointMidpointMomentRadius (s : ℝ) : ℝ := s / 2 + 1

theorem jointMidpointMomentRadius_pos {s : ℝ} (hs : 2 ≤ s) :
    0 < jointMidpointMomentRadius s := by unfold jointMidpointMomentRadius; linarith

theorem jointMidpointMomentRadius_le {s : ℝ} (hs : 2 ≤ s) :
    jointMidpointMomentRadius s ≤ s := by unfold jointMidpointMomentRadius; linarith

theorem jointSourceRegion_subset_midpoint_ball {s : ℝ} (hs : 2 ≤ s) :
    jointSourceRegion s ⊆ ball (spatialAxisDisplacement (s / 2) 0)
      (jointMidpointMomentRadius s) := by
  have hhalf : 0 ≤ s / 2 := by linarith
  have hc : ‖spatialAxisDisplacement (s / 2) 0‖ = s / 2 := by
    rw [norm_spatialAxisDisplacement_zero, abs_of_nonneg hhalf]
  have hd : spatialAxisDisplacement s 0 - spatialAxisDisplacement (s / 2) 0 =
      spatialAxisDisplacement (s / 2) 0 := by
    ext j
    simp only [PiLp.sub_apply, spatialAxisDisplacement, PiLp.coe_symm_continuousLinearEquiv,
      PiLp.zero_apply, add_zero]
    split_ifs <;> ring
  intro x hx
  simp only [jointSourceRegion, jointCenterIndex_zero, jointCenterIndex_one,
    mem_union, mem_ball] at hx
  rw [mem_ball]
  rcases hx with hx | hx
  · have ht := dist_triangle x 0 (spatialAxisDisplacement (s / 2) 0)
    rw [dist_zero_left, hc] at ht
    unfold jointMidpointMomentRadius
    linarith
  · have ht := dist_triangle x (spatialAxisDisplacement s 0)
      (spatialAxisDisplacement (s / 2) 0)
    rw [dist_eq_norm (spatialAxisDisplacement s 0), hd, hc] at ht
    unfold jointMidpointMomentRadius
    linarith

/-- Joint weighted moment degree base obtained from `max`. -/
def jointWeightedMomentDegreeBase (b : ℝ) : ℝ := max 1 (sourceMomentBase b)

/-- Joint weighted field scale. -/
def jointWeightedFieldScale (C b μ s : ℝ) : ℝ :=
  C * jointMidpointMomentRadius s / (1 + μ * jointMidpointMomentRadius s) *
    Real.exp (sourceMomentLambda b * μ * jointMidpointMomentRadius s)

/-- Joint weighted momentum scale. -/
def jointWeightedMomentumScale (C b μ s : ℝ) : ℝ :=
  C * jointMidpointMomentRadius s ^ 2 / (1 + μ * jointMidpointMomentRadius s) ^ 2 *
    Real.exp (sourceMomentLambda b * μ * jointMidpointMomentRadius s)

/-- Field and momentum moments with the midpoint weight, indexed by spatial monomials. -/
structure JointWeightedMomentFamily {μ : ℝ} (hμ : 0 < μ) (s b : ℝ) where
  /-- Weighted moment vectors in the field component of the joint source space. -/
  field : (Fin 3 → ℕ) → ComplexSourceHilbert hμ (jointSourceRegion s)
  /-- Weighted moment vectors in the momentum component of the joint source space. -/
  momentum : (Fin 3 → ℕ) → ComplexSourceHilbert hμ (jointSourceRegion s)
  field_pairing : ∀ α (x : SourceTestSpace hμ (jointSourceRegion s)),
    inner ℂ (ofReal (x : SourceHilbert hμ (jointSourceRegion s)))
      ((sourceReserve hμ (jointSourceRegion s) ^ b) (field α)) =
      (normalizedCenteredSourceMoment (spatialAxisDisplacement (s / 2) 0) s x.1.1 α : ℂ)
  momentum_pairing : ∀ α (x : SourceTestSpace hμ (jointSourceRegion s)),
    inner ℂ (ofReal (x : SourceHilbert hμ (jointSourceRegion s)))
      ((sourceReserve hμ (jointSourceRegion s) ^ b) (momentum α)) =
      (normalizedCenteredSourceMoment (spatialAxisDisplacement (s / 2) 0) s x.1.2 α : ℂ)

/-- Existence and degree growth are consequences of the actual modular
moment estimates, with constants fixed before the mass and separation. -/
theorem exists_jointWeightedMomentFamily {b : ℝ} (hb : 1 / 2 ≤ b) (hb1 : b < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : ℝ) (hμ : 0 < μ) (s : ℝ), 2 ≤ s →
      ∃ v : JointWeightedMomentFamily hμ s b,
        (∀ α, ‖v.field α‖ ≤ jointWeightedFieldScale C b μ s *
          jointWeightedMomentDegreeBase b ^ (∑ j, α j)) ∧
        (∀ α, ‖v.momentum α‖ ≤ jointWeightedMomentumScale C b μ s *
          jointWeightedMomentDegreeBase b ^ (∑ j, α j)) := by
  classical
  obtain ⟨C, hC, h⟩ := exists_normalized_centered_weighted_source_moments hb hb1
  refine ⟨C, hC, ?_⟩
  intro μ hμ s hs
  have hs₀ : 0 < s := by linarith
  have hT := jointMidpointMomentRadius_pos hs
  have hB : 0 ≤ sourceMomentBase b := by
    unfold sourceMomentBase
    exact mul_nonneg (by norm_num) (sourceMomentLambda_pos hb hb1).le
  have hbase : sourceMomentBase b * jointMidpointMomentRadius s / s ≤
      jointWeightedMomentDegreeBase b := by
    apply le_trans _ (le_max_right _ _)
    apply (div_le_iff₀ hs₀).mpr
    exact mul_le_mul_of_nonneg_left (jointMidpointMomentRadius_le hs) hB
  choose u v hu hv huf hvf using h μ hμ (jointMidpointMomentRadius s) s hT hs₀
    (spatialAxisDisplacement (s / 2) 0) (jointSourceRegion s)
    (jointSourceRegion_subset_midpoint_ball hs)
  let w : JointWeightedMomentFamily hμ s b := ⟨u, v, huf, hvf⟩
  refine ⟨w, ?_, ?_⟩
  · intro α
    apply (hu α).trans
    change jointWeightedFieldScale C b μ s * _ ≤ _
    apply mul_le_mul_of_nonneg_left _ (by unfold jointWeightedFieldScale; positivity)
    exact pow_le_pow_left₀ (by positivity) hbase _
  · intro α
    apply (hv α).trans
    change jointWeightedMomentumScale C b μ s * _ ≤ _
    apply mul_le_mul_of_nonneg_left _ (by unfold jointWeightedMomentumScale; positivity)
    exact pow_le_pow_left₀ (by positivity) hbase _

end VacuumBellSeparation
