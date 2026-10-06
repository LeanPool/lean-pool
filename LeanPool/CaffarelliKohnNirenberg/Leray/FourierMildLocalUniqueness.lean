/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMildLocalFixedPoint
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Uniqueness of the local mild trajectory

The lifespan bound also controls any continuous mild trajectory with the same
initial data. This supplies uniqueness without a radius hypothesis.
-/

public section

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

private theorem regularizedMildStokesIntegral_zero
    (F : ℝ → RealTensorL2) : regularizedMildStokesIntegral F 0 = 0 := by
  simp [regularizedMildStokesIntegral]

@[expose]
def regularizedMildPathRestrict {T : ℝ}
    (u : C(RegularizedMildTimeInterval T, RealVectorL2))
    (τ : RegularizedMildTimeInterval T) :
    C(RegularizedMildTimeInterval τ.1, RealVectorL2) :=
  ⟨fun s => u ⟨s.1, s.2.1, le_trans s.2.2 τ.2.2⟩,
    u.continuous.comp (continuous_subtype_val.subtype_mk fun s =>
      ⟨s.2.1, le_trans s.2.2 τ.2.2⟩)⟩

private theorem regularizedMildPathRestrict_apply {T : ℝ}
    (u : C(RegularizedMildTimeInterval T, RealVectorL2))
    (τ : RegularizedMildTimeInterval T)
    (s : RegularizedMildTimeInterval τ.1) :
    regularizedMildPathRestrict u τ s =
      u ⟨s.1, s.2.1, le_trans s.2.2 τ.2.2⟩ := rfl

private theorem regularizedMildTrajectory_initial_norm_le
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (b : RealVectorL2)
    (u : C(RegularizedMildTimeInterval (regularizedMildLocalLifespan ρ ε b),
      RealVectorL2))
    (hu : IsRegularizedMildTrajectory ρ ε hε b
      (regularizedMildLocalLifespan ρ ε b) u) :
    ‖u ⟨0, le_refl _, (regularizedMildLocalLifespan_pos ρ ε hε b).le⟩‖ ≤ ‖b‖ := by
  have h := hu ⟨0, le_refl _, (regularizedMildLocalLifespan_pos ρ ε hε b).le⟩
  rw [regularizedMildRightHandSide, regularizedMildStokesIntegral_zero, sub_zero] at h
  rw [h]
  exact realHeatOperator_norm_le 0 (le_refl _) b

private theorem regularizedMildFirstCrossing
    (T R : ℝ) (hT : 0 ≤ T) (u : C(RegularizedMildTimeInterval T, RealVectorL2))
    (hzero : ‖u ⟨0, le_refl _, hT⟩‖ < R)
    (hexceed : ∃ t : RegularizedMildTimeInterval T, R < ‖u t‖) :
    ∃ τ : RegularizedMildTimeInterval T,
      ‖u τ‖ = R ∧
      ∀ s : RegularizedMildTimeInterval τ.1,
        ‖regularizedMildPathRestrict u τ s‖ ≤ R := by
  let g : ℝ → ℝ := fun s => ‖u (regularizedMildTimeClamp T hT s)‖
  have hg : Continuous g :=
    continuous_norm.comp (u.continuous.comp (regularizedMildTimeClamp_continuous T hT))
  have hgone : g 0 < R := by
    simpa [g, regularizedMildTimeClamp_eq_of_mem T hT ⟨le_refl _, hT⟩] using hzero
  let S : Set ℝ := Set.Icc 0 T ∩ g ⁻¹' Set.Ici R
  have hScompact : IsCompact S :=
    isCompact_Icc.inter_right ((isClosed_Ici.preimage hg))
  obtain ⟨t, ht⟩ := hexceed
  have hSn : S.Nonempty := by
    refine ⟨t.1, t.2, ?_⟩
    simpa [g, regularizedMildTimeClamp_eq_of_mem T hT t.2] using le_of_lt ht
  obtain ⟨τ, hτS, hτmin⟩ := hScompact.exists_isMinOn hSn continuous_id.continuousOn
  have hτI : τ ∈ Set.Icc 0 T := hτS.1
  have hτR : R ≤ g τ := hτS.2
  have hmin : ∀ s ∈ S, τ ≤ s := by
    intro s hs
    exact hτmin hs
  have hτeq : g τ = R := by
    by_contra hneq
    have hRlt : R < g τ := lt_of_le_of_ne hτR (Ne.symm hneq)
    have hRmem : R ∈ Set.Icc (g 0) (g τ) := ⟨le_of_lt hgone, le_of_lt hRlt⟩
    obtain ⟨s, hs, hgs⟩ := (intermediate_value_Icc hτI.1 hg.continuousOn) hRmem
    have hsS : s ∈ S := ⟨⟨hs.1, le_trans hs.2 hτI.2⟩, le_of_eq hgs.symm⟩
    have hτle : τ ≤ s := hmin s hsS
    have hseq : s = τ := le_antisymm hs.2 hτle
    exact hneq (by simpa [hseq] using hgs)
  let τ' : RegularizedMildTimeInterval T := ⟨τ, hτI⟩
  refine ⟨τ', ?_, ?_⟩
  · simpa [g, τ', regularizedMildTimeClamp_eq_of_mem T hT hτI] using hτeq
  · intro s
    by_contra hnot
    have hstrict : R < ‖regularizedMildPathRestrict u τ' s‖ := lt_of_not_ge hnot
    have hsS : s.1 ∈ S := by
      refine ⟨⟨s.2.1, le_trans s.2.2 hτI.2⟩, ?_⟩
      simpa [g, regularizedMildPathRestrict_apply,
        regularizedMildTimeClamp_eq_of_mem T hT
          ⟨s.2.1, le_trans s.2.2 hτI.2⟩] using le_of_lt hstrict
    have hτle := hmin s.1 hsS
    have hsEq : s.1 = τ := le_antisymm s.2.2 hτle
    have hvalue : ‖regularizedMildPathRestrict u τ' s‖ = R := by
      have hpoint : (⟨s.1, s.2.1, le_trans s.2.2 hτI.2⟩ :
          RegularizedMildTimeInterval T) = τ' := Subtype.ext hsEq
      rw [regularizedMildPathRestrict_apply, hpoint]
      simpa [g, τ', regularizedMildTimeClamp_eq_of_mem T hT hτI] using hτeq
    exact (lt_irrefl R) (hvalue ▸ hstrict)

private theorem regularizedMildPathRestrict_mild_endpoint
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (b : RealVectorL2) (T : ℝ)
    (u : C(RegularizedMildTimeInterval T, RealVectorL2))
    (hu : IsRegularizedMildTrajectory ρ ε hε b T u)
    (τ : RegularizedMildTimeInterval T) :
    u τ = regularizedMildLocalMap ρ ε hε b τ.1 τ.2.1
      (regularizedMildPathRestrict u τ) ⟨τ.1, τ.2.1, le_refl _⟩ := by
  rw [hu τ, regularizedMildLocalMap_eq_rightHandSide]
  unfold regularizedMildRightHandSide
  congr 1
  unfold regularizedMildStokesIntegral
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  by_cases hst : s < τ.1
  · have hsT : s ∈ RegularizedMildTimeInterval T :=
      ⟨hs.1, le_trans hs.2 τ.2.2⟩
    have hsτ : s ∈ RegularizedMildTimeInterval τ.1 := hs
    simp [regularizedMildStokesIntegrand, hst, hsT, hsτ,
      regularizedMildPathRestrict_apply]
  · simp [regularizedMildStokesIntegrand, hst]

/-- Every continuous solution of `eq:reg-mild` lies in the contraction ball
throughout the lifespan of `eq:reg-lifespan`. -/
theorem regularizedMildTrajectory_norm_le_local
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (b : RealVectorL2)
    (u : C(RegularizedMildTimeInterval (regularizedMildLocalLifespan ρ ε b),
      RealVectorL2))
    (hu : IsRegularizedMildTrajectory ρ ε hε b
      (regularizedMildLocalLifespan ρ ε b) u) :
    ∀ t, ‖u t‖ ≤ 2 * regularizedMildLocalM b := by
  let T := regularizedMildLocalLifespan ρ ε b
  let M := regularizedMildLocalM b
  have hT : 0 ≤ T := (regularizedMildLocalLifespan_pos ρ ε hε b).le
  have hzero : ‖u ⟨0, le_refl _, hT⟩‖ < 2 * M := by
    have hbound := regularizedMildTrajectory_initial_norm_le ρ ε hε b u hu
    have hstrict : ‖b‖ < 2 * M := by
      dsimp [M, regularizedMildLocalM]
      linarith only [norm_nonneg b]
    exact hbound.trans_lt hstrict
  by_contra hnot
  push Not at hnot
  obtain ⟨τ, hτeq, hτbound⟩ :=
    regularizedMildFirstCrossing T (2 * M) hT u hzero hnot
  let w := regularizedMildPathRestrict u τ
  let F := regularizedMildClampedTensorTrajectory ρ ε hε τ.1 τ.2.1 w
  let C := regularizedMildMollifierConstant ρ ε * (2 * M) ^ 2
  have hMnonneg : 0 ≤ M := by dsimp [M, regularizedMildLocalM]; positivity
  have hR : 0 ≤ 2 * M := mul_nonneg (by norm_num) hMnonneg
  have hFC : ∀ s, ‖F s‖ ≤ C := by
    simpa [F, C, w] using
      regularizedMildClampedTensorTrajectory_norm_le ρ ε hε τ.1 τ.2.1 w
        (2 * M) hR hτbound
  have hC : 0 ≤ C :=
    mul_nonneg ENNReal.toReal_nonneg (sq_nonneg (2 * M))
  have hI :
      ‖∫ q in (0 : ℝ)..τ.1, mildShiftedStokesIntegrand F τ.1 q‖ ≤ M / 2 := by
    calc
      ‖∫ q in (0 : ℝ)..τ.1, mildShiftedStokesIntegrand F τ.1 q‖ ≤
          2 * (C / Real.sqrt (2 * Real.exp 1)) * Real.sqrt τ.1 :=
        mildShiftedStokesIntegral_norm_le F C hFC hC τ.1 τ.1 τ.2.1
      _ ≤ 2 * (C / Real.sqrt (2 * Real.exp 1)) * Real.sqrt T := by
        gcongr
        exact τ.2.2
      _ = M / 2 := by
        simpa [C, M] using regularizedMildBallAbelBalance ρ ε hε b
  have hendpoint := regularizedMildPathRestrict_mild_endpoint ρ ε hε b T u hu τ
  rw [regularizedMildLocalMap_eq_shifted] at hendpoint
  have hheat := realHeatOperator_norm_le τ.1 τ.2.1 b
  have hnorm : ‖u τ‖ ≤ ‖b‖ + M / 2 := by
    rw [hendpoint]
    exact (norm_sub_le _ _).trans (add_le_add hheat hI)
  rw [hτeq] at hnorm
  dsimp [M, regularizedMildLocalM] at hnorm
  linarith only [hnorm, norm_nonneg b]

/-- The mild trajectory on the lifespan of `eq:reg-lifespan` is unique among
all continuous spatial `L²` mild trajectories with the same initial data. -/
theorem regularizedMildTrajectory_unique_local
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (b : RealVectorL2)
    (u v : C(RegularizedMildTimeInterval (regularizedMildLocalLifespan ρ ε b),
      RealVectorL2))
    (hu : IsRegularizedMildTrajectory ρ ε hε b
      (regularizedMildLocalLifespan ρ ε b) u)
    (hv : IsRegularizedMildTrajectory ρ ε hε b
      (regularizedMildLocalLifespan ρ ε b) v) : u = v := by
  let T := regularizedMildLocalLifespan ρ ε b
  let hT : 0 ≤ T := (regularizedMildLocalLifespan_pos ρ ε hε b).le
  let f := regularizedMildLocalMap ρ ε hε b T hT
  have hufix : f u = u := by
    apply ContinuousMap.ext
    intro t
    exact (regularizedMildLocalMap_eq_rightHandSide ρ ε hε b T hT u t).trans
      (hu t).symm
  have hvfix : f v = v := by
    apply ContinuousMap.ext
    intro t
    exact (regularizedMildLocalMap_eq_rightHandSide ρ ε hε b T hT v t).trans
      (hv t).symm
  have hboundu := regularizedMildTrajectory_norm_le_local ρ ε hε b u hu
  have hboundv := regularizedMildTrajectory_norm_le_local ρ ε hε b v hv
  have hlip := regularizedMildLocalMap_sub_norm_le ρ ε hε b u v hboundu hboundv
  change ‖f u - f v‖ ≤ (1 / 2 : ℝ) * ‖u - v‖ at hlip
  rw [hufix, hvfix] at hlip
  have hzero : ‖u - v‖ = 0 := by
    linarith only [hlip, norm_nonneg (u - v)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

end CKN.Leray

end
