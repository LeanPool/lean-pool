/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Cap.Foundations.Development006
public import LeanPool.MovingSofa.Motion.Foundations.Development001
public import LeanPool.MovingSofa.Sofa.Foundations.Development001
/-!
# Moving sofa: related mathematical developments

* `Motion.Monotonization`.
-/

@[expose] public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Motion / Monotonization
-/

@[expose] public section

noncomputable section
open Set
open scoped unitInterval
namespace MovingSofa

private theorem isClosed_supportingHallway (s : Set Point) (t : Real.Angle) :
    IsClosed (supportingHallway s t) := by
  have hclosed : IsClosed hallway := by
    rw [hallway_eq_outerQuadrant_sdiff_innerQuadrant]
    apply IsClosed.sdiff
    · change IsClosed {p : Point | p 0 ≤ 1 ∧ p 1 ≤ 1}
      exact (isClosed_le (by fun_prop : Continuous (fun p : Point ↦ p 0)) continuous_const).inter
        (isClosed_le (by fun_prop : Continuous (fun p : Point ↦ p 1)) continuous_const)
    · change IsOpen {p : Point | p 0 < 0 ∧ p 1 < 0}
      exact (isOpen_lt (by fun_prop : Continuous (fun p : Point ↦ p 0)) continuous_const).inter
        (isOpen_lt (by fun_prop : Continuous (fun p : Point ↦ p 1)) continuous_const)
  have heq : supportingPlacement s t = supportingPlacementEquiv s t := by
    funext p
    exact (supportingPlacementEquiv_apply s t p).symm
  rw [supportingHallway, heq]
  exact (supportingPlacementEquiv s t).toHomeomorph.isClosedMap _ hclosed

private theorem isClosed_monotonization (s : Set Point) (ω : ℝ) :
    IsClosed (monotonization s ω) := by
  have hP : (stripParallelogram ω).1 =
      {p : Point | p 1 ∈ Icc (0 : ℝ) 1 ∧
        inner ℝ p (normalVector (ω : Real.Angle)) ∈ Icc (0 : ℝ) 1} := by
    ext p
    exact mem_stripParallelogram_iff ω p
  have hclosedP : IsClosed (stripParallelogram ω).1 := by
    rw [hP]
    exact (isClosed_Icc.preimage (by fun_prop : Continuous (fun p : Point ↦ p 1))).inter
      (isClosed_Icc.preimage (continuous_id.inner continuous_const))
  exact hclosedP.inter (isClosed_iInter fun t ↦
    isClosed_iInter fun _ ↦ isClosed_supportingHallway s (t : Real.Angle))

private theorem monotonization_subset_capOfSofa (s : Set Point) (ω : ℝ) :
    monotonization s ω ⊆ capOfSofa s ω := by
  intro p hp
  change p ∈ (stripParallelogram ω).1 ∩
    ⋂ t ∈ Icc 0 ω, supportingHallway s (t : Real.Angle) at hp
  refine ⟨hp.1, ?_⟩
  simp only [mem_inter_iff, mem_iInter] at hp ⊢
  intro t ht
  exact supportingHallway_subset_outerQuadrant s (t : Real.Angle) (hp.2 t ht)

private theorem isCompact_monotonization (s : Set Point) (ω : ℝ)
    (hs : IsStandardPosition s ω) : IsCompact (monotonization s ω) := by
  obtain ⟨K, hK⟩ := standardPosition_cap s ω hs
  have hc : IsCompact (capOfSofa s ω) := hK ▸ K.val.isCompact
  exact hc.of_isClosed_subset (isClosed_monotonization s ω)
    (monotonization_subset_capOfSofa s ω)

private theorem hasRotationAngle_monotonization (s : Set Point) (ω : ℝ)
    (hs : IsStandardPosition s ω) : HasRotationAngle (monotonization s ω) ω := by
  have hsne : s.Nonempty := by
    obtain ⟨m, hm, _⟩ := hs.2.1
    exact hm.1.nonempty
  exact hasRotationAngle_of_subset_supportingHallways s (monotonization s ω) ω
    hsne hs.1 hs.2.2.1.le hs.2.2.2.2.1 hs.2.2.2.2.2
    (standardPosition_monotonization_connected s ω hs)
    (isClosed_monotonization s ω) Set.Subset.rfl

theorem standardPosition_monotonization_standard (s : Set Point) (ω : ℝ)
    (hs : IsStandardPosition s ω) :
    IsStandardPosition (monotonization s ω) ω ∧ s ⊆ monotonization s ω := by
  refine ⟨⟨isCompact_monotonization s ω hs, hasRotationAngle_monotonization s ω hs,
    hs.2.2.1, hs.2.2.2.1, ?_, ?_⟩, standardPosition_subset_monotonization s ω hs⟩
  · exact ((standardPosition_support_eq s ω hs).1 ω
      (Or.inl ⟨hs.2.2.1.le, le_rfl⟩)).1.trans hs.2.2.2.2.1
  · exact ((standardPosition_support_eq s ω hs).1 (Real.pi / 2)
      (Or.inr ⟨le_rfl, by linarith [hs.2.2.1]⟩)).1.trans hs.2.2.2.2.2

end MovingSofa

end

end

end
