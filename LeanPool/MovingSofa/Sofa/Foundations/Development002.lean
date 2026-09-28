/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Cap.Foundations.Development006
public import LeanPool.MovingSofa.Gerver.Foundations.Development002
public import LeanPool.MovingSofa.Sofa.Foundations.Development001
public import Mathlib.MeasureTheory.Measure.Real
/-!
# Moving sofa: related mathematical developments

* `Sofa.Area`.
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
# Sofa / Area
-/

@[expose] public section

noncomputable section

namespace MovingSofa

theorem monotoneSofa_structure (s : Set Point) (ω : ℝ)
    (hs : ∃ s₀ : Set Point, IsStandardPosition s₀ ω ∧ s = monotonization s₀ ω)
    (K : CapSpace ω) (hK : (K.val : Set Point) = capOfSofa s ω) :
    s = (K.val : Set Point) \ capNiche K := by
  obtain ⟨s₀, hs₀, rfl⟩ := hs
  have heq : capOfSofa (monotonization s₀ ω) ω = capOfSofa s₀ ω := by
    have hparts (t : ℝ) (ht : t ∈ Set.Icc 0 ω) :
        (rotatingHallwayParts (monotonization s₀ ω) (t : Real.Angle)).outerQuadrant =
          (rotatingHallwayParts s₀ (t : Real.Angle)).outerQuadrant := by
      have h₀ := ((standardPosition_support_eq s₀ ω hs₀).1 t (Or.inl ht)).1
      have h₁ := ((standardPosition_support_eq s₀ ω hs₀).1 (t + Real.pi / 2)
        (Or.inr ⟨by linarith [ht.1], by linarith [ht.2]⟩)).1
      simp only [Real.Angle.coe_add] at h₁
      change supportingPlacement (monotonization s₀ ω) (t : Real.Angle) ''
        hallwayParts.outerQuadrant = supportingPlacement s₀ (t : Real.Angle) ''
          hallwayParts.outerQuadrant
      have he : supportingPlacement (monotonization s₀ ω) (t : Real.Angle) =
          supportingPlacement s₀ (t : Real.Angle) := by
        funext p
        simp only [supportingPlacement, h₀, h₁]
      rw [he]
    unfold capOfSofa
    congr 1
    apply Set.iInter_congr
    intro t
    apply Set.iInter_congr
    exact hparts t
  exact standardPosition_monotonization s₀ ω hs₀ K (hK.trans heq)

theorem capAreaFunctional_eq_sofaArea (s : Set Point) (ω : ℝ)
    (hs : ∃ s₀ : Set Point, IsStandardPosition s₀ ω ∧ s = monotonization s₀ ω)
    (K : CapSpace ω) (hK : (K.val : Set Point) = capOfSofa s ω) :
    capAreaFunctional K = ClassicalResults.area s := by
  have heq := monotoneSofa_structure s ω hs K hK
  have hconn : IsConnected s := by
    obtain ⟨s₀, hs₀, rfl⟩ := hs
    exact standardPosition_monotonization_connected s₀ ω hs₀
  have hsub : capNiche K ⊆ (K.val : Set Point) :=
    (cap_niche_connected_iff K).1.mpr
      ((cap_niche_connected_iff K).2.1.mpr
        ((cap_niche_connected_iff K).2.2.mpr (heq ▸ hconn)))
  rw [capAreaFunctional, heq]
  change MeasureTheory.volume.real (K.val : Set Point) -
    MeasureTheory.volume.real (capNiche K) =
      MeasureTheory.volume.real ((K.val : Set Point) \ capNiche K)
  have h := MeasureTheory.measureReal_inter_add_sdiff
    (μ := MeasureTheory.volume) (s := (K.val : Set Point))
    (measurableSet_capNiche K) K.val.isCompact.measure_lt_top.ne
  rw [Set.inter_eq_right.mpr hsub] at h
  linarith

end MovingSofa

end

end

end
