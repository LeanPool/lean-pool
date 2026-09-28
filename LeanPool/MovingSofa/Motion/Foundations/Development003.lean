/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Infrastructure.MathlibExtensions.Foundations.Development001
public import LeanPool.MovingSofa.Motion.Foundations.Development001
public import LeanPool.MovingSofa.Optimality
/-!
# Moving sofa: related mathematical developments

* `Motion.CanonicalBridge`.
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
# Motion / Canonical Bridge
-/

@[expose] public section

noncomputable section

namespace MovingSofa

open MeasureTheory
open scoped unitInterval

private def normalizeMotion (m : I → Point ≃ᵃⁱ[ℝ] Point) (t : I) :
    Point ≃ᵃⁱ[ℝ] Point :=
  (m 0).symm.trans (m t)

private theorem continuous_normalizeMotion (m : I → Point ≃ᵃⁱ[ℝ] Point)
    (hm : Continuous m) : Continuous (normalizeMotion m) := by
  rw [continuous_induced_rng]
  have hmc : Continuous (fun t ↦ (m t).toAffineIsometry.toContinuousAffineMap) :=
    continuous_induced_dom.comp hm
  apply (ContinuousAffineMap.continuous_comp_right
    (m 0).symm.toAffineIsometry.toContinuousAffineMap).comp hmc |>.congr
  intro t
  rfl

/-- A canonical hallway motion is also a paper motion of the same set. -/
theorem IsMovingSofa.isPaperMotion {s : Set Point} {m : I → Point ≃ᵃⁱ[ℝ] Point}
    (h : IsMovingSofa s m) : IsPaperMotion s m := by
  refine ⟨h.isConnected, h.isClosed, h.continuous, ⟨0, ?_⟩,
    exists_motion_rotation m h.continuous h.zero, ?_, h.subset_hallway, h.final⟩
  · intro p
    simp [h.zero]
  · simpa [h.zero] using h.initial

theorem canonical_paper_motion_bridge :
    (∀ s : Set Point, IsPaperMovingSofa s →
      ∃ (q : Point) (m : I → Point ≃ᵃⁱ[ℝ] Point),
        IsMovingSofa ((fun p ↦ p + q) '' s) m ∧
        volume ((fun p ↦ p + q) '' s) = volume s) ∧
    (∀ (s : Set Point) (m : I → Point ≃ᵃⁱ[ℝ] Point),
      IsMovingSofa s m → IsPaperMovingSofa s) := by
  constructor
  · rintro s ⟨m, hsconn, hsclosed, hmcont, ⟨q, hq⟩, -, hini, hall, hfinal⟩
    refine ⟨q, normalizeMotion m, ?_, ?_⟩
    · refine
        { isConnected := hsconn.image _ (by fun_prop)
          isClosed := ?_
          continuous := continuous_normalizeMotion m hmcont
          zero := ?_
          initial := ?_
          subset_hallway := ?_
          final := ?_ }
      · change IsClosed ((AffineIsometryEquiv.vaddConst ℝ q) '' s)
        exact (AffineIsometryEquiv.vaddConst ℝ q).toHomeomorph.isClosedMap s hsclosed
      · ext x
        simp [normalizeMotion]
      · rintro _ ⟨x, hx, rfl⟩
        change x + q ∈ horizontalHallway
        rw [← hq x]
        exact hini ⟨x, hx, rfl⟩
      · intro t
        rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        change normalizeMotion m t (x + q) ∈ hallway
        rw [← hq x]
        exact hall t ⟨x, hx, by simp [normalizeMotion]⟩
      · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        change normalizeMotion m 1 (x + q) ∈ verticalHallway
        rw [← hq x]
        exact hfinal ⟨x, hx, by simp [normalizeMotion]⟩
    · have himage : (fun p ↦ p + q) '' s = (fun p ↦ p - q) ⁻¹' s := by
        ext p
        constructor
        · rintro ⟨x, hx, rfl⟩
          simpa using hx
        · intro hp
          exact ⟨p - q, hp, by simp⟩
      rw [himage, ← Measure.map_apply_of_aemeasurable (μ := volume)
        (f := fun p : Point ↦ p - q) (by fun_prop) hsclosed.measurableSet]
      have hmap : Measure.map (fun p : Point ↦ p - q) volume = volume := by
        simpa only [sub_eq_add_neg] using map_add_right_eq_self volume (-q)
      rw [hmap]
  · exact fun s m h ↦ ⟨m, h.isPaperMotion⟩

theorem canonical_motion_compactness (s : Set Point) (m : I → Point ≃ᵃⁱ[ℝ] Point)
    (h : IsMovingSofa s m) :
    IsCompact s ∧ MeasurableSet s ∧ volume s < ⊤ := by
  have hc : IsCompact s := Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨h.isClosed, h.isBounded⟩
  exact ⟨hc, hc.measurableSet, hc.measure_lt_top⟩

theorem real_area_le_iff_volume_le (s t : Set Point)
    (hfinS : volume s < ⊤) (hfinT : volume t < ⊤) :
    ClassicalResults.area s ≤ ClassicalResults.area t ↔ volume s ≤ volume t := by
  exact ENNReal.toReal_le_toReal hfinS.ne hfinT.ne

end MovingSofa

end

end

end
