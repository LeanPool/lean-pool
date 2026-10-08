/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselLinearLocalMap

/-!
# Concatenation of complete Sobolev trajectories

Two continuous trajectories with matching endpoint values form one
continuous trajectory on the sum of their time intervals.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform Topology

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- Join two complete Sobolev paths at a common endpoint. -/
@[expose]
def regularisedBesselAppendPath
    (k : ℕ) (T S : ℝ) (hT : 0 ≤ T) (hS : 0 ≤ S)
    (u : C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2))
    (v : C(RegularizedMildTimeInterval S,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2))
    (_hend : u ⟨T, hT, le_refl _⟩ = v ⟨0, le_refl _, hS⟩) :
    C(RegularizedMildTimeInterval (T + S),
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2) :=
  ⟨fun t => u (regularizedMildTimeClamp T hT t.1) +
      v (regularizedMildTimeClamp S hS (t.1 - T)) -
        u ⟨T, hT, le_refl _⟩,
    ((u.continuous.comp
      ((regularizedMildTimeClamp_continuous T hT).comp continuous_subtype_val)).add
      (v.continuous.comp
        ((regularizedMildTimeClamp_continuous S hS).comp
          (continuous_subtype_val.sub continuous_const)))).sub continuous_const⟩

/-- Before the joining time, the concatenated path equals the first path. -/
theorem regularisedBesselAppendPath_left
    (k : ℕ) (T S : ℝ) (hT : 0 ≤ T) (hS : 0 ≤ S)
    (u : C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2))
    (v : C(RegularizedMildTimeInterval S,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2))
    (hend : u ⟨T, hT, le_refl _⟩ = v ⟨0, le_refl _, hS⟩)
    (t : RegularizedMildTimeInterval (T + S)) (ht : t.1 ≤ T) :
    regularisedBesselAppendPath k T S hT hS u v hend t =
      u ⟨t.1, t.2.1, ht⟩ := by
  have hleft : regularizedMildTimeClamp T hT t.1 =
      ⟨t.1, t.2.1, ht⟩ :=
    regularizedMildTimeClamp_eq_of_mem T hT ⟨t.2.1, ht⟩
  have hright : regularizedMildTimeClamp S hS (t.1 - T) =
      ⟨0, le_refl _, hS⟩ := by
    apply Subtype.ext
    simp [regularizedMildTimeClamp, max_eq_left (sub_nonpos.mpr ht), hS]
  change u (regularizedMildTimeClamp T hT t.1) +
      v (regularizedMildTimeClamp S hS (t.1 - T)) -
        u ⟨T, hT, le_refl _⟩ = _
  rw [hleft, hright, ← hend]
  abel

/-- After the joining time, the concatenated path equals the translated
second path. -/
theorem regularisedBesselAppendPath_right
    (k : ℕ) (T S : ℝ) (hT : 0 ≤ T) (hS : 0 ≤ S)
    (u : C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2))
    (v : C(RegularizedMildTimeInterval S,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2))
    (hend : u ⟨T, hT, le_refl _⟩ = v ⟨0, le_refl _, hS⟩)
    (t : RegularizedMildTimeInterval (T + S)) (ht : T ≤ t.1) :
    regularisedBesselAppendPath k T S hT hS u v hend t =
      v ⟨t.1 - T, sub_nonneg.mpr ht,
        by linarith only [t.2.2]⟩ := by
  have hleft : regularizedMildTimeClamp T hT t.1 =
      ⟨T, hT, le_refl _⟩ := by
    apply Subtype.ext
    simp [regularizedMildTimeClamp, max_eq_right t.2.1, min_eq_left ht]
  have hright : regularizedMildTimeClamp S hS (t.1 - T) =
      ⟨t.1 - T, sub_nonneg.mpr ht, by linarith only [t.2.2]⟩ :=
    regularizedMildTimeClamp_eq_of_mem S hS
      ⟨sub_nonneg.mpr ht, by linarith only [t.2.2]⟩
  change u (regularizedMildTimeClamp T hT t.1) +
      v (regularizedMildTimeClamp S hS (t.1 - T)) -
        u ⟨T, hT, le_refl _⟩ = _
  rw [hleft, hright]
  abel

end CKN.Leray

end
