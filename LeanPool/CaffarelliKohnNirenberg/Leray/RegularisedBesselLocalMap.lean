/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselShiftedStokesNorm
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselLocalParameterBounds
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselHeatSemigroup

/-!
# The local complete Sobolev mild map

Heat evolution and the translated nonlinear Stokes integral define a
continuous complete H²ᵏ trajectory on every closed local interval.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform Topology

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- The complete Sobolev mild map on a closed local time interval. -/
@[expose]
def regularisedBesselLocalMap
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (k : ℕ)
    (b : BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2)
    (T : ℝ) (hT : 0 ≤ T)
    (u : C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2)) :
    C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2) := by
  let F := regularisedBesselClampedTensorPath ρ ε hε k T hT u
  let C := regularisedBesselTensorConstant ρ ε hε k * ‖u‖ ^ 2
  have hFcont : Continuous F :=
    regularisedBesselClampedTensorPath_continuous ρ ε hε k T hT u
  have hu : ∀ t, ‖u t‖ ≤ ‖u‖ := fun t => u.norm_coe_le_norm t
  have hFC : ∀ s, ‖F s‖ ≤ C := by
    intro s
    exact regularisedBesselClampedTensorPath_norm_le
      ρ ε hε k T hT u ‖u‖ (norm_nonneg _) hu s
  have hC : 0 ≤ C :=
    mul_nonneg (regularisedBesselTensorMap_norm_le ρ ε hε k).1
      (sq_nonneg ‖u‖)
  let nonnegativeTime : RegularizedMildTimeInterval T → {s : ℝ // 0 ≤ s} :=
    fun t => ⟨t, t.2.1⟩
  have hnonnegativeTime : Continuous nonnegativeTime :=
    continuous_subtype_val.subtype_mk fun t => t.2.1
  have hheat : Continuous
      (fun t : RegularizedMildTimeInterval T =>
        regularisedBesselHeat ((2 * k : ℕ) : ℝ) t.1 t.2.1 b) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hAt := (regularisedBesselHeat_continuousAt
      ((2 * k : ℕ) : ℝ) t.2.1 b).comp
        hnonnegativeTime.continuousAt
    change ContinuousAt
      (fun q => regularisedBesselHeat ((2 * k : ℕ) : ℝ)
        (nonnegativeTime q).1 (nonnegativeTime q).2 b) t
    exact hAt
  have hintegral : Continuous (fun t : RegularizedMildTimeInterval T =>
      ∫ τ in (0 : ℝ)..T,
        regularisedBesselShiftedStokesIntegrand k F t.1 τ) := by
    exact (regularisedBesselShiftedStokesIntegral_continuous
      k F hFcont C hFC hC T hT).comp continuous_subtype_val
  exact ⟨fun t =>
    regularisedBesselHeat ((2 * k : ℕ) : ℝ) t.1 t.2.1 b -
      ∫ τ in (0 : ℝ)..T,
        regularisedBesselShiftedStokesIntegrand k F t.1 τ,
    hheat.sub hintegral⟩

/-- Evaluation of the local complete Sobolev map is heat minus the
translated complete nonlinear Stokes integral. -/
theorem regularisedBesselLocalMap_apply
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (k : ℕ)
    (b : BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2)
    (T : ℝ) (hT : 0 ≤ T)
    (u : C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2))
    (t : RegularizedMildTimeInterval T) :
    regularisedBesselLocalMap ρ ε hε k b T hT u t =
      regularisedBesselHeat ((2 * k : ℕ) : ℝ) t.1 t.2.1 b -
        ∫ τ in (0 : ℝ)..T,
          regularisedBesselShiftedStokesIntegrand k
            (regularisedBesselClampedTensorPath ρ ε hε k T hT u) t.1 τ := rfl

end CKN.Leray

end
