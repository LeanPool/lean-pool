/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselLinearTensorPath
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselShiftedStokesIntegral
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselHeatSemigroup

/-!
# Linear complete Sobolev mild map with prescribed physical velocity

The fixed physical L² velocity enters the first tensor factor, while the
unknown complete Sobolev trajectory enters the second factor.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform Topology

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- The local complete Sobolev mild map linearized around a prescribed
physical L² trajectory. -/
@[expose]
def regularisedBesselLinearLocalMap
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (k : ℕ)
    (b : BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2)
    (T : ℝ) (hT : 0 ≤ T)
    (g : C(RegularizedMildTimeInterval T, ComplexVectorL2))
    (B : ℝ) (hB : 0 ≤ B) (hg : ∀ q, ‖g q‖ ≤ B)
    (v : C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2)) :
    C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2) := by
  let F := regularisedBesselLinearTensorPath ρ ε hε k T hT g v
  let C := regularisedBesselTensorConstant ρ ε hε k * B * ‖v‖
  have hFcont : Continuous F :=
    regularisedBesselLinearTensorPath_continuous ρ ε hε k T hT g v
  have hFC : ∀ s, ‖F s‖ ≤ C := by
    intro s
    exact regularisedBesselLinearTensorPath_norm_le
      ρ ε hε k T hT g v B hB hg s
  have hC : 0 ≤ C :=
    mul_nonneg
      (mul_nonneg (regularisedBesselTensorMap_norm_le ρ ε hε k).1 hB)
      (norm_nonneg v)
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

/-- Evaluation of the linear complete Sobolev mild map. -/
theorem regularisedBesselLinearLocalMap_apply
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (k : ℕ)
    (b : BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2)
    (T : ℝ) (hT : 0 ≤ T)
    (g : C(RegularizedMildTimeInterval T, ComplexVectorL2))
    (B : ℝ) (hB : 0 ≤ B) (hg : ∀ q, ‖g q‖ ≤ B)
    (v : C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2))
    (t : RegularizedMildTimeInterval T) :
    regularisedBesselLinearLocalMap ρ ε hε k b T hT g B hB hg v t =
      regularisedBesselHeat ((2 * k : ℕ) : ℝ) t.1 t.2.1 b -
        ∫ τ in (0 : ℝ)..T,
          regularisedBesselShiftedStokesIntegrand k
            (regularisedBesselLinearTensorPath ρ ε hε k T hT g v) t.1 τ := rfl

end CKN.Leray

end
