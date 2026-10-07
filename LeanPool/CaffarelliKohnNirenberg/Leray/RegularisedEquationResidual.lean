/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Pointwise recovery from the space-time weak equation

A continuous residual that pairs to zero with every smooth compactly
supported scalar test vanishes at every interior positive-time point.
-/

public section

open MeasureTheory Set
open scoped Topology
open CKN
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

private theorem residual_test_eq_zero_of_not_tsupport
    {α : Type*} [TopologicalSpace α] {ψ : α → ℝ} {x : α}
    (hx : x ∉ tsupport ψ) : ψ x = 0 := by
  by_contra hne
  exact hx (subset_tsupport ψ (Function.mem_support.mpr hne))

/-- A continuous scalar residual with zero pairing against all smooth tests
supported inside `(0,T)` is pointwise zero there. -/
theorem regularised_continuousResidual_eq_zero_of_tests
    (T : ℝ) (R : Vec3 × ℝ → ℝ)
    (hRcont : ContinuousOn R
      ((Set.univ : Set Vec3) ×ˢ Set.Ioo 0 T))
    (hzero : ∀ ψ : Vec3 × ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ (Set.univ : Set Vec3) ×ˢ Set.Ioo 0 T →
      ∫ z in (Set.univ : Set Vec3) ×ˢ Set.Ioo 0 T,
        R z * ψ z = 0) :
    ∀ z : Vec3 × ℝ,
      z ∈ (Set.univ : Set Vec3) ×ˢ Set.Ioo 0 T → R z = 0 := by
  let S : Set (Vec3 × ℝ) := (Set.univ : Set Vec3) ×ˢ Set.Ioo 0 T
  have hSopen : IsOpen S := isOpen_univ.prod isOpen_Ioo
  have hSmeas : MeasurableSet S :=
    MeasurableSet.prod MeasurableSet.univ measurableSet_Ioo
  have hRloc : LocallyIntegrableOn R S (volume : Measure (Vec3 × ℝ)) :=
    hRcont.locallyIntegrableOn hSmeas
  have hzeroFull : ∀ ψ : Vec3 × ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ S →
      ∫ z : Vec3 × ℝ, ψ z * R z = 0 := by
    intro ψ hψ hψc hψs
    have hset : (∫ z : Vec3 × ℝ in S, ψ z * R z) =
        ∫ z : Vec3 × ℝ, ψ z * R z :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
        have hψz : ψ z = 0 := by
          apply residual_test_eq_zero_of_not_tsupport
          intro hzts
          exact hz (hψs hzts)
        simp [hψz]
    rw [← hset]
    have hzero' := hzero ψ hψ hψc (by
      intro z hz
      exact hψs hz)
    simpa [S, mul_comm] using hzero'
  have hae : ∀ᵐ z : Vec3 × ℝ ∂(volume : Measure (Vec3 × ℝ)),
      z ∈ S → R z = 0 := by
    apply hSopen.ae_eq_zero_of_integral_contDiff_smul_eq_zero hRloc
    intro ψ hψ hψc hψs
    simpa [smul_eq_mul] using hzeroFull ψ hψ hψc hψs
  have haeRestr : R =ᵐ[(volume : Measure (Vec3 × ℝ)).restrict S] 0 := by
    have hae' : ∀ᵐ z ∂((volume : Measure (Vec3 × ℝ)).restrict S),
        R z = 0 := (ae_restrict_iff' hSmeas).2 hae
    filter_upwards [hae'] with z hz
    exact hz
  have hEqOn := Measure.eqOn_open_of_ae_eq haeRestr hSopen hRcont continuousOn_const
  intro z hz
  have h := hEqOn hz
  simpa only [Pi.zero_apply] using h

end CKN.Leray

end
