/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.StrongSolution
public import LeanPool.CaffarelliKohnNirenberg.Witnesses.LerayHopfZero

/-!
# The zero field is a strong solution

The zero velocity, zero gradient and zero pressure satisfy the strong-solution
predicate of `prop:lps-local-strong` on every interval `[t₀,T]` with `t₀ < T`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The zero fields are a strong solution on every interval `[t₀,T]` with `t₀ < T`. -/
theorem isLpsStrongSolution_zero (t₀ T : ℝ) (h : t₀ < T) :
    IsLpsStrongSolution t₀ T (fun _ : ParabolicPoint => 0)
      (fun _ : ParabolicPoint => 0) (fun _ : ParabolicPoint => 0) := by
  have hzero : CKN.HasWeakGradientOn (Set.univ : Set Vec3) (fun _ : Vec3 => (0 : ℝ))
      (fun _ _ => 0) := by
    simpa using CKN.HasWeakGradientOn.of_contDiff (U := (Set.univ : Set Vec3))
      (f := fun _ : Vec3 => (0 : ℝ)) contDiff_const
  let zeroH1 : CKN.H1Function (Set.univ : Set Vec3) :=
    { toFun := fun _ => 0
      grad := fun _ _ => 0
      memL2 := by
        simp [CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn]
      gradMemL2 := by
        intro j
        simp [CKN.MemLpOn, CKN.volumeOn]
      hasWeakGradient := hzero }
  refine ⟨h, ?_, ?_, ?_, ?_, ?_⟩
  · intro t _
    exact ⟨isInJ_zero, fun i => ⟨zeroH1, rfl, rfl⟩⟩
  · intro t _
    simp only [sub_self]
    simp only [eLpNorm_fun_zero]
    exact ⟨tendsto_const_nhds, tendsto_const_nhds⟩
  · refine ⟨fun _ _ _ => 0, fun _ => 0, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · exact locallyIntegrableOn_zero
      · exact locallyIntegrableOn_zero
      · exact locallyIntegrableOn_zero
      · exact locallyIntegrableOn_zero
      · intro φ _
        refine ⟨fun i j => ?_, fun i j k => ?_, fun i => ?_⟩
        · simp only [Pi.zero_apply, zero_mul]
          simp
        · simp only [Pi.zero_apply, zero_mul]
          simp
        · simp only [Pi.zero_apply, zero_mul]
          simp
    all_goals exact MemLp.zero'
  · exact MemLp.zero'
  · intro φ _
    simp

end ESS
