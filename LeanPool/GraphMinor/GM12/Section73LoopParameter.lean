/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Section3
import Mathlib.Topology.Separation.Hausdorff

/-!
# Parameterizing the circle after collapsing an arc

For XII (7.3), Claim (1), page 262, the part of the old circuit
outside the collapsed arc becomes a loop whose only repeated
point is its pair of ends. Factoring through the usual interval
parameter of the circle gives an embedded circle. Reading the
loop on a half-open interval proves injectivity directly.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- A loop injective on its half-open parameter interval induces
an embedded parameterization of its image circle. This is the
parameterization used after the arc collapse in XII (7.3),
Claim (1), page 262. -/
theorem exists_embedded_circle_of_loop
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (m : C(unitInterval, S)) (h01 : m 0 = m 1)
    (hinj : InjOn m (Ico (0 : unitInterval) 1)) :
    ∃ φ : C(Circle, S), IsEmbedding φ ∧ range φ = range m ∧
      ∀ t, φ (arcParam 1 t) = m t := by
  let φ := loopLift 1 m h01
  have hpar : ∀ z : Circle, ∃ t ∈ Ico (0 : unitInterval) 1, arcParam 1 t = z := by
    intro z
    obtain ⟨t, rfl⟩ := arcParam_surjective 1 z
    by_cases ht : t = 1
    · subst t
      exact ⟨0, ⟨le_rfl, by norm_num⟩, by rw [arcParam_zero, arcParam_one]⟩
    · exact ⟨t, ⟨unitInterval.nonneg t, unitInterval.lt_one_iff_ne_one.mpr ht⟩, rfl⟩
  have hφinj : Function.Injective φ := by
    intro z w hzw
    obtain ⟨s, hs, rfl⟩ := hpar z
    obtain ⟨t, ht, rfl⟩ := hpar w
    have hst : m s = m t := by
      change loopLift 1 m h01 (arcParam 1 s) = loopLift 1 m h01 (arcParam 1 t) at hzw
      simpa only [loopLift_apply] using hzw
    exact congrArg (arcParam 1) (hinj hs ht hst)
  refine ⟨φ, (φ.continuous.isClosedEmbedding hφinj).isEmbedding, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨t, rfl⟩ := arcParam_surjective 1 z
      exact ⟨t, (loopLift_apply 1 m h01 t).symm⟩
    · rintro ⟨t, rfl⟩
      exact ⟨arcParam 1 t, loopLift_apply 1 m h01 t⟩
  · exact loopLift_apply 1 m h01

end GraphMinor.GM12
