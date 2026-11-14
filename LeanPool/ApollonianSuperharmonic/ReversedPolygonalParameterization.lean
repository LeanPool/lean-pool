/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P3723T1PolygonalParameterization
public import Mathlib.Tactic.Ring

/-!
# Reversing a polygonal parameterization

Adapted from Wesley Pegden's Apache-2.0 Trellis formalization.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/-- Reverse the subdivision and affine pieces along parameter reflection. -/
noncomputable abbrev reversedPolygonalParameterization
    (g : Set.Icc (0 : ℝ) 1 → ℝ × ℝ) (s : P3723T1PolygonalParameterization g)
    (flipHomeo : Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1)
    (flipHomeo_apply : ∀ t, (flipHomeo t : ℝ) = 1 - (t : ℝ)) :
    P3723T1PolygonalParameterization (fun t => g (flipHomeo t)) := by
  refine ⟨s.count, s.positive, fun i => 1 - s.time i.rev, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    have hrev : j.rev < i.rev := by
      have := (Fin.rev_lt_iff (i := j) (j := i.rev)).2 (by simpa using hij)
      simpa using this
    exact sub_lt_sub_left (s.strict hrev) 1
  · simp [Fin.rev_zero, s.finish]
  · simp [Fin.rev_last, s.start]
  · intro i
    let j : Fin s.count := i.rev
    obtain ⟨A, B, hA⟩ := s.affine_on j
    refine ⟨A + B, -B, ?_⟩
    intro t hlow hupp
    have hlow' : s.time j.castSucc ≤ 1 - (t : Real) := by
      have hj : j.castSucc = i.succ.rev := by
        apply Fin.ext
        simp [j, Fin.rev_succ]
      rw [hj]
      exact (le_sub_iff_add_le).2 (by
        simpa [add_comm] using (le_sub_iff_add_le).1 hupp)
    have hupp' : 1 - (t : Real) ≤ s.time j.succ := by
      have hj : j.succ = i.castSucc.rev := by
        apply Fin.ext
        simp [j, Fin.rev_castSucc]
      rw [hj]
      exact (sub_le_iff_le_add).2 (by
        simpa [add_comm] using (sub_le_iff_le_add).1 hlow)
    let u : Set.Icc (0 : Real) 1 := ⟨1 - (t : Real), ⟨sub_nonneg.mpr t.2.2, sub_le_self 1
        t.2.1⟩⟩
    have hseg' := hA u hlow' hupp'
    change g (flipHomeo t) = _
    have hu' : u = flipHomeo t := by
      apply Subtype.ext
      exact (flipHomeo_apply t).symm
    rw [hu'] at hseg'
    rw [hseg', flipHomeo_apply]
    apply Prod.ext
    · change A.1 + (1 - (t : Real)) * B.1 = A.1 + B.1 + (t : Real) * (-B.1)
      ring
    · change A.2 + (1 - (t : Real)) * B.2 = A.2 + B.2 + (t : Real) * (-B.2)
      ring

end ApollonianSuperharmonic

end
