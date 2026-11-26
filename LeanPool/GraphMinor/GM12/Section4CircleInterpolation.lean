/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.CircleMove
public import Mathlib.Analysis.Complex.Circle
import LeanPool.GraphMinor.Surface.PushOff

/-!
# Matching three marked positions on a circle

The four boundary marks in XII (4.5), claim (1), page 253, must
keep their cyclic order. Fix one mark and write the other three
at increasing positions between zero and one. Move the last mark
first, then the middle, then the first. Each piecewise linear tent
map fixes the marks already placed. Their composite is increasing,
fixes zero and one, and hence induces the required orientation
preserving circle homeomorphism.
-/

public section

namespace GraphMinor.GM12

open Set Surface

private theorem tentMap_strictMono {a l w t : ℝ}
    (hal : a < l) (hlt : l < t) (haw : a < w) (hwt : w < t) :
    StrictMono (tentMap a l w t) := by
  have hc : Continuous (tentMap a l w t) := by unfold tentMap tent; fun_prop
  have hi : Function.Injective (tentMap a l w t) :=
    Function.LeftInverse.injective (g := tentMap a w l t)
      (fun r => tentMap_inv hal hlt haw hwt)
  have ha : tentMap a l w t a = a := by rw [tentMap, tent_low hal hlt le_rfl]; ring
  have ht : tentMap a l w t t = t := by rw [tentMap, tent_high hal hlt le_rfl]; ring
  rcases hc.strictMono_of_inj hi with hm | hm
  · exact hm
  · have h := hm (hal.trans hlt)
    rw [ha, ht] at h
    exact False.elim (not_lt_of_ge (hal.trans hlt).le h)

private theorem tentMap_fixed_left {a l w t x : ℝ}
    (hal : a < l) (hlt : l < t) (hx : x ≤ a) : tentMap a l w t x = x := by
  rw [tentMap, tent_low hal hlt hx, mul_zero, add_zero]

private theorem tentMap_fixed_right {a l w t x : ℝ}
    (hal : a < l) (hlt : l < t) (hx : t ≤ x) : tentMap a l w t x = x := by
  rw [tentMap, tent_high hal hlt hx, mul_zero, add_zero]

private theorem tentMap_pivot {a l w t : ℝ}
    (hal : a < l) (hlt : l < t) : tentMap a l w t l = w := by
  rw [tentMap, tent_left hal hlt hal.le le_rfl, div_self (sub_pos.mpr hal).ne', mul_one]
  ring

/-- Match two increasing triples inside the unit interval by a
continuous strictly increasing map fixing both ends. -/
theorem exists_three_point_interpolation
    {a b c a' b' c' : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c) (hc : c < 1)
    (ha' : 0 < a') (hab' : a' < b') (hbc' : b' < c') (hc' : c' < 1) :
    ∃ τ : ℝ → ℝ, Continuous τ ∧ StrictMono τ ∧ τ 0 = 0 ∧ τ 1 = 1 ∧
      τ a = a' ∧ τ b = b' ∧ τ c = c' := by
  let f₃ := tentMap 0 c c' 1
  have h₃m : StrictMono f₃ := tentMap_strictMono (ha.trans (hab.trans hbc)) hc
    (ha'.trans (hab'.trans hbc')) hc'
  have h₃c : Continuous f₃ := by unfold f₃ tentMap tent; fun_prop
  have h₃0 : f₃ 0 = 0 := tentMap_fixed_left (ha.trans (hab.trans hbc)) hc le_rfl
  have h₃1 : f₃ 1 = 1 := tentMap_fixed_right (ha.trans (hab.trans hbc)) hc le_rfl
  have h₃c' : f₃ c = c' := tentMap_pivot (ha.trans (hab.trans hbc)) hc
  let b₃ := f₃ b
  have hb₃ : 0 < b₃ := by have h := h₃m (ha.trans hab); rwa [h₃0] at h
  have hb₃c : b₃ < c' := by have h := h₃m hbc; rwa [h₃c'] at h
  let f₂ := tentMap 0 b₃ b' c'
  have h₂m : StrictMono f₂ := tentMap_strictMono hb₃ hb₃c (ha'.trans hab') hbc'
  have h₂c : Continuous f₂ := by unfold f₂ tentMap tent; fun_prop
  have h₂0 : f₂ 0 = 0 := tentMap_fixed_left hb₃ hb₃c le_rfl
  have h₂1 : f₂ 1 = 1 := tentMap_fixed_right hb₃ hb₃c hc'.le
  have h₂c' : f₂ c' = c' := tentMap_fixed_right hb₃ hb₃c le_rfl
  have h₂b' : f₂ b₃ = b' := tentMap_pivot hb₃ hb₃c
  let a₂ := f₂ (f₃ a)
  have ha₂ : 0 < a₂ := by
    have h₁ : 0 < f₃ a := by have h := h₃m ha; rwa [h₃0] at h
    have h := h₂m h₁
    rwa [h₂0] at h
  have ha₂b : a₂ < b' := by
    have h := h₂m (h₃m hab)
    rwa [h₂b'] at h
  let f₁ := tentMap 0 a₂ a' b'
  have h₁m : StrictMono f₁ := tentMap_strictMono ha₂ ha₂b ha' hab'
  have h₁c : Continuous f₁ := by unfold f₁ tentMap tent; fun_prop
  have h₁0 : f₁ 0 = 0 := tentMap_fixed_left ha₂ ha₂b le_rfl
  have h₁1 : f₁ 1 = 1 := tentMap_fixed_right ha₂ ha₂b (hbc'.trans hc').le
  have h₁b' : f₁ b' = b' := tentMap_fixed_right ha₂ ha₂b le_rfl
  have h₁c' : f₁ c' = c' := tentMap_fixed_right ha₂ ha₂b hbc'.le
  refine ⟨fun x => f₁ (f₂ (f₃ x)), h₁c.comp (h₂c.comp h₃c), h₁m.comp (h₂m.comp h₃m),
    ?_, ?_, ?_, ?_, ?_⟩
  · change f₁ (f₂ (f₃ 0)) = 0
    rw [h₃0, h₂0, h₁0]
  · change f₁ (f₂ (f₃ 1)) = 1
    rw [h₃1, h₂1, h₁1]
  · exact tentMap_pivot ha₂ ha₂b
  · change f₁ (f₂ b₃) = b'
    rw [h₂b', h₁b']
  · change f₁ (f₂ (f₃ c)) = c'
    rw [h₃c', h₂c', h₁c']

/-- Fix the circle point at zero and match three further cyclically
ordered marks. This is the local boundary adjustment in XII (4.5). -/
theorem exists_circle_three_point_move
    {a b c a' b' c' : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c) (hc : c < 1)
    (ha' : 0 < a') (hab' : a' < b') (hbc' : b' < c') (hc' : c' < 1) :
    ∃ h : Circle ≃ₜ Circle, PreservesCircleOrientation h ∧ h 1 = 1 ∧
      h (ee a) = ee a' ∧ h (ee b) = ee b' ∧ h (ee c) = ee c' := by
  obtain ⟨τ, hτc, hτm, hτ0, hτ1, hτa, hτb, hτc'⟩ :=
    exists_three_point_interpolation ha hab hbc hc ha' hab' hbc' hc'
  obtain ⟨h, ho, hh⟩ := exists_circle_homeo hτc.continuousOn (hτm.strictMonoOn _)
    (by rw [hτ0, hτ1]; norm_num)
  refine ⟨h, ho, ?_, ?_, ?_, ?_⟩
  · have h0 := hh 0 ⟨le_rfl, zero_le_one⟩
    rw [hτ0] at h0
    simpa [ee] using h0
  · rw [hh a ⟨ha.le, (hab.trans (hbc.trans hc)).le⟩, hτa]
  · rw [hh b ⟨(ha.trans hab).le, (hbc.trans hc).le⟩, hτb]
  · rw [hh c ⟨(ha.trans (hab.trans hbc)).le, hc.le⟩, hτc']

end GraphMinor.GM12
