/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
public import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.PathConnected

/-!
# Simply connected convex chart patches

The local rerouting in the circle-intersection step used by XII (3.1),
page 245, must preserve the homotopy in the surface. A convex part of
a chart is simply connected after mapping back. Lift each loop with
the chart inverse and contract it by straight segments to one point.
This works for half-plane charts as well as interior charts.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface

/-- A convex patch mapped by a chart with continuous inverse is
simply connected. The stated inverse condition is needed only on the
chosen convex patch. -/
theorem image_convex_isSimplyConnected
    {S : Type*} [TopologicalSpace S] {j : S → ℂ} {g : ℂ → S} {A : Set ℂ}
    (hg : ContinuousOn g A) (hj : ContinuousOn j (g '' A))
    (hinv : ∀ z ∈ A, j (g z) = z) (hconvex : Convex ℝ A) {q : ℂ} (hq : q ∈ A) :
    IsSimplyConnectedSet (g '' A) := by
  refine ⟨(hconvex.isPathConnected ⟨q, hq⟩).image' hg, ?_⟩
  intro φ hφ
  have hθ : Continuous (fun z => j (φ z)) :=
    hj.comp_continuous φ.continuous (fun z => hφ (mem_range_self z))
  have hθA : ∀ z, j (φ z) ∈ A := by
    intro z
    obtain ⟨w, hw, he⟩ := hφ (mem_range_self z)
    rw [← he, hinv w hw]
    exact hw
  let κ : Circle × unitInterval → ℂ := fun z =>
    (1 - z.2.val) • j (φ z.1) + z.2.val • q
  have hκc : Continuous κ := by
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).smul
      (hθ.comp continuous_fst)).add
      ((continuous_subtype_val.comp continuous_snd).smul continuous_const)
  have hκA : ∀ z, κ z ∈ A := fun z => hconvex (hθA z.1) hq
    (sub_nonneg.mpr z.2.property.2) z.2.property.1 (by ring)
  let H : C(Circle × unitInterval, S) :=
    ⟨fun z => g (κ z), hg.comp_continuous hκc hκA⟩
  refine ⟨g q, mem_image_of_mem g hq, H, fun z => mem_image_of_mem g (hκA z), ?_, ?_⟩
  · intro z
    change g ((1 - (0 : ℝ)) • j (φ z) + (0 : ℝ) • q) = φ z
    simp only [sub_zero, one_smul, zero_smul, add_zero]
    obtain ⟨w, hw, he⟩ := hφ (mem_range_self z)
    rw [← he, hinv w hw]
  · intro z
    change g ((1 - (1 : ℝ)) • j (φ z) + (1 : ℝ) • q) = g q
    simp

end GraphMinor.GM12
