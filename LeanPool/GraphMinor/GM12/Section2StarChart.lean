/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
public import Mathlib.Analysis.Convex.Star
import Mathlib.Analysis.Convex.PathConnected

/-!
# Contracting star-convex chart patches

For the leaf-entry patch of XII, page 243, the slit coordinate ball
is star-convex at the restored leaf point. A chart carries its
straight-line contraction to the surface. A continuous chart inverse
lifts each loop, so the contraction stays inside the chosen patch.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface

/-- A chart image of a star-convex patch is simply connected. The
inverse conditions are needed only on that patch. -/
theorem image_starConvex_isSimplyConnected
    {S : Type*} [TopologicalSpace S] {j : S → ℂ} {g : ℂ → S} {A : Set ℂ} {q : ℂ}
    (hg : ContinuousOn g A) (hj : ContinuousOn j (g '' A))
    (hinv : ∀ z ∈ A, j (g z) = z) (hstar : StarConvex ℝ q A) (hq : q ∈ A) :
    IsSimplyConnectedSet (g '' A) := by
  refine ⟨(hstar.isPathConnected hq).image' hg, ?_⟩
  intro φ hφ
  have hθ : Continuous (fun z => j (φ z)) :=
    hj.comp_continuous φ.continuous (fun z => hφ (mem_range_self z))
  have hθA : ∀ z, j (φ z) ∈ A := by
    intro z
    obtain ⟨w, hw, he⟩ := hφ (mem_range_self z)
    rw [← he, hinv w hw]
    exact hw
  let κ : Circle × unitInterval → ℂ := fun z =>
    z.2.val • q + (1 - z.2.val) • j (φ z.1)
  have hκc : Continuous κ := by
    exact ((continuous_subtype_val.comp continuous_snd).smul continuous_const).add
      ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).smul
        (hθ.comp continuous_fst))
  have hκA : ∀ z, κ z ∈ A := fun z => hstar (hθA z.1)
    z.2.property.1 (sub_nonneg.mpr z.2.property.2) (by ring)
  let H : C(Circle × unitInterval, S) :=
    ⟨fun z => g (κ z), hg.comp_continuous hκc hκA⟩
  refine ⟨g q, mem_image_of_mem g hq, H, fun z => mem_image_of_mem g (hκA z), ?_, ?_⟩
  · intro z
    change g ((0 : ℝ) • q + (1 - (0 : ℝ)) • j (φ z)) = φ z
    simp only [sub_zero, one_smul, zero_smul, zero_add]
    obtain ⟨w, hw, he⟩ := hφ (mem_range_self z)
    rw [← he, hinv w hw]
  · intro z
    change g ((1 : ℝ) • q + (1 - (1 : ℝ)) • j (φ z)) = g q
    simp

end GraphMinor.GM12
