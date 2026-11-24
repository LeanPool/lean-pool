/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.DiscArcs
public import Mathlib.Analysis.Convex.Star
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.PathConnected

/-!
# Contracting a sector at its boundary vertex

For the entry-edge existence argument on XII page 243, an incoming curve
must be compared inside one corner. In disc coordinates, the open disc
together with one boundary point is star-convex at that point. Intersecting
with a small ball preserves this property. A chart carries the resulting
contraction back to a simply-connected patch of the sector.
-/

public section

namespace GraphMinor.GM12

open Set Topology Metric Surface

/-- Adding one point of the closed unit disc to the open unit disc gives
a set star-convex at that point. A positive contribution from an interior
point puts the combination in the interior. -/
theorem starConvex_insert_unitBall {q : ℂ} (hq : q ∈ closedBall 0 1) :
    StarConvex ℝ q (insert q (ball (0 : ℂ) 1)) := by
  intro x hx a b ha hb hab
  rcases hx with rfl | hx
  · rw [← add_smul, hab, one_smul]
    exact mem_insert _ _
  · by_cases hb0 : b = 0
    · have ha1 : a = 1 := by linarith
      simp only [hb0, ha1, one_smul, zero_smul, add_zero]
      exact mem_insert _ _
    · apply Or.inr
      have hx' : x ∈ interior (closedBall (0 : ℂ) 1) := by
        rw [interior_closedBall (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]
        exact hx
      have h := (convex_closedBall (0 : ℂ) (1 : ℝ)).combo_self_interior_mem_interior
        hq hx' ha (lt_of_le_of_ne hb (Ne.symm hb0)) hab
      simpa only [interior_closedBall (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] using h

/-- A disc chart carries a star-convex subset of its coordinate disc to
a simply-connected set. Straight segments to the star centre contract
every loop, and lie in the same subset throughout. -/
theorem chart_image_starConvex_isSimplyConnected {S : Type*} [TopologicalSpace S]
    {D : Set S} {h : S → ℂ} {g : ℂ → S} (c : IsChart D h g)
    {A : Set ℂ} {q : ℂ} (hA : A ⊆ closedBall 0 1)
    (hstar : StarConvex ℝ q A) (hq : q ∈ A) : IsSimplyConnectedSet (g '' A) := by
  refine ⟨(hstar.isPathConnected hq).image' (c.gc.mono hA), ?_⟩
  intro φ hφ
  have hφD : ∀ z, φ z ∈ D := fun z => c.g_subset hA (hφ (mem_range_self z))
  have hθ : Continuous (fun z => h (φ z)) := c.hc.comp_continuous φ.continuous hφD
  have hθA : ∀ z, h (φ z) ∈ A := by
    intro z
    obtain ⟨x, hx, hxeq⟩ := hφ (mem_range_self z)
    rw [← hxeq, c.hg (hA hx)]
    exact hx
  let κ : Circle × unitInterval → ℂ := fun z => z.2.val • q + (1 - z.2.val) • h (φ z.1)
  have hκc : Continuous κ := by
    exact ((continuous_subtype_val.comp continuous_snd).smul continuous_const).add
      ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).smul
        (hθ.comp continuous_fst))
  have hκA : ∀ z, κ z ∈ A := fun z =>
    hstar (hθA z.1) z.2.property.1 (sub_nonneg.mpr z.2.property.2) (by ring)
  let Ψ : C(Circle × unitInterval, S) := ⟨fun z => g (κ z),
    c.gc.comp_continuous hκc (fun z => hA (hκA z))⟩
  refine ⟨g q, mem_image_of_mem g hq, Ψ,
    (fun z => mem_image_of_mem g (hκA z)), ?_, ?_⟩
  · intro z
    change g ((0 : ℝ) • q + (1 - 0) • h (φ z)) = φ z
    simp only [zero_smul, sub_zero, one_smul, zero_add]
    exact c.gh (hφD z)
  · intro z
    change g ((1 : ℝ) • q + (1 - 1) • h (φ z)) = g q
    simp

end GraphMinor.GM12
