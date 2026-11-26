/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Defs
import LeanPool.GraphMinor.Surface.DiscMerge
import LeanPool.GraphMinor.Surface.DiscGrow
import LeanPool.GraphMinor.GM11.Walks

/-!
# A pendant line at an isolated target vertex

At the start of XII (4.3), page 249, an isolated target vertex
can first be given a pendant edge. Around an isolated point of a
closed set there is a chart avoiding all its other points. Draw a
short radial segment from the point in that chart. Its other end
is new, and its interior misses the closed set.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface Metric Complex

/-- A short line from an isolated point of a set meets that set
only at its initial end, as used in XII (4.3)'s target replacement. -/
theorem exists_line_at_isolated_point
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {B : Set S} {v : S} (hv : v ∈ B)
    (hclosed : IsClosed (B \ {v})) :
    ∃ (w : S) (L : Set S), IsLineWithEnds L v w ∧ w ∉ B ∧ L ∩ B = {v} := by
  have hvO : v ∈ (B \ {v})ᶜ := by simp
  obtain ⟨U, h, g, c, hUO, hg0⟩ := (hS.2.2 v).exists_ballChart hclosed.isOpen_compl hvO
    (R := 1) (by norm_num)
  let z : unitInterval → ℂ := fun t => ((t.val / 2 : ℝ) : ℂ)
  have hzc : Continuous z := continuous_ofReal.comp (continuous_subtype_val.div_const 2)
  have hz : ∀ t, z t ∈ ball (0 : ℂ) 1 := by
    intro t
    rw [mem_ball_zero_iff]
    change ‖((t.val / 2 : ℝ) : ℂ)‖ < 1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg t.property.1 (by norm_num))]
    linarith [t.property.2]
  let a : unitInterval → S := fun t => g (z t)
  have hac : Continuous a := c.gc.comp_continuous hzc hz
  have hai : Function.Injective a := by
    intro s t heq
    have heq' := congrArg h heq
    change h (g (z s)) = h (g (z t)) at heq'
    rw [c.hg (hz s), c.hg (hz t)] at heq'
    have hr := congrArg Complex.re heq'
    change s.val / 2 = t.val / 2 at hr
    apply Subtype.ext
    linarith
  have ha0 : a 0 = v := by simpa only [a, z, Icc.coe_zero, zero_div, ofReal_zero] using hg0
  have haO : ∀ t, a t ∈ (B \ {v})ᶜ := fun t => hUO (c.gm (hz t))
  have hmeet : range a ∩ B = {v} := by
    apply Set.Subset.antisymm
    · rintro x ⟨⟨t, rfl⟩, hxB⟩
      by_contra hxv
      exact haO t ⟨hxB, hxv⟩
    · intro x hx
      have hxv := Set.mem_singleton_iff.mp hx
      exact hxv ▸ ⟨⟨0, ha0⟩, hv⟩
  have ha1B : a 1 ∉ B := by
    intro hB
    have heq : a 1 = a 0 := (Set.mem_singleton_iff.mp (hmeet.subset ⟨mem_range_self 1, hB⟩)).trans
      ha0.symm
    exact (show (1 : unitInterval) ≠ 0 by norm_num) (hai heq)
  refine ⟨a 1, range a, ?_, ha1B, hmeet⟩
  simpa only [ha0] using (IsArcMap.isLineWithEnds ⟨hac, hai⟩)

/-- Removing an isolated drawing vertex leaves a closed point set. -/
theorem isClosed_U_sdiff_of_isolated_vertex
    {S : Type*} [TopologicalSpace S] [T2Space S] {Γ : Drawing S} {v : S}
    (hoff : ∀ e ∈ Γ.E, v ∉ closure e) : IsClosed (Γ.U \ {v}) := by
  have heq : Γ.U \ {v} = (Γ.V \ {v}) ∪ ⋃ e ∈ Γ.E, closure e := by
    ext x
    constructor
    · rintro ⟨hxU, hxv⟩
      rw [Γ.U_eq] at hxU
      rcases hxU with hxV | hxE
      · exact Or.inl ⟨hxV, hxv⟩
      · exact Or.inr hxE
    · rintro (hx | hx)
      · exact ⟨Γ.V_subset_U hx.1, hx.2⟩
      · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
        refine ⟨Γ.closure_subset_U he hxe, ?_⟩
        intro hxv
        have hxv' := Set.mem_singleton_iff.mp hxv
        exact hoff e he (hxv' ▸ hxe)
  rw [heq]
  exact (Γ.finite_V.subset sdiff_subset).isClosed.union
    (Γ.finite_edges.isClosed_biUnion fun _ _ => isClosed_closure)

end GraphMinor.GM12
