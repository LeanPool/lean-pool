/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73LoopParameter

/-!
# The circle parameter from two arcs

For XII (7.3), Claim (1), page 262, split the old circuit into
the arc collapsed to the hub and its complementary arc. Traverse
the first arc and then the second. Each is injective and their
only common points are their ends, so this loop is injective on
the half-open unit interval and parameterizes the old circle.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface

private theorem crossing_parameters
    {S : Type*} [TopologicalSpace S] {p q : S}
    (α : Path p q) (β : Path q p) (hα : Function.Injective α) (hβ : Function.Injective β)
    (hcap : range α ∩ range β ⊆ {p, q}) {s t : unitInterval} (heq : α s = β t) :
    (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
  rcases hcap ⟨mem_range_self s, t, heq.symm⟩ with hp | hq
  · exact Or.inl ⟨hα (hp.trans α.source.symm), hβ ((heq.symm.trans hp).trans β.target.symm)⟩
  · exact Or.inr ⟨hα (hq.trans α.target.symm), hβ ((heq.symm.trans hq).trans β.source.symm)⟩

/-- The loop obtained by traversing two arcs with only their ends
in common is injective on its half-open parameter interval. This
provides the old embedded circle in XII (7.3), Claim (1). -/
theorem two_arc_loop_injOn
    {S : Type*} [TopologicalSpace S] {p q : S}
    (α : Path p q) (β : Path q p) (hα : Function.Injective α) (hβ : Function.Injective β)
    (hcap : range α ∩ range β ⊆ {p, q}) :
    InjOn (α.trans β) (Ico (0 : unitInterval) 1) := by
  intro s hs t ht heq
  have hs1 : s.val < 1 := hs.2
  have ht1 : t.val < 1 := ht.2
  by_cases hsHalf : s.val ≤ 1 / 2
  · by_cases htHalf : t.val ≤ 1 / 2
    · rw [Path.trans_apply, Path.trans_apply, dite_eq_left hsHalf, dite_eq_left htHalf] at heq
      have hh := congrArg Subtype.val (hα heq)
      apply Subtype.ext
      change 2 * s.val = 2 * t.val at hh
      linarith
    · rw [Path.trans_apply, Path.trans_apply, dite_eq_left hsHalf, dite_eq_right htHalf] at heq
      rcases crossing_parameters α β hα hβ hcap heq with ⟨h₀, h₁⟩ | ⟨h₁, h₀⟩
      · have hh := congrArg Subtype.val h₁
        change 2 * t.val - 1 = 1 at hh
        linarith
      · have hh := congrArg Subtype.val h₀
        change 2 * t.val - 1 = 0 at hh
        linarith
  · by_cases htHalf : t.val ≤ 1 / 2
    · rw [Path.trans_apply, Path.trans_apply, dite_eq_right hsHalf, dite_eq_left htHalf] at heq
      rcases crossing_parameters α β hα hβ hcap heq.symm with ⟨h₀, h₁⟩ | ⟨h₁, h₀⟩
      · have hh := congrArg Subtype.val h₁
        change 2 * s.val - 1 = 1 at hh
        linarith
      · have hh := congrArg Subtype.val h₀
        change 2 * s.val - 1 = 0 at hh
        linarith
    · rw [Path.trans_apply, Path.trans_apply, dite_eq_right hsHalf, dite_eq_right htHalf] at heq
      have hh := congrArg Subtype.val (hβ heq)
      apply Subtype.ext
      change 2 * s.val - 1 = 2 * t.val - 1 at hh
      linarith

end GraphMinor.GM12
