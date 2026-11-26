/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3FiniteReroute
public import LeanPool.GraphMinor.GM12.Section3PathConcatenation

/-!
# The exact carrier of the global rerouting

For the circle-intersection step used by XII (3.1), page 245, the
rerouted path starts on the first circle. Its concatenation visits all
the retained outer pieces. After adjoining the first circle, the new
carrier is exactly the union of those finitely many original subpaths.
This equality lets the finite graph construction preserve connectedness
as well as the homotopy class.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- If the original path starts in the solid set, adjoining that set
to the rerouted path gives exactly the finite union of retained outer
subpaths, with singleton attachment bounds. -/
theorem exists_global_homotopic_reroute_carrier
    {S : Type*} [TopologicalSpace S] (hS : IsSurface S) {F : Set S}
    (hF : IsSolid F) {a b : S} (p : Path a b) (ha : a ∈ F) :
    ∃ (n : ℕ) (t : Fin (n + 1) → unitInterval) (s u : Fin n → unitInterval) (q : Path a b),
      t 0 = 0 ∧ t (Fin.last n) = 1 ∧ Monotone t ∧ p.Homotopic q ∧
      F ∪ range q = F ∪ ⋃ i : Fin n,
        (range ((p.subpath (t i.castSucc) (t i.succ)).subpath 0 (s i)) ∪
          range ((p.subpath (t i.castSucc) (t i.succ)).subpath (u i) 1)) ∧
      ∀ i : Fin n, s i ≤ u i ∧
        range ((p.subpath (t i.castSucc) (t i.succ)).subpath 0 (s i)) ∩ F ⊆
          {(p.subpath (t i.castSucc) (t i.succ)) (s i)} ∧
        range ((p.subpath (t i.castSucc) (t i.succ)).subpath (u i) 1) ∩ F ⊆
          {(p.subpath (t i.castSucc) (t i.succ)) (u i)} := by
  obtain ⟨n, t, s, u, r, ht0, htlast, hmono, hpieces⟩ := exists_finite_homotopic_reroutes hS hF p
  obtain ⟨q, hpq, hq⟩ := exists_homotopic_path_with_piecewise_range p t ht0 htlast r
    (fun i => (hpieces i).2.1)
  refine ⟨n, t, s, u, q, ht0, htlast, hmono, hpq, ?_,
    fun i => ⟨(hpieces i).1, (hpieces i).2.2.2.1, (hpieces i).2.2.2.2⟩⟩
  have hp0 : p 0 ∈ F := p.source.symm ▸ ha
  rw [hq]
  apply Subset.antisymm
  · rintro x (hxF | hx0 | hxr)
    · exact Or.inl hxF
    · exact Or.inl (mem_singleton_iff.mp hx0 ▸ hp0)
    · obtain ⟨i, hxi⟩ := mem_iUnion.mp hxr
      have hxparts := (hpieces i).2.2.1 ▸ (show x ∈ F ∪ range (r i) from Or.inr hxi)
      rcases hxparts with (hxF | hxL) | hxR
      · exact Or.inl hxF
      · exact Or.inr (mem_iUnion.mpr ⟨i, Or.inl hxL⟩)
      · exact Or.inr (mem_iUnion.mpr ⟨i, Or.inr hxR⟩)
  · rintro x (hxF | hxparts)
    · exact Or.inl hxF
    · obtain ⟨i, hxi⟩ := mem_iUnion.mp hxparts
      have hxlocal : x ∈ F ∪ range (r i) := (hpieces i).2.2.1.symm ▸
        (show x ∈ F ∪ range ((p.subpath (t i.castSucc) (t i.succ)).subpath 0 (s i)) ∪
          range ((p.subpath (t i.castSucc) (t i.succ)).subpath (u i) 1) from
          hxi.elim (fun h => Or.inl (Or.inr h)) Or.inr)
      rcases hxlocal with hxF | hxr
      · exact Or.inl hxF
      · exact Or.inr (Or.inr (mem_iUnion.mpr ⟨i, hxr⟩))

end GraphMinor.GM12
