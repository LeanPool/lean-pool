/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3RerouteCover
public import LeanPool.GraphMinor.GM12.Section3RerouteContacts

/-!
# Finitely many homotopy-preserving reroutings

For the circle-intersection step used by XII (3.1), page 245, apply
the first/last-contact replacement on each member of a finite patch
partition. A piece missing the closed set is retained. Every new piece
is homotopic to the original one and, after adjoining the closed set,
its carrier consists of at most two original outer subpaths. Each
outer subpath meets the closed set only at its attachment endpoint.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- A path piece either misses the closed set or has a first/last
replacement. In both cases two outer subpaths describe the new carrier,
and their intersections with the set are confined to their ends. -/
theorem exists_homotopic_reroute_piece
    {S : Type*} [TopologicalSpace S] {F U V : Set S}
    (hF : IsClosed F) (hV : IsSimplyConnectedSet V) (hUV : U ⊆ V)
    (hFU : IsArcConnected (F ∩ U)) {a b : S} (p : Path a b) (hpU : range p ⊆ U) :
    ∃ (s t : unitInterval) (q : Path a b), s ≤ t ∧ p.Homotopic q ∧
      F ∪ range q = F ∪ range (p.subpath 0 s) ∪ range (p.subpath t 1) ∧
      range (p.subpath 0 s) ∩ F ⊆ {p s} ∧ range (p.subpath t 1) ∩ F ⊆ {p t} := by
  classical
  by_cases hmeet : (p ⁻¹' F).Nonempty
  · obtain ⟨s, t, q, hst, hh, heq, hl, hr⟩ :=
      exists_homotopic_reroute_with_outer_pieces hF hV hUV hFU p hpU hmeet
    exact ⟨s, t, q, hst, hh, heq, hl.le, hr.le⟩
  · refine ⟨1, 1, p, le_rfl, Path.Homotopic.refl p, ?_, ?_, ?_⟩
    · rw [Path.subpath_zero_one, Path.subpath_self, Path.refl_range]
      change F ∪ range p = F ∪ range p ∪ {p 1}
      have hsub : ({p 1} : Set S) ⊆ F ∪ range p :=
        singleton_subset_iff.mpr (Or.inr (mem_range_self 1))
      exact (Set.union_eq_left.mpr hsub).symm
    · rw [Path.subpath_zero_one]
      change range p ∩ F ⊆ {p 1}
      rintro x ⟨⟨r, rfl⟩, hrF⟩
      exact (hmeet ⟨r, hrF⟩).elim
    · rw [Path.subpath_self, Path.refl_range]
      exact inter_subset_left

/-- A finite partition of a path admits simultaneous local reroutings
with preserved homotopies and only finitely many retained outer
subpaths. No approximation leaves the original path union the solid set. -/
theorem exists_finite_homotopic_reroutes
    {S : Type*} [TopologicalSpace S] (hS : IsSurface S) {F : Set S}
    (hF : IsSolid F) {a b : S} (p : Path a b) :
    ∃ (n : ℕ) (t : Fin (n + 1) → unitInterval) (s u : Fin n → unitInterval)
      (q : ∀ i : Fin n, Path (p (t i.castSucc)) (p (t i.succ))),
      t 0 = 0 ∧ t (Fin.last n) = 1 ∧ Monotone t ∧ ∀ i : Fin n,
        s i ≤ u i ∧ (p.subpath (t i.castSucc) (t i.succ)).Homotopic (q i) ∧
        F ∪ range (q i) = F ∪ range ((p.subpath (t i.castSucc) (t i.succ)).subpath 0 (s i)) ∪
          range ((p.subpath (t i.castSucc) (t i.succ)).subpath (u i) 1) ∧
        range ((p.subpath (t i.castSucc) (t i.succ)).subpath 0 (s i)) ∩ F ⊆
          {(p.subpath (t i.castSucc) (t i.succ)) (s i)} ∧
        range ((p.subpath (t i.castSucc) (t i.succ)).subpath (u i) 1) ∩ F ⊆
          {(p.subpath (t i.castSucc) (t i.succ)) (u i)} := by
  classical
  obtain ⟨n, t, ht0, htlast, hmono, hpieces⟩ := exists_finite_reroute_partition hS hF p
  have hlocal : ∀ i : Fin n, ∃ (s u : unitInterval)
      (q : Path (p (t i.castSucc)) (p (t i.succ))),
      s ≤ u ∧ (p.subpath (t i.castSucc) (t i.succ)).Homotopic q ∧
      F ∪ range q = F ∪ range ((p.subpath (t i.castSucc) (t i.succ)).subpath 0 s) ∪
        range ((p.subpath (t i.castSucc) (t i.succ)).subpath u 1) ∧
      range ((p.subpath (t i.castSucc) (t i.succ)).subpath 0 s) ∩ F ⊆
        {(p.subpath (t i.castSucc) (t i.succ)) s} ∧
      range ((p.subpath (t i.castSucc) (t i.succ)).subpath u 1) ∩ F ⊆
        {(p.subpath (t i.castSucc) (t i.succ)) u} := by
    intro i
    obtain ⟨U, V, _, hUV, hsc, hArc, hpU⟩ := hpieces i
    exact exists_homotopic_reroute_piece hF.2 hsc hUV hArc _ hpU
  choose s u q hst hh heq hl hr using hlocal
  exact ⟨n, t, s, u, q, ht0, htlast, hmono, fun i => ⟨hst i, hh i, heq i, hl i, hr i⟩⟩

end GraphMinor.GM12
