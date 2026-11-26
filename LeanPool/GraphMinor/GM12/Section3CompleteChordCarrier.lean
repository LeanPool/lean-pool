/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3RerouteCarrier
public import LeanPool.GraphMinor.GM12.Section3ParameterGaps
import LeanPool.GraphMinor.GM12.Section3SubpathIntervals

/-!
# Retaining finitely many complete chords

For the circle extraction used by XII (3.1), page 245, the local
reroutings retain finitely many outer pieces of an injective path.
Extend each such piece to the complete gap at its partition endpoint.
Both ends of the original path lie on the solid set, so every gap has
two contact endpoints. The homotopic path therefore lies in the solid
set together with finitely many complete chords, whose interiors miss
that set.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- An injective path with both ends on a solid set is homotopic to a
path in that set together with finitely many complete original chords.
Degenerate chords are allowed and consist of contact points. -/
theorem exists_homotopic_path_in_finite_complete_chords
    {S : Type*} [TopologicalSpace S] (hS : IsSurface S) {F : Set S}
    (hF : IsSolid F) {a b : S} (p : Path a b) (hpi : Function.Injective p)
    (ha : a ∈ F) (hb : b ∈ F) :
    ∃ (n : ℕ) (l r : Fin n → unitInterval) (q : Path a b), p.Homotopic q ∧
      range q ⊆ F ∪ ⋃ i : Fin n, p '' Icc (l i) (r i) ∧
      ∀ i, l i ≤ r i ∧ p (l i) ∈ F ∧ p (r i) ∈ F ∧
        Disjoint (p '' Ioo (l i) (r i)) F := by
  classical
  obtain ⟨n, t, s, u, q, _, _, hmono, hpq, hcarrier, hpieces⟩ :=
    exists_global_homotopic_reroute_carrier hS hF p ha
  let K := p ⁻¹' F
  have hK : IsClosed K := hF.2.preimage p.continuous
  have h0 : (0 : unitInterval) ∈ K := by change p 0 ∈ F; rwa [p.source]
  have h1 : (1 : unitInterval) ∈ K := by change p 1 ∈ F; rwa [p.target]
  have hex : ∀ i : Fin (n + 1), ∃ l r,
      l ≤ t i ∧ t i ≤ r ∧ l ∈ K ∧ r ∈ K ∧ Disjoint (Ioo l r) K := by
    intro i
    obtain ⟨l, r, hl, hr, hlK, hrK, hgap, _⟩ := exists_parameter_gap_or_contact hK h0 h1 (t i)
    exact ⟨l, r, hl, hr, hlK, hrK, hgap⟩
  choose l r hlt htr hlK hrK hgap using hex
  refine ⟨n + 1, l, r, q, hpq, ?_, ?_⟩
  · intro x hx
    have hx' : x ∈ F ∪ range q := Or.inr hx
    rw [hcarrier] at hx'
    rcases hx' with hxF | hxparts
    · exact Or.inl hxF
    · obtain ⟨i, hxi⟩ := mem_iUnion.mp hxparts
      have hti : t i.castSucc ≤ t i.succ := hmono (Fin.castSucc_le_succ i)
      rcases hxi with hxleft | hxright
      · have hleq := range_left_outer_subpath p hti (s i)
        rw [hleq] at hxleft
        obtain ⟨z, hz, rfl⟩ := hxleft
        have hcontact : ∀ w ∈ Icc (t i.castSucc) (Icc.convexComb (t i.castSucc) (t i.succ) (s i)),
            w ∈ K → w = Icc.convexComb (t i.castSucc) (t i.succ) (s i) := by
          intro w hw hwK
          have hwleft : p w ∈ range ((p.subpath (t i.castSucc) (t i.succ)).subpath 0 (s i)) :=
            hleq.symm ▸ (show p w ∈ p '' Icc (t i.castSucc)
              (Icc.convexComb (t i.castSucc) (t i.succ) (s i)) from ⟨w, hw, rfl⟩)
          have he := mem_singleton_iff.mp ((hpieces i).2.1 ⟨hwleft, hwK⟩)
          exact hpi he
        rcases parameter_segment_subset_contacts_union_gap_left
            (hlt i.castSucc) (htr i.castSucc) (hrK i.castSucc) hcontact hz with hzK | hzgap
        · exact Or.inl hzK
        · exact Or.inr (mem_iUnion.mpr ⟨i.castSucc, z, hzgap, rfl⟩)
      · have hreq := range_right_outer_subpath p hti (u i)
        rw [hreq] at hxright
        obtain ⟨z, hz, rfl⟩ := hxright
        have hcontact : ∀ w ∈ Icc (Icc.convexComb (t i.castSucc) (t i.succ) (u i)) (t i.succ),
            w ∈ K → w = Icc.convexComb (t i.castSucc) (t i.succ) (u i) := by
          intro w hw hwK
          have hwright : p w ∈ range ((p.subpath (t i.castSucc) (t i.succ)).subpath (u i) 1) :=
            hreq.symm ▸ (show p w ∈ p '' Icc
              (Icc.convexComb (t i.castSucc) (t i.succ) (u i)) (t i.succ) from ⟨w, hw, rfl⟩)
          have he := mem_singleton_iff.mp ((hpieces i).2.2 ⟨hwright, hwK⟩)
          exact hpi he
        rcases parameter_segment_subset_contacts_union_gap_right
            (hlt i.succ) (htr i.succ) (hlK i.succ) hcontact hz with hzK | hzgap
        · exact Or.inl hzK
        · exact Or.inr (mem_iUnion.mpr ⟨i.succ, z, hzgap, rfl⟩)
  · intro i
    refine ⟨(hlt i).trans (htr i), hlK i, hrK i, disjoint_left.mpr ?_⟩
    rintro x ⟨z, hz, rfl⟩ hzF
    exact disjoint_left.mp (hgap i) hz hzF

end GraphMinor.GM12
