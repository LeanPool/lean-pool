/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3ChordDichotomy
public import LeanPool.GraphMinor.GM12.Section3PathIntoCircle
public import LeanPool.GraphMinor.GM12.Section3PlanarHomotopicCircle
import LeanPool.GraphMinor.GM12.Section3PuncturedSurface
import LeanPool.GraphMinor.GM12.Section3PuncturedCuffs
import LeanPool.GraphMinor.GM11.RadialCorners

import LeanPool.GraphMinor.GM07.Section7
import LeanPool.GraphMinor.GM07.Bridge

/-!
# Schismatic extraction from meeting surrounding circles

The intersection step used by XII (3.1), page 245, follows the
unnumbered criterion in VII Section 8, page 241. Suppose that no
schismatic subset exists. Every complete chord of the second circle
is then planar together with the first circle after filling its cuff,
by the chord dichotomy. Finite complete-chord rerouting moves each of
the two arcs of the second circle into the first circle in that cap.
The second circle is null-homotopic there, so VII (5.1) makes it planar.
It would surround the first circle's cuff, contrary to cuff uniqueness.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

universe u

/-- Two circles surrounding distinct prescribed cuffs and meeting in
at least two points contain a schismatic subset. No finiteness or
connectedness assumption on their intersection is needed. -/
theorem exists_schismatic_subset_of_meeting_surrounding_circles
    {S : Type u} {ι : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [Finite ι]
    (hS : IsClosedSurface S) (Δ : ι → Set S) (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    (hcase : ¬ IsSphere S ∨ 3 ≤ Nat.card ι)
    {i j : ι} (hij : i ≠ j) {F A : Set (discComplement Δ)}
    (hF : IsOArc F) (hA : IsOArc A)
    (hsF : GM07.SurroundsCuff F (Subtype.val ⁻¹' discBd (Δ i)))
    (hsA : GM07.SurroundsCuff A (Subtype.val ⁻¹' discBd (Δ j)))
    {x y : discComplement Δ} (hx : x ∈ F ∩ A) (hy : y ∈ F ∩ A) (hxy : x ≠ y) :
    ∃ Y, Y ⊆ F ∪ A ∧ GM07.IsSchismatic Y := by
  classical
  by_contra hn
  have hno : ∀ Y, Y ⊆ F ∪ A → ¬ GM07.IsSchismatic Y := fun Y hY hs => hn ⟨Y, hY, hs⟩
  let : ConnectedSpace (discComplement Δ) :=
    Subtype.connectedSpace (discComplement_isConnected hS Δ hΔ hdisj)
  have hsurface := discComplement_isSurface hS Δ hΔ hdisj
  obtain ⟨T, tT, jcap, D, hcap⟩ := exists_cappedCuff hsurface hsF.1
  let := tT
  let : T2Space T := hcap.isSurface.2.1
  have hconnT : ConnectedSpace T := cappedCuff_connectedSpace hcap
  let J : C(discComplement Δ, T) := ⟨jcap, hcap.isEmbedding.continuous⟩
  have hJF : IsPlanar (jcap '' F) := hsF.2.1.2.2 T jcap D hcap
  obtain ⟨f, g, hfg, hf0, hf1, hfgA⟩ := hA.exists_arcs hx.2 hy.2 hxy
  let p : Path x y := {
    toFun := f
    continuous_toFun := hfg.arc_left.1
    source' := hf0
    target' := hf1 }
  let q : Path x y := {
    toFun := g
    continuous_toFun := hfg.arc_right.1
    source' := hfg.zero.trans hf0
    target' := hfg.one.trans hf1 }
  have hpA : range p ⊆ A := hfgA ▸ subset_union_left
  have hqA : range q ⊆ A := hfgA ▸ subset_union_right
  have hchord : ∀ (γ : Path x y), Function.Injective γ → range γ ⊆ A →
      ∀ l r : unitInterval, l < r → γ l ∈ F → γ r ∈ F →
      Disjoint (γ '' Ioo l r) F → IsPlanar (jcap '' (F ∪ γ '' Icc l r)) := by
    intro γ hγi hγA l r hlr hlF hrF hgap
    have hL : IsLineWithEnds (γ '' Icc l r) (γ l) (γ r) :=
      isLine_piece γ.continuous hγi hlr
    have huv : γ l ≠ γ r := fun he => hlr.ne (hγi he)
    have hLF : (γ '' Icc l r) ∩ F = {γ l, γ r} := by
      apply Subset.antisymm
      · rintro z ⟨⟨t, ht, rfl⟩, htF⟩
        by_cases htl : t = l
        · exact Or.inl (congrArg γ htl)
        · by_cases htr : t = r
          · exact Or.inr (congrArg γ htr)
          · exact (disjoint_left.mp hgap
              ⟨t, ⟨lt_of_le_of_ne ht.1 (Ne.symm htl), lt_of_le_of_ne ht.2 htr⟩, rfl⟩ htF).elim
      · rintro z (rfl | rfl)
        · exact ⟨hL.left_mem, hlF⟩
        · exact ⟨hL.right_mem, hrF⟩
    rcases schismatic_or_planarInCappedCuff_of_chord hS Δ hΔ hdisj hcase
        hF hL huv hLF hsF with ⟨Y, hY, hsY⟩ | hpC
    · have hLA : γ '' Icc l r ⊆ A := (image_subset_range _ _).trans hγA
      exact (hno Y (hY.trans (union_subset subset_union_left (hLA.trans subset_union_right)))
        hsY).elim
    · exact hpC.2.2 T jcap D hcap
  obtain ⟨r, hpr, hrF⟩ := exists_homotopic_path_in_circle_of_planar_chords
    hsurface hF p hfg.arc_left.2 hx.1 hy.1 J hcap.isEmbedding (hchord p hfg.arc_left.2 hpA)
  obtain ⟨s, hqs, hsF'⟩ := exists_homotopic_path_in_circle_of_planar_chords
    hsurface hF q hfg.arc_right.2 hx.1 hy.1 J hcap.isEmbedding (hchord q hfg.arc_right.2 hqA)
  have hPQ : IsTwoArcs (p.map J.continuous) (q.map J.continuous) := by
    refine ⟨⟨(p.map J.continuous).continuous, hcap.isEmbedding.injective.comp hfg.arc_left.2⟩,
      ⟨(q.map J.continuous).continuous, hcap.isEmbedding.injective.comp hfg.arc_right.2⟩,
      congrArg jcap hfg.zero, congrArg jcap hfg.one, ?_⟩
    intro a b he
    exact hfg.meet a b (hcap.isEmbedding.injective he)
  have hAeq : range (p.map J.continuous) ∪ range (q.map J.continuous) = jcap '' A := by
    change range (jcap ∘ p) ∪ range (jcap ∘ q) = _
    rw [range_comp, range_comp, ← image_union]
    exact congrArg (fun Z => jcap '' Z) hfgA
  have hnull := null_circle_of_homotopic_paths_in_planar_set
    (p.map J.continuous) (q.map J.continuous) r s hPQ hAeq hpr hqs
    (union_subset hrF hsF') hJF
  have hAo : IsOArc (jcap '' A) := by
    obtain ⟨e⟩ := hA
    exact ⟨e.trans (hcap.isEmbedding.homeomorphImage A)⟩
  have hproper : jcap '' A ≠ univ := by
    intro heq
    apply cappedCuff_range_ne_univ hcap
    apply Set.eq_univ_of_univ_subset
    rw [← heq]
    exact image_subset_range _ _
  have hplanA := planar_oArc_of_null hcap.isSurface hconnT hAo hproper hnull
  have hpAi := isPlanarInCappedCuff_of_one_cap hsurface hcap hplanA
  have hsAi : GM07.SurroundsCuff A (Subtype.val ⁻¹' discBd (Δ i)) := ⟨hsF.1, hpAi, hsA.2.2⟩
  exact hij (surrounding_cuff_index_unique hS Δ hΔ hdisj hcase hA hsAi hsA)

end GraphMinor.GM12
