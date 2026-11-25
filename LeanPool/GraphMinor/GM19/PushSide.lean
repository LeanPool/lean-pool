/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.PushOff

/-!
# Pushing a closed set off a disc across its boundary

Here is a form of `GraphMinor.Surface.push_off` for a disc `D` and a line `L` in the boundary of
`D`, with
the same local construction. A closed set that meets `L` only in its ends moves off `D`.
The fixed set `Z` meets `D` only in `L`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology Metric Filter GraphMinor.Surface

universe u

theorem push_off_side {S : Type u} [TopologicalSpace S] (hS : IsSurface S) {ι : Type} [Finite ι]
    {N Z : Set S} {D L : ι → Set S} (hN : N.Finite) (hZ : IsClosed Z) (hD : ∀ i, IsClosedDisc (D i))
    (hL : ∀ i, ∃ a b, IsLineWithEnds (L i) a b ∧ D i ∩ N = {a, b} ∧ L i ⊆ discBd (D i) ∧
      D i ∩ bd S ⊆ N)
    (hDD : ∀ i j, i ≠ j → D i ∩ D j ⊆ N) (hDZ : ∀ i, D i ∩ Z ⊆ L i)
    {F : Set S} (hF : IsOArc F) (hFZ : F ∩ Z ⊆ N) (hFL : ∀ i, F ∩ L i ⊆ N) :
    ∃ h : S ≃ₜ S, (∀ n ∈ N, h n = n) ∧ (h '' F) ∩ Z ⊆ N ∧ ∀ i, (h '' F) ∩ D i ⊆ N := by
  refine push_off_discs hS hN hZ hD ?_ hDD hF hFZ hFL
  intro i
  obtain ⟨a, b, hLi, hDN, hLb, hbdN⟩ := hL i
  have haL : a ∈ L i := by
    obtain ⟨f, h0, _⟩ := hLi
    exact h0 ▸ (f 0).2
  have hbL : b ∈ L i := by
    obtain ⟨f, _, h1⟩ := hLi
    exact h1 ▸ (f 1).2
  have hNL : D i ∩ N ⊆ L i := by
    rw [hDN]
    rintro _ (rfl | rfl)
    · exact haL
    · exact hbL
  exact ⟨a, b, hLi, hDN, hLb haL, hLb hbL, hLb.trans (discBd_subset _),
    .inr ⟨hLb, fun y hy => hNL ⟨hy.1, hbdN hy⟩, hDZ i⟩⟩

end GraphMinor.GM19
