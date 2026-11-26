/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4UnitDiscContacts
import LeanPool.GraphMinor.Surface.DiscPolygon
import LeanPool.GraphMinor.Surface.DiscArcs

/-!
# Shrinking a disc while retaining its marked parameters

For XII (4.5), page 253, replace a region closure by a smaller
disc touching its boundary only at four prescribed vertices.
Extend the given boundary parametrization to a chart of the
disc, carry the marks to the unit circle, and use the convex
contact disc there. Its radial parametrization fixes the
marks. Carrying it back retains their original parameters,
so their order is available for the four-marked disc match.
-/

public section

namespace GraphMinor.GM12

open Set Surface Metric

/-- A finite nonempty boundary contact set can be realized by
a smaller disc whose boundary parametrization agrees with the
original one at every contact. This prepares the ordered target
discs for XII (4.5), page 253. -/
theorem exists_contact_disc_preserving_param {S : Type} [TopologicalSpace S]
    {D N : Set S} (hD : IsClosedDisc D) (φ : Circle ≃ₜ discBd D)
    (hN : N ⊆ discBd D) (hfin : N.Finite) (hne : N.Nonempty) :
    ∃ (Q : Set S) (p : Circle → S), IsClosedDisc Q ∧ Q ⊆ D ∧ Q ∩ discBd D = N ∧
      N ⊆ discBd Q ∧ Continuous p ∧ Function.Injective p ∧ range p = discBd Q ∧
      ∀ w, (φ w).val ∈ N → p w = (φ w).val := by
  obtain ⟨h, g, c, hgφ⟩ := exists_chart_extending hD φ
  have hgφ' : ∀ w : Circle, g (w : ℂ) = (φ w).val := by
    intro w
    obtain ⟨t, rfl⟩ := Circle.exp_surjective w
    exact hgφ t
  let N₀ := h '' N
  have hN₀ : N₀ ⊆ sphere (0 : ℂ) 1 := by
    rintro _ ⟨n, hn, rfl⟩
    exact c.bd ▸ mem_image_of_mem h (hN hn)
  obtain ⟨K, p₀, hK, hKsub, hKN, -, hp₀c, hp₀i, hp₀r, hp₀fix⟩ :=
    exists_unit_disc_contacts_with_param hN₀ (hfin.image h) (hne.image h)
  have hp₀K : ∀ w, p₀ w ∈ K := fun w => discBd_subset _ (hp₀r ▸ mem_range_self w)
  have hQD : g '' K ⊆ D := fun z hz => by
    obtain ⟨y, hy, rfl⟩ := hz
    exact c.gm (hKsub hy)
  obtain ⟨hQ, hQbd⟩ := hK.image (c.gc.mono hKsub) (c.hc.mono hQD)
    (fun z hz => c.hg (hKsub hz))
  have hgi : InjOn g K := by
    intro z hz y hy hzy
    have heq := congrArg h hzy
    rwa [c.hg (hKsub hz), c.hg (hKsub hy)] at heq
  let p := g ∘ p₀
  have hpc : Continuous p := c.gc.comp_continuous hp₀c (fun w => hKsub (hp₀K w))
  have hpi : Function.Injective p := fun a b hab => hp₀i (hgi (hp₀K a) (hp₀K b) hab)
  have hpr : range p = discBd (g '' K) := by
    rw [show p = g ∘ p₀ from rfl, range_comp, hp₀r, hQbd]
  have hfix : ∀ w, (φ w).val ∈ N → p w = (φ w).val := by
    intro w hw
    have hwN : (w : ℂ) ∈ N₀ := by
      refine ⟨(φ w).val, hw, ?_⟩
      rw [← hgφ' w]
      exact c.hg (sphere_subset_closedBall w.property)
    change g (p₀ w) = _
    rw [hp₀fix w hwN, hgφ']
  have hgh : ∀ n ∈ N, g (h n) = n := fun n hn => c.gh (discBd_subset D (hN hn))
  have hcontact : (g '' K) ∩ discBd D = N := by
    apply Subset.antisymm
    · rintro _ ⟨⟨z, hz, rfl⟩, hzBd⟩
      have hzS : z ∈ sphere (0 : ℂ) 1 := by
        have h' : h (g z) ∈ sphere (0 : ℂ) 1 := c.bd ▸ mem_image_of_mem h hzBd
        rwa [c.hg (hKsub hz)] at h'
      obtain ⟨n, hn, heq⟩ := hKN.subset ⟨hz, hzS⟩
      rw [← heq, hgh n hn]
      exact hn
    · intro n hn
      have hnK : h n ∈ K := ((hKN.symm).subset (mem_image_of_mem h hn)).1
      exact ⟨⟨h n, hnK, hgh n hn⟩, hN hn⟩
  have hNQ : N ⊆ discBd (g '' K) := by
    intro n hn
    let w := φ.symm ⟨n, hN hn⟩
    have hw : (φ w).val = n := congrArg Subtype.val (φ.apply_symm_apply ⟨n, hN hn⟩)
    have hpw : p w = n := (hfix w (hw.symm ▸ hn)).trans hw
    exact hpr ▸ (show n ∈ range p from ⟨w, hpw⟩)
  exact ⟨g '' K, p, hQ, hQD, hcontact, hNQ, hpc, hpi, hpr, hfix⟩

end GraphMinor.GM12
