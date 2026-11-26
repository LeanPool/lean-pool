/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Open
import LeanPool.GraphMinor.GM07.Section2Base
import LeanPool.GraphMinor.GM07.Section46DiscApproach
import LeanPool.GraphMinor.GM07.Section46SeamComplement
import LeanPool.GraphMinor.GM07.Section46UniqueLiftLimit
import LeanPool.GraphMinor.GM11.Rotation
import LeanPool.GraphMinor.Surface.Cuffs
import LeanPool.GraphMinor.Surface.SurfacePull

/-!
# The second cutting map in VII (4.6)

On page 226 the disc `Δ` is cut from `Σ` in two stages, so there is a
natural surjection `ψ : Δ → Σ′` with `θ(ψ(x)) = φ(x)`. On the open disc,
`φ(x)` avoids the seam, so `θ` has exactly one point over it, and this
point is `ψ(x)`. The map on the open disc is continuous since `θ` is a
closed map. It extends to the closed disc since two limits at one
point would be separated in a finite fibre of `θ`, while small
approaches to that point in the open disc are connected.
-/

public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface

universe u

variable {S S' : Type u} [TopologicalSpace S] [TopologicalSpace S']

/-- The natural surjection `ψ : Δ → Σ′` of VII (4.6), page 226. -/
theorem Net.exists_psi [T2Space S] (_hS : IsSurface S) (N : Net S) {L : Drawing S} {θ : S' → S}
    (hθ : IsCutAlongGraph L S' θ) (hL : L.U ⊆ N.seamU) :
    ∃ ψ : N.D → S', Continuous ψ ∧ Function.Surjective ψ ∧ ∀ x, θ (ψ x) = N.φ x := by
  classical
  have hS' := hθ.isSurface
  have : CompactSpace S' := hS'.1
  have : T2Space S' := hS'.2.1
  have hD := N.isSurface_D
  have : CompactSpace N.D := hD.1
  have : T2Space N.D := hD.2.1
  have hθc : Continuous θ := hθ.quotientMap.continuous
  have hθs : Function.Surjective θ := hθ.quotientMap.surjective
  have hφc : Continuous N.φ := N.quotientMap_φ.continuous
  let U : Set N.D := (bd N.D)ᶜ
  have hint : ∀ x ∈ U, ∀ y : S', θ y = N.φ x → y ∉ bd S' := by
    intro x hx y hy hyb
    rw [← hθ.preimage_bd_union_U] at hyb
    have hseam : θ y ∈ N.seamU := by
      rcases hyb with h | h
      · exact N.bd_subset_seamU h
      · exact hL h
    rw [hy] at hseam
    exact hx (N.preimage_seamU ▸ hseam)
  choose g hg using fun x => hθs (N.φ x)
  have hclosed : IsClosedMap θ := hθc.isClosedMap
  have hgc : ContinuousOn g U := by
    intro x hx
    rw [ContinuousWithinAt, tendsto_nhds]
    intro O hO hgx
    have hK : IsClosed (θ '' Oᶜ) := hclosed _ hO.isClosed_compl
    have hxK : x ∈ N.φ ⁻¹' (θ '' Oᶜ)ᶜ := by
      rintro ⟨y, hy, hyθ⟩
      have hgxb : g x ∉ bd S' := hint x hx (g x) (hg x)
      have heq := hθ.interior_inj (g x) hgxb y ((hg x).trans hyθ.symm)
      exact hy (heq ▸ hgx)
    have hopen : IsOpen (N.φ ⁻¹' (θ '' Oᶜ)ᶜ) := hK.isOpen_compl.preimage hφc
    apply mem_nhdsWithin.mpr
    refine ⟨_, hopen, hxK, ?_⟩
    rintro z ⟨hz, -⟩
    by_contra hzO
    exact hz ⟨g z, hzO, hg z⟩
  let Γ : Set (N.D × S') := closure ((fun z => (z, g z)) '' U)
  have hΓc : IsClosed Γ := isClosed_closure
  have hrel : ∀ p ∈ Γ, θ p.2 = N.φ p.1 := by
    have hcl : IsClosed {p : N.D × S' | θ p.2 = N.φ p.1} :=
      isClosed_eq (hθc.comp continuous_snd) (hφc.comp continuous_fst)
    have hsub : Γ ⊆ {p : N.D × S' | θ p.2 = N.φ p.1} := by
      apply closure_minimal _ hcl
      rintro p ⟨z, -, rfl⟩
      exact hg z
    exact fun p hp => hsub hp
  have hdense : Dense U := fun x => mem_closure_compl_bd (hD.2.2 x)
  have hex : ∀ x : N.D, ∃ a : S', (x, a) ∈ Γ := by
    have hfstc : IsClosed (Prod.fst '' Γ) := isClosedMap_fst_of_compactSpace _ hΓc
    have hsub : U ⊆ Prod.fst '' Γ := fun z hz =>
      ⟨(z, g z), subset_closure ⟨z, hz, rfl⟩, rfl⟩
    intro x
    have hx : x ∈ Prod.fst '' Γ := closure_minimal hsub hfstc (hdense x)
    obtain ⟨⟨y, a⟩, hp, rfl⟩ := hx
    exact ⟨a, hp⟩
  obtain ⟨e⟩ : Nonempty (ClosedUnitDisc ≃ₜ N.D) := by
    obtain ⟨e⟩ := N.isClosedDisc_D
    exact ⟨e.trans (Homeomorph.Set.univ N.D)⟩
  have huniq : ∀ {x : N.D} {a b : S'}, (x, a) ∈ Γ → (x, b) ∈ Γ → a = b := by
    intro x a b ha hb
    exact unique_lift_limit_of_connected_approach hφc hgc hθc hθ.finite_fiber (fun z _ => hg z)
      (fun O hO hx => closed_disc_connected_approach e x O hO hx) ha hb
  choose ψ hψ using hex
  have hψc : Continuous ψ := by
    rw [continuous_iff_isClosed]
    intro C hC
    have hpre : ψ ⁻¹' C = Prod.fst '' (Γ ∩ Prod.snd ⁻¹' C) := by
      ext x
      constructor
      · intro hx
        exact ⟨(x, ψ x), ⟨hψ x, hx⟩, rfl⟩
      · rintro ⟨⟨y, a⟩, ⟨hp, ha⟩, rfl⟩
        change ψ y ∈ C
        rw [huniq (hψ y) hp]
        exact ha
    rw [hpre]
    exact isClosedMap_fst_of_compactSpace _ (hΓc.inter (hC.preimage continuous_snd))
  have hψg : ∀ x ∈ U, ψ x = g x := fun x hx => huniq (hψ x) (subset_closure ⟨x, hx, rfl⟩)
  have hsurj : Function.Surjective ψ := by
    have hrange : IsClosed (range ψ) := isCompact_range hψc |>.isClosed
    let Q : Set S' := θ ⁻¹' N.seamUᶜ
    have hQsub : Q ⊆ range ψ := by
      intro z hz
      obtain ⟨x, hx⟩ := N.quotientMap_φ.surjective (θ z)
      have hxU : x ∈ U := fun hb => hz (hx ▸ mem_image_of_mem N.φ hb)
      have hzb : z ∉ bd S' := by
        intro hb
        rw [← hθ.preimage_bd_union_U] at hb
        rcases hb with h | h
        · exact hz (N.bd_subset_seamU h)
        · exact hz (hL h)
      exact ⟨x, by
        rw [hψg x hxU]
        exact (hθ.interior_inj z hzb (g x) (by rw [hg x, hx])).symm⟩
    have hQdense : Dense Q := by
      intro y
      rw [mem_closure_iff]
      intro O hO hy
      obtain ⟨z, hzO, hzb⟩ := mem_closure_iff.mp (mem_closure_compl_bd (hS'.2.2 y)) O hO hy
      have hbc : IsOpen (bd S')ᶜ := (isClosed_bd S').isOpen_compl
      let O' := O ∩ (bd S')ᶜ
      have hO'o : IsOpen O' := hO.inter hbc
      have hsat : θ ⁻¹' (θ '' O') = O' := by
        apply Subset.antisymm _ (subset_preimage_image θ O')
        rintro w ⟨w', hw', hww⟩
        rw [hθ.interior_inj w' hw'.2 w hww] at hw'
        exact hw'
      have him : IsOpen (θ '' O') := by
        rw [← hθ.quotientMap.isOpen_preimage, hsat]
        exact hO'o
      obtain ⟨t, htO, htC⟩ := (N.dense_compl_seamU).inter_open_nonempty _ him ⟨θ z, z, ⟨hzO, hzb⟩,
        rfl⟩
      obtain ⟨w, hw, rfl⟩ := htO
      exact ⟨w, hw.1, htC⟩
    intro y
    exact closure_minimal hQsub hrange (hQdense y)
  exact ⟨ψ, hψc, hsurj, fun x => hrel _ (hψ x)⟩

end GraphMinor.GM07
