/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.LocalCoh
public import Mathlib.Topology.UniformSpace.OfCompactT2
public import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# A local cocycle from a free action

Let a finite group `A` act freely on the right on a compact Hausdorff space `Z`, with quotient `Y`.
Fix a function `σ` that
picks a point in each fibre. For near points `x, y` of `Y` there is one `s` such that `s • σ x` is
near `σ y`. This `s`
is a local cocycle on `Y` (`cocycle_of_cover`).
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Filter
open scoped Uniformity

universe u v

variable {Z : Type u} {Y : Type v} {A : Type}

theorem cocycle_of_cover_aux [UniformSpace Z] [CompactSpace Z] [T2Space Z] [TopologicalSpace Y]
  [T2Space Y]
    [AddGroup A] [Finite A] (τ : A → Z → Z) (hτc : ∀ s, Continuous (τ s)) (hτ0 : ∀ z, τ 0 z = z)
    (hτa : ∀ s t z, τ s (τ t z) = τ (t + s) z) (hfree : ∀ s z, τ s z = z → s = 0) (q : Z → Y)
      (hq : Continuous q)
    (hs : Function.Surjective q) (hfib : ∀ z z', q z = q z' → ∃ s, z' = τ s z) (hfib' : ∀ s z, q
      (τ s z) = q z)
    (σ : Y → Z) (hσ : ∀ y, q (σ y) = y) :
    ∃ (φ : Y → Y → A) (V : Set (Z × Z)), NearDiag V ∧ IsCoc φ ∧
      (∀ x y s, (τ s (σ x), σ y) ∈ V → φ x y = s) ∧ ∀ t z z', (z, z') ∈ V → (τ t z, τ t z') ∈ V
        := by
  classical
  have hW₀ : (⋃ s ∈ {s : A | s ≠ 0}, {p : Z × Z | p.2 = τ s p.1})ᶜ ∈ 𝓤 Z := by
    rw [← nhdsSet_diagonal_eq_uniformity]
    have hcl : IsClosed (⋃ s ∈ {s : A | s ≠ 0}, {p : Z × Z | p.2 = τ s p.1}) :=
      (toFinite _).isClosed_biUnion fun s _ => isClosed_eq continuous_snd
        ((hτc s).comp continuous_fst)
    refine hcl.isOpen_compl.mem_nhdsSet.mpr ?_
    rintro ⟨z, z'⟩ hd h
    have hd' : z = z' := hd
    subst hd'
    obtain ⟨s, hs0, he⟩ := mem_iUnion₂.mp h
    exact hs0 (hfree s z (Eq.symm he))
  obtain ⟨V₁, hV₁, hsym₁, hc₁⟩ := comp_symm_mem_uniformity_sets hW₀
  obtain ⟨V₂, hV₂, hsym₂, hc₂⟩ := comp_symm_mem_uniformity_sets hV₁
  have hV : (⋂ s : A, (fun p : Z × Z => (τ s p.1, τ s p.2)) ⁻¹' V₂) ∈ 𝓤 Z :=
    (Filter.iInter_mem).mpr fun s => (CompactSpace.uniformContinuous_of_continuous (hτc s)) hV₂
  set V : Set (Z × Z) := ⋂ s : A, (fun p : Z × Z => (τ s p.1, τ s p.2)) ⁻¹' V₂ with hVdef
  have hdiag : ∀ {W : Set (Z × Z)}, W ∈ 𝓤 Z → ∀ z, (z, z) ∈ W := fun hW z => refl_mem_uniformity hW
  have hsub : V ⊆ V₂ := fun p hp => by
    have h1 := mem_iInter.mp hp 0
    have h2 : (τ 0 p.1, τ 0 p.2) ∈ V₂ := h1
    rwa [hτ0, hτ0] at h2
  have hsub₁ : V₂ ⊆ V₁ := fun p hp => hc₂ (SetRel.prodMk_mem_comp hp (hdiag hV₂ _))
  have hinv : ∀ t {z z'}, (z, z') ∈ V → (τ t z, τ t z') ∈ V := by
    intro t z z' h
    refine mem_iInter.mpr fun s => ?_
    have h1 : (τ (t + s) z, τ (t + s) z') ∈ V₂ := mem_iInter.mp h (t + s)
    change (τ s (τ t z), τ s (τ t z')) ∈ V₂
    rwa [hτa, hτa]
  have hkey : ∀ s {a b c}, (a, b) ∈ V → (b, c) ∈ V → (τ s a, c) ∈ V → s = 0 := by
    intro s a b c h1 h2 h3
    by_contra hs0
    have h4 : (a, c) ∈ V₁ := hc₂ (SetRel.prodMk_mem_comp (hsub h1) (hsub h2))
    have h5 : (c, τ s a) ∈ V₁ := hsub₁ (hsym₂.symm _ _ (hsub h3))
    have h6 := hc₁ (SetRel.prodMk_mem_comp h4 h5)
    exact h6 (mem_iUnion₂.mpr ⟨s, hs0, rfl⟩)
  have huniq : ∀ {x y : Y} {s s'}, (τ s (σ x), σ y) ∈ V → (τ s' (σ x), σ y) ∈ V → s = s' := by
    intro x y s s' h1 h2
    have h3 : τ (-s + s') (τ s (σ x)) = τ s' (σ x) := by
      rw [hτa, add_neg_cancel_left]
    have h4 := hkey (-s + s') h1 (hdiag hV _) (h3 ▸ h2)
    exact neg_add_eq_zero.mp h4
  let φ : Y → Y → A := fun x y => if h : ∃ s, (τ s (σ x), σ y) ∈ V then h.choose else 0
  have hφ : ∀ x y s, (τ s (σ x), σ y) ∈ V → φ x y = s := by
    intro x y s h
    have hex : ∃ s, (τ s (σ x), σ y) ∈ V := ⟨s, h⟩
    simp only [φ, hex, dite_eq_left]
    exact huniq hex.choose_spec h
  let N : Set (Y × Y) := {p | ∃ z z', q z = p.1 ∧ q z' = p.2 ∧ (z, z') ∈ V}
  have hNex : ∀ x y, (x, y) ∈ N → ∃ s, (τ s (σ x), σ y) ∈ V := by
    rintro x y ⟨z, z', h1, h2, h3⟩
    obtain ⟨s₁, rfl⟩ := hfib (σ x) z (by rw [hσ]; exact h1.symm)
    obtain ⟨s₂, rfl⟩ := hfib (σ y) z' (by rw [hσ]; exact h2.symm)
    refine ⟨s₁ + -s₂, ?_⟩
    have h4 := hinv (-s₂) h3
    rwa [hτa, hτa, add_neg_cancel, hτ0] at h4
  have hVZ : NearDiag V := fun z => by
    have h1 : V ∈ 𝓝ˢ (diagonal Z) := by
      rw [nhdsSet_diagonal_eq_uniformity]
      exact hV
    exact mem_nhdsSet_iff_forall.mp h1 (z, z) rfl
  have hN : NearDiag N := by
    intro p
    obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.mp (hVZ (σ p))
    obtain ⟨O₀, hO₀, hO₀o, hzO⟩ := mem_nhds_iff.mp (Filter.inter_mem hu hv)
    let U' : Set Z := ⋃ s, τ s ⁻¹' O₀
    have hU' : IsOpen U' := isOpen_iUnion fun s => hO₀o.preimage (hτc s)
    have hC : IsClosed (q '' U'ᶜ) := (hU'.isClosed_compl.isCompact.image hq).isClosed
    have hp : p ∉ q '' U'ᶜ := by
      rintro ⟨z, hz, he⟩
      obtain ⟨s, hs'⟩ := hfib z (σ p) (by rw [hσ]; exact he)
      refine hz (mem_iUnion.mpr ⟨s, ?_⟩)
      change τ s z ∈ O₀
      rw [← hs']
      exact hzO
    have hO : (q '' U'ᶜ)ᶜ ×ˢ (q '' U'ᶜ)ᶜ ∈ 𝓝 (p, p) :=
      (hC.isOpen_compl.prod hC.isOpen_compl).mem_nhds ⟨hp, hp⟩
    refine Filter.mem_of_superset hO ?_
    have hlift : ∀ x ∈ (q '' U'ᶜ)ᶜ, ∃ z ∈ O₀, q z = x := by
      intro x hx
      obtain ⟨z, rfl⟩ := hs x
      have hz : z ∈ U' := by
        by_contra hc
        exact hx ⟨z, hc, rfl⟩
      obtain ⟨s, hs'⟩ := mem_iUnion.mp hz
      exact ⟨τ s z, hs', hfib' s z⟩
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    obtain ⟨z, hz, rfl⟩ := hlift x hx
    obtain ⟨z', hz', rfl⟩ := hlift y hy
    exact ⟨z, z', rfl, rfl, huv ⟨(hO₀ hz).1, (hO₀ hz').2⟩⟩
  refine ⟨φ, V, hVZ, ⟨N, hN, fun x y z hxy hyz hxz => ?_⟩, hφ, fun t z z' h => hinv t h⟩
  obtain ⟨s₁, h1⟩ := hNex _ _ hxy
  obtain ⟨s₂, h2⟩ := hNex _ _ hyz
  obtain ⟨s₃, h3⟩ := hNex _ _ hxz
  rw [hφ _ _ _ h1, hφ _ _ _ h2, hφ _ _ _ h3]
  have h4 := hinv s₂ h1
  rw [hτa] at h4
  have h5 : τ (-(s₁ + s₂) + s₃) (τ (s₁ + s₂) (σ x)) = τ s₃ (σ x) := by
    rw [hτa, add_neg_cancel_left]
  have h6 := hkey _ h4 h2 (h5 ▸ h3)
  exact neg_add_eq_zero.mp h6

theorem cocycle_of_cover [TopologicalSpace Z] [CompactSpace Z] [T2Space Z] [TopologicalSpace Y]
  [T2Space Y]
    [AddGroup A] [Finite A] (τ : A → Z → Z) (hτc : ∀ s, Continuous (τ s)) (hτ0 : ∀ z, τ 0 z = z)
    (hτa : ∀ s t z, τ s (τ t z) = τ (t + s) z) (hfree : ∀ s z, τ s z = z → s = 0) (q : Z → Y)
      (hq : Continuous q)
    (hs : Function.Surjective q) (hfib : ∀ z z', q z = q z' → ∃ s, z' = τ s z) (hfib' : ∀ s z, q
      (τ s z) = q z)
    (σ : Y → Z) (hσ : ∀ y, q (σ y) = y) :
    ∃ (φ : Y → Y → A) (V : Set (Z × Z)), NearDiag V ∧ IsCoc φ ∧
      (∀ x y s, (τ s (σ x), σ y) ∈ V → φ x y = s) ∧ ∀ t z z', (z, z') ∈ V → (τ t z, τ t z') ∈ V
        := by
  let _ : UniformSpace Z := uniformSpaceOfCompactR1
  exact cocycle_of_cover_aux τ hτc hτ0 hτa hfree q hq hs hfib hfib' σ hσ

end GraphMinor.Surface
