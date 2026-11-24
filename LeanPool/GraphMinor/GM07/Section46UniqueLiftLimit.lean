/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Separation.Basic

/-!
# Unique limiting values for a finite-fibre lift

The second cutting map in VII (4.6), page 226, extends the lift of the
open net disc to its boundary. Near a boundary point, small pieces of
the open disc are connected. Two different limiting values would lie
in disjoint neighbourhoods of a finite fibre. Connectedness forces the
lift into one of those neighbourhoods, contradicting the other limit.
-/

public section

namespace GraphMinor.GM07

open Set Topology

/-- The limiting value of a lift is unique when small approaches from
its domain are connected and the target cutting map has finite fibres.
This is the boundary extension argument for the second cut in VII (4.6),
page 226. -/
theorem unique_lift_limit_of_connected_approach
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [CompactSpace Y] [T2Space Y] [T2Space Z]
    {U : Set X} {f : X → Z} {g : X → Y} {θ : Y → Z}
    (hf : Continuous f) (hg : ContinuousOn g U) (hθ : Continuous θ)
    (hfinite : ∀ z, (θ ⁻¹' {z}).Finite) (hrel : ∀ x ∈ U, θ (g x) = f x)
    {x : X}
    (happroach : ∀ O : Set X, IsOpen O → x ∈ O →
      ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ W ⊆ O ∧ IsPreconnected (W ∩ U))
    {a b : Y}
    (ha : (x, a) ∈ closure ((fun z => (z, g z)) '' U))
    (hb : (x, b) ∈ closure ((fun z => (z, g z)) '' U)) : a = b := by
  classical
  have hclosed : IsClosed {p : X × Y | θ p.2 = f p.1} :=
    isClosed_eq (hθ.comp continuous_snd) (hf.comp continuous_fst)
  have hclrel : closure ((fun z => (z, g z)) '' U) ⊆ {p : X × Y | θ p.2 = f p.1} := by
    apply closure_minimal _ hclosed
    rintro p ⟨z, hz, rfl⟩
    exact hrel z hz
  have haθ : θ a = f x := hclrel ha
  have hbθ : θ b = f x := hclrel hb
  by_contra hne
  have hrest : (θ ⁻¹' {f x} \ {a}).Finite := (hfinite (f x)).subset sdiff_subset
  obtain ⟨O₁, O₂, hO₁, hO₂, haO, hrestO, hdis⟩ :=
    SeparatedNhds.of_finite (finite_singleton a) hrest (by simp)
  have haO₁ : a ∈ O₁ := haO rfl
  have hbO₂ : b ∈ O₂ := hrestO ⟨hbθ, fun h => hne h.symm⟩
  have hK : IsClosed (θ '' (O₁ ∪ O₂)ᶜ) := hθ.isClosedMap _ (hO₁.union hO₂).isClosed_compl
  have hxO : x ∈ f ⁻¹' (θ '' (O₁ ∪ O₂)ᶜ)ᶜ := by
    rintro ⟨y, hy, hyθ⟩
    by_cases hya : y = a
    · exact hy (.inl (hya ▸ haO₁))
    · exact hy (.inr (hrestO ⟨hyθ, hya⟩))
  obtain ⟨W, hWo, hxW, hWO, hWc⟩ := happroach _ (hK.isOpen_compl.preimage hf) hxO
  let T := g '' (W ∩ U)
  have hTc : IsPreconnected T := hWc.image g (hg.mono inter_subset_right)
  have hTsub : T ⊆ O₁ ∪ O₂ := by
    rintro y ⟨z, ⟨hzW, hzU⟩, rfl⟩
    by_contra hn
    exact hWO hzW ⟨g z, hn, hrel z hzU⟩
  have hmeet : ∀ (V : Set Y), IsOpen V → ∀ y ∈ V,
      (x, y) ∈ closure ((fun z => (z, g z)) '' U) → (T ∩ V).Nonempty := by
    intro V hVo y hy hcl
    obtain ⟨p, hp, hpgraph⟩ := mem_closure_iff.mp hcl (W ×ˢ V) (hWo.prod hVo) ⟨hxW, hy⟩
    obtain ⟨z, hzU, hz⟩ := hpgraph
    rw [← hz] at hp
    exact ⟨g z, ⟨z, ⟨hp.1, hzU⟩, rfl⟩, hp.2⟩
  rcases IsPreconnected.subset_or_subset hO₁ hO₂ hdis hTsub hTc with h | h
  · obtain ⟨y, hyT, hyO⟩ := hmeet O₂ hO₂ b hbO₂ hb
    exact disjoint_left.mp hdis (h hyT) hyO
  · obtain ⟨y, hyT, hyO⟩ := hmeet O₁ hO₁ a haO₁ ha
    exact disjoint_left.mp hdis hyO (h hyT)

end GraphMinor.GM07
