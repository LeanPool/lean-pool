/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2EntryAtPath

/-!
# Entry comparisons in a larger subspace

For the region deformation in XII (2.1), page 244, both ends of a
region visit must be present in one subspace. Lift a single approach
to the region together with its own limiting vertex, read its entry
comparison there, and map that comparison into the larger subspace.
The prescribed approach path is retained exactly.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- Read an entry comparison in any subspace containing the region
and the entering vertex. The terminal spoke retains its exact edge
closure and interior image. -/
theorem entry_comparison_at_path_start_in_subspace
    {S : Type*} [TopologicalSpace S] [T2Space S]
    {r e Z : Set S} {v w : S} (hcell : IsOpenDisc r) (hw : w ∈ r)
    (hZ : r ∪ {v} ⊆ Z) (hvE : v ∉ e) (hwE : w ∉ e) (hvw : v ≠ w)
    {f : ℝ → S} (hf : Continuous f) {a c h₀ : ℝ} (hh₀ : h₀ ∈ Ioo a c)
    (hfc : f c = v) (hfr : ∀ t ∈ Ioo a c, f t ∈ r)
    (hentry : EntersLike f a c e r v w)
    {x : Z} (F : Path x (⟨v, hZ (Or.inr rfl)⟩ : Z))
    (hFsmall : ∀ t, (F t).val ∈ r ∪ {v})
    (hF : ∀ t, (F t).val = f (h₀ + t.val * (c - h₀))) :
    ∃ (β : Path (⟨v, hZ (Or.inr rfl)⟩ : Z) ⟨w, hZ (Or.inl hw)⟩)
      (ρ : Path x (⟨w, hZ (Or.inl hw)⟩ : Z)),
      Function.Injective (fun t => (β t).val) ∧
      range (fun t => (β t).val) = closure e ∧
      (fun t => (β t).val) '' Ioo (0 : unitInterval) 1 = e ∧
      (∀ t, (ρ t).val ∈ r) ∧ (F.trans β).Homotopic ρ := by
  let x₀ : (r ∪ {v} : Set S) := ⟨x.val, (congrArg Subtype.val F.source) ▸ hFsmall 0⟩
  let F₀ : Path x₀ (⟨v, Or.inr rfl⟩ : (r ∪ {v} : Set S)) := {
    toFun := fun t => ⟨(F t).val, hFsmall t⟩
    continuous_toFun := (continuous_subtype_val.comp F.continuous).subtype_mk _
    source' := by
      apply Subtype.ext
      change (F 0).val = x.val
      exact congrArg (fun z : Z => z.val) F.source
    target' := by
      apply Subtype.ext
      change (F 1).val = v
      exact congrArg (fun z : Z => z.val) F.target }
  obtain ⟨β₀, ρ₀, hβ, hβrange, hβe, hρ, hhom⟩ :=
    entry_comparison_at_path_start hcell hw hvE hwE hvw hf hh₀ hfc hfr hentry F₀ hF
  let J : C((r ∪ {v} : Set S), Z) :=
    ⟨fun z => ⟨z.val, hZ z.property⟩, continuous_subtype_val.subtype_mk _⟩
  have hFmap : F₀.map J.continuous = F := by ext t; rfl
  have hm := hhom.map J
  rw [Path.map_trans, hFmap] at hm
  exact ⟨β₀.map J.continuous, ρ₀.map J.continuous, hβ, hβrange, hβe, hρ, hm⟩

end GraphMinor.GM12
