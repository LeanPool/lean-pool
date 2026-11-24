/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2EntryIndependence
import LeanPool.GraphMinor.GM12.Section2EntryComparison

/-!
# Reading an entry comparison at a prescribed starting path

For the corner comparison in XII (2.1), pages 243--244, move an entry
witness to a chosen point of its approach. Normalize it against the
path from that point to the vertex. The resulting spoke has the exact
edge closure and interior image, and its concatenation with the
approach is homotopic to a path in the region. Endpoint casts express
this comparison with the original path's endpoints.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- Read an entry witness as a spoke-path comparison for a normalized
approach starting at any prescribed interior parameter. -/
theorem entry_comparison_at_path_start
    {S : Type*} [TopologicalSpace S] [T2Space S]
    {r e : Set S} {v w : S} (hcell : IsOpenDisc r) (hw : w ∈ r)
    (hvE : v ∉ e) (hwE : w ∉ e) (hvw : v ≠ w)
    {f : ℝ → S} (hf : Continuous f) {a c h₀ : ℝ} (hh₀ : h₀ ∈ Ioo a c)
    (hfc : f c = v) (hfr : ∀ t ∈ Ioo a c, f t ∈ r)
    (hentry : EntersLike f a c e r v w)
    {x : (r ∪ {v} : Set S)}
    (F : Path x (⟨v, Or.inr rfl⟩ : (r ∪ {v} : Set S)))
    (hF : ∀ t, (F t).val = f (h₀ + t.val * (c - h₀))) :
    ∃ (β : Path (⟨v, Or.inr rfl⟩ : (r ∪ {v} : Set S)) ⟨w, Or.inl hw⟩)
      (ρ : Path x (⟨w, Or.inl hw⟩ : (r ∪ {v} : Set S))),
      Function.Injective (fun t => (β t).val) ∧
      range (fun t => (β t).val) = closure e ∧
      (fun t => (β t).val) '' Ioo (0 : unitInterval) 1 = e ∧
      (∀ t, (ρ t).val ∈ r) ∧ (F.trans β).Homotopic ρ := by
  obtain ⟨ξ, ρ₀, hξ, hρ₀, hhom⟩ := entersLike_witness_at hcell hw hvE hwE hvw
    hf hfc hfr hentry hh₀
  have hstart : h₀ = h₀ + (0 : unitInterval).val * (c - h₀) := by simp
  obtain ⟨β₀, σ₀, hβi, hβrange, hβe, hσr, hcompare⟩ :=
    compare_entry_to_approach hw F hF hstart hfc hvE hwE hvw hξ hρ₀ hhom
  let β := β₀.cast F.target.symm rfl
  let ρ := σ₀.cast F.source.symm rfl
  have hleft : ((F.subpath 0 1).trans β₀).cast F.source.symm rfl = F.trans β := by
    rw [Path.cast_trans _ _ _ F.target.symm _, Path.subpath_zero_one]
    rfl
  have hcompare' := hcompare.pathCast F.source.symm rfl
  rw [hleft] at hcompare'
  exact ⟨β, ρ, hβi, hβrange, hβe, hσr, hcompare'⟩

end GraphMinor.GM12
