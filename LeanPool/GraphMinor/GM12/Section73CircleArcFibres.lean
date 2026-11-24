/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73ArcCollapseCircle
public import LeanPool.GraphMinor.GM12.Section73CircleComplement
import LeanPool.GraphMinor.GM11.Forest
import LeanPool.GraphMinor.Surface.DiscGrow
import LeanPool.GraphMinor.Surface.SurfaceGraph

/-!
# Circle parameters when the collapsed fibre is an arc

For XII (7.3), Claim (1), page 262, the old circuit meets the
collapsed star in one arc. Split its circle into that arc and
the complementary arc. The exact fibre condition makes the image
of the complementary arc injective except at its ends. Its image
is the whole new circle, since the collapsed arc contributes only
the common endpoint. Removing the constant arc gives the required
homotopy of parameterized curves.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface

/-- If a collapse meets an old circle in an arc, its image circle
has an embedded parameterization homotopic to the collapsed old
parameterization. This is the arc-fibre case used for the selected
disc comparison in XII (7.3), Claim (1), page 262. -/
theorem exists_circle_parameters_of_arc_fibre
    {S : Type*} [TopologicalSpace S] [T2Space S]
    {F A Z : Set S} {p q : S} (hF : IsOArc F)
    (hL : IsLineWithEnds (F ∩ A) p q) (f : C(S, S))
    (hfibre : ∀ x y, f x = f y ↔ x = y ∨ (x ∈ A ∧ y ∈ A))
    (hZ : f '' F ⊆ Z) :
    ∃ φ ψ : C(Circle, S), IsEmbedding φ ∧ IsEmbedding ψ ∧
      range φ = F ∧ range ψ = f '' F ∧
      ClosedCurvesHomotopicIn Z (f.comp φ) ψ := by
  obtain ⟨B, hB, hFB, hcap⟩ := exists_complementary_line_in_circle hF hL inter_subset_left
  obtain ⟨a, ha, hArange, ha₀, ha₁⟩ := hL.exists_arc
  obtain ⟨b, hb, hBrange, hb₀, hb₁⟩ := (GM11.IsLineWithEnds.symm hB).exists_arc
  let α : Path p q := ⟨⟨a, ha.1⟩, ha₀, ha₁⟩
  let β : Path q p := ⟨⟨b, hb.1⟩, hb₀, hb₁⟩
  have hαrange : range α = F ∩ A := hArange
  have hβrange : range β = B := hBrange
  have hαA : range α ⊆ A := hαrange ▸ inter_subset_right
  have hβA : range β ∩ A ⊆ {p, q} := by
    rw [hβrange]
    rintro x ⟨hxB, hxA⟩
    have hxF : x ∈ F := hFB ▸ Or.inr hxB
    exact hcap.subset ⟨⟨hxF, hxA⟩, hxB⟩
  have hαβ : range α ∩ range β ⊆ {p, q} := by rw [hαrange, hβrange, hcap]
  obtain ⟨φ, ψ, hφ, hψ, hφrange, hψrange, hh⟩ :=
    exists_circle_parameters_of_collapse_fibres α β ha.2 hb.2 hαβ hαA hβA f hfibre
      ((image_mono (show range β ⊆ F by rw [hβrange]; exact fun x hx => hFB ▸ Or.inr hx)).trans hZ)
  have hpA : p ∈ A := hL.left_mem.2
  have hsmall : f '' (F ∩ A) ⊆ f '' B := by
    rintro x ⟨y, hy, rfl⟩
    have hfp : f y = f p := (hfibre _ _).mpr (Or.inr ⟨hy.2, hpA⟩)
    exact ⟨p, hB.left_mem, hfp.symm⟩
  have hBimage : f '' B = f '' F := by
    rw [← hFB, image_union, union_eq_right.mpr hsmall]
  refine ⟨φ, ψ, hφ, hψ, ?_, ?_, hh⟩
  · rw [hφrange, hαrange, hβrange, hFB]
  · rw [hψrange, hβrange, hBimage]

end GraphMinor.GM12
