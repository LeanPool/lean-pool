/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3ForestTransport
public import LeanPool.GraphMinor.GM12.Section3FeasibilityDiscs
public import LeanPool.GraphMinor.GM12.Section3PuncturedSurface
import LeanPool.GraphMinor.GM12.Section3PuncturedBoundary

/-!
# Reading an ambient boundary-connection forest in the punctured surface

In XII (3.2), page 247, the auxiliary disc avoids the forest, so
adding it changes neither the forest's prescribed contacts nor its
boundary connections. This file reads any such ambient forest in
the complement of the prescribed discs. The contact equations prove
properness and identify its boundary vertices. Walk transfer retains
the connection classes, and injective inclusion retains the forest
property.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- An ambient forest meeting the prescribed discs exactly at its
boundary classes is the feasibility forest in their complement.
This permits the auxiliary disc in XII (3.2), page 247. -/
theorem exists_punctured_forest_of_ambient
    {S : Type*} [TopologicalSpace S] [T2Space S] {t p : ℕ}
    (hS : IsClosedSurface S) (Δ : Fin t → Set S) (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdis : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    (Zs : Fin p → Set S) (K : Drawing S) (hF : IsGraphForest K.toGraph)
    (hU : K.U ∩ ⋃ i, Δ i = ⋃ j, Zs j) (hV : K.V ∩ ⋃ i, Δ i = ⋃ j, Zs j)
    (hZ : (⋃ j, Zs j) ⊆ ⋃ i, discBd (Δ i))
    (hclasses : ∀ j, ∀ x ∈ Zs j, ∀ y ∈ K.V ∩ ⋃ i, Δ i,
      Nonempty (GraphWalk K.toGraph x y) ↔ y ∈ Zs j) :
    ∃ H : Drawing (discComplement Δ), GM07.IsSurfaceForest H ∧
      H.V ∩ bd (discComplement Δ) = Subtype.val ⁻¹' ⋃ j, Zs j ∧
      ∀ j, ∀ x ∈ (Subtype.val : discComplement Δ → S) ⁻¹' Zs j,
        ∀ y ∈ H.V ∩ bd (discComplement Δ),
          Nonempty (GraphWalk H.toGraph x y) ↔ y.val ∈ Zs j := by
  let C := discComplement Δ
  have hKC : K.U ⊆ C := feasibility_disc_subset_discComplement hS Δ hΔ hdis hU hZ
  let H := drawingInSubspace K C hKC
  have hbd : ∀ x : C, x ∈ bd C ↔ x.val ∈ ⋃ i, discBd (Δ i) := by
    intro x
    exact (congrArg (fun F : Set C => x ∈ F) (discComplement_boundary_eq hS Δ hΔ)) |> of_eq
  have hbdΔ : (⋃ i, discBd (Δ i)) ⊆ ⋃ i, Δ i := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨i, Surface.discBd_subset _ hi⟩
  have hHV : ∀ x : C, x ∈ H.V ↔ x.val ∈ K.V := by
    intro x
    dsimp only [H]
    rw [drawingInSubspace_V]
    rfl
  have hHU : ∀ x : C, x ∈ H.U ↔ x.val ∈ K.U := by
    intro x
    dsimp only [H]
    rw [drawingInSubspace_U]
    rfl
  have hproper : H.IsProper := by
    intro x hx
    have hxZ := hU.subset ⟨(hHU x).mp hx.2, hbdΔ ((hbd x).mp hx.1)⟩
    exact (hHV x).mpr (hV.symm.subset hxZ).1
  have hboundary : H.V ∩ bd C = (Subtype.val : C → S) ⁻¹' ⋃ j, Zs j := by
    ext x
    constructor
    · intro hx
      exact hV.subset ⟨(hHV x).mp hx.1, hbdΔ ((hbd x).mp hx.2)⟩
    · intro hx
      exact ⟨(hHV x).mpr (hV.symm.subset hx).1, (hbd x).mpr (hZ hx)⟩
  refine ⟨H, ⟨hproper, isGraphForest_drawingInSubspace hF C isClosed_closure hKC⟩,
    hboundary, ?_⟩
  intro j x hx y hy
  exact (walk_drawingInSubspace_iff K C isClosed_closure hKC).trans
    (hclasses j x.val hx y.val ⟨(hHV y).mp hy.1, hbdΔ ((hbd y).mp hy.2)⟩)

end GraphMinor.GM12
