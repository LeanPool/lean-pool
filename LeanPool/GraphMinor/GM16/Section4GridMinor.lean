/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section4WallRows
public import LeanPool.GraphMinor.GM16.MinorModelRestriction
public import LeanPool.GraphMinor.GM15.Defs
import LeanPool.GraphMinor.GM10.Section7
import LeanPool.GraphMinor.RST94.Theorem23

/-!
# The wall minor controlled by the tangle

Use the large square grid supplied by Robertson, Seymour and Thomas,
then keep its rectangular wall. The wall rows are exactly the first
`θ` rows of that square grid. Thus no small side of the original tangle
contains a complete wall row. This is Step (2) and the following
restriction in XVI (4.2), page 53.
-/

public section
namespace GraphMinor.GM16
open Set Graph SimpleGraph Hypergraph GM10 GM15
universe u v

/-- The wall inclusion takes each whole horizontal row onto a row of
the large square grid, including all its edges. -/
theorem sphereWallGridVertex_row_edges (θ : ℕ) (j : Fin θ) :
    Sym2.map (sphereWallGridVertex θ) '' E(sphereWallRow θ j) =
      (gridRowPath (2 * θ + 1) (Fin.castLE (by omega) j)).edgeSet := by
  ext e
  constructor
  · rintro ⟨e₀, he₀, rfl⟩
    obtain ⟨x, y, hlink, hx, hy⟩ := he₀
    have hAdj : (sphereWallSimpleGraph θ).Adj x y := by
      have he := hlink.2
      rw [hlink.1] at he
      exact he
    have hGrid := sphereWallGridVertex_adj hAdj
    have heq : Sym2.map (sphereWallGridVertex θ) e₀ =
        s(sphereWallGridVertex θ x, sphereWallGridVertex θ y) := by
      rw [hlink.1, Sym2.map_mk]
    refine ⟨?_, ?_⟩
    · rw [heq]
      exact hGrid
    · intro z hz
      rw [heq] at hz
      rcases (gridHypergraph_inc_sym2.mp hz).2 with rfl | rfl
      · apply Fin.ext
        simpa only [sphereWallGridVertex, Fin.val_castLE] using congrArg (Fin.val : Fin θ → ℕ) hx
      · apply Fin.ext
        simpa only [sphereWallGridVertex, Fin.val_castLE] using congrArg (Fin.val : Fin θ → ℕ) hy
  · intro he
    induction e with
    | h x y =>
      have hAdj : (pathGraph (2 * θ + 1) □ pathGraph (2 * θ + 1)).Adj x y := he.1
      have hx := he.2 x (gridHypergraph_inc_sym2.mpr ⟨hAdj, Or.inl rfl⟩)
      have hy := he.2 y (gridHypergraph_inc_sym2.mpr ⟨hAdj, Or.inr rfl⟩)
      have hStep : (pathGraph (2 * θ + 1)).Adj x.2 y.2 := by
        rcases boxProd_adj.mp hAdj with ⟨h, _⟩ | ⟨h, _⟩
        · exact (h.ne (hx.trans hy.symm)).elim
        · exact h
      let a : Fin (2 * θ + 1) × Fin θ := (x.2, j)
      let b : Fin (2 * θ + 1) × Fin θ := (y.2, j)
      have ha : sphereWallGridVertex θ a = x := Prod.ext hx.symm rfl
      have hb : sphereWallGridVertex θ b = y := Prod.ext hy.symm rfl
      refine ⟨s(a,b), ?_, ?_⟩
      · refine ⟨a, b, ⟨rfl, ?_⟩, rfl, rfl⟩
        exact Or.inl ⟨rfl, pathGraph_adj.mp hStep⟩
      · rw [Sym2.map_mk, ha, hb]

/-- Graph Minors XVI, (4.2), Step (2) and the following paragraph,
page 53: a sufficiently large tangle has the specified wall minor,
and its small sides of order at most `2θ` contain no complete wall row.
The cited grid theorem is used through its proved theorem. -/
theorem exists_wall_minor_no_small_row (θ : ℕ) (hθ : 1 ≤ θ) :
    ∃ θ_star : ℕ, 1 ≤ θ_star ∧
      ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_G : ℕ)
        (T : Set (Hypergraph α β × Hypergraph α β)),
        IsGraphTangle G θ_G T → θ_star ≤ θ_G →
        ∃ (ηv : Fin (2 * θ + 1) × Fin θ → Set α)
          (ηe : Sym2 (Fin (2 * θ + 1) × Fin θ) → β),
          IsMinorModel (sphereWallGraph θ) G ηv ηe ∧
          ∀ A B : Hypergraph α β, (A,B) ∈ T → separationOrder A B ≤ 2 * θ →
            ∀ j : Fin θ, ¬ ηe '' E(sphereWallRow θ j) ⊆ A.edgeSet := by
  obtain ⟨θ_star, hθ_star, hGrid⟩ := RST94.rst94_theorem_2_3 θ hθ
  refine ⟨θ_star, hθ_star, ?_⟩
  intro α β G θ_G T hT hθG
  obtain ⟨ηv, ηe, hModel, hNoRow⟩ := hGrid G θ_G T hT hθG
  refine ⟨ηv ∘ sphereWallGridVertex θ, ηe ∘ Sym2.map (sphereWallGridVertex θ), ?_, ?_⟩
  · exact IsMinorModel.restrict_simpleGraph_copy hModel (sphereWallGridVertex θ)
      (sphereWallGridVertex_injective θ) (fun _ _ h => sphereWallGridVertex_adj h)
  · intro A B hAB hOrd j hRow
    apply hNoRow A B hAB hOrd (Fin.castLE (by omega) j)
    rw [← sphereWallGridVertex_row_edges θ j, image_image]
    exact hRow

end GraphMinor.GM16
