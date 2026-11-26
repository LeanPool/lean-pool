/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.Defs
public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.GM16.PathIsoCard
import LeanPool.GraphMinor.GM16.LineDrawingPath
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM11.ArcDrawings
import LeanPool.GraphMinor.Surface.SurfaceGraph
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Data.Set.Card

/-!
# Drawing an abstract path on a prescribed line

Choose as many marked points on the line as the path has vertices,
including both ends. The existing line drawing construction gives
a drawing supported on that line. It is a path, and matching the
ordered vertex positions gives an isomorphism with the abstract
path that preserves both ends. This draws the replacing paths
of the subdivision in XVI (4.2).
-/

public section
namespace GraphMinor.GM16
open Set Graph Topology Surface GM09 GM11
universe u v w

/-- A line has infinitely many points. -/
theorem infinite_of_isLineWithEnds {S : Type w} [TopologicalSpace S]
    {L : Set S} {x y : S} (hL : IsLineWithEnds L x y) : L.Infinite := by
  obtain ⟨e,_,_⟩ := hL
  let : Infinite unitInterval := Set.Icc.infinite (show (0 : ℝ)<1 by norm_num)
  have hInf : Infinite L := Infinite.of_injective e e.injective
  exact infinite_coe_iff.mp hInf

/-- A nontrivial abstract graph path can be drawn on any prescribed line,
with the isomorphism taking its stated ends to the line's stated ends. -/
theorem exists_path_drawing_on_line {α : Type u} {β : Type v}
    {S : Type w} [TopologicalSpace S] [T2Space S]
    {G P : Graph α β} {a b : α} (hP : IsGraphPathWithEnds G P a b) (hab : a ≠ b)
    {L : Set S} {x y : S} (hL : IsLineWithEnds L x y) (hxy : x ≠ y) :
    ∃ Γ : GraphDrawing P S, Γ.drawing.U=L ∧
      (∀ z : V(P), z.val=a → (Γ.iso.vertexEquiv z).val=x) ∧
      (∀ z : V(P), z.val=b → (Γ.iso.vertexEquiv z).val=y) := by
  classical
  have hTwo : 2 ≤ V(P).ncard := by
    have h := (Set.one_lt_ncard hP.vertexSet_finite).mpr ⟨a,hP.left_mem,b,hP.right_mem,hab⟩
    omega
  have hPairL : ({x,y} : Set S) ⊆ L := by
    rintro z (rfl | hz)
    · exact hL.left_mem
    · rw [mem_singleton_iff] at hz
      exact hz.symm ▸ hL.right_mem
  have hPairCard : ({x,y} : Set S).ncard ≤ V(P).ncard := by rw [ncard_pair hxy]; exact hTwo
  obtain ⟨A, hAFinite, hPairA, hAL, hACard⟩ := (infinite_of_isLineWithEnds
    hL).exists_superset_ncard_eq
    hPairL ((finite_singleton y).insert x) hPairCard
  have hxA : x ∈ A := hPairA (mem_insert x {y})
  have hyA : y ∈ A := hPairA (mem_insert_of_mem x rfl)
  obtain ⟨D,hDU,hDV⟩ := exists_drawing_on_line A.ncard hL hxy hAFinite hxA hyA hAL le_rfl
  have hDPath : D.IsPathBetween x y := drawing_isPathBetween_of_isLine_U (hDU.symm ▸ hL)
    hxy (hDV.symm ▸ hxA) (hDV.symm ▸ hyA)
  have hDGraphPath : IsGraphPathWithEnds D.toGraph D.toGraph x y := ⟨le_rfl,hDPath⟩
  have hCard : V(P).ncard=V(D.toGraph).ncard := by
    change V(P).ncard=D.V.ncard
    rw [hDV,hACard]
  obtain ⟨φ,hLeft,hRight⟩ := exists_iso_of_paths_of_ncard_eq hP hDGraphPath hCard
  exact ⟨⟨D,φ⟩,hDU,hLeft,hRight⟩

end GraphMinor.GM16
