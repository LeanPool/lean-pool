/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.Defs
public import LeanPool.GraphMinor.GM11.Defs
import LeanPool.GraphMinor.GM11.Walks
import LeanPool.GraphMinor.GM11.Section6

/-!
# Passing between graph paths and drawing paths

A path subgraph of the graph of a drawing traces a path subdrawing,
with the same graph. This lets us trim battlefield paths as graph
paths and then use their point sets in XVI (8.1), Claim (11).
-/

public section
namespace GraphMinor.GM16
open Set Graph GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM11
universe u
variable {S : Type u} [TopologicalSpace S]

/-- Reversing a drawing path exchanges its two ends. -/
theorem drawingPath_symm {J : Drawing S} {a b : S} (hP : J.IsPathBetween a b) :
    J.IsPathBetween b a := by
  obtain ⟨W, hW, hV, hE⟩ := hP
  refine ⟨W.reverse, hW.reverse, ?_, ?_⟩
  · simpa only [GraphWalk.support_reverse, List.mem_reverse] using hV
  · simpa only [GraphWalk.edges_reverse, List.mem_reverse] using hE

/-- A subdrawing gives a subgraph with the same vertices and edges. -/
theorem toGraph_le_of_isSubdrawing {H J : Drawing S} (hJ : J.IsSubdrawing H) :
    J.toGraph ≤ H.toGraph :=
  hJ.toGraph_le

/-- A drawing path is a graph path in every drawing containing it. -/
theorem graphPath_of_drawingPath {H J : Drawing S} {a b : S}
    (hJ : J.IsSubdrawing H) (hP : J.IsPathBetween a b) :
    IsGraphPathWithEnds H.toGraph J.toGraph a b :=
  ⟨toGraph_le_of_isSubdrawing hJ, hP⟩

/-- A graph path in a drawing traces a path subdrawing with exactly
that graph. -/
theorem exists_drawing_of_graphPath [T1Space S] {H : Drawing S}
    {P : Graph S (Set S)} {a b : S} (hP : IsGraphPathWithEnds H.toGraph P a b) :
    ∃ J : Drawing S, J.IsPathBetween a b ∧ J.IsSubdrawing H ∧ J.toGraph = P := by
  obtain ⟨hPH, W, hW, hV, hE⟩ := hP
  obtain ⟨W', hs, he⟩ := W.exists_transfer
    (fun _ _ _ _ hl => hPH.isLink_mono hl)
    (fun _ hx => hPH.vertexSet_mono (W.mem_vertexSet_of_mem_support hx))
  have hSimple : W'.IsSimple := by
    change W'.support.Nodup
    rw [hs]
    exact hW
  let J := walkDrawing H W'
  have hJH : J.IsSubdrawing H := walkDrawing_isSubdrawing H W'
  refine ⟨J, walkDrawing_isPathBetween H hSimple, hJH, ?_⟩
  apply Compatible.ext _ _ (Compatible.of_le_le (toGraph_le_of_isSubdrawing hJH) hPH)
  · change J.V = V(P)
    rw [show J.V = {x | x ∈ W'.support} from walkDrawing_V H W', hs, hV]
  · change J.E = E(P)
    rw [show J.E = {e | e ∈ W'.edges} from walkDrawing_E H W', he, hE]

end GraphMinor.GM16
