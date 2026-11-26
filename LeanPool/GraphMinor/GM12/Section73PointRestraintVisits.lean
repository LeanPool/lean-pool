/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73RestraintVisits
import LeanPool.GraphMinor.GM11.Section85
import LeanPool.GraphMinor.GM11.Section88
import LeanPool.GraphMinor.GM11.Ties

/-!
# A one-visit witness for a distinguished vertex

For XII (7.3)(ii), page 262, one of the two atoms corresponds
to the merged hub vertex. Use the pieces in the proof of XI
(9.2), as in the two-visit construction. If the first piece
already encloses the hub, its own boundary walk suffices. If the
connector reaches the hub, stop it at the hub and return, omitting
the second piece. Otherwise only the second piece can visit the
hub. These choices give at most one hub visit within the same
perimeter budget.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- The distinguished-vertex refinement of the XI (9.2) witness
selection used in XII (7.3)(ii), page 262. -/
theorem exists_restraint_walk_with_one_point_visit_bound
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {K : Drawing S} {k : ℕ} {ins : Drawing S → Set S}
    (hs : IsSlope K k ins) {a Y : Set S} {v : S} (ha : a ∈ K.A)
    (hv : ({v} : Set S) ∈ K.A) (hY : IsRestraint K ins k Y)
    (haY : a ⊆ Y) (hvY : v ∈ Y) :
    ∃ (p : S) (W : GraphWalk K.toGraph p p), W.length ≤ perimeterWalkLength K Y ∧
      W.length < k ∧ a ⊆ insWalk ins K W ∧ v ∈ insWalk ins K W ∧
      walkVertexCount v W ≤ 1 := by
  rcases exists_pieces hS hs ha hv hY haY (singleton_subset_iff.mpr hvY) with
    ⟨A, G, hP, haA, hvA⟩ | ⟨A, G, B, H, hP, hR, haA, hvB, _, hlink⟩
  · obtain ⟨p, hp⟩ := hP.Vne
    obtain ⟨Z, hZ, hcnt⟩ := hP.walk p hp
    have hZlen : Z.length ≤ perimeterWalkLength K Y :=
      length_le_of_count hS hY (fun e he => mem_E_of_mem_edges Z he) hcnt
    obtain ⟨W, hW, hlen, hcount⟩ := exists_piece_walk_with_visit_bound hP hp Z hZ
    have hinside : A ⊆ insWalk ins K W := by simpa only [insWalk, hW] using hP.sub_ins
    exact ⟨p, W, hlen.trans hZlen, (hlen.trans hZlen).trans_lt hY.length_lt,
      haA.trans hinside, hinside (hvA (mem_singleton v)), hcount v⟩
  · obtain ⟨a₀, b₀, Q₀, Z₀, R₀, ha₀, hb₀, hZ₀, hR₀, hbudget⟩ := hlink
    obtain ⟨p, hp, q, hq, Q, hQ, hmin, _, _⟩ :=
      exists_shortest (A := G.V) (B := H.V) ⟨a₀, ha₀, b₀, hb₀, ⟨Q₀⟩⟩
    have hQlen := hmin a₀ ha₀ b₀ hb₀ Q₀
    obtain ⟨P, hPG, hPlen, hPcount⟩ := exists_piece_walk_with_visit_bound hP hp Z₀ hZ₀
    obtain ⟨R, hRH, hRlen, hRcount⟩ := exists_piece_walk_with_visit_bound hR hq R₀ hR₀
    have hAin : A ⊆ insWalk ins K P := by simpa only [insWalk, hPG] using hP.sub_ins
    have hBin : B ⊆ insWalk ins K R := by simpa only [insWalk, hRH] using hR.sub_ins
    by_cases hvP : v ∈ insWalk ins K P
    · have hlen : P.length ≤ perimeterWalkLength K Y := by omega
      exact ⟨p, P, hlen, hlen.trans_lt hY.length_lt, haA.trans hAin, hvP, hPcount v⟩
    have hvPs : v ∉ P.support := by
      intro h
      exact hvP (Or.inl ((mem_walkDrawing_U K P).mpr (Or.inl h)))
    have hPzero := walkVertexCount_eq_zero_of_notMem_support P hvPs
    by_cases hvQ : v ∈ Q.support
    · obtain ⟨L, M, hQLM⟩ := Q.exists_append_of_mem hvQ
      have hLsimple : L.IsSimple := by
        have hn : Q.support.Nodup := hQ
        rw [hQLM, GraphWalk.support_append] at hn
        exact hn.of_append_left
      have hLlen : L.length ≤ Q.length := by
        rw [hQLM, GraphWalk.length_append]
        exact Nat.le_add_right _ _
      let W := P.append (L.append L.reverse)
      have hlen : W.length ≤ perimeterWalkLength K Y := by
        have hWlen : W.length = P.length + 2 * L.length := by
          simp only [W, GraphWalk.length_append, GraphWalk.length_reverse]
          omega
        omega
      have hPW : (walkDrawing K P).IsSubdrawing (walkDrawing K W) := by
        apply walkDrawing_mono
        · intro x hx; exact (GraphWalk.mem_support_append _ _).mpr (Or.inl hx)
        · intro e he; simp only [W, GraphWalk.edges_append, List.mem_append]; exact Or.inl he
      have hvW : v ∈ W.support := (GraphWalk.mem_support_append _ _).mpr (Or.inr
        ((GraphWalk.mem_support_append _ _).mpr (Or.inl L.end_mem_support)))
      refine ⟨p, W, hlen, hlen.trans_lt hY.length_lt,
        (haA.trans hAin).trans (insOf_mono hPW),
        Or.inl ((mem_walkDrawing_U K W).mpr (Or.inl hvW)), ?_⟩
      have hback := (walkVertexCount_backtrack_bounds L hLsimple v).2 (Or.inr rfl)
      change walkVertexCount v (P.append (L.append L.reverse)) ≤ 1
      rw [walkVertexCount_append, hPzero, Nat.zero_add]
      exact hback
    · let W := P.append (Q.append (R.append Q.reverse))
      have hlen : W.length ≤ perimeterWalkLength K Y := by
        have hWlen : W.length = P.length + Q.length + R.length + Q.length := by
          simp only [W, GraphWalk.length_append, GraphWalk.length_reverse]
          omega
        omega
      have hPW : (walkDrawing K P).IsSubdrawing (walkDrawing K W) := by
        apply walkDrawing_mono
        · intro x hx; exact (GraphWalk.mem_support_append _ _).mpr (Or.inl hx)
        · intro e he; simp only [W, GraphWalk.edges_append, List.mem_append]; exact Or.inl he
      have hRW : (walkDrawing K R).IsSubdrawing (walkDrawing K W) := by
        apply walkDrawing_mono
        · intro x hx
          exact (GraphWalk.mem_support_append _ _).mpr (Or.inr
            ((GraphWalk.mem_support_append _ _).mpr (Or.inr
              ((GraphWalk.mem_support_append _ _).mpr (Or.inl hx)))))
        · intro e he
          simp only [W, GraphWalk.edges_append, List.mem_append]
          exact Or.inr (Or.inr (Or.inl he))
      refine ⟨p, W, hlen, hlen.trans_lt hY.length_lt,
        (haA.trans hAin).trans (insOf_mono hPW),
        insOf_mono hRW (hBin (hvB (mem_singleton v))), ?_⟩
      have hback := walkVertexCount_backtrack_eq_zero_of_notMem_support Q hvQ
      have hr := hRcount v
      simp only [walkVertexCount_append] at hback ⊢
      change walkVertexCount v (P.append (Q.append (R.append Q.reverse))) ≤ 1
      simp only [walkVertexCount_append]
      omega

end GraphMinor.GM12
