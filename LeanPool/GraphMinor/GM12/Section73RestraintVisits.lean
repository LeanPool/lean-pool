/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73PieceWalk
public import LeanPool.GraphMinor.GM12.Section73ConnectorVisits
import LeanPool.GraphMinor.GM11.Section88
import LeanPool.GraphMinor.GM11.Section85
import LeanPool.GraphMinor.GM11.Ties

/-!
# Two-visit witnesses from XI (9.2)

XII (7.3), page 262, selects its metric witness by XI (9.2).
We use the proved piece construction in that argument. With one
piece, normalize its boundary walk. With two pieces, normalize
both boundary walks and replace their connector by a shortest
path between their vertex sets. These replacements preserve the
perimeter budget and the containment of the two atoms in the
inside. The connector visit lemma then gives at most two visits
to each vertex.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- The two-visit consequence of the proof of XI (9.2) used by
XII (7.3), page 262: two atoms in a restraint are enclosed by a
walk within its perimeter budget, visiting each vertex at most
twice. All pieces and their connecting path are constructed by
the proved lemmas of XI (9.2). -/
theorem exists_restraint_walk_with_two_visit_bound
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {K : Drawing S} {k : ℕ} {ins : Drawing S → Set S}
    (hs : IsSlope K k ins) {a b Y : Set S} (ha : a ∈ K.A) (hb : b ∈ K.A)
    (hY : IsRestraint K ins k Y) (haY : a ⊆ Y) (hbY : b ⊆ Y) :
    ∃ (p : S) (W : GraphWalk K.toGraph p p), W.length ≤ perimeterWalkLength K Y ∧
      W.length < k ∧ a ⊆ insWalk ins K W ∧ b ⊆ insWalk ins K W ∧
      ∀ v, walkVertexCount v W ≤ 2 := by
  rcases exists_pieces hS hs ha hb hY haY hbY with
    ⟨A, G, hP, haA, hbA⟩ | ⟨A, G, B, H, hP, hR, haA, hbB, _, hlink⟩
  · obtain ⟨p, hp⟩ := hP.Vne
    obtain ⟨Z, hZ, hcnt⟩ := hP.walk p hp
    have hZlen : Z.length ≤ perimeterWalkLength K Y :=
      length_le_of_count hS hY (fun e he => mem_E_of_mem_edges Z he) hcnt
    obtain ⟨W, hW, hlen, hcount⟩ := exists_piece_walk_with_visit_bound hP hp Z hZ
    have hinside : A ⊆ insWalk ins K W := by
      simpa only [insWalk, hW] using hP.sub_ins
    exact ⟨p, W, hlen.trans hZlen, (hlen.trans hZlen).trans_lt hY.length_lt,
      haA.trans hinside, hbA.trans hinside, fun v => (hcount v).trans (by decide)⟩
  · obtain ⟨a₀, b₀, Q₀, Z₀, R₀, ha₀, hb₀, hZ₀, hR₀, hbudget⟩ := hlink
    obtain ⟨p, hp, q, hq, Q, hQ, hmin, hQG, hQH⟩ :=
      exists_shortest (A := G.V) (B := H.V) ⟨a₀, ha₀, b₀, hb₀, ⟨Q₀⟩⟩
    have hQlen := hmin a₀ ha₀ b₀ hb₀ Q₀
    obtain ⟨P, hPG, hPlen, hPcount⟩ := exists_piece_walk_with_visit_bound hP hp Z₀ hZ₀
    obtain ⟨R, hRH, hRlen, hRcount⟩ := exists_piece_walk_with_visit_bound hR hq R₀ hR₀
    let W := P.append (Q.append (R.append Q.reverse))
    have hlen : W.length ≤ perimeterWalkLength K Y := by
      have hWlen : W.length = P.length + Q.length + R.length + Q.length := by
        simp only [W, GraphWalk.length_append, GraphWalk.length_reverse]
        omega
      omega
    have hGW : G.IsSubdrawing (walkDrawing K W) := by
      rw [← hPG]
      apply walkDrawing_mono
      · intro x hx
        exact (GraphWalk.mem_support_append _ _).mpr (Or.inl hx)
      · intro e he
        change e ∈ (P.append (Q.append (R.append Q.reverse))).edges
        rw [GraphWalk.edges_append]
        exact List.mem_append_left _ he
    have hHW : H.IsSubdrawing (walkDrawing K W) := by
      rw [← hRH]
      apply walkDrawing_mono
      · intro x hx
        exact (GraphWalk.mem_support_append _ _).mpr (Or.inr
          ((GraphWalk.mem_support_append _ _).mpr (Or.inr
            ((GraphWalk.mem_support_append _ _).mpr (Or.inl hx)))))
      · intro e he
        simp only [W, GraphWalk.edges_append, List.mem_append]
        exact Or.inr (Or.inr (Or.inl he))
    have hAin : A ⊆ insWalk ins K W := hP.sub_ins.trans (insOf_mono hGW)
    have hBin : B ⊆ insWalk ins K W := hR.sub_ins.trans (insOf_mono hHW)
    refine ⟨p, W, hlen, hlen.trans_lt hY.length_lt, haA.trans hAin, hbB.trans hBin, ?_⟩
    intro v
    apply walkVertexCount_join_le_two P R Q hPcount hRcount hQ
    · intro x hxQ hxP
      apply hQG x hxQ
      rw [← hPG, walkDrawing_V]
      exact hxP
    · intro x hxQ hxR
      apply hQH x hxQ
      rw [← hRH, walkDrawing_V]
      exact hxR

end GraphMinor.GM12
