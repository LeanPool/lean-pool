/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovSeries

/-!
# Round casts and agreement of certified series

General facts extracted from the credited Trellis proof families at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Change only the round index of series data along an equality. -/
abbrev TashkinovSeriesData.castRounds {V E : Type*} {G : LooplessMultigraph V E}
    {k r s : ℕ} {e0 : E} (data : TashkinovSeriesData G k r e0) (rounds : r = s) :
    TashkinovSeriesData G k s e0 := rounds ▸ data

/-- Change only the round index of a certified series along an equality. -/
abbrev TashkinovSeries.castRounds {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    {G : LooplessMultigraph V E} {k r s : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
    (series : TashkinovSeries G k r e0 input) (rounds : r = s) :
    TashkinovSeries G k s e0 input := rounds ▸ series

section CertifiedSeries

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    {G : LooplessMultigraph V E} {k r s : ℕ} {e0 : E} {input : PartialEdgeColoring E k}

/-- Round casts commute with the data projection. -/
@[simp] theorem TashkinovSeries.castRounds_data
    (series : TashkinovSeries G k r e0 input) (rounds : r = s) :
    (series.castRounds rounds).data = series.data.castRounds rounds := by
  cases rounds
  rfl

/-- Round casts commute with every tree projection. -/
theorem TashkinovSeries.castRounds_tree
    (series : TashkinovSeries G k r e0 input) (rounds : r = s) (i : Fin (s + 2)) :
    (series.castRounds rounds).data.tree i =
      series.data.tree (Fin.cast (congrArg (fun n : ℕ => n + 2) rounds.symm) i) := by
  cases rounds
  rfl

/-- Round casts commute with every coloring projection. -/
theorem TashkinovSeries.castRounds_coloring
    (series : TashkinovSeries G k r e0 input) (rounds : r = s) (i : Fin (s + 1)) :
    (series.castRounds rounds).data.coloring i =
      series.data.coloring (Fin.cast (congrArg (fun n : ℕ => n + 1) rounds.symm) i) := by
  cases rounds
  rfl

/-- Round casts commute with every stored-color projection. -/
theorem TashkinovSeries.castRounds_stored
    (series : TashkinovSeries G k r e0 input) (rounds : r = s) (i : Fin (s + 1)) :
    (series.castRounds rounds).data.stored i =
      series.data.stored (Fin.cast (congrArg (fun n : ℕ => n + 1) rounds.symm) i) := by
  cases rounds
  rfl

/-- Round casts commute with every connecting-edge projection. -/
theorem TashkinovSeries.castRounds_connectingEdges
    (series : TashkinovSeries G k r e0 input) (rounds : r = s) (i : Fin (s + 1)) :
    (series.castRounds rounds).data.connectingEdges i =
      series.data.connectingEdges (Fin.cast (congrArg (fun n : ℕ => n + 1) rounds.symm) i) := by
  cases rounds
  rfl

/-- Round casts commute with every extension-kind projection. -/
theorem TashkinovSeries.castRounds_kind
    (series : TashkinovSeries G k r e0 input) (rounds : r = s) (i : Fin (s + 1)) :
    (series.castRounds rounds).data.kind i =
      series.data.kind (Fin.cast (congrArg (fun n : ℕ => n + 1) rounds.symm) i) := by
  cases rounds
  rfl

/-- Round casts preserve the last tree. -/
theorem TashkinovSeries.castRounds_finalTree
    (series : TashkinovSeries G k r e0 input) (rounds : r = s) :
    (series.castRounds rounds).data.tree (Fin.last (s + 1)) =
      series.data.tree (Fin.last (r + 1)) := by
  cases rounds
  rfl

/-- Round casts preserve the last coloring. -/
theorem TashkinovSeries.castRounds_finalColoring
    (series : TashkinovSeries G k r e0 input) (rounds : r = s) :
    (series.castRounds rounds).data.coloring (Fin.last s) = series.data.coloring (Fin.last r) := by
  cases rounds
  rfl

/-- Round casts preserve the penultimate tree. -/
theorem TashkinovSeries.castRounds_penultimateTree
    (series : TashkinovSeries G k r e0 input) (rounds : r = s) :
    (series.castRounds rounds).data.tree (Fin.last s).castSucc =
      series.data.tree (Fin.last r).castSucc := by
  cases rounds
  rfl

end CertifiedSeries

variable {V E : Type*} {G : LooplessMultigraph V E} {k r s : ℕ} {e0 : E}

/-- Agreement of old metadata and the new terminal entry gives agreement after a round cast. -/
theorem TashkinovSeriesData.castMetadataAgreement
    (original : TashkinovSeriesData G k s e0)
    (extended : TashkinovSeriesData G k (r + 1) e0) (rounds : r + 1 = s)
    (earlierAgreement : ∀ i : Fin (r + 1),
      extended.stored i.castSucc = original.stored (Fin.castLE (by omega) i) ∧
        extended.connectingEdges i.castSucc = original.connectingEdges (Fin.castLE (by omega) i) ∧
        extended.kind i.castSucc = original.kind (Fin.castLE (by omega) i))
    (last : extended.stored (Fin.last (r + 1)) = original.stored (Fin.last s) ∧
      extended.connectingEdges (Fin.last (r + 1)) = original.connectingEdges (Fin.last s) ∧
      extended.kind (Fin.last (r + 1)) = original.kind (Fin.last s)) :
    ∀ i : Fin (s + 1),
      (extended.castRounds rounds).stored i = original.stored i ∧
        (extended.castRounds rounds).connectingEdges i = original.connectingEdges i ∧
        (extended.castRounds rounds).kind i = original.kind i := by
  cases rounds
  intro i
  exact Fin.lastCases last (fun j => earlierAgreement j) i

/-- Earlier tree agreement and penultimate agreement determine all ladder trees after a cast. -/
theorem TashkinovSeriesData.castTreeAgreement
    (original : TashkinovSeriesData G k s e0)
    (extended : TashkinovSeriesData G k (r + 1) e0) (rounds : r + 1 = s)
    (earlierAgreement : ∀ i : Fin r,
      extended.tree i.succ.castSucc.castSucc =
        original.tree (Fin.castLE (by omega) i.succ.castSucc))
    (penultimate : (extended.castRounds rounds).tree (Fin.last s).castSucc =
      original.tree (Fin.last s).castSucc) :
    ∀ i : Fin s, (extended.castRounds rounds).tree i.succ.castSucc =
      original.tree i.succ.castSucc := by
  cases rounds
  intro i
  exact Fin.lastCases penultimate (fun j => earlierAgreement j) i

end GoldbergSeymour

end
