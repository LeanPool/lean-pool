/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Word.Pres


/-!
# Theorem W, stage B1: the priority queue

Every value the queue writes is a chunk index or a bucket (a chunk size) passed as an argument,
`0`, or a value read from the queue's arrays (class R). So each operation keeps `WB K` once its
arguments are below `2^K`.
-/


@[expose] public section

namespace OrderMaintenance.Proof.Word

open OrderMaintenance.Model OrderMaintenance.Proof

variable {K : Nat} {P0 : Params}

theorem ht_pqLinkAfter {s p : Nat} (hs : s < 2 ^ K) (hp : p < 2 ^ K) :
    HT K P0 (pqLinkAfter s p) (fun _ => True) := by
  unfold pqLinkAfter; ht; all_goals htfin

theorem ht_pqAdd {c s p : Nat} (hc : c < 2 ^ K) (hs : s < 2 ^ K) (hp : p < 2 ^ K) :
    HT K P0 (pqAdd c s p) (fun _ => True) := by
  unfold pqAdd; ht [ht_pqLinkAfter hs hp]; all_goals htfin
theorem ht_pqDel (c : Nat) : HT K P0 (pqDel c) (fun _ => True) := by
  unfold pqDel; ht; all_goals htfin

theorem ht_pqInsertScan {c s : Nat} (hc : c < 2 ^ K) (hs : s < 2 ^ K) :
    HT K P0 (pqInsertScan c s) (fun _ => True) := by
  unfold pqInsertScan
  refine HT.bind HT.get fun st _ => ?_
  refine HT.bind (Q := fun p => p < 2 ^ K) (HT.forIn_list _ _ (by omega) fun _ b hb => ?_)
    fun p hp => ht_pqAdd hc hs (by split <;> first | exact hp | exact pos K)
  dsimp only
  split
  · exact HT.pure (by change b - 1 < 2 ^ K; omega)
  · exact HT.pure hb

theorem ht_pqAdjust {c old new : Nat} (hc : c < 2 ^ K) (ho : old < 2 ^ K) (hn : new < 2 ^ K) :
    HT K P0 (pqAdjust c old new) (fun _ => True) := by
  unfold pqAdjust
  ht [ht_pqInsertScan hc hn, ht_pqDel c, ht_pqAdd hc hn (pos K)]
  all_goals exact ht_pqAdd hc hn (by vb)

theorem ht_pqEnterIfAbove {c : Nat} (hc : c < 2 ^ K) : HT K P0 (pqEnterIfAbove c) (fun _ =>
  True) := by
  unfold pqEnterIfAbove
  refine HT.bind (HT.getC c) fun C hC => HT.bind HT.getP fun P _ => ?_
  split
  · exact ht_pqInsertScan hc (by vb)
  · exact HT.pure trivial

theorem ht_pqPopMax : HT K P0 pqPopMax (· < 2 ^ K) := by
  unfold pqPopMax
  ht [ht_pqDel _]
  all_goals htfin

end OrderMaintenance.Proof.Word
