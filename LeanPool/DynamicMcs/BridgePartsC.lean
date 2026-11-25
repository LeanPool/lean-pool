/-
Copyright (c) 2026 Md Thoriqul Islam Thonmay and Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Md Thoriqul Islam Thonmay, Gregory Morse
-/

-- Modified for Lean Pool.

module

public import LeanPool.DynamicMcs.Exec
public import LeanPool.DynamicMcs.McsInvariant
public import LeanPool.DynamicMcs.CardBridge
public import LeanPool.DynamicMcs.GreedySearch
public import LeanPool.DynamicMcs.BridgePartsA
public import LeanPool.DynamicMcs.BridgePartsB

/-!
# Bridge parts C: per-prefix legality of the executable MCS ordering

This module proves that the executable `mcsOrder` is a legal MCS ordering
of the abstract graph `toUGraph a hsymm hloop` (in the sense of
`UGraph.IsMCSNext` at every prefix).  Concretely:

  `ord_IsMCSNext_each`: for every `i < (mcsOrder a).length`, the `i`-th
  entry of the lifted ordering `ord` is the legal MCS next pick given the
  already-chosen `ord.take i`.

The argument hinges on the foldl invariant of `McsInvariant`:

  at foldl step `k` the state is `st_k = (chosenAt a k, remainingAt a k)` with
  `McListInv n (chosenAt a k, remainingAt a k)`.  When `k < a.length`, the remaining
  list `remainingAt a k` is nonempty and

    `chosenAt a (k+1) = bestPick a (chosenAt a k) (remainingAt a k) :: chosenAt a k`.

From this, `chosenAt a k` is the reverse of the sequence of picks
`P 0, P 1, ..., P (k-1)` (lemma `chosenAt_eq_picks_reverse`).  Because
`mcsOrder a` is `(chosenAt a a.length).reverse`, the `i`-th element of
`mcsOrder a` is exactly `P i` (lemma `mcsOrder_getElem_pick`).  Since
`ord` is the `Fin n`-lifting of `mcsOrder`, the `i`-th entry of `ord` equals
that pick (`ordOf_get_pick`).

Then `McsInvariant.bestPick_IsMCSNext` supplies exactly

    `IsMCSNext G (chosenFin n (chosenAt a i) hlt).toFinset ⟨bestPick, ...⟩`.

The only datum missing is the prefix-Finset equality

    `(ord.take i).toFinset = (CardBridge.chosenFin n (chosenAt a i) hlt).toFinset`

which is the subject of Slice B (`ord_take_finset_eq_chosenFin`).  To keep this
slice independent of Slice B (which may be written in parallel), we take that
equality as an explicit hypothesis `hB_prefix` in the main theorem.  The parent
wires Slice B's lemma in.

Status: COMPLETE.  Zero `sorry`/`axiom`.
-/

@[expose] public section

namespace DynamicMcs

namespace ExecBridge

/-- The chosen prefix `chosenAt a k` is exactly the reverse of the sequence of
picks `P 0, P 1, ..., P (k-1)` where `P j = bestPick a (chosenAt a j) (remainingAt a j)`.
This is the core structural fact: reversing it gives the pick sequence.
-/
lemma chosenAt_eq_picks_reverse (a : Adj n) (ha_len : a.length = n) :
    ∀ k, k ≤ a.length →
      chosenAt a k =
        ((List.range k).map (fun j =>
          bestPick a (chosenAt a j) (remainingAt a j))).reverse := by
  intro k
  induction k with
  | zero =>
      intro _
      simp [chosenAt, stk]
  | succ k ih =>
      intro hk
      have hklt : k < a.length := by omega
      have hkle : k ≤ a.length := by omega
      change (stk a (k + 1)).1 = _
      rw [stk_succ_chosen a ha_len hklt]
      change bestPick a (chosenAt a k) (remainingAt a k) :: chosenAt a k = _
      rw [List.range_succ, List.map_append, List.map_singleton]
      rw [List.reverse_append, List.reverse_singleton]
      have ihk : chosenAt a k =
          ((List.range k).map (fun j =>
          bestPick a (chosenAt a j) (remainingAt a j))).reverse :=
        ih hkle
      rw [ihk]
      simp [List.cons_append]

/-- Position `i` of the executable order equals the pick made at foldl step
`i`. -/
lemma mcsOrder_getElem_pick (a : Adj n) (ha_len : a.length = n) (i : ℕ)
    (hi : i < (mcsOrder a).length) :
    (mcsOrder a)[i]'hi = bestPick a (chosenAt a i) (remainingAt a i) := by
  let picks := (List.range a.length).map (fun j => bestPick a (chosenAt a j) (remainingAt a j))
  have hmorder : mcsOrder a = picks := by
    unfold picks
    rw [mcsOrder_eq_stk_reverse a]
    change (chosenAt a a.length).reverse = _
    rw [chosenAt_eq_picks_reverse a ha_len a.length (le_refl a.length)]
    rw [List.reverse_reverse]
  have hin : i < picks.length := by
    rw [← hmorder]
    exact hi
  have hval : picks[i]'hin = bestPick a (chosenAt a i) (remainingAt a i) := by
    unfold picks
    simp [List.getElem_map, List.getElem_range]
  simp [hmorder, hval]

/-- The `Fin`-lifted ordering, given a bound proof `hbound`.  This mirrors
`BridgePartsA`'s `ord_nodup_len_map` construction. -/
def ordOf (a : Adj n) (hbound : ∀ v, v ∈ mcsOrder a → v < n) : List (Fin n) :=
  (mcsOrder a).attach.map (fun ⟨v, hv⟩ => ⟨v, hbound v hv⟩)

/-- The `Fin`-lifted ordering has the same values as the executable order. -/
lemma ordOf_map_val (a : Adj n) (hbound : ∀ v, v ∈ mcsOrder a → v < n) :
    (ordOf a hbound).map (fun v : Fin n => v.val) = mcsOrder a := by
  unfold ordOf
  simp

/-- The `Fin`-lifted ordering has length `n` (given `ha_len`). -/
lemma ordOf_length (a : Adj n) (ha_len : a.length = n) (hbound : ∀ v, v ∈ mcsOrder a → v < n) :
    (ordOf a hbound).length = n := by
  unfold ordOf
  rw [List.length_map, List.length_attach]
  exact mcsOrder_len a ha_len

/-- At ordinal `i`, the `i`-th entry of the lifted order equals the `Fin`-lift
of the executable pick `bestPick a (chosenAt a i) (remainingAt a i)` made at foldl
step `i`. -/
lemma ordOf_get_pick (a : Adj n) (ha_len : a.length = n)
    (hbound : ∀ v, v ∈ mcsOrder a → v < n)
    (i : ℕ) (hiOrd : i < (ordOf a hbound).length) :
    (ordOf a hbound).get ⟨i, hiOrd⟩ =
      ⟨bestPick a (chosenAt a i) (remainingAt a i),
        hbound (bestPick a (chosenAt a i) (remainingAt a i)) (by
          have hi_morder : i < (mcsOrder a).length := by
            have h1 : (ordOf a hbound).length = n := ordOf_length a ha_len hbound
            have h2 : (mcsOrder a).length = n := mcsOrder_len a ha_len
            simpa [h1, h2] using hiOrd
          have hmc := mcsOrder_getElem_pick a ha_len i hi_morder
          rw [← hmc]
          exact List.getElem_mem hi_morder)⟩ := by
  apply Fin.ext
  have hi_morder : i < (mcsOrder a).length := by
    have h1 : (ordOf a hbound).length = n := ordOf_length a ha_len hbound
    have h2 : (mcsOrder a).length = n := mcsOrder_len a ha_len
    simpa [h1, h2] using hiOrd
  -- value-level: the i-th value of (mcsOrder.attach.map f), where f x = ⟨x.1,
  -- hbound x.1 x.2⟩, equals mcsOrder[i] = the pick.
  have hval : ((ordOf a hbound).get ⟨i, hiOrd⟩).val =
      bestPick a (chosenAt a i) (remainingAt a i) := by
    -- `(ordOf a hbound)` = (mcsOrder a).attach.map f; the i-th value of this
    -- is mcsOrder[i] (the attach lookup), which by mcsOrder_getElem_pick is
    -- exactly the pick at foldl step i.
    simp [ordOf, List.getElem_map, List.getElem_attach, Fin.val_mk,
          mcsOrder_getElem_pick a ha_len i hi_morder]
  exact hval

/-- `chosenFin` is insensitive to the carried bound proof (proof irrelevance of
the `Fin` subtype's index argument, transported through `pmap`).  This lets
Slice B's prefix-Finset equality (stated with `chosenAt_lt ...`) match any
other bound. -/
lemma chosenFin_congr_bound (n : ℕ) (l : List ℕ) (H1 H2 : ∀ v, v ∈ l → v < n) :
    CardBridge.chosenFin n l H1 = CardBridge.chosenFin n l H2 := by
  unfold CardBridge.chosenFin
  apply List.pmap_congr_left
  intro a ha h1 h2
  apply Fin.ext
  rfl

/-! ## Main theorem: per-prefix MCS-next legality

We state the main theorem with the prefix-Finset equality as an explicit
argument `hB_prefix`.  It is the only assumption beyond the standard
well-shapedness ones; the parent wiring Slice B's
`ord_take_finset_eq_chosenFin` into `hB_prefix` completes the slice.
-/

/-- Each prefix of the executable ordering is a legal MCS next step.

Given `a : Adj n` a well-shaped adjacency (`hsymm`, `hloop`, square `ha_len`)
and Slice B's prefix-Finset equality `hB_prefix`, for every
`i < (mcsOrder a).length` the `i`-th entry of the lifted ordering `ord`
is the legal MCS next pick against the prefix `ord.take i`.
-/
theorem ord_IsMCSNext_each (a : Adj n)
    (hsymm : ∀ u v : ℕ, getAdj a u v = getAdj a v u)
    (hloop : ∀ u : ℕ, getAdj a u u = false)
    (ha_len : a.length = n)
    (i : ℕ) (hi_lt : i < (mcsOrder a).length)
    (hB_prefix : ((ordOf a (mcsOrder_mem_lt a ha_len)).take i).toFinset =
        (CardBridge.chosenFin n (chosenAt a i)
          (chosenAt_lt a ha_len i (by
             rw [mcsOrder_len a ha_len] at hi_lt
             omega))).toFinset) :
    UGraph.IsMCSNext (toUGraph a hsymm hloop)
      ((ordOf a (mcsOrder_mem_lt a ha_len)).take i).toFinset
      ((ordOf a (mcsOrder_mem_lt a ha_len)).get ⟨i, by
         have h1 : (ordOf a (mcsOrder_mem_lt a ha_len)).length = n :=
           ordOf_length a ha_len (mcsOrder_mem_lt a ha_len)
         have h2 : (mcsOrder a).length = n := mcsOrder_len a ha_len
         omega⟩) := by
  let hb := mcsOrder_mem_lt a ha_len
  let w := bestPick a (chosenAt a i) (remainingAt a i)
  have hordlen : (ordOf a hb).length = n := ordOf_length a ha_len hb
  have hmlen : (mcsOrder a).length = n := mcsOrder_len a ha_len
  have hi_n : i < n := by omega
  have hi_le : i ≤ n := Nat.le_of_lt hi_n
  have hinv : McsInvariant.McListInv n (chosenAt a i, remainingAt a i) :=
    McsInvariant.foldl_mcsStep_listInv a ha_len i (by omega)
  have hrem : remainingAt a i ≠ [] := remainingAt_ne_of_lt a ha_len (by omega)
  have hnext := McsInvariant.bestPick_IsMCSNext n a hsymm hloop
    (chosenAt a i) (remainingAt a i) hinv hrem
  -- hnext : IsMCSNext G (chosenFin n (chosenAt a i) hinv.2.2.1).toFinset
  --             ⟨w, hinv.2.2.2.1 w (bestPick_lex ...).1⟩
  rw [hB_prefix]
  have hcf : CardBridge.chosenFin n (chosenAt a i)
        (chosenAt_lt a ha_len i (by omega))
      = CardBridge.chosenFin n (chosenAt a i) hinv.2.2.1 :=
    chosenFin_congr_bound n (chosenAt a i) _ _
  rw [hcf]
  -- Now the Finset matches hnext's.  Handle the vertex.
  have hidx : i < (ordOf a hb).length := by omega
  have hwrem : w ∈ remainingAt a i :=
    (BridgeSteps.bestPick_lex a (chosenAt a i) (remainingAt a i) hrem).1
  have hvert : (ordOf a hb).get ⟨i, hidx⟩ = ⟨w, hinv.2.2.2.1 w hwrem⟩ := by
    have hget := ordOf_get_pick a ha_len hb i hidx
    -- hget : (ordOf a hb).get ⟨i,hidx⟩ = ⟨w, hb w _⟩; both vertices have value w.
    apply Fin.ext
    rw [hget]
  -- The goal's vertex is `(ordOf a hb).get ⟨i, goal_idx⟩` where goal_idx is
  -- the inline `by ... omega`; it equals `(ordOf a hb).get ⟨i, hidx⟩` by
  -- proof irrelevance of the index (list.get is extensional in the index).
  -- Rewrite that argument to hvert's LHS, then use hvert.
  rw [(show (ordOf a hb).get ⟨i, by
        have h1 : (ordOf a (mcsOrder_mem_lt a ha_len)).length = n :=
          ordOf_length a ha_len (mcsOrder_mem_lt a ha_len)
        have h2 : (mcsOrder a).length = n := mcsOrder_len a ha_len
        omega⟩ = (ordOf a hb).get ⟨i, hidx⟩ by
      have hp : (by
        have h1 : (ordOf a (mcsOrder_mem_lt a ha_len)).length = n :=
          ordOf_length a ha_len (mcsOrder_mem_lt a ha_len)
        have h2 : (mcsOrder a).length = n := mcsOrder_len a ha_len
        omega : i < (ordOf a hb).length)
          = hidx := Subsingleton.elim _ _
      rw [hp])]
  rw [hvert]
  -- goal: IsMCSNext G cf.toFinset ⟨w, hinv.2.2.2.1 w _⟩ = hnext (up to Fin index)
  simpa [Fin.ext] using hnext

end ExecBridge
end DynamicMcs
