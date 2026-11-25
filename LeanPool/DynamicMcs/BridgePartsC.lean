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

/-!
# Bridge parts C: per-prefix legality of the executable MCS ordering

This module proves that the executable `Exec.mcsOrder` is a legal MCS ordering
of the abstract graph `Exec.toUGraph a hsymm hloop` (in the sense of
`Greedy.UGraph.IsMCSNext` at every prefix).  Concretely:

  `ord_IsMCSNext_each`: for every `i < (Exec.mcsOrder a).length`, the `i`-th
  entry of the lifted ordering `ord` is the legal MCS next pick given the
  already-chosen `ord.take i`.

The argument hinges on the foldl invariant of `McsInvariant`:

  at foldl step `k` the state is `st_k = (chosenK a k, remK a k)` with
  `McListInv n (chosenK a k, remK a k)`.  When `k < a.length`, the remaining
  list `remK a k` is nonempty and

    `chosenK a (k+1) = bestPick a (chosenK a k) (remK a k) :: chosenK a k`.

From this, `chosenK a k` is the reverse of the sequence of picks
`P 0, P 1, ..., P (k-1)` (lemma `chosenK_eq_picks_reverse`).  Because
`Exec.mcsOrder a` is `(chosenK a a.length).reverse`, the `i`-th element of
`Exec.mcsOrder a` is exactly `P i` (lemma `mcsOrder_getElem_pick`).  Since
`ord` is the `Fin n`-lifting of `mcsOrder`, the `i`-th entry of `ord` equals
that pick (`ordOf_get_pick`).

Then `McsInvariant.bestPick_IsMCSNext` supplies exactly

    `IsMCSNext G (chosenFin n (chosenK a i) hlt).toFinset ⟨bestPick, ...⟩`.

The only datum missing is the prefix-Finset equality

    `(ord.take i).toFinset = (CardBridge.chosenFin n (chosenK a i) hlt).toFinset`

which is the subject of Slice B (`ord_take_finset_eq_chosenFin`).  To keep this
slice independent of Slice B (which may be written in parallel), we take that
equality as an explicit hypothesis `hB_prefix` in the main theorem.  The parent
wires Slice B's lemma in.

Status: COMPLETE.  Zero `sorry`/`axiom`.
-/

@[expose] public section

open DynamicMcs.Greedy

namespace DynamicMcs

namespace ExecBridge

/-- The foldl state after `k` steps of the executable MCS loop (seed
`([], List.range a.length)`). -/
def stK (a : Adj n) (k : ℕ) : List ℕ × List ℕ :=
  (List.range k).foldl (fun s _ => Exec.mcsStep a s) ([], List.range a.length)

/-- The chosen-prefix (in reverse) after `k` foldl steps. -/
def chosenK (a : Adj n) (k : ℕ) : List ℕ := (stK a k).1
/-- The remaining list after `k` foldl steps. -/
def remK (a : Adj n) (k : ℕ) : List ℕ := (stK a k).2

/-- The `McListInv` invariant holds at foldl step `k` (for `k ≤ n`). -/
lemma invK (a : Adj n) (ha_len : a.length = n) (k : ℕ) (hk : k ≤ n) :
    McsInvariant.McListInv n (chosenK a k, remK a k) := by
  unfold chosenK remK stK
  exact McsInvariant.foldl_mcsStep_listInv a ha_len k (by omega)

/-- At foldl step `k`, the length of the chosen prefix is `k` and the length
of the remaining list is `n - k`. -/
lemma lenK (a : Adj n) (ha_len : a.length = n) (k : ℕ) (hk : k ≤ n) :
    (chosenK a k).length = k ∧ (remK a k).length = n - k := by
  unfold chosenK remK stK
  have hr : List.range a.length = List.range n := congrArg List.range ha_len
  have hcore := McsInvariant.foldl_mcsStep_len_core a k hk
  simpa [hr] using hcore

/-- When `k < n`, the remaining list at foldl step `k` is nonempty. -/
lemma remK_ne (a : Adj n) (ha_len : a.length = n) (k : ℕ) (hk : k < n) :
    remK a k ≠ [] := by
  intro hempty
  have hlen := (lenK a ha_len k (Nat.le_of_lt hk)).2
  rw [hempty] at hlen
  simp at hlen
  omega

/-- All ids in the chosen prefix at foldl step `k` are `< n`. -/
lemma chosenK_lt (a : Adj n) (ha_len : a.length = n) (k : ℕ) (hk : k ≤ n) :
    ∀ v ∈ chosenK a k, v < n := (invK a ha_len k hk).2.2.1

/-- Applying one more `mcsStep` to the state at foldl step `k` prepends the
pick `bestPick` to the chosen prefix (nonempty-`rem` case). -/
lemma stK_succ (a : Adj n) (ha_len : a.length = n) (k : ℕ) (hk : k < n) :
    stK a (k + 1) =
      (Exec.bestPick a (chosenK a k) (remK a k) :: chosenK a k,
       (remK a k).erase (Exec.bestPick a (chosenK a k) (remK a k))) := by
  have hrecur : stK a (k + 1) = Exec.mcsStep a (stK a k) := by
    unfold stK
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
  rw [hrecur]
  rw [McsInvariant.mcsStep_eq a (stK a k).1 (stK a k).2 (remK_ne a ha_len k hk)]
  rfl

/-- The state at step `k+1` has chosen prefix `bestPick :: chosenK a k`. -/
lemma chosenK_succ (a : Adj n) (ha_len : a.length = n) (k : ℕ) (hk : k < n) :
    chosenK a (k + 1) = Exec.bestPick a (chosenK a k) (remK a k) :: chosenK a k := by
  rw [chosenK, stK_succ a ha_len k hk]

/-- `Exec.mcsOrder a` is the reverse of the terminal chosen prefix. -/
lemma mcsOrder_eq_reverse_alt (a : Adj n) :
    Exec.mcsOrder a = (chosenK a a.length).reverse := by
  unfold Exec.mcsOrder chosenK stK
  rfl

/-- The chosen prefix `chosenK a k` is exactly the reverse of the sequence of
picks `P 0, P 1, ..., P (k-1)` where `P j = bestPick a (chosenK a j) (remK a j)`.
This is the core structural fact: reversing it gives the pick sequence.
-/
lemma chosenK_eq_picks_reverse (a : Adj n) (ha_len : a.length = n) :
    ∀ k, k ≤ a.length →
      chosenK a k =
        ((List.range k).map (fun j => Exec.bestPick a (chosenK a j) (remK a j))).reverse := by
  intro k
  induction k with
  | zero =>
      intro _
      simp [chosenK, stK]
  | succ k ih =>
      intro hk
      have hklt : k < a.length := by omega
      have hkltn : k < n := by rw [← ha_len]; exact hklt
      have hkle : k ≤ a.length := by omega
      rw [chosenK_succ a ha_len k hkltn]
      rw [List.range_succ, List.map_append, List.map_singleton]
      rw [List.reverse_append, List.reverse_singleton]
      have ihk : chosenK a k =
          ((List.range k).map (fun j => Exec.bestPick a (chosenK a j) (remK a j))).reverse :=
        ih hkle
      rw [ihk]
      simp [List.cons_append]

/-- Position `i` of the executable order equals the pick made at foldl step
`i`. -/
lemma mcsOrder_getElem_pick (a : Adj n) (ha_len : a.length = n) (i : ℕ)
    (hi : i < (Exec.mcsOrder a).length) :
    (Exec.mcsOrder a)[i]'hi = Exec.bestPick a (chosenK a i) (remK a i) := by
  let picks := (List.range a.length).map (fun j => Exec.bestPick a (chosenK a j) (remK a j))
  have hmorder : Exec.mcsOrder a = picks := by
    unfold picks
    rw [mcsOrder_eq_reverse_alt a]
    rw [chosenK_eq_picks_reverse a ha_len a.length (le_refl a.length)]
    rw [List.reverse_reverse]
  have hin : i < picks.length := by
    rw [← hmorder]
    exact hi
  have hval : picks[i]'hin = Exec.bestPick a (chosenK a i) (remK a i) := by
    unfold picks
    simp [List.getElem_map, List.getElem_range]
  simp [hmorder, hval]

/-- The `Fin`-lifted ordering, given a bound proof `hbound`.  This mirrors
`BridgePartsA`'s `ord_nodup_len_map` construction. -/
def ordOf (a : Adj n) (hbound : ∀ v, v ∈ Exec.mcsOrder a → v < n) : List (Fin n) :=
  (Exec.mcsOrder a).attach.map (fun ⟨v, hv⟩ => ⟨v, hbound v hv⟩)

/-- The `Fin`-lifted ordering has the same values as the executable order. -/
lemma ordOf_map_val (a : Adj n) (hbound : ∀ v, v ∈ Exec.mcsOrder a → v < n) :
    (ordOf a hbound).map (fun v : Fin n => v.val) = Exec.mcsOrder a := by
  unfold ordOf
  simp

/-- The `Fin`-lifted ordering has length `n` (given `ha_len`). -/
lemma ordOf_length (a : Adj n) (ha_len : a.length = n) (hbound : ∀ v, v ∈ Exec.mcsOrder a → v < n) :
    (ordOf a hbound).length = n := by
  unfold ordOf
  rw [List.length_map, List.length_attach]
  exact mcsOrder_len a ha_len

/-- At ordinal `i`, the `i`-th entry of the lifted order equals the `Fin`-lift
of the executable pick `bestPick a (chosenK a i) (remK a i)` made at foldl
step `i`. -/
lemma ordOf_get_pick (a : Adj n) (ha_len : a.length = n)
    (hbound : ∀ v, v ∈ Exec.mcsOrder a → v < n)
    (i : ℕ) (hiOrd : i < (ordOf a hbound).length) :
    (ordOf a hbound).get ⟨i, hiOrd⟩ =
      ⟨Exec.bestPick a (chosenK a i) (remK a i),
        hbound (Exec.bestPick a (chosenK a i) (remK a i)) (by
          have hi_morder : i < (Exec.mcsOrder a).length := by
            have h1 : (ordOf a hbound).length = n := ordOf_length a ha_len hbound
            have h2 : (Exec.mcsOrder a).length = n := mcsOrder_len a ha_len
            simpa [h1, h2] using hiOrd
          have hmc := mcsOrder_getElem_pick a ha_len i hi_morder
          rw [← hmc]
          exact List.getElem_mem hi_morder)⟩ := by
  apply Fin.ext
  have hi_morder : i < (Exec.mcsOrder a).length := by
    have h1 : (ordOf a hbound).length = n := ordOf_length a ha_len hbound
    have h2 : (Exec.mcsOrder a).length = n := mcsOrder_len a ha_len
    simpa [h1, h2] using hiOrd
  -- value-level: the i-th value of (mcsOrder.attach.map f), where f x = ⟨x.1,
  -- hbound x.1 x.2⟩, equals mcsOrder[i] = the pick.
  have hval : ((ordOf a hbound).get ⟨i, hiOrd⟩).val = Exec.bestPick a (chosenK a i) (remK a i) := by
    -- `(ordOf a hbound)` = (mcsOrder a).attach.map f; the i-th value of this
    -- is mcsOrder[i] (the attach lookup), which by mcsOrder_getElem_pick is
    -- exactly the pick at foldl step i.
    simp [ordOf, List.getElem_map, List.getElem_attach, Fin.val_mk,
          mcsOrder_getElem_pick a ha_len i hi_morder]
  exact hval

/-- `chosenFin` is insensitive to the carried bound proof (proof irrelevance of
the `Fin` subtype's index argument, transported through `pmap`).  This lets
Slice B's prefix-Finset equality (stated with `chosenK_lt ...`) match any
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
`i < (Exec.mcsOrder a).length` the `i`-th entry of the lifted ordering `ord`
is the legal MCS next pick against the prefix `ord.take i`.
-/
theorem ord_IsMCSNext_each (a : Adj n)
    (hsymm : ∀ u v : ℕ, Exec.getAdj a u v = Exec.getAdj a v u)
    (hloop : ∀ u : ℕ, Exec.getAdj a u u = false)
    (ha_len : a.length = n)
    (i : ℕ) (hi_lt : i < (Exec.mcsOrder a).length)
    (hB_prefix : ((ordOf a (mcsOrder_mem_lt a ha_len)).take i).toFinset =
        (CardBridge.chosenFin n (chosenK a i)
          (chosenK_lt a ha_len i (by
             rw [mcsOrder_len a ha_len] at hi_lt
             exact Nat.le_of_lt hi_lt))).toFinset) :
    Greedy.UGraph.IsMCSNext (Exec.toUGraph a hsymm hloop)
      ((ordOf a (mcsOrder_mem_lt a ha_len)).take i).toFinset
      ((ordOf a (mcsOrder_mem_lt a ha_len)).get ⟨i, by
         have h1 : (ordOf a (mcsOrder_mem_lt a ha_len)).length = n :=
           ordOf_length a ha_len (mcsOrder_mem_lt a ha_len)
         have h2 : (Exec.mcsOrder a).length = n := mcsOrder_len a ha_len
         omega⟩) := by
  let hb := mcsOrder_mem_lt a ha_len
  let w := Exec.bestPick a (chosenK a i) (remK a i)
  have hordlen : (ordOf a hb).length = n := ordOf_length a ha_len hb
  have hmlen : (Exec.mcsOrder a).length = n := mcsOrder_len a ha_len
  have hi_n : i < n := by omega
  have hi_le : i ≤ n := Nat.le_of_lt hi_n
  have hinv : McsInvariant.McListInv n (chosenK a i, remK a i) :=
    invK a ha_len i hi_le
  have hrem : remK a i ≠ [] := remK_ne a ha_len i hi_n
  have hnext := McsInvariant.bestPick_IsMCSNext n a hsymm hloop
    (chosenK a i) (remK a i) hinv hrem
  -- hnext : IsMCSNext G (chosenFin n (chosenK a i) hinv.2.2.1).toFinset
  --             ⟨w, hinv.2.2.2.1 w (bestPick_lex ...).1⟩
  rw [hB_prefix]
  have hcf : CardBridge.chosenFin n (chosenK a i)
        (chosenK_lt a ha_len i hi_le)
      = CardBridge.chosenFin n (chosenK a i) hinv.2.2.1 :=
    chosenFin_congr_bound n (chosenK a i) _ _
  rw [hcf]
  -- Now the Finset matches hnext's.  Handle the vertex.
  have hidx : i < (ordOf a hb).length := by omega
  have hvert : (ordOf a hb).get ⟨i, hidx⟩
      = ⟨w, hinv.2.2.2.1 w (BridgeSteps.bestPick_lex a (chosenK a i) (remK a i) hrem).1⟩ := by
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
        have h2 : (Exec.mcsOrder a).length = n := mcsOrder_len a ha_len
        omega⟩ = (ordOf a hb).get ⟨i, hidx⟩ by
      have hp : (by
        have h1 : (ordOf a (mcsOrder_mem_lt a ha_len)).length = n :=
          ordOf_length a ha_len (mcsOrder_mem_lt a ha_len)
        have h2 : (Exec.mcsOrder a).length = n := mcsOrder_len a ha_len
        omega : i < (ordOf a hb).length)
          = hidx := Subsingleton.elim _ _
      rw [hp])]
  rw [hvert]
  -- goal: IsMCSNext G cf.toFinset ⟨w, hinv.2.2.2.1 w _⟩ = hnext (up to Fin index)
  simpa [Fin.ext] using hnext

end ExecBridge
end DynamicMcs
