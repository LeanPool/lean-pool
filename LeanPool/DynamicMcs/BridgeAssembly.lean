/-
Copyright (c) 2026 Md Thoriqul Islam Thonmay and Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Md Thoriqul Islam Thonmay, Gregory Morse
-/

-- Modified for Lean Pool.

module

public import LeanPool.DynamicMcs.Exec
public import LeanPool.DynamicMcs.ExecBridge
public import LeanPool.DynamicMcs.BridgeSteps
public import LeanPool.DynamicMcs.CardBridge
public import LeanPool.DynamicMcs.McsInvariant
public import LeanPool.DynamicMcs.BridgePartsA
public import LeanPool.DynamicMcs.BridgePartsB
public import LeanPool.DynamicMcs.BridgePartsC
public import LeanPool.DynamicMcs.GreedySearch

/-!
# Bridge assembly: wiring the three slices into the final bridge theorem

`mcsOrder_eq_greedySuffix` states that the executable `Exec.mcsOrder` is a
valid abstract `Greedy.UGraph.IsMCSOrdering` of `Exec.toUGraph a hsymm hloop`,
and that its values equal `Exec.mcsOrder a`.

The assembly wires:
  * Slice A (`ord_nodup_len_map`): `Nodup`, `length`, value-map equality.
  * Slice B (`ord_take_finset_eq_chosenFin`): the prefix-Finset equality
    relating the lifted ordering to the `chosenFin` image of `chosenK`.
  * Slice C (`ord_IsMCSNext_each`): per-prefix MCS-next legality, which takes
    the Slice-B equality as an explicit hypothesis `hB_prefix`.

Two small alignment lemmas bridge the (definitionally different but
semantically equal) representations used by the slices:
  * `ordFin_eq_ordOf`: Slice B's `ordFin` equals Slice C's `ordOf`.
  * `hB_prefix_proof`: produces the exact `hB_prefix` hypothesis, aligning the
    Slice-B prefix equality with Slice C's `chosenK`/`ordOf` form.
-/

@[expose] public section

open DynamicMcs.Greedy

namespace DynamicMcs

namespace ExecBridge

/-- Slice B's `ordFin` and Slice C's `ordOf` (with the standard bound) are the
same list of `Fin n`. Both embed `Exec.mcsOrder a`; the lifting differs only in
how the bound proof is threaded through `pmap` vs `attach.map`, which is
proof-irrelevant. -/
lemma ordFin_eq_ordOf (a : Adj n) (ha_len : a.length = n) :
    ordFin a ha_len = ordOf a (mcsOrder_mem_lt a ha_len) := by
  unfold ordFin ordOf
  unfold CardBridge.chosenFin
  rw [List.pmap_eq_map_attach]

/-- The Slice-B prefix-Finset equality, restated in Slice C's `chosenK`/`ordOf`
form. This is the exact hypothesis `hB_prefix` required by
`ord_IsMCSNext_each`. -/
lemma hB_prefix_proof (a : Adj n) (ha_len : a.length = n) (i : ℕ)
    (hi_lt : i < (Exec.mcsOrder a).length) :
    ((ordOf a (mcsOrder_mem_lt a ha_len)).take i).toFinset =
      (CardBridge.chosenFin n (chosenK a i)
        (chosenK_lt a ha_len i (by
           rw [mcsOrder_len a ha_len] at hi_lt
           exact Nat.le_of_lt hi_lt))).toFinset := by
  have hk : i ≤ a.length := by
    have h := mcsOrder_len a ha_len
    omega
  rw [← ordFin_eq_ordOf a ha_len]
  -- `chosenK a i` and `chosenAt a i` are the same list (identical foldl), so
  -- the two `chosenFin` (differing only by the carried bound proof) are equal.
  have hcf : CardBridge.chosenFin n (chosenK a i) (chosenK_lt a ha_len i (by
        rw [mcsOrder_len a ha_len] at hi_lt; exact Nat.le_of_lt hi_lt))
      = CardBridge.chosenFin n (chosenAt a i) (chosenAt_lt a ha_len i hk) := by
    exact chosenFin_congr_bound n (chosenK a i) _ _
  rw [hcf]
  exact ord_take_finset_eq_chosenFin a ha_len i hk

/-- The final bridge: the executable MCS ordering is a valid abstract MCS
ordering of `Exec.toUGraph a hsymm hloop`, and its values are exactly
`Exec.mcsOrder a`. -/
theorem mcsOrder_eq_greedySuffix
    (a : Adj n)
    (hsymm : ∀ u v : ℕ, Exec.getAdj a u v = Exec.getAdj a v u)
    (hloop : ∀ u : ℕ, Exec.getAdj a u u = false)
    (ha_len : a.length = n) :
    let G := Exec.toUGraph a hsymm hloop
    ∃ (ord : List (Greedy.Vert n)),
      Greedy.UGraph.IsMCSOrdering G ord ∧
      ord.map (fun v => v.val) = Exec.mcsOrder a := by
  let hb := mcsOrder_mem_lt a ha_len
  let ord : List (Fin n) := (Exec.mcsOrder a).attach.map (fun ⟨v, hv⟩ => ⟨v, hb v hv⟩)
  have ho : ord.Nodup ∧ ord.length = n ∧ ord.map (fun v : Fin n => v.val) = Exec.mcsOrder a := by
    simpa [ord, hb] using (ord_nodup_len_map a ha_len)
  refine ⟨ord, ?_, ?_⟩
  · -- IsMCSOrdering G ord
    dsimp [Greedy.UGraph.IsMCSOrdering]
    constructor
    · exact ho.1
    constructor
    · exact ho.2.1
    · intro i hi
      have hi_lt : i < (Exec.mcsOrder a).length := by
        simpa [ho.2.1, mcsOrder_len a ha_len] using hi
      have hB : ((ordOf a (mcsOrder_mem_lt a ha_len)).take i).toFinset =
          (CardBridge.chosenFin n (chosenK a i)
            (chosenK_lt a ha_len i (by
               rw [mcsOrder_len a ha_len] at hi_lt
               exact Nat.le_of_lt hi_lt))).toFinset := by
        exact hB_prefix_proof a ha_len i hi_lt
      have hnext := ord_IsMCSNext_each a hsymm hloop ha_len i hi_lt hB
      simpa [ord, hb, ordOf] using hnext
  · exact ho.2.2

end ExecBridge
end DynamicMcs
