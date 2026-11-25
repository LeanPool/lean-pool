/-
Copyright (c) 2026 Md Thoriqul Islam Thonmay and Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Md Thoriqul Islam Thonmay, Gregory Morse
-/

-- Modified for Lean Pool.

module

public import LeanPool.DynamicMcs.Exec
public import LeanPool.DynamicMcs.McsInvariant
public import LeanPool.DynamicMcs.GreedySearch

/-!
# Bridge parts A: mechanical shape of the executable ordering

This module proves the basic list-theoretic facts about `Exec.mcsOrder a`:
that it is duplicate-free, has length `n`, all ids are `< n`, and can be
lifted to a `Nodup` length-`n` list of `Fin n` whose values equal it.
-/

@[expose] public section

open DynamicMcs.Greedy

namespace DynamicMcs

namespace ExecBridge

/-- The terminal foldl state over the full `range a.length` satisfies the
foldl invariant: the chosen prefix (in reverse) `stN.1` is `Nodup`, and every
chosen id is `< n`. -/
lemma chosenN_inv (a : Adj n) (ha_len : a.length = n) :
    McsInvariant.McListInv n
      ((List.range a.length).foldl (fun s _ => Exec.mcsStep a s)
                                     ([], List.range a.length)) := by
  exact McsInvariant.foldl_mcsStep_listInv a ha_len a.length (le_refl a.length)

/-- The terminal chosen prefix `stN.1` has length `n`. -/
lemma chosenN_len (a : Adj n) (ha_len : a.length = n) :
    ((List.range a.length).foldl (fun s _ => Exec.mcsStep a s)
                                   ([], List.range a.length)).1.length = n := by
  have hr : List.range a.length = List.range n := congrArg List.range ha_len
  have hlen_core := McsInvariant.foldl_mcsStep_len_core a n (le_refl n)
  simpa [hr] using hlen_core.1

/-- `Exec.mcsOrder a` is exactly the reverse of the terminal chosen prefix. -/
lemma mcsOrder_eq_reverse (a : Adj n) :
    Exec.mcsOrder a
      = ((List.range a.length).foldl (fun s _ => Exec.mcsStep a s)
                                       ([], List.range a.length)).1.reverse := by
  rfl

/-- Every vertex produced by the executable ordering is `< n`. -/
lemma mcsOrder_mem_lt (a : Adj n) (ha_len : a.length = n) :
    ∀ v ∈ Exec.mcsOrder a, v < n := by
  intro v hv
  rw [mcsOrder_eq_reverse a] at hv
  have hmem : v ∈ ((List.range a.length).foldl (fun s _ => Exec.mcsStep a s)
                    ([], List.range a.length)).1 := by
    exact List.mem_reverse.mp hv
  exact (chosenN_inv a ha_len).2.2.1 v hmem

/-- The executable ordering is duplicate-free. -/
lemma mcsOrder_nodup (a : Adj n) (ha_len : a.length = n) : (Exec.mcsOrder a).Nodup := by
  rw [mcsOrder_eq_reverse a]
  exact List.nodup_reverse.mpr (chosenN_inv a ha_len).1

/-- The executable ordering has length `n`. -/
lemma mcsOrder_len (a : Adj n) (ha_len : a.length = n) : (Exec.mcsOrder a).length = n := by
  rw [mcsOrder_eq_reverse a]
  simpa using chosenN_len a ha_len

/-- The ordering list can be lifted to a `Nodup` list of `Fin n` of length
`n` whose values are exactly `Exec.mcsOrder a`. This is the mechanical
"shape" of the ordering needed by the abstract `IsMCSOrdering`. -/
lemma ord_nodup_len_map (a : Adj n) (ha_len : a.length = n) :
    let ord : List (Fin n) :=
      (Exec.mcsOrder a).attach.map (fun ⟨v, hv⟩ => ⟨v, mcsOrder_mem_lt a ha_len v hv⟩)
    ord.Nodup ∧ ord.length = n ∧ ord.map (fun v => v.val) = Exec.mcsOrder a := by
  dsimp
  have hnd_l : (Exec.mcsOrder a).Nodup := mcsOrder_nodup a ha_len
  have hlen_l : (Exec.mcsOrder a).length = n := mcsOrder_len a ha_len
  let f : {x : ℕ // x ∈ Exec.mcsOrder a} → Fin n :=
    fun ⟨v, hv⟩ => ⟨v, mcsOrder_mem_lt a ha_len v hv⟩
  have hinj : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact congrArg Fin.val h
  constructor
  · exact List.Nodup.map hinj (List.Nodup.attach hnd_l)
  constructor
  · simpa [List.length_attach] using hlen_l
  · simp

end ExecBridge
end DynamicMcs
