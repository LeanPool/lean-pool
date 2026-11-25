/-
Copyright (c) 2026 Md Thoriqul Islam Thonmay and Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Md Thoriqul Islam Thonmay, Gregory Morse
-/

-- Modified for Lean Pool.

module

public import LeanPool.DynamicMcs.Exec
public import LeanPool.DynamicMcs.BridgeSteps
public import LeanPool.DynamicMcs.CardBridge
public import LeanPool.DynamicMcs.GreedySearch

/-!
# Foldl invariant for the executable MCS ordering

This module proves that the executable `mcsOrder` foldl maintains a legal
state at every intermediate point: the chosen prefix (stored in reverse) is a
`Nodup` list of ids `< n`, and the remaining list is exactly the complement of
the chosen prefix (relative to `Fin n` / `range n`). It also proves that every
pick made by `mcsStep` is a legal MCS `UGraph.IsMCSNext` step for the abstract
graph built by `toUGraph`.
-/

@[expose] public section

namespace DynamicMcs

namespace McsInvariant

/-- The purely-list foldl invariant on a state `(chosen, rem)`:
`chosen` (in reverse) is a `Nodup` list of ids `< n`, `rem` is a `Nodup` list
of ids `< n`, and every `v < n` is contained in exactly one of `chosen` / `rem`
(i.e. `rem` is the complement of `chosen` in `range n`). -/
def McListInv (n : ℕ) (st : List ℕ × List ℕ) : Prop :=
  st.1.Nodup ∧ st.2.Nodup ∧
    (∀ v ∈ st.1, v < n) ∧ (∀ v ∈ st.2, v < n) ∧
    (∀ v, v < n → (v ∈ st.2 ↔ v ∉ st.1))

/-- The invariant holds at the initial foldl state `([], range n)`. -/
lemma listInv_init (n : ℕ) : McListInv n ([], List.range n) := by
  unfold McListInv
  simp [List.mem_range, List.nodup_range]

/-- `mcsStep` on a nonempty `rem` reduces to prepending `bestPick` to `chosen`
and erasing it from `rem`. -/
lemma mcsStep_eq (a : Adj n) (chosen rem : List ℕ) (h : rem ≠ []) :
    mcsStep a (chosen, rem)
      = (bestPick a chosen rem :: chosen, rem.erase (bestPick a chosen rem)) := by
  rcases List.exists_cons_of_ne_nil h with ⟨y, ys, hc⟩
  rw [hc]
  rfl

/-- One `mcsStep` transition preserves `McListInv` (nonempty-rem variant). -/
lemma stepTransition (a : Adj n) (chosen rem : List ℕ)
    (h : McListInv n (chosen, rem)) (hrem_ne : rem ≠ []) :
    McListInv n (bestPick a chosen rem :: chosen,
                 rem.erase (bestPick a chosen rem)) := by
  rcases h with ⟨hnd_c, hnd_r, hlt_c, hlt_r, hcomp⟩
  let w := bestPick a chosen rem
  have hw_mem : w ∈ rem := (BridgeSteps.bestPick_lex a chosen rem hrem_ne).1
  have hw_lt : w < n := hlt_r w hw_mem
  have hw_notchosen : w ∉ chosen := (hcomp w hw_lt).mp hw_mem
  unfold McListInv
  constructor
  · -- (w :: chosen).Nodup
    exact List.Nodup.cons hw_notchosen hnd_c
  constructor
  · -- rem.erase w is Nodup
    exact List.Nodup.erase w hnd_r
  constructor
  · -- all chosen ids < n
    intro v hv
    rcases List.mem_cons.mp hv with hveq | hvch
    · simpa [hveq] using hw_lt
    · exact hlt_c v hvch
  constructor
  · -- all remaining ids < n
    intro v hv
    exact hlt_r v (List.mem_of_mem_erase hv)
  · -- complement property
    intro v hv_lt
    have hv_rem_iff : v ∈ rem ↔ v ∉ chosen := hcomp v hv_lt
    by_cases hveq : v = w
    · -- v = w: erase removes it, and chosen gains it; both sides are False
      rw [hveq]
      constructor
      · intro hv_rem
        -- w ∈ rem.erase w is impossible
        have hv' : w ∈ rem.erase w := hv_rem
        rw [List.Nodup.mem_erase_iff hnd_r] at hv'
        simp at hv'
      · intro hv_notchosen
        -- w ∉ (w :: chosen) is impossible
        have hv' : w ∉ w :: chosen := hv_notchosen
        simp at hv'
    · -- v ≠ w
      constructor
      · intro hv_rem
        -- v ∈ rem.erase w → v ∉ (w :: chosen)
        have hv_rem' : v ∈ rem := List.mem_of_mem_erase hv_rem
        have hv_nc : v ∉ chosen := hv_rem_iff.mp hv_rem'
        intro hmem
        rcases List.mem_cons.mp hmem with hvweq | hvc
        · exact hveq hvweq
        · exact hv_nc hvc
      · intro hv_notchosen
        -- v ∉ (w :: chosen) → v ∈ rem.erase w
        have hv_nc' : v ∉ chosen := by
          intro hvc
          exact hv_notchosen (List.mem_cons.mpr (Or.inr hvc))
        have hv_rem : v ∈ rem := hv_rem_iff.mpr hv_nc'
        rw [List.Nodup.mem_erase_iff hnd_r]
        exact ⟨hveq, hv_rem⟩

/-- One full `mcsStep` preserves `McListInv`. -/
lemma mcsStep_preserves (a : Adj n) {chosen rem : List ℕ}
    (h : McListInv n (chosen, rem)) :
    McListInv n (mcsStep a (chosen, rem)) := by
  by_cases h_empty : rem = []
  · subst rem
    simp only [mcsStep]
    exact h
  · rw [mcsStep_eq a chosen rem h_empty]
    exact stepTransition a chosen rem h h_empty

/-- The foldl invariant holds at every intermediate state of the executable
`mcsOrder` loop, measured over the first `k` steps of the foldl over the
full `range n` list (the `n`-indexed form, since the seed list is `range n`).
-/
lemma foldl_mcsStep_listInv_core (a : Adj n) :
    ∀ k ≤ n,
      McListInv n ((List.range k).foldl (fun s _ => mcsStep a s) ([], List.range n)) := by
  intro k
  induction k with
  | zero =>
      intro _
      simpa using listInv_init n
  | succ k ih =>
      intro hk
      have him_step : McListInv n
          ((List.range k).foldl (fun s _ => mcsStep a s) ([], List.range n)) := by
        exact ih (Nat.le_of_succ_le hk)
      -- `range (k+1) = range k ++ [k]`, so the foldl applies exactly one more
      -- `mcsStep` (whose result is independent of the folded element `k`).
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      exact mcsStep_preserves a him_step

/-- The foldl invariant holds at every intermediate state of the executable
`mcsOrder` loop. At step `k` of the foldl over `range a.length`, the
pair `st` satisfies `McListInv n`: the chosen prefix (in reverse) is `Nodup`,
all ids are `< n`, and its second component is exactly the complement. -/
lemma foldl_mcsStep_listInv (a : Adj n) (ha_len : a.length = n) :
    ∀ k ≤ a.length,
      McListInv n ((List.range k).foldl (fun s _ => mcsStep a s)
                                          ([], List.range a.length)) := by
  intro k hk
  have hr : List.range a.length = List.range n := congrArg List.range ha_len
  rw [hr]
  have hcore := foldl_mcsStep_listInv_core a k (by omega)
  simpa [hr] using hcore

/-- Length-tracking companion: after `k` steps (each consumes exactly one
remaining vertex), the chosen prefix has length `k` and `rem` has length
`n - k`. -/
lemma foldl_mcsStep_len_core (a : Adj n) :
    ∀ k ≤ n,
      ((List.range k).foldl (fun s _ => mcsStep a s) ([], List.range n)).1.length = k ∧
      ((List.range k).foldl (fun s _ => mcsStep a s) ([], List.range n)).2.length = n - k := by
  intro k
  induction k with
  | zero =>
      intro _
      simp
  | succ k ih =>
      intro hk
      have hk_le : k ≤ n := Nat.le_of_succ_le hk
      let stk := (List.range k).foldl (fun s _ => mcsStep a s) ([], List.range n)
      have hscale : stk.1.length = k ∧ stk.2.length = n - k := by
        exact ih hk_le
      have hstk_inv : McListInv n stk := foldl_mcsStep_listInv_core a k hk_le
      -- rem stk.2 is nonempty since k ≤ n implies n - k ≥ 1
      have hrem_ne : stk.2 ≠ [] := by
        intro hempty
        have hlen : stk.2.length = n - k := hscale.2
        rw [hempty] at hlen
        simp at hlen
        omega
      let w := bestPick a stk.1 stk.2
      have hstp : mcsStep a stk = (w :: stk.1, stk.2.erase w) :=
        mcsStep_eq a stk.1 stk.2 hrem_ne
      have hw_mem : w ∈ stk.2 := (BridgeSteps.bestPick_lex a stk.1 stk.2 hrem_ne).1
      have hrem_nodup : stk.2.Nodup := hstk_inv.2.1
      have hlen_erase : (stk.2.erase w).length = stk.2.length - 1 :=
        List.length_erase_of_mem hw_mem
      -- the foldl over `range (k+1)` is `mcsStep stk`
      have hstep : (List.range (k + 1)).foldl (fun s _ => mcsStep a s) ([], List.range n)
          = (w :: stk.1, stk.2.erase w) := by
        rw [List.range_succ, List.foldl_append]
        simp [stk, hstp]
      rw [hstep]
      constructor
      · simp [hscale.1]
      · rw [hlen_erase, hscale.2]
        omega

/-- `x : Fin n` lies in the `Fin`-image of `chosen` iff its value lies in
`chosen`. -/
lemma mem_chosenFin_iff {chosen : List ℕ} (hchosen : ∀ v ∈ chosen, v < n) (x : Fin n) :
    x ∈ (CardBridge.chosenFin n chosen hchosen).toFinset ↔ x.val ∈ chosen := by
  rw [List.mem_toFinset]
  constructor
  · intro hx
    rcases List.mem_pmap.mp hx with ⟨a, ha, hfa⟩
    have hv : a = x.val := congrArg Fin.val hfa
    rwa [hv] at ha
  · intro hx
    refine List.mem_pmap.mpr ⟨x.val, hx, ?_⟩
    apply Fin.ext
    rfl

/-- Modulo the finite image, `x` is an unchosen element of `Fin n` iff its
value is not already chosen. -/
lemma mem_univ_ndiff_chosenFin_iff {chosen : List ℕ} (hchosen : ∀ v ∈ chosen, v < n)
    (x : Fin n) :
    x ∈ (Finset.univ : Finset (Fin n)) \ (CardBridge.chosenFin n chosen hchosen).toFinset
      ↔ x.val ∉ chosen := by
  rw [Finset.mem_sdiff]
  simp only [Finset.mem_univ, true_and]
  exact (mem_chosenFin_iff hchosen x).not

/-- The vertex picked by `bestPick` is a legal MCS next step: it is unchosen,
its abstract cardinality `G.neigh` is maximal among the unchosen vertices, and
it is the least index achieving that maximum. This bridges the executable
`bestPick` selection to the abstract `UGraph.IsMCSNext` predicate via
`BridgeSteps.bestPick_lex` (max cardinality, smallest-id tie-break) and
`CardBridge.cardC_eq_neigh` (executable cardinality equals abstract `neigh`). -/
lemma bestPick_IsMCSNext (n : ℕ) (a : Adj n)
    (hsymm : ∀ u v : ℕ, getAdj a u v = getAdj a v u)
    (hloop : ∀ u : ℕ, getAdj a u u = false)
    (chosen rem : List ℕ) (hinv : McListInv n (chosen, rem)) (hrem_ne : rem ≠ []) :
    UGraph.IsMCSNext (toUGraph a hsymm hloop)
      (CardBridge.chosenFin n chosen hinv.2.2.1).toFinset
      ⟨bestPick a chosen rem,
        hinv.2.2.2.1 (bestPick a chosen rem)
          (BridgeSteps.bestPick_lex a chosen rem hrem_ne).1⟩ := by
  classical
  rcases hinv with ⟨hnd_c, hnd_r, hlt_c, hlt_r, hcomp⟩
  let w := bestPick a chosen rem
  let G : UGraph n := toUGraph a hsymm hloop
  have hwm : w ∈ rem := (BridgeSteps.bestPick_lex a chosen rem hrem_ne).1
  have hwlt : w < n := hlt_r w hwm
  have hWN : w ∉ chosen := (hcomp w hwlt).mp hwm
  unfold UGraph.IsMCSNext
  constructor
  · -- w ∈ univ \ chosen-image
    exact (mem_univ_ndiff_chosenFin_iff hlt_c ⟨w, hwlt⟩).mpr hWN
  constructor
  · -- cardinality maximal among unchosen
    intro x hx
    have hxvc : x.val ∉ chosen := (mem_univ_ndiff_chosenFin_iff hlt_c x).mp hx
    have hxlt : x.val < n := x.isLt
    have hxrem : x.val ∈ rem := (hcomp x.val hxlt).mpr hxvc
    have hlex : cardC a chosen x.val ≤ cardC a chosen w :=
      (BridgeSteps.bestPick_lex a chosen rem hrem_ne).2.1 x.val hxrem
    calc
      G.neigh (CardBridge.chosenFin n chosen hlt_c).toFinset x
          = cardC a chosen x.val := by
              exact CardBridge.cardC_eq_neigh n a hsymm hloop chosen hlt_c hnd_c x.val x.isLt
      _ ≤ cardC a chosen w := hlex
      _ = G.neigh (CardBridge.chosenFin n chosen hlt_c).toFinset ⟨w, hwlt⟩ := by
              exact (CardBridge.cardC_eq_neigh n a hsymm hloop chosen hlt_c hnd_c w hwlt).symm
  · -- smallest id among those achieving the max
    intro x hx hEq
    have hxvc : x.val ∉ chosen := (mem_univ_ndiff_chosenFin_iff hlt_c x).mp hx
    have hxlt : x.val < n := x.isLt
    have hxrem : x.val ∈ rem := (hcomp x.val hxlt).mpr hxvc
    have hEqc : cardC a chosen x.val = cardC a chosen w := by
      have h1 := CardBridge.cardC_eq_neigh n a hsymm hloop chosen hlt_c hnd_c x.val x.isLt
      have h2 := CardBridge.cardC_eq_neigh n a hsymm hloop chosen hlt_c hnd_c w hwlt
      -- h1 : G.neigh cf.toFinset ⟨x.val,·⟩ = cardC x.val; h2 : ... w ... = cardC w
      calc
        cardC a chosen x.val =
        G.neigh (CardBridge.chosenFin n chosen hlt_c).toFinset x := h1.symm
        _ = G.neigh (CardBridge.chosenFin n chosen hlt_c).toFinset ⟨w, hwlt⟩ := hEq
        _ = cardC a chosen w := h2
    have h_tie := (BridgeSteps.bestPick_lex a chosen rem hrem_ne).2.2 x.val hxrem hEqc
    -- `⟨w, hwlt⟩ ≤ x` decodes to the Nat comparison `w ≤ x.val`.
    simpa [Fin.le_def] using h_tie

/-- Terminal state of the foldl over the full `range n`: after `n` steps the
remaining list is empty, so every vertex is chosen exactly once (the MCS
ordering is complete). -/
lemma mcsStep_terminal_rem_empty (a : Adj n) (ha_len : a.length = n) (k : ℕ) (hk : k = n) :
    ((List.range k).foldl (fun s _ => mcsStep a s) ([], List.range a.length)).2 = [] := by
  have hr : List.range a.length = List.range n := congrArg List.range ha_len
  rw [hr, hk]
  have hlen := foldl_mcsStep_len_core a n (le_refl n)
  -- hlen.2 : stk.2.length = n - n = 0
  have hlen0 :
      ((List.range n).foldl (fun s _ => mcsStep a s) ([], List.range n)).2.length = 0 := by
    omega
  exact List.eq_nil_of_length_eq_zero hlen0

end McsInvariant
end DynamicMcs
