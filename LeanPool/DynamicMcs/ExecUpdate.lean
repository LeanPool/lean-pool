/-
Copyright (c) 2026 Md Thoriqul Islam Thonmay and Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Md Thoriqul Islam Thonmay, Gregory Morse
-/

-- Modified for Lean Pool.

module

import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Push
public import LeanPool.DynamicMcs.Correctness
public import LeanPool.DynamicMcs.Refinement

/-!
# The executable dynamic updates refine the abstract ones

On a symmetric loop-free square matrix whose graph differs from the old one by
a flip of `{u, v}`, the executable `execInsertUpdate` / `execDeleteUpdate`
applied to (the values of) the old canonical ordering return (the values of)
the abstract `insertUpdate` / `deleteUpdate`, which is the from-scratch
canonical ordering `mcsOrder` of the new matrix.

The operational cost theorems at the end bound the instrumented versions
`execInsertUpdateC` / `execDeleteUpdateC`, whose first component is the
executable update itself.
-/

@[expose] public section

noncomputable section

namespace DynamicMcs
namespace Proofs

open UGraph

variable {n : ℕ}

/-! ## Refinement of the dynamic updates -/

section Refine

variable (a a' : Adj)
  (hsymm : ∀ u v : ℕ, getAdj a u v = getAdj a v u) (hloop : ∀ u : ℕ, getAdj a u u = false)
  (hsymm' : ∀ u v : ℕ, getAdj a' u v = getAdj a' v u) (hloop' : ∀ u : ℕ, getAdj a' u u = false)
  (ha' : a'.length = n)

lemma mem_of_valid {G : UGraph n} {ord : List (Fin n)} (h : IsMCSOrdering G ord) (x : Fin n) :
    x ∈ ord :=
  List.mem_toFinset.1 ((order_toFinset_univ h).symm ▸ Finset.mem_univ x)

lemma idxOf_lt_of_valid {G : UGraph n} {ord : List (Fin n)} (h : IsMCSOrdering G ord) (x : Fin n) :
    ord.idxOf x < n := by
  have hlen : ord.length = n := h.2.1
  have hlt : ord.idxOf x < ord.length := List.idxOf_lt_length_of_mem (mem_of_valid h x)
  rw [hlen] at hlt
  exact hlt

include hsymm' hloop' ha' in
theorem insertProbe_map (u v : Fin n) (ord : List (Fin n))
    (hvalid : IsMCSOrdering (toUGraph (n := n) a hsymm hloop) ord) :
    insertProbe a' (ord.map Fin.val) u.val v.val =
      firstBreakWindow (toUGraph (n := n) a' hsymm' hloop') ord (earlierPos ord u v + 1)
        (laterPos ord u v) := by
  have he : execEarlierPos (ord.map Fin.val) u.val v.val = earlierPos ord u v := by
    simp [execEarlierPos, earlierPos, idxOf_map_val]
  have hl : execLaterPos (ord.map Fin.val) u.val v.val = laterPos ord u v := by
    simp [execLaterPos, laterPos, idxOf_map_val]
  have hu := idxOf_lt_of_valid hvalid u
  have hv := idxOf_lt_of_valid hvalid v
  have hlen : ord.length = n := hvalid.2.1
  have hel : earlierPos ord u v ≤ laterPos ord u v := by
    unfold earlierPos laterPos
    omega
  have helt : earlierPos ord u v < n := by
    unfold earlierPos
    omega
  have hwin : insertWindow (ord.map Fin.val) u.val v.val =
      ((ord.drop (earlierPos ord u v + 1)).take (laterPos ord u v - earlierPos ord u v)).map
        Fin.val := by
    rw [insertWindow, he, hl]
    simp [List.map_drop, List.map_take]
  unfold insertProbe firstBreakWindow
  rw [he, hwin, show laterPos ord u v + 1 - (earlierPos ord u v + 1) =
    laterPos ord u v - earlierPos ord u v by omega]
  refine execFirstBreak_map a' hsymm' hloop' ha' ord hvalid.1 _ _ ?_
  simp only [List.length_take, List.length_drop]
  omega

include hsymm' hloop' ha' in
/-- The executable insertion probe-and-repair computes the abstract insertion
update, for every flip of `{u, v}`. -/
theorem exec_insert_update_eq (u v : Fin n) (ord : List (Fin n))
    (hflip : FlipOf (toUGraph (n := n) a hsymm hloop) (toUGraph (n := n) a' hsymm' hloop') u v)
    (hvalid : IsMCSOrdering (toUGraph (n := n) a hsymm hloop) ord) :
    execInsertUpdate a' (ord.map Fin.val) u.val v.val =
      (insertUpdate (toUGraph (n := n) a' hsymm' hloop') ord u v).map Fin.val := by
  have hprobe := insertProbe_map a a' hsymm hloop hsymm' hloop' ha' u v ord hvalid
  unfold execInsertUpdate
  rw [hprobe]
  cases hw : firstBreakWindow (toUGraph (n := n) a' hsymm' hloop') ord (earlierPos ord u v + 1)
      (laterPos ord u v) with
  | none =>
      rw [insert_update_of_no_break u v ord hvalid hw]
  | some k =>
      have habs : insertUpdate (toUGraph (n := n) a' hsymm' hloop') ord u v =
          greedySuffix (toUGraph (n := n) a' hsymm' hloop') (ord.take k) := by
        simp only [insertUpdate, hw, Option.getD_some]
      have hv := insert_update_valid u v ord hflip hvalid
      rw [habs] at hv
      unfold greedySuffix at hv
      obtain ⟨hnd, hsteps⟩ := steps_of_prefix hv
      change regreedy a' ((ord.map Fin.val).take k) = _
      rw [habs, ← List.map_take]
      exact regreedy_eq_greedySuffix a' hsymm' hloop' ha' (ord.take k) hnd hsteps

include hsymm' hloop' ha' in
/-- The executable insertion update returns the from-scratch canonical
ordering of the new matrix. -/
theorem exec_insert_update_eq_mcsOrder (u v : Fin n) (ord : List (Fin n))
    (hflip : FlipOf (toUGraph (n := n) a hsymm hloop) (toUGraph (n := n) a' hsymm' hloop') u v)
    (hvalid : IsMCSOrdering (toUGraph (n := n) a hsymm hloop) ord) :
    execInsertUpdate a' (ord.map Fin.val) u.val v.val = mcsOrder a' := by
  rw [exec_insert_update_eq a a' hsymm hloop hsymm' hloop' ha' u v ord hflip hvalid,
    insert_update_eq_initOrder u v ord hflip hvalid,
    mcsOrder_eq_initOrder a' hsymm' hloop' ha']

include hsymm' hloop' ha' in
/-- The executable deletion probe-and-repair computes the abstract deletion
update. -/
theorem exec_delete_update_eq (u v : Fin n) (ord : List (Fin n))
    (hflip : FlipOf (toUGraph (n := n) a hsymm hloop) (toUGraph (n := n) a' hsymm' hloop') u v)
    (hdel : getAdj a u.val v.val = true) (hdel' : getAdj a' u.val v.val = false)
    (hvalid : IsMCSOrdering (toUGraph (n := n) a hsymm hloop) ord) :
    execDeleteUpdate a' (ord.map Fin.val) u.val v.val =
      (deleteUpdate (toUGraph (n := n) a' hsymm' hloop') ord u v).map Fin.val := by
  have hdel'G : ¬ (toUGraph (n := n) a' hsymm' hloop').adj u v := by
    intro h
    change getAdj a' u.val v.val = true at h
    rw [hdel'] at h
    exact Bool.false_ne_true h
  have hl : execLaterPos (ord.map Fin.val) u.val v.val = laterPos ord u v := by
    simp [execLaterPos, laterPos, idxOf_map_val]
  have hw : execLaterVert (ord.map Fin.val) u.val v.val = (laterVert ord u v).val := by
    unfold execLaterVert laterVert
    rw [idxOf_map_val, idxOf_map_val]
    split_ifs <;> rfl
  have hu := idxOf_lt_of_valid hvalid u
  have hv := idxOf_lt_of_valid hvalid v
  have hlen : ord.length = n := hvalid.2.1
  have hP : (ord.take (laterPos ord u v)).Nodup := hvalid.1.sublist (List.take_sublist _ _)
  have hPlen : (ord.take (laterPos ord u v)).length < n := by
    rw [List.length_take]
    unfold laterPos
    omega
  have hiff := pickAt_eq_iff a' hsymm' hloop' ha' _ hP hPlen (laterVert ord u v)
  have hvalid' := delete_update_valid u v ord hflip hdel hdel'G hvalid
  unfold execDeleteUpdate
  rw [hl, hw, show (ord.map Fin.val).take (laterPos ord u v) =
    (ord.take (laterPos ord u v)).map Fin.val by simp [List.map_take]]
  unfold deleteUpdate deletionBreaks UGraph.isFalse at hvalid' ⊢
  by_cases hlegal : IsMCSNext (toUGraph (n := n) a' hsymm' hloop')
      (ord.take (laterPos ord u v)).toFinset (laterVert ord u v)
  · rw [hiff.2 hlegal]
    simp [hlegal]
  · simp only [hlegal, ↓reduceIte] at hvalid' ⊢
    rw [ite_eq_right (mt hiff.1 hlegal)]
    unfold greedySuffix at hvalid'
    obtain ⟨hnd, hsteps⟩ := steps_of_prefix hvalid'
    exact regreedy_eq_greedySuffix a' hsymm' hloop' ha' _ hnd hsteps

include hsymm' hloop' ha' in
/-- The executable deletion update returns the from-scratch canonical
ordering of the new matrix. -/
theorem exec_delete_update_eq_mcsOrder (u v : Fin n) (ord : List (Fin n))
    (hflip : FlipOf (toUGraph (n := n) a hsymm hloop) (toUGraph (n := n) a' hsymm' hloop') u v)
    (hdel : getAdj a u.val v.val = true) (hdel' : getAdj a' u.val v.val = false)
    (hvalid : IsMCSOrdering (toUGraph (n := n) a hsymm hloop) ord) :
    execDeleteUpdate a' (ord.map Fin.val) u.val v.val = mcsOrder a' := by
  have hdel'G : ¬ (toUGraph (n := n) a' hsymm' hloop').adj u v := by
    intro h
    change getAdj a' u.val v.val = true at h
    rw [hdel'] at h
    exact Bool.false_ne_true h
  rw [exec_delete_update_eq a a' hsymm hloop hsymm' hloop' ha' u v ord hflip hdel hdel' hvalid,
    delete_update_eq_initOrder u v ord hflip hdel hdel'G hvalid,
    mcsOrder_eq_initOrder a' hsymm' hloop' ha']

end Refine

/-! ## Operational cost (unit-cost query model) -/

section Cost

variable (a : Adj) (o : List ℕ)

lemma execFirstBreakC_fst : ∀ k xs, (execFirstBreakC a o k xs).1 = execFirstBreak a o k xs := by
  intro k xs
  induction xs generalizing k with
  | nil => rfl
  | cons x xs ih =>
      by_cases hx : pickAt a (o.take k) = x
      · simp [execFirstBreakC, execFirstBreak, hx, ih]
      · simp [execFirstBreakC, execFirstBreak, hx]

lemma execFirstBreakC_snd_le : ∀ k xs, (execFirstBreakC a o k xs).2 ≤ xs.length := by
  intro k xs
  induction xs generalizing k with
  | nil => simp [execFirstBreakC]
  | cons x xs ih =>
      by_cases hx : pickAt a (o.take k) = x
      · simp only [execFirstBreakC, hx, ↓reduceIte, List.length_cons]
        have := ih (k + 1)
        omega
      · simp [execFirstBreakC, hx]

lemma execFirstBreak_some : ∀ k xs j, execFirstBreak a o k xs = some j →
    k ≤ j ∧ j < k + xs.length ∧ (execFirstBreakC a o k xs).2 = j - k + 1 := by
  intro k xs
  induction xs generalizing k with
  | nil => intro j h; simp [execFirstBreak] at h
  | cons x xs ih =>
      intro j h
      by_cases hx : pickAt a (o.take k) = x
      · simp only [execFirstBreak, hx, ↓reduceIte] at h
        obtain ⟨h1, h2, h3⟩ := ih (k + 1) j h
        simp only [execFirstBreakC, hx, ↓reduceIte, List.length_cons]
        refine ⟨by omega, by omega, ?_⟩
        rw [h3]
        omega
      · simp only [execFirstBreak, hx, ↓reduceIte, Option.some.injEq] at h
        subst h
        simp [execFirstBreakC, hx]

lemma mcsStepC_fst (st : List ℕ × List ℕ) : (mcsStepC a st).1 = mcsStep a st := by
  rcases st with ⟨c, r⟩
  cases r <;> rfl

lemma mcsStepC_snd_le (st : List ℕ × List ℕ) : (mcsStepC a st).2 ≤ 1 := by
  rcases st with ⟨c, r⟩
  cases r <;> simp [mcsStepC]

lemma foldl_mcsStepC : ∀ (l : List ℕ) (st : List ℕ × List ℕ) (c : ℕ),
    (l.foldl (fun s _ => let t := mcsStepC a s.1; (t.1, s.2 + t.2)) (st, c)).1 =
        l.foldl (fun s _ => mcsStep a s) st ∧
      (l.foldl (fun s _ => let t := mcsStepC a s.1; (t.1, s.2 + t.2)) (st, c)).2 ≤
        c + l.length := by
  intro l
  induction l with
  | nil => intro st c; simp
  | cons x l ih =>
      intro st c
      simp only [List.foldl_cons, List.length_cons]
      rw [← mcsStepC_fst]
      obtain ⟨h1, h2⟩ := ih (mcsStepC a st).1 (c + (mcsStepC a st).2)
      exact ⟨h1, le_trans h2 (by have := mcsStepC_snd_le a st; omega)⟩

lemma regreedyC_fst (pref : List ℕ) : (regreedyC a pref).1 = regreedy a pref := by
  simp only [regreedyC, regreedy, mcsFinish, (foldl_mcsStepC a _ _ 0).1]

lemma regreedyC_snd_le (pref : List ℕ) : (regreedyC a pref).2 ≤ a.length - pref.length := by
  have := (foldl_mcsStepC a (List.range (a.length - pref.length))
    (pref.reverse, remOf a.length pref) 0).2
  simp only [regreedyC]
  simpa using this

/-- The counted insertion update returns the same list as the plain update (the
count is the second projection). This is the link between the cost bounds and
the real executable update. -/
theorem exec_insert_update_c_fst (u v : ℕ) :
    (execInsertUpdateC a o u v).1 = execInsertUpdate a o u v := by
  simp only [execInsertUpdateC, execInsertUpdate, insertProbeC, insertProbe, execFirstBreakC_fst]
  cases execFirstBreak a o (execEarlierPos o u v + 1) (insertWindow o u v) with
  | none => rfl
  | some k => simp [regreedyC_fst]

/-- The counted deletion update returns the same list as the plain update. -/
theorem exec_delete_update_c_fst (u v : ℕ) :
    (execDeleteUpdateC a o u v).1 = execDeleteUpdate a o u v := by
  unfold execDeleteUpdateC execDeleteUpdate
  split_ifs <;> simp [regreedyC_fst]

lemma insertWindow_length_le (u v : ℕ) :
    (insertWindow o u v).length ≤ execLaterPos o u v - execEarlierPos o u v := by
  simp [insertWindow, List.length_take]

/-- If the insertion probe finds no break, the update costs at most the window
length `laterPos - earlierPos` and performs no regreedy. -/
theorem exec_insert_cost_of_no_break (u v : ℕ) (h : insertProbe a o u v = none) :
    (execInsertUpdateC a o u v).2 ≤ execLaterPos o u v - execEarlierPos o u v := by
  unfold insertProbe at h
  have hle := (execFirstBreakC_snd_le a o (execEarlierPos o u v + 1) (insertWindow o u v)).trans
    (insertWindow_length_le o u v)
  simp only [execInsertUpdateC, insertProbeC, execFirstBreakC_fst, h]
  exact hle

/-- If the insertion probe breaks at position `k`, the update costs the
`k - earlierPos` probe checks plus at most `n - k` regreedy steps. -/
theorem exec_insert_cost_of_break (u v k : ℕ) (h : insertProbe a o u v = some k) :
    (execInsertUpdateC a o u v).2 ≤ (k - execEarlierPos o u v) + (a.length - k) := by
  unfold insertProbe at h
  obtain ⟨hk1, hk2, hcost⟩ := execFirstBreak_some a o _ _ k h
  have hwin : (insertWindow o u v).length ≤ o.length - (execEarlierPos o u v + 1) := by
    simp [insertWindow, List.length_take, List.length_drop]
  have hko : (o.take k).length = k := by
    rw [List.length_take]
    omega
  have hr := regreedyC_snd_le a (o.take k)
  rw [hko] at hr
  simp only [execInsertUpdateC, insertProbeC, execFirstBreakC_fst, h]
  rw [hcost]
  omega

/-- If the deletion probe does not fire, the update costs exactly one check. -/
theorem exec_delete_cost_of_no_break (u v : ℕ)
    (h : pickAt a (o.take (execLaterPos o u v)) = execLaterVert o u v) :
    (execDeleteUpdateC a o u v).2 = 1 := by
  simp [execDeleteUpdateC, h]

/-- If the deletion probe fires, the update costs one check plus at most
`n - laterPos` regreedy steps. -/
theorem exec_delete_cost_of_break (u v : ℕ)
    (h : pickAt a (o.take (execLaterPos o u v)) ≠ execLaterVert o u v) :
    (execDeleteUpdateC a o u v).2 ≤ 1 + (a.length - execLaterPos o u v) := by
  have hle : execLaterPos o u v ≤ o.length := by
    unfold execLaterPos
    exact max_le (List.idxOf_le_length) (List.idxOf_le_length)
  have hr := regreedyC_snd_le a (o.take (execLaterPos o u v))
  rw [List.length_take, min_eq_left hle] at hr
  simp only [execDeleteUpdateC, h, ↓reduceIte]
  omega

/-- Worst case: an insertion costs at most `n` units (static recomputation
also costs `Θ(n)` picks). -/
theorem exec_insert_cost_le (u v : ℕ) (ho : o.length = a.length) :
    (execInsertUpdateC a o u v).2 ≤ a.length := by
  cases h : insertProbe a o u v with
  | none =>
      have := exec_insert_cost_of_no_break a o u v h
      have hle : execLaterPos o u v ≤ o.length := by
        unfold execLaterPos
        exact max_le (List.idxOf_le_length) (List.idxOf_le_length)
      omega
  | some k =>
      have := exec_insert_cost_of_break a o u v k h
      unfold insertProbe at h
      obtain ⟨hk1, hk2, -⟩ := execFirstBreak_some a o _ _ k h
      have hwin : (insertWindow o u v).length ≤ o.length - (execEarlierPos o u v + 1) := by
        simp [insertWindow, List.length_take, List.length_drop]
      omega

/-- Worst case: a deletion costs at most `n + 1` units. -/
theorem exec_delete_cost_le (u v : ℕ) :
    (execDeleteUpdateC a o u v).2 ≤ a.length + 1 := by
  by_cases h : pickAt a (o.take (execLaterPos o u v)) = execLaterVert o u v
  · rw [exec_delete_cost_of_no_break a o u v h]
    omega
  · have := exec_delete_cost_of_break a o u v h
    omega

end Cost

end Proofs
end DynamicMcs
