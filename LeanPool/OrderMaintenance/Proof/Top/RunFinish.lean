/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Top.Loops


/-!
# M5: running the end of a drain

`finishDrain v` removes ghost `v` from the tables of its entries and from the tables holding it,
releases its targets and marks it dead (`finishDrain_run`, state `fdS`). A sweep call on a ghost
with an empty range does exactly that (`drainStep_finish`).
-/


@[expose] public section

namespace OrderMaintenance.Proof.Top

open OrderMaintenance.Model OrderMaintenance.Proof
section defs
variable (v : Nat)

/-- `dropTable`, as a state update. -/
def dropTableS (hh : Nat) (s : Core) (e : Nat) : Core :=
  if hh == 0 then
    (if (s.cin.getX e).contains v then { s with cin := s.cin.setX e ((s.cin.getX e).erase v) }
      else s)
  else if (s.nodes.getX e).inTables.contains v then
    { s with nodes := s.nodes.modify e fun n => { n with
      inTables := (s.nodes.getX e).inTables.erase v } }
  else s

/-- `dropEntry`, as a state update. -/
def dropEntryS (s : Core) (T : Nat) : Core :=
  { s with nodes := s.nodes.modify T fun n =>
      { n with table := assocErase n.table v, side := assocErase n.side v } }

/-- `release`, as a state update. -/
def releaseS (s : Core) (t : Nat) : Core :=
  if (s.nodes.getX t).overflowOf == v then
    { s with nodes := s.nodes.modify t fun n => { n with overflowOf := NIL } }
  else s

/-- Removes the finished ghost from the inverse tables of every entry it held. -/
def fd1 (s : Core) : Core :=
  (s.nodes.getX v).order.foldl (dropTableS v ((s.nodes.getX v).height - 1)) s
/-- Removes the finished ghost entry from each table that contained it. -/
def fd2 (s : Core) : Core := (s.nodes.getX v).inTables.foldl (dropEntryS v) (fd1 v s)
/-- Releases both targets after removing the finished ghost from all tables. -/
def fd4 (s : Core) : Core :=
  releaseS v (releaseS v (fd2 v s) (s.nodes.getX v).t1) (s.nodes.getX v).t2

/-- The state after `finishDrain v`. -/
def fdS (s : Core) : Core :=
  { fd4 v s with nodes := (fd4 v s).nodes.modify v fun n => { n with
    alive := false
    inTables := [] } }

end defs

@[simp] theorem run_getN (i : Nat) (s : Core) : (getN i).run s = .ok (s.nodes.getX i) s := rfl

theorem dropTable_run (hh v e : Nat) (s : Core) :
    (dropTable hh v e).run s = .ok ⟨⟩ (dropTableS v hh s e) := by
  unfold dropTable dropTableS inTablesOf setInTables
  by_cases h0 : hh = 0
  · subst h0
    simp only [beq_self_eq_true, ite_true, run_bind, run_get, run_pure]
    split <;> rfl
  · simp only [show (hh == 0) = false by simpa using h0, Bool.false_eq_true, ite_false, run_bind,
        run_pure, run_getN]
    split <;> rfl

theorem dropEntry_run (v T : Nat) (s : Core) (h : v ∈ (s.nodes.getX T).order) :
    (dropEntry v T).run s = .ok ⟨⟩ (dropEntryS v s T) := by
  unfold dropEntry dropEntryS
  simp only [run_getN_bind]
  rw [ite_eq_right (by simpa using h)]
  rfl

theorem release_run (v t : Nat) (s : Core) : (release v t).run s = .ok ⟨⟩ (releaseS v s t) := by
  unfold release releaseS
  simp only [run_getN_bind]
  split <;> rfl

theorem dropTableS_table (v hh : Nat) (s : Core) (e T : Nat) :
    ((dropTableS v hh s e).nodes.getX T).table = (s.nodes.getX T).table := by
  unfold dropTableS; split_ifs <;> simp [Array.getX_modify] ; split <;> rfl

theorem foldl_dropTableS_table (v hh : Nat) (l : List Nat) (s : Core) (T : Nat) :
    ((l.foldl (dropTableS v hh) s).nodes.getX T).table = (s.nodes.getX T).table := by
  induction l generalizing s with
  | nil => rfl
  | cons x t ih => simp only [List.foldl_cons]; rw [ih, dropTableS_table]

theorem dropEntryS_other (v : Nat) (s : Core) (T T' : Nat) (h : T ≠ T') :
    (dropEntryS v s T).nodes.getX T' = s.nodes.getX T' := by
  unfold dropEntryS; simp [Array.getX_modify, h]

/-- **Running `finishDrain`**: every table holding the ghost still lists it. -/
theorem finishDrain_run (v : Nat) (s : Core) (hnd : (s.nodes.getX v).inTables.Nodup)
    (hT : ∀ T ∈ (s.nodes.getX v).inTables, v ∈ (s.nodes.getX T).order) :
    (finishDrain v).run s = .ok ⟨⟩ (fdS v s) := by
  unfold finishDrain fdS
  simp only [run_getN_bind]
  rw [run_bind, forM_run' _ _ _ (fun e t => dropTable_run _ v e t) s]
  simp only
  set s1 := (s.nodes.getX v).order.foldl (dropTableS v ((s.nodes.getX v).height - 1)) s with hs1
  rw [run_bind, forM_run _ _ (fun T t => dropEntryS v t T)
    (fun rest t => rest.Nodup ∧ ∀ T ∈ rest, v ∈ (t.nodes.getX T).order) s1
    ⟨hnd, fun T hT' => by
      change v ∈ ((s1.nodes.getX T).table.map (·.1))
      rw [foldl_dropTableS_table]; exact hT T hT'⟩
    (fun x rest t ⟨hn, hm⟩ => ⟨dropEntry_run v x t (hm x (by simp)),
      (List.nodup_cons.mp hn).2, fun T hT' => by
        rw [dropEntryS_other v t x T (fun e => (List.nodup_cons.mp hn).1 (e ▸ hT'))]
        exact hm T (List.mem_cons_of_mem _ hT')⟩)]
  simp only
  rw [run_bind, release_run]; simp only
  rw [run_bind, release_run]; simp only
  rfl

/-- **A sweep call on an empty range finishes the drain.** -/
theorem drainStep_finish {s : Core} {v : Nat} (hal : (s.nodes.getX v).alive = true)
    (hf : (s.nodes.getX v).first = NIL) (hnd : (s.nodes.getX v).inTables.Nodup)
    (hT : ∀ T ∈ (s.nodes.getX v).inTables, v ∈ (s.nodes.getX T).order) :
    (drainStep v).run s = .ok false (fdS v s) := by
  unfold drainStep
  simp only [run_getP_bind, run_getN_bind, hal, Bool.not_true, Bool.false_eq_true, ite_false,
    hf, beq_self_eq_true, ite_true]
  rw [run_bind, finishDrain_run v s hnd hT]
  rfl

/-! ### The state after `finishDrain` -/

theorem dropTableS_getX (v hh : Nat) (s : Core) (e u : Nat) :
    (dropTableS v hh s e).nodes.getX u =
      if u = e ∧ hh ≠ 0 ∧ u < s.nodes.size then
        { s.nodes.getX u with inTables := (s.nodes.getX u).inTables.erase v }
      else s.nodes.getX u := by
  unfold dropTableS
  by_cases h0 : hh = 0
  · simp only [h0, beq_self_eq_true, ite_true]; split <;> simp
  · simp only [show (hh == 0) = false by simpa using h0, Bool.false_eq_true, ite_false]
    split
    · rw [Array.getX_modify]; by_cases hu : u = e
      · subst hu; simp [h0]
      · simp [hu, Ne.symm hu]
    · next hc =>
      by_cases hu : u = e
      · subst hu
        have : v ∉ (s.nodes.getX u).inTables := by simpa using hc
        rw [List.erase_of_not_mem this]; simp
      · simp [hu]

theorem dropTableS_size (v hh : Nat) (s : Core) (e : Nat) :
    (dropTableS v hh s e).nodes.size = s.nodes.size := by
  unfold dropTableS; split_ifs <;> simp

theorem dropTableS_cin (v hh : Nat) (s : Core) (e u : Nat) :
    (dropTableS v hh s e).cin.getX u =
      if u = e ∧ hh = 0 then (s.cin.getX u).erase v else s.cin.getX u := by
  unfold dropTableS
  by_cases h0 : hh = 0
  · simp only [h0, beq_self_eq_true, ite_true, and_true]
    split
    · rw [Array.getX_setX]; split <;> simp_all
    · next hc =>
      by_cases hu : u = e
      · subst hu
        have : v ∉ s.cin.getX u := by simpa using hc
        simp [List.erase_of_not_mem this]
      · simp [hu]
  · simp only [show (hh == 0) = false by simpa using h0, Bool.false_eq_true, ite_false, h0,
    and_false]
    split <;> rfl

theorem foldl_dropTableS (v hh : Nat) (l : List Nat) (hl : l.Nodup) (s : Core) :
    (∀ u, (l.foldl (dropTableS v hh) s).nodes.getX u =
      if u ∈ l ∧ hh ≠ 0 ∧ u < s.nodes.size then
        { s.nodes.getX u with inTables := (s.nodes.getX u).inTables.erase v }
      else s.nodes.getX u) ∧
    (l.foldl (dropTableS v hh) s).nodes.size = s.nodes.size ∧
    (∀ u, (l.foldl (dropTableS v hh) s).cin.getX u =
      if u ∈ l ∧ hh = 0 then (s.cin.getX u).erase v else s.cin.getX u) ∧
    (l.foldl (dropTableS v hh) s).path = s.path ∧ (l.foldl (dropTableS v hh) s).lpar = s.lpar ∧
    (l.foldl (dropTableS v hh) s).P = s.P ∧ (l.foldl (dropTableS v hh) s).C = s.C ∧
    (l.foldl (dropTableS v hh) s).resJob = s.resJob := by
  induction l generalizing s with
  | nil => simp
  | cons x t ih =>
    have hx := List.nodup_cons.mp hl
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := ih hx.2 (dropTableS v hh s x)
    simp only [List.foldl_cons]
    have hp : (dropTableS v hh s x).path = s.path ∧ (dropTableS v hh s x).lpar = s.lpar ∧
        (dropTableS v hh s x).P = s.P ∧ (dropTableS v hh s x).C = s.C ∧
        (dropTableS v hh s x).resJob = s.resJob := by
      unfold dropTableS; split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    refine ⟨fun u => ?_, by rw [h2, dropTableS_size], fun u => ?_, h4.trans hp.1, h5.trans hp.2.1,
      h6.trans hp.2.2.1, h7.trans hp.2.2.2.1, h8.trans hp.2.2.2.2⟩
    · rw [h1, dropTableS_size, dropTableS_getX]
      by_cases hu : u = x
      · subst hu; simp [hx.1]
      · simp only [hu, false_and, ite_false, List.mem_cons, false_or]
    · rw [h3, dropTableS_cin]
      by_cases hu : u = x
      · subst hu; simp [hx.1]
      · simp [hu]

theorem foldl_dropEntryS (v : Nat) (l : List Nat) (hl : l.Nodup) (s : Core) :
    (∀ u, (l.foldl (dropEntryS v) s).nodes.getX u =
      if u ∈ l ∧ u < s.nodes.size then
        { s.nodes.getX u with
          table := assocErase (s.nodes.getX u).table v
          side := assocErase (s.nodes.getX u).side v }
      else s.nodes.getX u) ∧
    (l.foldl (dropEntryS v) s).nodes.size = s.nodes.size ∧
    (l.foldl (dropEntryS v) s).cin = s.cin ∧
    (l.foldl (dropEntryS v) s).path = s.path ∧ (l.foldl (dropEntryS v) s).lpar = s.lpar ∧
    (l.foldl (dropEntryS v) s).P = s.P ∧ (l.foldl (dropEntryS v) s).C = s.C ∧
    (l.foldl (dropEntryS v) s).resJob = s.resJob := by
  induction l generalizing s with
  | nil => simp
  | cons x t ih =>
    have hx := List.nodup_cons.mp hl
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := ih hx.2 (dropEntryS v s x)
    simp only [List.foldl_cons]
    have hsz : (dropEntryS v s x).nodes.size = s.nodes.size := by simp [dropEntryS]
    refine ⟨fun u => ?_, by rw [h2, hsz], h3, h4, h5, h6, h7, h8⟩
    rw [h1, hsz]
    by_cases hu : u = x
    · subst hu
      simp only [hx.1, false_and, ite_false, List.mem_cons, true_or, true_and]
      simp [dropEntryS, Array.getX_modify]
    · simp only [List.mem_cons, hu, false_or]
      have : (dropEntryS v s x).nodes.getX u = s.nodes.getX u := by
        simp [dropEntryS, Array.getX_modify, Ne.symm hu]
      rw [this]

theorem releaseS_getX (v : Nat) (s : Core) (t u : Nat) :
    (releaseS v s t).nodes.getX u =
      if u = t ∧ (s.nodes.getX t).overflowOf = v ∧ u < s.nodes.size then
        { s.nodes.getX u with overflowOf := NIL }
      else s.nodes.getX u := by
  unfold releaseS
  split
  · next hc =>
    simp only [beq_iff_eq] at hc
    rw [Array.getX_modify]
    by_cases hu : u = t
    · subst hu; simp [hc]
    · simp [hu, Ne.symm hu]
  · next hc =>
    simp only [beq_iff_eq] at hc
    by_cases hu : u = t
    · subst hu; simp [hc]
    · simp [hu]

theorem releaseS_size (v : Nat) (s : Core) (t : Nat) : (releaseS v s t).nodes.size =
  s.nodes.size := by
  unfold releaseS; split <;> simp

theorem releaseS_rest (v : Nat) (s : Core) (t : Nat) :
    (releaseS v s t).cin = s.cin ∧ (releaseS v s t).path = s.path ∧ (releaseS v s t).lpar = s.lpar ∧
      (releaseS v s t).P = s.P ∧ (releaseS v s t).C = s.C ∧ (releaseS v s t).resJob = s.resJob := by
  unfold releaseS; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

section fd
variable (v : Nat) (s : Core) (hno : (s.nodes.getX v).order.Nodup)
  (hni : (s.nodes.getX v).inTables.Nodup)

include hno in
theorem fd1_getX (u : Nat) : (fd1 v s).nodes.getX u =
    if u ∈ (s.nodes.getX v).order ∧ (s.nodes.getX v).height - 1 ≠ 0 ∧ u < s.nodes.size then
      { s.nodes.getX u with inTables := (s.nodes.getX u).inTables.erase v }
    else s.nodes.getX u :=
  (foldl_dropTableS v _ _ hno s).1 u

include hno in
theorem fd1_size : (fd1 v s).nodes.size = s.nodes.size := (foldl_dropTableS v _ _ hno s).2.1

include hno hni in
theorem fd2_getX (u : Nat) : (fd2 v s).nodes.getX u =
    if u ∈ (s.nodes.getX v).inTables ∧ u < s.nodes.size then
      { (fd1 v s).nodes.getX u with
        table := assocErase ((fd1 v s).nodes.getX u).table v
        side := assocErase ((fd1 v s).nodes.getX u).side v }
    else (fd1 v s).nodes.getX u := by
  unfold fd2; rw [(foldl_dropEntryS v _ hni (fd1 v s)).1, fd1_size v s hno]

include hno hni in
theorem fd2_size : (fd2 v s).nodes.size = s.nodes.size := by
  unfold fd2; rw [(foldl_dropEntryS v _ hni (fd1 v s)).2.1, fd1_size v s hno]

end fd

theorem fdS_nodes (v : Nat) (s : Core) :
    (fdS v s).nodes = (fd4 v s).nodes.modify v fun n => { n with alive := false, inTables := []
      } := by
  simp only [fdS]

/-- **The nodes after `finishDrain v`.** -/
theorem fdS_getX (v : Nat) (s : Core) (hv : v < s.nodes.size)
    (hno : (s.nodes.getX v).order.Nodup) (hni : (s.nodes.getX v).inTables.Nodup)
    (hvo : (s.nodes.getX v).height - 1 ≠ 0 → v ∉ (s.nodes.getX v).order)
    (hvi : v ∉ (s.nodes.getX v).inTables)
    (h1 : v ≠ (s.nodes.getX v).t1) (h2 : v ≠ (s.nodes.getX v).t2)
    (h12 : (s.nodes.getX v).t1 ≠ (s.nodes.getX v).t2)
    (ho1 : (s.nodes.getX v).height - 1 ≠ 0 → (s.nodes.getX v).t1 ∉ (s.nodes.getX v).order)
    (ho2 : (s.nodes.getX v).height - 1 ≠ 0 → (s.nodes.getX v).t2 ∉ (s.nodes.getX v).order)
    (hi1 : (s.nodes.getX v).t1 ∉ (s.nodes.getX v).inTables)
    (hi2 : (s.nodes.getX v).t2 ∉ (s.nodes.getX v).inTables)
    (hoi : ∀ u, u ∈ (s.nodes.getX v).order → (s.nodes.getX v).height - 1 ≠ 0 →
      u ∉ (s.nodes.getX v).inTables) (u : Nat) :
    (fdS v s).nodes.getX u =
      if u = v then { s.nodes.getX u with alive := false, inTables := [] }
      else if u ∈ (s.nodes.getX v).order ∧ (s.nodes.getX v).height - 1 ≠ 0 ∧ u < s.nodes.size then
        { s.nodes.getX u with inTables := (s.nodes.getX u).inTables.erase v }
      else if u ∈ (s.nodes.getX v).inTables ∧ u < s.nodes.size then
        { s.nodes.getX u with
          table := assocErase (s.nodes.getX u).table v
          side := assocErase (s.nodes.getX u).side v }
      else if (u = (s.nodes.getX v).t1 ∨ u = (s.nodes.getX v).t2) ∧
          (s.nodes.getX u).overflowOf = v ∧ u < s.nodes.size then
        { s.nodes.getX u with overflowOf := NIL }
      else s.nodes.getX u := by
  have hs2 := fd2_size v s hno hni
  have t1e : (fd2 v s).nodes.getX (s.nodes.getX v).t1 = s.nodes.getX (s.nodes.getX v).t1 := by
    rw [fd2_getX v s hno hni, ite_eq_right (fun h => hi1 h.1), fd1_getX v s hno,
      ite_eq_right (fun h => ho1 h.2.1 h.1)]
  have t2e : (releaseS v (fd2 v s) (s.nodes.getX v).t1).nodes.getX (s.nodes.getX v).t2 =
      s.nodes.getX (s.nodes.getX v).t2 := by
    rw [releaseS_getX, ite_eq_right (fun h => h12 h.1.symm), fd2_getX v s hno hni,
      ite_eq_right (fun h => hi2 h.1),
      fd1_getX v s hno, ite_eq_right (fun h => ho2 h.2.1 h.1)]
  have hs4 : (fd4 v s).nodes.size = s.nodes.size := by
    unfold fd4; rw [releaseS_size, releaseS_size, hs2]
  have h4 : (fd4 v s).nodes.getX u =
      if u = (s.nodes.getX v).t2 ∧ (s.nodes.getX (s.nodes.getX v).t2).overflowOf = v ∧ u <
        s.nodes.size then
        { (releaseS v (fd2 v s) (s.nodes.getX v).t1).nodes.getX u with overflowOf := NIL }
      else (releaseS v (fd2 v s) (s.nodes.getX v).t1).nodes.getX u := by
    unfold fd4; rw [releaseS_getX, t2e, releaseS_size, hs2]
  have h3 : (releaseS v (fd2 v s) (s.nodes.getX v).t1).nodes.getX u =
      if u = (s.nodes.getX v).t1 ∧ (s.nodes.getX (s.nodes.getX v).t1).overflowOf = v ∧ u <
        s.nodes.size then
        { (fd2 v s).nodes.getX u with overflowOf := NIL }
      else (fd2 v s).nodes.getX u := by
    rw [releaseS_getX, t1e, hs2]
  rw [fdS_nodes, Array.getX_modify, hs4, h4, h3, fd2_getX v s hno hni, fd1_getX v s hno]
  by_cases huv : u = v
  · subst huv
    have hvo' : ¬ (u ∈ (s.nodes.getX u).order ∧ ¬ (s.nodes.getX u).height - 1 = 0) :=
      fun h => hvo h.2 h.1
    simp [hv, h1, h2, hvo', hvi]
  · simp only [Ne.symm huv, false_and, ite_false, huv]
    by_cases hu1 : u ∈ (s.nodes.getX v).order ∧ (s.nodes.getX v).height - 1 ≠ 0 ∧ u < s.nodes.size
    · have hi : u ∉ (s.nodes.getX v).inTables := hoi u hu1.1 hu1.2.1
      have hn1 : u ≠ (s.nodes.getX v).t1 := fun e => ho1 hu1.2.1 (e ▸ hu1.1)
      have hn2 : u ≠ (s.nodes.getX v).t2 := fun e => ho2 hu1.2.1 (e ▸ hu1.1)
      simp [hu1, hi, hn1, hn2]
    · simp only [ite_eq_right hu1]
      by_cases hu2 : u ∈ (s.nodes.getX v).inTables ∧ u < s.nodes.size
      · have hn1 : u ≠ (s.nodes.getX v).t1 := fun e => hi1 (e ▸ hu2.1)
        have hn2 : u ≠ (s.nodes.getX v).t2 := fun e => hi2 (e ▸ hu2.1)
        simp [hu2, hn1, hn2]
      · simp only [hu2, ite_false]
        by_cases hu3 : u = (s.nodes.getX v).t1
        · subst hu3
          simp [h12]
        · by_cases hu4 : u = (s.nodes.getX v).t2
          · subst hu4; simp [hu3]
          · simp [hu3, hu4]

end OrderMaintenance.Proof.Top
