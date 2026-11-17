/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.GlueCore
public import LeanPool.OrderMaintenance.Impl.Init


/-!
# M6: the capacities (step 4 of the glue)

The Level M side conditions (`TopCaps`, `GCaps`, `InsCaps`, `PQCaps`, ...) bound the record
counts of a core. Level F bounds the element and chunk counts already (`E.size = count + 1`,
`CountInv.chunks`). Here are the bounds Level F lacks:
* nodes: a potential `nodes.size + topMu ≤ nb0 + topJ · C.size`. A drain start adds 2 nodes and
  lowers the job measure by `s ≥ 3`; no other step adds nodes; a split start adds 2 chunks and a
  job of measure at most `topJ`.
-/


@[expose] public section

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### Steps that keep the node count -/

/-- The node count is unchanged. -/
def NS (s s' : Core) : Prop := s'.nodes.size = s.nodes.size

instance : IsPre NS := ⟨fun _ => rfl, fun _ _ _ h1 h2 => h2.trans h1⟩

theorem ns_modN (i : Nat) (f : Node → Node) : Pres NS (modN i f) := by
  unfold modN; pres; intro s; simp [NS]
theorem ns_setPath (c : Nat) (p : Array Nat) : Pres NS (setPath c p) := by
  unfold setPath; pres; intro s; rfl
theorem ns_setPathAt (c j v : Nat) : Pres NS (setPathAt c j v) := by
  unfold setPathAt; pres; intro s; rfl
theorem ns_setLpar (c v : Nat) : Pres NS (setLpar c v) := by
  unfold setLpar; pres; intro s; rfl
theorem ns_inTablesOf (e h : Nat) : Pres NS (inTablesOf e h) := by
  unfold inTablesOf; pres [pres_getN _]
theorem ns_setInTables (e h : Nat) (l : List Nat) : Pres NS (setInTables e h l) := by
  unfold setInTables; pres [ns_modN _ _]; intro s; rfl
theorem ns_guardTag (c t : Nat) : Pres NS (guardTag c t) := by
  unfold guardTag; pres [pres_getC _]
theorem ns_guardedSetTag (c t : Nat) : Pres NS (guardedSetTag c t) := by
  unfold guardedSetTag modC; pres [ns_guardTag _ _]; intro s; rfl
theorem ns_dropTable (h v e : Nat) : Pres NS (dropTable h v e) := by
  unfold dropTable; pres [ns_inTablesOf _ _, ns_setInTables _ _ _]
theorem ns_dropEntry (v T : Nat) : Pres NS (dropEntry v T) := by
  unfold dropEntry; pres [pres_getN _, ns_modN _ _]
theorem ns_release (v t : Nat) : Pres NS (release v t) := by
  unfold release; pres [pres_getN _, ns_modN _ _]
theorem ns_finishDrain (v : Nat) : Pres NS (finishDrain v) := by
  unfold finishDrain
  pres [pres_getN _, ns_dropTable _ _ _, ns_dropEntry _ _, ns_release _ _, ns_modN _ _]
theorem ns_drainStep (v : Nat) : Pres NS (drainStep v) := by
  unfold drainStep
  pres [pres_getP, pres_getN _, ns_finishDrain _, pres_getPath _, pres_getC _,
    ns_guardedSetTag _ _, ns_setPathAt _ _ _, ns_modN _ _, pres_belowOf _ _]
theorem ns_fundLoop (j : Job) (v up src k : Nat) : Pres NS (fundLoop j v up src k) := by
  unfold fundLoop; pres [pres_getP, ns_drainStep _]
theorem ns_afterDrain (j : Job) (v up : Nat) : Pres NS (afterDrain j v up) := by
  unfold afterDrain; pres [pres_getN _, ns_fundLoop _ _ _ _ _]

theorem Pres.ok {R : Core → Core → Prop} {α : Type} {m : CM α} (h : Pres R m) {s s' : Core} {a : α}
    (hr : m.run s = .ok a s') : R s s' := by
  have := h s; rw [hr] at this; exact this

/-! ### Top steps keep the preparation state -/

/-- The preparation state is unchanged. -/
def TP (s s' : Core) : Prop := s'.prep = s.prep

instance : IsPre TP := ⟨fun _ => rfl, fun _ _ _ h1 h2 => h2.trans h1⟩

theorem tp_modN (i : Nat) (f : Node → Node) : Pres TP (modN i f) := by
  unfold modN; pres; intro s; rfl
theorem tp_setPath (c : Nat) (p : Array Nat) : Pres TP (setPath c p) := by
  unfold setPath; pres; intro s; rfl
theorem tp_setPathAt (c j v : Nat) : Pres TP (setPathAt c j v) := by
  unfold setPathAt; pres; intro s; rfl
theorem tp_setLpar (c v : Nat) : Pres TP (setLpar c v) := by
  unfold setLpar; pres; intro s; rfl
theorem tp_inTablesOf (e h : Nat) : Pres TP (inTablesOf e h) := by
  unfold inTablesOf; pres [pres_getN _]
theorem tp_setInTables (e h : Nat) (l : List Nat) : Pres TP (setInTables e h l) := by
  unfold setInTables; pres [tp_modN _ _]; intro s; rfl
theorem tp_newNode (h : Nat) : Pres TP (newNode h) := by
  unfold newNode; pres; intro s; rfl
theorem tp_guardTag (c t : Nat) : Pres TP (guardTag c t) := by
  unfold guardTag; pres [pres_getC _]
theorem tp_guardedSetTag (c t : Nat) : Pres TP (guardedSetTag c t) := by
  unfold guardedSetTag modC; pres [tp_guardTag _ _]; intro s; rfl
theorem tp_roomNextTo (t e : Nat) (b : Bool) : Pres TP (roomNextTo t e b) := by
  unfold roomNextTo; pres [pres_getP, pres_getN _]
theorem tp_tableInsert (t e new : Nat) (b : Bool) (lab : Nat) :
    Pres TP (tableInsert t e new b lab) := by
  unfold tableInsert; pres [pres_getN _, tp_modN _ _]
theorem tp_sameDrain (a b : Nat) : Pres TP (sameDrain a b) := by
  unfold sameDrain; pres
theorem tp_addTable (h t e : Nat) : Pres TP (addTable h t e) := by
  unfold addTable; pres [tp_inTablesOf _ _, tp_setInTables _ _ _]
theorem tp_insertAroundIn (v v1 v2 : Nat) (q : Nat × Nat × Nat) :
    Pres TP (insertAroundIn v v1 v2 q) := by
  unfold insertAroundIn; pres [tp_tableInsert _ _ _ _ _]
theorem tp_setParent (h w e : Nat) : Pres TP (setParent h w e) := by
  unfold setParent; pres [tp_setLpar _ _, tp_modN _ _]
theorem tp_startDrain (v : Nat) : Pres TP (startDrain v) := by
  unfold startDrain
  pres [pres_getP, pres_getN _, tp_roomNextTo _ _ _, tp_newNode _, tp_insertAroundIn _ _ _ _,
    tp_modN _ _, tp_addTable _ _ _, tp_setParent _ _ _]
theorem tp_dropTable (h v e : Nat) : Pres TP (dropTable h v e) := by
  unfold dropTable; pres [tp_inTablesOf _ _, tp_setInTables _ _ _]
theorem tp_dropEntry (v T : Nat) : Pres TP (dropEntry v T) := by
  unfold dropEntry; pres [pres_getN _, tp_modN _ _]
theorem tp_release (v t : Nat) : Pres TP (release v t) := by
  unfold release; pres [pres_getN _, tp_modN _ _]
theorem tp_finishDrain (v : Nat) : Pres TP (finishDrain v) := by
  unfold finishDrain
  pres [pres_getN _, tp_dropTable _ _ _, tp_dropEntry _ _, tp_release _ _, tp_modN _ _]
theorem tp_drainStep (v : Nat) : Pres TP (drainStep v) := by
  unfold drainStep
  pres [pres_getP, pres_getN _, tp_finishDrain _, pres_getPath _, pres_getC _,
    tp_guardedSetTag _ _, tp_setPathAt _ _ _, tp_modN _ _, pres_belowOf _ _]
theorem tp_fundLoop (j : Job) (v up src k : Nat) : Pres TP (fundLoop j v up src k) := by
  unfold fundLoop; pres [pres_getP, tp_drainStep _]
theorem tp_afterDrain (j : Job) (v up : Nat) : Pres TP (afterDrain j v up) := by
  unfold afterDrain; pres [pres_getN _, tp_fundLoop _ _ _ _ _]
theorem tp_walkBody (j : Job) (v : Nat) : Pres TP (walkBody j v) := by
  unfold walkBody; pres [pres_getP, pres_getN _, tp_modN _ _, tp_startDrain _, tp_afterDrain _ _ _]
theorem tp_jobStep (j : Job) : Pres TP (jobStep j) := by
  unfold jobStep
  pres [pres_getP, pres_getPath _, tp_setPathAt _ _ _, pres_getN _, tp_modN _ _,
    pres_getLpar _, tp_walkBody _ _, tp_afterDrain _ _ _, tp_fundLoop _ _ _ _ _]
theorem tp_insertAroundPrep (x : Nat) : Pres TP (insertAroundPrep x) := by
  unfold insertAroundPrep
  pres [pres_getPath _, tp_roomNextTo _ _ _, pres_getN _, pres_getC _, pres_getLpar _]
theorem tp_insertAroundFinish (x y z : Nat) (tabs ly lz : List Nat) (lp : Nat) :
    Pres TP (insertAroundFinish x y z tabs ly lz lp) := by
  unfold insertAroundFinish joinChunk
  pres [pres_getP, tp_insertAroundIn _ _ _ _, tp_setPath _ _, tp_setInTables _ _ _,
    tp_setLpar _ _, tp_modN _ _]
theorem tp_insertAround (x y z : Nat) : Pres TP (insertAround x y z) := by
  unfold insertAround
  pres [tp_insertAroundPrep _, tp_guardedSetTag _ _, tp_insertAroundFinish _ _ _ _ _ _ _]


/-! ### `insertAround` keeps the node count -/

theorem ns_roomNextTo (t e : Nat) (b : Bool) : Pres NS (roomNextTo t e b) := by
  unfold roomNextTo; pres [pres_getP, pres_getN _]
theorem ns_tableInsert (t e new : Nat) (b : Bool) (lab : Nat) :
    Pres NS (tableInsert t e new b lab) := by
  unfold tableInsert; pres [pres_getN _, ns_modN _ _]
theorem ns_insertAroundIn (v v1 v2 : Nat) (q : Nat × Nat × Nat) :
    Pres NS (insertAroundIn v v1 v2 q) := by
  unfold insertAroundIn; pres [ns_tableInsert _ _ _ _ _]
theorem ns_insertAroundPrep (x : Nat) : Pres NS (insertAroundPrep x) := by
  unfold insertAroundPrep
  pres [pres_getPath _, ns_roomNextTo _ _ _, pres_getN _, pres_getC _, pres_getLpar _]
theorem ns_insertAroundFinish (x y z : Nat) (tabs ly lz : List Nat) (lp : Nat) :
    Pres NS (insertAroundFinish x y z tabs ly lz lp) := by
  unfold insertAroundFinish joinChunk
  pres [pres_getP, ns_insertAroundIn _ _ _ _, ns_setPath _ _, ns_setInTables _ _ _,
    ns_setLpar _ _, ns_modN _ _]
theorem ns_insertAround (x y z : Nat) : Pres NS (insertAround x y z) := by
  unfold insertAround
  pres [ns_insertAroundPrep _, ns_guardedSetTag _ _, ns_insertAroundFinish _ _ _ _ _ _ _]

/-! ### The node count across a job step -/

open OrderMaintenance.Proof.Top in
/-- **A walk step adds no nodes, or starts a drain**: 2 nodes, and the job measure drops by at
least 2. -/
theorem walk_nodes {s : Core} {cl : List Nat} {ord : Nat → List Nat} {dr n0 : Nat → Nat} {j :
  Job} {v : Nat}
    (hpc : j.pc = .walk (some v)) (hTP : TopParams s.P) (hI : InvJ (ts s) cl ord dr n0 (some j))
    {r : Option Job} {t1 : Core} (h : (walkBody j v).run s = .ok r t1) :
    t1.nodes.size = s.nodes.size ∨
      (t1.nodes.size = s.nodes.size + 2 ∧ (∃ j', r = some j') ∧
        ∀ j', r = some j' → jobLeft (ts t1) j' + 2 ≤ jobLeft (ts s) j) := by
  by_cases hv0 : v = NIL
  · subst hv0; rw [run_walkBody_nil] at h; injection h with _ e; subst e; exact Or.inl rfl
  by_cases hd : (nd (ts s) v).livePar ≠ NIL ∧ (nd (ts s) v).draining = false ∧
      (nd (ts s) v).overflowOf = NIL ∧ Wd s.P (ht (ts s) v) < (nd (ts s) v).weight + 2
  · obtain ⟨h1, h2, h3, h4⟩ := hd
    obtain ⟨side, hside, hlook⟩ := sp_side hpc hv0 hI h1 hTP h3 h4
    have hrun := sr_run hpc hv0 hI h1 hTP h3 h4 hside hlook
    have H := sr_hyps hpc hv0 hI h1 hTP h3 h4 hlook
    have hR := sr_topRel hpc hv0 hI h1 hTP h3 h4 hside hlook
    have hht : ht (ts (sdS (wiC s v) v side)) v = ht (ts s) v := by
      change (nd (ts (sdS (wiC s v) v side)) v).height = _
      rw [H.height v, ite_eq_right (by
        have := H.hv
        omega)]
    have hP : (ts (sdS (wiC s v) v side)).P = s.P := hR.rest.1
    have hsz := H.size
    rw [run_walkBody_drain j s v hv0 h1 h2 h3 h4 hrun] at h
    generalize sdS (wiC s v) v side = S at h hht hP hsz
    obtain ⟨hr, ht⟩ := EStateM.Result.ok.inj h
    subst hr; subst ht
    right
    refine ⟨hsz, ⟨_, rfl⟩, fun j' hj' => ?_⟩
    cases hj'
    have hHt := (sd_ht hpc hv0 hI h1).2
    have hs3 := hTP.s3
    simp only [jobLeft, hpc, ite_eq_right hv0, hht, hP, show (ts s).P = s.P from rfl]
    unfold walkLeft
    have e : s.P.H + 1 - ht (ts s) v = (s.P.H + 1 - (ht (ts s) v + 1)) + 1 := by
      have : (ts s).P.H = s.P.H := rfl; omega
    rw [e, Nat.add_mul, one_mul]; omega
  · left
    rw [run_walkBody_noDrain j s v hv0 hd] at h
    have := (ns_afterDrain _ _ _).ok h
    rw [this]; simp [wiC]

open OrderMaintenance.Proof.Top in
/-- **The node count across a job step**: `nodes.size + topMu` does not grow. -/
theorem node_step {s : Core} {job : Job} (hT : TopInv s) (hres : s.resJob = some job) {r :
  Option Job}
    {t1 : Core} (h : (jobStep job).run s = .ok r t1) :
    t1.nodes.size + topMu {
      t1 with
      resJob := r
    } ≤ s.nodes.size + topMu s := by
  obtain ⟨r', s', hrun, -, hμ⟩ := top_step sdOK hT hres
  rw [h] at hrun; injection hrun with e1 e2; subst e1; subst e2
  have hμs : topMu s = jobLeft (ts s) job := by simp only [topMu, hres]
  obtain ⟨hTP, cl, ord, dr, n0, hL, hC, hI⟩ := hT
  rw [hres] at hI
  have hcase : t1.nodes.size = s.nodes.size ∨ (t1.nodes.size = s.nodes.size + 2 ∧ (∃ j', r =
    some j') ∧
      ∀ j', r = some j' → jobLeft (ts t1) j' + 2 ≤ jobLeft (ts s) job) := by
    cases hpc : job.pc with
    | copy l =>
      rw [jobStep_copy hpc] at h
      obtain ⟨-, e⟩ := EStateM.Result.ok.inj h; subst e
      left; unfold copyC; dsimp only; split_ifs <;> simp
    | walk ov =>
      have hfin : finS (ts s) (some job) = ts s := by simp only [finS, hpc]
      rw [hfin] at hI
      cases ov with
      | none =>
        obtain ⟨hI', hl, hh⟩ := walkNone_inv hpc hI
        have h' : (walkBody {
          job with
          pc := .walk (some (lpr (ts s) job.y))
        } (lpr (ts s)
          job.y)).run s =
            .ok r t1 := by rw [OrderMaintenance.Impl.jobStep_walkNone hpc] at h; exact h
        have e : jobLeft (ts s) {
          job with
          pc := .walk (some (lpr (ts s) job.y))
        } = jobLeft (ts
          s) job := by
          simp only [jobLeft, hpc, ite_eq_right hl.1.1, hh]
        rw [← e]
        exact walk_nodes rfl hTP hI' h'
      | some v =>
        rw [OrderMaintenance.Impl.jobStep_walkSome hpc] at h
        exact walk_nodes hpc hTP hI h
    | afterDrain v up =>
      rw [OrderMaintenance.Impl.jobStep_after hpc] at h
      exact Or.inl ((ns_afterDrain _ _ _).ok h)
    | fund v up src k =>
      rw [OrderMaintenance.Impl.jobStep_fund hpc] at h
      exact Or.inl ((ns_fundLoop _ _ _ _ _).ok h)
  rw [hμs]
  cases r with
  | none =>
    have : topMu {
      t1 with
      resJob := none
    } = 0 := rfl
    rw [this]
    rcases hcase with e | ⟨-, ⟨j', hj'⟩, -⟩
    · omega
    · cases hj'
  | some j' =>
    have : topMu {
      t1 with
      resJob := some j'
    } = jobLeft (ts t1) j' := rfl
    rw [this]
    rcases hcase with e | ⟨e, -, hle⟩
    · have h2 : jobLeft (ts t1) j' < jobLeft (ts s) job := (hμ j' rfl).2.trans_eq hμs
      omega
    · have := hle j' rfl; omega

/-- **A split start** keeps the node count and the preparation state, and adds two chunks. -/
theorem split_frame {t t2 : Core} {x : Nat} (h : (splitChunkStart x).run t = .ok () t2) :
    t2.nodes.size = t.nodes.size ∧ t2.C.size = t.C.size + 2 ∧ t2.prep = t.prep ∧ t2.Gs = t.Gs := by
  unfold splitChunkStart at h
  simp only [run_get_bind, run_require_bind] at h
  split at h
  · simp only [run_newChunk_bind, run_modify_bind, Array.size_push] at h
    have hps : ({
      ({
        t with
        C := t.C.push {}
      } : Core) with
      C := (t.C.push {}).push {}
    } : Core) =
        push2 t := rfl
    rw [hps, run_bind] at h
    rcases hj : (insertAround x t.C.size (t.C.size + 1)).run
        (linkChunkPair (push2 t) x t.C.size (t.C.size + 1)) with ⟨job, s2⟩ | ⟨e, s2⟩
    · rw [hj] at h
      have hN := (ns_insertAround _ _ _).ok hj
      have hP := (tp_insertAround _ _ _).ok hj
      have hR := (top_insertAround _ _ _).ok hj
      simp only [markSplit_run] at h
      obtain ⟨-, e⟩ := EStateM.Result.ok.inj h; subst e
      have hl := (linkChunkPair_rest (s := push2 t) (x := x) (y := t.C.size) (z := t.C.size +
        1)).2.2.2.2.2.2.1
      refine ⟨hN, ?_, hP, by
        rw [show (markState s2 x t.C.size (t.C.size + 1) job).Gs = s2.Gs from rfl, hR.Gs]
        rfl⟩
      simp only [markState, Array.size_modify]
      rw [hR.Csize, hl]; simp [push2]
    · rw [hj] at h; simp at h
  · simp [] at h

/-! ### Top steps without path writes keep the paths and the chunk count -/

/-- The paths and the chunk count are unchanged. -/
def PCS (s s' : Core) : Prop := s'.path = s.path ∧ s'.C.size = s.C.size

instance : IsPre PCS := ⟨fun _ => ⟨rfl, rfl⟩, fun _ _ _ h1 h2 => ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩⟩

theorem pcs_modN (i : Nat) (f : Node → Node) : Pres PCS (modN i f) := by
  unfold modN; pres; intro s; simp [PCS]
theorem pcs_setLpar (c v : Nat) : Pres PCS (setLpar c v) := by
  unfold setLpar; pres; intro s; simp [PCS]
theorem pcs_inTablesOf (e h : Nat) : Pres PCS (inTablesOf e h) := by
  unfold inTablesOf; pres [pres_getN _]
theorem pcs_setInTables (e h : Nat) (l : List Nat) : Pres PCS (setInTables e h l) := by
  unfold setInTables; pres [pcs_modN _ _]; intro s; simp [PCS]
theorem pcs_newNode (h : Nat) : Pres PCS (newNode h) := by
  unfold newNode; pres; intro s; simp [PCS]
theorem pcs_guardTag (c t : Nat) : Pres PCS (guardTag c t) := by
  unfold guardTag; pres [pres_getC _]
theorem pcs_guardedSetTag (c t : Nat) : Pres PCS (guardedSetTag c t) := by
  unfold guardedSetTag modC; pres [pcs_guardTag _ _]; intro s; simp [PCS]
theorem pcs_roomNextTo (t e : Nat) (b : Bool) : Pres PCS (roomNextTo t e b) := by
  unfold roomNextTo; pres [pres_getP, pres_getN _]
theorem pcs_tableInsert (t e new : Nat) (b : Bool) (lab : Nat) :
    Pres PCS (tableInsert t e new b lab) := by
  unfold tableInsert; pres [pres_getN _, pcs_modN _ _]
theorem pcs_sameDrain (a b : Nat) : Pres PCS (sameDrain a b) := by
  unfold sameDrain; pres
theorem pcs_addTable (h t e : Nat) : Pres PCS (addTable h t e) := by
  unfold addTable; pres [pcs_inTablesOf _ _, pcs_setInTables _ _ _]
theorem pcs_insertAroundIn (v v1 v2 : Nat) (q : Nat × Nat × Nat) :
    Pres PCS (insertAroundIn v v1 v2 q) := by
  unfold insertAroundIn; pres [pcs_tableInsert _ _ _ _ _]
theorem pcs_setParent (h w e : Nat) : Pres PCS (setParent h w e) := by
  unfold setParent; pres [pcs_setLpar _ _, pcs_modN _ _]
theorem pcs_startDrain (v : Nat) : Pres PCS (startDrain v) := by
  unfold startDrain
  pres [pres_getP, pres_getN _, pcs_roomNextTo _ _ _, pcs_newNode _, pcs_insertAroundIn _ _ _ _,
    pcs_modN _ _, pcs_addTable _ _ _, pcs_setParent _ _ _]
theorem pcs_dropTable (h v e : Nat) : Pres PCS (dropTable h v e) := by
  unfold dropTable; pres [pcs_inTablesOf _ _, pcs_setInTables _ _ _]
theorem pcs_dropEntry (v T : Nat) : Pres PCS (dropEntry v T) := by
  unfold dropEntry; pres [pres_getN _, pcs_modN _ _]
theorem pcs_release (v t : Nat) : Pres PCS (release v t) := by
  unfold release; pres [pres_getN _, pcs_modN _ _]
theorem pcs_finishDrain (v : Nat) : Pres PCS (finishDrain v) := by
  unfold finishDrain
  pres [pres_getN _, pcs_dropTable _ _ _, pcs_dropEntry _ _, pcs_release _ _, pcs_modN _ _]

/-! ### Path rows beyond the chunks stay zero -/

open OrderMaintenance.Proof.Top

/-- The path rows of chunks not yet allocated read zero. -/
def PZ (s : Core) : Prop := ∀ c, s.C.size ≤ c → ∀ j, (s.path.getX c).getX j = 0

theorem PZ.of_frame {s s' : Core} (h : PZ s) (hC : s.C.size ≤ s'.C.size)
    (hp : ∀ c, s.C.size ≤ c → s'.path.getX c = s.path.getX c) : PZ s' := fun c hc j => by
  rw [hp c (by omega)]; exact h c (by omega) j

theorem PZ.setX {s s' : Core} (h : PZ s) (hC : s'.C.size = s.C.size) {y : Nat} {row : Array Nat}
    (hy : y < s.C.size) (hp : s'.path = s.path.setX y row) : PZ s' :=
  h.of_frame hC.ge fun c hc => by rw [hp, Array.getX_setX, ite_eq_right (by omega)]

theorem fd_frame {v : Nat} : ∀ (l : List Nat) (hh : Nat) (s : Core),
    (l.foldl (dropTableS v hh) s).path = s.path ∧ (l.foldl (dropTableS v hh) s).C = s.C
  | [], _, _ => ⟨rfl, rfl⟩
  | e :: l, hh, s => by
    simp only [List.foldl_cons]
    obtain ⟨a, b⟩ := fd_frame l hh (dropTableS v hh s e)
    rw [a, b]; unfold dropTableS; split_ifs <;> exact ⟨rfl, rfl⟩

theorem fe_frame {v : Nat} : ∀ (l : List Nat) (s : Core),
    (l.foldl (dropEntryS v) s).path = s.path ∧ (l.foldl (dropEntryS v) s).C = s.C
  | [], _ => ⟨rfl, rfl⟩
  | e :: l, s => by
    simp only [List.foldl_cons]
    obtain ⟨a, b⟩ := fe_frame l (dropEntryS v s e)
    rw [a, b]; exact ⟨rfl, rfl⟩

theorem releaseS_frame (v t : Nat) (s : Core) : (releaseS v s t).path = s.path ∧ (releaseS v s
  t).C = s.C := by
  unfold releaseS; split_ifs <;> exact ⟨rfl, rfl⟩

open OrderMaintenance.Proof.Top in
theorem fd4_frame (v : Nat) (s : Core) : (fd4 v s).path = s.path ∧ (fd4 v s).C = s.C := by
  unfold fd4 fd2 fd1
  obtain ⟨a1, b1⟩ := releaseS_frame v (s.nodes.getX v).t2
    (releaseS v ((s.nodes.getX v).inTables.foldl (dropEntryS v)
      ((s.nodes.getX v).order.foldl (dropTableS v ((s.nodes.getX v).height - 1)) s))
        (s.nodes.getX v).t1)
  obtain ⟨a2, b2⟩ := releaseS_frame v (s.nodes.getX v).t1 ((s.nodes.getX v).inTables.foldl
    (dropEntryS v)
      ((s.nodes.getX v).order.foldl (dropTableS v ((s.nodes.getX v).height - 1)) s))
  obtain ⟨a3, b3⟩ := fe_frame (v := v) (s.nodes.getX v).inTables
      ((s.nodes.getX v).order.foldl (dropTableS v ((s.nodes.getX v).height - 1)) s)
  obtain ⟨a4, b4⟩ := fd_frame (v := v) (s.nodes.getX v).order ((s.nodes.getX v).height - 1) s
  exact ⟨a1.trans (a2.trans (a3.trans a4)), b1.trans (b2.trans (b3.trans b4))⟩

theorem fdS_frame (v : Nat) (s : Core) : (fdS v s).path = s.path ∧ (fdS v s).C = s.C := by
  unfold fdS; exact fd4_frame v s

open OrderMaintenance.Proof.Top in
theorem dsS_frame (s : Core) (v tag : Nat) :
    (dsS s v tag).path = s.path.setX (dsY s v) ((s.path.getX (dsY s v)).setX (s.nodes.getX
      v).height (dsT s v)) ∧
    (dsS s v tag).C.size = s.C.size := by
  unfold dsS; dsimp only; split_ifs <;> simp

open OrderMaintenance.Proof.Top in
/-- **A sweep step keeps the zero rows** and the chunk count. -/
theorem drain_pz {s : Core} {cl : List Nat} {ord : Nat → List Nat} (S : Shape (ts s) cl ord) {v
  : Nat}
    (hg : ghostN (ts s) v) (hcl : CLok s cl) {b : Bool} {t : Core} (h : (drainStep v).run s =
      .ok b t) :
    t.C.size = s.C.size ∧ (PZ s → PZ t) := by
  by_cases hemp : rng (ts s) cl v = []
  · obtain ⟨hal, hf, hnd, hT, -⟩ := S.drain_finish_hyps hg hemp
    rw [drainStep_finish hal hf hnd hT] at h
    obtain ⟨-, e⟩ := EStateM.Result.ok.inj h; subst e
    obtain ⟨a, b⟩ := fdS_frame v s
    exact ⟨by rw [b], fun hz => hz.of_frame (by rw [b]) fun c _ => by rw [a]⟩
  · obtain ⟨hal, hf, hside, hsz, hpt, htb, hpv, hvb, hold, hok, -, -, -, -, -, -, -, hycl, -⟩ :=
      S.drain_move_hyps hg hemp hcl.1
    rw [drainStep_move hal hf hside hsz hpt htb hpv hvb hold hok] at h
    obtain ⟨-, e⟩ := EStateM.Result.ok.inj h; subst e
    obtain ⟨a, b⟩ := dsS_frame s v _
    exact ⟨b, fun hz => hz.setX b ((hcl.2 _).mp hycl).2 a⟩

/-- **The funding loop keeps the zero rows** and the chunk count. -/
theorem fund_pz {s : Core} {cl : List Nat} {ord : Nat → List Nat} {dr n0 : Nat → Nat} {j : Job}
    {v up src k : Nat} (hcl : CLok s cl) (hI : InvJ (ts s) cl ord dr n0 (some {
      j with
      pc := .fund v up src k
    }))
    {r : Option Job} {t : Core} (h : (fundLoop j v up src k).run s = .ok r t) :
    t.C.size = s.C.size ∧ (PZ s → PZ t) := by
  obtain ⟨-, hat⟩ := hI.job _ rfl
  simp only [JobAt] at hat
  obtain ⟨-, -, -, hg, -, -⟩ := hat
  unfold fundLoop at h
  simp only [run_getP_bind] at h
  split at h
  · rw [run_bind] at h
    rcases hd : (drainStep src).run s with ⟨b, t'⟩ | ⟨e, t'⟩
    · rw [hd] at h
      obtain ⟨hC, hz⟩ := drain_pz hI.shape hg hcl hd
      cases b <;> (simp only [Bool.false_eq_true, ↓reduceIte, EStateM.run_pure,
          EStateM.Result.ok.injEq] at h; obtain ⟨-, rfl⟩ := h; exact ⟨hC, hz⟩)
    · rw [hd] at h; simp at h
  · simp only [EStateM.run_pure, EStateM.Result.ok.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨rfl, id⟩

/-- **A walk step keeps the zero rows** and the chunk count. -/
theorem walk_pz {s : Core} {cl : List Nat} {ord : Nat → List Nat} {dr n0 : Nat → Nat} {j : Job}
  {v : Nat}
    (hpc : j.pc = .walk (some v)) (hcl : CLok s cl) (hI : InvJ (ts s) cl ord dr n0 (some j))
    {r : Option Job} {t1 : Core} (h : (walkBody j v).run s = .ok r t1) :
    t1.C.size = s.C.size ∧ (PZ s → PZ t1) := by
  by_cases hv0 : v = NIL
  · subst hv0; rw [run_walkBody_nil] at h; injection h with _ e; subst e; exact ⟨rfl, id⟩
  by_cases hd : (nd (ts s) v).livePar ≠ NIL ∧ (nd (ts s) v).draining = false ∧
      (nd (ts s) v).overflowOf = NIL ∧ Wd s.P (ht (ts s) v) < (nd (ts s) v).weight + 2
  · obtain ⟨h1, h2, h3, h4⟩ := hd
    unfold walkBody at h
    simp only [beq_iff_eq, hv0, ite_false, run_getP_bind, run_getN_bind, run_modN_bind] at h
    rw [ite_eq_left (by
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true', beq_iff_eq,
        decide_eq_true_eq]; exact ⟨⟨⟨h1, h2⟩, h3⟩, by unfold Wd ht at h4; exact h4⟩), run_bind] at h
    rcases hs : (startDrain v).run {
      s with
      nodes := s.nodes.modify v fun n => {
        n with
        weight := n.weight + 2
      }
    }
      with ⟨u, t'⟩ | ⟨e, t'⟩
    · rw [hs] at h; simp only [EStateM.run_pure, EStateM.Result.ok.injEq] at h; obtain ⟨-, rfl⟩ := h
      obtain ⟨a, b⟩ := (pcs_startDrain v).ok hs
      exact ⟨b, fun hz => hz.of_frame b.ge fun c _ => by rw [a]⟩
    · rw [hs] at h; simp at h
  · rw [run_walkBody_noDrain j s v hv0 hd] at h
    have hI' := inv_winc hpc hv0 hI hd
    have hcl' := hcl.topRel (wiC_topRel s v)
    unfold afterDrain at h
    simp only [run_getN_bind] at h
    split at h
    · next hne =>
      have hsrc : ((wiC s v).nodes.getX v).overflowOf = srcOf (ts s) v := by
        change ((s.nodes.modify v _).getX v).overflowOf = _
        rw [Array.getX_modify]; split <;> rfl
      have hn : walkNext (ts s) j v = {
        j with
        pc := .fund v (nd (ts s) v).livePar (srcOf (ts s) v) 0
      } := by
        simp only [walkNext]; rw [ite_eq_right]; intro e
        rw [hsrc, e] at hne; exact absurd hne (by decide)
      rw [hn] at hI'
      rw [hsrc] at h
      obtain ⟨a, b⟩ := fund_pz hcl' hI' h
      exact ⟨a, fun hz => b (hz.of_frame le_rfl fun _ _ => rfl)⟩
    · simp only [EStateM.run_pure, EStateM.Result.ok.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact ⟨rfl, fun hz => hz.of_frame le_rfl fun _ _ => rfl⟩

theorem copyC_frame (s : Core) (j : Job) (l : Nat) : (copyC s j l).C.size = s.C.size ∧
    ∀ c, c ≠ j.y → c ≠ j.z → (copyC s j l).path.getX c = s.path.getX c := by
  unfold copyC; dsimp only
  refine ⟨by split_ifs <;> simp, fun c h1 h2 => ?_⟩
  split_ifs <;> simp [Array.getX_setX, h1, h2]

/-- **A job step keeps the zero rows** and the chunk count. -/
theorem path_step {s : Core} {job : Job} (hT : TopInv s) (hres : s.resJob = some job) {r :
  Option Job}
    {t1 : Core} (h : (jobStep job).run s = .ok r t1) : t1.C.size = s.C.size ∧ (PZ s → PZ t1) := by
  obtain ⟨hTP, cl, ord, dr, n0, hL, hC, hI⟩ := hT
  rw [hres] at hI
  have hcl : CLok s cl := ⟨hL, hC⟩
  cases hpc : job.pc with
  | copy l =>
    rw [jobStep_copy hpc] at h
    obtain ⟨-, e⟩ := EStateM.Result.ok.inj h; subst e
    obtain ⟨-, hy, hz, -, -, -⟩ := OrderMaintenance.Impl.job_chunks hcl (hI.job job rfl)
    obtain ⟨a, b⟩ := copyC_frame s job l
    exact ⟨a, fun hz' => hz'.of_frame a.ge fun c hc => b c (by
      have := ((hC _).mp hy).2
      omega)
      (by
        have := ((hC _).mp hz).2
        omega)⟩
  | walk ov =>
    have hfin : finS (ts s) (some job) = ts s := by simp only [finS, hpc]
    rw [hfin] at hI
    cases ov with
    | none =>
      obtain ⟨hI', -, -⟩ := walkNone_inv hpc hI
      have h' : (walkBody {
        job with
        pc := .walk (some (lpr (ts s) job.y))
      } (lpr (ts s)
        job.y)).run s =
          .ok r t1 := by rw [OrderMaintenance.Impl.jobStep_walkNone hpc] at h; exact h
      exact walk_pz rfl hcl hI' h'
    | some v =>
      rw [OrderMaintenance.Impl.jobStep_walkSome hpc] at h
      exact walk_pz hpc hcl hI h
  | afterDrain v up =>
    have hfin : finS (ts s) (some job) = ts s := by simp only [finS, hpc]
    rw [hfin] at hI
    obtain ⟨hrun, -, -⟩ := afterDrain_step hpc hI
    rw [hrun] at h; obtain ⟨-, e⟩ := EStateM.Result.ok.inj h; subst e
    exact ⟨rfl, id⟩
  | fund v up src k =>
    have hfin : finS (ts s) (some job) = ts s := by simp only [finS, hpc]
    rw [hfin, job_eta hpc] at hI
    rw [OrderMaintenance.Impl.jobStep_fund hpc] at h
    exact fund_pz hcl hI h

/-- The path rows from `n` on are unchanged. -/
def PY (n : Nat) (s s' : Core) : Prop := ∀ c, n ≤ c → s'.path.getX c = s.path.getX c

instance (n : Nat) : IsPre (PY n) := ⟨fun _ _ _ => rfl, fun _ _ _ h1 h2 c hc => (h2 c hc).trans
  (h1 c hc)⟩

section py
variable (n : Nat)
theorem py_modN (i : Nat) (f : Node → Node) : Pres (PY n) (modN i f) := by
  unfold modN; pres; intro s c _; rfl
theorem py_setPath {c : Nat} (p : Array Nat) (hc : c < n) : Pres (PY n) (setPath c p) := by
  unfold setPath; pres; intro s d hd; simp only [Array.getX_setX]; rw [ite_eq_right (by omega)]
theorem py_setLpar (c v : Nat) : Pres (PY n) (setLpar c v) := by
  unfold setLpar; pres; intro s c _; rfl
theorem py_setInTables (e h : Nat) (l : List Nat) : Pres (PY n) (setInTables e h l) := by
  unfold setInTables; pres [py_modN _ _ _]; intro s c _; rfl
theorem py_guardTag (c t : Nat) : Pres (PY n) (guardTag c t) := by
  unfold guardTag; pres [pres_getC _]
theorem py_guardedSetTag (c t : Nat) : Pres (PY n) (guardedSetTag c t) := by
  unfold guardedSetTag modC; pres [py_guardTag _ _ _]; intro s c _; rfl
theorem py_roomNextTo (t e : Nat) (b : Bool) : Pres (PY n) (roomNextTo t e b) := by
  unfold roomNextTo; pres [pres_getP, pres_getN _]
theorem py_tableInsert (t e new : Nat) (b : Bool) (lab : Nat) : Pres (PY n) (tableInsert t e new
  b lab) := by
  unfold tableInsert; pres [pres_getN _, py_modN _ _ _]
theorem py_insertAroundIn (v v1 v2 : Nat) (q : Nat × Nat × Nat) : Pres (PY n) (insertAroundIn v
  v1 v2 q) := by
  unfold insertAroundIn; pres [py_tableInsert _ _ _ _ _ _]
theorem py_insertAroundPrep (x : Nat) : Pres (PY n) (insertAroundPrep x) := by
  unfold insertAroundPrep
  pres [pres_getPath _, py_roomNextTo _ _ _ _, pres_getN _, pres_getC _, pres_getLpar _]
theorem py_insertAroundFinish {x y z : Nat} (tabs ly lz : List Nat) (lp : Nat) (hy : y < n) (hz
  : z < n) :
    Pres (PY n) (insertAroundFinish x y z tabs ly lz lp) := by
  unfold insertAroundFinish joinChunk
  pres [pres_getP, py_insertAroundIn _ _ _ _ _, py_setPath n _ hy, py_setPath n _ hz,
    py_setInTables _ _ _ _,
    py_setLpar _ _ _, py_modN _ _ _]
theorem py_insertAround {x y z : Nat} (hy : y < n) (hz : z < n) : Pres (PY n) (insertAround x y
  z) := by
  unfold insertAround
  pres [py_insertAroundPrep _ _, py_guardedSetTag _ _ _, py_insertAroundFinish n _ _ _ _ hy hz]
end py

/-- **A split start keeps the zero rows.** -/
theorem split_pz {t t2 : Core} {x : Nat} (h : (splitChunkStart x).run t = .ok () t2) (hz : PZ t)
  : PZ t2 := by
  have hC := (split_frame h).2.1
  unfold splitChunkStart at h
  simp only [run_get_bind, run_require_bind] at h
  split at h
  · simp only [run_newChunk_bind, run_modify_bind, Array.size_push] at h
    have hps : ({
      ({
        t with
        C := t.C.push {}
      } : Core) with
      C := (t.C.push {}).push {}
    } : Core) =
        push2 t := rfl
    rw [hps, run_bind] at h
    rcases hj : (insertAround x t.C.size (t.C.size + 1)).run
        (linkChunkPair (push2 t) x t.C.size (t.C.size + 1)) with ⟨job, s2⟩ | ⟨e, s2⟩
    · rw [hj] at h
      have hY := (py_insertAround (t.C.size + 2) (x := x) (by omega) (by omega)).ok hj
      simp only [markSplit_run] at h
      obtain ⟨-, e⟩ := EStateM.Result.ok.inj h; subst e
      intro c hc j
      rw [hC] at hc
      have e1 : (markState s2 x t.C.size (t.C.size + 1) job).path = s2.path := rfl
      rw [e1, hY c hc]
      exact hz c (by omega) j
    · rw [hj] at h; simp at h
  · simp [] at h

/-! ### A queue pop changes only the queue -/

instance : IsPre PQOnly := ⟨PQOnly.refl, fun _ _ _ => PQOnly.trans⟩

theorem pqo_pqDel (c : Nat) : Pres PQOnly (pqDel c) := by
  unfold pqDel
  pres <;> (intro s; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl⟩)

theorem pqo_pqPopMax : Pres PQOnly pqPopMax := by
  unfold pqPopMax; pres [pqo_pqDel _]

/-- A split start keeps the queue. -/
theorem split_pq {t t2 : Core} {x : Nat} (h : (splitChunkStart x).run t = .ok () t2) : PQSame t
  t2 := by
  unfold splitChunkStart at h
  simp only [run_get_bind, run_require_bind] at h
  split at h
  · simp only [run_newChunk_bind, run_modify_bind, Array.size_push] at h
    have hps : ({
      ({
        t with
        C := t.C.push {}
      } : Core) with
      C := (t.C.push {}).push {}
    } : Core) =
        push2 t := rfl
    rw [hps, run_bind] at h
    rcases hj : (insertAround x t.C.size (t.C.size + 1)).run
        (linkChunkPair (push2 t) x t.C.size (t.C.size + 1)) with ⟨job, s2⟩ | ⟨e, s2⟩
    · rw [hj] at h
      have hR := (top_insertAround _ _ _).ok hj
      simp only [markSplit_run] at h
      obtain ⟨-, e⟩ := EStateM.Result.ok.inj h; subst e
      obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8⟩ := hR.pq
      have hP : (markState s2 x t.C.size (t.C.size + 1) job).P.theta = t.P.theta := by
        change s2.P.theta = _; rw [hR.rest.1]; rfl
      exact ⟨q4, q2, q3, q1, q5, q6, q8, q7, hP⟩
    · rw [hj] at h; simp at h
  · simp [] at h

end OrderMaintenance.Proof

namespace OrderMaintenance.Impl

open OrderMaintenance.Model OrderMaintenance.Proof OrderMaintenance.Proof.Top
/-! ### The capacity conditions -/

/-- The chunk bound of a core of capacity `P.N` (`CountInv.chunks`). -/
def cb (P : Params) : Nat := 2 + 2 * (P.N / (P.theta + 1 - cmax P))
/-- The nodes of a fresh core. -/
def nb0 (P : Params) : Nat := P.H + 2
/-- The node bound. -/
def nbMax (P : Params) : Nat := nb0 P + topJ P * cb P

/-- **The node budget**: each chunk pays for the nodes of one job. -/
def NodeB (s : Core) : Prop := s.nodes.size + topMu s ≤ nb0 s.P + topJ s.P * s.C.size

/-- **The capacities as functions of the parameters.** -/
structure CapsOK (κ : Caps) (P : Params) : Prop where
  N : nbMax P + 2 ≤ κ.tbl .N
  NC : cb P ≤ κ.tbl .N
  C : cb P + 2 ≤ κ.tbl .C
  rc : nbMax P + 2 ≤ κ.lrec .children
  rs : nbMax P + 2 ≤ κ.lrec .side
  rt : nbMax P + 2 ≤ κ.lrec .table
  ri : nbMax P + 2 ≤ κ.lrec .inTab
  rcin : nbMax P + cb P + 2 ≤ κ.lrec .cin
  alp : nbMax P + cb P + 2 ≤ κ.arr .lpar
  lt : 162 ≤ κ.lcap .table
  ls : 322 ≤ κ.lcap .side
  li : 322 ≤ κ.lcap .inTab
  lcin : 322 ≤ κ.lcap .cin
  lc : 162 ≤ κ.lcap .children
  pw : κ.pw = P.H + 1
  E : P.N + 2 ≤ κ.tbl .E
  G : 2 * P.N + 4 ≤ κ.tbl .G
  fl : κ.tbl .G ≤ κ.lcap .freeG
  f0 : 0 < κ.lrec .freeG
  cC : cb P ≤ Ccap κ
  cB : P.N + 2 < Bcap κ
  pqC : κ.arr .pqPrev = Ccap κ ∧ κ.arr .pqWhere = Ccap κ
  pqB : κ.arr .nbNext = Bcap κ ∧ κ.arr .nbPrev = Bcap κ

theorem NodeB.le {s : Core} (h : NodeB s) (hC : s.C.size ≤ cb s.P) : s.nodes.size ≤ nbMax s.P := by
  unfold NodeB at h; unfold nbMax; have := Nat.mul_le_mul_left (topJ s.P) hC; omega

theorem topCaps_of {κ : Caps} {s : Core} (K : CapsOK κ s.P) (hN : NodeB s) (hC : s.C.size ≤ cb
  s.P) :
    TopCaps κ s := by
  have h := hN.le hC
  have := K.N; have := K.NC; have := K.C; have := K.rc; have := K.rs; have := K.rt; have := K.ri
  have := K.rcin; have := K.alp
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    K.lt, K.ls, K.li, K.lcin, K.lc, K.pw⟩

/-- **The capacity predicate of the reservation rounds.** -/
def Mc (κ : Caps) (P : Params) (t : Core) : Prop :=
  t.P = P ∧ NodeB t ∧ t.C.size ≤ cb P ∧ PQCaps κ t ∧ t.prep = none ∧ PZ t ∧ t.count ≤ P.N ∧
    t.Gs.size ≤ 2 + 2 * t.count

theorem Mc.caps {κ : Caps} {P : Params} (K : CapsOK κ P) {t : Core} (h : Mc κ P t) :
    TopCaps κ t ∧ PQCaps κ t ∧ t.prep = none ∧ ∀ c, t.C.size ≤ c → ∀ j, (t.path.getX c).getX j =
      0 := by
  obtain ⟨hP, hN, hC, hq, hpr, hz, -⟩ := h
  subst hP
  exact ⟨topCaps_of K hN hC, hq, hpr, hz⟩

theorem ts_eq_of {s s' : Core} (hP : s'.P = s.P) (hN : s'.nodes = s.nodes) (hp : s'.path = s.path)
    (hc : s'.cin = s.cin) (hl : s'.lpar = s.lpar) (hC : s'.C = s.C) : ts s' = ts s := by
  unfold ts; rw [hP, hN, hp, hc, hl, hC]

theorem mc_pop {κ : Caps} {P : Params} {t t1 : Core} {c : Nat} (h : Mc κ P t) (hp : pqPopMax.run
  t = .ok c t1) :
    Mc κ P t1 := by
  obtain ⟨hP, hN, hC, hq, hpr, hz, hcnt, hgs⟩ := h
  have F := pqo_pqPopMax.ok hp
  obtain ⟨-, eG, eC, eP, r⟩ := F
  obtain ⟨-, ecnt, -, -, -, -, -, epr, ejob, -, eN, epa, ecin, elp⟩ := r
  have hts : ts t1 = ts t := ts_eq_of eP eN epa ecin elp eC
  have hmu : topMu t1 = topMu t := by unfold topMu; rw [ejob, hts]
  refine ⟨eP.trans hP, ?_, by rw [eC]; exact hC, (pqPopMax_agree κ t (fun _ => 0) hq hp).2, by
    rw [epr]; exact hpr,
    fun d hd j => by rw [epa]; rw [eC] at hd; exact hz d hd j, by rw [ecnt]; exact hcnt,
    by rw [eG, ecnt]; exact hgs⟩
  unfold NodeB at hN ⊢; rw [eN, hmu, eC, eP]; exact hN

theorem mc_job {κ : Caps} {P : Params} {t : Core} {job : Job} (hT : TopInv t) (h : Mc κ P t)
    (hres : t.resJob = some job) {r : Option Job} {t1 : Core} (hr : (jobStep job).run t = .ok r
      t1) :
    Mc κ P {
      t1 with
      resJob := r
    } := by
  obtain ⟨hP, hN, hC, hq, hpr, hz, hcnt, hgs⟩ := h
  have hR := (top_jobStep job).ok hr
  have hn := node_step hT hres hr
  obtain ⟨hCs, hzz⟩ := path_step hT hres hr
  have hpp := (tp_jobStep job).ok hr
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8⟩ := hR.pq
  refine ⟨hR.rest.1.trans hP, ?_, by change t1.C.size ≤ _; rw [hCs]; exact hC,
    hq.of_same ⟨q4, q2, q3, q1, q5, q6, q8, q7, by change t1.P.theta = _; rw [hR.rest.1]⟩,
    by change t1.prep = _; rw [hpp]; exact hpr, hzz hz, by
      change t1.count ≤ _
      rw [hR.rest.2.1]
      exact hcnt,
    by
      change t1.Gs.size ≤ 2 + 2 * t1.count
      rw [hR.Gs, hR.rest.2.1]
      exact hgs⟩
  unfold NodeB at hN ⊢
  have e1 : ({
    t1 with
    resJob := r
  } : Core).P = t.P := hR.rest.1
  have e2 : ({
    t1 with
    resJob := r
  } : Core).C.size = t.C.size := hCs
  have eR : nb0 ({
    t1 with
    resJob := r
  } : Core).P + topJ ({
    t1 with
    resJob := r
  } : Core).P *
      ({
        t1 with
        resJob := r
      } : Core).C.size = nb0 t.P + topJ t.P * t.C.size := by rw [e1, e2]
  rw [eR]; exact le_trans hn hN

theorem mc_split {κ : Caps} {P : Params} {t t1 t2 : Core} {c : Nat} (h : Mc κ P t) (hnone :
  t.resJob = none)
    (hp : pqPopMax.run t = .ok c t1) (hs : (splitChunkStart c).run t1 = .ok () t2) (hP2 : t2.P = P)
    (hmu : topMu t2 ≤ topJ P) (hC2 : t2.C.size ≤ cb P) (hc2 : t2.count ≤ P.N) (hce : t2.count =
      t.count) :
    Mc κ P t2 := by
  have h1 := mc_pop h hp
  obtain ⟨hP, hN, -, -, -, -, -, -⟩ := h
  obtain ⟨hP1, hN1, hC1, hq1, hpr1, hz1, -, hgs1⟩ := h1
  obtain ⟨en, ec, epr, eg⟩ := split_frame hs
  have hc1 : t1.count = t.count := (pqo_pqPopMax.ok hp).rest.2.1
  refine ⟨hP2, ?_, hC2, hq1.of_same (split_pq hs), by rw [epr]; exact hpr1, split_pz hs hz1, hc2,
    by rw [eg, hce, ← hc1]; exact hgs1⟩
  have hmu0 : topMu t = 0 := by unfold topMu; rw [hnone]
  have F := pqo_pqPopMax.ok hp
  have eN : t1.nodes = t.nodes := F.rest.2.2.2.2.2.2.2.2.2.2.1
  have eC : t1.C = t.C := F.C
  unfold NodeB at hN ⊢
  rw [hmu0] at hN
  rw [hP2, en, ec, eN, eC, ← hP]
  rw [← hP] at hmu
  have := Nat.mul_add (topJ t.P) t.C.size 2
  omega

/-- The chunk bound at a state of the low invariant whose count is at most `N`. -/
theorem cb_of {t : Core} {L : List Nat} (hL : LowInv t L) (hc : t.count ≤ t.P.N) : t.C.size ≤ cb
  t.P := by
  obtain ⟨e, pops, hN⟩ := hL.cnt
  have h1 := hN.chunks (by
    have := hL.cp.I4
    omega)
  have h2 : t.count / (t.P.theta + 1 - cmax t.P) ≤ t.P.N / (t.P.theta + 1 - cmax t.P) :=
    Nat.div_le_div_right hc
  unfold cb; omega

/-- The element count of a core is its number of element records. -/
theorem E_size_le {s : Core} {A : Abs} (hI : INV s A) : s.E.size ≤ A.elist.length + 1 := by
  have := length_eq_of_mem_iff hI.eList.nodup List.nodup_range' (l' := List.range' 1 (s.E.size - 1))
    (fun c => by rw [hI.eAlloc c, List.mem_range'_1]; omega)
  simp at this; omega

/-- **The capacities at the start of an insertion**, from the capacity conditions and the
invariants. -/
theorem insCaps_of {κ : Caps} {s : Core} {L : List Nat} (K : CapsOK κ s.P) (hM : Mc κ s.P s)
    (hL : LowInv s L) (hcntL : s.count = L.length) (hcnt : s.count + 1 ≤ s.P.N) : InsCaps κ s := by
  obtain ⟨-, -, hC, hq, -, -, -, hgs⟩ := hM
  obtain ⟨A, hI, hel⟩ := hL.inv
  obtain ⟨s₀, hCI, -⟩ := hL.cinv
  have hE := E_size_le hI
  rw [hel, ← hcntL] at hE
  have := K.E; have := K.G; have := K.C; have := K.cC; have := K.cB
  refine ⟨by omega, by omega, by omega, K.fl, K.f0, hq, by omega, fun c hc => ?_⟩
  have h1 : (s.C.getX c).size = (celts s L c).length := hCI.csz c hc
  have h2 : (celts s L c).length ≤ L.length := List.length_filter_le _ _
  omega

/-- The cost bound of an insertion at Level M, at parameters `P`. -/
abbrev insBoundM (P : Params) : Nat := insBound P

/-- **An insertion agrees** at Level M under the cost invariant, the capacity conditions, the node
budget, the zero path rows, and no preparation in progress. -/
theorem insertAgreeM {P : Params} {n R : Nat} {L : List Nat} {s : Core} {x : Nat}
    (hC : CostInv (TIat TopInv P) topMu (topJ P) n R L s) (hsP : s.P = P)
    (hx : x ∈ L) (hk : 1 ≤ s.P.reservationBudget) (hR : topJ P / s.P.reservationBudget + 1 ≤ R)
      (hn : 1 ≤ n)
    (hsize : 2 + 2 * ((s.count + 1) / (s.P.theta + 1 - cmax s.P)) ≤ n + 1)
    (hcap : 2 + 2 * ((s.count + 1) / (s.P.theta + 1 - cmax s.P)) ≤ capT s.P)
    (hI5 : (s.P.theta : ℝ) + R * (OrderMaintenance.Zeroing.Hn (n - 1) + 1) ≤ s.P.T) (hh : Nat)
    {κ : Caps} (Lx : Loc) (hLx : Lx "x" = x) (hLh : Lx "h" = hh) (hpow : s.P.a = 2 ^ Nat.log2 s.P.a)
    (K : CapsOK κ P) (hcntL : s.count = L.length) (hcnt : s.count + 1 ≤ P.N) (hM0 : Mc κ P s) :
    ∃ s', (insertAfter x hh).run s = .ok s.E.size s' ∧
      (∃ L' m, evalF κ insertAfterP.body s Lx = .ok s' L' m ∧ L' "y" = s.E.size ∧ m ≤ insBound
        s.P) ∧
      CostInv (TIat TopInv P) topMu (topJ P) n R (OrderMaintenance.Spec.insertAfterL x s.E.size
        L) s' ∧
      s'.count = s.count + 1 ∧ s'.P = s.P ∧ Mc κ P s' := by
  have hTC : TopContract (TIat TopInv P) topMu (topJ P) capT := topContract'.at P
  have KI : InsCaps κ s := by
    subst hsP; exact insCaps_of K hM0 hC.low hcntL hcnt
  refine insertAgree hTC (fun t h => h.1) hC hx hk hR hn hsize hcap hI5 hh Lx hLx hLh hpow KI
    (Mc κ P)
    (fun t hts hjob hprt hCs hct hGt hq => ?_) (fun t h => h.caps K) (fun t c t1 h hp => mc_pop
      h hp)
    (fun L' s' j t job r t1 hI hM hjob hr _ => mc_job hI.2.1.1 hM hjob hr)
    (fun L' s' j t c t1 t2 hI hM hnone hp hs hI' => ?_)
  · -- the start of the reservation
    obtain ⟨-, hNB, -, -, hpr, hPZ, -, hgs⟩ := hM0
    have hPt : t.P = P := by
      have : (OrderMaintenance.Proof.Top.ts t).P = (OrderMaintenance.Proof.Top.ts s).P := by
        rw [hts]
      exact this.trans hsP
    have hNt : t.nodes = s.nodes := by
      have : (OrderMaintenance.Proof.Top.ts t).nodes = (OrderMaintenance.Proof.Top.ts s).nodes := by
        rw [hts]
      exact this
    have hmu : topMu t = topMu s := by unfold topMu; rw [hjob, hts]
    have hcbs : s.C.size ≤ cb s.P := cb_of hC.low (by
      rw [hsP]
      omega)
    refine ⟨hPt, ?_, by rw [hCs, ← hsP]; exact hcbs, hq, by rw [hprt]; exact hpr, ?_, by
      rw [hct]
      omega,
      by rw [hct]; omega⟩
    · unfold NodeB at hNB ⊢; rw [hNt, hmu, hCs, hPt, ← hsP]; exact hNB
    · intro c hc j
      have : (OrderMaintenance.Proof.Top.ts t).path = (OrderMaintenance.Proof.Top.ts s).path := by
        rw [hts]
      have hpa : t.path = s.path := this
      rw [hpa]; exact hPZ c (by
        rw [← hCs]
        exact hc) j
  · -- a split start
    obtain ⟨hL', hT', hc', hP', y', i', a', ip', js', hG', hR'⟩ := hI'
    obtain ⟨-, -, hc0, hP0, -⟩ := hI
    have hPt : t.P = P := hM.1
    have hP2 : t2.P = P := by rw [hP', ← hP0, hPt]
    have hc2 : t2.count ≤ P.N := by rw [hc', ← hc0]; exact hM.2.2.2.2.2.2.1
    refine mc_split hM hnone hp hs hP2 ?_ (by
      have bound := cb_of hL' (by rw [hP2]; exact hc2)
      rwa [hP2] at bound) hc2
      (by rw [hc', hc0])
    rcases hj : t2.resJob with _ | j'
    · have : topMu t2 = 0 := by unfold topMu; rw [hj]
      omega
    · unfold RoundAt at hR'; rw [hj] at hR'
      have := hR'.2.1; omega

/-! ### Deletion and order -/

/-- **A deletion agrees** and keeps the capacity predicate. -/
theorem markDeadAgreeM {P : Params} {n R : Nat} {L : List Nat} {s : Core} {x : Nat}
    (hC : CostInv (TIat TopInv P) topMu (topJ P) n R L s) (hsP : s.P = P) (hx : x ∈ L)
    {κ : Caps} (Lx : Loc) (hLx : Lx "x" = x) (K : CapsOK κ P) (hcntL : s.count = L.length) (hM :
      Mc κ P s) :
    ∃ s', (markDead x).run s = .ok () s' ∧
      (∃ L' m, evalF κ markDeadP.body s Lx = .ok s' L' m ∧ m ≤ 5) ∧
      CostInv (TIat TopInv P) topMu (topJ P) n R L s' ∧ s'.count = s.count ∧ s'.P = s.P ∧ Mc κ P
        s' := by
  have hTC : TopContract (TIat TopInv P) topMu (topJ P) capT := topContract'.at P
  obtain ⟨s', hr, hC'⟩ := markDead_cost hTC hC x
  have he : s' = {
    s with
    E := s.E.modify x fun e => {
      e with
      live := false
    }
  } := by
    rw [markDead_run] at hr; cases hr; rfl
  subst he
  obtain ⟨A, hI, hel⟩ := hC.low.inv
  have hxs := hI.size_pos (hel ▸ hx)
  have hE := E_size_le hI
  rw [hel, ← hcntL] at hE
  have := hM.2.2.2.2.2.2.1; have := K.E
  refine ⟨_, hr, markDead_agree κ s Lx hLx hxs.2 (by
    rw [← hsP] at *
    omega) hr, hC', rfl, rfl, ?_⟩
  obtain ⟨a, b, c, d, e, f, g, h⟩ := hM
  exact ⟨a, b, c, d.of_same ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, e, f, g, h⟩

/-- **An order query agrees**; it changes nothing. -/
theorem orderAgreeM {P : Params} {n R : Nat} {L : List Nat} {s : Core} {x y : Nat}
    (hC : CostInv (TIat TopInv P) topMu (topJ P) n R L s) (hx : x ∈ L) (hy : y ∈ L)
    {κ : Caps} (Lxy : Loc) (hLx : Lxy "x" = x) (hLy : Lxy "y" = y) (K : CapsOK κ P) (hcntL :
      s.count = L.length)
    (hM : Mc κ P s) {b : Bool} {s' : Core} (h : (OrderMaintenance.Model.order x y).run s = .ok b
      s') :
    ∃ L' m, evalF κ orderP.body s Lxy = .ok s' L' m ∧ L' "r" = b2n b ∧ m ≤ 80 := by
  obtain ⟨A, hI, hel⟩ := hC.low.inv
  obtain ⟨s₀, hCI, -⟩ := hC.low.cinv
  subst hel
  have hE := E_size_le hI
  rw [← hcntL] at hE
  obtain ⟨hP, -, hcb, -, -, -, hcnt, hgs⟩ := hM
  have := K.E; have := K.G; have := K.C
  have hxs := (hI.size_pos hx).2
  have hys := (hI.size_pos hy).2
  have hgx := hI.mem_glist_iff.mp (hI.eG_mem hx)
  have hgy := hI.mem_glist_iff.mp (hI.eG_mem hy)
  have hcx := (hCI.gchk _ hgx).1.2
  have hcy := (hCI.gchk _ hgy).1.2
  have hgx' : (s.E.getX x).grp < s.Gs.size := hgx.2.1
  have hgy' : (s.E.getX y).grp < s.Gs.size := hgy.2.1
  have hcx' : (s.Gs.getX (s.E.getX x).grp).chk < s.C.size := hcx
  have hcy' : (s.Gs.getX (s.E.getX y).grp).chk < s.C.size := hcy
  exact order_agree κ s Lxy hLx hLy (by omega) (by omega) (by omega) (by omega) (by omega) (by
    omega) h

/-! ### A fresh core -/

/-- The path rows from 2 on are empty (a core under construction). -/
def PZ1 (s : Core) : Prop := ∀ c, 2 ≤ c → s.path.getX c = #[]

theorem pz1_initState (P : Params) (r : Bool) : PZ1 (prepStart P r) := fun c _ => by
  change (#[] : Array (Array Nat)).getX c = #[]; rfl

/-- **A construction step keeps the empty rows.** -/
theorem prep_pz1 {P : Params} {h : Nat} {s s' : Core} {b : Bool} (S : Stage P h s) (hH1 : 1 ≤ P.H)
    (hz : PZ1 s) (hr : initStep.run s = .ok b s') : PZ1 s' := by
  obtain ⟨pa, hp, -, -⟩ := S.pr
  have hP := S.P
  by_cases e1 : h = 1
  · subst e1
    rw [initStep_first s _ hp rfl (by
      rw [hP]
      exact hH1)] at hr
    obtain ⟨-, e⟩ := EStateM.Result.ok.inj hr; subst e
    intro c _; rfl
  · by_cases eH : h ≤ P.H
    · rw [initStep_mid s _ hp e1 (by
      rw [hP]
      exact eH)] at hr
      obtain ⟨-, e⟩ := EStateM.Result.ok.inj hr; subst e
      exact hz
    · rw [initStep_last s _ hp e1 (by
      rw [hP]
      change P.H < h
      omega)] at hr
      obtain ⟨-, e⟩ := EStateM.Result.ok.inj hr; subst e
      intro c hc
      change (s.path.setX 1 pa).getX c = _
      rw [OrderMaintenance.Proof.Top.getX_setX', ite_eq_right (by omega)]; exact hz c hc

/-- **A ready fresh core satisfies the capacity predicate.** -/
theorem mc_final {κ : Caps} {P : Params} (K : CapsOK κ P) (hN : 1 ≤ P.N) {s : Core} (F : Final P
  s) (hz : PZ1 s) :
    Mc κ P s := by
  have hP : s.P = P := F.low.rest.1
  have hC : s.C.size = 2 := by rw [F.low.Csize]; rfl
  have hG : s.Gs.size = 2 := by rw [F.low.Gs]; rfl
  have hcnt : s.count = 1 := by rw [F.low.rest.2.1]; rfl
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8⟩ := F.low.pq
  have q1 : s.pqHead = #[] := q1
  have q2 : s.pqNext = #[] := q2
  have q3 : s.pqPrev = #[] := q3
  have q4 : s.pqWhere = #[] := q4
  have q5 : s.nbNext = #[] := q5
  have q6 : s.nbPrev = #[] := q6
  have q7 : s.pqHi = 0 := q7
  have q8 : s.pqLo = 0 := q8
  have hcb : 2 ≤ cb P := by unfold cb; omega
  have hCc := K.cC; have hBc := K.cB
  have hmu : topMu s = 0 := by unfold topMu; rw [F.res]
  refine ⟨hP, ?_, by rw [hC]; exact hcb, ⟨K.pqC, K.pqB, fun i => ?_, fun i => ?_, fun i => ?_,
    fun i => ?_,
    fun i => ?_, fun i => ?_, ?_, ?_⟩, F.prep, fun c hc j => ?_, by rw [hcnt]; exact hN, by
      rw [hG, hcnt]
      omega⟩
  · unfold NodeB; rw [F.nsz, hmu, hC, hP]; unfold nb0; omega
  · rw [q2]; show (#[] : Array Nat).getX i < _; change 0 < _; omega
  · rw [q3]; show (#[] : Array Nat).getX i < _; change 0 < _; omega
  · rw [q1]; show (#[] : Array Nat).getX i < _; change 0 < _; omega
  · rw [q4]; show (#[] : Array Nat).getX i < _; change 0 < _; omega
  · rw [q5]; show (#[] : Array Nat).getX i < _; change 0 < _; omega
  · rw [q6]; show (#[] : Array Nat).getX i < _; change 0 < _; omega
  · rw [q8]; show 0 < _; omega
  · rw [q7]; show 0 < _; omega
  · rw [hC] at hc; rw [hz c hc]; rfl

/-! ### The capacities of a core -/

/-- **The capacities of a core with parameters `P`**: every bound above, exactly. The list
capacities are constants (they fix the strides of the compiled code), except the free-group
stack's, which has stride 0. -/
def capsOf (P : Params) : Caps where
  tbl
    | .E => P.N + 2
    | .G => 2 * P.N + 4
    | .C => cb P + 2
    | .N => nbMax P + cb P + 2
  arr
    | .pqHead => P.N + 3
    | .pqNext => cb P + 2
    | .pqPrev => cb P + 2
    | .pqWhere => cb P + 2
    | .nbNext => P.N + 3
    | .nbPrev => P.N + 3
    | .lpar => nbMax P + cb P + 2
  lrec
    | .children => nbMax P + 2
    | .table => nbMax P + 2
    | .inTab => nbMax P + 2
    | .side => nbMax P + 2
    | .cin => nbMax P + cb P + 2
    | .freeG => 1
  lcap
    | .children => 162
    | .table => 162
    | .inTab => 322
    | .side => 322
    | .cin => 322
    | .freeG => 2 * P.N + 4
  pw := P.H + 1

theorem capsOf_ok (P : Params) : CapsOK (capsOf P) P where
  N := by simp [capsOf]
  NC := by simp [capsOf]; omega
  C := le_rfl
  rc := le_rfl
  rs := le_rfl
  rt := le_rfl
  ri := le_rfl
  rcin := le_rfl
  alp := le_rfl
  lt := le_rfl
  ls := le_rfl
  li := le_rfl
  lcin := le_rfl
  lc := le_rfl
  pw := rfl
  E := le_rfl
  G := le_rfl
  fl := le_rfl
  f0 := by simp [capsOf]
  cC := by simp [capsOf, Ccap]
  cB := by simp [capsOf, Bcap]
  pqC := ⟨rfl, rfl⟩
  pqB := ⟨rfl, rfl⟩

theorem capsOf_init (P : Params) : InitCaps (capsOf P) P where
  pw := rfl
  N := by simp [capsOf, nbMax, nb0]; omega
  C := by simp [capsOf]
  rc := by simp [capsOf, nbMax, nb0]; omega
  rt := by simp [capsOf, nbMax, nb0]; omega
  ri := by simp [capsOf, nbMax, nb0]; omega
  rcin := by simp [capsOf]
  alp := by simp [capsOf]
  cc := by simp [capsOf]
  ct := by simp [capsOf]
  ci := by simp [capsOf]
  ccin := by simp [capsOf]

/-- The list capacities do not depend on the parameters, so neither does the compiled code. -/
theorem capsOf_lcap (P P' : Params) (k : LK) : LK.stride (capsOf P).lcap k = LK.stride (capsOf
  P').lcap k := by
  cases k <;> rfl

theorem Exp.compile_congr {p : Nat} {κ κ' : Caps} (h : ∀ k : LK, k.stride κ.lcap = k.stride
  κ'.lcap) :
    ∀ e : Exp, e.compile p κ = e.compile p κ' := by
  intro e
  induction e with
  | bin op a b iha ihb => simp [Exp.compile, iha, ihb]
  | un op a ih => simp [Exp.compile, ih]
  | rd f i ih => simp [Exp.compile, ih]
  | lrd k b i j ihi ihj => simp [Exp.compile, ihi, ihj, h k]
  | llen k i ih => simp [Exp.compile, ih]
  | prd c j ihc ihj => simp [Exp.compile, ihc, ihj]
  | _ => rfl

/-- **The compiled code does not depend on the capacities**, beyond the list strides. -/
theorem Stm.compile_congr {p : Nat} {κ κ' : Caps} (h : ∀ k : LK, k.stride κ.lcap = k.stride
  κ'.lcap) :
    ∀ c : Stm, c.compile p κ = c.compile p κ' := by
  have he := Exp.compile_congr (p := p) h
  intro c
  induction c with
  | seq c d ihc ihd => simp [Stm.compile, ihc, ihd]
  | ite e t f iht ihf => simp [Stm.compile, he, iht, ihf]
  | loop x n b ih => simp [Stm.compile, he, ih]
  | call nm ps b rs args ds ih => simp [Stm.compile, ih, he]
  | «catch» c d ihc ihd => simp [Stm.compile, ihc, ihd]
  | _ => simp [Stm.compile, he, h]

/-! ### A preparation step -/

/-- **A core under construction**, as Level M needs it: Level F's stage invariant, empty path
rows from 2 on, and empty top arrays at the first stage. -/
def PrepM (s : Core) : Prop :=
  topPI s ∧ PZ1 s ∧ (∀ h, Stage s.P h s → h = 1 → s.nodes = #[default] ∧ s.path = #[] ∧ s.cin =
    #[] ∧ s.lpar = #[])

theorem prepM_start (P : Params) (hPP : topPP P) : PrepM (prepStart P false) := by
  refine ⟨⟨hPP, rfl, 1, le_rfl, by omega, stage_one (initState P) false⟩, pz1_initState P false,
    fun h _ _ => ?_⟩
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- **A preparation step agrees**, and keeps the construction's invariant or makes the core
ready with the capacity predicate. -/
theorem prepAgreeM {s : Core} (hM : PrepM s) (hN : 1 ≤ s.P.N) {b : Bool} {s' : Core}
    (hr : prepareStep.run s = .ok b s') (L : Loc) :
    (∃ L' c, evalF (capsOf s.P) prepP.body s L = .ok s' L' c ∧ L' "r" = b2n b ∧ c ≤ 440) ∧
      s'.P = s.P ∧ (b = false → PrepM s') ∧ (b = true → Mc (capsOf s.P) s.P s' ∧ TopInv s' ∧
        s'.resJob = none) := by
  obtain ⟨⟨hPP, hrd, h, h1, hH, S⟩, hz, hfirst⟩ := hM
  have hb := hPP.beta
  have hH1 : 1 ≤ s.P.H := by have := hPP.2; omega
  have hA : ISAgree (capsOf s.P) s 400 :=
    isAgree_stage S h1 hH hb hH1 (capsOf_init s.P) (fun e => hfirst h S e)
  by_cases hh : h ≤ s.P.H
  · obtain ⟨s1, hr1, S', hrd'⟩ := stage_next S h1 hh hb
    have hrun : prepareStep.run s = .ok false s1 := by
      unfold prepareStep
      simp only [hrd, Bool.not_eq_eq_eq_not, Bool.not_true, bind_pure_comp, EStateM.run_bind,
        EStateM.run_get, run_ite, EStateM.run_modify]
      rw [hr1]
      change EStateM.Result.ok s1.ready s1 = EStateM.Result.ok false s1
      rw [hrd', hrd]
    have hrdA : ∀ b' s2, initStep.run s = .ok b' s2 → s2.ready = s.ready := fun b' s2 h2 => by
      rw [hr1] at h2; obtain ⟨-, rfl⟩ := EStateM.Result.ok.inj h2; exact hrd'
    have hag := prepP_agree (L := L) (fun _ => hA) hrdA hrun
    rw [hrun] at hr; obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj hr
    have hP' : s1.P = s.P := S'.P.trans S.P.symm
    refine ⟨hag, hP', fun _ => ?_, fun e => absurd e (by simp)⟩
    refine ⟨⟨by rw [hP']; exact hPP, by rw [hrd', hrd], h + 1, by omega, by rw [hP']; omega, by
      rw [hP']; exact S'⟩,
      prep_pz1 S hH1 hz hr1, fun h' S2 e => ?_⟩
    obtain ⟨pa, hp, -, -⟩ := S'.pr
    obtain ⟨pa', hp', -, -⟩ := S2.pr
    rw [hp] at hp'
    have := congrArg (fun o => (o.map (·.h)).getD 0) hp'
    simp at this; omega
  · have e : h = s.P.H + 1 := by omega
    subst e
    obtain ⟨s1, hr1, F, hrd'⟩ := stage_last S hH1
    have hrun : prepareStep.run s = .ok true {
      s1 with
      ready := true
    } := by
      unfold prepareStep
      simp only [hrd, Bool.not_eq_eq_eq_not, Bool.not_true, bind_pure_comp, EStateM.run_bind,
        EStateM.run_get, run_ite, EStateM.run_modify]
      rw [hr1]
      rfl
    have hrdA : ∀ b' s2, initStep.run s = .ok b' s2 → s2.ready = s.ready := fun b' s2 h2 => by
      rw [hr1] at h2; obtain ⟨-, rfl⟩ := EStateM.Result.ok.inj h2; exact hrd'
    have hag := prepP_agree (L := L) (fun _ => hA) hrdA hrun
    rw [hrun] at hr; obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj hr
    have hP1 : s1.P = s.P := F.low.rest.1
    refine ⟨hag, hP1, fun e => absurd e (by simp), fun _ => ?_⟩
    have hz1 := prep_pz1 S hH1 hz hr1
    have hM := mc_final (capsOf_ok s.P) hN F hz1
    have F' := F.ready true
    refine ⟨?_, F'.topInv hPP.1 hPP.2, F'.res⟩
    obtain ⟨a, b, c, d, e, f, g, i⟩ := hM
    exact ⟨a, b, c, d.of_same ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, e, f, g, i⟩

end OrderMaintenance.Impl
