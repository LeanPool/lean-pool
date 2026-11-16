/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Top.PresWalk


/-!
# M5: a step of the running job

Every resumption of the job (`jobStep`) succeeds and keeps the invariant, and the job measure
decreases (`top_step`). The cases: a copy step; a walk step (with or without a drain start); the
step after a drain start; a step of the funding loop.
-/


@[expose] public section

namespace OrderMaintenance.Proof.Top

open OrderMaintenance.Model OrderMaintenance.Proof
/-! ### The chunk list across top-structure steps -/

/-- The chunk list facts of `TopInv`. -/
def CLok (s : Core) (cl : List Nat) : Prop :=
  LList (cN s) (cP s) s.firstChunk cl ∧ ∀ c, c ∈ cl ↔ 1 ≤ c ∧ c < s.C.size

theorem CLok.topRel {s s' : Core} {cl : List Nat} (h : CLok s cl) (hr : TopRel s s') : CLok s'
  cl := by
  obtain ⟨hL, hC⟩ := h
  have e1 : cN s' = cN s := funext fun c => by
    change (s'.C.getX c).next = (s.C.getX c).next; rw [hr.C c]
  have e2 : cP s' = cP s := funext fun c => by
    change (s'.C.getX c).prev = (s.C.getX c).prev; rw [hr.C c]
  refine ⟨by rw [e1, e2, hr.rest.2.2.2.2.2.1]; exact hL, fun c => by rw [hr.Csize]; exact hC c⟩

/-! ### The job measure -/

theorem walkLeft_lt (P : Params) {h : Nat} (hh : h ≤ P.H) : walkLeft P (h + 1) + P.s < walkLeft
  P h := by
  unfold walkLeft
  have : P.H + 1 - h = (P.H + 1 - (h + 1)) + 1 := by omega
  rw [this, Nat.add_mul, one_mul]; omega

/-! ### The funding loop -/

/-- The funding loop moves a chunk, ends the drain, or finishes its remaining work. -/
theorem fund_run {s : Core} {cl : List Nat} {ord : Nat → List Nat} {dr n0 : Nat → Nat}
    {j : Job} {v up src k : Nat} (hTP : TopParams s.P) (hcl : CLok s cl)
    (hI : InvJ (ts s) cl ord dr n0 (some { j with pc := .fund v up src k })) :
    ∃ j' s' ord', (fundLoop j v up src k).run s = .ok (some j') s' ∧ TopRel s s' ∧
      InvJ (ts s') cl ord' dr n0 (some j') ∧
      jobLeft (ts s') j' < jobLeft (ts s) { j with pc := .fund v up src k } ∧
      ∀ l, j'.pc ≠ .copy l := by
  have S := hI.shape
  obtain ⟨hpos, hat⟩ := hI.job _ rfl
  simp only [JobAt] at hat
  obtain ⟨hvl, hva, hua, hg, hsv, hks⟩ := hat
  obtain ⟨hv1, hvH⟩ := S.htN v hvl.1
  have hsrc := S.src v hvl (by rw [hsv]; exact hg.1.1)
  rw [hsv] at hsrc
  obtain ⟨-, -, hh1, hh2, -, -, -, -, -, hlt, -⟩ := S.ghost src hg
  have hvh : ht (ts s) v = ht (ts s) src := by rcases hsrc.2 with e | e <;> rw [e] <;> assumption
  -- the walk goes on from the live parent of the target
  obtain ⟨hupl, huph, -⟩ := S.up v hvl (by omega)
  have hup : up = (nd (ts s) v).livePar := by
    rw [hua, anc_succ j.y _ hv1, ← hva]
  rw [← hup] at hupl huph
  unfold fundLoop
  simp only [run_getP_bind]
  by_cases hk : k < s.P.s
  · rw [ite_eq_left hk, run_bind]
    by_cases hne : rng (ts s) cl src = []
    · obtain ⟨hrun, hrel, hinv⟩ := inv_drainFinish hI hTP hne
      rw [hrun]
      simp only [Bool.false_eq_true, ite_false, run_pure]
      refine ⟨_, _, _, rfl, hrel, hinv, ?_, fun l h => by cases h⟩
      have F := S.fin_frame hg
      simp only [jobLeft]
      rw [ite_eq_right (fun e => by rw [e] at hupl; exact hupl.1.1 rfl), F.ht, F.P, huph]
      have := walkLeft_lt s.P (h := ht (ts s) v) (S.htN v hvl.1).2
      have e : (ts s).P = s.P := rfl
      rw [e]; omega
    · obtain ⟨s', hrun, hrel, hinv, hht⟩ := inv_drainMove hI hcl.1
        (fun c hc => ((hcl.2 c).mp hc).2) hk hne
      rw [hrun]
      simp only [ite_true, run_pure]
      refine ⟨_, _, _, rfl, hrel, hinv, ?_, fun l h => by cases h⟩
      simp only [jobLeft]
      rw [hht, show (ts s').P = s.P from hrel.rest.1]
      have e : (ts s).P = s.P := rfl
      rw [e]; omega
  · rw [ite_eq_right hk]
    simp only [run_pure]
    refine ⟨_, _, ord, rfl, TopRel.refl s, ?_, ?_, fun l h => by cases h⟩
    · -- the loop is done: the sweeps owed are 0
      have hks' : k = s.P.s := by have : k ≤ (ts s).P.s := hks; exact le_antisymm this (by omega)
      have hc : curH (ts s) { j with pc := .walk (some up) } = ht (ts s) v + 1 := by
        simp only [curH]; rw [ite_eq_right (fun e => by rw [e] at hupl; exact hupl.1.1 rfl), huph]
      have hp : pend (ts s) (some { j with pc := .walk (some up) }) =
          pend (ts s) (some { j with pc := .fund v up src k }) := rfl
      have hs : ∀ u, slack (ts s) (some { j with pc := .walk (some up) }) u =
          slack (ts s) (some { j with pc := .fund v up src k }) u := by
        intro u
        simp only [slack]
        rw [hc]
        have hc' : curH (ts s) { j with pc := .fund v up src k } = ht (ts s) v + 1 := rfl
        rw [hc']
        have h0 : (ts s).P.s - k = 0 := by rw [hks']; exact Nat.sub_self _
        split_ifs <;> first | rfl | simp only [h0]
      refine ⟨S, hI.time.congr_job hp hs (fun _ => Iff.rfl), hI.room, fun j' hj' => ?_, hI.cap,
        hI.len⟩
      cases hj'
      refine ⟨hpos, ?_⟩
      simp only [JobAt]
      right
      exact ⟨hupl, by rw [huph, hua]⟩
    · simp only [jobLeft]
      rw [ite_eq_right (fun e => by rw [e] at hupl; exact hupl.1.1 rfl), huph]
      have e : (ts s).P = s.P := rfl
      rw [e]; omega

/-! ### The end of a job -/

/-- **The job ends**: the walk has passed the root. -/
theorem inv_end {t : TS} {cl : List Nat} {ord : Nat → List Nat} {dr n0 : Nat → Nat} {j : Job}
    (hpc : j.pc = .walk (some NIL)) (hI : InvJ t cl ord dr n0 (some j)) :
    InvJ t cl ord dr n0 none := by
  have S := hI.shape
  have Ti := hI.time
  have hp : pend t (some j) = [] := by simp only [pend, wStart, hpc]; exact upChain_nil t _
  have hs : ∀ u, ghostN t u → slack t (some j) u = 0 := by
    intro u hu
    have := (S.htN u hu.1).2
    simp only [slack, curH, hpc, ite_true]
    split_ifs <;> first | rfl | omega
  refine ⟨S, ⟨fun u hu => ?_, Ti.wA, Ti.wB, Ti.wF, fun u hu => ?_, fun u hu => ?_, Ti.wD,
    Ti.big, Ti.chain, Ti.tw1⟩,
    hI.room, fun _ h => absurd h (by simp), hI.cap, hI.len⟩
  · have := Ti.wts u hu; rw [hp] at this; simpa [pend] using this
  · have := Ti.wC u hu; rw [hs u hu] at this; simpa [slack] using this
  · have := Ti.wC u hu; rw [hs u hu] at this
    simp only [funded, ite_false, Nat.sub_zero]
    have h2 : (t.P.s - 2) * fundOf t cl u ≤ (rng t cl u).length + (t.P.s - 2) * fundOf t cl u :=
      Nat.le_add_left _ _
    omega

/-! ### The walk -/

/-- What `startDrain` must do: the statement M5 proves in `PresStart.lean`. -/
def SDOK : Prop :=
  ∀ (s : Core) (cl : List Nat) (ord : Nat → List Nat) (dr n0 : Nat → Nat) (j : Job) (v : Nat),
    j.pc = .walk (some v) → v ≠ NIL → TopParams s.P → CLok s cl →
    InvJ (ts s) cl ord dr n0 (some j) →
    (nd (ts s) v).livePar ≠ NIL → (nd (ts s) v).draining = false → (nd (ts s) v).overflowOf = NIL →
    Wd s.P (ht (ts s) v) < (nd (ts s) v).weight + 2 →
    ∃ s' ord' dr' n0', (startDrain v).run (wiC s v) = .ok () s' ∧ TopRel (wiC s v) s' ∧
      InvJ (ts s') cl ord' dr' n0' (some { j with pc := .afterDrain v (nd (ts s) v).livePar }) ∧
      ht (ts s') v = ht (ts s) v

theorem run_walkBody_nil (j : Job) (s : Core) : (walkBody j NIL).run s = .ok none s := by
  unfold walkBody; simp

/-- The walk at `v ≠ NIL`, when `v` starts no drain. -/
theorem run_walkBody_noDrain (j : Job) (s : Core) (v : Nat) (hv : v ≠ NIL)
    (hno : ¬ ((nd (ts s) v).livePar ≠ NIL ∧ (nd (ts s) v).draining = false ∧
      (nd (ts s) v).overflowOf = NIL ∧ Wd s.P (ht (ts s) v) < (nd (ts s) v).weight + 2)) :
    (walkBody j v).run s = (afterDrain j v (nd (ts s) v).livePar).run (wiC s v) := by
  unfold walkBody
  simp only [beq_iff_eq, hv, ite_false, run_getP_bind, run_getN_bind, run_modN_bind]
  rw [ite_eq_right]
  · rfl
  · simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true', beq_iff_eq,
      decide_eq_true_eq]
    intro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    exact hno ⟨h1, h2, h3, by unfold Wd ht; exact h4⟩

/-- The walk at `v ≠ NIL`, when `v` starts a drain. -/
theorem run_walkBody_drain (j : Job) (s : Core) (v : Nat) (hv : v ≠ NIL)
    (h1 : (nd (ts s) v).livePar ≠ NIL) (h2 : (nd (ts s) v).draining = false)
    (h3 : (nd (ts s) v).overflowOf = NIL) (h4 : Wd s.P (ht (ts s) v) < (nd (ts s) v).weight + 2)
    {s' : Core} (hsd : (startDrain v).run (wiC s v) = .ok () s') :
    (walkBody j v).run s = .ok (some { j with pc := .afterDrain v (nd (ts s) v).livePar }) s' := by
  unfold walkBody
  simp only [beq_iff_eq, hv, ite_false, run_getP_bind, run_getN_bind, run_modN_bind]
  rw [ite_eq_left]
  · rw [run_bind]
    have hsd' : (startDrain v).run
        { s with nodes := s.nodes.modify v fun n => { n with weight := n.weight + 2 } } = .ok ()
          s' := hsd
    rw [hsd']; rfl
  · simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true', beq_iff_eq,
      decide_eq_true_eq]
    exact ⟨⟨⟨h1, h2⟩, h3⟩, by unfold Wd ht at h4; exact h4⟩

theorem run_afterDrain (j : Job) (v up : Nat) (t : Core) :
    (afterDrain j v up).run t =
      if (t.nodes.getX v).overflowOf = NIL then .ok (some { j with pc := .walk (some up) }) t
      else (fundLoop j v up (t.nodes.getX v).overflowOf 0).run t := by
  unfold afterDrain
  simp only [run_getN_bind]
  by_cases h : (t.nodes.getX v).overflowOf = NIL
  · simp [h]
  · simp [h]

theorem wiC_topRel (s : Core) (v : Nat) : TopRel s (wiC s v) := TopRel.of_top s _ s.path s.cin
  s.lpar

/-- **A walk step.** -/
theorem walk_run (hSD : SDOK) {s : Core} {cl : List Nat} {ord : Nat → List Nat}
    {dr n0 : Nat → Nat} {j : Job} {v : Nat} (hpc : j.pc = .walk (some v)) (hTP : TopParams s.P)
    (hcl : CLok s cl) (hI : InvJ (ts s) cl ord dr n0 (some j)) :
    ∃ r s' ord' dr' n0', (walkBody j v).run s = .ok r s' ∧ TopRel s s' ∧
      InvJ (ts s') cl ord' dr' n0' r ∧
      (∀ j', r = some j' → jobLeft (ts s') j' < jobLeft (ts s) j ∧ ∀ l, j'.pc ≠ .copy l) := by
  have S := hI.shape
  by_cases hv0 : v = NIL
  · subst hv0
    exact ⟨none, s, ord, dr, n0, run_walkBody_nil j s, TopRel.refl s, inv_end hpc hI,
      fun _ h => absurd h (by simp)⟩
  obtain ⟨hpos, hat⟩ := hI.job j rfl
  simp only [JobAt, hpc] at hat
  obtain ⟨hvl, hva⟩ := hat.resolve_left hv0
  obtain ⟨hv1, hvH⟩ := S.htN v hvl.1
  have hjl : jobLeft (ts s) j = walkLeft s.P (ht (ts s) v) := by
    simp only [jobLeft, hpc, ite_eq_right hv0]; rfl
  have hlt := walkLeft_lt s.P (h := ht (ts s) v) hvH
  by_cases hd : (nd (ts s) v).livePar ≠ NIL ∧ (nd (ts s) v).draining = false ∧
      (nd (ts s) v).overflowOf = NIL ∧ Wd s.P (ht (ts s) v) < (nd (ts s) v).weight + 2
  · obtain ⟨h1, h2, h3, h4⟩ := hd
    obtain ⟨s', ord', dr', n0', hrun, hrel, hinv, hht⟩ := hSD s cl ord dr n0 j v hpc hv0 hTP hcl
      hI h1 h2 h3 h4
    refine ⟨_, s', ord', dr', n0', run_walkBody_drain j s v hv0 h1 h2 h3 h4 hrun,
      (wiC_topRel s v).trans hrel, hinv, fun j' hj' => ?_⟩
    cases hj'
    refine ⟨?_, fun l h => by cases h⟩
    rw [hjl]
    simp only [jobLeft, hht, show (ts s').P = s.P from hrel.rest.1]
    have := hTP.s3
    omega
  · rw [run_walkBody_noDrain j s v hv0 hd, run_afterDrain]
    have hI' := inv_winc hpc hv0 hI hd
    have hcl' := hcl.topRel (wiC_topRel s v)
    have hTP' : TopParams (wiC s v).P := hTP
    have hW : ((wiC s v).nodes.getX v).overflowOf = srcOf (ts s) v := by
      change ((s.nodes.modify v _).getX v).overflowOf = _
      rw [Array.getX_modify]; split <;> rfl
    rw [hW]
    -- where the walk goes on
    have hupl : (nd (ts s) v).livePar = NIL ∨ (liveN (ts s) (nd (ts s) v).livePar ∧
        ht (ts s) (nd (ts s) v).livePar = ht (ts s) v + 1) := by
      by_cases hH : ht (ts s) v < (ts s).P.H
      · obtain ⟨h1, h2, -⟩ := S.up v hvl hH; exact Or.inr ⟨h1, h2⟩
      · left
        have hm := (S.ordMem (ts s).P.H (by have := S.H3; omega) le_rfl v).mpr ⟨hvl.1, by omega⟩
        rw [S.root.1] at hm
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        rw [hm]
        exact S.root.2.2
    by_cases hsv : srcOf (ts s) v = NIL
    · rw [ite_eq_left hsv]
      have hn : walkNext (ts s) j v = { j with pc := .walk (some (nd (ts s) v).livePar) } := by
        simp [walkNext, hsv]
      rw [hn] at hI'
      refine ⟨_, _, ord, dr, n0, rfl, wiC_topRel s v, hI', fun j' hj' => ?_⟩
      cases hj'
      refine ⟨?_, fun l h => by cases h⟩
      rw [hjl]
      simp only [jobLeft]
      have h1w : 1 ≤ walkLeft s.P (ht (ts s) v + 1) := by unfold walkLeft; omega
      rcases hupl with h | ⟨h1, h2⟩
      · rw [ite_eq_left h]; omega
      · rw [ite_eq_right (fun e => h1.1.1 e), (wiC_sameTree s v).ht, h2]
        have e : (ts (wiC s v)).P = s.P := rfl
        rw [e]; omega
    · rw [ite_eq_right hsv]
      have hn : walkNext (ts s) j v =
          { j with pc := .fund v (nd (ts s) v).livePar (srcOf (ts s) v) 0 } := by
        simp [walkNext, hsv]
      rw [hn] at hI'
      obtain ⟨j', s', ord', hrun, hrel, hinv, hlt', hnc⟩ := fund_run hTP' hcl' hI'
      refine ⟨_, s', ord', dr, n0, hrun, (wiC_topRel s v).trans hrel, hinv, fun j'' hj'' => ?_⟩
      cases hj''
      refine ⟨lt_of_lt_of_le hlt' ?_, hnc⟩
      rw [hjl]
      simp only [jobLeft]
      rw [show ht (ts (wiC s v)) v = ht (ts s) v from (wiC_sameTree s v).ht v]
      have e : (ts (wiC s v)).P = s.P := rfl
      rw [e]; omega

/-! ### The step after a drain start -/

theorem afterDrain_step {s : Core} {cl : List Nat} {ord : Nat → List Nat} {dr n0 : Nat → Nat}
    {j : Job} {v up : Nat} (hpc : j.pc = .afterDrain v up) (hI : InvJ (ts s) cl ord dr n0 (some
      j)) :
    (jobStep j).run s = .ok (some { j with pc := .walk (some up) }) s ∧
      InvJ (ts s) cl ord dr n0 (some { j with pc := .walk (some up) }) ∧
      jobLeft (ts s) { j with pc := .walk (some up) } < jobLeft (ts s) j := by
  have S := hI.shape
  obtain ⟨hpos, hat⟩ := hI.job j rfl
  simp only [JobAt, hpc] at hat
  obtain ⟨hg, hgt, hua⟩ := hat
  obtain ⟨-, -, -, -, -, -, -, -, hgs, hlt, -⟩ := S.ghost v hg
  have hy : j.y ∈ cl := by obtain ⟨A, B, e⟩ := hpos; rw [e]; simp
  obtain ⟨hupl, huph⟩ := S.anc_live hy (ht (ts s) v + 1) (by omega) (by omega)
  rw [← hua] at hupl huph
  refine ⟨?_, ?_, ?_⟩
  · unfold jobStep; rw [hpc]; simp only [run_getP_bind]
    rw [run_afterDrain, ite_eq_left (show (s.nodes.getX v).overflowOf = NIL from hgs)]
  · have hc : curH (ts s) { j with pc := .walk (some up) } = ht (ts s) v + 1 := by
      simp only [curH]; rw [ite_eq_right (fun e => by rw [e] at hupl; exact hupl.1.1 rfl), huph]
    have hs : ∀ u, slack (ts s) (some { j with pc := .walk (some up) }) u = slack (ts s) (some
      j) u := by
      intro u
      simp only [slack]
      rw [hc]
      have hc' : curH (ts s) j = ht (ts s) v + 1 := by simp only [curH, hpc]
      rw [hc', hpc]
    have hp : pend (ts s) (some { j with pc := .walk (some up) }) = pend (ts s) (some j) := by
      simp only [pend, wStart, hpc]
    refine ⟨S, hI.time.congr_job hp hs (fun _ => Iff.rfl), hI.room, fun j' hj' => ?_, hI.cap,
      hI.len⟩
    cases hj'
    exact ⟨hpos, Or.inr ⟨hupl, by rw [huph, hua]⟩⟩
  · simp only [jobLeft, hpc]
    rw [ite_eq_right (fun e => by rw [e] at hupl; exact hupl.1.1 rfl), huph]
    omega

/-! ### The walk's start -/

theorem walkNone_inv {t : TS} {cl : List Nat} {ord : Nat → List Nat} {dr n0 : Nat → Nat} {j : Job}
    (hpc : j.pc = .walk none) (hI : InvJ t cl ord dr n0 (some j)) :
    InvJ t cl ord dr n0 (some { j with pc := .walk (some (lpr t j.y)) }) ∧ liveN t (lpr t j.y) ∧
      ht t (lpr t j.y) = 1 := by
  have S := hI.shape
  obtain ⟨hpos, hat⟩ := hI.job j rfl
  have hy : j.y ∈ cl := by obtain ⟨A, B, e⟩ := hpos; rw [e]; simp
  obtain ⟨hl, hh, -⟩ := S.lp j.y hy
  refine ⟨⟨S, hI.time.congr_job ?_ ?_ (fun _ => Iff.rfl), hI.room, fun j' hj' => ?_, hI.cap,
    hI.len⟩, hl, hh⟩
  · simp only [pend, wStart, hpc]
  · intro u
    simp only [slack, curH, hpc, ite_eq_right hl.1.1, hh]
  · cases hj'
    exact ⟨hpos, Or.inr ⟨hl, by rw [hh]; rfl⟩⟩

/-! ### A step of the running job -/

theorem jobLeft_pos (t : TS) (j : Job) : 1 ≤ jobLeft t j := by
  unfold jobLeft walkLeft; split <;> (try split) <;> (try omega)

theorem copyC_topRel (s : Core) (j : Job) (l : Nat) : TopRel s (copyC s j l) := by
  unfold copyC; dsimp only; split_ifs <;> exact TopRel.of_top s _ _ s.cin s.lpar

theorem finS_noncopy (t : TS) {j : Job} (h : ∀ l, j.pc ≠ .copy l) : finS t (some j) = t := by
  unfold finS
  cases hj : j.pc with
  | copy l => exact absurd hj (h l)
  | _ => simp only [hj]

theorem job_eta {j : Job} {p : JobPc} (h : j.pc = p) : j = { j with pc := p } := by
  cases j; simp only at h; subst h; rfl

/-- **A step of the running job** keeps the top invariant and decreases the job measure. -/
theorem top_step (hSD : SDOK) {s : Core} {job : Job} (hT : TopInv s) (hres : s.resJob = some job) :
    ∃ r s', (jobStep job).run s = .ok r s' ∧ TopInv { s' with resJob := r } ∧
      ∀ j', r = some j' → 1 ≤ topMu { s' with resJob := r } ∧ topMu { s' with resJob := r } <
        topMu s := by
  obtain ⟨hTP, cl, ord, dr, n0, hL, hC, hI⟩ := hT
  rw [hres] at hI
  have hcl : CLok s cl := ⟨hL, hC⟩
  have hmu : topMu s = jobLeft (ts s) job := by simp only [topMu, hres]
  rw [hmu]
  -- the result, packaged
  have pack : ∀ (r : Option Job) (s' : Core) ord' dr' n0', TopRel s s' →
      InvJ (finS (ts s') r) cl ord' dr' n0' r → TopInv { s' with resJob := r } := by
    intro r s' ord' dr' n0' hrel hinv
    obtain ⟨hL', hC'⟩ := hcl.topRel hrel
    exact ⟨by rw [show ({ s' with resJob := r } : Core).P = s.P from hrel.rest.1]; exact hTP,
      cl, ord', dr', n0', hL', hC', hinv⟩
  have hmu' : ∀ (s' : Core) (j' : Job), topMu { s' with resJob := some j' } = jobLeft (ts s') j' :=
    fun _ _ => rfl
  cases hpc : job.pc with
  | copy l =>
    have hfin : finS (ts s) (some job) = copyRest job s.P.H (ts s) l := by
      simp only [finS, hpc]; rfl
    refine ⟨_, _, jobStep_copy hpc, pack _ _ ord dr n0 (copyC_topRel s job l) (inv_copy hpc hI),
      fun j' hj' => ?_⟩
    cases hj'
    rw [hmu']
    refine ⟨jobLeft_pos _ _, ?_⟩
    obtain ⟨-, hat⟩ := hI.job job rfl
    simp only [JobAt, hpc] at hat
    have hlH : l ≤ s.P.H := by
      have := hat.2.1; rw [hfin, copyRest_P job _ _ _ _ rfl] at this; exact this
    have e1 : (ts (copyC s job l)).P = s.P := (copyC_topRel s job l).rest.1
    have e2 : (ts s).P = s.P := rfl
    by_cases h : l < s.P.H
    · simp only [jobLeft, copyNext, hpc, ite_eq_left h, e1, e2]; omega
    · simp only [jobLeft, copyNext, hpc, ite_eq_right h, e1, e2]; omega
  | walk ov =>
    have hfin : finS (ts s) (some job) = ts s := by simp only [finS, hpc]
    rw [hfin] at hI
    cases ov with
    | none =>
      obtain ⟨hI', hl, hh⟩ := walkNone_inv hpc hI
      obtain ⟨r, s', ord', dr', n0', hrun, hrel, hinv, hlt⟩ :=
        walk_run hSD (j := { job with pc := .walk (some (lpr (ts s) job.y)) }) rfl hTP hcl hI'
      refine ⟨r, s', ?_, pack r s' ord' dr' n0' hrel ?_, fun j' hj' => ?_⟩
      · unfold jobStep; rw [hpc]; simp only [run_getP_bind, run_getLpar_bind]; exact hrun
      · cases r with
        | none => exact hinv
        | some j' => rw [finS_noncopy _ (hlt j' rfl).2]; exact hinv
      · subst hj'
        rw [hmu']
        refine ⟨jobLeft_pos _ _, ?_⟩
        have := (hlt j' rfl).1
        have e : jobLeft (ts s) { job with pc := .walk (some (lpr (ts s) job.y)) } = jobLeft (ts
          s) job := by
          simp only [jobLeft, hpc, ite_eq_right hl.1.1, hh]
        rw [e] at this; exact this
    | some v =>
      obtain ⟨r, s', ord', dr', n0', hrun, hrel, hinv, hlt⟩ := walk_run hSD hpc hTP hcl hI
      refine ⟨r, s', ?_, pack r s' ord' dr' n0' hrel ?_, fun j' hj' => ?_⟩
      · unfold jobStep; rw [hpc]; simp only [run_getP_bind]; exact hrun
      · cases r with
        | none => exact hinv
        | some j' => rw [finS_noncopy _ (hlt j' rfl).2]; exact hinv
      · subst hj'
        rw [hmu']
        exact ⟨jobLeft_pos _ _, (hlt j' rfl).1⟩
  | afterDrain v up =>
    have hfin : finS (ts s) (some job) = ts s := by simp only [finS, hpc]
    rw [hfin] at hI
    obtain ⟨hrun, hinv, hlt⟩ := afterDrain_step hpc hI
    refine ⟨_, _, hrun, pack _ _ ord dr n0 (TopRel.refl s) ?_, fun j' hj' => ?_⟩
    · rw [finS_noncopy _ (fun l h => by cases h)]; exact hinv
    · cases hj'
      rw [hmu']
      exact ⟨jobLeft_pos _ _, hlt⟩
  | fund v up src k =>
    have hfin : finS (ts s) (some job) = ts s := by simp only [finS, hpc]
    rw [hfin] at hI
    have he := job_eta hpc
    rw [he] at hI
    obtain ⟨j', s', ord', hrun, hrel, hinv, hlt, hnc⟩ := fund_run hTP hcl hI
    refine ⟨some j', s', ?_, pack _ s' ord' dr n0 hrel ?_, fun j'' hj'' => ?_⟩
    · unfold jobStep; rw [hpc]; simp only [run_getP_bind]; exact hrun
    · rw [finS_noncopy _ hnc]; exact hinv
    · cases hj''
      rw [hmu']
      refine ⟨jobLeft_pos _ _, ?_⟩
      rw [← he] at hlt; exact hlt

end OrderMaintenance.Proof.Top
