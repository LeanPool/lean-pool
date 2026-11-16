/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Word.TopB


/-!
# Theorem W, stage B2: a step of the running job keeps the stored-value bound

The cases of `top_step` (`Top/Step.lean`), each with its final state as the cost proof computes
it: a copy step (`copyC`), a walk step (`wiC`, then a drain start `sdS`, or the funding loop), the
step after a drain start, and a step of the funding loop (a sweep `dsS`, the end of a drain `fdS`).

The values that need a reachable state:
* the weight `weight + 2` of the walk (Sz): the stored weight plus the pending 2 is the true weight
  (`Timing.wts`), at most the chunk count;
* the weights of a drain start's new nodes (Sz): sums of their children's stored weights, at most
  the true weights (`Timing.wts`), which add up to the drained node's (`Shape.tw_kids`);
* the two fresh nodes (F): the hypothesis `nodes.size + 2 ≤ 2^K`;
* the new tag of a sweep (Tag): the tag of a chunk in the state after the step, which the top
  invariant of that state bounds (`tag_lt_of_topInv`), as a hypothesis on the final state.
-/


@[expose] public section

namespace OrderMaintenance.Proof.Word

open OrderMaintenance.Model OrderMaintenance.Proof OrderMaintenance.Proof.Top
variable {K : Nat}

/-- Room for the top structure's values: labels (`β ≤ K`) and tags (`H·β ≤ K`). -/
structure TopRoom (K : Nat) (P : Params) : Prop where
  beta : P.beta ≤ K
  tag : P.H * P.beta ≤ K

theorem sum_map_le_sum_map {l : List Nat} {f g : Nat → Nat} (h : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h a (by simp)) (ih fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem sum_filter_le (l : List Nat) (f : Nat → Nat) (p : Nat → Bool) :
    ((l.filter p).map f).sum ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.filter_cons]
    split <;> simp only [List.map_cons, List.sum_cons] <;> omega

/-- The chunk list of a core has at most `C.size - 1` entries. -/
theorem CLok.len {s : Core} {cl : List Nat} (h : CLok s cl) (hnd : cl.Nodup) : cl.length + 1 ≤
  max 1 s.C.size := by
  have := (hnd.subperm (l₂ := List.range' 1 (s.C.size - 1))
    (fun e he => List.mem_range'_1.mpr (by
      have := (h.2 e).mp he
      omega))).length_le
  simp only [List.length_range'] at this
  omega

/-! ### The walk -/

section walk
variable {s : Core} {cl : List Nat} {ord : Nat → List Nat} {dr n0 : Nat → Nat} {j : Job} {v : Nat}
  (hpc : j.pc = .walk (some v)) (hv0 : v ≠ NIL) (hI : InvJ (ts s) cl ord dr n0 (some j))
include hpc hv0 hI

theorem walk_live : liveN (ts s) v := by
  obtain ⟨-, hat⟩ := hI.job j rfl
  simp only [JobAt, hpc] at hat
  exact (hat.resolve_left hv0).1

/-- **The walk's weight update** (Sz): the stored weight plus the pending 2 is the true weight. -/
theorem walk_weight : (s.nodes.getX v).weight + 2 ≤ cl.length := by
  have hvl := walk_live hpc hv0 hI
  have hw := hI.time.wts v hvl
  have hp : v ∈ pend (ts s) (some j) := by
    simp only [pend, wStart, hpc]
    unfold upChain; rw [ite_eq_right hv0]; simp
  rw [ite_eq_left hp] at hw
  have := tw_le (s := ts s) cl v
  change (nd (ts s) v).weight + 2 ≤ _
  omega

/-- **A drain start's new weights** (Sz): the children's stored weights are at most their true
weights, which add up to the drained node's. -/
theorem walk_sum (p : Nat → Bool) :
    ((((wiC s v).nodes.getX v).children.filter p).map
      (drainWt (wiC s v).nodes ((wiC s v).nodes.getX v).height)).sum ≤ cl.length := by
  have S := hI.shape
  have hvl := walk_live hpc hv0 hI
  have hvs : v < s.nodes.size := hvl.1.2.1
  have eV : (wiC s v).nodes.getX v = {
    s.nodes.getX v with
    weight := (s.nodes.getX v).weight + 2
  } := by
    change (s.nodes.modify v _).getX v = _
    rw [Array.getX_modify, ite_eq_left ⟨rfl, hvs⟩]
  rw [eV]
  dsimp only
  refine le_trans (sum_filter_le _ _ p) ?_
  have hht : (s.nodes.getX v).height = ht (ts s) v := rfl
  have hch : (s.nodes.getX v).children = (nd (ts s) v).children := rfl
  rw [hht, hch]
  obtain ⟨hh1, -⟩ := S.htN v hvl.1
  by_cases h1 : ht (ts s) v = 1
  · have e : ∀ e ∈ (nd (ts s) v).children, drainWt (wiC s v).nodes (ht (ts s) v) e = 1 := by
      intro e _; simp [drainWt, h1]
    rw [List.map_congr_left e]
    simp only [List.map_const', List.sum_replicate, smul_eq_mul, mul_one]
    rw [← S.tw_one hvl h1]
    exact tw_le cl v
  · have h2 : 2 ≤ ht (ts s) v := by omega
    have e : ∀ e ∈ (nd (ts s) v).children, drainWt (wiC s v).nodes (ht (ts s) v) e ≤ tw (ts s)
      cl e := by
      intro e he
      have hm := ((S.mem_children hvl).mp he).1
      rw [ite_eq_right h1] at hm
      obtain ⟨hel, heh⟩ := hm
      have hne : e ≠ v := fun h => by subst h; omega
      have hw := hI.time.wts e hel
      have : drainWt (wiC s v).nodes (ht (ts s) v) e = (nd (ts s) e).weight := by
        simp only [drainWt, show (ht (ts s) v == 1) = false by simp [h1], Bool.false_eq_true,
          ite_false]
        have := wiC_weight s v e hvs
        rw [ite_eq_right hne] at this; exact this
      rw [this]; omega
    refine le_trans (sum_map_le_sum_map e) ?_
    rw [← S.tw_kids hvl h2]
    exact tw_le cl v

end walk

/-! ### The funding loop -/

theorem jobB_with {j : Job} (hj : JobB K j) {pc : JobPc} (hpc : JobPcB K pc) : JobB K {
  j with
  pc := pc
} :=
  ⟨hj.1, hj.2.1, hj.2.2.1, hpc⟩

/-- **A step of the funding loop**: a sweep (`dsS`, its tag bounded by the final state's
hypothesis), the end of a drain (`fdS`), or the end of the loop. -/
theorem fund_wb {t : Core} {cl : List Nat} {ord : Nat → List Nat} {dr n0 : Nat → Nat} {j : Job}
    {v up src k : Nat} (hTP : TopParams t.P) (hcl : CLok t cl)
    (hI : InvJ (ts t) cl ord dr n0 (some {
      j with
      pc := .fund v up src k
    }))
    (hW : WB K t) (hj : JobB K j) (hpc : JobPcB K (.fund v up src k)) {r : Option Job} {t' : Core}
    (hr : (fundLoop j v up src k).run t = .ok r t')
    (htag : ∀ c, 1 ≤ c → c < t'.C.size → (t'.C.getX c).tag < 2 ^ K) :
    WB K t' ∧ ∀ j', r = some j' → JobB K j' := by
  obtain ⟨hv, hup, hsrc, hk⟩ := hpc
  have S := hI.shape
  obtain ⟨-, hat⟩ := hI.job _ rfl
  simp only [JobAt] at hat
  obtain ⟨-, -, -, hg, -, -⟩ := hat
  have hwalk : JobB K {
    j with
    pc := .walk (some up)
  } := jobB_with hj hup
  unfold fundLoop at hr
  simp only [run_getP_bind] at hr
  by_cases hks : k < t.P.s
  · rw [ite_eq_left hks, run_bind] at hr
    by_cases hne : rng (ts t) cl src = []
    · obtain ⟨hrun, -, -⟩ := inv_drainFinish hI hTP hne
      rw [hrun] at hr
      simp only [Bool.false_eq_true, ite_false, run_pure] at hr
      obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj hr
      exact ⟨wb_fdS hW src, fun j' e => by cases e; exact hwalk⟩
    · obtain ⟨hrun, -⟩ := S.drain_run hg hne hcl.1
      rw [hrun] at hr
      simp only [ite_true, run_pure] at hr
      obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj hr
      obtain ⟨hy, -⟩ := S.pick hg hne
      have hycl := (rng_sub (s := t) (cl := cl) src).subset hy
      obtain ⟨hy1, hys⟩ := (hcl.2 _).mp hycl
      refine ⟨wb_dsS hW ?_, fun j' e => ?_⟩
      · have := htag _ hy1 (by
        rw [dsS_C, Array.size_modify]
        exact hys)
        rw [dsS_C, Array.getX_modify, ite_eq_left ⟨rfl, hys⟩] at this
        exact this
      · cases e
        have := hW.P.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        exact jobB_with hj ⟨hv, hup, hsrc, by omega⟩
  · rw [ite_eq_right hks] at hr
    simp only [run_pure] at hr
    obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj hr
    exact ⟨hW, fun j' e => by cases e; exact hwalk⟩

/-! ### A walk step -/

/-- **A walk step**: the weight update (`wiC`, Sz), then a drain start (`sdS`: F, Lab, Sz), or the
funding loop, or the walk moves up. -/
theorem walk_wb {s : Core} {cl : List Nat} {ord : Nat → List Nat} {dr n0 : Nat → Nat} {j : Job}
    {v : Nat} (hpc : j.pc = .walk (some v)) (hTP : TopParams s.P) (hcl : CLok s cl)
    (hI : InvJ (ts s) cl ord dr n0 (some j)) (hW : WB K s) (hj : JobB K j) (hv : v < 2 ^ K)
    (hR : TopRoom K s.P) (hN : s.nodes.size + 2 ≤ 2 ^ K) (hC : s.C.size ≤ 2 ^ K)
    {r : Option Job} {t' : Core} (hr : (walkBody j v).run s = .ok r t')
    (htag : ∀ c, 1 ≤ c → c < t'.C.size → (t'.C.getX c).tag < 2 ^ K) :
    WB K t' ∧ ∀ j', r = some j' → JobB K j' := by
  have S := hI.shape
  by_cases hv0 : v = NIL
  · subst hv0
    rw [run_walkBody_nil] at hr
    obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj hr
    exact ⟨hW, fun j' e => by cases e⟩
  have hlen := CLok.len hcl (S.ord0 ▸ S.ordNodup 0)
  have hww := walk_weight hpc hv0 hI
  have hW1 : WB K (wiC s v) := wb_wiC hW (by omega)
  have hlp := hW.nLivePar v
  by_cases hd : (nd (ts s) v).livePar ≠ NIL ∧ (nd (ts s) v).draining = false ∧
      (nd (ts s) v).overflowOf = NIL ∧ Wd s.P (ht (ts s) v) < (nd (ts s) v).weight + 2
  · obtain ⟨h1, h2, h3, h4⟩ := hd
    obtain ⟨side, hside, hlook⟩ := sp_side hpc hv0 hI h1 hTP h3 h4
    have hrun := sr_run hpc hv0 hI h1 hTP h3 h4 hside hlook
    rw [run_walkBody_drain j s v hv0 h1 h2 h3 h4 hrun] at hr
    obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj hr
    have hs1 := walk_sum hpc hv0 hI (fun x => lookup side x == some .left)
    have hs2 := walk_sum hpc hv0 hI (fun x => lookup side x == some .right)
    refine ⟨wb_sdS hW1 (by
      simp only [wiC, Array.size_modify]
      omega) hR.beta hv
      (lt_of_le_of_lt hs1 (by omega)) (lt_of_le_of_lt hs2 (by omega))
      (drainSide_keys (hW1.nOrder v) hside), fun j' e => ?_⟩
    cases e
    exact jobB_with hj ⟨hv, hlp⟩
  · rw [run_walkBody_noDrain j s v hv0 hd, run_afterDrain] at hr
    have hI' := inv_winc hpc hv0 hI hd
    have hcl' := hcl.topRel (wiC_topRel s v)
    have hTP' : TopParams (wiC s v).P := hTP
    have hO : ((wiC s v).nodes.getX v).overflowOf = srcOf (ts s) v := by
      change ((s.nodes.modify v _).getX v).overflowOf = _
      rw [Array.getX_modify]; split <;> rfl
    rw [hO] at hr
    by_cases hsv : srcOf (ts s) v = NIL
    · rw [ite_eq_left hsv] at hr
      obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj hr
      exact ⟨hW1, fun j' e => by cases e; exact jobB_with hj hlp⟩
    · rw [ite_eq_right hsv] at hr
      have hn : walkNext (ts s) j v = {
        j with
        pc := .fund v (nd (ts s) v).livePar (srcOf (ts s) v) 0
      } := by
        simp [walkNext, hsv]
      rw [hn] at hI'
      exact fund_wb hTP' hcl' hI' hW1 hj ⟨hv, hlp, hW.nOvf v, pos K⟩ hr htag

/-! ### A step of the running job -/

/-- **A step of the running job keeps the stored-value bound**, given the top invariant before
the step (for the run) and after it (for the new tag of a sweep), room for two fresh nodes, and
the chunk count below `2^K` (for the weights). -/
theorem jobStep_wb {s : Core} {job : Job} (hT : TopInv s) (hres : s.resJob = some job) (hW : WB K s)
    (hR : TopRoom K s.P) (hN : s.nodes.size + 2 ≤ 2 ^ K) (hC : s.C.size ≤ 2 ^ K) {r : Option Job}
    {s' : Core} (hr : (jobStep job).run s = .ok r s') (hT' : TopInv {
      s' with
      resJob := r
    }) :
    WB K {
      s' with
      resJob := r
    } := by
  have hP' : s'.P = s.P := ((top_jobStep job).ok hr).rest.1
  have htag : ∀ c, 1 ≤ c → c < s'.C.size → (s'.C.getX c).tag < 2 ^ K := fun c h1 h2 => by
    have := tag_lt_of_topInv hT' h1 h2
    exact lt_pow_mono this (by
      change s'.P.H * s'.P.beta ≤ K
      rw [hP']
      exact hR.tag)
  have hJ : JobB K job := hW.job job hres
  have hH := hW.P.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  suffices h : WB K s' ∧ ∀ j', r = some j' → JobB K j' from h.1.withResJob h.2
  obtain ⟨hTP, cl, ord, dr, n0, hL, hCl, hI⟩ := hT
  rw [hres] at hI
  have hcl : CLok s cl := ⟨hL, hCl⟩
  cases hpc : job.pc with
  | copy l =>
    rw [jobStep_copy hpc] at hr
    obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj hr
    refine ⟨wb_copyC hW hJ l, fun j' e => ?_⟩
    cases e
    refine jobB_with hJ ?_
    split
    · change l + 1 < 2 ^ K; omega
    · trivial
  | walk ov =>
    have hfin : finS (ts s) (some job) = ts s := by simp only [finS, hpc]
    rw [hfin] at hI
    cases ov with
    | none =>
      obtain ⟨hI', -, -⟩ := walkNone_inv hpc hI
      rw [OrderMaintenance.Impl.jobStep_walkNone hpc] at hr
      exact walk_wb (j := {
        job with
        pc := .walk (some (lpr (ts s) job.y))
      }) rfl hTP hcl hI' hW
        (jobB_with hJ (hW.lparE job.y)) (hW.lparE job.y) hR hN hC hr htag
    | some v =>
      rw [OrderMaintenance.Impl.jobStep_walkSome hpc] at hr
      have hv : v < 2 ^ K := by have := hJ.2.2.2; rw [hpc] at this; exact this
      exact walk_wb hpc hTP hcl hI hW hJ hv hR hN hC hr htag
  | afterDrain v up =>
    have hfin : finS (ts s) (some job) = ts s := by simp only [finS, hpc]
    rw [hfin] at hI
    rw [(afterDrain_step hpc hI).1] at hr
    obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj hr
    have hup : up < 2 ^ K := by have := hJ.2.2.2; rw [hpc] at this; exact this.2
    exact ⟨hW, fun j' e => by cases e; exact jobB_with hJ hup⟩
  | fund v up src k =>
    have hfin : finS (ts s) (some job) = ts s := by simp only [finS, hpc]
    rw [hfin] at hI
    have he := job_eta hpc
    rw [he] at hI
    rw [OrderMaintenance.Impl.jobStep_fund hpc] at hr
    have hpcB : JobPcB K (.fund v up src k) := by have := hJ.2.2.2; rw [hpc] at this; exact this
    exact fund_wb hTP hcl hI hW hJ hpcB hr htag

end OrderMaintenance.Proof.Word
