/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Word.PeakSD


/-!
# Theorem W, option (A), stage A2: the peak of a job step (`jobStepS`)

* `jcopy_pk`: a copy step; the next level `ja + 1 ≤ H` by its guard.
* `walk_pkok`: a walk step; the weight `wt + 2` and the height `ht ≤ H` of the walk node are
  bounded at the state before the step (a hypothesis; `walk_lt` provides it), the threshold
  `a^ht` by `powS_pk`, the drain start by `startDrain_pkok` (its weights bounded by the end state).
* `afterDS_pkok`: after a drain, the funding loop (`fund_pkok`).
* `jobStep_pkok`: the step, by the job's program counter.

Nothing here is used by Theorems A and B.
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model
open OrderMaintenance.Machine (Reg BinOp UnOp State)

variable {K KH W : Nat} {κ : Caps}

/-- The values a walk step reads. -/
theorem walkRd_vals {s s1 : Core} {L L1 : Loc} {n : Nat} (h : evalF κ walkRd s L = .ok s1 L1 n) :
    s1 = s ∧ L1 "wv" = L "wv" ∧ L1 "wt" = (s.nodes.getX (L "wv")).weight ∧
      L1 "ht" = (s.nodes.getX (L "wv")).height := by
  unfold walkRd at h
  obtain ⟨sa, La, _, _, ha, h1⟩ := evalF_seq_inv h
  obtain ⟨sb, Lb, _, _, hb, h2⟩ := evalF_seq_inv h1
  obtain ⟨sc, Lc, _, _, hc, h3⟩ := evalF_seq_inv h2
  obtain ⟨sd, Ld, _, _, hd, he⟩ := evalF_seq_inv h3
  obtain ⟨v1, hv1, rfl, rfl⟩ := evalF_assign_inv ha
  obtain ⟨v2, hv2, rfl, rfl⟩ := evalF_assign_inv hb
  obtain ⟨v3, hv3, rfl, rfl⟩ := evalF_assign_inv hc
  obtain ⟨v4, hv4, rfl, rfl⟩ := evalF_assign_inv hd
  obtain ⟨v5, hv5, rfl, rfl⟩ := evalF_assign_inv he
  obtain ⟨-, e2⟩ := Exp.ev_rdv hv2
  obtain ⟨-, e3⟩ := Exp.ev_rdv hv3
  subst e2 e3
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> simp [Machine.State.upd, Fld.get, NF.get]

theorem pcEnc_one {pc : JobPc} (h : (pcEnc pc).1 = 1) : pc = .walk none := by
  cases pc with
  | walk v => cases v <;> simp_all [pcEnc]
  | _ => simp [pcEnc] at h

theorem pcEnc_two {pc : JobPc} (h : (pcEnc pc).1 = 2) : pc = .walk (some (pcEnc pc).2.1) := by
  cases pc with
  | walk v => cases v <;> simp_all [pcEnc]
  | _ => simp [pcEnc] at h

section step
variable {s : Core} {L : Loc}
variable (hC : CapsW K κ) (hK : 8 ≤ K) (hW : 2 * K + 4 ≤ W)
include hC hK hW

/-- **A copy step**: the next level `ja + 1 ≤ H`. -/
theorem jcopy_pk (hG : Gd K KH κ (ΓJ K) s L) : PK K KH κ (ΓJ K) W jcopyS s L := by
  unfold jcopyS
  refine PK.safe_seq' hC (by omega) (by omega) (by jsafe) hG (fun _ _ _ _ hG1 => ?_)
  refine PK.safe_seq' hC (by omega) (by omega) (by jsafe) hG1 (fun _ _ _ _ hG2 => ?_)
  refine PK.safe_seq' hC (by omega) (by omega) (by jsafe) hG2 (fun _ _ _ _ hG3 => ?_)
  refine PK.safe_seq' hC (by omega) (by omega) (by jsafe) hG3 (fun _ _ _ _ hG4 => ?_)
  refine PK.safe_seq' hC (by omega) (by omega) (by jsafe) hG4 (fun s5 L5 _ _ hG5 => ?_)
  refine PK.ite_ok hG5 hC (by jsafe) (fun c hc hc0 => ?_) (fun _ => PK.of_safe hC (by omega) (by
    omega)
    (by jsafe) hG5)
  have hH : L5 "ja" < s5.P.H := by
    simp [Exp.ev, Machine.BinOp.eval, PF.get] at hc
    by_contra hh; simp [hh] at hc; exact hc0 hc.symm
  have hR := hG5.vb.room
  have hHK : s5.P.H < 2 ^ K := by
    have h1 := hR.Hb; have h2 := hR.beta1
    have : s5.P.H + 1 ≤ (s5.P.H + 1) * s5.P.beta := Nat.le_mul_of_pos_right _ (by omega)
    exact lt_of_lt_of_le (Nat.lt_two_pow_self) (pow_le_pow' (by omega))
  have hev : evList κ s5 L5 [0, "ja" + 1, 0, 0, 0] = some [0, L5 "ja" + 1, 0, 0, 0] := by
    simp [evList, Exp.ev, Machine.BinOp.eval]
  refine PK.pcSetV hG5 hev (hG5.pkList hC (fun e he => ?_) hev) (fun v hv => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl <;> jsafe
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl <;> first | exact Nat.two_pow_pos _ | omega

/-- **After a drain** (`afterDS`, locals `av`, `au`): the funding loop. -/
theorem afterDS_pkok (hG : Gd K KH κ (ΓJ K) s L) (hF : Fin (κ := κ) (FB K KH κ (.c .tag))
  afterDS s L) :
    PKok K KH κ (ΓJ K) W afterDS s L := by
  unfold afterDS at hF ⊢
  refine PKok.safe_seq_fin hC (by omega) (by omega) (by jsafe) hG hF (fun s1 L1 n1 h1 hG1 hF1 => ?_)
  refine PKok.ite_ok hC hG1 (by jsafe) (fun _ _ _ => PK.ok (PK.of_safe hC (by omega) (by
    omega) (by jsafe) hG1))
    (fun hv => ?_)
  refine PKok.safe_seq_fin hC (by omega) (by omega) (by
    simp only [afSetS]
    jsafe) hG1 (hF1.ite_f hv)
    (fun s2 L2 n2 h2 hG2 hF2 => fund_pkok hC hK hW hG2 hF2)

/-- **A walk step** at node `wv`, given the bounds of the node's weight and height at the state
before the step. -/
theorem walk_pkok (hcap : κ.lcap .children < 512) (hcapT : κ.lcap .table < 512)
    (hG : Gd K KH κ (ΓJ K) s L)
    (hwb : L "wv" ≠ 0 → (s.nodes.getX (L "wv")).weight + 2 < 2 ^ K ∧ (s.nodes.getX (L
      "wv")).height ≤ s.P.H)
    (hFw : Fin (κ := κ) (FB K KH κ (.n .weight)) walkS s L) (hFt : Fin (κ := κ) (FB K KH κ (.c
      .tag)) walkS s L) :
    PKok K KH κ (ΓJ K) W walkS s L := by
  unfold walkS at hFw hFt ⊢
  refine PKok.ite_ok hC hG (by jsafe) (fun _ _ _ => PK.ok (PK.of_safe hC (by omega) (by
    omega) (by jsafe) hG))
    (fun hv => ?_)
  have hv0 : L "wv" ≠ 0 := by
    intro e; simp [Exp.ev, Machine.BinOp.eval, e] at hv
  obtain ⟨hwt, hht⟩ := hwb hv0
  have hFw1 := hFw.ite_f hv
  have hFt1 := hFt.ite_f hv
  refine PKok.seq (PK.ok (PK.of_safe hC (by omega) (by omega) (by
    simp only [walkRd]
    jsafe) hG))
    (fun s1 L1 n1 h1 hG1 => ?_)
  obtain ⟨e1, hwv, hwt1, hht1⟩ := walkRd_vals h1
  subst s1
  have hFw2 := hFw1.seq_right h1
  have hFt2 := hFt1.seq_right h1
  have hwK : L1 "wv" < 2 ^ K := by simpa [ΓJ] using hG1.loc "wv"
  have hwtK : L1 "wt" < 2 ^ K := by simpa [ΓJ] using hG1.loc "wt"
  have hev : (("wt" : Exp) + 2).ev κ s L1 = some (L1 "wt" + 2) := by
    simp [Exp.ev, Machine.BinOp.eval]
  refine PKok.seq (PK.ok (PK.wr hG1 (f := .n .weight) (i := "wv") (j := L1 "wv") (by
    simp [Exp.ev]) hev
    (by simp only [Exp.pk]; exact pow_mono_lt hwK (by omega)) (hG1.pk hC (by jsafe) hev)
    (by
      simp only [Fld.wd]
      rw [hwt1]
      exact hwt))) (fun s2 L2 n2 h2 hG2 => ?_)
  obtain ⟨_, _, _, _, _, e2⟩ := evalF_wr_inv h2
  subst e2
  have hP2 : s2.P = s.P := evalF_P h2
  have hFw3 := hFw2.seq_right h2
  have hFt3 := hFt2.seq_right h2
  refine PKok.seq (PK.ok (powS_pk hC hW hG2 (by
    rw [hP2, hht1]
    exact hht) (by simp [ΓJ]) (by simp [ΓJ])))
    (fun s3 L3 n3 h3 hG3 => ?_)
  have hFw4 := hFw3.seq_right h3
  have hFt4 := hFt3.seq_right h3
  refine PKok.ite_ok hC hG3 (by
    simp only [walkC]
    jsafe) (fun c hc hc0 => ?_) (fun hc => ?_)
  · refine PKok.seq_fb (Γ' := ΓJ K) (hFw4.ite_t hc hc0) (by decide) (fun hF5 => ?_)
      (fun s4 L4 n4 h4 hG4 _ => PK.ok (PK.of_safe hC (by omega) (by omega) (by jsafe) hG4))
    exact PKok.callF (Γc := ΓD K) (Γe := ΓD K) hC hG3 (by jsafe)
      (fun x => by simp only [ΓD]; split <;> omega) hF5
      (fun vs _ hG0 hF0 => startDrain_pkok hC hK hW hcap hcapT hG0 hF0) (by simp [sdP]) (by simp)
  · have hF5 := hFt4.ite_f hc
    refine PKok.safe_seq_fin hC (by omega) (by omega) (by jsafe) hG3 hF5 (fun s4 L4 n4 h4 hG4
      hF6 => ?_)
    refine PKok.safe_seq_fin hC (by omega) (by omega) (by jsafe) hG4 hF6 (fun s5 L5 n5 h5 hG5
      hF7 => ?_)
    exact afterDS_pkok hC hK hW hG5 hF7

/-- **A job step**, given the bounds of the walk node at the state before the step (`walk_lt`)
and the end-state bounds of the weights and tags (`fin_jobStep`). -/
theorem jobStep_pkok (hcap : κ.lcap .children < 512) (hcapT : κ.lcap .table < 512)
    (hG : Gd K KH κ (ΓJ K) s L) {job : Job} (hjob : s.resJob = some job)
    (hwalk : ∀ v, (job.pc = .walk (some v) ∨ (job.pc = .walk none ∧ v = s.lpar.getX job.y)) → v
      ≠ 0 →
      (s.nodes.getX v).weight + 2 < 2 ^ K ∧ (s.nodes.getX v).height ≤ s.P.H)
    (hFw : Fin (κ := κ) (FB K KH κ (.n .weight)) jobStepS s L) (hFt : Fin (κ := κ) (FB K KH κ
      (.c .tag)) jobStepS s L) :
    PKok K KH κ (ΓJ K) W jobStepS s L := by
  unfold jobStepS at hFw hFt ⊢
  obtain ⟨L', e, hx, hy, hz, ht, ha, hb, hc, hd⟩ := jobRdS_ok (κ := κ) (L := L) hjob
  refine PKok.seq (PK.ok (PK.of_safe hC (by omega) (by omega) (by
    simp only [jobRdS]
    jsafe) hG))
    (fun s1 L1 n1 h1 hG1 => ?_)
  rw [e] at h1
  injection h1 with e1 e2; subst e1 e2
  have hFw1 := hFw.seq_right e
  have hFt1 := hFt.seq_right e
  refine PKok.ite_ok hC hG1 (by jsafe) (fun _ _ _ => PK.ok (jcopy_pk hC hK hW hG1)) (fun
    hv0 => ?_)
  refine PKok.ite_ok hC hG1 (by jsafe) (fun c1 hc1 hc10 => ?_) (fun hv1 => ?_)
  · -- a fresh walk, from `lpar[y]`
    have hpc : job.pc = .walk none := pcEnc_one (by
      simp [Exp.ev, Machine.BinOp.eval,
        ht] at hc1; by_contra hh; simp [hh] at hc1; exact hc10 hc1.symm)
    have hF1 := (hFw1.ite_f hv0).ite_t hc1 hc10
    have hF2 := (hFt1.ite_f hv0).ite_t hc1 hc10
    refine PKok.safe_seq_fin hC (by omega) (by omega) (by jsafe) hG1 hF1 (fun s2 L2 n2 h2 hG2
      hF3 => ?_)
    obtain ⟨w, hw, rfl, rfl⟩ := evalF_assign_inv h2
    obtain ⟨-, rfl⟩ := Exp.ev_rdv hw
    exact walk_pkok hC hK hW hcap hcapT hG2
      (fun h0 => by
        rw [upd_eq] at h0 ⊢
        exact hwalk _ (Or.inr ⟨hpc, by simp [Fld.get, AF.get, hy]⟩) h0) hF3 (hF2.seq_right h2)
  refine PKok.ite_ok hC hG1 (by jsafe) (fun c2 hc2 hc20 => ?_) (fun hv2 => ?_)
  · -- a walk at node `ja`
    have hpc : job.pc = .walk (some (pcEnc job.pc).2.1) := pcEnc_two (by
      simp [Exp.ev, Machine.BinOp.eval,
        ht] at hc2; by_contra hh; simp [hh] at hc2; exact hc20 hc2.symm)
    have hF1 := ((hFw1.ite_f hv0).ite_f hv1).ite_t hc2 hc20
    have hF2 := ((hFt1.ite_f hv0).ite_f hv1).ite_t hc2 hc20
    refine PKok.safe_seq_fin hC (by omega) (by omega) (by jsafe) hG1 hF1 (fun s2 L2 n2 h2 hG2
      hF3 => ?_)
    obtain ⟨w, hw, rfl, rfl⟩ := evalF_assign_inv h2
    simp only [Exp.ev, Option.some.injEq] at hw
    subst hw
    exact walk_pkok hC hK hW hcap hcapT hG2
      (fun h0 => by
        rw [upd_eq] at h0 ⊢
        exact hwalk _ (Or.inl (by
          rw [ha]
          exact hpc)) h0) hF3 (hF2.seq_right h2)
  have hF2 := ((hFt1.ite_f hv0).ite_f hv1).ite_f hv2
  refine PKok.ite_ok hC hG1 (by jsafe) (fun c3 hc3 hc30 => ?_) (fun hv3 => fund_pkok hC hK
    hW hG1 (hF2.ite_f hv3))
  have hF3 := hF2.ite_t hc3 hc30
  refine PKok.safe_seq_fin hC (by omega) (by omega) (by jsafe) hG1 hF3 (fun s4 L4 n4 h4 hG4 hF4
    => ?_)
  refine PKok.safe_seq_fin hC (by omega) (by omega) (by jsafe) hG4 hF4 (fun s5 L5 n5 h5 hG5 hF5
    => ?_)
  exact afterDS_pkok hC hK hW hG5 hF5

end step

end OrderMaintenance.Impl
