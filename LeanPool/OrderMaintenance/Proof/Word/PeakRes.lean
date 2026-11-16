/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Word.PeakSplit
public import LeanPool.OrderMaintenance.Proof.Word.Insert


/-!
# Theorem W, option (A), stage A2: the peak of the reservation loop

The loop is re-run along the joint invariant of `reservation_wb` (option (B): `ResInv`, the
stored-value bound `WB`, the node budget) and of `reservationAgree_top` (Theorem A: the capacity
predicate `Mc`), `RJ`. At each round:

* a job step (`jobStep_pkok`): the walk node's bounds from `walk_lt` (the top invariant at the
  state before the step, from `ResInv`), the end-state bounds from `fin_jobStep`;
* a split start (`split_pkok`): the end-state bound from `fin_split`;
* the state after the round is Level F's (the agreement lemmas, and `evalF` is a function), so the
  invariant passes on.

`reservation_peak`: the loop computes nothing at or above `2^W` (`W ≥ 2K + 4`).

Nothing here is used by Theorems A and B.
-/


@[expose] public section

namespace OrderMaintenance.Proof.Word

open OrderMaintenance.Model OrderMaintenance.Proof OrderMaintenance.Proof.Top OrderMaintenance.Impl OrderMaintenance.Zeroing
open OrderMaintenance.Machine (Reg State)
variable {K KH W : Nat} {κ : Caps}

/-- **The joint invariant of the reservation rounds.** -/
def RJ (K : Nat) (TI : Core → Prop) (μ : Core → Nat) (J k n R NB0 : Nat) (L : List Nat) (s : Core)
    (Mc : Core → Prop) (j : Nat) (t : Core) : Prop :=
  ResInv TI k J n R μ L s j t ∧ WB K t ∧ t.nodes.size + μ t ≤ NB0 + J * t.C.size ∧ Mc t

/-- The node fields of the end state of a step with `WB K`. -/
theorem fb_n_of_WB {t : Core} (hW : WB K t) (hK : 3 ≤ K) (k : NF) : FB K KH κ (.n k) t :=
  fun j _ => by simpa [Fld.wd] using fld_n_of_WB hW hK k j

theorem fb_c_of_WB {t : Core} (hW : WB K t) (hK : 3 ≤ K) (k : CF) : FB K KH κ (.c k) t :=
  fun j _ => by simpa [Fld.wd] using fld_c_of_WB hW hK k j

section round
variable {TI : Core → Prop} {μ : Core → Nat} {J k n R NB0 : Nat} {cap : Params → Nat} {L : List Nat} {s : Core}
  {Mc : Core → Prop}
variable (hTC : TopContract TI μ J cap) (hT : TopWB K TI μ) (hTI : ∀ t, TI t → TopInv t) (hn : 1 ≤ n)
  (hsize : 2 + 2 * (s.count / (s.P.theta + 1 - cmax s.P)) ≤ n + 1)
  (hcap : 2 + 2 * (s.count / (s.P.theta + 1 - cmax s.P)) ≤ cap s.P)
  (hI5 : (s.P.theta : ℝ) + R * (Hn (n - 1) + 1) ≤ s.P.T)
  (hcnt : 2 * s.count + 2 ≤ 2 ^ K) (hNK : NB0 + J * (2 + 2 * s.count) + 2 ≤ 2 ^ K)
  (hMc : ∀ t, Mc t → TopCaps κ t ∧ PQCaps κ t ∧ t.prep = none ∧
      ∀ c, t.C.size ≤ c → ∀ j, (t.path.getX c).getX j = 0)
  (hMpop : ∀ t c t1, Mc t → pqPopMax.run t = .ok c t1 → Mc t1)
  (hMjob : ∀ j t job r t1, ResInv TI k J n R μ L s j t → Mc t → t.resJob = some job →
      (jobStep job).run t = .ok r t1 → ResInv TI k J n R μ L s (j + 1) { t1 with resJob := r } →
      Mc { t1 with resJob := r })
  (hMsplit : ∀ j t c t1 t2, ResInv TI k J n R μ L s j t → Mc t → t.resJob = none → pqPopMax.run t = .ok c t1 →
      (splitChunkStart c).run t1 = .ok () t2 → ResInv TI k J n R μ L s (j + 1) t2 → Mc t2)
include hTC hT hTI hn hsize hcap hI5 hcnt hNK hMc hMpop hMjob hMsplit

/-- **A job round of the joint invariant**: the step's run, the invariant after it, and the facts
the peak proof needs. -/
theorem rj_job {j : Nat} {t : Core} {job : Job} (hj : j < k) (hJ : RJ K TI μ J k n R NB0 L s Mc j t)
    (hjob : t.resJob = some job) :
    ∃ r t1, (jobStep job).run t = .ok r t1 ∧ RJ K TI μ J k n R NB0 L s Mc (j + 1) { t1 with resJob := r } ∧
      TopInv t ∧ TopInv { t1 with resJob := r } ∧ t.nodes.size + 2 ≤ 2 ^ K ∧ t.C.size ≤ 2 ^ K := by
  obtain ⟨hI, hWt, hNBt, hM⟩ := hJ
  have step := resInv_step (L := L) (k := k) hTC hn hsize hcap hI5
  obtain ⟨-, hs'⟩ := step j t hI hj
  have hCt : t.C.size ≤ 2 + 2 * s.count := by rw [← hI.2.2.1]; exact hI.1.Csize
  have hJC : J * t.C.size ≤ J * (2 + 2 * s.count) := Nat.mul_le_mul_left J hCt
  obtain ⟨r, t1, hj1, hI'⟩ := hs' job hjob
  refine ⟨r, t1, hj1, ?_, hTI t hI.2.1, hTI _ hI'.2.1, by omega, by omega⟩
  obtain ⟨hL, hTt, -⟩ := id hI
  obtain ⟨A, hIA, -⟩ := hL.inv
  obtain ⟨hW1, hN1⟩ := hT.step t A job r t1 hIA hTt hjob hWt (by omega) (by omega) hj1 hI'.2.1
  have hCs : ({ t1 with resJob := r } : Core).C.size = t.C.size := by
    have := top_jobStep job t; rw [hj1] at this; exact this.Csize
  refine ⟨hI', hW1, ?_, hMjob j t job r t1 hI hM hjob hj1 hI'⟩
  rw [hCs]
  show t1.nodes.size + _ ≤ _
  omega

/-- **A split round of the joint invariant**: the pop and the split start, the invariant after them,
and `Fin (WB K)` of the split start at the state after the pop. -/
theorem rj_split {j : Nat} {t : Core} (hj : j < k) (hJ : RJ K TI μ J k n R NB0 L s Mc j t)
    (hnone : t.resJob = none) (hq0 : t.pqHi ≠ 0) :
    ∃ c t1 t2, pqPopMax.run t = .ok c t1 ∧ (splitChunkStart c).run t1 = .ok () t2 ∧
      RJ K TI μ J k n R NB0 L s Mc (j + 1) t2 ∧
      OrderMaintenance.Impl.Fin (κ := κ) (WB K) splitChunkStartS t1 (State.setLocs (fun _ => 0) ["x"] [c]) ∧
      ∃ D, SplitAgree κ t1 c D := by
  obtain ⟨hI, hWt, hNBt, hM⟩ := hJ
  have step := resInv_step (L := L) (k := k) hTC hn hsize hcap hI5
  obtain ⟨hn', -⟩ := step j t hI hj
  rcases hn' hnone with ⟨h0, -⟩ | ⟨-, c, t1, t2, hpop, hsc, hI'⟩
  · exact absurd h0 hq0
  refine ⟨c, t1, t2, hpop, hsc, ?_⟩
  obtain ⟨hL, hTt, hc, hP, -⟩ := id hI
  obtain ⟨bl, nb, hQ⟩ := hL.pq
  obtain ⟨c', hpop', hcin, -⟩ := pqPopMax_ok hQ hq0
  rw [hpop'] at hpop
  obtain ⟨e1, e2⟩ := EStateM.Result.ok.inj hpop
  subst e2
  subst c'
  have hcq := hcin
  unfold inQC at hcq; simp only [decide_eq_true_eq] at hcq
  obtain ⟨hcL, hcQ, -⟩ := hcq
  obtain ⟨A, hIA, -⟩ := hL.inv
  have hD := delSt_only t c
  have hI1 : INV (delSt t c) A := hIA.of_sameLinks hD.sameLinks (fun d => by simp only [cT, hD.C])
  have hTI1 : TI (delSt t c) := hTC.frame _ _ hD.topSame hTt
  have hsz1 : (delSt t c).C.size = t.C.size := by rw [hD.C]
  have hQS := hD.lowSame.qsame
  have hcL1 : LiveC (delSt t c) c := by simp only [LiveC, hsz1]; exact hcL
  have hcq1 : cSt (delSt t c) c = .quiet := (hQS.q c hcL).mpr hcQ
  have hnone1 : (delSt t c).resJob = none := by rw [hD.rest.2.2.2.2.2.2.2.2.1]; exact hnone
  have hW1 := ((ht_pqPopMax (K := K) (P0 := t.P)).ok hWt rfl hpop')
  have hM1 := hMpop t c _ hM hpop'
  obtain ⟨hTC1, -, hpr1, hrow1⟩ := hMc _ hM1
  have hMs := hMsplit j t c _ t2 hI hM hnone hpop' hsc hI'
  -- the run of the split start
  obtain ⟨job, s2, hjb, rfl⟩ := splitChunkStart_dec hsc
  have hR : TopRel (linkChunkPair (push2 (delSt t c)) c (delSt t c).C.size
      ((delSt t c).C.size + 1)) s2 := by
    have := top_insertAround c (delSt t c).C.size ((delSt t c).C.size + 1)
      (linkChunkPair (push2 (delSt t c)) c (delSt t c).C.size ((delSt t c).C.size + 1))
    rw [hjb] at this; exact this
  obtain ⟨hL2, hTI2, hc2, -, y2, i2, a2, ip2, js2, -, hRA⟩ := id hI'
  have h2 : (markState s2 c (delSt t c).C.size ((delSt t c).C.size + 1) job).C.size =
      (delSt t c).C.size + 2 := by
    simp only [markState, Array.size_modify']
    rw [hR.Csize]; simp [linkChunkPair, push2]
  have hroom : (delSt t c).C.size + 2 ≤ 2 ^ K := by
    have h1 := hL2.Csize
    rw [h2, hc2] at h1
    omega
  have hc2' : c < 2 ^ K := hW1.2
  have hWl := wb_splitLink hW1.1.1 hc2' hroom
  obtain ⟨hW2, hJ, hN2⟩ := hT.start _ A c job s2 hI1 hTI1 hnone1 hcL1 hcq1 hroom hWl hjb hTI2
  obtain ⟨D, -, hSA⟩ := splitAgree_top hI1 (hTI _ hTI1) hnone1 hcL1 hpr1 hrow1 hTC1
  refine ⟨⟨hI', wb_markState hW2 hc2' (by omega) (by omega) hJ, ?_, hMs⟩,
    fin_split hT hTI hI1 hTI1 hnone1 hcL1 hcq1 hpr1 hrow1 hTC1 hroom hW1.1.1 hc2' hsc hTI2, D, hSA⟩
  -- the node budget: a job of measure at most `J`, and two more chunks
  have hmu : μ (markState s2 c (delSt t c).C.size ((delSt t c).C.size + 1) job) ≤ J := by
    unfold RoundAt at hRA
    have e : (markState s2 c (delSt t c).C.size ((delSt t c).C.size + 1) job).resJob = some job := rfl
    rw [e] at hRA
    omega
  have hn2 : (markState s2 c (delSt t c).C.size ((delSt t c).C.size + 1) job).nodes.size =
      t.nodes.size := by
    show s2.nodes.size = _; rw [hN2, hD.rest.2.2.2.2.2.2.2.2.2.2.1]
  rw [hn2, h2]
  have e1 : J * ((delSt t c).C.size + 2) = J * t.C.size + 2 * J := by rw [hsz1]; ring
  rw [e1]
  omega

/-- **A round of the reservation** (`resBody`, at `dn = 0`): its peak, and the invariant after it
(unless it stopped the loop). -/
theorem resRound_peak (hC : CapsW K κ) (hK : 8 ≤ K) (hW : 2 * K + 4 ≤ W)
    (hcapC : κ.lcap .children < 512) (hcapT : κ.lcap .table < 512) (hpow : s.P.a = 2 ^ Nat.log2 s.P.a)
    (hRm : TopRoom K s.P)
    {j : Nat} {t : Core} {Lr : Loc} (hj : j < k) (hJ : RJ K TI μ J k n R NB0 L s Mc j t)
    (hG : Gd K KH κ (ΓK K) t Lr) (hdn : Lr "dn" = 0) :
    PKok K KH κ (ΓK K) W resBody t Lr ∧ ∀ t' L' m, evalF κ resBody t Lr = .ok t' L' m →
      (L' "dn" = 0 ∧ RJ K TI μ J k n R NB0 L s Mc (j + 1) t') ∨ L' "dn" = 1 := by
  have hM := hJ.2.2.2
  obtain ⟨hTCt, hPQ, hpr, hrow⟩ := hMc t hM
  have hP : t.P = s.P := hJ.1.2.2.2.1
  have hdn0 : ("dn" =ₑ 0 : Exp).ev κ t Lr = some 1 := by simp [Exp.ev, OrderMaintenance.Machine.BinOp.eval, hdn]
  constructor
  · -- the peak
    unfold resBody
    refine PKok.ite_ok hC hK hW hG (by jsafe) (fun _ _ _ => ?_) (fun hv => by rw [hdn0] at hv; cases hv)
    refine PKok.ite_ok hC hK hW hG (by jsafe) (fun c hc hc0 => ?_) (fun hc => ?_)
    · -- a job step
      cases hjob : t.resJob with
      | none => simp [Exp.ev, OF.get, hjob, b2n] at hc; exact absurd hc.symm hc0
      | some job =>
        obtain ⟨r, t1, hrun, -, hT0, hT1, hN, hCs⟩ := rj_job hTC hT hTI hn hsize hcap hI5 hcnt hNK hMc hMpop hMjob
          hMsplit hj hJ hjob
        have hFin := fin_jobStep (κ := κ) hT0 hjob hpr (by rw [hP]; exact hpow) hTCt hJ.2.1 (by rw [hP]; exact hRm)
          hN hCs hrun hT1
        refine PKok.callS hC hK hW (Γc := ΓJ K) (Γe := ΓJ K) hG (by jsafe) (ΓJ_ge K) (fun vs hvs hG0 => ?_)
          (by simp [jobP]) (by simp)
        simp only [evList, List.mapM_nil] at hvs
        cases hvs
        exact jobStep_pkok hC hK hW hcapC hcapT hG0 hjob (fun v hv hv0 => walk_lt hT0 hjob hv hv0 hCs)
          (hFin.mono (fun u hu => fb_n_of_WB hu (by omega) .weight))
          (hFin.mono (fun u hu => fb_c_of_WB hu (by omega) .tag))
    · -- no job
      have hnone : t.resJob = none := by
        cases hjob : t.resJob with
        | none => rfl
        | some _ => simp [Exp.ev, OF.get, hjob, b2n] at hc
      refine PKok.seq (PK.ok (PK.of_safe hC (by omega) (by omega) (by simp only [pqEmptyP]; jsafe) hG))
        (fun s1 L1 n1 h1 hG1 => ?_)
      by_cases h0 : t.pqHi = 0
      · obtain ⟨Le, ce, ee, her, -⟩ := pqEmpty_agree κ t (State.setLocs (fun _ => 0) [] [])
          (b := true) (σ' := t) (by simp [pqEmpty, h0])
        have e1 := evalF_call_ok (q := pqEmptyP) (args := []) (ds := ["em"]) (L := Lr) (by simp [evList]) ee
        rw [e1] at h1
        injection h1 with e2 e3; subst e2 e3
        refine PKok.ite_ok hC hK hW hG1 (by jsafe)
          (fun _ _ _ => PK.ok (PK.of_safe hC (by omega) (by omega) (by jsafe) hG1)) (fun hv => ?_)
        simp [Exp.ev, OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd,
          pqEmptyP, her, b2n] at hv
      · obtain ⟨Le, ce, ee, her, -⟩ := pqEmpty_agree κ t (State.setLocs (fun _ => 0) [] [])
          (b := false) (σ' := t) (by simp [pqEmpty, h0])
        have e1 := evalF_call_ok (q := pqEmptyP) (args := []) (ds := ["em"]) (L := Lr) (by simp [evList]) ee
        rw [e1] at h1
        injection h1 with e2 e3; subst e2 e3
        refine PKok.ite_ok hC hK hW hG1 (by jsafe) (fun c hc hc0 => ?_) (fun _ => ?_)
        · simp [Exp.ev, OrderMaintenance.Machine.State.setLocs,
          OrderMaintenance.Machine.State.upd, pqEmptyP, her, b2n] at hc
          exact absurd hc.symm hc0
        obtain ⟨c, t1, t2, hpop, hsc, -, hFin, -⟩ := rj_split hTC hT hTI hn hsize hcap hI5 hcnt hNK hMc hMpop hMjob
          hMsplit hj hJ hnone h0
        refine PKok.seq (PK.ok (PK.of_safe hC (by omega) (by omega) (by simp only [pqPopMaxP, pqDelP]; jsafe) hG1))
          (fun s2 L2 n2 h2 hG2 => ?_)
        obtain ⟨⟨Lp, cp, ep, hcp, -⟩, -⟩ := pqPopMax_agree κ t (State.setLocs (fun _ => 0) [] []) hPQ hpop
        rw [evalF_call_ok (q := pqPopMaxP) (args := []) (ds := ["x"]) (by simp [evList]) ep] at h2
        injection h2 with e5 e6; subst e5 e6
        refine PKok.callS hC hK hW (Γc := ΓS K) (Γe := ΓS K) hG2 (by jsafe) (ΓS_ge K) (fun vs hvs hG0 => ?_)
          (by simp [splitP]) (by simp)
        simp [evList, Exp.ev, OrderMaintenance.Machine.State.setLocs,
          OrderMaintenance.Machine.State.upd, pqPopMaxP, hcp] at hvs
        subst hvs
        exact split_pkok hC hK hW hG0 (hFin.mono (fun u hu => fb_c_of_WB hu (by omega) .tag))
  · -- the invariant after the round
    intro t' L' m he
    cases hjob : t.resJob with
    | some job =>
      obtain ⟨r, t1, hrun, hJ', hT0, -, -, -⟩ := rj_job hTC hT hTI hn hsize hcap hI5 hcnt hNK hMc hMpop hMjob
        hMsplit hj hJ hjob
      have hA := jobAgree hT0 hjob hpr (by rw [hP]; exact hpow) hTCt
      obtain ⟨L2, m2, e2, hdn2, -⟩ := resAgree_job hjob hA hrun Lr hdn
      rw [e2] at he
      injection he with e3 e4; subst e3 e4
      exact Or.inl ⟨by simpa [b2n] using hdn2, hJ'⟩
    | none =>
      by_cases h0 : t.pqHi = 0
      · obtain ⟨L2, m2, e2, hdn2, -⟩ := resAgree_empty (κ := κ) hjob h0 Lr hdn
        rw [e2] at he
        injection he with e3 e4; subst e3 e4
        exact Or.inr (by simpa [b2n] using hdn2)
      · obtain ⟨c, t1, t2, hpop, hsc, hJ', -, D, hSA⟩ := rj_split hTC hT hTI hn hsize hcap hI5 hcnt hNK hMc hMpop
          hMjob hMsplit hj hJ hjob h0
        obtain ⟨L2, m2, e2, hdn2, -⟩ := resAgree_split hjob hPQ h0 hpop hSA hsc Lr hdn
        rw [e2] at he
        injection he with e3 e4; subst e3 e4
        exact Or.inl ⟨by simpa [b2n] using hdn2, hJ'⟩

/-- **The reservation loop** (`reservationS`, `reservationBudget` rounds): its peak, along the
  joint invariant. -/
theorem reservation_peak (hC : CapsW K κ) (hK : 8 ≤ K) (hW : 2 * K + 4 ≤ W)
    (hcapC : κ.lcap .children < 512) (hcapT : κ.lcap .table < 512) (hpow : s.P.a = 2 ^ Nat.log2 s.P.a)
    (hRm : TopRoom K s.P) (hk : k = s.P.reservationBudget) (h0 : RJ K TI μ J k n R NB0 L s Mc 0 s)
    {Lr : Loc} (hG : Gd K KH κ (ΓK K) s Lr) : PKok K KH κ (ΓK K) W reservationS s Lr := by
  unfold reservationS
  refine PKok.seq (PK.ok (PK.of_safe hC (by omega) (by omega) (by jsafe) hG)) (fun s1 L1 n1 h1 hG1 => ?_)
  obtain ⟨v, hv, e1, e2⟩ := evalF_assign_inv h1
  subst e1 e2
  simp only [Exp.ofNat_def, Exp.ev, Option.some.injEq] at hv
  subst hv
  have hKR : s.P.reservationBudget < 2 ^ K := by simpa [PF.get] using hG.vb.prm .KR
  have hn0 : (Exp.prm .KR).ev κ s (State.upd Lr "dn" 0) = some s.P.reservationBudget := by simp
    [Exp.ev, PF.get]
  refine PKok.loop hn0 (hG1.pk hC (by jsafe) hn0)
    (fun j S L' => Gd K KH κ (ΓK K) S L' ∧ ((L' "dn" = 0 ∧ RJ K TI μ J k n R NB0 L s Mc j S) ∨ L' "dn" = 1))
    ⟨hG1, Or.inl ⟨upd_eq _ _ _, h0⟩⟩ (fun _ _ _ h => h.1) (fun j S L' hj ⟨hGS, hcase⟩ s' L'' c he => ?_)
  have hGS' : Gd K KH κ (ΓK K) S (State.upd L' "ri" j) := ⟨hGS.enc, hGS.vb, upd_lt hGS.loc (by simp only [ΓK]; omega)⟩
  rcases hcase with ⟨hdn, hJ⟩ | hdn
  · have hdn' : State.upd L' "ri" j "dn" = 0 := by rw [upd_ne _ _ (by decide)]; exact hdn
    obtain ⟨hpk, hpost⟩ := resRound_peak hTC hT hTI hn hsize hcap hI5 hcnt hNK hMc hMpop hMjob hMsplit hC hK hW
      hcapC hcapT hpow hRm (by rw [hk]; exact hj) hJ hGS' hdn'
    obtain ⟨p1, g1⟩ := hpk _ _ _ he
    exact ⟨p1, g1, hpost _ _ _ he⟩
  · have hdn' : State.upd L' "ri" j "dn" = 1 := by rw [upd_ne _ _ (by decide)]; exact hdn
    have hc1 : ("dn" =ₑ 0 : Exp).ev κ S (State.upd L' "ri" j) = some 0 := by
      simp [Exp.ev, OrderMaintenance.Machine.BinOp.eval, hdn]
    have he' := he
    unfold resBody at he'
    obtain ⟨v, hv, m, hm⟩ := evalF_ite_inv he'
    rw [hc1] at hv; cases hv
    simp [evalF] at hm
    obtain ⟨e1, e2, -⟩ := hm
    subst e1 e2
    refine ⟨?_, hGS', Or.inr hdn'⟩
    unfold resBody
    rw [pkF_ite hc1, ite_eq_right (by simp)]
    simp only [pkF]
    exact max_lt (hGS'.pk hC (by jsafe) hc1) (Nat.two_pow_pos _)

end round

end OrderMaintenance.Proof.Word
