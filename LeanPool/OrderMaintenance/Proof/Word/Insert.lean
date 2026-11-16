/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Word.Hooks
public import LeanPool.OrderMaintenance.Impl.GlueCore


/-!
# Theorem W, stage B1: a core insertion keeps the stored-value bound

`insertAfter_wb`: from the cost invariant of a core (`CostInv`, as in `insertAfter_cost`), the
stored-value bound `WB K`, room for labels and numeric room for the sizes, an insertion ends in
a core with `WB K`. The proof follows `insertAfter_cost` and `background_ok` step by step and runs
the cost proof's phase lemmas with the hooks of `Hooks.lean` added.

The top structure's two operations (`insertAround`, `jobStep`) enter through the contract
`TopWB`, which stage B2 proves (the Tag, weight and node sites of `docs/WORD.md` §2).
-/


@[expose] public section

namespace OrderMaintenance.Proof.Word

open OrderMaintenance.Model OrderMaintenance.Proof OrderMaintenance.Zeroing
variable {K : Nat}

/-- **The top structure keeps the stored-value bound** (the contract stage B2 proves,
`topWB` in `TopWB.lean`): the insertion of a split's two new chunks into the tree, and each step of
the running job. The top invariant of the state after the operation is a hypothesis (it bounds the
tags the operation writes); a job step also needs room for two fresh nodes and the chunk count
below `2^K` (for the weights), and does not grow `nodes.size + μ` (so the node count stays within a
budget, as in `NodeB`). -/
structure TopWB (K : Nat) (TI : Core → Prop) (μ : Core → Nat) : Prop where
  start : ∀ s A x job s2, INV s A → TI s → s.resJob = none → LiveC s x → cSt s x = .quiet →
    s.C.size + 2 ≤ 2 ^ K → WB K (linkChunkPair (push2 s) x s.C.size (s.C.size + 1)) →
    (insertAround x s.C.size (s.C.size + 1)).run (linkChunkPair (push2 s) x s.C.size (s.C.size +
      1)) =
      .ok job s2 → TI (markState s2 x s.C.size (s.C.size + 1) job) →
    WB K s2 ∧ JobB K job ∧ s2.nodes.size = s.nodes.size
  step : ∀ s A job r s', INV s A → TI s → s.resJob = some job → WB K s →
    s.nodes.size + 2 ≤ 2 ^ K → s.C.size ≤ 2 ^ K → (jobStep job).run s = .ok r s' →
    TI {
      s' with
      resJob := r
    } →
    WB K {
      s' with
      resJob := r
    } ∧ s'.nodes.size + μ {
      s' with
      resJob := r
    } ≤ s.nodes.size + μ s

/-! ### What an insertion leaves of the top structure -/

instance : IsPre TopSame := ⟨TopSame.refl, fun _ _ _ => TopSame.trans⟩

/-- Close `∀ s, TopSame s (f s)` for an update of the queue's fields. -/
macro "tsame" : tactic => `(tactic| (intro _; exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl,
  fun _ => ⟨rfl, rfl, rfl⟩, rfl⟩))

theorem ts_pqLinkAfter (s p : Nat) : Pres TopSame (pqLinkAfter s p) := by
  unfold pqLinkAfter; pres; all_goals tsame
theorem ts_pqAdd (c s p : Nat) : Pres TopSame (pqAdd c s p) := by
  unfold pqAdd; pres [ts_pqLinkAfter _ _]; all_goals tsame
theorem ts_pqDel (c : Nat) : Pres TopSame (pqDel c) := by
  unfold pqDel; pres; all_goals tsame
theorem ts_pqInsertScan (c s : Nat) : Pres TopSame (pqInsertScan c s) := by
  unfold pqInsertScan; pres [ts_pqAdd _ _ _]
theorem ts_pqAdjust (c old new : Nat) : Pres TopSame (pqAdjust c old new) := by
  unfold pqAdjust; pres [pres_getP, ts_pqInsertScan _ _, ts_pqDel _, ts_pqAdd _ _ _]
theorem ts_chunkSize (c : Nat) (inc : Bool) : Pres TopSame (chunkSize c inc) := by
  unfold chunkSize modC
  pres [pres_getC _, ts_pqAdjust _ _ _]
  all_goals
    intro s
    refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, by simp, fun d => ?_, rfl⟩
    simp only [cN, cP, cT, Array.getX_modify]
    split <;> simp

theorem ts_linkElem (s : Core) (x y lab hh : Nat) : TopSame s (linkElem s x y lab hh) :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, fun _ => ⟨rfl, rfl, rfl⟩, rfl⟩

/-! ### The split start -/

/-- The run of a split start, decomposed. -/
theorem splitChunkStart_dec {t t2 : Core} {x : Nat} (h : (splitChunkStart x).run t = .ok () t2) :
    ∃ job s2, (insertAround x t.C.size (t.C.size + 1)).run
        (linkChunkPair (push2 t) x t.C.size (t.C.size + 1)) = .ok job s2 ∧
      t2 = markState s2 x t.C.size (t.C.size + 1) job := by
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
      simp only [markSplit_run] at h
      obtain ⟨-, e⟩ := EStateM.Result.ok.inj h
      exact ⟨job, s2, rfl, e.symm⟩
    · rw [hj] at h; simp at h
  · simp at h

/-- The chunk count of a state of the low invariant is at most `2 + 2·count` (`CountInv`). -/
theorem _root_.OrderMaintenance.Proof.LowInv.Csize {t : Core} {L : List Nat} (hL : LowInv t L) :
  t.C.size ≤ 2 + 2 * t.count := by
  obtain ⟨e, pops, hN⟩ := hL.cnt
  have h1 := hN.chunks (by
    have := hL.cp.I4
    omega)
  have h2 : t.count / (t.P.theta + 1 - cmax t.P) ≤ t.count := Nat.div_le_self _ _
  omega

/-- **The reservation keeps the stored-value bound**, given the top structure's contract, room
for the chunks (`2·count + 2 ≤ 2^K`; the chunk count is at most `2 + 2·count`, `CountInv`), and a
node budget: `nodes.size + μ ≤ NB0 + J·C.size` (a split start adds 2 chunks and a job of measure at
most `J`; a job step does not grow `nodes.size + μ`), with `NB0 + J·(2 + 2·count) + 2 ≤ 2^K`. -/
theorem reservation_wb {TI : Core → Prop} {μ : Core → Nat} {J k n R NB0 : Nat} {cap : Params → Nat}
    {L : List Nat} {s : Core} (hTC : TopContract TI μ J cap) (hT : TopWB K TI μ)
    (h0 : ResInv TI k J n R μ L s 0 s) (hn : 1 ≤ n)
    (hsize : 2 + 2 * (s.count / (s.P.theta + 1 - cmax s.P)) ≤ n + 1)
    (hcap : 2 + 2 * (s.count / (s.P.theta + 1 - cmax s.P)) ≤ cap s.P)
    (hI5 : (s.P.theta : ℝ) + R * (Hn (n - 1) + 1) ≤ s.P.T) (hW : WB K s)
    (hcnt : 2 * s.count + 2 ≤ 2 ^ K) (hNB : s.nodes.size + μ s ≤ NB0 + J * s.C.size)
    (hNK : NB0 + J * (2 + 2 * s.count) + 2 ≤ 2 ^ K) :
    ∃ t', (reservation k).run s = .ok () t' ∧ WB K t' := by
  have step := resInv_step (L := L) (k := k) hTC hn hsize hcap hI5
  obtain ⟨t', hrun, hres⟩ := reservation_ok (fun j t => ResInv TI k J n R μ L s j t ∧ WB K t ∧
      t.nodes.size + μ t ≤ NB0 + J * t.C.size)
    (fun t => WB K t) ⟨h0, hW, hNB⟩ (by
    intro j t ⟨hI, hWt, hNBt⟩ hj
    obtain ⟨hn', hs'⟩ := step j t hI hj
    refine ⟨fun hnone => ?_, fun job hjob => ?_⟩
    · rcases hn' hnone with ⟨hq0, -⟩ | ⟨hq0, c, t1, t2, hpop, hsc, hI'⟩
      · exact Or.inl ⟨hq0, hWt⟩
      · right
        refine ⟨hq0, c, t1, t2, hpop, hsc, hI', ?_⟩
        obtain ⟨hL, hTt, hc, hP, -⟩ := hI
        -- the popped chunk and the state after the pop
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
        have hI1 : INV (delSt t c) A := hIA.of_sameLinks hD.sameLinks (fun d => by simp only
          [cT, hD.C])
        have hTI1 : TI (delSt t c) := hTC.frame _ _ hD.topSame hTt
        have hsz1 : (delSt t c).C.size = t.C.size := by rw [hD.C]
        have hQS := hD.lowSame.qsame
        have hcL1 : LiveC (delSt t c) c := by simp only [LiveC, hsz1]; exact hcL
        have hcq1 : cSt (delSt t c) c = .quiet := (hQS.q c hcL).mpr hcQ
        have hnone1 : (delSt t c).resJob = none := by rw [hD.rest.2.2.2.2.2.2.2.2.1]; exact hnone
        have hW1 := ((ht_pqPopMax (K := K) (P0 := t.P)).ok hWt rfl hpop')
        -- the run of the split start
        obtain ⟨job, s2, hj, rfl⟩ := splitChunkStart_dec hsc
        have hR : TopRel (linkChunkPair (push2 (delSt t c)) c (delSt t c).C.size
            ((delSt t c).C.size + 1)) s2 := by
          have := top_insertAround c (delSt t c).C.size ((delSt t c).C.size + 1)
            (linkChunkPair (push2 (delSt t c)) c (delSt t c).C.size ((delSt t c).C.size + 1))
          rw [hj] at this; exact this
        obtain ⟨hL2, hTI2, hc2, -, y2, i2, a2, ip2, js2, -, hRA⟩ := hI'
        have h2 : (markState s2 c (delSt t c).C.size ((delSt t c).C.size + 1) job).C.size =
            (delSt t c).C.size + 2 := by
          simp only [markState, Array.size_modify']
          rw [hR.Csize]; simp [linkChunkPair, push2]
        -- room for the two new chunks
        have hroom : (delSt t c).C.size + 2 ≤ 2 ^ K := by
          have h1 := hL2.Csize
          rw [h2, hc2] at h1
          omega
        have hc2' : c < 2 ^ K := hW1.2
        have hWl := wb_splitLink hW1.1.1 hc2' hroom
        obtain ⟨hW2, hJ, hN2⟩ := hT.start _ A c job s2 hI1 hTI1 hnone1 hcL1 hcq1 hroom hWl hj hTI2
        refine ⟨wb_markState hW2 hc2' (by omega) (by omega) hJ, ?_⟩
        -- the node budget: a job of measure at most `J`, and two more chunks
        have hmu : μ (markState s2 c (delSt t c).C.size ((delSt t c).C.size + 1) job) ≤ J := by
          unfold RoundAt at hRA
          have e : (markState s2 c (delSt t c).C.size ((delSt t c).C.size + 1) job).resJob =
            some job := rfl
          rw [e] at hRA
          omega
        have hn2 : (markState s2 c (delSt t c).C.size ((delSt t c).C.size + 1) job).nodes.size =
            t.nodes.size := by
          change s2.nodes.size = _; rw [hN2, hD.rest.2.2.2.2.2.2.2.2.2.2.1]
        rw [hn2, h2]
        have e1 : J * ((delSt t c).C.size + 2) = J * t.C.size + 2 * J := by rw [hsz1]; ring
        rw [e1]
        omega
    · have hCt : t.C.size ≤ 2 + 2 * s.count := by rw [← hI.2.2.1]; exact hI.1.Csize
      have hJC : J * t.C.size ≤ J * (2 + 2 * s.count) := Nat.mul_le_mul_left J hCt
      obtain ⟨r, t1, hj1, hI'⟩ := hs' job hjob
      refine ⟨r, t1, hj1, hI', ?_⟩
      obtain ⟨hL, hTt, -⟩ := hI
      obtain ⟨A, hIA, -⟩ := hL.inv
      obtain ⟨hW1, hN1⟩ := hT.step t A job r t1 hIA hTt hjob hWt (by omega) (by omega) hj1 hI'.2.1
      have hCs : ({
        t1 with
        resJob := r
      } : Core).C.size = t.C.size := by
        have := top_jobStep job t; rw [hj1] at this; exact this.Csize
      refine ⟨hW1, ?_⟩
      rw [hCs]
      change t1.nodes.size + _ ≤ _
      omega)
  refine ⟨t', hrun, ?_⟩
  rcases hres with h | h
  · exact h.2.1
  · exact h

/-! ### The chunk phase -/

/-- **The chunk phase keeps the stored-value bound** (the context of `driveChunk_ok`). -/
theorem driveChunk_wb {t : Core} {A : Abs} {L : List Nat} {gh : GGh} {s₀ δu : Nat → Nat} {c : Nat}
    (hI : INV t A) (hel : A.elist = L) (hG : GInv t L gh (fun _ => 0)) (hC : CInv t L (δ1 c) δu s₀)
    (hLX : LX s₀ (δ1 c) δu t) (hGP : GParams t.P) (hCP : CParams t.P) (hcL : LiveC t c)
    (hcnd : cSt t c ≠ .dead) (hcsz : 1 ≤ cSz t c) (hW : WB K t) (hL : LabRoom K t.P)
    (hlen : 4 * L.length + 1 ≤ 2 ^ K) :
    ∃ t4, (driveChunk c).run t = .ok () t4 ∧ WB K t4 := by
  have hδu := hC.δu
  have drive : ∀ x, LiveC t x → cSt t x = .splitting →
      (c = cLl t x ∨ c = x ∨ c = cRr t x) →
      ∃ t4, (driveChunkFrom x).run t = .ok () t4 ∧ WB K t4 := by
    intro x hxL hxs hcx
    subst hel
    have Fx := hC.cfam x hxL hxs
    have hlx := Fx.lx hI hxL
    have hrx := Fx.rx hI hxL
    have hlr := Fx.lr hI hxL
    have hCx : CInvE t A.elist (δ1 c) δu s₀ x :=
      { hC with c1 := fun z hz hzs _ => hC.c1 z hz hzs (by
        unfold NIL
        have := hz.1
        omega) }
    have hC1 := hC.c1 x hxL hxs (by
      unfold NIL
      have := hxL.1
      omega)
    have hXs := cxsteps_wb (cxsteps_linv (L := A.elist) (δ := δ1 c) (δu := δu) (s₀ := s₀) (x := x))
      hL hlen
    obtain ⟨t4, hrun, hD⟩ := cinv_drive hI hG hCx hC1 hXs ⟨hLX, hW, rfl⟩ hGP hCP
      hxL hxs (fun c' h1 h2 h3 => by
        unfold δ1; rw [ite_eq_right]; rintro rfl; rcases hcx with h | h | h <;> contradiction)
      (by
        unfold δ1
        rcases hcx with rfl | rfl | rfl <;> simp [hlx, hrx, hlr, Ne.symm hlx, Ne.symm hrx,
          Ne.symm hlr])
      (by
        unfold δ1
        refine ⟨?_, ?_, ?_⟩ <;> split <;> first | omega | (subst_vars; exact hcsz))
    refine ⟨t4, hrun, ?_⟩
    rcases hD.xx with ⟨-, h⟩ | ⟨-, h⟩
    · exact h.1
    · exact h.1
  cases hst : cSt t c with
  | splitting =>
    rw [driveChunk_run_split hst]
    exact drive c hcL hst (Or.inr (Or.inl rfl))
  | overflow =>
    rw [driveChunk_run_ovf hst]
    obtain ⟨hxL, hxs, hlr⟩ := hC.covf c hcL hst
    exact drive _ hxL hxs (by
      rcases hlr with h | h
      · exact Or.inl h.symm
      · exact Or.inr (Or.inr h.symm))
  | quiet =>
    rw [driveChunk_run_quiet hst]
    exact ⟨t, rfl, hW⟩
  | dead => exact absurd hst hcnd

/-! ### The background work -/

/-- **The background work of an insertion keeps the stored-value bound** (the context of
`background_ok`). -/
theorem background_wb {TI : Core → Prop} {μ : Core → Nat} {J k n R NB0 : Nat} {cap : Params → Nat}
    {L : List Nat} {s0 s1 s2 : Core} {y g c : Nat} (hTC : TopContract TI μ J cap) (hT : TopWB K
      TI μ)
    (hPost : InsPost TI k J n R μ L s0 g c s2) (hy : y ∈ L) (heg1 : eG s1 y = g)
    (hgc1 : gC s1 g = c) (hchunk : (chunkSize c true).run s1 = .ok () s2)
    (hE12 : s2.E = s1.E) (hP1 : s1.P = s0.P) (hkP : s0.P.reservationBudget = k) (hn : 1 ≤ n)
    (hsize : 2 + 2 * (s2.count / (s0.P.theta + 1 - cmax s0.P)) ≤ n + 1)
    (hcap : 2 + 2 * (s2.count / (s0.P.theta + 1 - cmax s0.P)) ≤ cap s0.P)
    (hI5 : (s0.P.theta : ℝ) + R * (Hn (n - 1) + 1) ≤ s0.P.T)
    (hW2 : WB K s2) (hL : LabRoom K s0.P) (hlen : 4 * L.length + 4 ≤ 2 ^ K)
    (hG2 : s2.Gs.size + 2 ≤ 2 ^ K) (hcnt : 2 * s2.count + 2 ≤ 2 ^ K)
    (hNB : s2.nodes.size + μ s2 ≤ NB0 + J * s2.C.size) (hNK : NB0 + J * (2 + 2 * s2.count) + 2 ≤
      2 ^ K) :
    ∃ s', (background y).run s1 = .ok () s' ∧ WB K s' := by
  obtain ⟨A, hI, hel⟩ := hPost.inv
  obtain ⟨gh, hG⟩ := hPost.ginv
  obtain ⟨s₀, hC, hLX⟩ := hPost.cinv
  obtain ⟨e, pops, hN⟩ := hPost.cnt
  obtain ⟨⟨lg, hLi⟩, hLP, hGP⟩ := hLX
  have hP2 : s2.P = s0.P := hPost.P
  obtain ⟨hgL, hgc, hpos⟩ := hPost.grp
  have heg2 : eG s2 y = g := by simp only [eG, hE12]; exact heg1
  subst hel
  -- the group phase, with the stored-value bound added to its hooks
  have hXg := ((((xgroup_cinv (L := A.elist) (δ := δ1 c) (δu := fun _ => 0) (s₀ := s₀) (c := c)
    (by
      unfold δ1
      simp)).and (xgroup_linv (L := A.elist) (s₀ := s₀) (δ := δ1 c)
      (δu := fun _ => 0) (c := c))).and (xgroup_frame (L := A.elist) (c := c) s2)).and
    (xgroup_track (L := A.elist) (c' := c) y c hy)).and
    (xgroup_wb (K := K) (P := s0.P) (G0 := s2.Gs.size) (L := A.elist) (c := c) hL hG2 (by omega))
  have hroom : gSt s2 g = .quiet → s2.P.G ≤ gSz s2 g → SplitRoom s2 g := by
    intro hq hge
    have hq0 := (hG.quiet g hgL hq).1
    unfold δ1 at hq0; rw [ite_eq_left rfl] at hq0
    have hcl : LiveC s2 (gC s2 g) := by rw [hgc]; exact hPost.cL
    have hδ1 : ∀ x, LiveC s2 x → cSt s2 x = .splitting →
        δ1 c (cLl s2 x) + δ1 c x + δ1 c (cRr s2 x) ≤ 1 := by
      intro x hx hxs
      have Fx := hC.cfam x hx hxs
      have h1 := Fx.lx hI hx; have h2 := Fx.rx hI hx; have h3 := Fx.lr hI hx
      unfold δ1; split_ifs <;> simp_all
    have hnd : cSt s2 c ≠ .dead := by rw [← hgc]; exact (hC.gchk g hgL).2
    obtain ⟨harr, hins⟩ := chunk_budget hC hLi hPost.cp hPost.cL hnd hδ1 hPost.quiet
    rw [← hgc] at harr hins
    exact split_room hI hLi hLP hGP hgL hq (by omega) hcl harr hins
  have hX0 : ((((CInv s2 A.elist (δ1 c) (fun _ => 0) s₀ ∧ LX s₀ (δ1 c) (fun _ => 0) s2) ∧
      CFrame s2 s2) ∧ gC s2 (eG s2 y) = c) ∧ XG K s0.P s2.Gs.size s2) :=
    ⟨⟨⟨⟨hC, ⟨lg, hLi⟩, hLP, hGP⟩, CFrame.refl s2⟩, by rw [heg2, hgc]⟩,
      hW2, hP2, by omega, Or.inl le_rfl⟩
  obtain ⟨s3, hgp, hDD⟩ := groupPhase_ok hI (by
    rw [hgc]
    exact hXg) hX0 hG hGP hgL hpos hroom
  -- the state after the group phase
  obtain ⟨A3, hI3, hel3⟩ := hDD.inv
  obtain ⟨gh3, hG3⟩ := hDD.ginv
  have hP3 : s3.P = s2.P := hDD.P
  obtain ⟨δu', hC3, hLX3, hCF, htr, hW3⟩ : ∃ δu' : Nat → Nat, CInv s3 A.elist (δ1 c) δu' s₀ ∧
      LX s₀ (δ1 c) δu' s3 ∧ CFrame s2 s3 ∧ gC s3 (eG s3 y) = c ∧ WB K s3 := by
    rcases hDD.x with ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ | ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
    · exact ⟨_, h1, h2, h3, h4, h5.1⟩
    · exact ⟨_, h1, h2, h3, h4, h5.1⟩
  have hQS := hCF.qsame
  have hcL3 : LiveC s3 c := by simp only [LiveC, hCF.Csize]; exact hPost.cL
  have hcnd3 : cSt s3 c ≠ .dead := by
    rw [(hCF.C c).2.1, ← hgc]; exact (hC.gchk g hgL).2
  have hcsz3 : 1 ≤ cSz s3 c := by rw [(hCF.C c).1]; exact hPost.csz
  -- the chunk phase
  obtain ⟨t4, hdc, hCP4⟩ := driveChunk_ok hI3 hel3 hG3 (hel3 ▸ hC3) hLX3
    (hN.frame hQS hCF.count) (by
      rw [hP3]
      exact hGP) (by
      rw [hP3]
      exact hPost.cp) hcL3 hcnd3
    hcsz3
  obtain ⟨t4', hdc', hW4⟩ := driveChunk_wb hI3 hel3 hG3 (hel3 ▸ hC3) hLX3 (by
    rw [hP3]
    exact hGP)
    (by
      rw [hP3]
      exact hPost.cp) hcL3 hcnd3 hcsz3 hW3 (by
      rw [hP3, hP2]
      exact hL) (by omega)
  rw [hdc] at hdc'
  obtain ⟨-, rfl⟩ := EStateM.Result.ok.inj hdc'
  have hD : DFrame s2 t4 := hCF.dframe.trans hCP4.fr
  -- the reservation
  obtain ⟨yg, ig, ag, ipg, jsg, hGm, hRA⟩ := hPost.game
  have hk2 : s1.P.reservationBudget = k := by rw [hP1]; exact hkP
  have hP4 : t4.P = s0.P := hD.P.trans hP2
  have h0 : ResInv TI k J n R μ A.elist t4 0 t4 := by
    refine ⟨⟨hCP4.inv, hCP4.ginv, ⟨s₀, hCP4.cinv, hCP4.lx⟩, hPost.pq.dframe hD, hCP4.cnt,
      by rw [hP4, ← hP2]; exact hPost.cp⟩, hTC.frame _ _ hD.topSame hPost.ti, rfl, rfl,
      yg, ig, ag, ipg, jsg, hGm.mono (fun j => le_of_eq (by rw [hD.gvec])), ?_⟩
    rw [hD.top.2.2.2.2.1, hTC.mframe _ _ hD.topSame]; exact hRA
  obtain ⟨s', hres, hW'⟩ := reservation_wb hTC hT h0 hn
    (by
      rw [hD.count, hP4]
      exact hsize) (by
      rw [hD.count, hP4]
      exact hcap)
    (by
      rw [hP4]
      exact hI5) hW4 (by
      rw [hD.count]
      exact hcnt)
    (by
      rw [hD.topSame.top.1, hD.topSame.Csize, hTC.mframe _ _ hD.topSame]
      exact hNB)
    (by
      rw [hD.count]
      exact hNK)
  refine ⟨s', ?_, hW'⟩
  -- the run of `background`
  unfold background
  rw [run_getP_bind, run_getE_bind, run_getG_bind]
  have e1 : (s1.Gs.getX (s1.E.getX y).grp).chk = c := by
    change gC s1 (eG s1 y) = c; rw [heg1, hgc1]
  rw [e1, run_bind, hchunk]
  dsimp only
  rw [run_getE_bind, run_getG_bind]
  have e2 : (s2.E.getX y).grp = g := heg2
  rw [e2, hk2]
  have hPG : s1.P.G = s2.P.G := by rw [hP1, hP2]
  rw [hPG]
  by_cases hcond : ((s2.Gs.getX g).st == St.quiet && decide ((s2.Gs.getX g).size ≥ s2.P.G)) = true
  · rw [ite_eq_left hcond]
    rw [ite_eq_left hcond] at hgp
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
    obtain ⟨labL, labR, hLb, hLa⟩ := hroom hcond.1 hcond.2
    have hsg := startGroupSplit_ok hgL hLb hLa
    rw [run_bind, hsg] at hgp
    rw [run_bind, hsg]
    dsimp only at hgp ⊢
    have hEu : (splitState s2 g labL labR).E = s2.E :=
      (splitSpec hI (hI.mem_glist_iff.mpr hgL) labL labR).E
    exact bg_rest_run (by
      simp only [eG, hEu]
      exact heg2) hgp htr hdc hres
  · rw [ite_eq_right hcond]
    rw [ite_eq_right hcond] at hgp
    exact bg_rest_run heg2 hgp htr hdc hres

/-! ### A core insertion -/

/-- The element list has at most `E.size - 1` entries (indices `1 … E.size - 1`). -/
theorem _root_.OrderMaintenance.Proof.INV.len_lt {s : Core} {A : Abs} (hI : INV s A) :
  A.elist.length + 1 ≤ max 1 s.E.size := by
  have h := (hI.eList.nodup.subperm (l₂ := List.range' 1 (s.E.size - 1))
    (fun e he => List.mem_range'_1.mpr (by
      have := (hI.eAlloc e).mp he
      omega))).length_le
  simp only [List.length_range'] at h
  omega

/-- **A core insertion keeps the stored-value bound** (the context of `insertAfter_cost`), given
the top structure's contract `TopWB`, room for labels, and room for the sizes and record counts:
`4·E.size + 8`, `Gs.size + 2` and `2·count + 4` at most `2^K`. -/
theorem insertAfter_wb {TI : Core → Prop} {μ : Core → Nat} {J n R NB0 : Nat} {cap : Params → Nat}
    {L : List Nat} {s : Core} {x : Nat} (hTC : TopContract TI μ J cap) (hT : TopWB K TI μ)
    (hC : CostInv TI μ J n R L s)
    (hx : x ∈ L) (hk : 1 ≤ s.P.reservationBudget) (hR : J / s.P.reservationBudget + 1 ≤ R) (hn
      : 1 ≤ n)
    (hsize : 2 + 2 * ((s.count + 1) / (s.P.theta + 1 - cmax s.P)) ≤ n + 1)
    (hcap : 2 + 2 * ((s.count + 1) / (s.P.theta + 1 - cmax s.P)) ≤ cap s.P)
    (hI5 : (s.P.theta : ℝ) + R * (Hn (n - 1) + 1) ≤ s.P.T) (hh : Nat)
    (hW : WB K s) (hL : LabRoom K s.P) (hE : 4 * s.E.size + 8 ≤ 2 ^ K)
    (hG : s.Gs.size + 2 ≤ 2 ^ K) (hcnt : 2 * s.count + 4 ≤ 2 ^ K)
    (hNB : s.nodes.size + μ s ≤ NB0 + J * s.C.size)
    (hNK : NB0 + J * (2 + 2 * (s.count + 1)) + 2 ≤ 2 ^ K) :
    ∃ s', (insertAfter x hh).run s = .ok s.E.size s' ∧ WB K s' := by
  obtain ⟨y, i, a, ip, js, hGm, hRO⟩ := hC.game
  have hdiv : s.count / (s.P.theta + 1 - cmax s.P) ≤ (s.count + 1) / (s.P.theta + 1 - cmax s.P) :=
    Nat.div_le_div_right (Nat.le_succ s.count)
  have hcnt0 : 2 + 2 * (s.count / (s.P.theta + 1 - cmax s.P)) ≤ n + 1 := by omega
  obtain ⟨s1, s2, hrun1, hrun2, hPost, heG, hgC, hE12, hP1⟩ := insert_step hTC hC.low hC.ti hGm
    hRO hx
    hk hR hn hcnt0 hI5 hh
  have hyL : s.E.size ∈ OrderMaintenance.Spec.insertAfterL x s.E.size L :=
    (OrderMaintenance.Spec.mem_insertAfterL hx).mpr (Or.inl rfl)
  -- the element insertion
  obtain ⟨A, hI, hel⟩ := hC.low.inv
  obtain ⟨gh, hG0⟩ := hC.low.ginv
  obtain ⟨s₀, hCI, -⟩ := hC.low.cinv
  subst hel
  have hlen := hI.len_lt
  have hxE : x < s.E.size := ((hI.eAlloc x).mp hx).2
  have hgL : LiveG s (eG s x) := hI.mem_glist_iff.mp (hI.eG_mem hx)
  have hgsz : gSz s (eG s x) ≤ A.elist.length := by rw [hG0.sz _ hgL]; exact runOf_len_le _ _ _
  obtain ⟨-, hW1, lab, rfl⟩ := insertElem_wb hW hL hrun1 (by omega) (by omega)
    (show gSz s (eG s x) + 1 < 2 ^ K by omega) (by omega)
  -- the chunk size
  have hcL : LiveC s (gC s (eG s x)) := (hCI.gchk _ hgL).1
  have hcsz : cSz s (gC s (eG s x)) ≤ A.elist.length := by
    rw [hCI.csz _ hcL]; exact celts_len_le _ _ _
  have hrun2' : (chunkSize (gC s (eG s x)) true).run (linkElem s x s.E.size lab hh) = .ok () s2
    := by
    rw [← hgC, ← heG]; exact hrun2
  have hW2 : WB K s2 := by
    have := wb_chunkSize hW1 (c := gC s (eG s x)) (inc := true) (hW.gChk _)
      (fun _ => show cSz s (gC s (eG s x)) + 1 < 2 ^ K by omega)
    rw [hrun2'] at this; exact this
  have hS12 : Same (linkElem s x s.E.size lab hh) s2 := by
    have := pres_chunkSize (gC s (eG s x)) true (linkElem s x s.E.size lab hh); rw [hrun2'] at this
    exact this
  have hGs2 : s2.Gs.size = s.Gs.size := by rw [hS12.1.Gsize]; simp [linkElem]
  have hEs2 : s2.E.size = s.E.size + 1 := by rw [hE12]; simp [linkElem]
  obtain ⟨A2, hI2, hel2⟩ := hPost.inv
  have hlen2 := hI2.len_lt
  rw [hel2] at hlen2
  have hTS : TopSame s s2 := (ts_linkElem s x s.E.size lab hh).trans (by
    have := ts_chunkSize (gC s (eG s x)) true (linkElem s x s.E.size lab hh)
    rw [hrun2'] at this; exact this)
  obtain ⟨s', hbg, hW'⟩ := background_wb hTC hT hPost hyL heG hgC hrun2' hE12 hP1 rfl hn
    (by
      rw [hPost.count]
      exact hsize) (by
      rw [hPost.count]
      exact hcap) hI5 hW2 hL
    (by omega) (by omega) (by
      rw [hPost.count]
      omega)
    (by
      rw [hTS.top.1, hTS.Csize, hTC.mframe _ _ hTS]
      exact hNB) (by
      rw [hPost.count]
      exact hNK)
  refine ⟨s', ?_, hW'⟩
  unfold insertAfter
  rw [run_bind, run_onGuard_ok hrun1]
  dsimp only
  rw [run_bind, run_onGuard_ok hbg]
  rfl

/-- **A deletion keeps the stored-value bound.** -/
theorem markDead_wb {s : Core} (hW : WB K s) (x : Nat) {s' : Core} (h : (markDead x).run s = .ok
  () s') :
    WB K s' := ((ht_markDead (P0 := s.P) x).ok hW rfl h).1.1

/-- **An order query** changes nothing. -/
theorem order_wb {s : Core} (x y : Nat) : ∃ b, (order x y).run s = .ok b s := order_cost s x y

end OrderMaintenance.Proof.Word
