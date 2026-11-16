/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Cost.Wrap


/-!
# The wrapper: what the machine code needs along Level F's run

The machine code of an operation calls core procedures; each call needs the core's cost
invariant and some facts about its arguments. Level F's cost proof establishes them along the
run, at intermediate states it does not expose. This file replays the proof of the rebuild loop
(`rebuildLoop_cost`) and records them (`RLSafeF`).
-/


@[expose] public section

namespace OrderMaintenance.Proof

open OrderMaintenance.Model OrderMaintenance.Zeroing
variable {mk : Nat → Params} {TI PI : Core → Prop} {μ : Core → Nat} {ν : Core → Nat}
  {PP : Params → Prop}
  {Jf capf nf Rf : Params → Nat}

/-- **What the iterations of the rebuild loop need**, along Level F's run: a preparation step needs
a core of positive capacity and keeps its count; a copy step reads an element of `cur`, and if the
element is live, `nxt` is in service with room, the anchor `tail` is in its list, and the handle is
below the counter. -/
def RLSafeF (mk : Nat → Params) (TI : Core → Prop) (μ : Core → Nat) (Jf nf Rf : Params → Nat)
    (om : OrderMaintenance) (n : Core) : Nat → Nat → Prop
  | 0, _ => True
  | f + 1, b => b ≠ 0 →
    (om.cursorSet = false → 1 ≤ n.P.N ∧ om.cur.head < om.cur.E.size ∧
      ∀ r n', prepareStep.run n = .ok r n' → n'.count = n.count ∧
        (r = true → RLSafeF mk TI μ Jf nf Rf
          { om with cursor := (om.cur.E.getX om.cur.head).next, cursorSet := true } n' f b) ∧
        (r = false → RLSafeF mk TI μ Jf nf Rf om n' f (b - 1))) ∧
    (om.cursorSet = true → om.cursor ≠ NIL → om.cursor < om.cur.E.size ∧
      ((om.cur.E.getX om.cursor).live = true → ∃ L, CoreOK mk TI μ Jf nf Rf n L ∧ n.count + 1 ≤
        n.P.N ∧
        n.tail ∈ L ∧ (om.cur.E.getX om.cursor).h < om.nextHandle) ∧
      ∀ om' n', copyAtCursor om n = .ok (om', n') → om'.cursor ≠ NIL →
        RLSafeF mk TI μ Jf nf Rf om' n' f (b - 1))

theorem elist_lt {c : Core} {A : Abs} (hR : CoreR c A) {e : Nat} (he : e ∈ A.elist) : e <
  c.E.size :=
  ((hR.inv.eAlloc e).mp he).2

/-- **The rebuild loop is safe**: under `rebuildLoop_cost`'s hypotheses, its iterations get what
they need. -/
theorem rebuildLoop_safe (S : CostSetup mk TI PI μ ν PP Jf capf nf Rf) {Sp :
  OrderMaintenance.Spec.State}
    (hS : OrderMaintenance.Spec.Inv Sp) {Φe live₀ I D N' : Nat} :
    ∀ fuel budget (om : OrderMaintenance) (n : Core) (A : Abs), CoreR om.cur A →
      liveH om.cur A.elist = Sp.list → IdxOK om.cur A om.curIdx Sp.list → NxtR' om.cur A om n →
      om.nextHandle = Sp.fresh → om.live = Sp.list.length →
      LoopC mk TI PI μ ν Jf nf Rf om n A budget Φe live₀ I D N' →
      RLSafeF mk TI μ Jf nf Rf om n fuel budget := by
  intro fuel
  induction fuel with
  | zero => intro budget om n A _ _ _ _ _ _ _; trivial
  | succ fuel ih =>
    intro budget om n A hR hL hI hN hf hlv hC hb
    have hnd : (liveH om.cur A.elist).Nodup := hL ▸ hS.1
    refine ⟨fun hf' => ?_, fun hset hc => ?_⟩
    · obtain ⟨hprep, hφ⟩ := hC.prep hf'
      obtain ⟨ready, n', hr, hN1, hN2⟩ := prepare_ok hN hR hf'
      obtain ⟨b, n2, hr2, hcnt2, hP2, hI2, hT2, hF2⟩ := hprep.step S
      rw [hr] at hr2
      injection hr2 with hr2
      injection hr2 with h1 h2
      subst h1; subst h2
      refine ⟨by rw [hC.nP, S.PN]; have := hC.room; omega, elist_lt hR hR.head, fun r n3 hr3 => ?_⟩
      have hr3' : runCore n prepareStep = .ok (r, n3) := runCore_ok hr3
      rw [hr] at hr3'
      injection hr3' with hr3'
      injection hr3' with h1 h2
      subst h1; subst h2
      refine ⟨hcnt2, fun hrd => ?_, fun hrd => ?_⟩
      · subst hrd
        have hok := hT2 rfl
        set om1 : OrderMaintenance := {
          om with
          cursor := (om.cur.E.getX om.cur.head).next
          cursorSet := true } with hom1
        have hcnt : om.cur.count = A.elist.length := by
          have := hC.curok.cnt; exact this
        have hpost1 : (postOf A.elist om1.cursor).length + 1 = A.elist.length := by
          change (postOf A.elist (eN om.cur om.cur.head)).length + 1 = _
          rw [hR.inv.eList.next _ hR.head, hR.inv.eList.head,
            postOf_succOf hR.inv.eList.nodup hR.inv.eList.nonil
              (by rw [← hR.inv.eList.head]; exact hR.head), postOf_headD hR.ne, List.length_tail]
          have := List.length_pos_of_ne_nil hR.ne; omega
        have hC1 : LoopC mk TI PI μ ν Jf nf Rf om1 n' A budget Φe live₀ I D N' := by
          refine ⟨hC.curok, by rw [hP2]; exact hC.nP, fun h => by simp [hom1] at h, fun _ =>
            ⟨fun B' hB' => ?_, ?_⟩, hC.room, hC.live, hC.bud⟩
          · rw [INV.elist_unique hB' hI2]
            refine ⟨hok, ?_⟩
            rw [hcnt2, hprep.cnt]; omega
          · change (postOf A.elist om1.cursor).length + (om.KB - budget) ≤ Φe
            omega
        exact ih budget om1 n' A hR hL hI (hN2 rfl) hf hlv hC1
      · subst hrd
        obtain ⟨hprep', hν⟩ := hF2 rfl
        have hC1 : LoopC mk TI PI μ ν Jf nf Rf om n' A (budget - 1) Φe live₀ I D N' := by
          refine ⟨hC.curok, by rw [hP2]; exact hC.nP, fun _ => ⟨hprep', ?_⟩,
            fun h => absurd h (by simp [hf']), hC.room, hC.live, by have := hC.bud; omega⟩
          have := hC.bud; omega
        exact ih (budget - 1) om n' A hR hL hI hN1 hf hlv hC1
    · obtain ⟨hserve, hpost⟩ := hC.serve hset
      have hN0 := hN
      obtain ⟨B, hRB, hIB, hzB, hcs⟩ := hN0
      rw [ite_eq_left hset] at hcs
      obtain ⟨pre, post, hsplit, hcpost, hpre, hLB⟩ := hcs
      have hfill := (hserve B hRB.inv).2
      have hcurA : om.cursor ∈ A.elist := by
        rw [hsplit, hcpost]
        cases post with
        | nil => exact absurd hcpost hc
        | cons a t => simp
      have hlB := nxtR'_live_le hN hL hset hRB.inv
      have hlive := hC.live
      have hroom : n.count + 1 ≤ n.P.N := by
        rw [hC.nP, S.PN]; have := hC.room; omega
      refine ⟨elist_lt hR hcurA, fun hl => ?_, fun om3 n3 hcp3 hc3 => ?_⟩
      · refine ⟨B.elist, (hserve B hRB.inv).1, hroom, ?_, ?_⟩
        · rw [hRB.inv.tail]
          obtain ⟨b, bt, hb⟩ := List.exists_cons_of_ne_nil hRB.ne
          rw [hb]; exact getLastD_cons_mem _ _ _
        · have hmem : hdl om.cur om.cursor ∈ Sp.list := by
            rw [← hL]; exact FM_mem_of _ _ hcurA hl
          have := hS.2 _ hmem
          rw [hf]; exact this
      · obtain ⟨om', n', hcp, e1, e2, e3, e4, e5, e6, e7, hN'⟩ := copy_ok hN hR hnd hset hc
        obtain ⟨om2, n2, B2, hcp2, hcur2, hRB2, hok2, hfill2, hP2⟩ :=
          copy_cost S hRB (hserve B hRB.inv).1 hfill hroom
        rw [hcp] at hcp2
        injection hcp2 with hcp2
        injection hcp2 with h1 h2
        subst h1; subst h2
        rw [hcp] at hcp3
        injection hcp3 with hcp3
        injection hcp3 with h1 h2
        subst h1; subst h2
        have hC' : LoopC mk TI PI μ ν Jf nf Rf om' n' A (budget - 1) Φe live₀ I D N' := by
          refine ⟨by rw [e1]; exact hC.curok, by rw [hP2]; exact hC.nP, fun h => absurd (e4 ▸ h)
            (by simp [hset]), fun _ => ⟨fun B' hB' => ?_, ?_⟩, hC.room, by rw [e6]; exact hC.live,
            by rw [e7]; have := hC.bud; omega⟩
          · rw [INV.elist_unique hB' hRB2.inv]; exact ⟨hok2, hfill2⟩
          · have hpo : postOf A.elist om.cursor = post := by
              rw [hsplit]
              exact (split_unique (hsplit ▸ hR.inv.eList.nodup) (hsplit ▸ hR.inv.eList.nonil)
                hcpost).2
            have hpne : post ≠ [] := by intro h; rw [h] at hcpost; exact hc hcpost
            have hpost' : (postOf A.elist om'.cursor).length + 1 = (postOf A.elist
              om.cursor).length := by
              rw [hcur2, hR.inv.eList.next _ hcurA,
                postOf_succOf hR.inv.eList.nodup hR.inv.eList.nonil hcurA,
                hpo, List.length_tail]
              have := List.length_pos_of_ne_nil hpne; omega
            rw [e7]; have := hC.bud; omega
        exact ih (budget - 1) om' n' A (e1 ▸ hR) (e1 ▸ hL) (e1 ▸ e2 ▸ hI) (e1 ▸ hN') (e5 ▸ hf)
          (by rw [e6]; exact hlv) hC'

/-- **The rebuild step's loop is safe**, under `rebuildStep_cost`'s hypotheses. -/
theorem rebuildStep_safe (S : CostSetup mk TI PI μ ν PP Jf capf nf Rf) {om : OrderMaintenance}
  {Sp : OrderMaintenance.Spec.State}
    (hW : WInv om Sp) (hlv : om.live = Sp.list.length)
    (hcur : ∀ A, INV om.cur A → CoreOK mk TI μ Jf nf Rf om.cur A.elist)
    (hbusy : ∀ n, om.nxt = some n → ∃ c₀ live₀ I D, MidW mk TI PI μ ν Jf nf Rf om n c₀ live₀ I D) :
    ∀ n0, om.nxt = some n0 → RLSafeF mk TI μ Jf nf Rf { om with nxt := none } n0 (om.KB + 1)
      om.KB := by
  intro n0 hn
  have hW0 := hW
  obtain ⟨hS, hf, A, hR, hL, hI, hN⟩ := hW0
  have hok := hcur A hR.inv
  unfold NxtR at hN
  rw [hn] at hN
  obtain ⟨c₀, live₀, I, D, hM⟩ := hbusy n0 hn
  set Φe := if om.cursorSet then (postOf A.elist om.cursor).length else ν n0 + om.cur.count
    with hΦe
  have hroom : 1 + live₀ + I + 1 ≤
      4 * max (live₀ + ((c₀ + (om.cur.P.L + 2)) / (om.KB - 1) + 1)) 16 := by
    have := hM.Iq
    have : live₀ + ((c₀ + (om.cur.P.L + 2)) / (om.KB - 1) + 1) ≤
        max (live₀ + ((c₀ + (om.cur.P.L + 2)) / (om.KB - 1) + 1)) 16 := le_max_left _ _
    omega
  have hC0 : LoopC mk TI PI μ ν Jf nf Rf { om with nxt := none } n0 A om.KB Φe live₀ I D
      (4 * max (live₀ + ((c₀ + (om.cur.P.L + 2)) / (om.KB - 1) + 1)) 16) := by
    refine ⟨hok, hM.nP, fun hs => ⟨(hM.prep hs).1, ?_⟩, fun hs => ⟨(hM.serve hs).1, ?_⟩, hroom,
      hM.live, le_rfl⟩
    · change ν n0 + om.cur.count + (om.KB - om.KB) ≤ Φe
      simp only [hΦe, show om.cursorSet = false from hs, Bool.false_eq_true, ite_false]; omega
    · change (postOf A.elist om.cursor).length + (om.KB - om.KB) ≤ Φe
      simp only [hΦe, show om.cursorSet = true from hs, ite_true]; omega
  exact rebuildLoop_safe S hS (om.KB + 1) om.KB { om with nxt := none } n0 A hR hL hI hN hf hlv hC0

/-- The anchor of an insertion in `cur`. -/
def insXi (om : OrderMaintenance) (hx : Option Nat) : Nat :=
  match hx with
  | none => om.cur.head
  | some x => om.curIdx.getX x

/-- **An insertion's rebuild step is safe**: after the insertion into `cur` and its mirroring, the
rebuild loop gets what it needs. -/
theorem insert_safe (S : CostSetup mk TI PI μ ν PP Jf capf nf Rf) {om : OrderMaintenance} {Sp :
  OrderMaintenance.Spec.State}
    (hW : WC mk TI PI μ ν Jf nf Rf om Sp) (hx : Option Nat) (hv : (insOp hx).Valid Sp) :
    ∃ c' om2, (insertAfter (insXi om hx) om.nextHandle).run om.cur = .ok om.cur.E.size c' ∧
      ({
        om with
        cur := c'
        nextHandle := om.nextHandle + 1
        curIdx := om.curIdx.setX om.nextHandle om.cur.E.size
      } : OrderMaintenance).mirrorInsert hx om.nextHandle = .ok om2 ∧
      ∀ n, om2.nxt = some n →
        RLSafeF mk TI μ Jf nf Rf { om2 with live := om2.live + 1, nxt := none } n (om2.KB + 1)
          om2.KB := by
  obtain ⟨hS, hf, A, hR, hL, hI, hN⟩ := hW.w
  have hnd : (liveH om.cur A.elist).Nodup := hL ▸ hS.1
  have hfresh : om.nextHandle ∉ liveH om.cur A.elist := by
    rw [hL, hf]; exact fun h => Nat.lt_irrefl _ (hS.2 _ h)
  obtain ⟨xi, hxi, hxeq, hxn, hxs⟩ := insertion_position hR hI hx hv
  have hok := hW.cur A hR.inv
  obtain ⟨c', A', hr, hR', hA', hrec, hly, hhy, hyA, hy0, hhead, hPc⟩ :=
    core_insert hR hxi om.nextHandle
  obtain ⟨c2, hr2, -, hok', hcnt', hP2⟩ := hok.insert S hxi (hW.cur_room S) om.nextHandle
  rw [hr] at hr2; cases hr2
  obtain ⟨om2, hm, e1, e2, e3, e4, e5, hN2⟩ := mirrorInsert_ok (om := { om with
      cur := c'
      nextHandle := om.nextHandle + 1
      curIdx := om.curIdx.setX om.nextHandle om.cur.E.size })
    (c' := c') hN hR hnd hxi hxn hxs hA' hyA hrec hly hhy hfresh
  -- Invariant R after the insertion (as in `insert_ok`)
  have hL' : liveH c' A'.elist = (OrderMaintenance.Spec.step Sp (insOp hx)).1.list := by
    rw [hA']
    exact inserted_live_handles hR hf hL hnd hxi hxn hxs hrec hly hhy hyA
  have hW3 : WInv { om2 with live := om2.live + 1 }
      (OrderMaintenance.Spec.step Sp (insOp hx)).1 :=
    WInv.insert_after_mirror hS hf hI hv hR' hL' hA' hxi hrec hly hhy e1 e2 e3 hN2
  -- the cost side of the mirroring
  have hm2 : ∀ om', ({
    om with
    cur := c'
    nextHandle := om.nextHandle + 1
    curIdx := om.curIdx.setX om.nextHandle om.cur.E.size
  } : OrderMaintenance).mirrorInsert hx
      om.nextHandle = .ok om' → om' = om2 := by
    intro om' h; rw [hm] at h; injection h with h; exact h.symm
  have hcnt1 : c'.count = om.cur.count + 1 := hcnt'
  have hPc' : c'.P = om.cur.P := hP2
  have hlv3 : om2.live + 1 = (OrderMaintenance.Spec.step Sp (insOp hx)).1.list.length := by
    rw [e4, step_ins_length Sp hx hv, hW.live]
  have hcur3 : ∀ A'', INV om2.cur A'' → CoreOK mk TI μ Jf nf Rf om2.cur A''.elist := by
    intro A'' hA''; rw [e1] at hA'' ⊢
    rw [INV.elist_unique hA'' hR'.inv, hA']; exact hok'
  have hmi_none : om.nxt = none → om2.nxt = none := by
    intro hn
    have : ({
      om with
      cur := c'
      nextHandle := om.nextHandle + 1
      curIdx := om.curIdx.setX om.nextHandle om.cur.E.size
    } : OrderMaintenance).mirrorInsert hx om.nextHandle = .ok {
      om with
      cur := c'
      nextHandle := om.nextHandle + 1
      curIdx := om.curIdx.setX om.nextHandle om.cur.E.size
    } := by
      unfold OrderMaintenance.mirrorInsert; simp only [hn]; rfl
    rw [← hm2 _ this]; exact hn
  have hxi' : xi = insXi om hx := by cases hx <;> exact hxeq
  refine ⟨c', om2, by rw [← hxi']; exact hr, hm, ?_⟩
  cases hn : om.nxt with
  | none =>
    exact rebuildStep_safe S hW3 hlv3 hcur3
      (fun n' hn' => by
        exfalso; have := hmi_none hn; simp only at hn'; rw [this] at hn'; cases hn')
  | some n =>
    obtain ⟨c₀, live₀, I, D, hRW⟩ := hW.busy n hn
    have hpostins : ∀ c, c ≠ om.cur.E.size →
        (postOf A'.elist c).length ≤ (postOf A.elist c).length + 1 := by
      intro c hc; rw [hA']; exact postOf_insertAfterL_le (Ne.symm hc) _
    unfold NxtR at hN; rw [hn] at hN
    obtain ⟨B, hRB, hIB, hzB, hcs⟩ := hN
    cases hs : om.cursorSet with
    | false =>
      have hmi : ({
        om with
        cur := c'
        nextHandle := om.nextHandle + 1
        curIdx := om.curIdx.setX om.nextHandle om.cur.E.size
      } : OrderMaintenance).mirrorInsert hx om.nextHandle = .ok {
          om with
          cur := c'
          nextHandle := om.nextHandle + 1
          curIdx := om.curIdx.setX om.nextHandle om.cur.E.size
        } := by
        unfold OrderMaintenance.mirrorInsert; simp only [hn, hs, Bool.false_and,
          Bool.false_eq_true, ite_false]; rfl
      have h2 := hm2 _ hmi
      subst h2
      refine rebuildStep_safe S hW3 hlv3 hcur3
        (fun n' hn' => by
          simp only [hn, Option.some.injEq] at hn'
          subst hn'
          refine ⟨c₀, live₀, I + 1, D, ?_⟩
          exact hRW.insert_mid hW.kb hR.inv
            hPc' hcnt1 rfl rfl rfl rfl (fun _ => rfl)
            (by intro h; rw [hs] at h; cases h))
    | true =>
      obtain ⟨hserve, -⟩ := hRW.serve hs
      obtain ⟨hok0, hfill0⟩ := hserve B hRB.inv
      have hroom := hW.nxt_room S hn hs
      rw [ite_eq_left hs] at hcs
      obtain ⟨pre, post, hsplit, hcpost, -, -⟩ := hcs
      obtain ⟨om2', hmi, f1, f2, f3, f4, f5, n', B', hn2, hRB', hok', hfill', hP'⟩ :=
        mirrorInsert_cost (om := {
          om with
          cur := c'
          nextHandle := om.nextHandle + 1
          curIdx := om.curIdx.setX om.nextHandle om.cur.E.size
        })
          (hx := hx) (hy := om.nextHandle) S hn hs hRB hok0 hfill0 hroom hIB hzB
      have h2 := hm2 _ hmi
      subst h2
      have g1 : om2'.cur = c' := f1
      have g2 : om2'.cursorSet = om.cursorSet := f2
      have g3 : om2'.cursor = om.cursor := f3
      have g4 : om2'.KB = om.KB := f4
      have g5 : om2'.live = om.live := f5
      have hcurNe : om.cursor ≠ om.cur.E.size := by
        intro e
        cases post with
        | nil =>
          simp only [List.headD_eq_head?_getD, List.head?_nil, Option.getD_none] at hcpost
          rw [hcpost] at e
          exact hy0 e.symm
        | cons a t =>
          simp only [List.headD_eq_head?_getD, List.head?_cons, Option.getD_some] at hcpost
          exact hyA (by rw [hsplit, ← e, hcpost]; simp)
      refine rebuildStep_safe S hW3 hlv3 hcur3
        (fun n'' hn'' => by
          simp only [hn2, Option.some.injEq] at hn''
          subst hn''
          refine ⟨c₀, live₀, I + 1, D, ?_⟩
          apply hRW.insert_mid (om' := { om2' with live := om2'.live + 1 }) hW.kb hR.inv
            (by change om2'.cur.P = om.cur.P; rw [g1, hPc'])
            (by change om2'.cur.count = _; rw [g1, hcnt1])
            (by change om2'.live + 1 = om.live + 1; rw [g5])
            g4 g2 hP' (by intro h; rw [hs] at h; cases h)
          intro _
          refine ⟨fun B'' hB'' => ?_, fun A'' hA'' => ?_⟩
          · rw [INV.elist_unique hB'' hRB'.inv]; exact ⟨hok', hfill'⟩
          · change INV om2'.cur A'' at hA''
            rw [g1] at hA''
            change (postOf A''.elist om2'.cursor).length ≤ _
            rw [g3, INV.elist_unique hA'' hR'.inv]
            exact hpostins om.cursor hcurNe)

/-- **A deletion's rebuild step is safe.** -/
theorem delete_safe (S : CostSetup mk TI PI μ ν PP Jf capf nf Rf) {om : OrderMaintenance} {Sp :
  OrderMaintenance.Spec.State}
    (hW : WC mk TI PI μ ν Jf nf Rf om Sp) {x : Nat} (hv : x ∈ Sp.list) :
    ∃ c' om2, (markDead (om.curIdx.getX x)).run om.cur = .ok () c' ∧
      ({
        om with
        cur := c'
        curIdx := om.curIdx.setX x 0
      } : OrderMaintenance).mirrorDelete x =
        .ok om2 ∧
      ∀ n, om2.nxt = some n →
        RLSafeF mk TI μ Jf nf Rf { om2 with live := om2.live - 1, nxt := none } n (om2.KB + 1)
          om2.KB := by
  obtain ⟨hS, hf, A, hR, hL, hI, hN⟩ := hW.w
  have hnd : (liveH om.cur A.elist).Nodup := hL ▸ hS.1
  obtain ⟨hxi, hlx, hhx⟩ := hI x hv
  obtain ⟨c', hr, hR', hL', hrec, hhdl, _, hdead⟩ := core_kill hR hxi hlx hnd
  have hok := hW.cur A hR.inv
  obtain ⟨c2, hr2, hok', hcnt', hP2⟩ := hok.markDead S (om.curIdx.getX x)
  rw [hr] at hr2; cases hr2
  obtain ⟨om2, hm, e1, e2, e3, e4, e5, hN2⟩ := mirrorDelete_ok (om := { om with
      cur := c'
      curIdx := om.curIdx.setX x 0 }) (c' := c') hN hR hnd hxi hlx hhx hrec hhdl hdead
  have hW3 : WInv { om2 with live := om2.live - 1 }
      (OrderMaintenance.Spec.step Sp (.delete x)).1 :=
    WInv.delete_after_mirror hS hf hI hv hR' (by rw [hL', hhx, hL]) hhx hrec hhdl
      e1 e2 e3 hN2
  have hm2 : ∀ om', ({
    om with
    cur := c'
    curIdx := om.curIdx.setX x 0
  } :
    OrderMaintenance).mirrorDelete x = .ok om' → om' = om2 := by
    intro om' h; rw [hm] at h; injection h with h; exact h.symm
  have hlen : 1 ≤ Sp.list.length := List.length_pos_of_mem hv
  have hlv3 : om2.live - 1 = (OrderMaintenance.Spec.step Sp (.delete x)).1.list.length := by
    rw [e4, hW.live]; change _ = (Sp.list.erase x).length; rw [List.length_erase_of_mem hv]
  have hcur3 : ∀ A'', INV om2.cur A'' → CoreOK mk TI μ Jf nf Rf om2.cur A''.elist := by
    intro A'' hA''; rw [e1] at hA'' ⊢; rw [INV.elist_unique hA'' hR'.inv]; exact hok'
  have hPc' : c'.P = om.cur.P := hP2
  refine ⟨c', om2, hr, hm, ?_⟩
  cases hn : om.nxt with
  | none =>
    have hmi : ({
      om with
      cur := c'
      curIdx := om.curIdx.setX x 0
    } :
      OrderMaintenance).mirrorDelete x = .ok {
        om with
        cur := c'
        curIdx := om.curIdx.setX x 0
      }
        := by
      unfold OrderMaintenance.mirrorDelete; simp only [hn]; rfl
    have h2 := hm2 _ hmi
    subst h2
    exact rebuildStep_safe S hW3 hlv3 hcur3
      (fun n' hn' => by simp only [hn] at hn'; cases hn')
  | some n =>
    obtain ⟨c₀, live₀, I, D, hRW⟩ := hW.busy n hn
    have hN0 := hN
    unfold NxtR at hN0; rw [hn] at hN0
    obtain ⟨B, hRB, hIB, hzB, hcs⟩ := hN0
    cases hs : om.cursorSet with
    | false =>
      rw [ite_eq_right (by simp [hs])] at hcs
      subst hcs
      have hx0 : om.nxtIdx.getX x = 0 := by
        by_contra h; have := hzB x h; rw [liveH_initAbs hRB] at this; simp at this
      have hmi : ({
        om with
        cur := c'
        curIdx := om.curIdx.setX x 0
      } :
        OrderMaintenance).mirrorDelete x = .ok {
          om with
          cur := c'
          curIdx := om.curIdx.setX x 0
        } := by
        unfold OrderMaintenance.mirrorDelete; simp only [hn, hx0, bne_self_eq_false,
          Bool.false_eq_true, ite_false]
        rfl
      have h2 := hm2 _ hmi
      subst h2
      refine rebuildStep_safe S hW3 hlv3 hcur3
        (fun n' hn' => by
          simp only [hn, Option.some.injEq] at hn'
          subst hn'
          refine ⟨c₀, live₀, I, D + 1, ?_⟩
          exact hRW.delete_mid hW.kb hR.inv (by rw [hW.live]; exact hlen)
            hPc' hcnt' rfl rfl rfl rfl (fun _ => rfl)
            (by intro h; rw [hs] at h; cases h))
    | true =>
      obtain ⟨hserve, -⟩ := hRW.serve hs
      obtain ⟨hok0, hfill0⟩ := hserve B hRB.inv
      rw [ite_eq_left hs] at hcs
      obtain ⟨pre, post, hsplit, hcpost, -, hLB⟩ := hcs
      have hndB : (liveH n B.elist).Nodup := by
        rw [hLB]; exact (FM_sub_nodup (hsplit ▸ hnd)).1
      obtain ⟨om2', hmi, f1, f2, f3, f4, f5, n', hn2, hRB', hok', hfill', hP'⟩ :=
        mirrorDelete_cost (om := {
          om with
          cur := c'
          curIdx := om.curIdx.setX x 0
        }) (x := x)
          S hn hRB hok0 hfill0 hIB hzB hndB
      have h2 := hm2 _ hmi
      subst h2
      have g1 : om2'.cur = c' := f1
      have g2 : om2'.cursorSet = om.cursorSet := f2
      have g3 : om2'.cursor = om.cursor := f3
      have g4 : om2'.KB = om.KB := f4
      have g5 : om2'.live = om.live := f5
      refine rebuildStep_safe S hW3 hlv3 hcur3
        (fun n'' hn'' => by
          simp only [hn2, Option.some.injEq] at hn''
          subst hn''
          refine ⟨c₀, live₀, I, D + 1, ?_⟩
          apply hRW.delete_mid (om' := { om2' with live := om2'.live - 1 }) hW.kb hR.inv
            (by rw [hW.live]; exact hlen)
            (by change om2'.cur.P = om.cur.P; rw [g1, hPc'])
            (by change om2'.cur.count = _; rw [g1, hcnt'])
            (by change om2'.live - 1 = om.live - 1; rw [g5])
            g4 g2 hP' (by intro h; rw [hs] at h; cases h)
          intro _
          refine ⟨fun B'' hB'' => ?_, fun A'' hA'' => ?_⟩
          · rw [INV.elist_unique hB'' hRB'.inv]; exact ⟨hok', hfill'⟩
          · change INV om2'.cur A'' at hA''
            rw [g1] at hA''
            change (postOf A''.elist om2'.cursor).length ≤ _
            rw [g3, INV.elist_unique hA'' hR'.inv])

end OrderMaintenance.Proof
