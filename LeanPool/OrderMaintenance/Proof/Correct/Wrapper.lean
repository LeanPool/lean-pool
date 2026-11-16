/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Correct.Handles


/-!
# The wrapper (Invariant R)

`cur` is a well-formed core whose live handles, in list order, are the specification's list,
and `curIdx` maps each of them to its element. A rebuild core `nxt` is either being prepared
(the sentinel alone) or holds exactly the live handles of the part `pre` of `cur`'s list
before the cursor, with `nxtIdx` mapping them; mirrored operations keep this.
-/


@[expose] public section

namespace OrderMaintenance.Proof

open OrderMaintenance.Model

theorem runCore_ok {α : Type} {c : Core} {act : CM α} {a : α} {s : Core} (h : act.run c = .ok a s) :
    runCore c act = .ok (a, s) := by
  unfold runCore; rw [h]

theorem onCur_ok {α : Type} {om : OrderMaintenance} {act : CM α} {a : α} {s : Core} (h : act.run
  om.cur = .ok a s) :
    om.onCur act = .ok (a, { om with cur := s }) := by
  unfold OrderMaintenance.onCur
  simp only [bind, Except.bind]
  rw [runCore_ok h]; rfl

/-! ### The invariant -/

/-- The rebuild core `n` relative to `cur = c` with nesting `A`. -/
def NxtR' (c : Core) (A : Abs) (om : OrderMaintenance) (n : Core) : Prop :=
  ∃ B, CoreR n B ∧ IdxOK n B om.nxtIdx (liveH n B.elist) ∧
    (∀ x, om.nxtIdx.getX x ≠ 0 → x ∈ liveH n B.elist) ∧
    (if om.cursorSet then ∃ pre post, A.elist = pre ++ post ∧ om.cursor = post.headD NIL ∧
        pre ≠ [] ∧ liveH n B.elist = liveH c pre
     else B = initAbs)

/-- Require the replacement-core invariant when an incremental rebuild is active. -/
def NxtR (c : Core) (A : Abs) (om : OrderMaintenance) : Prop :=
  match om.nxt with
  | none => True
  | some n => NxtR' c A om n

/-- **Invariant R.** -/
structure WInv (om : OrderMaintenance) (S : OrderMaintenance.Spec.State) : Prop where
  spec : OrderMaintenance.Spec.Inv S
  fresh : om.nextHandle = S.fresh
  core : ∃ A, CoreR om.cur A ∧ liveH om.cur A.elist = S.list ∧ IdxOK om.cur A om.curIdx S.list ∧
    NxtR om.cur A om

theorem liveH_initAbs {n : Core} (hR : CoreR n initAbs) : liveH n initAbs.elist = [] := by
  have hh := hR.head
  rw [initAbs_elist] at hh ⊢
  simp at hh
  simp [FM_cons, ← hh, hR.dead]

theorem FM_sub_nodup {p : Nat → Bool} {f : Nat → Nat} {pre post : List Nat}
    (h : (FM p f (pre ++ post)).Nodup) : (FM p f pre).Nodup ∧ (FM p f post).Nodup := by
  rw [FM_append] at h; exact ⟨(List.nodup_append.mp h).1, (List.nodup_append.mp h).2.1⟩

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
theorem liveH_append (c : Core) (l1 l2 : List Nat) : liveH c (l1 ++ l2) = liveH c l1 ++ liveH c
  l2 :=
  FM_append _ _ _ _

theorem liveH_insertAfterL (c : Core) {l : List Nat} {a b : Nat} (ha : a ∈ l) (hpa : live c a =
  true)
    (hnd : (liveH c l).Nodup) (hb : b ∉ l) (hpb : live c b = true) :
    liveH c (OrderMaintenance.Spec.insertAfterL a b l) = OrderMaintenance.Spec.insertAfterL (hdl
      c a) (hdl c b) (liveH c l) :=
  FM_insertAfterL _ _ ha hpa hnd hb hpb

theorem liveH_insertAfterL_head (c : Core) {a b : Nat} (t : List Nat) (hpa : live c a = false)
    (hpb : live c b = true) :
    liveH c (OrderMaintenance.Spec.insertAfterL a b (a :: t)) = hdl c b :: liveH c t :=
  FM_insertAfterL_head _ _ t hpa hpb

theorem headD_pre {pre post : List Nat} (hpre : pre ≠ []) : (pre ++ post).headD NIL ∈ pre := by
  cases pre with
  | nil => exact absurd rfl hpre
  | cons a t => simp

theorem nxtR_copied {c' : Core} {A' : Abs} {om : OrderMaintenance} {n n' : Core} {B B' : Abs}
  {hy y' : Nat}
    {pre post : List Nat} (hRB' : CoreR n' B') (hIB : IdxOK n B om.nxtIdx (liveH n B.elist))
    (hzB : ∀ x, om.nxtIdx.getX x ≠ 0 → x ∈ liveH n B.elist) (hsub : ∀ e ∈ B.elist, e ∈ B'.elist)
    (hy'B : y' ∈ B'.elist) (hrecB : ∀ e ∈ B.elist, live n' e = live n e ∧ hdl n' e = hdl n e)
    (hly' : live n' y' = true) (hhy' : hdl n' y' = hy) (hfreshB : hy ∉ liveH n B.elist)
    (hL : ∀ z, z ∈ liveH n' B'.elist ↔ z = hy ∨ z ∈ liveH n B.elist)
    (hset : om.cursorSet = true) (hsplit : A'.elist = pre ++ post) (hcur : om.cursor =
      post.headD NIL)
    (hpre : pre ≠ []) (hLB : liveH n' B'.elist = liveH c' pre) :
    NxtR' c' A' { om with nxt := some n', nxtIdx := om.nxtIdx.setX hy y' } n' := by
  refine ⟨B', hRB', fun z hz => ?_, fun z hz => ?_, ?_⟩
  · simp only [Array.getX_setX]
    rcases (hL z).mp hz with rfl | hz'
    · rw [ite_eq_left rfl]; exact ⟨hy'B, hly', hhy'⟩
    · have hzy : z ≠ hy := fun e => hfreshB (e ▸ hz')
      rw [ite_eq_right hzy]
      obtain ⟨h1, h2, h3⟩ := hIB z hz'
      exact ⟨hsub _ h1, by rw [(hrecB _ h1).1]; exact h2, by rw [(hrecB _ h1).2]; exact h3⟩
  · simp only [Array.getX_setX] at hz
    split at hz
    · exact (hL z).mpr (Or.inl ‹_›)
    · exact (hL z).mpr (Or.inr (hzB z hz))
  · change if om.cursorSet = true then _ else _
    rw [ite_eq_left hset]; exact ⟨pre, post, hsplit, hcur, hpre, hLB⟩

theorem mirrorInsert_ok {om : OrderMaintenance} {c c' : Core} {A A' : Abs} {hx : Option Nat} {xi
  y hy : Nat}
    (hN : NxtR c A om) (hR : CoreR c A) (hnd : (liveH c A.elist).Nodup)
    (hxi : xi ∈ A.elist) (hxn : hx = none → xi = c.head)
    (hxs : ∀ x, hx = some x → live c xi = true ∧ hdl c xi = x)
    (hA' : A'.elist = OrderMaintenance.Spec.insertAfterL xi y A.elist) (hyA : y ∉ A.elist)
    (hrec : ∀ e ∈ A.elist, live c' e = live c e ∧ hdl c' e = hdl c e)
    (hly : live c' y = true) (hhy : hdl c' y = hy) (hfresh : hy ∉ liveH c A.elist) :
    ∃ om2, om.mirrorInsert hx hy = .ok om2 ∧ om2.cur = om.cur ∧ om2.curIdx = om.curIdx ∧
      om2.nextHandle = om.nextHandle ∧ om2.live = om.live ∧ om2.KB = om.KB ∧ NxtR c' A' om2 := by
  unfold OrderMaintenance.mirrorInsert
  unfold NxtR at hN
  cases hn : om.nxt with
  | none => exact ⟨om, rfl, rfl, rfl, rfl, rfl, rfl, by unfold NxtR; rw [hn]; trivial⟩
  | some n =>
    rw [hn] at hN
    obtain ⟨B, hRB, hIB, hzB, hcs⟩ := hN
    by_cases hset : om.cursorSet = true
    swap
    · have hf : om.cursorSet = false := by simpa using hset
      simp only [hf, Bool.false_and, Bool.false_eq_true, ite_false]
      refine ⟨om, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
      unfold NxtR; rw [hn]
      exact ⟨B, hRB, hIB, hzB, by simp only [hf] at hcs ⊢; exact hcs⟩
    rw [ite_eq_left hset] at hcs
    obtain ⟨pre, post, hsplit, hcur, hpre, hLB⟩ := hcs
    have hndpre := (FM_sub_nodup (hsplit ▸ hnd)).1
    have hBnd : (liveH n B.elist).Nodup := hLB ▸ hndpre
    have hfreshB : hy ∉ liveH n B.elist := by
      rw [hLB]; intro h; apply hfresh; rw [hsplit, liveH_append]; exact List.mem_append_left _ h
    -- records of `c'` on `pre`
    have hrecpre : ∀ e ∈ pre, live c' e = live c e ∧ hdl c' e = hdl c e :=
      fun e he => hrec e (hsplit ▸ List.mem_append_left _ he)
    have hypre : y ∉ pre := fun h => hyA (hsplit ▸ List.mem_append_left _ h)
    have hfpre : liveH c' pre = liveH c pre := liveH_frame hrecpre
    -- the copied case, given the anchor `xn` in `nxt` and the new handle lists
    have copied : ∀ xn, xn ∈ B.elist → xi ∈ pre →
        (∀ (n' : Core) (B' : Abs), CoreR n' B' →
          B'.elist = OrderMaintenance.Spec.insertAfterL xn n.E.size B.elist →
          (∀ e ∈ B.elist, live n' e = live n e ∧ hdl n' e = hdl n e) →
          live n' n.E.size = true → hdl n' n.E.size = hy → n.E.size ∉ B.elist →
          liveH n' B'.elist = liveH c' (OrderMaintenance.Spec.insertAfterL xi y pre) ∧
          (∀ z, z ∈ liveH n' B'.elist ↔ z = hy ∨ z ∈ liveH n B.elist)) →
        ∃ y' n', runCore n (insertAfter xn hy) = .ok (y', n') ∧
          NxtR' c' A' { om with nxt := some n', nxtIdx := om.nxtIdx.setX hy y' } n' := by
      intro xn hxn hxpre hlists
      obtain ⟨n', B', hr', hRB', hB', hrecB, hlyB, hhyB, hyB, _, _, _⟩ := core_insert hRB hxn hy
      obtain ⟨hLB', hL⟩ := hlists n' B' hRB' hB' hrecB hlyB hhyB hyB
      refine ⟨_, n', runCore_ok hr', ?_⟩
      exact nxtR_copied (post := post) hRB' hIB hzB
        (fun e he => by rw [hB']; exact (OrderMaintenance.Spec.mem_insertAfterL hxn).mpr (Or.inr
          he))
        (by rw [hB']; exact (OrderMaintenance.Spec.mem_insertAfterL hxn).mpr (Or.inl rfl)) hrecB
          hlyB hhyB hfreshB hL
        hset (by rw [hA', hsplit, insertAfterL_append, ite_eq_left hxpre]) hcur
        (List.ne_nil_of_mem ((OrderMaintenance.Spec.mem_insertAfterL hxpre).mpr (Or.inl rfl))) hLB'
    cases hx with
    | none =>
      have hxi' := hxn rfl
      have hhp : c.head ∈ pre := by
        rw [hR.inv.eList.head, hsplit]; exact headD_pre hpre
      simp only [Bool.and_true]
      rw [ite_eq_left hset]
      obtain ⟨a, pt, rfl⟩ : ∃ a pt, pre = a :: pt := List.exists_cons_of_ne_nil hpre
      have ha : a = c.head := by rw [hR.inv.eList.head, hsplit]; rfl
      refine (copied n.head hRB.head (hxi' ▸ hhp) ?_).elim fun y' h => h.elim fun n' h => ?_
      swap
      · obtain ⟨hrc, hN'⟩ := h
        simp only [bind, Except.bind, hrc]
        exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, by unfold NxtR; exact hN'⟩
      intro n' B' hRB' hB' hrecB hlyB hhyB hyB
      obtain ⟨b, bt, hbt⟩ : ∃ b bt, B.elist = b :: bt := List.exists_cons_of_ne_nil hRB.ne
      have hb : b = n.head := by rw [hRB.inv.eList.head, hbt]; rfl
      have hdeadn' : live n' n.head = false := by rw [(hrecB _ hRB.head).1]; exact hRB.dead
      have hLn : liveH n B.elist = liveH n bt := by rw [hbt, hb]; simp [FM_cons, hRB.dead]
      have e1 : liveH n' B'.elist = hy :: liveH n B.elist := by
        have hLn' : liveH n (n.head :: bt) = liveH n bt := by simp [FM_cons, hRB.dead]
        rw [hB', hbt, hb, liveH_insertAfterL_head _ _ hdeadn' hlyB, hhyB, hLn']
        congr 1
        exact liveH_frame fun e he => hrecB e (by rw [hbt]; exact List.mem_cons_of_mem _ he)
      refine ⟨?_, fun z => by rw [e1]; simp⟩
      rw [e1, hLB, hxi', ← ha]
      have hdc' : live c' a = false := by
        rw [(hrecpre a List.mem_cons_self).1, ha]; exact hR.dead
      rw [liveH_insertAfterL_head _ _ hdc' hly, hhy]
      congr 1
      rw [ha]; simp only [FM_cons, hR.dead, ite_false, Bool.false_eq_true]
      exact (liveH_frame fun e he => hrecpre e (List.mem_cons_of_mem _ he)).symm
    | some x =>
      obtain ⟨hlx, hhx⟩ := hxs x rfl
      have hmem : x ∈ liveH c pre ↔ xi ∈ pre := by
        rw [← hhx]; exact FM_mem_pre _ _ (hsplit ▸ hxi) hlx (hsplit ▸ hnd)
      by_cases hxpre : xi ∈ pre
      · have hxB : x ∈ liveH n B.elist := hLB ▸ hmem.mpr hxpre
        obtain ⟨hxn1, hxn2, hxn3⟩ := hIB x hxB
        have hne0 : om.nxtIdx.getX x ≠ 0 := by
          have := ((hRB.inv.eAlloc _).mp hxn1).1; omega
        dsimp only
        rw [ite_eq_left (by simp [hset, hne0])]
        refine (copied _ hxn1 hxpre ?_).elim fun y' h => h.elim fun n' h => ?_
        swap
        · obtain ⟨hrc, hN'⟩ := h
          simp only [bind, Except.bind, hrc]
          exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, by unfold NxtR; exact hN'⟩
        intro n' B' hRB' hB' hrecB hlyB hhyB hyB
        have hfB : liveH n' B.elist = liveH n B.elist := liveH_frame hrecB
        have e1 : liveH n' B'.elist = OrderMaintenance.Spec.insertAfterL x hy (liveH n B.elist)
          := by
          rw [hB',
            liveH_insertAfterL _ hxn1 (by rw [(hrecB _ hxn1).1]; exact hxn2) (hfB ▸ hBnd) hyB hlyB,
            hfB, hhyB, (hrecB _ hxn1).2, hxn3]
        refine ⟨?_, fun z => by rw [e1]; exact OrderMaintenance.Spec.mem_insertAfterL hxB⟩
        rw [e1, hLB,
          liveH_insertAfterL _ hxpre (by rw [(hrecpre _ hxpre).1]; exact hlx) (hfpre ▸ hndpre)
          hypre hly, hfpre, hhy, (hrecpre _ hxpre).2, hhx]
      · have hxB : x ∉ liveH n B.elist := hLB ▸ fun h => hxpre (hmem.mp h)
        have h0 : om.nxtIdx.getX x = 0 := by
          by_contra h; exact hxB (hzB x h)
        simp only [hset, Bool.true_and, h0, bne_self_eq_false, Bool.false_eq_true, ite_false]
        refine ⟨om, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
        unfold NxtR; rw [hn]
        have hxpost : xi ∈ post := by
          rcases List.mem_append.mp (hsplit ▸ hxi) with h | h
          · exact absurd h hxpre
          · exact h
        refine ⟨B, hRB, hIB, hzB, ?_⟩
        rw [ite_eq_left hset]
        refine ⟨pre, OrderMaintenance.Spec.insertAfterL xi y post, ?_, ?_, hpre, ?_⟩
        · rw [hA', hsplit, insertAfterL_append, ite_eq_right hxpre]
        · rw [hcur, insertAfterL_headD (List.ne_nil_of_mem hxpost)]
        · rw [hLB]; exact hfpre.symm

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
theorem liveH_kill {c c' : Core} {l : List Nat} {a : Nat} (ha : a ∈ l) (hpa : live c a = true)
    (hp'a : live c' a = false) (hp' : ∀ e, e ≠ a → live c' e = live c e) (hh : ∀ e, hdl c' e =
      hdl c e)
    (hl : l.Nodup) (hnd : (liveH c l).Nodup) : liveH c' l = (liveH c l).erase (hdl c a) := by
  rw [← FM_kill (live c) (hdl c) (p' := live c') ha hpa hp'a hp' hl hnd]
  exact FM_congr _ _ fun e _ => ⟨rfl, hh e⟩

theorem mirrorDelete_ok {om : OrderMaintenance} {c c' : Core} {A : Abs} {x xi : Nat}
    (hN : NxtR c A om) (hR : CoreR c A) (hnd : (liveH c A.elist).Nodup) (hxi : xi ∈ A.elist)
    (hlx : live c xi = true) (hhx : hdl c xi = x)
    (hrec : ∀ e, e ≠ xi → live c' e = live c e) (hhdl : ∀ e, hdl c' e = hdl c e)
    (hdead : live c' xi = false) :
    ∃ om2, om.mirrorDelete x = .ok om2 ∧ om2.cur = om.cur ∧ om2.curIdx = om.curIdx ∧
      om2.nextHandle = om.nextHandle ∧ om2.live = om.live ∧ om2.KB = om.KB ∧ NxtR c' A om2 := by
  unfold OrderMaintenance.mirrorDelete
  unfold NxtR at hN
  cases hn : om.nxt with
  | none => exact ⟨om, rfl, rfl, rfl, rfl, rfl, rfl, by unfold NxtR; rw [hn]; trivial⟩
  | some n =>
    rw [hn] at hN
    obtain ⟨B, hRB, hIB, hzB, hcs⟩ := hN
    have hnl := hR.inv.eList.nodup
    -- the part of `cur` before the cursor
    have hpre_same : ∀ pre post, A.elist = pre ++ post → xi ∉ pre → liveH c' pre = liveH c pre :=
      fun pre post hs hx => liveH_frame fun e he =>
        ⟨hrec e (fun h => hx (h ▸ he)), hhdl e⟩
    by_cases h0 : om.nxtIdx.getX x = 0
    · simp only [h0, bne_self_eq_false, Bool.false_eq_true, ite_false]
      refine ⟨om, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
      unfold NxtR; rw [hn]
      refine ⟨B, hRB, hIB, hzB, ?_⟩
      by_cases hset : om.cursorSet = true
      · rw [ite_eq_left hset] at hcs ⊢
        obtain ⟨pre, post, hsplit, hcur, hpre, hLB⟩ := hcs
        refine ⟨pre, post, hsplit, hcur, hpre, ?_⟩
        have hxB : x ∉ liveH n B.elist := fun h => by
          have := ((hRB.inv.eAlloc _).mp (hIB x h).1).1; omega
        have hxpre : xi ∉ pre := fun h => hxB (by
          rw [hLB, ← hhx]; exact FM_mem_of _ _ h hlx)
        rw [hLB, hpre_same pre post hsplit hxpre]
      · rw [ite_eq_right hset] at hcs ⊢; exact hcs
    · have hxB : x ∈ liveH n B.elist := hzB x h0
      have hset : om.cursorSet = true := by
        by_contra hset
        rw [ite_eq_right hset] at hcs
        subst hcs
        rw [liveH_initAbs hRB] at hxB; simp at hxB
      rw [ite_eq_left hset] at hcs
      obtain ⟨pre, post, hsplit, hcur, hpre, hLB⟩ := hcs
      have hxpre : xi ∈ pre := by
        have := hLB ▸ hxB
        rw [← hhx] at this
        exact (FM_mem_pre _ _ (hsplit ▸ hxi) hlx (hsplit ▸ hnd)).mp this
      obtain ⟨hxn1, hxn2, hxn3⟩ := hIB x hxB
      have hBnd : (liveH n B.elist).Nodup := hLB ▸ (FM_sub_nodup (hsplit ▸ hnd)).1
      obtain ⟨n', hr', hRB', hL', hrecB, hhdlB, _, _⟩ := core_kill hRB hxn1 hxn2 hBnd
      simp only [bne_iff_ne, ne_eq, h0, not_false_eq_true, ite_true, bind, Except.bind,
        runCore_ok hr']
      refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
      unfold NxtR
      have hLB' : liveH n' B.elist = (liveH n B.elist).erase x := by rw [hL', hxn3]
      refine ⟨B, hRB', fun z hz => ?_, fun z hz => ?_, ?_⟩
      · rw [hLB'] at hz
        have hzx : z ≠ x := fun e => by
          subst e; exact (List.Nodup.not_mem_erase hBnd) hz
        have hz' := List.mem_of_mem_erase hz
        simp only [Array.getX_setX, ite_eq_right hzx]
        obtain ⟨h1, h2, h3⟩ := hIB z hz'
        have hne : om.nxtIdx.getX z ≠ om.nxtIdx.getX x := fun e => hzx (by rw [← h3, e, hxn3])
        exact ⟨h1, by rw [hrecB _ hne]; exact h2, by rw [hhdlB]; exact h3⟩
      · simp only [Array.getX_setX] at hz
        split at hz
        · exact absurd rfl hz
        · rw [hLB']; exact (List.Nodup.mem_erase_iff hBnd).mpr ⟨‹_›, hzB z hz⟩
      · change if om.cursorSet = true then _ else _
        rw [ite_eq_left hset]
        refine ⟨pre, post, hsplit, hcur, hpre, ?_⟩
        have hprel : pre.Nodup := (List.nodup_append.mp (hsplit ▸ hnl)).1
        rw [hLB', hLB, liveH_kill hxpre hlx hdead hrec hhdl hprel (FM_sub_nodup (hsplit ▸ hnd)).1,
          hhx]

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### The rebuild -/

theorem post_nil {A : Abs} {c : Core} (hR : CoreR c A) {pre post : List Nat}
    (hs : A.elist = pre ++ post) (h : post.headD NIL = NIL) : post = [] := by
  cases post with
  | nil => rfl
  | cons p t =>
    change p = NIL at h
    exact absurd (hs ▸ List.mem_append_right _ (List.mem_cons_self (a := p) (l := t)) : p ∈ A.elist)
      (h ▸ hR.inv.eList.nonil)

/-- **The swap**: once the cursor has passed the end, `nxt` holds every live handle. -/
theorem swap_ok {om : OrderMaintenance} {n : Core} {A : Abs} {S : OrderMaintenance.Spec.State}
  (hN : NxtR' om.cur A om n)
    (hR : CoreR om.cur A) (hL : liveH om.cur A.elist = S.list) (hset : om.cursorSet = true)
    (hcur : om.cursor = NIL) (hS : OrderMaintenance.Spec.Inv S) (hf : om.nextHandle = S.fresh) :
    WInv (om.swap n) S := by
  obtain ⟨B, hRB, hIB, _, hcs⟩ := hN
  rw [ite_eq_left hset] at hcs
  obtain ⟨pre, post, hsplit, hc, _, hLB⟩ := hcs
  have hp := post_nil hR hsplit (hc ▸ hcur)
  subst hp
  rw [List.append_nil] at hsplit
  have hLB' : liveH n B.elist = S.list := by rw [hLB, ← hsplit, hL]
  exact ⟨hS, hf, B, hRB, hLB', hLB' ▸ hIB, by unfold NxtR; simp [OrderMaintenance.swap]⟩

/-- **Copying one element** at the cursor. -/
theorem copy_ok {om : OrderMaintenance} {n : Core} {A : Abs} (hN : NxtR' om.cur A om n) (hR :
  CoreR om.cur A)
    (hnd : (liveH om.cur A.elist).Nodup) (hset : om.cursorSet = true) (hcur : om.cursor ≠ NIL) :
    ∃ om' n', copyAtCursor om n = .ok (om', n') ∧ om'.cur = om.cur ∧ om'.curIdx = om.curIdx ∧
      om'.nxt = om.nxt ∧ om'.cursorSet = om.cursorSet ∧ om'.nextHandle = om.nextHandle ∧
      om'.live = om.live ∧ om'.KB = om.KB ∧ NxtR' om.cur A om' n' := by
  obtain ⟨B, hRB, hIB, hzB, hcs⟩ := hN
  rw [ite_eq_left hset] at hcs
  obtain ⟨pre, post, hsplit, hc, hpre, hLB⟩ := hcs
  obtain ⟨e, post', rfl⟩ : ∃ e post', post = e :: post' := by
    cases post with
    | nil => exact absurd hc hcur
    | cons e t => exact ⟨e, t, rfl⟩
  simp only [List.headD_cons] at hc
  subst hc
  have hnl := hR.inv.eList.nodup
  have heA : om.cursor ∈ A.elist := by rw [hsplit]; simp
  have hnext : eN om.cur om.cursor = post'.headD NIL := by
    rw [hR.inv.eList.next _ heA, hsplit, succOf_mid (hsplit ▸ hnl)]
  have hsplit' : A.elist = (pre ++ [om.cursor]) ++ post' := by rw [hsplit]; simp
  have hndpre := (FM_sub_nodup (hsplit ▸ hnd))
  have hhe : live om.cur om.cursor = true → hdl om.cur om.cursor ∉ liveH om.cur pre := by
    intro hl h
    rw [hsplit, liveH_append] at hnd
    exact (List.nodup_append.mp hnd).2.2 _ h _ (FM_mem_of _ _ List.mem_cons_self hl) rfl
  unfold copyAtCursor
  by_cases hl : live om.cur om.cursor = true
  · have hl' : (om.cur.E.getX om.cursor).live = true := hl
    simp only [hl', ite_true]
    have htail : n.tail ∈ B.elist := by
      rw [hRB.inv.tail]
      obtain ⟨b, bt, hb⟩ := List.exists_cons_of_ne_nil hRB.ne
      rw [hb]; exact getLastD_cons_mem _ _ _
    obtain ⟨n', B', hr', hRB', hB', hrecB, hlyB, hhyB, hyB, _, _, _⟩ :=
      core_insert hRB htail (hdl om.cur om.cursor)
    simp only [bind, Except.bind]
    rw [show (om.cur.E.getX om.cursor).h = hdl om.cur om.cursor from rfl, runCore_ok hr']
    refine ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    have hB'e : B'.elist = B.elist ++ [n.E.size] := by
      rw [hB', hRB.inv.tail]; exact insertAfterL_getLastD hRB.inv.eList.nodup hRB.ne _
    have hLn : liveH n' B'.elist = liveH n B.elist ++ [hdl om.cur om.cursor] := by
      rw [hB'e, liveH_append, liveH_frame hrecB]
      simp [FM_cons, hlyB, hhyB]
    have hfreshB : hdl om.cur om.cursor ∉ liveH n B.elist := hLB ▸ hhe hl
    dsimp only
    generalize hH : hdl om.cur om.cursor = H at *
    refine ⟨B', hRB', fun z hz => ?_, fun z hz => ?_, ?_⟩
    · rw [hLn, List.mem_append, List.mem_singleton] at hz
      dsimp only
      rw [Array.getX_setX]
      rcases hz with hz | rfl
      · have hzx : z ≠ H := fun e => hfreshB (e ▸ hz)
        rw [ite_eq_right hzx]
        obtain ⟨h1, h2, h3⟩ := hIB z hz
        exact ⟨by rw [hB'e]; exact List.mem_append_left _ h1, by rw [(hrecB _ h1).1]; exact h2,
          by rw [(hrecB _ h1).2]; exact h3⟩
      · rw [ite_eq_left rfl]
        exact ⟨by rw [hB'e]; simp, hlyB, hhyB⟩
    · rw [hLn, List.mem_append, List.mem_singleton]
      dsimp only at hz
      rw [Array.getX_setX] at hz
      split at hz
      · exact Or.inr ‹_›
      · exact Or.inl (hzB z hz)
    · change if om.cursorSet = true then _ else _
      rw [ite_eq_left hset]
      refine ⟨pre ++ [om.cursor], post', hsplit', hnext, by simp, ?_⟩
      rw [hLn, hLB, liveH_append]
      simp [FM_cons, hl, hH]
  · have hl' : (om.cur.E.getX om.cursor).live = false := by simpa [live] using hl
    simp only [hl', Bool.false_eq_true, ite_false]
    refine ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, B, hRB, hIB, hzB, ?_⟩
    change if om.cursorSet = true then _ else _
    rw [ite_eq_left hset]
    refine ⟨pre ++ [om.cursor], post', hsplit', hnext, by simp, ?_⟩
    rw [hLB, liveH_append]
    simp [FM_cons, hl]

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
theorem coreR_sameLinks_init {n n' : Core} (hR : CoreR n initAbs) (hs : SameLinks n n') :
    CoreR n' initAbs :=
  ⟨hR.inv.of_sameLinks' hs (by simp [initAbs]), hs.P ▸ hR.P, hR.ne,
   by simp only [live]; rw [hs.head, hs.eLive]; exact hR.dead⟩

/-- **One preparation step** of `nxt`; when it completes, the cursor starts after the sentinel. -/
theorem prepare_ok {om : OrderMaintenance} {n : Core} {A : Abs} (hN : NxtR' om.cur A om n) (hR :
  CoreR om.cur A)
    (hset : om.cursorSet = false) :
    ∃ ready n', runCore n prepareStep = .ok (ready, n') ∧ NxtR' om.cur A om n' ∧
      (ready = true →
        NxtR' om.cur A { om with cursor := (om.cur.E.getX om.cur.head).next, cursorSet := true }
          n') := by
  obtain ⟨B, hRB, hIB, hzB, hcs⟩ := hN
  rw [ite_eq_right (by simp [hset])] at hcs
  subst hcs
  obtain ⟨ready, n', hr, hsl⟩ := noerr_prepareStep.run pres_prepareStep n
  have hRB' := coreR_sameLinks_init hRB hsl
  have hL0 := liveH_initAbs hRB
  have hL0' := liveH_initAbs hRB'
  have hz : ∀ x, om.nxtIdx.getX x ≠ 0 → False := fun x hx => by
    have := hzB x hx; rw [hL0] at this; simp at this
  refine ⟨ready, n', runCore_ok hr, ⟨initAbs, hRB', fun z hz' => ?_, fun z h => (hz z h).elim, ?_⟩,
    fun _ => ⟨initAbs, hRB', fun z hz' => ?_, fun z h => (hz z h).elim, ?_⟩⟩
  · rw [hL0'] at hz'; simp at hz'
  · rw [ite_eq_right (by simp [hset])]
  · rw [hL0'] at hz'; simp at hz'
  · change if true = true then _ else _
    rw [ite_eq_left rfl]
    obtain ⟨a, t, ht⟩ := List.exists_cons_of_ne_nil hR.ne
    have ha : om.cur.head = a := by rw [hR.inv.eList.head, ht]; rfl
    refine ⟨[a], t, ht, ?_, by simp, ?_⟩
    · change eN om.cur om.cur.head = _
      rw [hR.inv.eList.next _ hR.head, ht, ha, succOf_cons', ite_eq_left rfl]
    · rw [hL0', ← ha]; simp [FM_cons, hR.dead]

theorem rebuildLoop_ok {S : OrderMaintenance.Spec.State} (hS : OrderMaintenance.Spec.Inv S) :
    ∀ fuel budget (om : OrderMaintenance) (n : Core) (A : Abs), CoreR om.cur A → liveH om.cur
      A.elist = S.list →
      IdxOK om.cur A om.curIdx S.list → NxtR' om.cur A om n → om.nextHandle = S.fresh →
      ∃ om', rebuildLoop om n fuel budget = .ok om' ∧ WInv om' S := by
  intro fuel
  induction fuel with
  | zero =>
    intro budget om n A hR hL hI hN hf
    exact ⟨_, rfl, hS, hf, A, hR, hL, hI, hN⟩
  | succ fuel ih =>
    intro budget om n A hR hL hI hN hf
    have hnd : (liveH om.cur A.elist).Nodup := hL ▸ hS.1
    unfold rebuildLoop
    by_cases hb : budget = 0
    · rw [ite_eq_left hb]; exact ⟨_, rfl, hS, hf, A, hR, hL, hI, hN⟩
    rw [ite_eq_right hb]
    by_cases hset : om.cursorSet = true
    · rw [ite_eq_right (by simp [hset])]
      by_cases hc : om.cursor = NIL
      · rw [ite_eq_left hc]; exact ⟨_, rfl, swap_ok hN hR hL hset hc hS hf⟩
      rw [ite_eq_right hc]
      obtain ⟨om', n', hcp, e1, e2, _, e4, e5, _, _, hN'⟩ := copy_ok hN hR hnd hset hc
      simp only [bind, Except.bind, hcp]
      by_cases hc' : om'.cursor = NIL
      · rw [ite_eq_left hc']
        refine ⟨_, rfl, swap_ok (om := om') (e1 ▸ hN') (e1 ▸ hR) (e1 ▸ hL) (e4 ▸ hset) hc' hS
          (e5 ▸ hf)⟩
      · rw [ite_eq_right hc']
        exact ih _ om' n' A (e1 ▸ hR) (e1 ▸ hL) (e1 ▸ e2 ▸ hI) (e1 ▸ hN') (e5 ▸ hf)
    · have hf' : om.cursorSet = false := by simpa using hset
      rw [ite_eq_left (by simp [hf'])]
      obtain ⟨ready, n', hr, hN1, hN2⟩ := prepare_ok hN hR hf'
      simp only [bind, Except.bind, hr]
      cases ready with
      | true =>
        rw [ite_eq_left rfl]
        exact ih budget _ n' A hR hL hI (hN2 rfl) hf
      | false =>
        simp only [Bool.false_eq_true, ite_false]
        exact ih _ om n' A hR hL hI hN1 hf

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
theorem newCore_ok {P : Params} (hP : CoreP P) (lazy : Bool) :
    ∃ n, newCore P lazy = .ok n ∧ CoreR n initAbs := by
  obtain ⟨n, hr, hI, hs⟩ := initCore_run lazy { P := P }
  refine ⟨n, ?_, hI, hs.P ▸ hP, by rw [initAbs_elist]; simp, ?_⟩
  · unfold newCore; rw [runCore_ok hr]; rfl
  · simp only [live]; rw [hs.head, hs.eLive]; rfl

/-- **The rebuild step** keeps Invariant R. -/
theorem rebuildStep_ok {mk : Nat → Params} (hmk : ∀ N, CoreP (mk N)) {om : OrderMaintenance} {S
  : OrderMaintenance.Spec.State}
    (hW : WInv om S) : ∃ om', om.rebuildStep mk = .ok om' ∧ WInv om' S := by
  obtain ⟨hS, hf, A, hR, hL, hI, hN⟩ := hW
  unfold OrderMaintenance.rebuildStep
  unfold NxtR at hN
  cases hn : om.nxt with
  | none =>
    simp only
    split
    · obtain ⟨n, hnew, hRn⟩ := newCore_ok (hmk om.nextCapacity) true
      simp only [bind, Except.bind, hnew]
      refine ⟨_, rfl, hS, hf, A, hR, hL, hI, ?_⟩
      unfold NxtR
      refine ⟨initAbs, hRn, fun z hz => ?_, fun z hz => ?_, by simp⟩
      · rw [liveH_initAbs hRn] at hz; simp at hz
      · exact absurd (by simp [Array.getX] : (#[] : Array Nat).getX z = 0) hz
    · exact ⟨om, rfl, hS, hf, A, hR, hL, hI, by unfold NxtR; rw [hn]; trivial⟩
  | some n0 =>
    rw [hn] at hN
    exact rebuildLoop_ok hS _ _ _ n0 A hR hL hI hN hf

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-- The specification operation of a wrapper insertion. -/
def insOp : Option Nat → OrderMaintenance.Spec.Op
  | none => .insertFirst
  | some x => .insertAfter x

/-- The wrapper's index supplies a concrete insertion position, including the sentinel case. -/
theorem insertion_position {om : OrderMaintenance} {Sp : OrderMaintenance.Spec.State} {A : Abs}
    (hR : CoreR om.cur A) (hI : IdxOK om.cur A om.curIdx Sp.list)
    (hx : Option Nat) (hv : (insOp hx).Valid Sp) :
    ∃ xi, xi ∈ A.elist ∧
      xi = (match hx with | none => om.cur.head | some x => om.curIdx.getX x) ∧
      (hx = none → xi = om.cur.head) ∧
      (∀ x, hx = some x → live om.cur xi = true ∧ hdl om.cur xi = x) := by
  cases hx with
  | none => exact ⟨_, hR.head, rfl, fun _ => rfl, fun _ h => (by cases h)⟩
  | some x =>
    obtain ⟨h1, h2, h3⟩ := hI x hv
    exact ⟨_, h1, rfl, fun h => (by cases h), fun x' h => (by cases h; exact ⟨h2, h3⟩)⟩

/-- A valid specification insertion adds exactly the fresh handle to the live list. -/
theorem step_ins_mem (Sp : OrderMaintenance.Spec.State) (hx : Option Nat)
    (hv : (insOp hx).Valid Sp) :
    ∀ z, z ∈ (OrderMaintenance.Spec.step Sp (insOp hx)).1.list ↔ z = Sp.fresh ∨ z ∈ Sp.list := by
  intro z
  cases hx with
  | none => simp only [Spec.step, insOp, List.mem_cons]
  | some x => exact OrderMaintenance.Spec.mem_insertAfterL hv

/-- Core insertion preserves the live-handle interpretation, including insertion at the sentinel. -/
theorem inserted_live_handles {om : OrderMaintenance} {Sp : OrderMaintenance.Spec.State}
    {A : Abs} {c' : Core} {xi : Nat} {hx : Option Nat} (hR : CoreR om.cur A)
    (hf : om.nextHandle = Sp.fresh) (hL : liveH om.cur A.elist = Sp.list)
    (hnd : (liveH om.cur A.elist).Nodup) (hxi : xi ∈ A.elist)
    (hxn : hx = none → xi = om.cur.head)
    (hxs : ∀ x, hx = some x → live om.cur xi = true ∧ hdl om.cur xi = x)
    (hrec : ∀ e ∈ A.elist, live c' e = live om.cur e ∧ hdl c' e = hdl om.cur e)
    (hly : live c' om.cur.E.size = true) (hhy : hdl c' om.cur.E.size = om.nextHandle)
    (hyA : om.cur.E.size ∉ A.elist) :
    liveH c' (OrderMaintenance.Spec.insertAfterL xi om.cur.E.size A.elist) =
      (OrderMaintenance.Spec.step Sp (insOp hx)).1.list := by
  have hfr : liveH c' A.elist = liveH om.cur A.elist := liveH_frame hrec
  cases hx with
  | none =>
    obtain ⟨a, t, ht⟩ := List.exists_cons_of_ne_nil hR.ne
    have ha : om.cur.head = a := by rw [hR.inv.eList.head, ht]; rfl
    have hda : live c' a = false := by
      rw [(hrec a (ht ▸ List.mem_cons_self)).1, ← ha]; exact hR.dead
    rw [hxn rfl, ha, ht, liveH_insertAfterL_head _ _ hda hly, hhy, hf]
    change _ = Sp.fresh :: Sp.list
    rw [← hL, ht]
    have hda0 : live om.cur a = false := ha ▸ hR.dead
    simp only [FM_cons, hda0, Bool.false_eq_true, ite_false]
    congr 1
    exact liveH_frame fun e he => hrec e (ht ▸ List.mem_cons_of_mem _ he)
  | some x =>
    obtain ⟨hlx, hhx⟩ := hxs x rfl
    rw [liveH_insertAfterL _ hxi (by rw [(hrec _ hxi).1]; exact hlx) (hfr ▸ hnd) hyA hly,
      hfr,
      (hrec _ hxi).2, hhx, hhy, hL, hf]
    rfl

/-- Updating the fresh handle's index preserves every live element's lookup. -/
theorem IdxOK.insert_update {om : OrderMaintenance} {Sp : OrderMaintenance.Spec.State}
    {A A' : Abs} {c' : Core} {xi : Nat} {hx : Option Nat}
    (hS : OrderMaintenance.Spec.Inv Sp) (hf : om.nextHandle = Sp.fresh)
    (hI : IdxOK om.cur A om.curIdx Sp.list) (hv : (insOp hx).Valid Sp)
    (hA' : A'.elist = OrderMaintenance.Spec.insertAfterL xi om.cur.E.size A.elist)
    (hxi : xi ∈ A.elist)
    (hrec : ∀ e ∈ A.elist, live c' e = live om.cur e ∧ hdl c' e = hdl om.cur e)
    (hly : live c' om.cur.E.size = true) (hhy : hdl c' om.cur.E.size = om.nextHandle) :
    IdxOK c' A' (om.curIdx.setX om.nextHandle om.cur.E.size)
      (OrderMaintenance.Spec.step Sp (insOp hx)).1.list := by
  have hmem := step_ins_mem Sp hx hv
  have hyA' : om.cur.E.size ∈ A'.elist := by
    rw [hA']; exact (OrderMaintenance.Spec.mem_insertAfterL hxi).mpr (Or.inl rfl)
  intro z hz
  simp only [Array.getX_setX]
  rcases (hmem z).mp hz with rfl | hz'
  · rw [ite_eq_left hf.symm]; exact ⟨hyA', hly, hhy.trans hf⟩
  · have hzy : z ≠ om.nextHandle := fun e => Nat.lt_irrefl z (by
      have := hS.2 z hz'; rw [← hf, ← e] at this; exact this)
    rw [ite_eq_right hzy]
    obtain ⟨h1, h2, h3⟩ := hI z hz'
    refine ⟨?_, by rw [(hrec _ h1).1]; exact h2, by rw [(hrec _ h1).2]; exact h3⟩
    rw [hA']; exact (OrderMaintenance.Spec.mem_insertAfterL hxi).mpr (Or.inr h1)

/-- Deleting a handle preserves all remaining index entries when the other elements stay live. -/
theorem IdxOK.delete_update {c c' : Core} {A : Abs} {idx : Array Nat} {L : List Nat} {x : Nat}
    (hI : IdxOK c A idx L) (hnd : L.Nodup) (hhx : hdl c (idx.getX x) = x)
    (hrec : ∀ e, e ≠ idx.getX x → live c' e = live c e)
    (hhdl : ∀ e, hdl c' e = hdl c e) : IdxOK c' A (idx.setX x 0) (L.erase x) := by
  intro z hz
  have hzx : z ≠ x := fun e => by subst e; exact (List.Nodup.not_mem_erase hnd) hz
  have hz' := List.mem_of_mem_erase hz
  simp only [Array.getX_setX, ite_eq_right hzx]
  obtain ⟨h1, h2, h3⟩ := hI z hz'
  have hne : idx.getX z ≠ idx.getX x := fun e => hzx (by rw [← h3, e, hhx])
  exact ⟨h1, by show live c' _ = true; rw [hrec _ hne]; exact h2,
    by show hdl c' _ = z; rw [hhdl]; exact h3⟩

/-- The common wrapper invariant after a core insertion has been mirrored. -/
theorem WInv.insert_after_mirror {om om2 : OrderMaintenance} {Sp : OrderMaintenance.Spec.State}
    {A A' : Abs} {c' : Core} {xi : Nat} {hx : Option Nat}
    (hS : OrderMaintenance.Spec.Inv Sp) (hf : om.nextHandle = Sp.fresh)
    (hI : IdxOK om.cur A om.curIdx Sp.list) (hv : (insOp hx).Valid Sp)
    (hR' : CoreR c' A')
    (hL' : liveH c' A'.elist = (OrderMaintenance.Spec.step Sp (insOp hx)).1.list)
    (hA' : A'.elist = OrderMaintenance.Spec.insertAfterL xi om.cur.E.size A.elist)
    (hxi : xi ∈ A.elist)
    (hrec : ∀ e ∈ A.elist, live c' e = live om.cur e ∧ hdl c' e = hdl om.cur e)
    (hly : live c' om.cur.E.size = true) (hhy : hdl c' om.cur.E.size = om.nextHandle)
    (hcur : om2.cur = c') (hidx : om2.curIdx = om.curIdx.setX om.nextHandle om.cur.E.size)
    (hfresh : om2.nextHandle = om.nextHandle + 1)
    (hN : NxtR c' A' { om2 with live := om2.live + 1 }) :
    WInv { om2 with live := om2.live + 1 } (OrderMaintenance.Spec.step Sp (insOp hx)).1 := by
  refine ⟨OrderMaintenance.Spec.step_inv hS hv, ?_, A', ?_, ?_, ?_, ?_⟩
  · change om2.nextHandle = _
    rw [hfresh]; cases hx <;> simp only [hf, Spec.step, insOp]
  · change CoreR om2.cur A'; rw [hcur]; exact hR'
  · change liveH om2.cur A'.elist = _; rw [hcur]; exact hL'
  · change IdxOK om2.cur A' om2.curIdx _
    rw [hcur, hidx]
    exact hI.insert_update hS hf hv hA' hxi hrec hly hhy
  · change NxtR om2.cur A' { om2 with live := om2.live + 1 }
    rw [hcur]; exact hN

/-- The common wrapper invariant after a core deletion has been mirrored. -/
theorem WInv.delete_after_mirror {om om2 : OrderMaintenance} {Sp : OrderMaintenance.Spec.State}
    {A : Abs} {c' : Core} {x : Nat}
    (hS : OrderMaintenance.Spec.Inv Sp) (hf : om.nextHandle = Sp.fresh)
    (hI : IdxOK om.cur A om.curIdx Sp.list) (hv : x ∈ Sp.list) (hR' : CoreR c' A)
    (hL' : liveH c' A.elist = (Sp.list.erase x)) (hhx : hdl om.cur (om.curIdx.getX x) = x)
    (hrec : ∀ e, e ≠ om.curIdx.getX x → live c' e = live om.cur e)
    (hhdl : ∀ e, hdl c' e = hdl om.cur e)
    (hcur : om2.cur = c') (hidx : om2.curIdx = om.curIdx.setX x 0)
    (hfresh : om2.nextHandle = om.nextHandle)
    (hN : NxtR c' A { om2 with live := om2.live - 1 }) :
    WInv { om2 with live := om2.live - 1 } (OrderMaintenance.Spec.step Sp (.delete x)).1 := by
  refine ⟨OrderMaintenance.Spec.step_inv hS hv, ?_, A, ?_, ?_, ?_, ?_⟩
  · change om2.nextHandle = _; rw [hfresh]; exact hf
  · change CoreR om2.cur A; rw [hcur]; exact hR'
  · change liveH om2.cur A.elist = Sp.list.erase x; rw [hcur]; exact hL'
  · change IdxOK om2.cur A om2.curIdx (Sp.list.erase x)
    rw [hcur, hidx]
    exact hI.delete_update hS.1 hhx hrec hhdl
  · change NxtR om2.cur A { om2 with live := om2.live - 1 }
    rw [hcur]; exact hN

/-- **Insertion** keeps Invariant R and returns the specification's new name. -/
theorem insert_ok {mk : Nat → Params} (hmk : ∀ N, CoreP (mk N)) {om : OrderMaintenance} {S :
  OrderMaintenance.Spec.State}
    (hW : WInv om S) (hx : Option Nat) (hv : (insOp hx).Valid S) :
    ∃ om', om.insert mk hx = .ok (S.fresh, om') ∧ WInv om' (OrderMaintenance.Spec.step S (insOp
      hx)).1 := by
  obtain ⟨hS, hf, A, hR, hL, hI, hN⟩ := hW
  have hnd : (liveH om.cur A.elist).Nodup := hL ▸ hS.1
  have hfresh : om.nextHandle ∉ liveH om.cur A.elist := by
    rw [hL, hf]; exact fun h => Nat.lt_irrefl _ (hS.2 _ h)
  -- the anchor
  obtain ⟨xi, hxi, hxeq, hxn, hxs⟩ := insertion_position hR hI hx hv
  obtain ⟨c', A', hr, hR', hA', hrec, hly, hhy, hyA, _, hhead, _⟩ := core_insert hR hxi
    om.nextHandle
  obtain ⟨om2, hm, e1, e2, e3, _, _, hN2⟩ := mirrorInsert_ok (om := { om with
      cur := c'
      nextHandle := om.nextHandle + 1
      curIdx := om.curIdx.setX om.nextHandle om.cur.E.size })
    (c' := c') hN hR hnd hxi hxn hxs hA' hyA hrec hly hhy hfresh
  -- the new handle list
  have hL' : liveH c' A'.elist = (OrderMaintenance.Spec.step S (insOp hx)).1.list := by
    rw [hA']
    exact inserted_live_handles hR hf hL hnd hxi hxn hxs hrec hly hhy hyA
  have hW3 : WInv { om2 with live := om2.live + 1 }
      (OrderMaintenance.Spec.step S (insOp hx)).1 :=
    WInv.insert_after_mirror hS hf hI hv hR' hL' hA' hxi hrec hly hhy e1 e2 e3 hN2
  obtain ⟨om4, hrb, hW4⟩ := rebuildStep_ok hmk hW3
  refine ⟨om4, ?_, hW4⟩
  unfold OrderMaintenance.insert
  cases hx <;>
  · simp only at hxeq
    subst hxeq
    dsimp only
    rw [onCur_ok hr]
    simp only [bind, Except.bind]
    rw [hm]
    simp only
    rw [hrb, hf]
    rfl

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-- **Deletion** keeps Invariant R. -/
theorem delete_ok {mk : Nat → Params} (hmk : ∀ N, CoreP (mk N)) {om : OrderMaintenance} {S :
  OrderMaintenance.Spec.State}
    (hW : WInv om S) {x : Nat} (hv : x ∈ S.list) :
    ∃ om', om.delete mk x = .ok om' ∧ WInv om' (OrderMaintenance.Spec.step S (.delete x)).1 := by
  obtain ⟨hS, hf, A, hR, hL, hI, hN⟩ := hW
  have hnd : (liveH om.cur A.elist).Nodup := hL ▸ hS.1
  obtain ⟨hxi, hlx, hhx⟩ := hI x hv
  obtain ⟨c', hr, hR', hL', hrec, hhdl, _, hdead⟩ := core_kill hR hxi hlx hnd
  obtain ⟨om2, hm, e1, e2, e3, _, _, hN2⟩ := mirrorDelete_ok (om := { om with
      cur := c'
      curIdx := om.curIdx.setX x 0 }) (c' := c') hN hR hnd hxi hlx hhx hrec hhdl hdead
  have hW3 : WInv { om2 with live := om2.live - 1 }
      (OrderMaintenance.Spec.step S (.delete x)).1 :=
    WInv.delete_after_mirror hS hf hI hv hR' (by rw [hL', hhx, hL]) hhx hrec hhdl
      e1 e2 e3 hN2
  obtain ⟨om4, hrb, hW4⟩ := rebuildStep_ok hmk hW3
  refine ⟨om4, ?_, hW4⟩
  unfold OrderMaintenance.delete
  rw [onCur_ok hr]
  simp only [bind, Except.bind]
  rw [hm]
  exact hrb

/-- **Order queries** answer as the specification. -/
theorem order_ok {om : OrderMaintenance} {S : OrderMaintenance.Spec.State} (hW : WInv om S) {x y
  : Nat} (hx : x ∈ S.list)
    (hy : y ∈ S.list) : om.order x y = .ok (OrderMaintenance.Spec.precedes S.list x y) := by
  obtain ⟨hS, _, A, hR, hL, hI, _⟩ := hW
  have hnd : (liveH om.cur A.elist).Nodup := hL ▸ hS.1
  obtain ⟨hx1, hx2, hx3⟩ := hI x hx
  obtain ⟨hy1, hy2, hy3⟩ := hI y hy
  unfold OrderMaintenance.order
  rw [runCore_ok (order_correct hR.inv hx1 hy1)]
  change Except.ok (OrderMaintenance.Spec.precedes A.elist _ _) = _
  congr 1
  unfold OrderMaintenance.Spec.precedes
  have := FM_idxOf_lt _ _ hx1 hy1 hx2 hy2 hnd
  rw [hx3, hy3] at this
  rw [← hL]
  exact decide_eq_decide.mpr this.symm

/-- **Initialization** establishes Invariant R for the empty list. -/
theorem init_ok {mk : Nat → Params} (hmk : ∀ N, CoreP (mk N)) (KB : Nat) :
    ∃ om, OrderMaintenance.init mk KB = .ok om ∧ WInv om OrderMaintenance.Spec.State.empty := by
  obtain ⟨n, hn, hR⟩ := newCore_ok (hmk minimumCapacity) false
  refine ⟨{ cur := n, KB := KB }, ?_,
    ⟨by simp [OrderMaintenance.Spec.Inv, OrderMaintenance.Spec.State.empty],
      rfl, initAbs, hR, liveH_initAbs hR,
      fun z hz => by simp [OrderMaintenance.Spec.State.empty] at hz, ?_⟩⟩
  · unfold OrderMaintenance.init
    simp only [bind, Except.bind, hn]
    rfl
  · unfold NxtR
    trivial


end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-- Each operation answers as the specification and keeps Invariant R. -/
theorem apply_ok {mk : Nat → Params} (hmk : ∀ N, CoreP (mk N)) {om : OrderMaintenance} {S :
  OrderMaintenance.Spec.State}
    (hW : WInv om S) {op : OrderMaintenance.Spec.Op} (hv : op.Valid S) :
    ∃ om', om.apply mk op = .ok ((OrderMaintenance.Spec.step S op).2, om') ∧ WInv om'
      (OrderMaintenance.Spec.step S op).1 := by
  cases op with
  | insertFirst =>
    obtain ⟨om', h, hW'⟩ := insert_ok hmk hW none hv
    exact ⟨om', by simp only [OrderMaintenance.apply, bind, Except.bind, h]; rfl, hW'⟩
  | insertAfter x =>
    obtain ⟨om', h, hW'⟩ := insert_ok hmk hW (some x) hv
    exact ⟨om', by simp only [OrderMaintenance.apply, bind, Except.bind, h]; rfl, hW'⟩
  | delete x =>
    obtain ⟨om', h, hW'⟩ := delete_ok hmk hW hv
    exact ⟨om', by simp only [OrderMaintenance.apply, bind, Except.bind, h]; rfl, hW'⟩
  | order x y =>
    refine ⟨om, ?_, hW⟩
    simp only [OrderMaintenance.apply, bind, Except.bind, order_ok hW hv.1 hv.2]
    rfl

theorem runOps_ok {mk : Nat → Params} (hmk : ∀ N, CoreP (mk N)) :
    ∀ (ops : List OrderMaintenance.Spec.Op) {om : OrderMaintenance} {S :
      OrderMaintenance.Spec.State}, WInv om S → OrderMaintenance.Spec.Valid S ops →
      om.runOps mk ops = .ok (OrderMaintenance.Spec.run S ops) := by
  intro ops
  induction ops with
  | nil => intro om S _ _; rfl
  | cons op ops ih =>
    intro om S hW hv
    obtain ⟨om', h, hW'⟩ := apply_ok hmk hW hv.1
    simp only [OrderMaintenance.runOps, bind, Except.bind, h, ih hW' hv.2]
    rfl

/-- **Theorem A (correctness of Level F).** For parameters satisfying the conditions of
`docs/PROOF.md` §3.4 at every capacity, the structure initializes, and on every valid sequence
of operations it never fails and answers exactly as the list specification. -/
theorem theoremA {mk : Nat → Params} (hmk : ∀ N, CoreP (mk N)) (KB : Nat) :
    ∃ om, OrderMaintenance.init mk KB = .ok om ∧
      ∀ ops, OrderMaintenance.Spec.Valid OrderMaintenance.Spec.State.empty ops →
        om.runOps mk ops = .ok (OrderMaintenance.Spec.run OrderMaintenance.Spec.State.empty ops)
          := by
  obtain ⟨om, h, hW⟩ := init_ok hmk KB
  exact ⟨om, h, fun ops hv => runOps_ok hmk ops hW hv⟩

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model

/-- The parameter conditions hold for the prototype's shape (`Params.for_capacity`):
`elementSpacing = 2^(elementBits-1) / (8G+8)` with `8G+8 ≤ 2^(elementBits-1)`, and `T + 1 <
  2^groupBits`. -/
theorem coreP_of_shape (P : Params) (hD : P.elementSpacing = 2 ^ (P.elementBits - 1) / (8 * P.G
  + 8))
    (hB : 8 * P.G + 8 ≤ 2 ^ (P.elementBits - 1)) (hT : P.T + 1 < 2 ^ P.groupBits) : CoreP P := by
  have hBe : 1 ≤ P.elementBits := by
    rcases Nat.eq_zero_or_pos P.elementBits with h | h
    · rw [h] at hB; simp at hB
    · exact h
  have h2 : 2 ^ P.elementBits = 2 * 2 ^ (P.elementBits - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  have hgs : fbGS P ≤ P.G + 1 := by unfold fbGS; omega
  have hgs1 : 1 ≤ fbGS P := fbGS_pos P
  have hgpc : fbGPC P ≤ P.T + 1 := by
    unfold fbGPC
    have : P.T / 2 / fbGS P ≤ P.T := Nat.le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _)
    omega
  generalize hX : 2 ^ (P.elementBits - 1) = X at hD hB h2
  have hD1 : 1 ≤ P.elementSpacing := by
    rw [hD]
    exact (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  -- elementSpacing * (8G + 8) ≤ X
  have hDX : P.elementSpacing * (8 * P.G + 8) ≤ X := by rw [hD]; exact Nat.div_mul_le_self _ _
  refine ⟨⟨?_, ?_⟩, hD1, ?_⟩
  · rw [Nat.one_shiftLeft, h2]; omega
  · rw [Nat.one_shiftLeft]; omega
  · rw [Nat.one_shiftLeft, h2]
    apply (Nat.lt_div_iff_mul_lt (by omega)).mpr
    -- elementSpacing (gs + 1) < 2X
    have : P.elementSpacing * (fbGS P + 1) ≤ P.elementSpacing * (P.G + 2) :=
      Nat.mul_le_mul_left _ (by omega)
    have : P.elementSpacing * (P.G + 2) ≤ P.elementSpacing * (8 * P.G + 8) :=
      Nat.mul_le_mul_left _ (by omega)
    have hX0 : 1 ≤ X := by omega
    omega

end OrderMaintenance.Proof
