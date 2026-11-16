/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Cost.CoreCost


/-!
# Fresh cores

A fresh core holds the sentinel alone, in one group of one chunk. It satisfies the lower
invariants, and the deferred construction of its top structure (`prepareStep`) touches only the
top structure, the chunk tags and the `ready` flag.
-/


@[expose] public section

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-- `TopRel`, but the `ready` flag may change too. -/
def TopRelR (s s' : Core) : Prop := TopRel s { s' with ready := s.ready }

theorem TopRel.topRelR {s s' : Core} (h : TopRel s s') : TopRelR s s' := by
  unfold TopRelR
  have hr : s'.ready = s.ready := h.rest.2.2.2.2.2.2.2.2
  have : ({ s' with ready := s.ready } : Core) = s' := by rw [← hr]
  rw [this]; exact h

theorem TopRelR.lowSame {s s' : Core} (h : TopRelR s s') : LowSame s s' :=
  ⟨h.E, h.Gs, h.Csize, h.C, h.rest.1, h.rest.2.1, h.rest.2.2.1⟩

theorem TopRelR.pqsame {s s' : Core} (h : TopRelR s s') : PQSame s s' := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := h.pq
  exact ⟨p4, p2, p3, p1, p5, p6, p8, p7, by rw [← h.rest.1]⟩

theorem TopRelR.trans {a b c : Core} (h1 : TopRelR a b) (h2 : TopRelR b c) : TopRelR a c := by
  unfold TopRelR at *
  have h1' : TopRel a { b with ready := a.ready } := h1
  obtain ⟨e2, g2, s2, c2, ⟨q1, q2, q3, q4, q5, q6, q7, q8⟩, ⟨r1, r2, r3, r4, r5, r6, r7, r8, -⟩⟩
    := h2
  obtain ⟨e1, g1, s1, c1, ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩, ⟨t1, t2, t3, t4, t5, t6, t7, t8, -⟩⟩
    := h1'
  have c1' : ∀ x, b.C.getX x = { a.C.getX x with tag := (b.C.getX x).tag } := c1
  have c2' : ∀ x, c.C.getX x = { b.C.getX x with tag := (c.C.getX x).tag } := c2
  exact ⟨e2.trans e1, g2.trans g1, s2.trans s1, fun x => by
    change c.C.getX x = { a.C.getX x with tag := (c.C.getX x).tag }
    rw [c2' x, c1' x],
    ⟨q1.trans p1, q2.trans p2, q3.trans p3, q4.trans p4, q5.trans p5, q6.trans p6, q7.trans p7,
      q8.trans p8⟩, ⟨r1.trans t1, r2.trans t2, r3.trans t3, r4.trans t4, r5.trans t5,
      r6.trans t6, r7.trans t7, r8.trans t8, rfl⟩⟩

theorem top_resetTop : Pres TopRel resetTop := by
  unfold resetTop; pres; intro s; exact TopRel.of_top s _ _ _ _

theorem top_initStep : Pres TopRel initStep := by
  unfold initStep
  pres [pres_getP, top_resetTop, top_setInTables _ _ _, top_newNode _, top_modN _ _,
    top_setLpar _ _, top_setPath _ _]
  all_goals first
    | (intro s; exact TopRel.of_tag s _ _)
    | (intro s; exact ⟨rfl, rfl, rfl, fun _ => rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩)

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-- What the deferred construction keeps: everything below the top structure, and the queue. -/
def LowRel (s s' : Core) : Prop := LowSame s s' ∧ PQSame s s'

instance : IsPre LowRel where
  refl s := ⟨⟨rfl, rfl, rfl, fun _ => rfl, rfl, rfl, rfl⟩, PQSame.refl s⟩
  trans _ _ _ h1 h2 := ⟨⟨h2.1.E.trans h1.1.E, h2.1.Gs.trans h1.1.Gs, h2.1.Csize.trans h1.1.Csize,
    fun c => by rw [h2.1.C c, h1.1.C c], h2.1.P.trans h1.1.P, h2.1.count.trans h1.1.count,
    h2.1.head.trans h1.1.head⟩, h1.2.trans h2.2⟩

theorem TopRel.lowRel {s s' : Core} (h : TopRel s s') : LowRel s s' := ⟨h.lowSame, h.pqsame⟩

theorem low_initStep : Pres LowRel initStep := top_initStep.mono fun _ _ h => h.lowRel

theorem low_prepareStep : Pres LowRel prepareStep := by
  unfold prepareStep
  pres [low_initStep]
  intro s; exact ⟨⟨rfl, rfl, rfl, fun _ => rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl⟩⟩

theorem low_initTop (lazy : Bool) : Pres LowRel (initTop lazy) := by
  unfold initTop
  pres [pres_getP, low_initStep]
  all_goals (intro s; exact ⟨⟨rfl, rfl, rfl, fun _ => rfl, rfl, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩)

/-- The lower invariants survive steps that keep `LowRel`, given INV-S. -/
theorem LowInv.lowRel {s s' : Core} {L : List Nat} (h : LowInv s L) (hR : LowRel s s')
    (hI : ∃ A, INV s' A ∧ A.elist = L) : LowInv s' L :=
  h.transfer hR.1 hI (h.pq.qsame hR.2 hR.1.qsame)

/-- **The deferred construction** of a core holding the sentinel alone never fails, and keeps the
lower invariants. -/
theorem prepareStep_low {s : Core} (h : LowInv s initAbs.elist) (hI : INV s initAbs) :
    ∃ b s', prepareStep.run s = .ok b s' ∧ LowInv s' initAbs.elist ∧ INV s' initAbs ∧
      LowRel s s' := by
  obtain ⟨b, s', hr⟩ := noerr_prepareStep s
  have hR : LowRel s s' := by have := low_prepareStep s; rw [hr] at this; exact this
  have hS : SameLinks s s' := by have := pres_prepareStep s; rw [hr] at this; exact this
  have hI' : INV s' initAbs := hI.of_sameLinks' hS (by simp [initAbs])
  exact ⟨b, s', hr, h.lowRel hR ⟨initAbs, hI', rfl⟩, hI', hR⟩

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
section init
variable (P : Params)

theorem init_liveG (g : Nat) : LiveG (initState P) g ↔ g = 1 := by
  have hG := getX_two (default : Group)
    { chk := 1, lab := 1 <<< (P.groupBits - 1), first := 1, last := 1, size := 1 }
  simp only [LiveG, gA, initState, hG]
  constructor
  · rintro ⟨h1, h2, -⟩; simp at h2; unfold NIL at h1; omega
  · rintro rfl; simp [NIL]

theorem init_liveC (c : Nat) : LiveC (initState P) c ↔ c = 1 := by
  simp only [LiveC, initState]; simp; omega

theorem init_g1 : gSz (initState P) 1 = 1 ∧ gSt (initState P) 1 = .quiet ∧ gC (initState P) 1 = 1 ∧
    gL (initState P) 1 = cG P ∧ gN (initState P) 1 = NIL := by
  have hG := getX_two (default : Group)
    { chk := 1, lab := 1 <<< (P.groupBits - 1), first := 1, last := 1, size := 1 }
  simp [gSz, gSt, gC, gL, gN, initState, hG, cG]

theorem init_c1 : cSz (initState P) 1 = 1 ∧ cSt (initState P) 1 = .quiet ∧ cLs (initState P) 1 =
  1 := by
  have hC := getX_two (default : Chunk) { first := 1, last := 1, size := 1 }
  simp [cSz, cSt, cLs, initState, hC]

theorem init_e1 : eG (initState P) 1 = 1 ∧ eL (initState P) 1 = cE P := by
  have hE := getX_two (default : Elem)
    { grp := 1, lab := 1 <<< (P.elementBits - 1), h := 0, live := false }
  simp [eG, eL, initState, hE, cE]

theorem init_runOf : runOf (initState P) initAbs.elist 1 = [1] := by
  rw [initAbs_elist]; unfold runOf; simp [(init_e1 P).1]

theorem init_GrpsC (c : Nat) : GrpsC (initState P) c = if c = 1 then {1} else ∅ := by
  ext g
  rw [mem_GrpsC, init_liveG]
  constructor
  · rintro ⟨rfl, hc⟩; rw [(init_g1 P).2.2.1] at hc; subst hc; simp
  · intro h; split at h
    · next hc => simp only [Finset.mem_singleton] at h; subst h; subst hc; exact ⟨rfl, (init_g1
      P).2.2.1⟩
    · simp at h

end init

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-- **The lower invariants of a fresh core.** -/
theorem lowinv_initState (P : Params) (hGP : GParams P) (hCP : CParams P) (hLP : LParams P) :
    LowInv (initState P) initAbs.elist := by
  obtain ⟨g1sz, g1st, g1c, g1l, g1n⟩ := init_g1 P
  obtain ⟨c1sz, c1st, c1ls⟩ := init_c1 P
  obtain ⟨e1g, e1l⟩ := init_e1 P
  have hrun := init_runOf P
  have hLv := init_liveG P
  have hLC := init_liveC P
  have hP : (initState P).P = P := rfl
  have hG4 := hGP.G4
  have hcm : 1 ≤ cmax P := by unfold cmax umax; omega
  have hθ := hCP.I4
  refine ⟨⟨initAbs, inv_initState P, rfl⟩, ⟨⟨fun _ => 0, fun _ => 0, fun _ => 0⟩, ?_⟩,
    ⟨fun _ => 0, ?_, ⟨⟨fun _ => false, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0,
      fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 1⟩, ?_⟩, hLP, hGP⟩, ?_, ⟨fun _ => 1, 0, ?_⟩, hCP⟩
  · -- groups
    refine ⟨fun g hg => ?_, fun g hg hs => ?_, fun g hg hs => ?_, fun g hg => ?_, fun g hg hs => ?_,
      fun g hg hs _ => ?_, fun g hg => ?_, fun g hg e he => ?_, fun g hg hs => ?_, fun g hg hs
        => ?_,
      fun g hg hs => ?_⟩ <;> rw [hLv] at hg <;> subst hg
    · rw [hrun, g1sz]; rfl
    · rw [g1st] at hs; cases hs
    · rw [g1st] at hs; cases hs
    · rw [g1st]; simp
    · refine ⟨by rw [g1sz, hP]; omega, by rw [g1sz], Or.inr ?_⟩
      rw [hrun]; simp [initState]
    · rw [g1st] at hs; cases hs
    · rw [hrun]; simp
    · rw [hrun] at he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      subst he
      rw [e1l, hP]
      omega
    · simp
    · rw [g1st] at hs; cases hs
    · rw [g1st] at hs; cases hs
  · -- chunks
    refine ⟨fun c hc => ?_, fun x hx hxs => ?_, fun c hc hcs => ?_, fun g hg => ?_,
      fun x hx hxs _ => ?_, fun _ => le_rfl⟩
    · rw [hLC] at hc; subst hc
      rw [c1sz]; unfold celts; rw [initAbs_elist]; simp [e1g, g1c]
    · rw [hLC] at hx; subst hx; rw [c1st] at hxs; cases hxs
    · rw [hLC] at hc; subst hc; rw [c1st] at hcs; cases hcs
    · rw [hLv] at hg; subst hg; rw [g1c, hLC, c1st]; simp
    · rw [hLC] at hx; subst hx; rw [c1st] at hxs; cases hxs
  · -- labels
    refine
      { gaps := fun g hg hl => ?_, range := fun g hg => ?_, hv := fun _ => by simp,
        pb := fun _ => by simp, pf := fun _ => by simp, roots := fun c hc => ?_,
        claim2 := fun c hc => ?_, insQ := fun c hc _ => ?_, insO := fun c hc hcs => ?_,
        insS := fun c hc hcs => ?_, arrS := fun x hx hxs => ?_, arrN := fun c hc _ => by simp,
        e0 := fun c hc _ => ?_, famChild := fun p hp hps => ?_ }
    · rw [hLv] at hg; subst hg; rw [g1c, c1ls] at hl; exact absurd rfl hl
    · rw [hLv] at hg; subst hg; rw [g1l, hP, g1c]; simp
    · rw [hLC] at hc; subst hc
      change 0 + pending (initState P) _ 1 ≤ 0 + 0 + 1
      unfold pending; rw [init_GrpsC, ite_eq_left rfl]
      have := Finset.card_filter_le ({1} : Finset Nat)
        (fun g => (fun _ => false : Nat → Bool) g = false ∧ gSt (initState P) g ≠ .splitting)
      simp at this ⊢; omega
    · rw [hLC] at hc; subst hc
      change 0 * gmin _ + charge (initState P) _ 1 ≤ 0
      rw [charge_eq, init_GrpsC, ite_eq_left rfl, Finset.sum_singleton]
      unfold chTerm; rw [g1st]; simp
    · rw [hLC] at hc; subst hc; change 0 + 1 ≤ _; rw [c1sz]; omega
    · rw [hLC] at hc; subst hc; rw [c1st] at hcs; cases hcs
    · rw [hLC] at hc; subst hc; rw [c1st] at hcs; cases hcs
    · rw [hLC] at hx; subst hx; rw [c1st] at hxs; cases hxs
    · rw [hLC] at hc; subst hc; change 1 ≤ _; simp only [c1sz, le_refl]
    · rfl
  · -- the queue: empty
    refine ⟨fun _ => [], [], ⟨fun c => ?_, fun c h => ?_, fun b => ?_, fun b c => ?_, ?_, fun b
      => ?_,
      List.IsChain.nil, rfl⟩⟩
    · have : inQC (initState P) c = false := by
        unfold inQC
        by_cases hc : c = 1
        · subst hc; rw [c1sz, hP]; simp; omega
        · simp [hLC, hc]
      rw [this]; simp [initState, Array.getX, Array.getD]
    · exfalso
      unfold inQC at h; simp only [decide_eq_true_eq] at h
      rw [hLC] at h; obtain ⟨rfl, -, h3⟩ := h; rw [c1sz, hP] at h3; omega
    · exact ⟨List.nodup_nil, by simp, by simp [initState, Array.getX, Array.getD, NIL],
        fun _ h => by simp at h, fun _ h => by simp at h⟩
    · constructor
      · intro h; simp at h
      · rintro ⟨h, -⟩
        exfalso
        unfold inQC at h; simp only [decide_eq_true_eq] at h
        rw [hLC] at h; obtain ⟨rfl, -, h3⟩ := h; rw [c1sz, hP] at h3; omega
    · exact ⟨List.nodup_nil, by simp, by simp [initState, NIL], fun _ h => by simp at h,
        fun _ h => by simp at h⟩
    · simp
  · -- the chunk count
    refine ⟨by simp [initState], ?_, fun c hc _ => by rw [hP]; exact hcm⟩
    have hQ : quietSet (initState P) = {1} := by
      ext c; rw [mem_quietSet, hLC]
      constructor
      · rintro ⟨rfl, -⟩; simp
      · intro h; simp only [Finset.mem_singleton] at h; subst h; exact ⟨rfl, c1st⟩
    rw [hQ, Finset.sum_singleton, c1sz]; simp [initState]

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model OrderMaintenance.Zeroing
/-- A fresh core keeps its lower invariants through `initCore`. -/
theorem lowinv_initCore {s s' : Core} {lazy : Bool} (hGP : GParams s.P) (hCP : CParams s.P)
    (hLP : LParams s.P) (h : (initCore lazy).run s = .ok () s') :
    LowInv s' initAbs.elist ∧ INV s' initAbs := by
  obtain ⟨s'', hr, hI, -⟩ := initCore_run lazy s
  rw [hr] at h; cases h
  have hR : LowRel (initState s.P) s' := by
    unfold initCore at hr
    simp only [run_getP_bind] at hr
    rw [run_bind, run_set] at hr
    dsimp only at hr
    have := low_initTop lazy (initState s.P)
    rw [hr] at this; exact this
  exact ⟨(lowinv_initState s.P hGP hCP hLP).lowRel hR ⟨initAbs, hI, rfl⟩, hI⟩

/-- **The top structure's contract for its deferred construction.** `PI` holds while it is being
built; `ν` counts the steps left; `PP` is what it needs of the parameters. -/
structure PrepContract (TI PI : Core → Prop) (ν : Core → Nat) (PP : Params → Prop) : Prop where
  eager : ∀ s s', PP s.P → (initCore false).run s = .ok () s' → TI s' ∧ s'.resJob = none
  lazy : ∀ s s', PP s.P → (initCore true).run s = .ok () s' → PI s' ∧ ν s' ≤ s.P.H + 1
  step : ∀ s, PI s → ∃ b s', prepareStep.run s = .ok b s' ∧
    (b = true → TI s' ∧ s'.resJob = none) ∧ (b = false → PI s' ∧ ν s' < ν s)

/-- A ready fresh core satisfies the cost invariant: all game values are 0 and no job runs. -/
theorem costInv_fresh {TI : Core → Prop} {μ : Core → Nat} {J n R : Nat} {s : Core}
    (hL : LowInv s initAbs.elist) (hTI : TI s) (hres : s.resJob = none) (hn : 1 ≤ n)
    (hz : ∀ c, gval s c = 0) : CostInv TI μ J n R initAbs.elist s := by
  have hz' : ∀ j : Fin n, gvec n s j = 0 := fun j => by unfold gvec; rw [hz]; simp
  refine ⟨hL, hTI, 0, ⟨0, hn⟩, fun _ => 0, 0, 0, GameInv.reset hz' _, ?_⟩
  unfold RoundOK; rw [hres]; exact Or.inl hz

/-- The game values of a core holding the sentinel alone are 0. -/
theorem gval_fresh {s : Core} (hL : LowInv s initAbs.elist) (c : Nat) :
    gval s c = 0 := by
  obtain ⟨s₀, hC, -⟩ := hL.cinv
  have hθ := hL.cp.I4
  unfold gval
  split
  · next hc =>
    have hsz := hC.csz c hc.1
    have : (celts s initAbs.elist c).length ≤ 1 := by
      unfold celts; rw [initAbs_elist]; exact (List.length_filter_le _ _).trans (by simp)
    have hkG : 1 ≤ kG s.P := Nat.le_add_left 1 _
    have hcm : 1 ≤ cmax s.P := by unfold cmax umax; omega
    omega
  · rfl

end OrderMaintenance.Proof
