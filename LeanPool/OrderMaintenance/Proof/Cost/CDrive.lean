/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Cost.CMove


/-!
# Lemmas C1 and C2: the chunk drive

`driveChunkFrom x` makes `chunkBudget` chunk-split moves of `x`, each moving one unit to the lighter
sibling, or removes `x` once it is empty. With the units counted as in `C1`, the split ends
within `k_C(s₀)` insertions, and the siblings then hold at most `c_max ≤ θ` elements each (C2).
-/


@[expose] public section

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
theorem driveChunkFrom_ok {s : Core} {x : Nat} (I : Nat → Core → Prop) (Q : Core → Prop)
    (h0 : I 0 s)
    (hstep : ∀ j t, I j t → j < s.P.chunkBudget → ∃ t',
      ((chunkSplitStep x).run t = .ok true t' ∧ I (j + 1) t') ∨
      ((chunkSplitStep x).run t = .ok false t' ∧ Q t')) :
    ∃ t', (driveChunkFrom x).run s = .ok () t' ∧ (I s.P.chunkBudget t' ∨ Q t') := by
  unfold driveChunkFrom
  rw [run_getP_bind, run_bind]
  obtain ⟨c, t', hr, hres⟩ := forIn_loop
    (fun (_ : Nat) (_ : Option Unit × Unit) => do
      let b ← chunkSplitStep x
      if (!b) = true then pure (ForInStep.done (some (), ()))
      else pure (ForInStep.yield (none, ())))
    I Q s.P.chunkBudget (by
      intro _ j b t hI hj
      obtain ⟨t', h⟩ := hstep j t hI hj
      rcases h with ⟨hr, hI'⟩ | ⟨hr, hQ⟩
      · exact ⟨(none, ()), t', Or.inl ⟨by rw [run_bind, hr]; rfl, hI'⟩⟩
      · exact ⟨(some (), ()), t', Or.inr ⟨by rw [run_bind, hr]; rfl, hQ⟩⟩)
    (List.range s.P.chunkBudget) 0 (none, ()) s h0 (by simp)
  rw [hr]
  refine ⟨t', ?_, by simpa using hres⟩
  dsimp only
  split <;> rfl

/-- What the chunk drive knows about the family of `x` throughout: its size is at most what C1
allowed when the drive started, at most one insertion is undriven, and `s₀ x ≤ T`. -/
structure FamBound (t : Core) (δ s₀ : Nat → Nat) (x : Nat) : Prop where
  fam : cSz t (cLl t x) + cSz t x + cSz t (cRr t x) ≤
    δ (cLl t x) + δ x + δ (cRr t x) + s₀ x + unitsOf t.P (s₀ x) / (t.P.chunkBudget - 1)
  δs : δ (cLl t x) + δ x + δ (cRr t x) ≤ 1
  T : s₀ x ≤ t.P.T

/-- The extra invariant of the chunk drive survives its steps; a move also finds room for the
moved groups' labels (Lemma C3 provides it). -/
structure CXSteps (X Y : Core → Prop) (L : List Nat) (δ δu s₀ : Nat → Nat) (x : Nat) : Prop where
  moveL : ∀ t A' gh, INV t A' → A'.elist = L → GInv t L gh (fun _ => 0) → CInvE t L δ δu s₀ x →
    LiveC t x → cSt t x = .splitting → cF t x ≠ NIL → cSz t (cLl t x) ≤ cSz t (cRr t x) →
    FamBound t δ s₀ x → X t →
    ∃ labs, (pushLabsL t x (unitCand t x true).length).run t = .ok labs t ∧
      X (cmoveLState t x (unitCand t x true) labs)
  moveR : ∀ t A' gh, INV t A' → A'.elist = L → GInv t L gh (fun _ => 0) → CInvE t L δ δu s₀ x →
    LiveC t x → cSt t x = .splitting → cF t x ≠ NIL → cSz t (cRr t x) < cSz t (cLl t x) →
    FamBound t δ s₀ x → X t →
    ∃ labs, (pushLabsR t x (unitCand t x false).length).run t = .ok labs t ∧
      X (cmoveRState t x (unitCand t x false) labs)
  rem : ∀ t A' gh, INV t A' → A'.elist = L → GInv t L gh (fun _ => 0) → CInvE t L δ δu s₀ x →
    LiveC t x → cSt t x = .splitting → cF t x = NIL → cSz t (cLl t x) ≤ cmax t.P →
    cSz t (cRr t x) ≤ cmax t.P →
    FamBound t δ s₀ x → X t → Y (cremoveState t x)

/-- The chunk drive's invariant after `j` moves of `x`'s split. -/
structure CDriveInv (X : Core → Prop) (s : Core) (L : List Nat) (δ δu s₀ : Nat → Nat)
    (x y z a b c u₀ j : Nat) (t : Core) : Prop where
  xx : X t
  P : t.P = s.P
  ef : EFrame s t
  inv : ∃ A', INV t A' ∧ A'.elist = L
  ginv : ∃ gh, GInv t L gh (fun _ => 0)
  cinv : CInvE t L δ δu s₀ x
  live : LiveC t x
  st : cSt t x = .splitting
  ll : cLl t x = y
  rr : cRr t x = z
  sum : cSz t y + cSz t x + cSz t z = a + b + c
  cnt : units t x + j = u₀
  bal : (j = 0 ∧ cSz t y = a ∧ cSz t z = c) ∨
    (1 ≤ j ∧ cSz t y ≤ cSz t z + umax s.P ∧ cSz t z ≤ cSz t y + umax s.P)

/-- The chunk drive ended. -/
structure CDriveDone (X Y : Core → Prop) (s : Core) (L : List Nat) (δ δu s₀ : Nat → Nat) (x : Nat)
    (t : Core) : Prop where
  xx : X t ∨ Y t
  P : t.P = s.P
  ef : EFrame s t
  inv : ∃ A', INV t A' ∧ A'.elist = L
  ginv : ∃ gh, GInv t L gh (fun _ => 0)
  cinv : CInv t L (fun _ => 0) (fun _ => 0) s₀

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### Facts used by the step -/

theorem INV.no_group_of_empty {s : Core} {A : Abs} (hI : INV s A) {x : Nat} (hxL : LiveC s x)
    (he : cF s x = NIL) : ∀ g, LiveG s g → gC s g ≠ x := by
  intro g hg hgx
  have hgm := hI.mem_glist_iff.mpr hg
  have hgx' := hI.mem_grps_of_chk hgm hgx
  have hxm := (hI.cAlloc x).mpr hxL
  have hE := (hI.cEnds x hxm).1
  rw [he] at hE
  cases h : A.grps x with
  | nil => rw [h] at hgx'; simp only [List.not_mem_nil] at hgx'
  | cons a t =>
    rw [h] at hE; simp only [List.headD_eq_head?_getD, List.head?_cons, Option.getD_some] at hE
    exact hI.gList.nonil (hE ▸ A.grps_sub_glist hxm (h ▸ by simp))

theorem INV.celts_empty {s : Core} {A : Abs} (hI : INV s A) {x : Nat} (hxL : LiveC s x)
    (he : cF s x = NIL) : celts s A.elist x = [] := by
  unfold celts
  rw [List.filter_eq_nil_iff]
  intro e hel
  have := hI.no_group_of_empty hxL he _ (hI.mem_glist_iff.mp (hI.eG_mem hel))
  simpa using this

theorem CFamOK.lx {s : Core} {A : Abs} (hI : INV s A) {x : Nat} (F : CFamOK s x) (hxL : LiveC s x) :
    cLl s x ≠ x := by
  intro e; have := F.lAdj; rw [e] at this
  have hxm := (hI.cAlloc x).mpr hxL
  rw [hI.cList.next x hxm] at this
  exact succOf_ne_self hI.cList.nodup x (by unfold NIL; have := hxL.1; omega) this

theorem CFamOK.rx {s : Core} {A : Abs} (hI : INV s A) {x : Nat} (F : CFamOK s x) (hxL : LiveC s x) :
    cRr s x ≠ x := by
  intro e; have := F.rAdj; rw [e] at this
  have hxm := (hI.cAlloc x).mpr hxL
  rw [hI.cList.next x hxm] at this
  exact succOf_ne_self hI.cList.nodup x (by unfold NIL; have := hxL.1; omega) this

theorem CFamOK.lr {s : Core} {A : Abs} (hI : INV s A) {x : Nat} (F : CFamOK s x) (hxL : LiveC s x) :
    cLl s x ≠ cRr s x := by
  intro e
  have h1 := F.lAdj; have h2 := F.rAdj
  rw [e] at h1
  have hr' := (hI.cAlloc _).mpr F.rLive
  have hxm := (hI.cAlloc x).mpr hxL
  have hx0 : x ≠ NIL := by unfold NIL; have := hxL.1; omega
  obtain ⟨l1, l2, e1⟩ := succOf_split ((hI.cList.next _ hr').symm.trans h1) hx0
  rw [hI.cList.next x hxm, e1] at h2
  have hnd := hI.cList.nodup
  rw [e1] at hnd
  rw [show l1 ++ cRr s x :: x :: l2 = (l1 ++ [cRr s x]) ++ x :: l2 by simp,
    succOf_mid (by simpa using hnd)] at h2
  cases l2 with
  | nil =>
    have : cRr s x = NIL := by simpa using h2.symm
    exact hI.cList.nonil (this ▸ hr')
  | cons a t =>
    have ha : a = cRr s x := by simpa using h2
    rw [ha] at hnd
    have := (List.nodup_append.mp hnd).2.1
    simp only [List.nodup_cons, List.mem_cons, true_or, not_true_eq_false, false_and,
      or_true] at this

theorem CFamOK.radj {s : Core} {A : Abs} (hI : INV s A) {x : Nat} (F : CFamOK s x) (hxL : LiveC
  s x) :
    cP s (cRr s x) = x := by
  have hxm := (hI.cAlloc x).mpr hxL
  have hr0 : cRr s x ≠ NIL := by unfold NIL; have := F.rLive.1; omega
  obtain ⟨l1, l2, e⟩ := succOf_split ((hI.cList.next x hxm).symm.trans F.rAdj) hr0
  have hrm := (hI.cAlloc _).mpr F.rLive
  have e' : A.chunks = (l1 ++ [x]) ++ cRr s x :: l2 := by rw [e]; simp only [List.append_assoc,
      List.cons_append,
      List.nil_append]
  rw [hI.cList.prev _ hrm, e', predOf_mid (e' ▸ hI.cList.nodup)]; simp only [
      List.getLastD_eq_getLast?,
      List.getLast?_append,
      List.getLast?_singleton,
      Option.some_or,
      Option.getD_some]

/-- The units at an end of a chunk, as needed for a move. -/
theorem unit_facts {s : Core} {A : Abs} {gh : GGh} (hI : INV s A) (hG : GInv s A.elist gh (fun _
  => 0))
    (hP : GParams s.P) {x : Nat} {u : List Nat}
    (hu : (gSt s (u.headD NIL) = .quiet ∧ u = [u.headD NIL] ∧ LiveG s (u.headD NIL) ∧
        gC s (u.headD NIL) = x) ∨
      (∃ p, LiveG s p ∧ gSt s p = .splitting ∧ u = [gLl s p, p, gRr s p] ∧ gC s p = x)) :
    (u.length = 1 ∨ unitOK s x u = true → True) ∧ u.Nodup ∧ (∀ g ∈ u, LiveG s g ∧ gC s g = x) ∧
    (∃ um ∈ u, UnitG s x um ∧ ∀ g ∈ u, g ≠ um → gSt s g = .overflow) ∧ FamClosed s u ∧
    1 ≤ (u.map fun g => gSz s g).sum ∧ (u.map fun g => gSz s g).sum ≤ umax s.P := by
  rcases hu with ⟨hq, hu, hL, hx⟩ | ⟨p, hp, hps, hu, hpx⟩
  · generalize u.headD NIL = g0 at hq hu hL hx
    subst hu
    have hq0 := hG.quiet g0 hL hq
    refine ⟨fun _ => trivial, by simp, by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq, hL, hx, and_self], ⟨g0,
        by simp, ⟨hL, hx, by rw [hq]; simp⟩,
      by simp⟩, ?_, ?_, ?_⟩
    · intro p hp hps
      have F := hG.fam p hp hps
      have h1 : gLl s p ≠ g0 := fun e => by have := F.lSt; rw [e, hq] at this; cases this
      have h2 : p ≠ g0 := fun e => by rw [e, hq] at hps; cases hps
      have h3 : gRr s p ≠ g0 := fun e => by have := F.rSt; rw [e, hq] at this; cases this
      simp only [List.mem_cons, h1, List.not_mem_nil, or_self, h2, h3, and_self]
    · simpa using hq0.2.1
    · have := hq0.1; simp only [umax, kG]; simp only [add_zero, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, ge_iff_le] at this ⊢
      generalize s.P.G / (s.P.groupBudget - 1) = q at *; omega
  · subst hu
    have F := hG.fam p hp hps
    have hlp := F.lp hI hp
    have hrp := F.rp hI hp
    have hlr := F.lr hI hp
    refine ⟨fun _ => trivial, by
      simp only [List.nodup_cons, List.mem_cons, hlp, hlr, List.not_mem_nil, or_self,
        not_false_eq_true, Ne.symm hrp, List.nodup_nil, and_self], ?_,
      ⟨p, by simp, ⟨hp, hpx, by rw [hps]; simp⟩, ?_⟩, ?_, ?_, ?_⟩
    · intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl
      · exact ⟨F.lLive, by rw [F.lC, hpx]⟩
      · exact ⟨hp, hpx⟩
      · exact ⟨F.rLive, by rw [F.rC, hpx]⟩
    · intro g hg hgp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl
      · exact F.lSt
      · exact absurd rfl hgp
      · exact F.rSt
    · intro q hq hqs
      by_cases hqp : q = p
      · subst hqp; simp only [List.mem_cons, List.not_mem_nil, or_false, true_or, or_true,
          and_self]
      · obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8⟩ := F.disjoint (hG.fam q hq hqs) (Ne.symm hqp)
          hps hqs
        simp only [List.mem_cons, d3, d5, d4, List.not_mem_nil, or_self, d1, hqp, d2, d6, d8, d7,
            and_self]
    · obtain ⟨g1, -, -, -⟩ := (hG.split p hp hps hp.1).zero fun _ => rfl
      unfold famT at g1
      have := hP.G4
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, ge_iff_le];
        omega
    · have := hG.famT_le hP hp hps
      unfold famT at this
      simp only [umax, kG]; simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          add_zero, ge_iff_le]; omega

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
theorem GSame.of_C {s : Core} (C' : Array Chunk) : GSame s { s with C := C' } :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
   fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl, rfl⟩

theorem gsame_cremove (s : Core) (x : Nat) : GSame s (cremoveState s x) := by
  have h1 := GSame.of_C (s := s) (s.C.modify x deadC)
  have h2 := GSame.of_C (s := { s with C := s.C.modify x deadC })
    ((s.C.modify x deadC).modify (cLl s x) quietC)
  have h3 := GSame.of_C (s := { { s with C := s.C.modify x deadC } with
    C := (s.C.modify x deadC).modify (cLl s x) quietC })
    (((s.C.modify x deadC).modify (cLl s x) quietC).modify (cRr s x) quietC)
  exact h1.trans (h2.trans h3)

theorem pushBackLabs_len {s : Core} {center D B k : Nat} {prev : Option Nat} {labs : List Nat}
    (h : (pushBackLabs center D B prev k).run s = .ok labs s) : labs.length = k := by
  rcases pushBackLabs_run s center D B k prev with ⟨l, hl, hlen, -, -⟩ | ⟨msg, hl⟩
  · rw [h] at hl; cases hl; exact hlen
  · rw [h] at hl; cases hl

theorem pushFrontLabs_len {s : Core} {center D k : Nat} {nxt : Option Nat} {labs : List Nat}
    (h : (pushFrontLabs center D nxt k).run s = .ok labs s) : labs.length = k := by
  rcases pushFrontLabs_run s center D k nxt with ⟨l, hl, hlen, -, -⟩ | ⟨msg, hl⟩
  · rw [h] at hl; cases hl; exact hlen
  · rw [h] at hl; cases hl

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-- An empty source leaves both siblings within the common chunk and threshold bounds. -/
theorem CDriveInv.removal_bounds {X : Core → Prop} {s : Core} {L : List Nat}
    {δ δu s₀ : Nat → Nat} {x y z a b c u₀ j : Nat} {t : Core}
    (hD : CDriveInv X s L δ δu s₀ x y z a b c u₀ j t) (hCP : CParams t.P)
    (hThi : a + b + c ≤ t.P.T + kC t.P t.P.T)
    (hbal0 : a ≤ c + umax t.P + 1 ∧ c ≤ a + umax t.P + 1) (he : cF t x = NIL) :
    cSz t (cLl t x) ≤ cmax t.P ∧ cSz t (cRr t x) ≤ cmax t.P ∧
      cSz t (cLl t x) ≤ t.P.theta ∧ cSz t (cRr t x) ≤ t.P.theta := by
  obtain ⟨A, hI, hel⟩ := hD.inv
  subst hel
  have hcx : cSz t x = 0 := by
    rw [hD.cinv.csz x hD.live, hI.celts_empty hD.live he]
    rfl
  have hsum := hD.sum
  have hbal := hD.bal
  rw [← hD.ll, ← hD.rr] at hsum hbal
  rw [← hD.P] at hbal
  have hl : cSz t (cLl t x) ≤ cmax t.P := by
    unfold cmax
    rcases hbal with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;> omega
  have hr : cSz t (cRr t x) ≤ cmax t.P := by
    unfold cmax
    rcases hbal with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;> omega
  exact ⟨hl, hr, hl.trans hCP.I4, hr.trans hCP.I4⟩

theorem CDriveInv.step {X Y : Core → Prop} {s : Core} {L : List Nat} {δ δu s₀ : Nat → Nat}
    {x y z a b c u₀ j : Nat} {t : Core} (hXs : CXSteps X Y L δ δu s₀ x) (hP : GParams s.P)
    (hCP : CParams s.P) (hδ : ∀ c', c' ≠ y → c' ≠ x → c' ≠ z → δ c' = 0)
    (hThi : a + b + c ≤ s.P.T + kC s.P s.P.T)
    (hbal0 : a ≤ c + umax s.P + 1 ∧ c ≤ a + umax s.P + 1)
    (hfam0 : a + b + c ≤ δ y + δ x + δ z + s₀ x + unitsOf s.P (s₀ x) / (s.P.chunkBudget - 1))
    (hδs : δ y + δ x + δ z ≤ 1) (hs0T : s₀ x ≤ s.P.T)
    (hD : CDriveInv X s L δ δu s₀ x y z a b c u₀ j t) :
    ∃ t', ((chunkSplitStep x).run t = .ok true t' ∧
        CDriveInv X s L δ δu s₀ x y z a b c u₀ (j + 1) t') ∨
      ((chunkSplitStep x).run t = .ok false t' ∧ CDriveDone X Y s L δ δu s₀ x t') := by
  obtain ⟨A', hI', hel⟩ := hD.inv
  obtain ⟨gh, hG⟩ := hD.ginv
  subst hel
  have hPt := hD.P
  rw [← hPt] at hP hCP hThi hbal0 hfam0 hs0T
  have hC := hD.cinv
  have Fx := hC.cfam x hD.live hD.st
  have hxy : cLl t x ≠ x := Fx.lx hI' hD.live
  have hxz : cRr t x ≠ x := Fx.rx hI' hD.live
  have hyz : cLl t x ≠ cRr t x := Fx.lr hI' hD.live
  have hsum := hD.sum
  have hcnt := hD.cnt
  have hbal := hD.bal
  rw [← hD.ll, ← hD.rr] at hsum hbal hδ hfam0 hδs
  rw [← hPt] at hbal
  have hFB : FamBound t δ s₀ x := ⟨by omega, hδs, hs0T⟩
  by_cases he : cF t x = NIL
  · -- removal
    obtain ⟨hszy', hszz', hszy, hszz⟩ := hD.removal_bounds hCP hThi hbal0 he
    have hrun := chunkSplitStep_remove he hyz hxy hxz hD.live.2 ⟨Fx.lSt, Fx.lSrc⟩ ⟨Fx.rSt, Fx.rSrc⟩
      hszy hszz
    obtain ⟨hef, A'', hI'', hel''⟩ := Good.ok_inv (good_chunkSplitStep x) hI' hrun
    refine ⟨_, Or.inr ⟨hrun, ⟨Or.inr (hXs.rem t A' gh hI' rfl hG hC hD.live hD.st he hszy' hszz'
      hFB hD.xx),
      hef.P.trans hPt, hD.ef.trans hef, ⟨A'', hI'', hel''⟩,
      ⟨gh, hG.of_gsame (gsame_cremove t x)⟩, ?_⟩⟩⟩
    exact cinv_cremove hI' hC hD.live hD.st he hδ
  · -- a move
    obtain ⟨hxc, t0, ht0⟩ := hI'.run_ne_nil he
    have hg0 : cF t x ∈ A'.glist := A'.grps_sub_glist hxc (by rw [ht0]; simp)
    have hg0L := hI'.mem_glist_iff.mp hg0
    have hg0x : gC t (cF t x) = x := hI'.chk x hxc _ (by rw [ht0]; simp)
    by_cases hdir : cSz t (cLl t x) ≤ cSz t (cRr t x)
    · have lu := left_unit hI' hG he
      have hu : (unitCand t x true).length = 1 ∨ unitOK t x (unitCand t x true) = true := by
        rcases lu with ⟨-, h⟩ | ⟨p, -, -, -, -, h⟩
        · left; rw [h]; rfl
        · right; exact h
      obtain ⟨labs, hlabs, hX'⟩ := hXs.moveL t A' gh hI' rfl hG hC hD.live hD.st he hdir hFB hD.xx
      have hrun := chunkSplitStep_left he hdir hu Fx.lAdj hlabs
      obtain ⟨hef, A'', hI'', hel''⟩ := Good.ok_inv (good_chunkSplitStep x) hI' hrun
      have hlen : labs.length = (unitCand t x true).length := pushBackLabs_len hlabs
      have UF := unit_facts (u := unitCand t x true) (x := x) hI' hG hP (by
        rcases lu with ⟨hq, h⟩ | ⟨p, hp, hps, hl, h, hok⟩
        · left; rw [h]; exact ⟨hq, rfl, hg0L, hg0x⟩
        · right
          refine ⟨p, hp, hps, by rw [h, hl], ?_⟩
          rw [h] at hok; exact (unitOK_three hok).2.2.2.2.1)
      obtain ⟨-, hnd, hmem, hone, hcl, hm1, hm2⟩ := UF
      have M := cmoveL_spec (s := t) (x := x) (u := unitCand t x true) (labs := labs)
        (Ne.symm hxy) hD.live.2 Fx.lLive.2 hnd hlen (fun g hg => (hmem g hg).1.2.1)
      have hG' := ginv_cmove hG M hcl
      obtain ⟨hC', hun, hle⟩ := cinv_cmove hG hC M hD.live hD.st (Or.inl rfl) (Ne.symm hxy)
        hmem hnd hone
      refine ⟨_, Or.inl ⟨hrun, ⟨hX', hef.P.trans hPt, hD.ef.trans hef, ⟨A'', hI'', hel''⟩,
        ⟨gh, hG'⟩, hC', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩⟩
      · simp only [LiveC, M.Csize]; exact hD.live
      · rw [M.cst]; exact hD.st
      · rw [M.cl]; exact hD.ll
      · rw [M.cr]; exact hD.rr
      · rw [← hD.ll, ← hD.rr, M.csz, M.csz, M.csz, ite_eq_right hxy, ite_eq_left rfl,
        ite_eq_left rfl,
          ite_eq_right hxz, ite_eq_right (Ne.symm hyz)]
        omega
      · omega
      · right
        rw [← hD.ll, ← hD.rr, M.csz, M.csz, ite_eq_right hxy, ite_eq_left rfl, ite_eq_right hxz,
          ite_eq_right (Ne.symm hyz), ← hPt]
        refine ⟨by omega, ?_, ?_⟩ <;> rcases hbal with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;> omega
    · have ru := right_unit hI' hG he
      have hu : (unitCand t x false).length = 1 ∨ unitOK t x (unitCand t x false) = true := by
        rcases ru with ⟨-, h⟩ | ⟨p, -, -, -, -, h⟩
        · left; rw [h]; rfl
        · right; exact h
      have hdir' : cSz t (cRr t x) < cSz t (cLl t x) := by omega
      obtain ⟨labs, hlabs, hX'⟩ := hXs.moveR t A' gh hI' rfl hG hC hD.live hD.st he hdir' hFB hD.xx
      have hrun := chunkSplitStep_right he hdir' hu (Fx.radj hI' hD.live) hlabs
      obtain ⟨hef, A'', hI'', hel''⟩ := Good.ok_inv (good_chunkSplitStep x) hI' hrun
      have hlen : labs.length = (unitCand t x false).length := pushFrontLabs_len hlabs
      obtain ⟨hxc', tl, htl⟩ := hI'.run_ne_nil he
      have hE := hI'.cEnds x hxc'
      have hlm : cLs t x ∈ A'.grps x := by rw [hE.2, htl]; exact getLastD_cons_mem _ _ _
      have hgl : cLs t x ∈ A'.glist := A'.grps_sub_glist hxc' hlm
      have UF := unit_facts (u := unitCand t x false) (x := x) hI' hG hP (by
        rcases ru with ⟨hq, h⟩ | ⟨p, hp, hps, hr, h, hok⟩
        · left; rw [h]
          exact ⟨hq, rfl, hI'.mem_glist_iff.mp hgl, hI'.chk x hxc' _ hlm⟩
        · right
          refine ⟨p, hp, hps, by rw [h, hr], ?_⟩
          rw [h] at hok; exact (unitOK_three hok).2.2.2.2.1)
      obtain ⟨-, hnd, hmem, hone, hcl, hm1, hm2⟩ := UF
      have M := cmoveR_spec (s := t) (x := x) (u := unitCand t x false) (labs := labs)
        (Ne.symm hxz) hD.live.2 Fx.rLive.2 hnd hlen (fun g hg => (hmem g hg).1.2.1)
      have hG' := ginv_cmove hG M hcl
      obtain ⟨hC', hun, hle⟩ := cinv_cmove hG hC M hD.live hD.st (Or.inr rfl) (Ne.symm hxz)
        hmem hnd hone
      refine ⟨_, Or.inl ⟨hrun, ⟨hX', hef.P.trans hPt, hD.ef.trans hef, ⟨A'', hI'', hel''⟩,
        ⟨gh, hG'⟩, hC', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩⟩
      · simp only [LiveC, M.Csize]; exact hD.live
      · rw [M.cst]; exact hD.st
      · rw [M.cl]; exact hD.ll
      · rw [M.cr]; exact hD.rr
      · rw [← hD.ll, ← hD.rr, M.csz, M.csz, M.csz, ite_eq_right hxy, ite_eq_right hyz,
        ite_eq_left rfl,
          ite_eq_right hxz, ite_eq_left rfl]
        omega
      · omega
      · right
        rw [← hD.ll, ← hD.rr, M.csz, M.csz, ite_eq_right hxy, ite_eq_right hyz, ite_eq_right hxz,
          ite_eq_left rfl, ← hPt]
        refine ⟨by omega, ?_, ?_⟩ <;> rcases hbal with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;> omega

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-- Closing a chunk drive: C1 holds again for the family of `x`, and nothing else was exempt. -/
theorem CInvE.close {s : Core} {L : List Nat} {δ δu s₀ : Nat → Nat} {x : Nat}
    (hC : CInvE s L δ δu s₀ x) (hxL : LiveC s x) (hst : cSt s x = .splitting)
    (hδ : ∀ c, c ≠ cLl s x → c ≠ x → c ≠ cRr s x → δ c = 0)
    (hC1 : C1 s (fun _ => 0) (fun _ => 0) s₀ x) : CInv s L (fun _ => 0) (fun _ => 0) s₀ := by
  have Fx := hC.cfam x hxL hst
  refine { hC with c1 := ?_, δu := fun _ => le_rfl }
  intro y hy hys _
  by_cases hyx : y = x
  · subst hyx; exact hC1
  · have Fy := hC.cfam y hy hys
    obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8⟩ := Fx.disjoint Fy (Ne.symm hyx) hst hys
    have := hC.c1 y hy hys hyx
    have hδy : δ y = 0 := hδ y d1 hyx d2
    have hδu : δu y = 0 := by have := hC.δu y; omega
    unfold C1 at this ⊢
    rw [hδ _ d5 d3 d6, hδy, hδ _ d7 d4 d8, hδu] at this
    simpa using this

/-- **Lemmas C1 and C2 for one chunk drive.** Driving the family of `x` after at most one undriven
insertion into it ends with the chunk invariant restored (no undriven insertion): either `x` has
made `chunkBudget` moves and C1 holds again, or `x` was removed and its siblings are quiet
  chunks of size at
most `c_max ≤ θ`. -/
theorem cinv_drive {X Y : Core → Prop} {s : Core} {A : Abs} {gh : GGh} {δ δu s₀ : Nat → Nat} {x
  : Nat}
    (hI : INV s A) (hG : GInv s A.elist gh (fun _ => 0)) (hC : CInvE s A.elist δ δu s₀ x)
    (hC1 : C1 s δ δu s₀ x) (hXs : CXSteps X Y A.elist δ δu s₀ x) (hX : X s) (hP : GParams s.P)
    (hCP : CParams s.P) (hxL : LiveC s x) (hst : cSt s x = .splitting)
    (hδ : ∀ c, c ≠ cLl s x → c ≠ x → c ≠ cRr s x → δ c = 0)
    (hδs : δ (cLl s x) + δ x + δ (cRr s x) ≤ 1)
    (hδle : δ (cLl s x) ≤ cSz s (cLl s x) ∧ δ x ≤ cSz s x ∧ δ (cRr s x) ≤ cSz s (cRr s x)) :
    ∃ s', (driveChunkFrom x).run s = .ok () s' ∧ CDriveDone X Y s A.elist δ δu s₀ x s' := by
  have hBounds := hC1.drive_bounds hCP.K2 hδs hδle
  generalize hl : cLl s x = y at *
  generalize hr : cRr s x = z at *
  generalize ha : cSz s y = a at *
  generalize hb : cSz s x = b at *
  generalize hc : cSz s z = c at *
  obtain ⟨hThi, hbal0, hfam0⟩ := hBounds
  have hK2 := hCP.K2
  unfold C1 at hC1
  rw [hl, hr, ha, hb, hc] at hC1
  obtain ⟨hs0T, g1, g2, g3, g4⟩ := hC1
  generalize hσ : s₀ x = σ at hs0T g1 g2
  generalize hm : s.P.chunkBudget - 1 = m at g2
  generalize hX0 : (a - δ y) + (b - δ x) + (c - δ z) - σ = Xs at g2
  obtain ⟨t, hrun, hres⟩ := driveChunkFrom_ok (s := s) (x := x)
    (fun j t => CDriveInv X s A.elist δ δu s₀ x y z a b c (units s x) j t)
    (CDriveDone X Y s A.elist δ δu s₀ x)
    ⟨hX, rfl, EFrame.refl s, ⟨A, hI, rfl⟩, ⟨gh, hG⟩, hC, hxL, hst, hl, hr, by omega, by omega,
      Or.inl ⟨rfl, ha, hc⟩⟩
    (fun j t hD _ => hD.step hXs hP hCP (by intro c' h1 h2 h3; exact hδ c' h1 h2 h3) hThi hbal0
      hfam0 hδs (by rw [hσ]; exact hs0T))
  refine ⟨t, hrun, ?_⟩
  rcases hres with hD | hD
  · refine ⟨Or.inl hD.xx, hD.P, hD.ef, hD.inv, hD.ginv, hD.cinv.close hD.live hD.st ?_ ?_⟩
    · rw [hD.ll, hD.rr]; exact hδ
    · have hsum := hD.sum
      have hcnt := hD.cnt
      have hbal := hD.bal
      have hKm : s.P.chunkBudget = m + 1 := by omega
      rw [hKm] at hcnt
      have hbalK : cSz t y ≤ cSz t z + umax s.P ∧ cSz t z ≤ cSz t y + umax s.P := by
        rcases hbal with ⟨h0, -⟩ | ⟨-, h1, h2⟩
        · omega
        · exact ⟨h1, h2⟩
      unfold C1
      simp only [Nat.sub_zero]
      rw [hD.ll, hD.rr, hD.P, hm, hσ]
      refine ⟨hs0T, ?_⟩
      refine ⟨by omega, ?_, hbalK.1, hbalK.2⟩
      have hT : cSz t y + cSz t x + cSz t z - σ = Xs + (δ y + δ x + δ z) := by omega
      rw [hT, Nat.mul_add]
      have hδux := hC.δu x
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hδs with h0 | h1
      · rw [h0, Nat.mul_zero]; omega
      · rw [h1, Nat.mul_one]; omega
  · exact hD

end OrderMaintenance.Proof
