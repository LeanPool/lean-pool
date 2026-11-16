/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Cost.GSteps


/-!
# Split moves and group removal
-/


@[expose] public section

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### Split moves -/

section moves
variable (s : Core) (p : Nat)

/-- The label of the element moved to the left sibling. -/
def labMoveL : Nat :=
  if gF s (gLl s p) = NIL then cE s.P else eL s (gLs s (gLl s p)) + s.P.elementSpacing

/-- The label of the element moved to the right sibling. -/
def labMoveR : Nat :=
  if gF s (gRr s p) = NIL then cE s.P else eL s (gF s (gRr s p)) - s.P.elementSpacing

/-- Transfers one element from the source group count to the destination group count. -/
def sizeAdj (s : Core) (a b : Nat) : Core :=
  let s2 := { s with Gs := s.Gs.modify a fun X => { X with size := X.size - 1 } }
  { s2 with Gs := s2.Gs.modify b fun X => { X with size := X.size + 1 } }

/-- The state after moving the first element of `p` to its left sibling. -/
def moveLState : Core :=
  sizeAdj (moveFirstLeft s p (gLl s p) (gF s p) (labMoveL s p)) p (gLl s p)

/-- The state after moving the last element of `p` to its right sibling. -/
def moveRState : Core :=
  sizeAdj (moveLastRight s p (gRr s p) (gLs s p) (labMoveR s p)) p (gRr s p)

end moves

/-- What a successful left move needs: `p` alive and non-empty, the left sibling lighter and
adjacent, and room for a pushed label. -/
structure MoveLOK (s : Core) (p : Nat) : Prop where
  live : LiveG s p
  ne : gF s p ≠ NIL
  dir : gSz s (gLl s p) ≤ gSz s (gRr s p)
  adj : gN s (gLl s p) = p
  room : gF s (gLl s p) ≠ NIL → eL s (gLs s (gLl s p)) + s.P.elementSpacing < 1 <<< s.P.elementBits
  D : 0 < s.P.elementSpacing
  chk : gC s (gLl s p) = gC s p

/-- Conditions for moving right: a live nonempty source, adjacent lighter sibling and label room. -/
structure MoveROK (s : Core) (p : Nat) : Prop where
  live : LiveG s p
  ne : gF s p ≠ NIL
  dir : gSz s (gRr s p) < gSz s (gLl s p)
  adj : gP s (gRr s p) = p
  room : gF s (gRr s p) ≠ NIL → s.P.elementSpacing ≤ eL s (gF s (gRr s p))
  D : 0 < s.P.elementSpacing
  chk : gC s (gRr s p) = gC s p

theorem getX_modify_chk (a : Array Group) (i j : Nat) (f : Group → Group)
    (hf : ∀ X, (f X).chk = X.chk) : ((a.modify i f).getX j).chk = (a.getX j).chk := by
  rw [Array.getX_modify]
  by_cases h : i = j ∧ i < a.size
  · rw [ite_eq_left h, hf]
  · rw [ite_eq_right h]

/-- `groupSplitStep` after a successful move into a sibling in the same chunk. -/
theorem groupSplitStep_tail {s s1 : Core} {p d : Nat} (hm : (moveElem p).run s = .ok d s1)
    (hne : gF s p ≠ NIL) (hc : (p != NIL && decide (p < s.Gs.size) && (s.Gs.getX p).alive) = true)
    (hchk : (s1.Gs.getX d).chk = (s.Gs.getX p).chk) :
    (groupSplitStep p).run s = .ok true (sizeAdj s1 p d) := by
  unfold groupSplitStep
  rw [run_getG_bind, run_get_bind, run_require_bind, ite_eq_left hc,
    ite_eq_right (fun h => hne (beq_iff_eq.mp h)), run_bind, hm]
  dsimp only
  unfold modG
  rw [run_modify_bind, run_modify_bind, run_getG_bind]
  rw [getX_modify_chk _ _ _ (fun X => { X with size := X.size + 1 }) (fun _ => rfl),
    getX_modify_chk _ _ _ (fun X => { X with size := X.size - 1 }) (fun _ => rfl), hchk]
  rw [bne_self_eq_false, ite_eq_right Bool.false_ne_true]
  rfl

theorem moveElem_left {s : Core} {p : Nat} (h : MoveLOK s p) :
    (moveElem p).run s = .ok (gLl s p) (moveFirstLeft s p (gLl s p) (gF s p) (labMoveL s p)) := by
  obtain ⟨⟨h0, hs, ha⟩, hne, hdir, hadj, hroom, hD, -⟩ := h
  unfold moveElem
  simp only [run_getP_bind, run_getG_bind, run_get_bind, run_require_bind]
  have hc' : (p != NIL && decide (p < s.Gs.size) && (s.Gs.getX p).alive &&
      (s.Gs.getX p).first != NIL) = true := by
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
    exact ⟨⟨⟨h0, hs⟩, ha⟩, hne⟩
  rw [ite_eq_left hc', ite_eq_left hdir, run_require_bind, ite_eq_left (beq_iff_eq.mpr hadj)]
  unfold labMoveL
  by_cases he : gF s (gLl s p) = NIL
  · rw [ite_eq_left (beq_iff_eq.mpr he), ite_eq_left he]; rfl
  · rw [ite_eq_right (fun h => he (beq_iff_eq.mp h)), ite_eq_right he]
    simp only [run_getE_bind]
    rw [run_bind, run_after]
    have := hroom he
    simp only [eL, gLs, gLl, gF] at this he ⊢
    rw [ite_eq_right (by omega)]
    rfl

theorem moveElem_right {s : Core} {p : Nat} (h : MoveROK s p) :
    (moveElem p).run s = .ok (gRr s p) (moveLastRight s p (gRr s p) (gLs s p) (labMoveR s p)) := by
  obtain ⟨⟨h0, hs, ha⟩, hne, hdir, hadj, hroom, hD, -⟩ := h
  unfold moveElem
  simp only [run_getP_bind, run_getG_bind, run_get_bind, run_require_bind]
  have hc' : (p != NIL && decide (p < s.Gs.size) && (s.Gs.getX p).alive &&
      (s.Gs.getX p).first != NIL) = true := by
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
    exact ⟨⟨⟨h0, hs⟩, ha⟩, hne⟩
  rw [ite_eq_left hc', ite_eq_right (by simp only [gSz, gLl, gRr] at hdir ⊢; omega),
    run_require_bind,
    ite_eq_left (beq_iff_eq.mpr hadj)]
  unfold labMoveR
  by_cases he : gF s (gRr s p) = NIL
  · rw [ite_eq_left (beq_iff_eq.mpr he), ite_eq_left he]; rfl
  · rw [ite_eq_right (fun h => he (beq_iff_eq.mp h)), ite_eq_right he]
    simp only [run_getE_bind]
    rw [run_bind, run_before]
    have := hroom he
    simp only [eL, gF, gRr] at this he ⊢
    rw [ite_eq_right (by omega)]
    rfl

theorem LiveG.cond {s : Core} {p : Nat} (h : LiveG s p) :
    (p != NIL && decide (p < s.Gs.size) && (s.Gs.getX p).alive) = true := by
  obtain ⟨h0, hs, ha⟩ := h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]; exact ⟨⟨h0, hs⟩, ha⟩

theorem groupSplitStep_left {s : Core} {p : Nat} (h : MoveLOK s p) :
    (groupSplitStep p).run s = .ok true (moveLState s p) := by
  refine groupSplitStep_tail (moveElem_left h) h.ne h.live.cond ?_
  have := (moveFirstLeft_same (s := s) (g := p) (gl := gLl s p) (e := gF s p)
    (lab := labMoveL s p)).2.2.1 (gLl s p)
  have hc := h.chk
  simp only [gC] at this hc
  rw [this, hc]

theorem groupSplitStep_right {s : Core} {p : Nat} (h : MoveROK s p) :
    (groupSplitStep p).run s = .ok true (moveRState s p) := by
  refine groupSplitStep_tail (moveElem_right h) h.ne h.live.cond ?_
  have := (moveLastRight_same (s := s) (g := p) (gr := gRr s p) (e := gLs s p)
    (lab := labMoveR s p)).2.2.1 (gRr s p)
  have hc := h.chk
  simp only [gC] at this hc
  rw [this, hc]

/-- Finishes a group split by clearing its state and source pointer. -/
def quietG (X : Group) : Group := { X with st := .quiet, src := NIL }

/-- Unlinks an emptied source group and returns its siblings to the quiet state. -/
def removeState (s : Core) (p : Nat) : Core :=
  let s1 := unlinkGroup s p
  let s2 := { s1 with Gs := s1.Gs.modify (gLl s p) quietG }
  { s2 with Gs := s2.Gs.modify (gRr s p) quietG }

theorem unlinkGroup_getX_lr (s : Core) (p z : Nat) :
    ((unlinkGroup s p).Gs.getX z).l = (s.Gs.getX z).l ∧ ((unlinkGroup s p).Gs.getX z).r =
      (s.Gs.getX z).r ∧
    ((unlinkGroup s p).Gs.getX z).st = (s.Gs.getX z).st ∧ ((unlinkGroup s p).Gs.getX z).src =
      (s.Gs.getX z).src ∧
    ((unlinkGroup s p).Gs.getX z).size = (s.Gs.getX z).size ∧ (unlinkGroup s p).P = s.P := by
  refine ⟨?_, ?_, ?_, ?_, ?_, rfl⟩ <;>
    simp only [unlinkGroup, Array.getX_modify, Array.getX_ite, Array.size_modify',
      Array.size_ite] <;>
    split_ifs <;> rfl

@[simp] theorem run_getG' (i : Nat) (s : Core) : (getG i).run s = .ok (s.Gs.getX i) s := rfl
@[simp] theorem run_getP' (s : Core) : (getP).run s = .ok s.P s := rfl

theorem removeGroup_ok {s : Core} {p : Nat} (hp : LiveG s p) (he : gF s p = NIL)
    (hlr : gLl s p ≠ gRr s p)
    (hl : gSt s (gLl s p) = .overflow ∧ gSrc s (gLl s p) = p)
    (hr : gSt s (gRr s p) = .overflow ∧ gSrc s (gRr s p) = p)
    (hszl : gSz s (gLl s p) < s.P.G) (hszr : gSz s (gRr s p) < s.P.G) :
    (removeGroup p).run s = .ok () (removeState s p) := by
  obtain ⟨h0, hs, ha⟩ := hp
  unfold removeGroup
  have hu : (unlinkStep p).run s = .ok () (unlinkGroup s p) := by
    rcases unlinkStep_run s p with ⟨-, -, -, -, h⟩ | ⟨msg, h⟩
    · exact h
    · exfalso; revert h; unfold unlinkStep
      simp only [run_getG_bind, run_get_bind, run_require_bind]
      rw [ite_eq_left (by
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, beq_iff_eq]
        exact ⟨⟨⟨h0, hs⟩, ha⟩, he⟩)]
      simp
  rw [run_bind, hu]
  dsimp only
  obtain ⟨u1, u2, -, -, -, uP⟩ := unlinkGroup_getX_lr s p p
  obtain ⟨-, -, l3, l4, l5, -⟩ := unlinkGroup_getX_lr s p (gLl s p)
  obtain ⟨-, -, r3, r4, r5, -⟩ := unlinkGroup_getX_lr s p (gRr s p)
  simp only [gLl, gRr, gSt, gSrc, gSz] at l3 l4 l5 r3 r4 r5 hl hr hlr hszl hszr
  have nl : ¬ s.P.G ≤ (s.Gs.getX (s.Gs.getX p).l).size := by omega
  have nr : ¬ s.P.G ≤ (s.Gs.getX (s.Gs.getX p).r).size := by omega
  simp [modG, Array.getX_modify, u1, u2, l3, l4, l5, r3, r4, r5, hl, hr, hlr, Ne.symm hlr, uP,
    List.forIn_cons, apply_ite (f := Group.size), nl, nr]
  rfl

theorem groupSplitStep_remove {s : Core} {p : Nat} (hp : LiveG s p) (he : gF s p = NIL)
    (hlr : gLl s p ≠ gRr s p)
    (hl : gSt s (gLl s p) = .overflow ∧ gSrc s (gLl s p) = p)
    (hr : gSt s (gRr s p) = .overflow ∧ gSrc s (gRr s p) = p)
    (hszl : gSz s (gLl s p) < s.P.G) (hszr : gSz s (gRr s p) < s.P.G) :
    (groupSplitStep p).run s = .ok false (removeState s p) := by
  unfold groupSplitStep
  rw [run_getG_bind, run_get_bind, run_require_bind, ite_eq_left hp.cond,
    ite_eq_left (beq_iff_eq.mpr he),
    run_bind, removeGroup_ok hp he hlr hl hr hszl hszr]
  rfl

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### Runs of adjacent groups -/

/-- Two adjacent groups' runs are adjacent in the element list. -/
theorem INV.runs_adj {s : Core} {A : Abs} (hI : INV s A) {l p : Nat} (hl : l ∈ A.glist)
    (hadj : gN s l = p) (hp0 : p ≠ NIL) :
    ∃ X Y, A.elist = X ++ runOf s A.elist l ++ runOf s A.elist p ++ Y ∧
      ∀ z ∈ X ++ Y, eG s z ≠ l ∧ eG s z ≠ p := by
  have hnd := hI.gList.nodup
  obtain ⟨g1, g2, e⟩ := succOf_split ((hI.gList.next l hl).symm.trans hadj) hp0
  refine ⟨(g1.map (runOf s A.elist)).flatten, (g2.map (runOf s A.elist)).flatten, ?_, ?_⟩
  · conv_lhs => rw [hI.elist_runs, e]
    simp
  · rw [e] at hnd
    have hd := (List.nodup_append.mp hnd)
    have hl1 : l ∉ g1 := fun h => hd.2.2 l h l (by simp) rfl
    have hp1 : p ∉ g1 := fun h => hd.2.2 p h p (by simp) rfl
    have h2 := List.nodup_cons.mp (List.nodup_cons.mp hd.2.1).2
    have hl2 : l ∉ g2 := fun h => (List.nodup_cons.mp hd.2.1).1 (by simp [h])
    have hp2 : p ∉ g2 := h2.1
    intro z hz
    simp only [List.mem_append, List.mem_flatten, List.mem_map] at hz
    rcases hz with ⟨_, ⟨b, hb, rfl⟩, hzb⟩ | ⟨_, ⟨b, hb, rfl⟩, hzb⟩
    · rw [(mem_runOf.mp hzb).2]
      exact ⟨fun h => hl1 (h ▸ hb), fun h => hp1 (h ▸ hb)⟩
    · rw [(mem_runOf.mp hzb).2]
      exact ⟨fun h => hl2 (h ▸ hb), fun h => hp2 (h ▸ hb)⟩

theorem filter_nil_of {p : Nat → Bool} {L : List Nat} (h : ∀ z ∈ L, p z = false) :
    L.filter p = [] := List.filter_eq_nil_iff.mpr fun z hz => by simp [h z hz]

theorem nodup_mid {A B : List Nat} {e : Nat} (h : (A ++ e :: B).Nodup) : e ∉ A ∧ e ∉ B :=
  ⟨fun hA => (List.nodup_append.mp h).2.2 e hA e (by simp) rfl,
   (List.nodup_cons.mp (List.nodup_append.mp h).2.1).1⟩

/-- Moving element `e` from the front of `p`'s run to the end of the adjacent `l`'s run. -/
theorem runOf_moveFront {s s' : Core} {L X Y rest : List Nat} {l p e : Nat}
    (hL : L = X ++ runOf s L l ++ (e :: rest) ++ Y)
    (hXY : ∀ z ∈ X ++ Y, eG s z ≠ l ∧ eG s z ≠ p) (hrest : ∀ z ∈ rest, eG s z = p)
    (hRl : ∀ z ∈ runOf s L l, eG s z = l) (he : eG s e = p) (hlp : l ≠ p)
    (hnd : L.Nodup) (heG : ∀ z, eG s' z = if z = e then l else eG s z) (b : Nat) :
    runOf s' L b = if b = l then runOf s L l ++ [e] else if b = p then rest else runOf s L b := by
  generalize hR : runOf s L l = R at hL hRl
  have hnd' := hnd
  rw [hL, show X ++ R ++ e :: rest ++ Y = (X ++ R) ++ e :: (rest ++ Y) by simp] at hnd'
  obtain ⟨h1, h2⟩ := nodup_mid hnd'
  simp only [List.mem_append, not_or] at h1 h2
  have hfilt : ∀ {M : List Nat} (q : Nat), e ∉ M →
      M.filter (fun z => decide (eG s' z = q)) = M.filter (fun z => decide (eG s z = q)) := by
    intro M q hM
    exact List.filter_congr fun z hz => by rw [heG, ite_eq_right (fun (h : z = e) => hM (h ▸ hz))]
  unfold runOf
  rw [hL]
  simp only [List.filter_append, List.filter_cons]
  rw [hfilt b h1.1, hfilt b h1.2, hfilt b h2.1, hfilt b h2.2, heG, ite_eq_left rfl]
  have hXn : ∀ q, q = l ∨ q = p → X.filter (fun z => decide (eG s z = q)) = [] := by
    intro q hq; refine filter_nil_of fun z hz => ?_
    have := hXY z (by simp [hz]); rcases hq with rfl | rfl <;> simp [this.1, this.2]
  have hYn : ∀ q, q = l ∨ q = p → Y.filter (fun z => decide (eG s z = q)) = [] := by
    intro q hq; refine filter_nil_of fun z hz => ?_
    have := hXY z (by simp [hz]); rcases hq with rfl | rfl <;> simp [this.1, this.2]
  by_cases hbl : b = l
  · subst hbl
    have hRe : R.filter (fun z => decide (eG s z = b)) = R :=
      List.filter_eq_self.mpr fun z hz => by simp [hRl z hz]
    have hrn : rest.filter (fun z => decide (eG s z = b)) = [] :=
      filter_nil_of fun z hz => by simp [hrest z hz, Ne.symm hlp]
    rw [hXn b (Or.inl rfl), hYn b (Or.inl rfl), hRe, hrn]
    simp
  · by_cases hbp : b = p
    · subst hbp
      have hRn : R.filter (fun z => decide (eG s z = b)) = [] :=
        filter_nil_of fun z hz => by simp [hRl z hz, hlp]
      have hre : rest.filter (fun z => decide (eG s z = b)) = rest :=
        List.filter_eq_self.mpr fun z hz => by simp [hrest z hz]
      rw [hXn b (Or.inr rfl), hYn b (Or.inr rfl), hRn, hre]
      simp [hlp, Ne.symm hlp]
    · simp only [ite_eq_right hbl, ite_eq_right hbp, he, Ne.symm hbl, Ne.symm hbp, decide_false]

/-- Moving element `e` from the back of `p`'s run to the front of the adjacent `r`'s run. -/
theorem runOf_moveBack {s s' : Core} {L X Y front : List Nat} {p r e : Nat}
    (hL : L = X ++ (front ++ [e]) ++ runOf s L r ++ Y)
    (hXY : ∀ z ∈ X ++ Y, eG s z ≠ p ∧ eG s z ≠ r) (hfront : ∀ z ∈ front, eG s z = p)
    (hRr : ∀ z ∈ runOf s L r, eG s z = r) (he : eG s e = p) (hpr : p ≠ r)
    (hnd : L.Nodup) (heG : ∀ z, eG s' z = if z = e then r else eG s z) (b : Nat) :
    runOf s' L b = if b = r then e :: runOf s L r else if b = p then front else runOf s L b := by
  generalize hR : runOf s L r = R at hL hRr
  have hnd' := hnd
  rw [hL, show X ++ (front ++ [e]) ++ R ++ Y = (X ++ front) ++ e :: (R ++ Y) by simp] at hnd'
  obtain ⟨h1, h2⟩ := nodup_mid hnd'
  simp only [List.mem_append, not_or] at h1 h2
  have hfilt : ∀ {M : List Nat} (q : Nat), e ∉ M →
      M.filter (fun z => decide (eG s' z = q)) = M.filter (fun z => decide (eG s z = q)) := by
    intro M q hM
    exact List.filter_congr fun z hz => by rw [heG, ite_eq_right (fun (h : z = e) => hM (h ▸ hz))]
  unfold runOf
  rw [hL]
  simp only [List.filter_append, List.filter_cons, List.filter_nil]
  rw [hfilt b h1.1, hfilt b h1.2, hfilt b h2.1, hfilt b h2.2, heG, ite_eq_left rfl]
  have hXn : ∀ q, q = p ∨ q = r → X.filter (fun z => decide (eG s z = q)) = [] := by
    intro q hq; refine filter_nil_of fun z hz => ?_
    have := hXY z (by simp [hz]); rcases hq with rfl | rfl <;> simp [this.1, this.2]
  have hYn : ∀ q, q = p ∨ q = r → Y.filter (fun z => decide (eG s z = q)) = [] := by
    intro q hq; refine filter_nil_of fun z hz => ?_
    have := hXY z (by simp [hz]); rcases hq with rfl | rfl <;> simp [this.1, this.2]
  by_cases hbr : b = r
  · subst hbr
    have hfn : front.filter (fun z => decide (eG s z = b)) = [] :=
      filter_nil_of fun z hz => by simp [hfront z hz, hpr]
    have hRe : R.filter (fun z => decide (eG s z = b)) = R :=
      List.filter_eq_self.mpr fun z hz => by simp [hRr z hz]
    rw [hXn b (Or.inr rfl), hYn b (Or.inr rfl), hfn, hRe]
    simp
  · by_cases hbp : b = p
    · subst hbp
      have hfe : front.filter (fun z => decide (eG s z = b)) = front :=
        List.filter_eq_self.mpr fun z hz => by simp [hfront z hz]
      have hRn : R.filter (fun z => decide (eG s z = b)) = [] :=
        filter_nil_of fun z hz => by simp [hRr z hz, Ne.symm hpr]
      rw [hXn b (Or.inl rfl), hYn b (Or.inl rfl), hfe, hRn]
      simp [hpr, Ne.symm hpr]
    · simp only [ite_eq_right hbr, ite_eq_right hbp, he, Ne.symm hbr, Ne.symm hbp, decide_false]

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### The records after a move -/

theorem sizeAdj_getX (t : Core) (a b z : Nat) (hab : a ≠ b) (ha : a < t.Gs.size) (hb : b <
  t.Gs.size) :
    (sizeAdj t a b).Gs.getX z =
      if z = a then { t.Gs.getX z with size := (t.Gs.getX z).size - 1 }
      else if z = b then { t.Gs.getX z with size := (t.Gs.getX z).size + 1 } else t.Gs.getX z := by
  simp only [sizeAdj, Array.getX_modify, Array.size_modify']
  by_cases h1 : z = a
  · subst h1; simp [ha, Ne.symm hab]
  · by_cases h2 : z = b
    · subst h2; simp [hb, h1, Ne.symm h1]
    · simp [h1, h2, Ne.symm h1, Ne.symm h2]

theorem moveFirstLeft_fields (s : Core) (g gl e lab z : Nat) :
    gSt (moveFirstLeft s g gl e lab) z = gSt s z ∧ gSrc (moveFirstLeft s g gl e lab) z = gSrc s z ∧
    gLl (moveFirstLeft s g gl e lab) z = gLl s z ∧ gRr (moveFirstLeft s g gl e lab) z = gRr s z ∧
    gSz (moveFirstLeft s g gl e lab) z = gSz s z := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [moveFirstLeft, gSt, gSrc, gLl, gRr, gSz, Array.getX_modify, Array.size_modify'] <;>
    split_ifs <;> simp_all

theorem moveLastRight_fields (s : Core) (g gr e lab z : Nat) :
    gSt (moveLastRight s g gr e lab) z = gSt s z ∧ gSrc (moveLastRight s g gr e lab) z = gSrc s z ∧
    gLl (moveLastRight s g gr e lab) z = gLl s z ∧ gRr (moveLastRight s g gr e lab) z = gRr s z ∧
    gSz (moveLastRight s g gr e lab) z = gSz s z := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [moveLastRight, gSt, gSrc, gLl, gRr, gSz, Array.getX_modify, Array.size_modify'] <;>
    split_ifs <;> simp_all

/-- What a move does to the fields the cost invariants read. -/
structure MoveSpec (s s' : Core) (src dst e lab : Nat) : Prop where
  links : GLinks s s'
  sz : ∀ z, gSz s' z = if z = src then gSz s src - 1 else if z = dst then gSz s dst + 1 else gSz s z
  eG : ∀ z, eG s' z = if z = e then dst else eG s z
  eL : ∀ z, eL s' z = if z = e then lab else eL s z
  head : s'.head = s.head
  P : s'.P = s.P
  E : s'.E.size = s.E.size ∧ (∀ z, eN s' z = eN s z) ∧ (∀ z, eP s' z = eP s z) ∧
    (∀ z, (s'.E.getX z).live = (s.E.getX z).live) ∧ (∀ z, (s'.E.getX z).h = (s.E.getX z).h)
  tail : s'.tail = s.tail
  C : s'.C = s.C
  lab : ∀ z, gL s' z = gL s z

theorem moveLState_spec {s : Core} {p : Nat} (hlp : gLl s p ≠ p) (hp : p < s.Gs.size)
    (hl : gLl s p < s.Gs.size) (he : gF s p < s.E.size) :
    MoveSpec s (moveLState s p) p (gLl s p) (gF s p) (labMoveL s p) := by
  obtain ⟨sN, sP, sC, sL, sA, sGs, seN, seP, sLive, sH, sEs, sCC, sF, sHd, sT, sFG, sFC⟩ :=
    moveFirstLeft_same (s := s) (g := p) (gl := gLl s p) (e := gF s p) (lab := labMoveL s p)
  have hGs : ∀ z, (moveLState s p).Gs.getX z = _ := fun z =>
    sizeAdj_getX (moveFirstLeft s p (gLl s p) (gF s p) (labMoveL s p)) p (gLl s p) z
      (Ne.symm hlp) (by rw [sGs]; exact hp) (by rw [sGs]; exact hl)
  have F := moveFirstLeft_fields s p (gLl s p) (gF s p) (labMoveL s p)
  have fld : ∀ {β : Type} (f : Group → β), (∀ X v, f { X with size := v } = f X) →
      ∀ z, f ((moveLState s p).Gs.getX z) = f ((moveFirstLeft s p (gLl s p) (gF s p) (labMoveL s
        p)).Gs.getX z) := by
    intro β f hf z; rw [hGs z]; split_ifs <;> simp [hf]
  refine ⟨⟨by simp [moveLState, sizeAdj, sGs], fun z => ?_, fun z => ?_, fun z => ?_, fun z => ?_,
    fun z => ?_, fun z => ?_, fun z => ?_⟩, fun z => ?_, fun z => ?_, fun z => ?_, sHd, rfl,
    ⟨sEs, seN, seP, sLive, sH⟩, sT, sCC, fun z => ?_⟩
  · change (_ : Group).st = _; rw [fld Group.st (fun _ _ => rfl)]; exact (F z).1
  · change (_ : Group).src = _; rw [fld Group.src (fun _ _ => rfl)]; exact (F z).2.1
  · change (_ : Group).l = _; rw [fld Group.l (fun _ _ => rfl)]; exact (F z).2.2.1
  · change (_ : Group).r = _; rw [fld Group.r (fun _ _ => rfl)]; exact (F z).2.2.2.1
  · change (_ : Group).next = _; rw [fld Group.next (fun _ _ => rfl)]; exact sN z
  · change (_ : Group).chk = _; rw [fld Group.chk (fun _ _ => rfl)]; exact sC z
  · change (_ : Group).alive = _; rw [fld Group.alive (fun _ _ => rfl)]; exact sA z
  · change (_ : Group).size = _
    rw [hGs z]
    have := (F z).2.2.2.2; simp only [gSz] at this
    by_cases h1 : z = p
    · subst h1; simp [this]
    · by_cases h2 : z = gLl s p
      · subst h2; simp [h1, this]
      · simp [h1, h2, this]
  · change ((moveLState s p).E.getX z).grp = _
    have := moveFirstLeft_eG (s := s) (g := p) (gl := gLl s p) (e := gF s p) (lab := labMoveL s p) z
    simp only [eG] at this
    simp only [moveLState, sizeAdj]
    rw [this]; simp [he]
  · change ((moveLState s p).E.getX z).lab = _
    have := moveFirstLeft_eL (s := s) (g := p) (gl := gLl s p) (e := gF s p) (lab := labMoveL s p) z
    simp only [eL] at this
    simp only [moveLState, sizeAdj]
    rw [this]; simp [he]
  · change (_ : Group).lab = _; rw [fld Group.lab (fun _ _ => rfl)]; exact sL z

theorem moveRState_spec {s : Core} {p : Nat} (hrp : gRr s p ≠ p) (hp : p < s.Gs.size)
    (hr : gRr s p < s.Gs.size) (he : gLs s p < s.E.size) :
    MoveSpec s (moveRState s p) p (gRr s p) (gLs s p) (labMoveR s p) := by
  obtain ⟨sN, sP, sC, sL, sA, sGs, seN, seP, sLive, sH, sEs, sCC, sF, sHd, sT, sFG, sFC⟩ :=
    moveLastRight_same (s := s) (g := p) (gr := gRr s p) (e := gLs s p) (lab := labMoveR s p)
  have hGs : ∀ z, (moveRState s p).Gs.getX z = _ := fun z =>
    sizeAdj_getX (moveLastRight s p (gRr s p) (gLs s p) (labMoveR s p)) p (gRr s p) z
      (Ne.symm hrp) (by rw [sGs]; exact hp) (by rw [sGs]; exact hr)
  have F := moveLastRight_fields s p (gRr s p) (gLs s p) (labMoveR s p)
  have fld : ∀ {β : Type} (f : Group → β), (∀ X v, f { X with size := v } = f X) →
      ∀ z, f ((moveRState s p).Gs.getX z) = f ((moveLastRight s p (gRr s p) (gLs s p) (labMoveR
        s p)).Gs.getX z) := by
    intro β f hf z; rw [hGs z]; split_ifs <;> simp [hf]
  refine ⟨⟨by simp [moveRState, sizeAdj, sGs], fun z => ?_, fun z => ?_, fun z => ?_, fun z => ?_,
    fun z => ?_, fun z => ?_, fun z => ?_⟩, fun z => ?_, fun z => ?_, fun z => ?_, sHd, rfl,
    ⟨sEs, seN, seP, sLive, sH⟩, sT, sCC, fun z => ?_⟩
  · change (_ : Group).st = _; rw [fld Group.st (fun _ _ => rfl)]; exact (F z).1
  · change (_ : Group).src = _; rw [fld Group.src (fun _ _ => rfl)]; exact (F z).2.1
  · change (_ : Group).l = _; rw [fld Group.l (fun _ _ => rfl)]; exact (F z).2.2.1
  · change (_ : Group).r = _; rw [fld Group.r (fun _ _ => rfl)]; exact (F z).2.2.2.1
  · change (_ : Group).next = _; rw [fld Group.next (fun _ _ => rfl)]; exact sN z
  · change (_ : Group).chk = _; rw [fld Group.chk (fun _ _ => rfl)]; exact sC z
  · change (_ : Group).alive = _; rw [fld Group.alive (fun _ _ => rfl)]; exact sA z
  · change (_ : Group).size = _
    rw [hGs z]
    have := (F z).2.2.2.2; simp only [gSz] at this
    by_cases h1 : z = p
    · subst h1; simp [this]
    · by_cases h2 : z = gRr s p
      · subst h2; simp [h1, this]
      · simp [h1, h2, this]
  · change ((moveRState s p).E.getX z).grp = _
    have := moveLastRight_eG (s := s) (g := p) (gr := gRr s p) (e := gLs s p) (lab := labMoveR s
      p) z
    simp only [eG] at this
    simp only [moveRState, sizeAdj]
    rw [this]; simp [he]
  · change ((moveRState s p).E.getX z).lab = _
    have := moveLastRight_eL (s := s) (g := p) (gr := gRr s p) (e := gLs s p) (lab := labMoveR s
      p) z
    simp only [eL] at this
    simp only [moveRState, sizeAdj]
    rw [this]; simp [he]
  · change (_ : Group).lab = _; rw [fld Group.lab (fun _ _ => rfl)]; exact sL z

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### `GInvE` across a move -/

/-- The family members of a splitting group other than `p` are not in `p`'s family. -/
theorem FamOK.disjoint {s : Core} {p q : Nat} (Fp : FamOK s p) (Fq : FamOK s q) (hpq : p ≠ q)
    (hps : gSt s p = .splitting) (hqs : gSt s q = .splitting) :
    q ≠ gLl s p ∧ q ≠ gRr s p ∧ gLl s q ≠ gLl s p ∧ gLl s q ≠ gRr s p ∧ gLl s q ≠ p ∧
      gRr s q ≠ gLl s p ∧ gRr s q ≠ gRr s p ∧ gRr s q ≠ p := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e; have := Fp.lSt; rw [← e, hqs] at this; cases this
  · intro e; have := Fp.rSt; rw [← e, hqs] at this; cases this
  · intro e; have h1 := Fq.lSrc; rw [e, Fp.lSrc] at h1; exact hpq h1
  · intro e; have h1 := Fq.lSrc; rw [e, Fp.rSrc] at h1; exact hpq h1
  · intro e; have := Fq.lSt; rw [e, hps] at this; cases this
  · intro e; have h1 := Fq.rSrc; rw [e, Fp.lSrc] at h1; exact hpq h1
  · intro e; have h1 := Fq.rSrc; rw [e, Fp.rSrc] at h1; exact hpq h1
  · intro e; have := Fq.rSt; rw [e, hps] at this; cases this

theorem FamOK.lp {s : Core} {A : Abs} (hI : INV s A) {p : Nat} (F : FamOK s p) (hp : LiveG s p) :
    gLl s p ≠ p := by
  intro e; have := F.lAdj; rw [e] at this
  have hp' := hI.mem_glist_iff.mpr hp
  rw [hI.gList.next p hp'] at this
  exact succOf_ne_self hI.gList.nodup p hp.1 this

theorem FamOK.rp {s : Core} {A : Abs} (hI : INV s A) {p : Nat} (F : FamOK s p) (hp : LiveG s p) :
    gRr s p ≠ p := by
  intro e; have := F.rAdj; rw [e] at this
  have hp' := hI.mem_glist_iff.mpr hp
  rw [hI.gList.next p hp'] at this
  exact succOf_ne_self hI.gList.nodup p hp.1 this

theorem FamOK.lr {s : Core} {A : Abs} (hI : INV s A) {p : Nat} (F : FamOK s p) (hp : LiveG s p) :
    gLl s p ≠ gRr s p := by
  intro e
  have h1 := F.lAdj; have h2 := F.rAdj
  rw [e] at h1
  have hr' := hI.mem_glist_iff.mpr F.rLive
  have hp' := hI.mem_glist_iff.mpr hp
  -- `r` precedes `p` and `p` precedes `r`
  obtain ⟨l1, l2, e1⟩ := succOf_split ((hI.gList.next _ hr').symm.trans h1) hp.1
  rw [hI.gList.next p hp', e1] at h2
  have hnd := hI.gList.nodup
  rw [e1] at hnd
  rw [show l1 ++ gRr s p :: p :: l2 = (l1 ++ [gRr s p]) ++ p :: l2 by simp,
    succOf_mid (by simpa using hnd)] at h2
  cases l2 with
  | nil => exact F.rLive.1 (by simpa using h2.symm)
  | cons a t =>
    have ha : a = gRr s p := by simpa using h2
    rw [ha] at hnd
    have := (List.nodup_append.mp hnd).2.1
    simp only [List.nodup_cons, List.mem_cons, true_or, not_true_eq_false, false_and,
      or_true] at this

/-- The run of a non-empty group starts at its `first` element. -/
theorem INV.run_head {s : Core} {A : Abs} (hI : INV s A) {g : Nat} (hg : g ∈ A.glist)
    (hne : gF s g ≠ NIL) : ∃ rest, runOf s A.elist g = gF s g :: rest := by
  have hE := (hI.gEnds g hg).1
  rw [hI.elts_eq hg] at hE
  cases h : runOf s A.elist g with
  | nil => rw [h] at hE; exact absurd hE hne
  | cons a t => rw [h] at hE; exact ⟨t, by simp [hE]⟩

/-- The run of a non-empty group ends at its `last` element. -/
theorem INV.run_last {s : Core} {A : Abs} (hI : INV s A) {g : Nat} (hg : g ∈ A.glist)
    (hne : gF s g ≠ NIL) : ∃ front, runOf s A.elist g = front ++ [gLs s g] := by
  have hE := hI.gEnds g hg
  rw [hI.elts_eq hg] at hE
  rcases (runOf s A.elist g).eq_nil_or_concat with h | ⟨front, a, h⟩
  · rw [h] at hE; exact absurd hE.1 hne
  · rw [List.concat_eq_append] at h
    rw [h] at hE ⊢; simp only [Ends] at hE
    refine ⟨front, ?_⟩
    rw [hE.2]; simp

theorem ginv_moveL {s : Core} {A : Abs} {gh : GGh} {δ : Nat → Nat} {p : Nat} (hI : INV s A)
    (hG : GInvE s A.elist gh δ p) (hp : LiveG s p) (hs : gSt s p = .splitting)
    (hne : gF s p ≠ NIL) :
    GInvE (moveLState s p) A.elist
      ⟨gh.hv, Function.update gh.pb (gLl s p) (gh.pb (gLl s p) + 1), gh.pf⟩ δ p := by
  have Fp := hG.fam p hp hs
  generalize hldef : gLl s p = l at *
  have hp' := hI.mem_glist_iff.mpr hp
  have hl' := hI.mem_glist_iff.mpr (hldef ▸ Fp.lLive)
  have hlp : l ≠ p := hldef ▸ Fp.lp hI hp
  have hlL : LiveG s l := hldef ▸ Fp.lLive
  obtain ⟨rest, hrun⟩ := hI.run_head hp' hne
  have he : gF s p ∈ A.elist := (mem_runOf.mp (hrun ▸ (by simp : gF s p ∈ gF s p :: rest))).1
  have heG : eG s (gF s p) = p := (mem_runOf.mp (hrun ▸ (by simp : gF s p ∈ gF s p :: rest))).2
  have M := moveLState_spec (s := s) (p := p) (hldef ▸ hlp) hp.2.1 (hldef ▸ hlL.2.1)
    ((hI.eAlloc _).mp he).2
  rw [hldef] at M
  generalize moveLState s p = s' at M ⊢
  generalize gF s p = e at hrun he heG M
  obtain ⟨X, Y, hL, hXY⟩ := hI.runs_adj hl' (hldef ▸ Fp.lAdj) hp.1
  rw [hrun] at hL
  have hRun := runOf_moveFront hL hXY
    (fun z hz => (mem_runOf.mp (hrun ▸ (by simp [hz] : z ∈ e :: rest))).2)
    (fun z hz => (mem_runOf.mp hz).2) heG hlp hI.eList.nodup M.eG
  have hK := M.links
  have hLive : ∀ b, LiveG s' b ↔ LiveG s b := hK.liveG
  have hszp : gSz s p = rest.length + 1 := by rw [hG.sz p hp, hrun]; simp
  have hSzO : ∀ z, z ≠ l → z ≠ p → gSz s' z = gSz s z := by
    intro z h1 h2; rw [M.sz, ite_eq_right h2, ite_eq_right h1]
  have hSzl : gSz s' l = gSz s l + 1 := by rw [M.sz, ite_eq_right hlp, ite_eq_left rfl]
  have hSzp : gSz s' p = gSz s p - 1 := by rw [M.sz, ite_eq_left rfl]
  have hRO : ∀ z, z ≠ l → z ≠ p → runOf s' A.elist z = runOf s A.elist z := by
    intro z h1 h2; rw [hRun, ite_eq_right h1, ite_eq_right h2]
  have heR : e ∉ runOf s A.elist l := fun h => by
    have := (mem_runOf.mp h).2; rw [heG] at this; exact hlp this.symm
  have heRest : e ∉ rest := fun h => by
    have hnd := hI.eList.nodup.filter (fun z => decide (eG s z = p))
    change (runOf s A.elist p).Nodup at hnd
    rw [hrun] at hnd; exact (List.nodup_cons.mp hnd).1 h
  have hEL : ∀ z, z ≠ e → eL s' z = eL s z := fun z h => by rw [M.eL, ite_eq_right h]
  have hrl : gRr s p ≠ l := fun h => (hldef ▸ Fp.lr hI hp) h.symm
  have hrp : gRr s p ≠ p := Fp.rp hI hp
  have hfamT : famT s' p = famT s p := by
    simp only [famT, hK.l, hK.r, hldef, hSzl, hSzp, hSzO _ hrl hrp]; omega
  have hfamO : ∀ q, LiveG s q → gSt s q = .splitting → q ≠ p → famT s' q = famT s q := by
    intro q hq hqs hqp
    have D := Fp.disjoint (hG.fam q hq hqs) (Ne.symm hqp) hs hqs
    rw [hldef] at D
    simp only [famT, hK.l, hK.r, hSzO _ D.1 hqp, hSzO _ D.2.2.1 D.2.2.2.2.1,
      hSzO _ D.2.2.2.2.2.1 D.2.2.2.2.2.2.2]
  have hlst : gSt s l = .overflow := hldef ▸ Fp.lSt
  have hlsrc : gSrc s l = p := hldef ▸ Fp.lSrc
  -- the label of the moved element
  have hlab : labMoveL s p = if runOf s A.elist l = [] then cE s.P
      else eL s (gLs s l) + s.P.elementSpacing := by
    unfold labMoveL; rw [hldef]
    by_cases h : gF s l = NIL
    · rw [ite_eq_left h, ite_eq_left ((hI.first_nil_iff hl').mp h)]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h ((hI.first_nil_iff hl').mpr h'))]
  refine
    { sz := ?_, fam := ?_, ovf := ?_, notDead := ?_, quiet := ?_, split := ?_, gaps := ?_,
      range := ?_, ghQ := ?_, ghO := ?_, ghS := ?_ }
  · intro z hz
    rw [hLive] at hz
    by_cases h1 : z = l
    · subst h1; rw [hSzl, hRun, ite_eq_left rfl, hG.sz _ hz]; simp
    · by_cases h2 : z = p
      · subst h2; rw [hSzp, hRun, ite_eq_right h1, ite_eq_left rfl, hszp]; simp
      · rw [hSzO z h1 h2, hRO z h1 h2]; exact hG.sz z hz
  · intro z hz hzs; rw [hLive] at hz; rw [hK.st] at hzs; exact hK.famOK (hG.fam z hz hzs)
  · intro z hz hzs; rw [hLive] at hz; rw [hK.st] at hzs; exact hK.ovf (hG.ovf z hz hzs)
  · intro z hz; rw [hLive] at hz; rw [hK.st]; exact hG.notDead z hz
  · intro z hz hzs
    rw [hLive] at hz; rw [hK.st] at hzs
    have h1 : z ≠ l := by rintro rfl; rw [hlst] at hzs; cases hzs
    have h2 : z ≠ p := by rintro rfl; rw [hs] at hzs; cases hzs
    rw [hSzO z h1 h2, hRO z h1 h2, M.head, M.P]
    exact hG.quiet z hz hzs
  · intro z hz hzs hzp
    rw [hLive] at hz; rw [hK.st] at hzs
    have D := Fp.disjoint (hG.fam z hz hzs) (Ne.symm hzp) hs hzs
    rw [hldef] at D
    have := hG.split z hz hzs hzp
    unfold G1 at this ⊢
    rw [M.P, hK.l, hK.r, hSzO _ D.1 hzp, hSzO _ D.2.2.1 D.2.2.2.2.1,
      hSzO _ D.2.2.2.2.2.1 D.2.2.2.2.2.2.2]
    exact this
  · intro z hz
    rw [hLive] at hz
    simp only [M.P]
    by_cases h1 : z = l
    · subst h1
      rw [hRun, ite_eq_left rfl]
      show ((runOf s A.elist z ++ [e]).map (eL s')).IsChain (fun a b => a + s.P.elementSpacing /
        2 ^ gh.hv z ≤ b)
      by_cases hemp : runOf s A.elist z = []
      · rw [hemp]; simp
      · have hz' : gF s z ≠ NIL := fun h => hemp ((hI.first_nil_iff hl').mp h)
        obtain ⟨front, hfr⟩ := hI.run_last hl' hz'
        have hc := hG.gaps z hz
        rw [hfr] at hc ⊢
        rw [show front ++ [gLs s z] ++ [e] = front ++ gLs s z :: e :: [] by simp]
        rw [show front ++ [gLs s z] = front ++ gLs s z :: [] by simp] at hc
        refine isChain_insert' hc (fun w hw => hEL w (fun h => heR (by rw [hfr]; exact h ▸ hw)))
          ?_ (by simp)
        rw [M.eL, ite_eq_left rfl, hlab, ite_eq_right hemp]
        have := Nat.div_le_self s.P.elementSpacing (2 ^ gh.hv z); omega
    · by_cases h2 : z = p
      · subst h2
        rw [hRun, ite_eq_right h1, ite_eq_left rfl]
        have hc := hG.gaps z hz
        rw [hrun, List.map_cons] at hc
        have := hc.tail
        rw [List.map_congr_left fun w hw => hEL w (fun h => heRest (h ▸ hw))]
        exact this
      · rw [hRO z h1 h2]
        rw [List.map_congr_left fun w hw => hEL w (fun h => by
          subst h; have := (mem_runOf.mp hw).2; rw [heG] at this; exact h2 this.symm)]
        exact hG.gaps z hz
  · intro z hz w hw
    rw [hLive] at hz
    simp only [M.P]
    by_cases h1 : z = l
    · subst h1
      rw [hRun, ite_eq_left rfl] at hw
      simp only [Function.update_self]
      rcases List.mem_append.mp hw with hw | hw
      · rw [hEL w (fun h => heR (h ▸ hw))]
        obtain ⟨q1, q2⟩ := hG.range z hz w hw
        refine ⟨q1, ?_⟩
        have := Nat.le_add_right (gh.pb z * s.P.elementSpacing) s.P.elementSpacing
        rw [Nat.add_mul]
        omega
      · simp only [List.mem_singleton] at hw
        subst hw
        rw [M.eL, ite_eq_left rfl, hlab]
        split
        · constructor <;> simp
        · next hemp =>
          have hz' : gF s z ≠ NIL := fun h => hemp ((hI.first_nil_iff hl').mp h)
          obtain ⟨front, hfr⟩ := hI.run_last hl' hz'
          obtain ⟨q1, q2⟩ := hG.range z hz (gLs s z) (by rw [hfr]; simp)
          rw [Nat.add_mul]; constructor <;> omega
    · rw [hEL w (fun h => by
        subst h
        by_cases h2 : z = p
        · subst h2; rw [hRun, ite_eq_right h1, ite_eq_left rfl] at hw; exact heRest hw
        · rw [hRO z h1 h2] at hw; have := (mem_runOf.mp hw).2; rw [heG] at this
          exact h2 this.symm)]
      simp only [Function.update_of_ne h1]
      by_cases h2 : z = p
      · subst h2; rw [hRun, ite_eq_right h1, ite_eq_left rfl] at hw
        exact hG.range z hz w (by rw [hrun]; simp [hw])
      · rw [hRO z h1 h2] at hw; exact hG.range z hz w hw
  · intro z hz hzs
    rw [hLive] at hz; rw [hK.st] at hzs
    have h1 : z ≠ l := by rintro rfl; rw [hlst] at hzs; cases hzs
    have h2 : z ≠ p := by rintro rfl; rw [hs] at hzs; cases hzs
    simp only [M.P, hSzO z h1 h2, Function.update_of_ne h1]
    exact hG.ghQ z hz hzs
  · intro z hz hzs
    rw [hLive] at hz; rw [hK.st] at hzs
    simp only [M.P, hK.src]
    by_cases h1 : z = l
    · subst h1
      rw [hlsrc, hfamT, hSzl]; simp only [Function.update_self]
      obtain ⟨q1, q2⟩ := hG.ghO z hz hzs
      rw [hlsrc] at q1
      exact ⟨q1, by omega⟩
    · have h2 : z ≠ p := by rintro rfl; rw [hs] at hzs; cases hzs
      obtain ⟨o1, o2, -⟩ := hG.ovf z hz hzs
      simp only [Function.update_of_ne h1, hSzO z h1 h2]
      by_cases hq : gSrc s z = p
      · rw [hq, hfamT]; have := hG.ghO z hz hzs; rw [hq] at this; exact this
      · rw [hfamO _ o1 o2 hq]; exact hG.ghO z hz hzs
  · intro z hz hzs
    rw [hLive] at hz; rw [hK.st] at hzs
    have h1 : z ≠ l := by rintro rfl; rw [hlst] at hzs; cases hzs
    simp only [M.P, Function.update_of_ne h1]
    by_cases h2 : z = p
    · subst h2; rw [hfamT]; exact hG.ghS z hz hzs
    · rw [hfamO z hz hzs h2]; exact hG.ghS z hz hzs

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
theorem ginv_moveR {s : Core} {A : Abs} {gh : GGh} {δ : Nat → Nat} {p : Nat} (hI : INV s A)
    (hG : GInvE s A.elist gh δ p) (hp : LiveG s p) (hs : gSt s p = .splitting)
    (hne : gF s p ≠ NIL) (hroom : gF s (gRr s p) ≠ NIL → s.P.elementSpacing ≤ eL s (gF s (gRr s
      p))) :
    GInvE (moveRState s p) A.elist
      ⟨gh.hv, gh.pb, Function.update gh.pf (gRr s p) (gh.pf (gRr s p) + 1)⟩ δ p := by
  have Fp := hG.fam p hp hs
  have hrl0 : gRr s p ≠ gLl s p := fun h => Fp.lr hI hp h.symm
  have hlp0 : gLl s p ≠ p := Fp.lp hI hp
  generalize hrdef : gRr s p = r at *
  have hp' := hI.mem_glist_iff.mpr hp
  have hr' := hI.mem_glist_iff.mpr (hrdef ▸ Fp.rLive)
  have hrp : r ≠ p := hrdef ▸ Fp.rp hI hp
  have hrL : LiveG s r := hrdef ▸ Fp.rLive
  obtain ⟨front, hrun⟩ := hI.run_last hp' hne
  have he : gLs s p ∈ A.elist := (mem_runOf.mp (hrun ▸ (by simp : gLs s p ∈ front ++ [gLs s p]))).1
  have heG : eG s (gLs s p) = p :=
    (mem_runOf.mp (hrun ▸ (by simp : gLs s p ∈ front ++ [gLs s p]))).2
  have M := moveRState_spec (s := s) (p := p) (hrdef ▸ hrp) hp.2.1 (hrdef ▸ hrL.2.1)
    ((hI.eAlloc _).mp he).2
  rw [hrdef] at M
  generalize moveRState s p = s' at M ⊢
  generalize gLs s p = e at hrun he heG M
  obtain ⟨X, Y, hL, hXY⟩ := hI.runs_adj hp' (hrdef ▸ Fp.rAdj) (hrdef ▸ hrL.1)
  rw [hrun] at hL
  have hRun := runOf_moveBack hL hXY
    (fun z hz => (mem_runOf.mp (hrun ▸ (by simp [hz] : z ∈ front ++ [e]))).2)
    (fun z hz => (mem_runOf.mp hz).2) heG (Ne.symm hrp) hI.eList.nodup M.eG
  have hK := M.links
  have hLive : ∀ b, LiveG s' b ↔ LiveG s b := hK.liveG
  have hszp : gSz s p = front.length + 1 := by rw [hG.sz p hp, hrun]; simp
  have hSzO : ∀ z, z ≠ r → z ≠ p → gSz s' z = gSz s z := by
    intro z h1 h2; rw [M.sz, ite_eq_right h2, ite_eq_right h1]
  have hSzr : gSz s' r = gSz s r + 1 := by rw [M.sz, ite_eq_right hrp, ite_eq_left rfl]
  have hSzp : gSz s' p = gSz s p - 1 := by rw [M.sz, ite_eq_left rfl]
  have hRO : ∀ z, z ≠ r → z ≠ p → runOf s' A.elist z = runOf s A.elist z := by
    intro z h1 h2; rw [hRun, ite_eq_right h1, ite_eq_right h2]
  have heR : e ∉ runOf s A.elist r := fun h => by
    have := (mem_runOf.mp h).2; rw [heG] at this; exact hrp this.symm
  have heF : e ∉ front := fun h => by
    have hnd := hI.eList.nodup.filter (fun z => decide (eG s z = p))
    change (runOf s A.elist p).Nodup at hnd
    rw [hrun] at hnd
    exact (List.nodup_append.mp hnd).2.2 e h e (by simp) rfl
  have hEL : ∀ z, z ≠ e → eL s' z = eL s z := fun z h => by rw [M.eL, ite_eq_right h]
  have hfamT : famT s' p = famT s p := by
    simp only [famT, hK.l, hK.r, hrdef, hSzr, hSzp, hSzO _ hrl0.symm hlp0]; omega
  have hfamO : ∀ q, LiveG s q → gSt s q = .splitting → q ≠ p → famT s' q = famT s q := by
    intro q hq hqs hqp
    have D := Fp.disjoint (hG.fam q hq hqs) (Ne.symm hqp) hs hqs
    rw [hrdef] at D
    simp only [famT, hK.l, hK.r, hSzO _ D.2.1 hqp, hSzO _ D.2.2.2.1 D.2.2.2.2.1,
      hSzO _ D.2.2.2.2.2.2.1 D.2.2.2.2.2.2.2]
  have hrst : gSt s r = .overflow := hrdef ▸ Fp.rSt
  have hrsrc : gSrc s r = p := hrdef ▸ Fp.rSrc
  have hlab : labMoveR s p = if runOf s A.elist r = [] then cE s.P
      else eL s (gF s r) - s.P.elementSpacing := by
    unfold labMoveR; rw [hrdef]
    by_cases h : gF s r = NIL
    · rw [ite_eq_left h, ite_eq_left ((hI.first_nil_iff hr').mp h)]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h ((hI.first_nil_iff hr').mpr h'))]
  refine
    { sz := ?_, fam := ?_, ovf := ?_, notDead := ?_, quiet := ?_, split := ?_, gaps := ?_,
      range := ?_, ghQ := ?_, ghO := ?_, ghS := ?_ }
  · intro z hz
    rw [hLive] at hz
    by_cases h1 : z = r
    · subst h1; rw [hSzr, hRun, ite_eq_left rfl, hG.sz _ hz]; simp
    · by_cases h2 : z = p
      · subst h2; rw [hSzp, hRun, ite_eq_right h1, ite_eq_left rfl, hszp]; simp
      · rw [hSzO z h1 h2, hRO z h1 h2]; exact hG.sz z hz
  · intro z hz hzs; rw [hLive] at hz; rw [hK.st] at hzs; exact hK.famOK (hG.fam z hz hzs)
  · intro z hz hzs; rw [hLive] at hz; rw [hK.st] at hzs; exact hK.ovf (hG.ovf z hz hzs)
  · intro z hz; rw [hLive] at hz; rw [hK.st]; exact hG.notDead z hz
  · intro z hz hzs
    rw [hLive] at hz; rw [hK.st] at hzs
    have h1 : z ≠ r := by rintro rfl; rw [hrst] at hzs; cases hzs
    have h2 : z ≠ p := by rintro rfl; rw [hs] at hzs; cases hzs
    rw [hSzO z h1 h2, hRO z h1 h2, M.head, M.P]
    exact hG.quiet z hz hzs
  · intro z hz hzs hzp
    rw [hLive] at hz; rw [hK.st] at hzs
    have D := Fp.disjoint (hG.fam z hz hzs) (Ne.symm hzp) hs hzs
    rw [hrdef] at D
    have := hG.split z hz hzs hzp
    unfold G1 at this ⊢
    rw [M.P, hK.l, hK.r, hSzO _ D.2.1 hzp, hSzO _ D.2.2.2.1 D.2.2.2.2.1,
      hSzO _ D.2.2.2.2.2.2.1 D.2.2.2.2.2.2.2]
    exact this
  · intro z hz
    rw [hLive] at hz
    simp only [M.P]
    by_cases h1 : z = r
    · subst h1
      rw [hRun, ite_eq_left rfl]
      by_cases hemp : runOf s A.elist z = []
      · rw [hemp]; simp
      · have hz' : gF s z ≠ NIL := fun h => hemp ((hI.first_nil_iff hr').mp h)
        obtain ⟨rest, hre⟩ := hI.run_head hr' hz'
        have hc := hG.gaps z hz
        rw [hre] at hc ⊢
        have hc' : (([] ++ gF s z :: rest).map (eL s')).IsChain
            (fun a b => a + s.P.elementSpacing / 2 ^ gh.hv z ≤ b) := by
          rw [List.map_congr_left fun w hw => hEL w (fun h => heR (by rw [hre]; simpa [h] using
            hw))]
          simpa using hc
        have hgap : eL s' e + s.P.elementSpacing / 2 ^ gh.hv z ≤ eL s' (gF s z) := by
          rw [M.eL, ite_eq_left rfl, hlab, ite_eq_right hemp,
            hEL _ (fun h => heR (by rw [hre, ← h]; simp))]
          have := hroom hz'
          have := Nat.div_le_self s.P.elementSpacing (2 ^ gh.hv z)
          omega
        rw [List.map_cons, List.map_cons, List.isChain_cons_cons]
        exact ⟨hgap, by simpa using hc'⟩
    · by_cases h2 : z = p
      · subst h2
        rw [hRun, ite_eq_right h1, ite_eq_left rfl]
        have hc := hG.gaps z hz
        rw [hrun] at hc
        rw [List.map_congr_left fun w hw => hEL w (fun h => heF (h ▸ hw))]
        exact (List.isChain_append.mp (by simpa using hc)).1
      · rw [hRO z h1 h2]
        rw [List.map_congr_left fun w hw => hEL w (fun h => by
          subst h; have := (mem_runOf.mp hw).2; rw [heG] at this; exact h2 this.symm)]
        exact hG.gaps z hz
  · intro z hz w hw
    rw [hLive] at hz
    simp only [M.P]
    by_cases h1 : z = r
    · subst h1
      rw [hRun, ite_eq_left rfl] at hw
      simp only [Function.update_self]
      rcases List.mem_cons.mp hw with hw | hw
      · subst hw
        rw [M.eL, ite_eq_left rfl, hlab]
        split
        · constructor <;> simp
        · next hemp =>
          have hz' : gF s z ≠ NIL := fun h => hemp ((hI.first_nil_iff hr').mp h)
          obtain ⟨rest, hre⟩ := hI.run_head hr' hz'
          obtain ⟨q1, q2⟩ := hG.range z hz (gF s z) (by rw [hre]; simp)
          have := hroom hz'
          rw [Nat.add_mul]; constructor <;> omega
      · rw [hEL w (fun h => heR (h ▸ hw))]
        obtain ⟨q1, q2⟩ := hG.range z hz w hw
        refine ⟨?_, q2⟩
        have := Nat.le_add_right (gh.pf z * s.P.elementSpacing) s.P.elementSpacing
        rw [Nat.add_mul]
        omega
    · rw [hEL w (fun h => by
        subst h
        by_cases h2 : z = p
        · subst h2; rw [hRun, ite_eq_right h1, ite_eq_left rfl] at hw; exact heF hw
        · rw [hRO z h1 h2] at hw; have := (mem_runOf.mp hw).2; rw [heG] at this
          exact h2 this.symm)]
      simp only [Function.update_of_ne h1]
      by_cases h2 : z = p
      · subst h2; rw [hRun, ite_eq_right h1, ite_eq_left rfl] at hw
        exact hG.range z hz w (by rw [hrun]; simp [hw])
      · rw [hRO z h1 h2] at hw; exact hG.range z hz w hw
  · intro z hz hzs
    rw [hLive] at hz; rw [hK.st] at hzs
    have h1 : z ≠ r := by rintro rfl; rw [hrst] at hzs; cases hzs
    have h2 : z ≠ p := by rintro rfl; rw [hs] at hzs; cases hzs
    simp only [M.P, hSzO z h1 h2, Function.update_of_ne h1]
    exact hG.ghQ z hz hzs
  · intro z hz hzs
    rw [hLive] at hz; rw [hK.st] at hzs
    simp only [M.P, hK.src]
    by_cases h1 : z = r
    · subst h1
      rw [hrsrc, hfamT, hSzr]; simp only [Function.update_self]
      obtain ⟨q1, q2⟩ := hG.ghO z hz hzs
      rw [hrsrc] at q1
      exact ⟨q1, by omega⟩
    · have h2 : z ≠ p := by rintro rfl; rw [hs] at hzs; cases hzs
      obtain ⟨o1, o2, -⟩ := hG.ovf z hz hzs
      simp only [Function.update_of_ne h1, hSzO z h1 h2]
      by_cases hq : gSrc s z = p
      · rw [hq, hfamT]; have := hG.ghO z hz hzs; rw [hq] at this; exact this
      · rw [hfamO _ o1 o2 hq]; exact hG.ghO z hz hzs
  · intro z hz hzs
    rw [hLive] at hz; rw [hK.st] at hzs
    have h1 : z ≠ r := by rintro rfl; rw [hrst] at hzs; cases hzs
    simp only [M.P, Function.update_of_ne h1]
    by_cases h2 : z = p
    · subst h2; rw [hfamT]; exact hG.ghS z hz hzs
    · rw [hfamO z hz hzs h2]; exact hG.ghS z hz hzs

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### Group removal -/

/-- What removing the emptied group `p` (with siblings `l`, `r`) does to the group records. -/
structure RemSpec (s s' : Core) (p l r : Nat) : Prop where
  live : ∀ z, LiveG s' z ↔ LiveG s z ∧ z ≠ p
  st : ∀ z, gSt s' z = if z = l ∨ z = r then .quiet else gSt s z
  src : ∀ z, gSrc s' z = if z = l ∨ z = r then NIL else gSrc s z
  l : ∀ z, gLl s' z = gLl s z
  r : ∀ z, gRr s' z = gRr s z
  sz : ∀ z, gSz s' z = gSz s z
  chk : ∀ z, gC s' z = gC s z
  next : ∀ z, z ≠ p → z ≠ gP s p → gN s' z = gN s z
  nextp : gP s p ≠ NIL → gN s' (gP s p) = gN s p
  lab : ∀ z, gL s' z = gL s z
  E : s'.E = s.E
  head : s'.head = s.head
  P : s'.P = s.P
  C : s'.C = (unlinkGroup s p).C

theorem quietG_quietG (X : Group) : quietG (quietG X) = quietG X := rfl

theorem removeState_getX {s : Core} {p : Nat} (hl : gLl s p < s.Gs.size)
    (hr : gRr s p < s.Gs.size) (z : Nat) :
    (removeState s p).Gs.getX z = if z = gLl s p ∨ z = gRr s p then
      quietG ((unlinkGroup s p).Gs.getX z) else (unlinkGroup s p).Gs.getX z := by
  simp only [removeState, Array.getX_modify, Array.size_modify', unlinkGroup_Gsize]
  by_cases h1 : z = gLl s p
  · subst h1
    by_cases h2 : gLl s p = gRr s p
    · simp [h2, hr, quietG_quietG]
    · simp [h2, Ne.symm h2, hl]
  · by_cases h2 : z = gRr s p
    · subst h2; simp [h1, Ne.symm h1, hr]
    · simp [h1, h2, Ne.symm h1, Ne.symm h2]

theorem removeState_spec {s : Core} {p : Nat} (hp : p < s.Gs.size) (hl : gLl s p < s.Gs.size)
    (hr : gRr s p < s.Gs.size) (hpp : gP s p ≠ p) (hps : gP s p ≠ NIL → gP s p < s.Gs.size) :
    RemSpec s (removeState s p) p (gLl s p) (gRr s p) := by
  have key := removeState_getX hl hr
  have fld : ∀ {β : Type} (f : Group → β), (∀ X, f (quietG X) = f X) →
      ∀ z, f ((removeState s p).Gs.getX z) = f ((unlinkGroup s p).Gs.getX z) := by
    intro β f hf z; rw [key z]; split_ifs <;> simp [hf]
  obtain ⟨rE, rCs, rF, rH, rT, rFC, rFG⟩ := unlinkGroup_rest (s := s) (g := p)
  have hsize : (removeState s p).Gs.size = s.Gs.size := by
    simp [removeState, unlinkGroup_Gsize]
  refine ⟨fun z => ?_, fun z => ?_, fun z => ?_, fun z => ?_, fun z => ?_, fun z => ?_,
    fun z => ?_, fun z hz1 hz2 => ?_, fun hp0 => ?_, fun z => ?_, rE, rH, rfl, rfl⟩
  · simp only [LiveG, gA, hsize]
    rw [fld Group.alive (fun _ => rfl)]
    have := unlinkGroup_gA (s := s) (g := p) z
    simp only [gA] at this
    rw [this]
    by_cases hz : z = p
    · subst hz; simp [hp]
    · simp [hz]
  · simp only [gSt]; rw [key z]
    have := (unlinkGroup_getX_lr s p z).2.2.1
    split_ifs <;> simp [quietG, this]
  · simp only [gSrc]; rw [key z]
    have := (unlinkGroup_getX_lr s p z).2.2.2.1
    split_ifs <;> simp [quietG, this]
  · simp only [gLl]; rw [fld Group.l (fun _ => rfl)]; exact (unlinkGroup_getX_lr s p z).1
  · simp only [gRr]; rw [fld Group.r (fun _ => rfl)]; exact (unlinkGroup_getX_lr s p z).2.1
  · simp only [gSz]; rw [fld Group.size (fun _ => rfl)]; exact (unlinkGroup_getX_lr s p z).2.2.2.2.1
  · simp only [gC]; rw [fld Group.chk (fun _ => rfl)]
    have := unlinkGroup_gC (s := s) (g := p) z; simpa only [gC] using this
  · simp only [gN]; rw [fld Group.next (fun _ => rfl)]
    have := unlinkGroup_gN (s := s) (g := p) hpp z
    simp only [gN] at this; rw [this]
    simp [hz1, hz2]
  · simp only [gN]; rw [fld Group.next (fun _ => rfl)]
    have := unlinkGroup_gN (s := s) (g := p) hpp (gP s p)
    have hps' := hps hp0
    simp only [gN, gP] at this hpp hp0 hps' ⊢; rw [this]
    simp [hpp, hp0, hps']
  · simp only [gL]; rw [fld Group.lab (fun _ => rfl)]
    have := unlinkGroup_gL (s := s) (g := p) z; simpa only [gL] using this

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-- **Removing an emptied group keeps `GInv`.** Its siblings become quiet groups of the right
size. -/
theorem ginv_remove {s : Core} {A : Abs} {gh : GGh} {δ : Nat → Nat} {p : Nat} (hI : INV s A)
    (hG : GInvE s A.elist gh δ p) (hp : LiveG s p) (hs : gSt s p = .splitting)
    (hδ : ∀ z, z ≠ gLl s p → z ≠ p → z ≠ gRr s p → δ z = 0)
    (hfam : famT s p ≤ s.P.G + kG s.P)
    (hql : gSz s (gLl s p) < s.P.G ∧ gmin s.P ≤ gSz s (gLl s p))
    (hqr : gSz s (gRr s p) < s.P.G ∧ gmin s.P ≤ gSz s (gRr s p)) (hg1 : 1 ≤ gmin s.P) :
    GInv (removeState s p) A.elist gh (fun _ => 0) := by
  have Fp := hG.fam p hp hs
  have hp' := hI.mem_glist_iff.mpr hp
  have hpp : gP s p ≠ p := by
    rw [hI.gList.prev p hp']; exact predOf_ne_self hI.gList.nodup p hp.1
  have hgPl : gP s p = gLl s p := by
    have := hI.gP_gN (hI.mem_glist_iff.mpr Fp.lLive) (by rw [Fp.lAdj]; exact hp.1)
    rw [Fp.lAdj] at this; exact this
  have R := removeState_spec hp.2.1 Fp.lLive.2.1 Fp.rLive.2.1 hpp
    (fun _ => by rw [hgPl]; exact Fp.lLive.2.1)
  generalize removeState s p = s' at R ⊢
  generalize hldef : gLl s p = l at *
  generalize hrdef : gRr s p = r at *
  have hRun : ∀ z, runOf s' A.elist z = runOf s A.elist z := by
    intro z; unfold runOf; simp only [eG, R.E]
  have hEL : eL s' = eL s := by funext e; simp only [eL, R.E]
  have hlst : gSt s l = .overflow := hldef ▸ Fp.lSt
  have hrst : gSt s r = .overflow := hrdef ▸ Fp.rSt
  have hlsrc : gSrc s l = p := hldef ▸ Fp.lSrc
  have hrsrc : gSrc s r = p := hrdef ▸ Fp.rSrc
  have hlL : LiveG s l := hldef ▸ Fp.lLive
  have hrL : LiveG s r := hrdef ▸ Fp.rLive
  have hlp : l ≠ p := hldef ▸ Fp.lp hI hp
  have hrp : r ≠ p := hrdef ▸ Fp.rp hI hp
  -- other groups keep state and source
  have hO : ∀ z, z ≠ l → z ≠ r → gSt s' z = gSt s z ∧ gSrc s' z = gSrc s z := by
    intro z h1 h2
    exact ⟨by rw [R.st, ite_eq_right (not_or.mpr ⟨h1, h2⟩)], by rw [R.src, ite_eq_right
      (not_or.mpr ⟨h1, h2⟩)]⟩
  have hfamO : ∀ q, famT s' q = famT s q := by
    intro q; simp only [famT, R.l, R.r, R.sz]
  -- a family other than `p`'s is untouched
  have hD : ∀ q, LiveG s q → gSt s q = .splitting → q ≠ p →
      q ≠ l ∧ q ≠ r ∧ gLl s q ≠ l ∧ gLl s q ≠ r ∧ gLl s q ≠ p ∧ gRr s q ≠ l ∧ gRr s q ≠ r ∧
        gRr s q ≠ p := by
    intro q hq hqs hqp
    have := Fp.disjoint (hG.fam q hq hqs) (Ne.symm hqp) hs hqs
    rw [hldef, hrdef] at this; exact this
  refine
    { sz := ?_, fam := ?_, ovf := ?_, notDead := ?_, quiet := ?_, split := ?_, gaps := ?_,
      range := ?_, ghQ := ?_, ghO := ?_, ghS := ?_ }
  · intro z hz; rw [R.live] at hz; rw [R.sz, hRun]; exact hG.sz z hz.1
  · intro z hz hzs
    rw [R.live] at hz
    have h1 : z ≠ l := by rintro rfl; rw [R.st, ite_eq_left (Or.inl rfl)] at hzs; cases hzs
    have h2 : z ≠ r := by rintro rfl; rw [R.st, ite_eq_left (Or.inr rfl)] at hzs; cases hzs
    rw [(hO z h1 h2).1] at hzs
    have Fz := hG.fam z hz.1 hzs
    obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8⟩ := hD z hz.1 hzs hz.2
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [R.l, R.live]; exact ⟨Fz.lLive, d5⟩
    · rw [R.r, R.live]; exact ⟨Fz.rLive, d8⟩
    · rw [R.l, R.next _ d5 (by rw [hgPl]; exact d3)]; exact Fz.lAdj
    · rw [R.r, R.next _ hz.2 (by rw [hgPl]; exact h1)]; exact Fz.rAdj
    · rw [R.l, (hO _ d3 d4).1]; exact Fz.lSt
    · rw [R.l, (hO _ d3 d4).2]; exact Fz.lSrc
    · rw [R.r, (hO _ d6 d7).1]; exact Fz.rSt
    · rw [R.r, (hO _ d6 d7).2]; exact Fz.rSrc
    · rw [R.l, R.chk, R.chk]; exact Fz.lC
    · rw [R.r, R.chk, R.chk]; exact Fz.rC
  · intro z hz hzs
    rw [R.live] at hz
    have h1 : z ≠ l := by rintro rfl; rw [R.st, ite_eq_left (Or.inl rfl)] at hzs; cases hzs
    have h2 : z ≠ r := by rintro rfl; rw [R.st, ite_eq_left (Or.inr rfl)] at hzs; cases hzs
    rw [(hO z h1 h2).1] at hzs
    obtain ⟨o1, o2, o3⟩ := hG.ovf z hz.1 hzs
    have hq : gSrc s z ≠ p := by
      intro e; rw [e] at o3; rcases o3 with o3 | o3
      · exact h1 (by rw [← o3, hldef])
      · exact h2 (by rw [← o3, hrdef])
    obtain ⟨d1, d2, -⟩ := hD _ o1 o2 hq
    rw [(hO z h1 h2).2, R.live, (hO _ d1 d2).1, R.l, R.r]
    exact ⟨⟨o1, hq⟩, o2, o3⟩
  · intro z hz
    rw [R.live] at hz
    rw [R.st]; split
    · simp
    · exact hG.notDead z hz.1
  · intro z hz hzs
    rw [R.live] at hz
    rw [R.sz, R.P, R.head, hRun]
    by_cases h1 : z = l
    · subst h1; exact ⟨by simpa using hql.1, le_trans hg1 hql.2, Or.inl hql.2⟩
    · by_cases h2 : z = r
      · subst h2; exact ⟨by simpa using hqr.1, le_trans hg1 hqr.2, Or.inl hqr.2⟩
      · rw [(hO z h1 h2).1] at hzs
        have hz0 : δ z = 0 := hδ z h1 hz.2 h2
        obtain ⟨q1, q2, q3⟩ := hG.quiet z hz.1 hzs
        exact ⟨by rw [hz0] at q1; simpa using q1, q2, q3⟩
  · intro z hz hzs _
    rw [R.live] at hz
    have h1 : z ≠ l := by rintro rfl; rw [R.st, ite_eq_left (Or.inl rfl)] at hzs; cases hzs
    have h2 : z ≠ r := by rintro rfl; rw [R.st, ite_eq_left (Or.inr rfl)] at hzs; cases hzs
    rw [(hO z h1 h2).1] at hzs
    obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8⟩ := hD z hz.1 hzs hz.2
    have := hG.split z hz.1 hzs hz.2
    unfold G1 at this ⊢
    rw [R.P, R.l, R.r, R.sz, R.sz, R.sz]
    rw [hδ _ d3 d5 d4, hδ _ h1 hz.2 h2, hδ _ d6 d8 d7] at this
    simpa using this
  · intro z hz; rw [R.live] at hz; rw [hRun, hEL, R.P]; exact hG.gaps z hz.1
  · intro z hz w hw; rw [R.live] at hz; rw [hRun] at hw; rw [hEL, R.P]; exact hG.range z hz.1 w hw
  · intro z hz hzs
    rw [R.live] at hz
    rw [R.sz, R.P]
    by_cases h1 : z = l
    · subst h1
      obtain ⟨q1, q2⟩ := hG.ghO z hz.1 hlst
      rw [hlsrc] at q1
      simp only [kG] at hfam ⊢
      exact ⟨by omega, q2⟩
    · by_cases h2 : z = r
      · subst h2
        obtain ⟨q1, q2⟩ := hG.ghO z hz.1 hrst
        rw [hrsrc] at q1
        simp only [kG] at hfam ⊢
        exact ⟨by omega, q2⟩
      · rw [(hO z h1 h2).1] at hzs; exact hG.ghQ z hz.1 hzs
  · intro z hz hzs
    rw [R.live] at hz
    have h1 : z ≠ l := by rintro rfl; rw [R.st, ite_eq_left (Or.inl rfl)] at hzs; cases hzs
    have h2 : z ≠ r := by rintro rfl; rw [R.st, ite_eq_left (Or.inr rfl)] at hzs; cases hzs
    rw [(hO z h1 h2).1] at hzs
    rw [R.sz, R.P, (hO z h1 h2).2, hfamO]
    exact hG.ghO z hz.1 hzs
  · intro z hz hzs
    rw [R.live] at hz
    have h1 : z ≠ l := by rintro rfl; rw [R.st, ite_eq_left (Or.inl rfl)] at hzs; cases hzs
    have h2 : z ≠ r := by rintro rfl; rw [R.st, ite_eq_left (Or.inr rfl)] at hzs; cases hzs
    rw [(hO z h1 h2).1] at hzs
    rw [R.P, hfamO]
    exact hG.ghS z hz.1 hzs

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### The drive loop -/

theorem forIn_loop {α β : Type} (f : α → β → CM (ForInStep β)) (I : Nat → Core → Prop)
    (Q : Core → Prop) (N : Nat)
    (hstep : ∀ x j b t, I j t → j < N → ∃ c t',
      ((f x b).run t = .ok (.yield c) t' ∧ I (j + 1) t') ∨
      ((f x b).run t = .ok (.done c) t' ∧ Q t')) :
    ∀ (l : List α) (k : Nat) (b : β) (t : Core), I k t → k + l.length ≤ N →
      ∃ c t', (forIn l b f).run t = .ok c t' ∧ (I (k + l.length) t' ∨ Q t') := by
  intro l
  induction l with
  | nil => intro k b t hI _; exact ⟨b, t, rfl, Or.inl (by simpa using hI)⟩
  | cons x l ih =>
    intro k b t hI hN
    simp only [List.length_cons] at hN
    rw [List.forIn_cons, run_bind]
    obtain ⟨c, t', h⟩ := hstep x k b t hI (by omega)
    rcases h with ⟨hr, hI'⟩ | ⟨hr, hQ⟩
    · rw [hr]
      obtain ⟨c', t'', hr', hres⟩ := ih (k + 1) c t' hI' (by omega)
      refine ⟨c', t'', hr', ?_⟩
      rw [List.length_cons, show k + (l.length + 1) = k + 1 + l.length by omega]
      exact hres
    · rw [hr]; exact ⟨c, t', rfl, Or.inr hQ⟩

/-- **The drive loop**: `groupBudget` split steps of `p`, stopping when `p` is removed. -/
theorem driveGroupFrom_ok {s : Core} {p : Nat} (I : Nat → Core → Prop) (Q : Core → Prop)
    (h0 : I 0 s)
    (hstep : ∀ j t, I j t → j < s.P.groupBudget → ∃ t',
      ((groupSplitStep p).run t = .ok true t' ∧ I (j + 1) t') ∨
      ((groupSplitStep p).run t = .ok false t' ∧ Q t')) :
    ∃ t', (driveGroupFrom p).run s = .ok () t' ∧ (I s.P.groupBudget t' ∨ Q t') := by
  unfold driveGroupFrom
  rw [run_getP_bind, run_bind]
  obtain ⟨c, t', hr, hres⟩ := forIn_loop
    (fun (_ : Nat) (_ : Option Unit × Unit) => do
      let b ← groupSplitStep p
      if (!b) = true then pure (ForInStep.done (some (), ()))
      else pure (ForInStep.yield (none, ())))
    I Q s.P.groupBudget (by
      intro x j b t hI hj
      obtain ⟨t', h⟩ := hstep j t hI hj
      rcases h with ⟨hr, hI'⟩ | ⟨hr, hQ⟩
      · exact ⟨(none, ()), t', Or.inl ⟨by rw [run_bind, hr]; rfl, hI'⟩⟩
      · exact ⟨(some (), ()), t', Or.inr ⟨by rw [run_bind, hr]; rfl, hQ⟩⟩)
    (List.range s.P.groupBudget) 0 (none, ()) s h0 (by simp)
  rw [hr]
  refine ⟨t', ?_, by simpa using hres⟩
  dsimp only
  split <;> rfl

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
theorem Good.ok_inv {α : Type} {m : CM α} (h : Good m) {s : Core} {A : Abs} (hI : INV s A) {a : α}
    {s' : Core} (hr : m.run s = .ok a s') : EFrame s s' ∧ ∃ A', INV s' A' ∧ A'.elist = A.elist := by
  have := h s A hI; rw [hr] at this; exact this

/-- Closing a drive: the family of `p` satisfies G1 again, and nothing else was exempt. -/
theorem GInvE.close {s : Core} {L : List Nat} {gh : GGh} {δ : Nat → Nat} {p : Nat}
    (hG : GInvE s L gh δ p) (hp : LiveG s p) (hs : gSt s p = .splitting)
    (hδ : ∀ z, z ≠ gLl s p → z ≠ p → z ≠ gRr s p → δ z = 0) (hG1 : G1 s (fun _ => 0) p) :
    GInv s L gh (fun _ => 0) := by
  have Fp := hG.fam p hp hs
  refine { hG with quiet := ?_, split := ?_ }
  · intro z hz hzs
    have h1 : z ≠ gLl s p := by intro e; rw [e, Fp.lSt] at hzs; cases hzs
    have h2 : z ≠ p := by intro e; rw [e, hs] at hzs; cases hzs
    have h3 : z ≠ gRr s p := by intro e; rw [e, Fp.rSt] at hzs; cases hzs
    have := hG.quiet z hz hzs; rw [hδ z h1 h2 h3] at this; simpa using this
  · intro z hz hzs _
    by_cases hzp : z = p
    · subst hzp; exact hG1
    · have D := Fp.disjoint (hG.fam z hz hzs) (Ne.symm hzp) hs hzs
      obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8⟩ := D
      have := hG.split z hz hzs hzp
      unfold G1 at this ⊢
      rw [hδ _ d3 d5 d4, hδ _ d1 hzp d2, hδ _ d6 d8 d7] at this
      simpa using this

/-- The drive's invariant after `j` moves of `p`'s split. `a`, `b`, `c` are the sizes of `l`,
`p`, `r` before the drive. -/
structure DriveInv (X : Core → Prop) (s : Core) (L : List Nat) (δ : Nat → Nat) (p l r a b c j : Nat)
    (t : Core) : Prop where
  x : X t
  P : t.P = s.P
  ef : EFrame s t
  inv : ∃ A', INV t A' ∧ A'.elist = L
  ginv : ∃ gh, GInvE t L gh δ p
  live : LiveG t p
  st : gSt t p = .splitting
  ll : gLl t p = l
  rr : gRr t p = r
  sum : gSz t l + gSz t p + gSz t r = a + b + c
  cnt : gSz t p + j = b
  bal : (j = 0 ∧ gSz t l = a ∧ gSz t r = c) ∨
    (1 ≤ j ∧ gSz t l ≤ gSz t r + 1 ∧ gSz t r ≤ gSz t l + 1)
  chk : gC t p = gC s p

/-- The drive ended by removing `p`. -/
structure DriveDone (X Y : Core → Prop) (s : Core) (L : List Nat) (t : Core) : Prop where
  x : X t ∨ Y t
  P : t.P = s.P
  ef : EFrame s t
  inv : ∃ A', INV t A' ∧ A'.elist = L
  ginv : ∃ gh, GInv t L gh (fun _ => 0)

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-- The extra invariant `X` survives the steps of a drive. -/
structure XSteps (X Y : Core → Prop) (L : List Nat) (δ : Nat → Nat) (p c : Nat) : Prop where
  moveL : ∀ t A' gh, INV t A' → A'.elist = L → GInvE t L gh δ p → MoveLOK t p →
    gSt t p = .splitting → X t → X (moveLState t p)
  moveR : ∀ t A' gh, INV t A' → A'.elist = L → GInvE t L gh δ p → MoveROK t p →
    gSt t p = .splitting → X t → X (moveRState t p)
  rem : ∀ t A' gh, INV t A' → A'.elist = L → GInvE t L gh δ p → LiveG t p →
    gSt t p = .splitting → gF t p = NIL → gSz t (gLl t p) < t.P.G → gSz t (gRr t p) < t.P.G →
    gmin t.P ≤ gSz t (gLl t p) → gmin t.P ≤ gSz t (gRr t p) →
    gC t p = c → X t → Y (removeState t p)

/-- Overflow label bounds supply every guard for a left move into the lighter sibling. -/
theorem GInvE.move_left_ok {s : Core} {A : Abs} {gh : GGh} {δ : Nat → Nat} {p : Nat}
    (hG : GInvE s A.elist gh δ p) (hI : INV s A) (hP : GParams s.P)
    (hp : LiveG s p) (hs : gSt s p = .splitting) (hne : gF s p ≠ NIL)
    (hdir : gSz s (gLl s p) ≤ gSz s (gRr s p))
    (hsize : gSz s (gLl s p) + 1 ≤ s.P.G + kG s.P) : MoveLOK s p := by
  have Fp := hG.fam p hp hs
  have hlL := Fp.lLive
  have hl' := hI.mem_glist_iff.mpr hlL
  obtain ⟨-, hpush⟩ := hG.ghO _ hlL Fp.lSt
  have hcE := hP.push
  refine ⟨hp, hne, hdir, Fp.lAdj, ?_, by have := hP.De; omega, Fp.lC⟩
  intro hfl
  obtain ⟨fr, hfr⟩ := hI.run_last hl' hfl
  obtain ⟨-, h2⟩ := hG.range _ hlL (gLs s (gLl s p)) (by rw [hfr]; simp)
  rw [cE_two _ hP.Be]
  have : (gh.pb (gLl s p) + 1) * s.P.elementSpacing ≤
      (s.P.G + kG s.P) * s.P.elementSpacing := Nat.mul_le_mul_right _ (by omega)
  have : (gh.pb (gLl s p) + 1) * s.P.elementSpacing =
      gh.pb (gLl s p) * s.P.elementSpacing + s.P.elementSpacing := by ring
  omega

/-- Overflow label bounds supply every guard for a right move into the strictly lighter sibling. -/
theorem GInvE.move_right_ok {s : Core} {A : Abs} {gh : GGh} {δ : Nat → Nat} {p : Nat}
    (hG : GInvE s A.elist gh δ p) (hI : INV s A) (hP : GParams s.P)
    (hp : LiveG s p) (hs : gSt s p = .splitting) (hne : gF s p ≠ NIL)
    (hdir : gSz s (gRr s p) < gSz s (gLl s p))
    (hsize : gSz s (gRr s p) + 1 ≤ s.P.G + kG s.P) : MoveROK s p := by
  have Fp := hG.fam p hp hs
  have hrL := Fp.rLive
  have hr' := hI.mem_glist_iff.mpr hrL
  obtain ⟨-, hpush⟩ := hG.ghO _ hrL Fp.rSt
  have hcE := hP.push
  have hadj : gP s (gRr s p) = p := by
    rw [← Fp.rAdj]
    exact hI.gP_gN (hI.mem_glist_iff.mpr hp) (by rw [Fp.rAdj]; exact hrL.1)
  refine ⟨hp, hne, hdir, hadj, ?_, by have := hP.De; omega, Fp.rC⟩
  intro hfr
  obtain ⟨rs, hrs⟩ := hI.run_head hr' hfr
  obtain ⟨h1, -⟩ := hG.range _ hrL (gF s (gRr s p)) (by rw [hrs]; simp)
  have : (gh.pf (gRr s p) + 1) * s.P.elementSpacing ≤
      (s.P.G + kG s.P) * s.P.elementSpacing := Nat.mul_le_mul_right _ (by omega)
  have : (gh.pf (gRr s p) + 1) * s.P.elementSpacing =
      gh.pf (gRr s p) * s.P.elementSpacing + s.P.elementSpacing := by ring
  omega

theorem DriveInv.step {X Y : Core → Prop} {s : Core} {L : List Nat} {δ : Nat → Nat}
    {p l r a b c j : Nat} {t : Core} (hXs : XSteps X Y L δ p (gC s p))
    (hP : GParams s.P) (hδ : ∀ z, z ≠ l → z ≠ p → z ≠ r → δ z = 0)
    (hTlo : s.P.G ≤ a + b + c) (hThi : a + b + c ≤ s.P.G + s.P.G / (s.P.groupBudget - 1) + 1)
    (hbal0 : a ≤ c + 2 ∧ c ≤ a + 2)
    (hD : DriveInv X s L δ p l r a b c j t) :
    ∃ t', ((groupSplitStep p).run t = .ok true t' ∧ DriveInv X s L δ p l r a b c (j + 1) t') ∨
      ((groupSplitStep p).run t = .ok false t' ∧ DriveDone X Y s L t') := by
  obtain ⟨A', hI', hel⟩ := hD.inv
  obtain ⟨gh, hG⟩ := hD.ginv
  subst hel
  have hp := hD.live
  have hs := hD.st
  have Fp := hG.fam p hp hs
  have hp' := hI'.mem_glist_iff.mpr hp
  have hPt := hD.P
  rw [← hPt] at hP hTlo hThi
  have hlL : LiveG t l := hD.ll ▸ Fp.lLive
  have hrL : LiveG t r := hD.rr ▸ Fp.rLive
  have hl' := hI'.mem_glist_iff.mpr hlL
  have hr' := hI'.mem_glist_iff.mpr hrL
  have hlp : l ≠ p := hD.ll ▸ Fp.lp hI' hp
  have hrp : r ≠ p := hD.rr ▸ Fp.rp hI' hp
  have hlr : l ≠ r := hD.ll ▸ hD.rr ▸ Fp.lr hI' hp
  have hsum := hD.sum
  have hcnt := hD.cnt
  have hbal := hD.bal
  have hK2 := hP.K2
  have hI1 := hP.I1
  generalize hq : t.P.G / (t.P.groupBudget - 1) = q at hThi hI1
  have hkG : kG t.P = q + 1 := by unfold kG; rw [hq]
  by_cases hz : gSz t p = 0
  · -- removal
    have he : gF t p = NIL := by
      rw [hI'.first_nil_iff hp', ← List.length_eq_zero_iff, ← hG.sz p hp]; exact hz
    have hszl : gSz t l < t.P.G := by rcases hbal with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;> omega
    have hszr : gSz t r < t.P.G := by rcases hbal with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;> omega
    have hgl : gmin t.P ≤ gSz t l := by
      unfold gmin; rcases hbal with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;> omega
    have hgr : gmin t.P ≤ gSz t r := by
      unfold gmin; rcases hbal with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;> omega
    have hfam : famT t p ≤ t.P.G + kG t.P := by
      unfold famT; rw [hD.ll, hD.rr, hkG]; omega
    have hg1 : 1 ≤ gmin t.P := by unfold gmin; have := hP.G4; omega
    have hrun := groupSplitStep_remove hp he (by rw [hD.ll, hD.rr]; exact hlr)
      ⟨by rw [hD.ll]; exact Fp.lSt ▸ hD.ll ▸ rfl, by rw [hD.ll]; exact hD.ll ▸ Fp.lSrc⟩
      ⟨by rw [hD.rr]; exact hD.rr ▸ Fp.rSt, by rw [hD.rr]; exact hD.rr ▸ Fp.rSrc⟩
      (by rw [hD.ll]; exact hszl) (by rw [hD.rr]; exact hszr)
    obtain ⟨hef, A'', hI'', hel''⟩ := Good.ok_inv (good_groupSplitStep p) hI' hrun
    refine ⟨_, Or.inr ⟨hrun, ⟨?_, ?_, hD.ef.trans hef, ⟨A'', hI'', hel''⟩, ⟨gh, ?_⟩⟩⟩⟩
    · exact Or.inr (hXs.rem t A' gh hI' rfl hG hp hs he (by rw [hD.ll]; exact hszl)
        (by rw [hD.rr]; exact hszr) (by rw [hD.ll]; exact hgl) (by rw [hD.rr]; exact hgr)
        hD.chk hD.x)
    · exact hef.P.trans hPt
    · refine ginv_remove hI' hG hp hs (by rw [hD.ll, hD.rr]; exact hδ) hfam
        (by rw [hD.ll]; exact ⟨hszl, hgl⟩) (by rw [hD.rr]; exact ⟨hszr, hgr⟩) hg1
  · have hne : gF t p ≠ NIL := by
      intro h; apply hz
      rw [hG.sz p hp]; exact List.length_eq_zero_iff.mpr ((hI'.first_nil_iff hp').mp h)
    obtain ⟨rest, hrun⟩ := hI'.run_head hp' hne
    have he : gF t p ∈ A'.elist := (mem_runOf.mp (hrun ▸ (by simp : gF t p ∈ gF t p :: rest))).1
    have heS : gF t p < t.E.size := ((hI'.eAlloc _).mp he).2
    obtain ⟨front, hrunL⟩ := hI'.run_last hp' hne
    have heL : gLs t p ∈ A'.elist :=
      (mem_runOf.mp (hrunL ▸ (by simp : gLs t p ∈ front ++ [gLs t p]))).1
    have heLS : gLs t p < t.E.size := ((hI'.eAlloc _).mp heL).2
    by_cases hdir : gSz t l ≤ gSz t r
    · -- move to the left sibling
      have hlsz : gSz t l + 1 ≤ t.P.G + q + 1 := by omega
      have hok := hG.move_left_ok hI' hP hp hs hne
        (by rw [hD.ll, hD.rr]; exact hdir) (by rw [hD.ll, hkG]; exact hlsz)
      have hrun2 := groupSplitStep_left hok
      obtain ⟨hef, A'', hI'', hel''⟩ := Good.ok_inv (good_groupSplitStep p) hI' hrun2
      have M := moveLState_spec (s := t) (p := p) (hD.ll ▸ hlp) hp.2.1 (hD.ll ▸ hlL.2.1) heS
      rw [hD.ll] at M
      have hG' := ginv_moveL hI' hG hp hs hne
      rw [hD.ll] at hG'
      have hK := M.links
      refine ⟨_, Or.inl ⟨hrun2, ?_⟩⟩
      refine ⟨hXs.moveL t A' gh hI' rfl hG hok hD.st hD.x, hef.P.trans hPt, hD.ef.trans hef,
        ⟨A'', hI'', hel''⟩, ⟨_, hG'⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact (hK.liveG p).mpr hp
      · rw [hK.st]; exact hs
      · rw [hK.l]; exact hD.ll
      · rw [hK.r]; exact hD.rr
      · rw [M.sz, M.sz, M.sz, ite_eq_right hlp, ite_eq_left rfl, ite_eq_left rfl,
        ite_eq_right hrp, ite_eq_right (Ne.symm hlr)]
        omega
      · rw [M.sz, ite_eq_left rfl]; omega
      · right
        rw [M.sz, M.sz, ite_eq_right hlp, ite_eq_left rfl, ite_eq_right hrp,
          ite_eq_right (Ne.symm hlr)]
        refine ⟨by omega, ?_, ?_⟩ <;> rcases hbal with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;> omega
      · rw [hK.chk]; exact hD.chk
    · -- move to the right sibling
      have hrsz : gSz t r + 1 ≤ t.P.G + q + 1 := by omega
      have hok := hG.move_right_ok hI' hP hp hs hne
        (by rw [hD.ll, hD.rr]; omega) (by rw [hD.rr, hkG]; exact hrsz)
      have hrun2 := groupSplitStep_right hok
      obtain ⟨hef, A'', hI'', hel''⟩ := Good.ok_inv (good_groupSplitStep p) hI' hrun2
      have M := moveRState_spec (s := t) (p := p) (hD.rr ▸ hrp) hp.2.1 (hD.rr ▸ hrL.2.1) heLS
      rw [hD.rr] at M
      have hG' := ginv_moveR hI' hG hp hs hne hok.room
      rw [hD.rr] at hG'
      have hK := M.links
      refine ⟨_, Or.inl ⟨hrun2, ?_⟩⟩
      refine ⟨hXs.moveR t A' gh hI' rfl hG hok hD.st hD.x, hef.P.trans hPt, hD.ef.trans hef,
        ⟨A'', hI'', hel''⟩, ⟨_, hG'⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact (hK.liveG p).mpr hp
      · rw [hK.st]; exact hs
      · rw [hK.l]; exact hD.ll
      · rw [hK.r]; exact hD.rr
      · rw [M.sz, M.sz, M.sz, ite_eq_right hlp, ite_eq_right hlr, ite_eq_left rfl,
        ite_eq_right hrp, ite_eq_left rfl]
        omega
      · rw [M.sz, ite_eq_left rfl]; omega
      · right
        rw [M.sz, M.sz, ite_eq_right hlp, ite_eq_right hlr, ite_eq_right hrp, ite_eq_left rfl]
        refine ⟨by omega, ?_, ?_⟩ <;> rcases hbal with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;> omega
      · rw [hK.chk]; exact hD.chk

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-- **Lemma G1 for one drive.** Driving the family of `p` after at most one undriven insertion
into it ends with `GInv` (no undriven insertion): either `p` has made `groupBudget` moves and
  the family
satisfies G1 again, or `p` was removed and its siblings are quiet groups of the right size. -/
theorem ginv_drive {X Y : Core → Prop} {s : Core} {A : Abs} {gh : GGh} {δ : Nat → Nat} {p : Nat}
    (hI : INV s A) (hXs : XSteps X Y A.elist δ p (gC s p)) (hX : X s)
    (hG : GInvE s A.elist gh δ p) (hP : GParams s.P) (hp : LiveG s p) (hs : gSt s p = .splitting)
    (hG1 : G1 s δ p)
    (hδ : ∀ z, z ≠ gLl s p → z ≠ p → z ≠ gRr s p → δ z = 0)
    (hδs : δ (gLl s p) + δ p + δ (gRr s p) ≤ 1)
    (hδle : δ (gLl s p) ≤ gSz s (gLl s p) ∧ δ p ≤ gSz s p ∧ δ (gRr s p) ≤ gSz s (gRr s p)) :
    ∃ s', (driveGroupFrom p).run s = .ok () s' ∧ DriveDone X Y s A.elist s' := by
  have hBounds := hG1.drive_bounds hP.K2 hδs hδle
  generalize hl : gLl s p = l at *
  generalize hr : gRr s p = r at *
  generalize ha : gSz s l = a at *
  generalize hb : gSz s p = b at *
  generalize hc : gSz s r = c at *
  obtain ⟨hTlo, hThi, hbal0⟩ := hBounds
  have hK2 := hP.K2
  unfold G1 at hG1
  rw [hl, hr, ha, hb, hc] at hG1
  obtain ⟨g1, g2, g3, g4⟩ := hG1
  generalize hm : s.P.groupBudget - 1 = m at g2
  obtain ⟨t, hrun, hres⟩ := driveGroupFrom_ok (s := s) (p := p)
    (fun j t => DriveInv X s A.elist δ p l r a b c j t) (DriveDone X Y s A.elist)
    ⟨hX, rfl, EFrame.refl s, ⟨A, hI, rfl⟩, ⟨gh, hG⟩, hp, hs, hl, hr, by omega, by omega,
      Or.inl ⟨rfl, ha, hc⟩, rfl⟩
    (fun j t hD _ => hD.step hXs hP (by intro z h1 h2 h3; exact hδ z h1 h2 h3) hTlo hThi hbal0)
  refine ⟨t, hrun, ?_⟩
  rcases hres with hD | hD
  · -- `groupBudget` moves: G1 holds again
    obtain ⟨A', hI', hel⟩ := hD.inv
    obtain ⟨gh', hG'⟩ := hD.ginv
    refine ⟨Or.inl hD.x, hD.P, hD.ef, ⟨A', hI', hel⟩, ⟨gh', hG'.close hD.live hD.st ?_ ?_⟩⟩
    · rw [hD.ll, hD.rr]; exact hδ
    · have hsum := hD.sum
      have hcnt := hD.cnt
      have hbal := hD.bal
      unfold G1
      rw [hD.P, hD.ll, hD.rr, hm]
      simp only [Nat.sub_zero]
      have hbalK : gSz t l ≤ gSz t r + 1 ∧ gSz t r ≤ gSz t l + 1 := by
        rcases hbal with ⟨h0, -⟩ | ⟨-, h1, h2⟩
        · omega
        · exact ⟨h1, h2⟩
      refine ⟨by omega, ?_, hbalK.1, hbalK.2⟩
      -- `b - K + m (T - G) ≤ G`
      have hKm : s.P.groupBudget = m + 1 := by omega
      rw [hKm] at hcnt
      generalize hX0 : (a - δ l) + (b - δ p) + (c - δ r) - s.P.G = Xs at g2
      have hT : gSz t l + gSz t p + gSz t r - s.P.G = Xs + (δ l + δ p + δ r) := by omega
      rw [hT, Nat.mul_add]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hδs with h0 | h1
      · rw [h0, Nat.mul_zero]; omega
      · rw [h1, Nat.mul_one]; omega
  · exact hD

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### The group phase of `background` -/

/-- Room for the labels of a split start (Lemma C3 provides it). -/
def SplitRoom (s : Core) (g : Nat) : Prop :=
  ∃ labL labR, (labBefore g).run s = .ok labL s ∧ (labAfter g).run s = .ok labR s

theorem GInvE.weaken {s : Core} {L : List Nat} {gh : GGh} {δ : Nat → Nat} (hG : GInv s L gh δ)
    (x : Nat) : GInvE s L gh δ x :=
  { hG with split := fun g hg hs _ => hG.split g hg hs hg.1 }

/-- A quiet group that did not split leaves no undriven insertion. -/
theorem GInv.quiet_close {s : Core} {L : List Nat} {gh : GGh} {g : Nat}
    (hG : GInv s L gh (fun b => if b = g then 1 else 0)) (hq : gSt s g = .quiet)
    (hsz : gSz s g < s.P.G) : GInv s L gh (fun _ => 0) := by
  refine { hG with quiet := ?_, split := ?_ }
  · intro z hz hzs
    have := hG.quiet z hz hzs
    by_cases hzg : z = g
    · subst hzg; exact ⟨by simpa using hsz, this.2⟩
    · simp only [hzg, ite_false] at this; simpa using this
  · intro z hz hzs hzx
    have Fz := hG.fam z hz hzs
    have := hG.split z hz hzs hzx
    have h1 : gLl s z ≠ g := by intro e; have := Fz.lSt; rw [e, hq] at this; cases this
    have h2 : z ≠ g := by intro e; rw [e, hq] at hzs; cases hzs
    have h3 : gRr s z ≠ g := by intro e; have := Fz.rSt; rw [e, hq] at this; cases this
    unfold G1 at this ⊢
    simp only [h1, h2, h3, ite_false] at this
    simpa using this

/-- What the extra invariant must survive in the group phase. -/
structure XGroup (X Y : Core → Prop) (L : List Nat) (c : Nat) : Prop where
  drive : ∀ δ p, XSteps X Y L δ p c
  split : ∀ s A gh g labL labR, INV s A → A.elist = L →
    GInv s L gh (fun b => if b = g then 1 else 0) → LiveG s g → gSt s g = .quiet →
    gSz s g = s.P.G → (labBefore g).run s = .ok labL s → (labAfter g).run s = .ok labR s →
    X s → X (splitState s g labL labR)

/-- **The group phase.** After an insertion into group `g`, the optional split start and the
drive of `g`'s family succeed and restore `GInv` with no undriven insertion. -/
theorem groupPhase_ok {X Y : Core → Prop} {s : Core} {A : Abs} {gh : GGh} {g : Nat} (hI : INV s A)
    (hXg : XGroup X Y A.elist (gC s g)) (hX : X s)
    (hG : GInv s A.elist gh (fun b => if b = g then 1 else 0)) (hP : GParams s.P)
    (hg : LiveG s g) (hpos : 1 ≤ gSz s g)
    (hroom : gSt s g = .quiet → s.P.G ≤ gSz s g → SplitRoom s g) :
    ∃ s', (do
        if ((s.Gs.getX g).st == St.quiet && decide ((s.Gs.getX g).size ≥ s.P.G)) = true then
          startGroupSplit g
        else pure ()
        driveGroup g).run s = .ok () s' ∧ DriveDone X Y s A.elist s' := by
  have hδle : ∀ p, (fun b => if b = g then 1 else 0) p ≤ gSz s p := by
    intro p; by_cases h : p = g
    · subst h; simp [hpos]
    · simp [h]
  cases hst : gSt s g with
  | quiet =>
    by_cases hsz : s.P.G ≤ gSz s g
    · obtain ⟨labL, labR, hL, hR⟩ := hroom hst hsz
      have hc : ((s.Gs.getX g).st == St.quiet && decide ((s.Gs.getX g).size ≥ s.P.G)) = true := by
        simp only [gSt, gSz] at hst hsz; simp [hst, hsz]
      rw [ite_eq_left hc, run_bind, startGroupSplit_ok hg hL hR]
      dsimp only
      have hgG : gSz s g = s.P.G := by
        have := (hG.quiet g hg hst).1; simp at this; omega
      have hgl := hI.mem_glist_iff.mpr hg
      obtain ⟨hef1, A1, hI1, hel1⟩ := Good.ok_inv (good_startGroupSplit g) hI
        (startGroupSplit_ok hg hL hR)
      have hG1 := ginv_splitStart hI hG hg hst hsz labL labR
      have hX1 := hXg.split s A gh g labL labR hI rfl hG hg hst hgG hL hR hX
      have S := splitSpec hI hgl labL labR
      generalize splitState s g labL labR = s1 at hef1 hI1 hG1 hX1 S
      generalize gh.reset (splitL s g) (splitR s g) = gh1 at hG1
      have hg1 : LiveG s1 g := (S.live g).mpr (Or.inr (Or.inr hg))
      have hs1 : gSt s1 g = .splitting := by rw [S.st, ite_eq_left rfl]
      unfold driveGroup
      rw [run_getG_bind]
      simp only [gSt] at hs1
      rw [hs1]
      rw [← hel1] at hG1
      have hP1 : GParams s1.P := by rw [S.P]; exact hP
      have hXd : XSteps X Y A1.elist (fun _ => 0) g (gC s1 g) := by
        rw [hel1, S.chk, ite_eq_right (not_or.mpr ⟨S.ggl, S.ggr⟩)]; exact hXg.drive _ g
      obtain ⟨s2, hrun, hD⟩ := ginv_drive hI1 hXd
        hX1 (hG1.weaken g) hP1 hg1 hs1 (hG1.split g hg1 hs1 hg1.1) (fun _ _ _ _ => rfl)
        (by simp) (by simp)
      refine ⟨s2, hrun, ⟨hD.x, hD.P.trans S.P, hef1.trans hD.ef, ?_, ?_⟩⟩
      · rw [← hel1]; exact hD.inv
      · rw [← hel1]; exact hD.ginv
    · have hc : ¬ ((s.Gs.getX g).st == St.quiet && decide ((s.Gs.getX g).size ≥ s.P.G)) = true := by
        simp only [gSt, gSz] at hst hsz; simp [hst]; omega
      rw [ite_eq_right hc]
      dsimp only
      unfold driveGroup
      rw [run_getG_bind]
      simp only [gSt] at hst
      rw [hst]
      exact ⟨s, rfl, ⟨Or.inl hX, rfl, EFrame.refl s, ⟨A, hI, rfl⟩,
        ⟨gh, hG.quiet_close hst (by omega)⟩⟩⟩
  | overflow =>
    have hc : ¬ ((s.Gs.getX g).st == St.quiet && decide ((s.Gs.getX g).size ≥ s.P.G)) = true := by
      simp only [gSt] at hst; simp [hst]
    rw [ite_eq_right hc]
    dsimp only
    unfold driveGroup
    rw [run_getG_bind]
    obtain ⟨hp, hps, hlr⟩ := hG.ovf g hg hst
    have Fp := hG.fam _ hp hps
    have hl0 : gLl s (gSrc s g) ≠ gSrc s g := Fp.lp hI hp
    have hr0 : gRr s (gSrc s g) ≠ gSrc s g := Fp.rp hI hp
    have hgp : gSrc s g ≠ g := by intro e; rw [e, hst] at hps; cases hps
    have hlr0 : gLl s (gSrc s g) ≠ gRr s (gSrc s g) := Fp.lr hI hp
    have hδs : (fun b => if b = g then 1 else 0) (gLl s (gSrc s g)) +
        (fun b => if b = g then 1 else 0) (gSrc s g) +
        (fun b => if b = g then 1 else 0) (gRr s (gSrc s g)) ≤ 1 := by
      rcases hlr with e | e
      · have : gRr s (gSrc s g) ≠ g := fun h => hlr0 (e.trans h.symm)
        simp [e, hgp, this]
      · have : gLl s (gSrc s g) ≠ g := fun h => hlr0 (h.trans e.symm)
        simp [e, hgp, this]
    simp only [gSt] at hst
    rw [hst]
    simp only
    have hXd : XSteps X Y A.elist (fun b => if b = g then 1 else 0) (gSrc s g) (gC s (gSrc s g))
      := by
      rcases hlr with e | e
      · rw [← Fp.lC, e]; exact hXg.drive _ _
      · rw [← Fp.rC, e]; exact hXg.drive _ _
    obtain ⟨s2, hrun, hD⟩ := ginv_drive hI hXd hX (hG.weaken (gSrc s g)) hP hp hps
      (hG.split _ hp hps hp.1)
      (by intro z h1 h2 h3; have : z ≠ g := by
            rintro rfl; rcases hlr with e | e <;> [exact h1 e.symm; exact h3 e.symm]
          simp [this])
      hδs ⟨hδle _, hδle _, hδle _⟩
    exact ⟨s2, hrun, hD⟩
  | splitting =>
    have hc : ¬ ((s.Gs.getX g).st == St.quiet && decide ((s.Gs.getX g).size ≥ s.P.G)) = true := by
      simp only [gSt] at hst; simp [hst]
    rw [ite_eq_right hc]
    dsimp only
    unfold driveGroup
    rw [run_getG_bind]
    have Fp := hG.fam g hg hst
    have hl0 : gLl s g ≠ g := Fp.lp hI hg
    have hr0 : gRr s g ≠ g := Fp.rp hI hg
    simp only [gSt] at hst
    rw [hst]
    simp only
    obtain ⟨s2, hrun, hD⟩ := ginv_drive hI (hXg.drive _ _) hX (hG.weaken g) hP hg hst
      (hG.split g hg hst hg.1) (by intro z _ h2 _; simp [h2]) (by simp [hl0, hr0])
      ⟨hδle _, hδle _, hδle _⟩
    exact ⟨s2, hrun, hD⟩
  | dead => exact absurd hst (hG.notDead g hg)

end OrderMaintenance.Proof
