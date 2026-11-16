/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.Job


/-!
# M6: the reservation loop at Level M

`reservation k`: up to `k` rounds; a round resumes the running job, or, with no job, pops the
fullest quiet chunk and starts its split, or stops when the queue is empty. The machine has no
`return`, so a flag `dn` makes the remaining rounds empty, as in `driveGroupFrom`.
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model
open OrderMaintenance.Proof.Top
open OrderMaintenance.Machine (Reg BinOp UnOp)

local notation "upd" => OrderMaintenance.Machine.State.upd

/-- The body of Level F's reservation loop (as elaborated). -/
def resF : Nat → Option Unit × Unit → CM (ForInStep (Option Unit × Unit)) := fun _ _ => do
  let d ← get
  match d.resJob with
  | none => do
    let e ← pqEmpty
    if e = true then pure (ForInStep.done (some (), ())) else do
      let c ← pqPopMax
      splitChunkStart c
      pure (ForInStep.yield (none, ()))
  | some job => do
    let r ← jobStep job
    modify fun s => { s with resJob := r }
    pure (ForInStep.yield (none, ()))

theorem reservation_eq (k : Nat) (s : Core) :
    (reservation k).run s = ((forIn (List.range k) ((none : Option Unit), ()) resF) >>= fun r =>
      match r.1 with | some r => pure r | none => pure ()).run s := by
  unfold reservation
  congr 2
  funext x a
  rcases x with ⟨_ | _, _⟩ <;> rfl

def jobP : Proc := { name := "jobStep", params := [], rets := [], body := jobStepS }
def splitP : Proc := { name := "splitChunkStart", params := ["x"], rets := [], body := splitChunkStartS }

def resBody : Stm := cm{
  if dn = 0 then {
    if O.jobOn then call jobP()
    else {
      em ← pqEmptyP()
      if em then dn := 1 else { x ← pqPopMaxP(); call splitP(x) } } } }
/-- `reservation reservationBudget`. -/
def reservationS : Stm := cm{ dn := 0; for ri < P.KR do resBody }

/-- A Level M round that agrees with a Level F one (`stop`: Level F's round ended the loop). -/
def ResAgree (κ : Caps) (t t' : Core) (stop : Bool) (D : Nat) : Prop :=
  ∀ L : Loc, L "dn" = 0 → ∃ L' n, evalF κ resBody t L = .ok t' L' n ∧ L' "dn" = b2n stop ∧ n ≤ D

/-- A round's Level F outcome: stop (`done`) or go on (`yield`). -/
def resOut (stop : Bool) : ForInStep (Option Unit × Unit) :=
  if stop then .done (some (), ()) else .yield (none, ())

theorem reservationS_agree (κ : Caps) (s : Core) (L : Loc) {D : Nat}
    (I : Nat → Core → Prop) (h0 : I 0 s)
    (hstep : ∀ j t, I j t → j < s.P.reservationBudget → ∃ stop t', (resF j ((none : Option Unit), ())).run t = .ok (resOut stop) t' ∧
      (stop = false → I (j + 1) t') ∧ ResAgree κ t t' stop D) :
    ∃ t' L' n, (reservation s.P.reservationBudget).run s = .ok () t' ∧ evalF κ reservationS s L
      = .ok t' L' n ∧
      n ≤ 5 + s.P.reservationBudget * (D + 6) := by
  set K := s.P.reservationBudget
  set R := fun (l : List Nat) (t : Core) => (forIn l ((none : Option Unit), ()) resF).run t
  -- Level F's loop ends
  have hF : ∀ (n j : Nat) (t : Core), I j t → j + n = K →
      ∃ c tF, R ((List.range K).drop j) t = .ok c tF := by
    intro n; induction n with
    | zero =>
      intro j t _ hj; refine ⟨(none, ()), t, ?_⟩
      simp only [R, show j = K by omega]; rw [List.drop_of_length_le (by simp)]; rfl
    | succ n ih =>
      intro j t hI hj
      have hjK : j < K := by omega
      rw [List.drop_eq_getElem_cons (by simpa using hjK), List.getElem_range]
      obtain ⟨stop, t', hr, hI', -⟩ := hstep j t hI hjK
      cases stop
      · obtain ⟨c, tF, h⟩ := ih (j + 1) t' (hI' rfl) (by omega)
        exact ⟨c, tF, by simp only [R, List.forIn_cons, OrderMaintenance.Proof.run_bind, hr, resOut]; exact h⟩
      · exact ⟨_, _, by simp only [R, List.forIn_cons, OrderMaintenance.Proof.run_bind, hr, resOut]; rfl⟩
  obtain ⟨c0, tF, hR0⟩ := hF K 0 s h0 (by omega)
  simp only [List.drop_zero] at hR0
  have hFrun : (reservation s.P.reservationBudget).run s = .ok () tF := by
    rw [reservation_eq, OrderMaintenance.Proof.run_bind]
    have hR0' : (forIn (List.range s.P.reservationBudget) ((none : Option Unit), ()) resF).run s = .ok c0 tF := hR0
    rw [hR0']
    dsimp only
    split <;> rfl
  -- Level M's loop
  have a1 := evalF_assign_ok (κ := κ) (s := s) (L := L) (x := "dn") (e := (0 : Exp)) (v := 0) rfl
  obtain ⟨S', L', c, he, hc, hI⟩ := evalF_loop (κ := κ) (x := "ri") (n := .prm .KR) (b := resBody) (s := s)
    (L := upd L "dn" 0) (N := K) (by simp [Exp.ev, PF.get, K])
    (fun j S L' => (L' "dn" = 0 ∧ I j S ∧ ∃ c, R ((List.range K).drop j) S = .ok c tF) ∨
      (L' "dn" = 1 ∧ S = tF)) (D + 5)
    (Or.inl ⟨by simp [OrderMaintenance.Machine.State.upd], h0, c0, by simpa using hR0⟩)
    (by
      intro j hj S L1 hcase
      set L2 := upd L1 "ri" j
      rcases hcase with ⟨hdn, hIj, c1, hR⟩ | ⟨hdn, hSF⟩
      · have h2dn : L2 "dn" = 0 := by simp [L2, OrderMaintenance.Machine.State.upd, hdn]
        obtain ⟨stop, t', hr, hI', hRA⟩ := hstep j S hIj hj
        obtain ⟨L3, n3, e3, h3dn, hn3⟩ := hRA L2 h2dn
        rw [List.drop_eq_getElem_cons (by simpa using hj), List.getElem_range] at hR
        cases stop
        · simp only [R, List.forIn_cons, OrderMaintenance.Proof.run_bind, hr, resOut] at hR
          exact ⟨t', L3, n3, e3, by omega, Or.inl ⟨by simpa [b2n] using h3dn, hI' rfl, c1, hR⟩⟩
        · simp only [R, List.forIn_cons, OrderMaintenance.Proof.run_bind, hr, resOut] at hR
          injection hR with _ hT; subst hT
          exact ⟨t', L3, n3, e3, by omega, Or.inr ⟨by simpa [b2n] using h3dn, rfl⟩⟩
      · subst hSF
        have hc0 : ("dn" =ₑ 0 : Exp).ev κ S L2 = some 0 := by simp [Exp.ev, OrderMaintenance.Machine.BinOp.eval, L2,
          OrderMaintenance.Machine.State.upd, hdn]
        exact ⟨S, L2, _, evalF_ite_f hc0 evalF_skip, by simp [Exp.cost],
          Or.inr ⟨by simp [L2, OrderMaintenance.Machine.State.upd, hdn], rfl⟩⟩)
  have hS' : S' = tF := by
    rcases hI with ⟨hdn, hIK, c2, hR⟩ | ⟨hdn, h⟩
    · rw [List.drop_of_length_le (by simp)] at hR
      simp only [R] at hR
      injection hR
    · exact h
  subst hS'
  refine ⟨S', L', _, hFrun, evalF_seq_ok2 a1 he, ?_⟩
  have e : K * (1 + (D + 5)) = K * (D + 6) := by ring
  simp only [Exp.cost] at hc ⊢; omega

/-! ### The three kinds of rounds -/

theorem resF_empty {t : Core} {j : Nat} (hj : t.resJob = none) (h0 : t.pqHi = 0) :
    (resF j ((none : Option Unit), ())).run t = .ok (resOut true) t := by
  simp [resF, OrderMaintenance.Proof.run_bind, hj, pqEmpty, h0, resOut]

theorem resAgree_empty {κ : Caps} {t : Core} (hj : t.resJob = none) (h0 : t.pqHi = 0) : ResAgree κ t t true 40 := by
  intro L hdn
  obtain ⟨Le, ce, ee, her, hce⟩ := pqEmpty_agree κ t (OrderMaintenance.Machine.State.setLocs (fun _ => 0) [] [])
    (b := true) (σ' := t) (by simp [pqEmpty, h0])
  have e1 := evalF_call_ok (q := pqEmptyP) (args := []) (ds := ["em"]) (L := L) (by simp [evList]) ee
  set L1 := OrderMaintenance.Machine.State.setLocs L ["em"] (pqEmptyP.rets.map Le)
  have h1em : L1 "em" = 1 := by simp [L1, pqEmptyP, OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd, her, b2n]
  have e2 := evalF_assign_ok (κ := κ) (s := t) (L := L1) (x := "dn") (e := (1 : Exp)) (v := 1) rfl
  refine ⟨_, _, evalF_ite_t (v := 1) (by simp [Exp.ev, OrderMaintenance.Machine.BinOp.eval, hdn]) one_ne_zero
    (evalF_ite_f (by simp [Exp.ev, OF.get, hj, b2n]) (evalF_seq_ok2 e1 (evalF_ite_t (v := 1)
      (by simp [Exp.ev,
        h1em]) one_ne_zero e2))), by simp [OrderMaintenance.Machine.State.upd, b2n], ?_⟩
  simp [Exp.cost, costList] at hce ⊢; omega

/-- The program agrees with Level F's `jobStep j` from `t` (within `D` steps). -/
def JobAgree (κ : Caps) (t : Core) (j : Job) (D : Nat) : Prop :=
  ∀ r t1, (jobStep j).run t = .ok r t1 →
    ∃ L' c, evalF κ jobStepS t (OrderMaintenance.Machine.State.setLocs (fun _ => 0) [] []) = .ok { t1 with resJob := r } L' c ∧ c ≤ D

theorem resF_job {t t1 : Core} {i : Nat} {j : Job} {r : Option Job} (hj : t.resJob = some j)
    (h : (jobStep j).run t = .ok r t1) :
    (resF i ((none : Option Unit), ())).run t = .ok (resOut false) { t1 with resJob := r } := by
  simp only [resF, OrderMaintenance.Proof.run_bind, OrderMaintenance.Proof.run_get, hj]
  simp only [OrderMaintenance.Proof.run_bind, h]; rfl

theorem resAgree_job {κ : Caps} {t t1 : Core} {j : Job} {r : Option Job} {D : Nat} (hj : t.resJob = some j)
    (hA : JobAgree κ t j D) (h : (jobStep j).run t = .ok r t1) :
    ResAgree κ t { t1 with resJob := r } false (D + 10) := by
  intro L hdn
  obtain ⟨Lj, cj, ej, hcj⟩ := hA r t1 h
  have e1 := evalF_call_ok (q := jobP) (args := []) (ds := []) (L := L) (by simp [evList]) ej
  refine ⟨_, _, evalF_ite_t (v := 1) (by simp [Exp.ev, OrderMaintenance.Machine.BinOp.eval, hdn]) one_ne_zero
    (evalF_ite_t (v := 1) (by simp [Exp.ev, OF.get, hj, b2n]) one_ne_zero e1),
    by simp [OrderMaintenance.Machine.State.setLocs, hdn, b2n], ?_⟩
  simp [Exp.cost, costList]; omega

/-- The program agrees with Level F's `splitChunkStart c` from `t` (within `D` steps). -/
def SplitAgree (κ : Caps) (t : Core) (c D : Nat) : Prop :=
  ∀ t2, (splitChunkStart c).run t = .ok () t2 →
    ∃ L' n, evalF κ splitChunkStartS t (OrderMaintenance.Machine.State.setLocs (fun _ => 0) ["x"] [c]) = .ok t2 L' n ∧ n ≤ D

theorem resF_split {t t1 t2 : Core} {i c : Nat} (hj : t.resJob = none) (h0 : t.pqHi ≠ 0)
    (hp : pqPopMax.run t = .ok c t1) (hs : (splitChunkStart c).run t1 = .ok () t2) :
    (resF i ((none : Option Unit), ())).run t = .ok (resOut false) t2 := by
  simp only [resF, OrderMaintenance.Proof.run_bind, OrderMaintenance.Proof.run_get, hj]
  simp only [pqEmpty, OrderMaintenance.Proof.run_bind]
  simp [h0]
  simp only [OrderMaintenance.Proof.run_bind, hp, hs]; rfl

theorem resAgree_split {κ : Caps} {t t1 t2 : Core} {c D : Nat} (hj : t.resJob = none) (hq : PQCaps κ t)
    (h0 : t.pqHi ≠ 0) (hp : pqPopMax.run t = .ok c t1) (hA : SplitAgree κ t1 c D)
    (hs : (splitChunkStart c).run t1 = .ok () t2) :
    ResAgree κ t t2 false (D + 300) := by
  intro L hdn
  obtain ⟨Le, ce, ee, her, hce⟩ := pqEmpty_agree κ t (OrderMaintenance.Machine.State.setLocs (fun _ => 0) [] [])
    (b := false) (σ' := t) (by simp [pqEmpty, h0])
  have e1 := evalF_call_ok (q := pqEmptyP) (args := []) (ds := ["em"]) (L := L) (by simp [evList]) ee
  set L1 := OrderMaintenance.Machine.State.setLocs L ["em"] (pqEmptyP.rets.map Le)
  have h1em : L1 "em" = 0 := by simp [L1, pqEmptyP, OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd, her, b2n]
  have h1dn : L1 "dn" = 0 := by simp [L1, pqEmptyP, OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd, hdn]
  obtain ⟨⟨Lp, cp, ep, hcp, hncp⟩, -⟩ := pqPopMax_agree κ t (OrderMaintenance.Machine.State.setLocs (fun _ => 0) [] []) hq hp
  have e2 := evalF_call_ok (q := pqPopMaxP) (args := []) (ds := ["x"]) (L := L1) (by simp [evList]) ep
  set L2 := OrderMaintenance.Machine.State.setLocs L1 ["x"] (pqPopMaxP.rets.map Lp)
  have h2x : L2 "x" = c := by simp [L2, pqPopMaxP, OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd, hcp]
  have h2dn : L2 "dn" = 0 := by simp [L2, pqPopMaxP, OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd, h1dn]
  obtain ⟨Ls, cs, es, hcs⟩ := hA t2 hs
  have e3 := evalF_call_ok (q := splitP) (args := [.var "x"]) (ds := []) (L := L2) (by simp [evList, Exp.ev, h2x]) es
  refine ⟨_, _, evalF_ite_t (v := 1) (by simp [Exp.ev, OrderMaintenance.Machine.BinOp.eval, hdn]) one_ne_zero
    (evalF_ite_f (by simp [Exp.ev, OF.get, hj, b2n]) (evalF_seq_ok2 e1 (evalF_ite_f
      (by simp [Exp.ev,
        h1em]) (evalF_seq_ok2 e2 e3)))), by simp [OrderMaintenance.Machine.State.setLocs, h2dn,
        b2n], ?_⟩
  simp [Exp.cost, costList] at hce hncp ⊢; omega

theorem splitAgree_ok {κ : Caps} {s : Core} {x f1x i1 B : Nat} (hx0 : x ≠ NIL)
    (hxs : x < s.C.size) (hC : s.C.size + 2 ≤ κ.tbl .C)
    (hp : (s.C.getX x).prev ≠ NIL → (s.C.getX x).prev < s.C.size)
    (hn : (s.C.getX x).next ≠ NIL → (s.C.getX x).next < s.C.size)
    (hia : IAOK κ (linkChunkPair (OrderMaintenance.Proof.push2 s) x s.C.size (s.C.size + 1)) x s.C.size (s.C.size + 1) f1x i1 B) :
    SplitAgree κ s x (150 + iaCost (linkChunkPair (OrderMaintenance.Proof.push2 s) x s.C.size (s.C.size + 1)) x B) := by
  intro t2 h
  rw [OrderMaintenance.Proof.splitChunkStart_ok hx0 hxs hia.run] at h
  injection h with _ h2; subst h2
  obtain ⟨L', c, e, hc, -⟩ := splitChunkStartS_ok (κ := κ) (L := OrderMaintenance.Machine.State.setLocs (fun _ => 0) ["x"] [x])
    (by simp [OrderMaintenance.Machine.State.setLocs,
      OrderMaintenance.Machine.State.upd]) hx0 hxs hC hp hn hia
  exact ⟨L', c, e, hc⟩

end OrderMaintenance.Impl
