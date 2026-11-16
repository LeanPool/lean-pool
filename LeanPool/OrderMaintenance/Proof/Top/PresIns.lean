/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Top.InsViews


/-!
# M5: a chunk split keeps the invariant (the contract's `start`)

`insertAround x y z` on the linked core succeeds, writes tags that pass their guards, and the top
structure with the job's path copy completed satisfies the invariant, with the job at its start.
-/


@[expose] public section

namespace OrderMaintenance.Proof.Top

open OrderMaintenance.Model OrderMaintenance.Proof
/-! ### Room for an insertion event -/

theorem gapsGe_mono {β B B' : Nat} {ls : List Nat} (h : B' ≤ B) (hg : GapsGe β B ls) : GapsGe β B' ls :=
  List.IsChain.imp (fun a b hab => by omega) hg

theorem gapB_succ (β n d : Nat) : gapB β n (d + 1) = gapB β n d / 2 := by
  unfold gapB; rw [Nat.pow_succ, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul,
    Nat.div_div_eq_div_mul]

theorem gap_two {β n0 dr D nmax : Nat} (hn0 : n0 ≤ nmax) (hdr : dr + 1 ≤ D)
    (hroom : 2 ^ D * (nmax + 1) ≤ 2 ^ β) : 2 ≤ gapB β n0 dr := by
  unfold gapB
  have h1 : 2 ^ (dr + 1) * (n0 + 1) ≤ 2 ^ β := by
    calc 2 ^ (dr + 1) * (n0 + 1) ≤ 2 ^ D * (nmax + 1) :=
          Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hdr) (by omega)
      _ ≤ 2 ^ β := hroom
  have h2 : 2 ^ (dr + 1) ≤ 2 ^ β / (n0 + 1) := by
    rw [Nat.le_div_iff_mul_le (by omega)]; exact h1
  rw [Nat.le_div_iff_mul_le (by positivity)]
  calc 2 * 2 ^ dr = 2 ^ (dr + 1) := by ring
    _ ≤ 2 ^ β / (n0 + 1) := h2

/-! ### Between jobs -/

section between
variable {s : TS} {cl : List Nat} {ord : Nat → List Nat} (S : Shape s cl ord) (Ti : Timing s cl none)
include S Ti

/-- Between jobs, a running drain has had fewer than `K_h` funding jobs. -/
theorem Timing.fund_lt (hTP : TopParams s.P) {v : Nat} (hg : ghostN s v) :
    fundOf s cl v + 1 ≤ Kd s.P (ht s v) := by
  have h1 := Ti.wC v hg
  have h2 := (Ti.wB v hg).2
  have hs := hTP.s3
  simp only [slack, Nat.add_zero] at h1
  unfold Kd
  have : fundOf s cl v ≤ (Wd s.P (ht s v) + 2) / (s.P.s - 2) := by
    rw [Nat.le_div_iff_mul_le (by omega), Nat.mul_comm]; omega
  omega

/-- Between jobs, a live non-root node weighs at most `W_h`. -/
theorem Timing.tw_live (hTP : TopParams s.P) {u : Nat} (hu : liveN s u)
    (hp : (nd s u).livePar ≠ NIL) : tw s cl u ≤ Wd s.P (ht s u) := by
  have hw := Ti.wts u hu
  simp only [pend, List.not_mem_nil, ite_false, Nat.add_zero] at hw
  rw [← hw]
  by_cases hs : srcOf s u = NIL
  · exact Ti.wA u hu hp hs
  · obtain ⟨hg, htg⟩ := S.src u hu hs
    generalize hgv : srcOf s u = g at hg htg
    obtain ⟨-, -, hh1, hh2, -⟩ := S.ghost _ hg
    have := Ti.release S hTP hg htg (by simp [pend])
    have hhu : ht s u = ht s g := by rcases htg with e | e <;> rw [e] <;> assumption
    rw [hhu]; exact this

end between

/-! ### The split's tables have room -/

theorem table_split {t : List (Nat × Nat)} {e : Nat} (he : e ∈ t.map (·.1)) :
    ∃ A le Bs, t = A ++ (e, le) :: Bs ∧ e ∉ A.map (·.1) := by
  induction t with
  | nil => simp at he
  | cons p r ih =>
    obtain ⟨k, l⟩ := p
    by_cases hk : k = e
    · subst hk; exact ⟨[], l, r, rfl, by simp⟩
    · have he' : e ∈ r.map (·.1) := by simp at he ⊢; rcases he with h | h <;> [exact absurd h.symm hk; exact h]
      obtain ⟨A, le, Bs, h1, h2⟩ := ih he'
      exact ⟨(k, l) :: A, le, Bs, by simp [h1], by simp [h2, Ne.symm hk]⟩

/-- **The tables of the split chunk have room on both sides of it.** -/
theorem start_room {s : TS} {cl : List Nat} {ord : Nat → List Nat} {dr n0 : Nat → Nat}
    (hI : InvJ s cl ord dr n0 none) (hTP : TopParams s.P) {x T : Nat} (hx : x ∈ cl)
    (hT : T ∈ cinT s x) (y z : Nat) :
    ∃ A le Bs, (nd s T).table = A ++ (x, le) :: Bs ∧ x ∉ A.map (·.1) ∧
      ((nd s T).draining = true → (lookup (nd s T).side x).isSome) ∧
      roomLo A le true < roomHi s.P.beta Bs le true ∧ roomLo A le false < roomHi s.P.beta Bs le false ∧
      2 ≤ gapB s.P.beta (n0 T) (dr T) ∧
      GapsGe s.P.beta (gapB s.P.beta (n0 T) (dr T) / 2)
        ((A ++ (y, (roomLo A le true + roomHi s.P.beta Bs le true - 1) / 2) :: (x, le) ::
          (z, (roomLo A le false + roomHi s.P.beta Bs le false - 1) / 2) :: Bs).map (·.2)) := by
  have S := hI.shape
  have Ti := hI.time
  have Ro := hI.room
  have hent : Ent ord 0 x := by unfold Ent; rw [S.ord0]; exact hx
  have hT' : T ∈ tabs s 0 x := by unfold tabs; rw [ite_eq_left rfl]; exact hT
  obtain ⟨hTN, hTh, hxT⟩ := (S.tabsIff 0 x T hent).mp hT'
  simp only [Nat.zero_add] at hTh
  obtain ⟨A, le, Bs, htab, hA⟩ := table_split (t := (nd s T).table) hxT
  -- the drain bound of the table
  have hew : ew s cl T + 2 ≤ Pid s.P 1 := by
    obtain ⟨hl, hlh, -⟩ := S.lp x hx
    have hpar : par s 0 x = lpr s x := by simp [par]
    rcases S.Q 0 x T hent hT' with h | h <;> rw [hpar] at h
    · subst h
      obtain ⟨hpl, -, -⟩ := S.up _ hl (by have := S.H3; omega)
      have hw := Ti.tw_live S hTP hl (fun e => hpl.1.1 e)
      have : ew s cl (lpr s x) = tw s cl (lpr s x) := by unfold ew; rw [ite_eq_right (by rw [hl.2]; simp)]
      rw [this]; rw [hlh] at hw; unfold Pid; omega
    · have hsn : srcOf s (lpr s x) ≠ NIL := fun e => hTN.1 (h.trans e)
      obtain ⟨hg, -⟩ := S.src _ hl hsn
      rw [← h] at hg
      have hf := Ti.fund_lt S hTP hg
      have hF := Ti.wF T hg
      have hB := (Ti.wB T hg).2
      rw [hTh] at hf hB
      unfold fundOf at hf
      unfold Pid; omega
  have hdr : dr T + 1 ≤ Dmax s.P 1 := by
    have hp := Ro.pot1 T hTN hTh
    unfold Dmax; simp only [le_refl, ite_true]; omega
  have hB := gap_two (Ro.n0le T hTN) hdr (by have := hTP.room 1 le_rfl; rw [hTh]; exact this)
  have hg := Ro.gaps T hTN
  unfold labs at hg; rw [htab] at hg
  obtain ⟨r1, r2, r3⟩ := gaps_room_around (y := y) (z := z) hB hg
  refine ⟨A, le, Bs, htab, hA, fun hd => ?_, r1, r2, hB, r3⟩
  have := S.side T ⟨hTN, hd⟩ x hxT
  rw [this]; rfl

/-! ### Views of the state after the split -/

namespace InsFrame
variable {s : Core} {x f1x i1 : Nat} {t : TS} (F : InsFrame s x f1x i1 t)
include F

theorem height (u : Nat) : (nd t u).height = (nd (ts s) u).height := by
  rw [F.node]; unfold insNode; split_ifs <;> rfl
theorem livePar (u : Nat) : (nd t u).livePar = (nd (ts s) u).livePar := by
  rw [F.node]; unfold insNode; split_ifs <;> rfl
theorem weight (u : Nat) : (nd t u).weight = (nd (ts s) u).weight := by
  rw [F.node]; unfold insNode; split_ifs <;> rfl
theorem inTables (u : Nat) : (nd t u).inTables = (nd (ts s) u).inTables := by
  rw [F.node]; unfold insNode; split_ifs <;> rfl
theorem draining (u : Nat) : (nd t u).draining = (nd (ts s) u).draining := by
  rw [F.node]; unfold insNode; split_ifs <;> rfl
theorem t1 (u : Nat) : (nd t u).t1 = (nd (ts s) u).t1 := by
  rw [F.node]; unfold insNode; split_ifs <;> rfl
theorem t2 (u : Nat) : (nd t u).t2 = (nd (ts s) u).t2 := by
  rw [F.node]; unfold insNode; split_ifs <;> rfl
theorem overflowOf (u : Nat) : (nd t u).overflowOf = (nd (ts s) u).overflowOf := by
  rw [F.node]; unfold insNode; split_ifs <;> rfl
theorem alive (u : Nat) : (nd t u).alive = (nd (ts s) u).alive := by
  rw [F.node]; unfold insNode; split_ifs <;> rfl
theorem first (u : Nat) : (nd t u).first = insFirst s x u := by rw [F.node]
theorem last (u : Nat) : (nd t u).last = insLast s x u := by rw [F.node]
theorem table (u : Nat) : (nd t u).table = if u ∈ s.cin.getX x ∧ u < s.nodes.size then
    aroundT (s.nodes.getX u).table x s.C.size (s.C.size + 1) (insF s x u).1 (insF s x u).2
    else (s.nodes.getX u).table := by
  rw [F.node]; unfold insNode; split_ifs <;> rfl
theorem side (u : Nat) : (nd t u).side = if u ∈ s.cin.getX x ∧ u < s.nodes.size then
    sideAround (s.nodes.getX u) x s.C.size (s.C.size + 1) else (s.nodes.getX u).side := by
  rw [F.node]; unfold insNode; split_ifs <;> rfl
theorem children (u : Nat) : (nd t u).children = if u = s.lpar.getX x ∧ u < s.nodes.size then
    (s.nodes.getX u).children.replace1 x [s.C.size, x, s.C.size + 1] else (s.nodes.getX u).children := by
  rw [F.node]; unfold insNode; split_ifs <;> rfl

theorem par_pos {h : Nat} (hh : 1 ≤ h) (e : Nat) : par t h e = par (ts s) h e := by
  unfold par; simp only [show h ≠ 0 by omega, ite_false, F.draining, F.t1, F.livePar]

theorem par_zero (e : Nat) : par t 0 e = lpr t e := by unfold par; rw [ite_eq_left rfl]

theorem ht (u : Nat) : Top.ht t u = Top.ht (ts s) u := F.height u
theorem isN (u : Nat) : Top.isN t u ↔ Top.isN (ts s) u := by
  unfold Top.isN; rw [F.size, F.alive]; rfl
theorem liveN (u : Nat) : Top.liveN t u ↔ Top.liveN (ts s) u := by
  unfold Top.liveN; rw [F.isN, F.draining]
theorem ghostN (u : Nat) : Top.ghostN t u ↔ Top.ghostN (ts s) u := by
  unfold Top.ghostN; rw [F.isN, F.draining]
theorem srcOf (u : Nat) : Top.srcOf t u = Top.srcOf (ts s) u := F.overflowOf u

theorem anc_old (c : Nat) (hy : c ≠ s.C.size) (hz : c ≠ s.C.size + 1) :
    ∀ j, Top.anc t c j = Top.anc (ts s) c j
  | 0 => rfl
  | 1 => by show lpr t c = lpr (ts s) c; rw [F.lpar, ite_eq_right (by omega)]
  | j + 2 => by
    show (nd t (Top.anc t c (j + 1))).livePar = (nd (ts s) (Top.anc (ts s) c (j + 1))).livePar
    rw [anc_old c hy hz (j + 1), F.livePar]

theorem anc_new (c : Nat) (hc : c = s.C.size ∨ c = s.C.size + 1) :
    ∀ j, 1 ≤ j → Top.anc t c j = Top.anc (ts s) x j
  | 0, h => absurd h (by omega)
  | 1, _ => by show lpr t c = lpr (ts s) x; rw [F.lpar, ite_eq_left hc]
  | j + 2, _ => by
    show (nd t (Top.anc t c (j + 1))).livePar = (nd (ts s) (Top.anc (ts s) x (j + 1))).livePar
    rw [anc_new c hc (j + 1) (by omega), F.livePar]

theorem pp_old (c : Nat) (hy : c ≠ s.C.size) (hz : c ≠ s.C.size + 1) (j : Nat) :
    Top.pp t c j = Top.pp (ts s) c j := by
  unfold Top.pp; split
  · rfl
  · rw [F.path, ite_eq_right (by omega)]

theorem pp_new (c : Nat) (hc : c = s.C.size ∨ c = s.C.size + 1) (j : Nat) (hj1 : 1 ≤ j)
    (hj : j ≤ s.P.H) : Top.pp t c j = Top.pp (ts s) x j := by
  unfold Top.pp; rw [ite_eq_right (by omega), ite_eq_right (by omega), F.path, ite_eq_left hc, ite_eq_left ⟨hj1, hj⟩]

end InsFrame

end OrderMaintenance.Proof.Top
