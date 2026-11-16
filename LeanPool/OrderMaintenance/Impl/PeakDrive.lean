/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.PeakCore1
public import LeanPool.OrderMaintenance.Impl.PeakFrame
public import LeanPool.OrderMaintenance.Impl.ChunkStep


/-!
# Theorem W, option (A), stage A2: the drive loops

`driveLoop q g k`: up to `K` steps of procedure `q` on the record in local `g`, stopping when a
step returns 0 (the shape of `driveGroupFromS` and `driveChunkFromS`). `driveLoop_pk` bounds its
peak along a Level F invariant `I` of the drive (as in `driveGroupFromS_agree`), given the peak
bound of each step.

Nothing here is used by Theorems A and B.
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model
open OrderMaintenance.Machine (Reg BinOp UnOp State)

variable {K KH W : Nat} {κ : Caps}

/-- The drive loop: up to `k` steps of `q` on local `g`, stopping when one returns 0. -/
def driveLoop (q : Proc) (g : Reg) (k : PF) : Stm := cm{
  dn := 0
  for jj < ‹.prm k› do if dn = 0 then { ok ← q(‹g›); if ok = 0 then dn := 1 } }

theorem driveGroupFromS_eq : driveGroupFromS = driveLoop groupSplitStepP "g" .KG := rfl
theorem driveChunkFromS_eq : driveChunkFromS = driveLoop chunkSplitStepP "x" .KC := rfl

section drive
variable {s : Core} {L : Loc}
variable (hC : CapsW K κ) (hK : 8 ≤ K) (hW : 2 * K + 4 ≤ W)
include hC hK hW

/-- **The drive loop**, along a Level F invariant `I` of the drive: from a state with `I j t`, the
step ends in `t'` with result `b` (and `I (j + 1) t'` if `b`), and its peak is bounded. -/
theorem driveLoop_pk {q : Proc} {g : Reg} {k : PF} {Γq : Reg → Nat} (hq : q.params = [g])
    (hr : q.rets = ["ok"]) (hrK : Γq "ok" ≤ K) (hg1 : g ≠ "ok") (hg2 : g ≠ "jj") (hg3 : g ≠ "dn") {p : Nat}
    (I : Nat → Core → Prop) (h0 : I 0 s)
    (hstep : ∀ j t, I j t → j < k.get s.P → ∃ b t' L' n,
      evalF κ q.body t (OrderMaintenance.Machine.State.setLocs (fun _ => 0) [g] [p]) = .ok t' L' n ∧ L' "ok" = b2n b ∧
      (b = true → I (j + 1) t') ∧
      (Gd K KH κ (ΓK K) t (OrderMaintenance.Machine.State.setLocs (fun _ => 0) [g] [p]) →
        PKok K KH κ Γq W q.body t (OrderMaintenance.Machine.State.setLocs (fun _ => 0) [g] [p])))
    (hG : Gd K KH κ (ΓK K) s L) (hg : L g = p) : PKok K KH κ (ΓK K) W (driveLoop q g k) s L := by
  unfold driveLoop
  refine PKok.seq (PK.ok (PK.of_safe hC (by omega) (by omega) (by safe_tac) hG)) (fun s1 L1 n1 h1 hG1 => ?_)
  obtain ⟨v, hv, e1, e2⟩ := evalF_assign_inv h1
  subst e1; subst e2
  simp only [Exp.ev, Option.some.injEq] at hv; subst hv
  have hN : (Exp.prm k).ev κ s (OrderMaintenance.Machine.State.upd L "dn" 0) = some (k.get s.P) := rfl
  refine PKok.loop hN (hG1.pk hC (by safe_tac) hN)
    (fun j S L' => Gd K KH κ (ΓK K) S L' ∧ L' g = p ∧ ((L' "dn" = 0 ∧ I j S) ∨ L' "dn" = 1))
    ⟨hG1, by simp [OrderMaintenance.Machine.State.upd, hg, hg3], Or.inl ⟨by simp [OrderMaintenance.Machine.State.upd], h0⟩⟩
    (fun _ _ _ h => h.1) ?_
  intro j S L' hj ⟨hGS, hLg, hcase⟩
  set L2 := OrderMaintenance.Machine.State.upd L' "jj" j
  have hG2 : Gd K KH κ (ΓK K) S L2 := ⟨hGS.enc, hGS.vb, upd_lt hGS.loc (lt_trans hj (hG.vb.prm k))⟩
  have h2g : L2 g = p := by simp [L2, OrderMaintenance.Machine.State.upd, hLg, hg2]
  rcases hcase with ⟨hdn, hI⟩ | hdn
  · have hc0 : ("dn" =ₑ 0 : Exp).ev κ S L2 = some 1 := by
      simp [Exp.ev, OrderMaintenance.Machine.BinOp.eval, L2, OrderMaintenance.Machine.State.upd,
        hdn]
    obtain ⟨b, t', Lg, ng, eg, hok, hI', hPK⟩ := hstep j S hI hj
    have hargs : evList κ S L2 [.var g] = some [p] := by simp [evList, Exp.ev, h2g]
    have hG0 : Gd K KH κ (ΓK K) S (OrderMaintenance.Machine.State.setLocs (fun _ => 0) [g] [p]) :=
      ⟨hG2.enc, hG2.vb, setLocs_lt (zero_locs _) (fun _ _ => le_refl K)
        (by intro v hv; simp? at hv; subst hv; rw [← h2g]; exact hG2.loc g)⟩
    have hCall : PKok K KH κ (ΓK K) W (q.call [.var g] ["ok"]) S L2 :=
      PKok.call hG2 hargs (hG2.pkList hC (by safe_tac) hargs) (by rw [hq]; exact hPK hG0)
        (by rw [hr]; simpa using hrK) (by simp)
    have ec := evalF_call_ok (q := q) (args := [.var g]) (ds := ["ok"]) (L := L2) hargs (by rw [hq]; exact eg)
    set L3 := OrderMaintenance.Machine.State.setLocs L2 ["ok"] (q.rets.map Lg)
    have h3ok : L3 "ok" = b2n b := by simp [L3, hr, OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd, hok]
    have h3g : L3 g = p := by simp [L3, hr, OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd, h2g, hg1]
    have h3dn : L3 "dn" = 0 := by simp [L3, L2, hr, OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd, hdn]
    obtain ⟨pc, hG3⟩ := hCall _ _ _ ec
    have hc1 : ("ok" =ₑ 0 : Exp).ev κ t' L3 = some (if b2n b = 0 then 1 else 0) := by
      simp [Exp.ev, OrderMaintenance.Machine.BinOp.eval, h3ok]
    intro s' L'' c he
    have hpk : pkF κ (.ite ("dn" =ₑ 0) (q.call [.var g] ["ok"];; .ite ("ok" =ₑ 0) ("dn" ::= 1) .skip) .skip) S L2
        < 2 ^ W := by
      rw [pkF_ite hc0, ite_eq_left one_ne_zero, pkF_seq_ok ec]
      refine max_lt (hG2.pk hC (by safe_tac) hc0) (max_lt pc ?_)
      rw [pkF_ite hc1]
      refine max_lt (hG3.pk hC (by safe_tac) hc1) ?_
      have : (1 : Nat) < 2 ^ W := Nat.one_lt_two_pow (by omega)
      split
      · simpa [pkF, Exp.pk] using this
      · simp [pkF]
    cases b
    · have et : evalF κ (.ite ("ok" =ₑ 0) ("dn" ::= 1) .skip) t' L3 = .ok t' (OrderMaintenance.Machine.State.upd L3 "dn" 1) _ :=
        evalF_ite_t (by simpa [b2n] using hc1) one_ne_zero (evalF_assign_ok (v := 1) rfl)
      have he' := evalF_ite_t (f := .skip) hc0 one_ne_zero (evalF_seq_ok2 ec et)
      rw [he'] at he
      cases he
      refine ⟨hpk, ⟨hG3.enc, hG3.vb, upd_lt hG3.loc (by simp only [ΓK]; exact Nat.one_lt_two_pow (by omega))⟩,
        by simp [OrderMaintenance.Machine.State.upd, h3g,
          hg3], Or.inr (by simp [OrderMaintenance.Machine.State.upd])⟩
    · have et : evalF κ (.ite ("ok" =ₑ 0) ("dn" ::= 1) .skip) t' L3 = .ok t' L3 _ :=
        evalF_ite_f (by simpa [b2n] using hc1) evalF_skip
      have he' := evalF_ite_t (f := .skip) hc0 one_ne_zero (evalF_seq_ok2 ec et)
      rw [he'] at he
      cases he
      exact ⟨hpk, hG3, h3g, Or.inl ⟨h3dn, hI' rfl⟩⟩
  · have hc0 : ("dn" =ₑ 0 : Exp).ev κ S L2 = some 0 := by
      simp [Exp.ev, OrderMaintenance.Machine.BinOp.eval, L2, OrderMaintenance.Machine.State.upd,
        hdn]
    intro s' L'' c he
    rw [evalF_ite_f hc0 evalF_skip] at he
    cases he
    refine ⟨?_, hG2, h2g, Or.inr (by simp [L2, OrderMaintenance.Machine.State.upd, hdn])⟩
    rw [pkF_ite hc0, ite_eq_right (by simp)]
    exact max_lt (hG2.pk hC (by safe_tac) hc0) (by simp [pkF])

end drive

end OrderMaintenance.Impl
