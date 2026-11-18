/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.PeakCore2
public import LeanPool.OrderMaintenance.Impl.Reservation


/-!
# Theorem W, option (A), stage A2: the peak of the table procedures

* `roomP_pk`: the free label between two neighbours, below the upper one (a label, or `2^β`
  with `β < K`).
* `tableInsert_pk`: the insertion position `r + (1 − bf)`, at most the table's length.

Nothing here is used by Theorems A and B.
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model
open OrderMaintenance.Machine (Reg BinOp UnOp State)

variable {K KH W : Nat} {κ : Caps}

/-- The guard `if c then skip else fail` passed. -/
theorem guard_ok' {c : Exp} {s s' : Core} {L L' : Loc} {n : Nat} (h : evalF κ (.ite c .skip
  .fail) s L = .ok s' L' n) :
    ∃ v, c.ev κ s L = some v ∧ v ≠ 0 ∧ s = s' ∧ L = L' := by
  obtain ⟨v, hv, m, hm⟩ := evalF_ite_inv h
  split at hm
  · next h0 => simp only [evalF, Res.ok.injEq] at hm; exact ⟨v, hv, h0, hm.1, hm.2.1⟩
  · simp [evalF] at hm

section tab
variable {s : Core} {L : Loc}
variable (hC : CapsW K κ) (hK : 8 ≤ K) (hW : 2 * K + 4 ≤ W)
include hC hK hW

theorem boundsS_pk (hG : Gd K KH κ (ΓR K) s L) : PK K KH κ (ΓR K) W boundsS s L := by
  unfold boundsS
  refine PK.ite_ok hG hC (by proveSafe) (fun _ _ _ => PK.of_safe hC (by omega) (by omega) (by
    proveSafe) hG)
    (fun _ => ?_)
  refine PK.safe_seq' hC (by omega) (by omega) (by proveSafe) hG (fun s1 L1 n1 h1 hG1 => ?_)
  refine PK.ite_ok hG1 hC (by proveSafe) (fun _ _ _ => PK.of_safe hC (by omega) (by omega) (by
    proveSafe) hG1)
    (fun _ => ?_)
  have hb := hG1.vb.room.beta9
  have hv : (Exp.bin .shl 1 (.prm .beta)).ev κ s1 L1 = some (1 * 2 ^ s1.P.beta) := by
    simp [Exp.ev, Machine.BinOp.eval, PF.get]
  have hs : (Exp.bin .shl 1 (.prm .beta)).ShOK κ s1 L1 K :=
    ⟨trivial, trivial, fun _ => by simp [Exp.val, Exp.ev, PF.get]; omega⟩
  exact PK.assign hG1 hv (hG1.pkS hC hs hv (by proveSafe))
    (by
      simp only [ΓR, one_mul, String.reduceEq, ↓reduceIte]
      exact Nat.pow_lt_pow_right (by norm_num) (by omega))

/-- **`roomNextTo`**: the label lies below the upper neighbour. -/
theorem roomP_pk (hG : Gd K KH κ (ΓR K) s L) : PK K KH κ (ΓR K) W roomP.body s L := by
  simp only [roomP]
  refine PK.safe_seq' hC (by omega) (by omega) (by
    simp only [findP]
    proveSafe) hG (fun s1 L1 n1 h1 hG1 => ?_)
  peelSafe
  refine PK.seq_g (Γ' := ΓR K) (PK.of_safe hC (by omega) (by omega) (by proveSafe) ‹_›) (fun s3
    L3 n3 h3 hG3 => ?_)
  refine PK.seq_g (boundsS_pk hC hK hW hG3) (fun s4 L4 n4 h4 hG4 => ?_)
  refine PK.seq_g (Γ' := ΓR K) (PK.of_safe hC (by omega) (by omega) (by proveSafe) hG4) (fun s5
    L5 n5 h5 hG5 => ?_)
  obtain ⟨hc0, e1, e2⟩ := guard_ok h5
  subst e1 e2
  have hlo : L4 "lo" < L4 "hi" := by
    simp [Exp.ev, Machine.BinOp.eval] at hc0; omega
  have hhi : L4 "hi" < 2 ^ K := by simpa [ΓR] using hG4.loc "hi"
  have hv : ((("lo" : Exp) + "hi" - 1) / 2).ev κ s4 L4 = some ((L4 "lo" + L4 "hi" - 1) / 2) := by
    simp only [Exp.add_def, Exp.ofNat_def, Exp.sub_def, Exp.div_def, Exp.ev,
      Machine.BinOp.eval, Option.bind_some]
    rw [ite_eq_left (by omega)]
    rfl
  refine PK.assign hG4 hv (hG4.pk hC (by proveSafe) hv) ?_
  change _ < 2 ^ (if ("l" : Reg) = "lo" then K + 1 else K)
  rw [ite_eq_right (by decide)]
  omega

theorem roomCall_pk {Γ : Reg → Nat} {args : List Exp} {ds : List Reg} (hG : Gd K KH κ Γ s L)
    (ha : ∀ e ∈ args, e.OK Γ K KH W ∧ e.vw Γ K KH K ≤ K) (hd : ∀ d ∈ ds, K ≤ Γ d) :
    PK K KH κ Γ W (roomP.call args ds) s L :=
  PK.callS (Γc := ΓR K) (Γe := ΓR K) hC hG ha (fun x => by simp only [ΓR]; split <;> omega)
    (fun vs _ hG0 => roomP_pk hC hK hW hG0) (by simp [roomP, ΓR]) hd

/-- **`tableInsert`**: the position `r + (1 − bf)` is at most the length. -/
theorem tableInsert_pk (hG : Gd K KH κ (ΓK K) s L) : PK K KH κ (ΓK K) W tableInsertP.body s L := by
  simp only [tableInsertP]
  refine PK.safe_seq' hC (by omega) (by omega) (by
    simp only [findP]
    proveSafe) hG (fun s1 L1 n1 h1 hG1 => ?_)
  refine PK.safe_seq' hC (by omega) (by omega) (by proveSafe) hG1 (fun s2 L2 n2 h2 hG2 => ?_)
  obtain ⟨N, hN, e1, e2⟩ := evalF_assign_inv h2
  subst e1 e2
  refine PK.seq_g (Γ' := ΓK K) (PK.of_safe hC (by omega) (by omega) (by proveSafe) hG2) (fun s3
    L3 n3 h3 hG3 => ?_)
  obtain ⟨v, hc, hv0, e1, e2⟩ := guard_ok' h3
  subst e1 e2
  have hNK : N < 2 ^ K := hG1.valN hC rfl (by proveSafe) hN
  have hrn : L1 "r" < N := by
    simp [Exp.ev, Machine.BinOp.eval, ] at hc
    by_contra hh; simp [hh] at hc; exact hv0 hc.symm
  intro hnb
  cases hp : (("r" : Exp) + (1 - "bf")).ev κ s1 (Machine.State.upd L1 "n" N) with
  | none => simp only [Exp.add_def, Exp.sub_def, Exp.ofNat_def] at hp; simp [evalF, hp,
    Res.bind] at hnb
  | some p =>
    have hpv : p < 2 ^ K := by
      obtain ⟨a, b, ha, hb, rfl⟩ := Exp.ev_add_inv (by simpa [Exp.add_def] using hp)
      simp only [Exp.ev, upd_ne _ _ (show ("r" : Reg) ≠ "n" by decide), Option.some.injEq] at ha
      subst ha
      simp only [  Exp.ev, Option.bind_eq_some_iff,
        Machine.BinOp.eval] at hb
      obtain ⟨one, hone, y, -, hb⟩ := hb
      simp only [Option.some.injEq] at hone; subst hone
      split at hb
      · simp only [Option.some.injEq] at hb; omega
      · cases hb
    refine PK.assign_seq hG3 hp (hG3.pk hC (by proveSafe) hp) (by simpa using hpv) (fun hG4 =>
      ?_) hnb
    refine PK.seq_g (Γ' := ΓK K) (PK.callS (Γe := ΓK K) hC hG4 (by proveSafe) (fun _ => le_refl K)
      (fun vs _ hG0 => PK.of_safe hC (by omega) (by omega) (by
        simp only [insertIdxP, swapS]
        proveSafe) hG0)
      (by simp [insertIdxP]) (by simp)) (fun s5 L5 n5 h5 hG5 => ?_)
    exact PK.of_safe hC (by omega) (by omega) (by
      simp only [lookupP, findP, assocSetP]
      proveSafe) hG5

theorem tableInsertCall_pk {Γ : Reg → Nat} {args : List Exp} {ds : List Reg} (hG : Gd K KH κ Γ s L)
    (ha : ∀ e ∈ args, e.OK Γ K KH W ∧ e.vw Γ K KH K ≤ K) (hd : ∀ d ∈ ds, K ≤ Γ d) :
    PK K KH κ Γ W (tableInsertP.call args ds) s L :=
  PK.callS (Γc := ΓK K) (Γe := ΓK K) hC hG ha (fun _ => le_refl K)
    (fun vs _ hG0 => tableInsert_pk hC hK hW hG0) (by simp [tableInsertP]) hd

end tab

end OrderMaintenance.Impl
