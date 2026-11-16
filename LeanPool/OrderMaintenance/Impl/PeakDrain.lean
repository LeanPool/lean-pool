/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.PeakTop2
public import LeanPool.OrderMaintenance.Impl.StartDrain


/-!
# Theorem W, option (A), stage A2: the tables of the new nodes of a drain start

* `PK.lgrowV`: appending a pair of known values below `2^K` to a top list.
* `tab_pk` (`tabS`): with at most 511 table entries, the even labels `(i + 1)·⌊2^β / (c + 1)⌋`
  are below `512·2^β ≤ 2^K` (`β + 9 ≤ K`, `PRoom.beta9`).

The rest of `startDrainS` (the weights of the new nodes, written from sums of width `K + 9`) is
not done yet (`docs/WORD.md` §7).

Nothing here is used by Theorems A and B.
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model
open OrderMaintenance.Machine (Reg BinOp UnOp State)

variable {K KH W : Nat} {κ : Caps}

section rules
variable {s : Core} {L : Loc} {Γ : Reg → Nat}

/-- `lgrow` with known values below `2^K`. -/
theorem PK.lgrowV {k : LK} {i a b : Exp} {x va vb : Nat} (hC : CapsW K κ) (hW : K ≤ W) (hG : Gd
  K KH κ Γ s L)
    (hx : i.ev κ s L = some x) (ha : a.ev κ s L = some va) (hb : b.ev κ s L = some vb)
    (hpi : i.pk κ s L < 2 ^ W) (hpa : a.pk κ s L < 2 ^ W) (hpb : b.pk κ s L < 2 ^ W)
    (hva : va < 2 ^ K) (hvb : vb < 2 ^ K) : PK K KH κ Γ W (.lgrow k i a b) s L := by
  intro hnb
  simp only [evalF, hx, ha, hb] at hnb
  split at hnb
  · next s1 hs1 =>
    obtain ⟨hxr, hlc⟩ := LK.set_lrec hs1
    rw [List.length_append, List.length_singleton] at hlc
    have hidx := lidx_lt hC hxr (by omega : (k.view s x).length < κ.lcap k)
    have hst := lt_of_le_of_lt (stride_le κ k) (hC.lcap k)
    have hl1 : (k.view s x).length + 1 < 2 ^ K := lt_of_le_of_lt hlc (hC.lcap k)
    refine ⟨?_, fun s' L' n h => ?_⟩
    · simp only [pkF, Exp.val_of hx]
      have hm : x * k.stride κ.lcap ≤ x * k.stride κ.lcap + (k.view s x).length :=
        Nat.le_add_right _ _
      have hKW : 2 ^ K ≤ 2 ^ W := pow_le_pow' hW
      refine max_lt (max_lt (max_lt (max_lt (max_lt (max_lt ?_ ?_) ?_) ?_) ?_) (max_lt ?_ ?_))
        ?_ <;>
        first | assumption | omega
    · have h' : evalF κ (.lgrow k i a b) s L = .ok s' L' n := h
      simp only [evalF, hx, ha, hb, hs1] at h; cases h
      exact ⟨hG.enc.of_ok h', hG.vb.lset hs1 ((hG.vb.lb k hxr).append ⟨hva, hvb⟩), hG.loc⟩
  · exact absurd rfl hnb

end rules

section tab
variable {s : Core} {L : Loc}
variable (hC : CapsW K κ) (hK : 8 ≤ K) (hW : 2 * K + 4 ≤ W)
include hC hK hW

omit hC hK hW in
theorem gdD (hG : Gd K KH κ (ΓD K) s L) (x : Reg) (hx : ¬ (x = "t" ∨ x = "b" ∨ x = "ws")) : L x
  < 2 ^ K :=
  gdD_K hG hx

/-- **The table of a new node** (`tabS`): even labels below `512·2^β ≤ 2^K`. -/
theorem tab_pk (hcapT : κ.lcap .table < 512) (hG : Gd K KH κ (ΓD K) s L) : PK K KH κ (ΓD K) W
  tabS s L := by
  have hR := hG.vb.room
  unfold tabS
  refine PK.safe_seq' hC (by omega) (by omega) (by proveSafe) hG (fun s1 L1 n1 h1 hG1 => ?_)
  obtain ⟨NT, hNT, e1, e2⟩ := evalF_assign_inv h1
  subst e1 e2
  have hNc : NT ≤ κ.lcap .table := by
    simp only [Exp.ev, Option.bind_eq_some_iff] at hNT
    obtain ⟨x, -, hx⟩ := hNT
    split at hx
    · next hxr => cases hx; exact hG.enc.llen _ hxr
    · cases hx
  have hNK : NT < 2 ^ K := lt_of_le_of_lt hNc (hC.lcap _)
  refine PK.safe_assign_seq hC hG1 (by proveSafe) (by proveSafe) (v := 0) rfl (fun hG2 => ?_)
  set L2 := Machine.State.upd (Machine.State.upd L "nt" NT) "cnt" 0
  have hn2 : (Exp.var "nt").ev κ s L2 = some NT := by simp [Exp.ev, L2, Machine.State.upd]
  -- the count
  have hL1 : PK K KH κ (ΓD K) W (.loop "j" "nt" cntBody) s L2 := by
    refine PK.loop hn2 (hG2.pk hC (by proveSafe) hn2)
      (fun j S L' => Gd K KH κ (ΓD K) S L' ∧ L' "cnt" ≤ j ∧ L' "nt" = NT)
      ⟨hG2, by simp [L2, Machine.State.upd], by simp [L2, Machine.State.upd]⟩ (fun _ _ _ h =>
        h.1) ?_
    intro j S L' hj ⟨hGS, hc, hn'⟩
    have hG3 : Gd K KH κ (ΓD K) S (Machine.State.upd L' "j" j) :=
      ⟨hGS.enc, hGS.vb, upd_lt hGS.loc (by
        simp [ΓD]
        omega)⟩
    have hc3 : Machine.State.upd L' "j" j "cnt" ≤ j := by rw [upd_ne _ _ (by decide)]; exact hc
    unfold cntBody
    have hPK : PK K KH κ (ΓD K) W ("e" ::= .lrd .table false "v" "j";; selS;; .ite "q" ("cnt"
      ::= "cnt" + 1) .skip)
        S (Machine.State.upd L' "j" j) := by
      refine PK.safe_seq' hC (by omega) (by omega) (by proveSafe) hG3 (fun S4 L4 n4 h4 hG4 => ?_)
      refine PK.safe_seq' hC (by omega) (by omega) (by
        simp only [selS, selE, findP, lookupP]
        proveSafe) hG4
        (fun S5 L5 n5 h5 hG5 => ?_)
      have h5c : L5 "cnt" ≤ j := by
        rw [evalF_frame_loc (by decide) h5, evalF_frame_loc (by decide) h4]; exact hc3
      refine PK.ite_ok hG5 hC (by proveSafe) (fun _ _ _ => ?_) (fun _ => PK.skip hG5)
      have hv : (("cnt" : Exp) + 1).ev κ S5 L5 = some (L5 "cnt" + 1) := by
        simp [Exp.ev, Machine.BinOp.eval]
      exact PK.assign hG5 hv (hG5.pk hC (by proveSafe) hv) (by
        simp only [ΓD]
        rw [ite_eq_right (by decide)]
        omega)
    refine ⟨hPK, fun s' L'' c he => ⟨hPK.post he, ?_, by
      rw [evalF_frame_loc (by decide) he, upd_ne _ _ (by decide), hn']⟩⟩
    obtain ⟨S4, L4, n4, n5, h4, h5⟩ := evalF_seq_inv he
    obtain ⟨S6, L6, n6, n7, h6, h7⟩ := evalF_seq_inv h5
    have h6c : L6 "cnt" ≤ j := by
      rw [evalF_frame_loc (by decide) h6, evalF_frame_loc (by decide) h4]; exact hc3
    obtain ⟨v, -, m, hm⟩ := evalF_ite_inv h7
    split at hm
    · obtain ⟨u, hu, -, e⟩ := evalF_assign_inv hm
      rw [e, upd_eq]; simp [Exp.ev, Machine.BinOp.eval] at hu; omega
    · simp only [evalF, Res.ok.injEq] at hm; rw [← hm.2.1]; omega
  refine PK.seq_g hL1 (fun s3 L3 n3 h3 hG3 => ?_)
  have h3n : L3 "nt" = NT := by rw [evalF_frame_loc (by decide) h3]; simp [L2, Machine.State.upd]
  -- the step between labels
  have hstv : (Exp.bin .shl 1 (.prm .beta) / ("cnt" + 1)).ev κ s3 L3 = some (1 * 2 ^ s3.P.beta /
    (L3 "cnt" + 1)) := by
    simp [Exp.ev, Machine.BinOp.eval, PF.get]
  have hβ := hG3.vb.room.beta9
  have hsts : (Exp.bin .shl 1 (.prm .beta) / ("cnt" + 1)).ShOK κ s3 L3 K :=
    ⟨⟨trivial, trivial, fun _ => by simp [Exp.val, Exp.ev, PF.get]; omega⟩, Exp.shOK_of_noShl _
      _ _ _ _ rfl,
      fun h => by cases h⟩
  have hstle : 1 * 2 ^ s3.P.beta / (L3 "cnt" + 1) ≤ 2 ^ s3.P.beta := by
    simpa using Nat.div_le_self _ _
  have hβK : 2 ^ s3.P.beta * 512 ≤ 2 ^ K := by
    rw [show (512 : Nat) = 2 ^ 9 from rfl, ← pow_add]; exact pow_le_pow' (by omega)
  refine PK.assign_seq hG3 hstv (hG3.pkS hC hsts hstv (by proveSafe))
    (by simp only [ΓD]; rw [ite_eq_right (by decide)]; have := Nat.one_le_two_pow (n :=
      s3.P.beta); omega)
    (fun hG4 => ?_)
  refine PK.safe_assign_seq hC hG4 (by proveSafe) (by proveSafe) (v := 0) rfl (fun hG5 => ?_)
  set ST := 1 * 2 ^ s3.P.beta / (L3 "cnt" + 1)
  set L5 := Machine.State.upd (Machine.State.upd L3 "st" ST) "idx" 0
  have hn5 : (Exp.var "nt").ev κ s3 L5 = some NT := by simp [Exp.ev, L5, Machine.State.upd, h3n]
  -- the labels
  refine PK.loop hn5 (hG5.pk hC (by proveSafe) hn5)
    (fun j S L' => Gd K KH κ (ΓD K) S L' ∧ L' "idx" ≤ j ∧ L' "nt" = NT ∧ L' "st" = ST ∧ S.P = s3.P)
    ⟨hG5, by simp [L5, Machine.State.upd], by simp [L5, Machine.State.upd, h3n],
      by simp [L5, Machine.State.upd], rfl⟩ (fun _ _ _ h => h.1) ?_
  intro j S L' hj ⟨hGS, hc, hn', hst, hP⟩
  have hG6 : Gd K KH κ (ΓD K) S (Machine.State.upd L' "j" j) :=
    ⟨hGS.enc, hGS.vb, upd_lt hGS.loc (by
      simp [ΓD]
      omega)⟩
  have hc6 : Machine.State.upd L' "j" j "idx" ≤ j := by rw [upd_ne _ _ (by decide)]; exact hc
  have hs6 : Machine.State.upd L' "j" j "st" = ST := by rw [upd_ne _ _ (by decide)]; exact hst
  unfold bldBody
  have hPK : PK K KH κ (ΓD K) W ("e" ::= .lrd .table false "v" "j";; selS;;
      .ite "q" ("idx" ::= "idx" + 1;; .lgrow .table "w" "e" ("idx" * "st")) .skip) S
        (Machine.State.upd L' "j" j) := by
    refine PK.safe_seq' hC (by omega) (by omega) (by proveSafe) hG6 (fun S7 L7 n7 h7 hG7 => ?_)
    refine PK.safe_seq' hC (by omega) (by omega) (by
      simp only [selS, selE, findP, lookupP]
      proveSafe) hG7
      (fun S8 L8 n8 h8 hG8 => ?_)
    have h8c : L8 "idx" ≤ j := by
      rw [evalF_frame_loc (by decide) h8, evalF_frame_loc (by decide) h7]; exact hc6
    have h8s : L8 "st" = ST := by
      rw [evalF_frame_loc (by decide) h8, evalF_frame_loc (by decide) h7]; exact hs6
    refine PK.ite_ok hG8 hC (by proveSafe) (fun _ _ _ => ?_) (fun _ => PK.skip hG8)
    have hv : (("idx" : Exp) + 1).ev κ S8 L8 = some (L8 "idx" + 1) := by
      simp [Exp.ev, Machine.BinOp.eval]
    refine PK.assign_seq hG8 hv (hG8.pk hC (by proveSafe) hv) (by
      simp only [ΓD]
      rw [ite_eq_right (by decide)]
      omega)
      (fun hG9 => ?_)
    set L9 := Machine.State.upd L8 "idx" (L8 "idx" + 1)
    have hlab : L9 "idx" * L9 "st" < 2 ^ K := by
      have e1 : L9 "idx" = L8 "idx" + 1 := upd_eq _ _ _
      have e2 : L9 "st" = ST := by
        change Machine.State.upd L8 "idx" (L8 "idx" + 1) "st" = ST
        rw [upd_ne _ _ (by decide)]; exact h8s
      rw [e1, e2]
      have : (L8 "idx" + 1) * ST ≤ 511 * 2 ^ s3.P.beta :=
        Nat.mul_le_mul (by omega) hstle
      have := Nat.one_le_two_pow (n := s3.P.beta)
      omega
    exact PK.lgrowV hC (by omega) hG9 (show (Exp.var "w").ev κ S8 L9 = some (L9 "w") from rfl)
      (show (Exp.var "e").ev κ S8 L9 = some (L9 "e") from rfl)
      (show (("idx" : Exp) * "st").ev κ S8 L9 = some (L9 "idx" * L9 "st") by simp [Exp.ev,
        Machine.BinOp.eval])
      (hG9.pk hC (by proveSafe) rfl) (hG9.pk hC (by proveSafe) rfl)
      (hG9.pk hC (by proveSafe) (show (("idx" : Exp) * "st").ev κ S8 L9 = some (L9 "idx" * L9
        "st") by
        simp [Exp.ev, Machine.BinOp.eval]))
      (gdD hG9 "e" (by decide)) hlab
  refine ⟨hPK, fun s' L'' c he => ⟨hPK.post he, ?_, by rw [evalF_frame_loc (by decide) he,
    upd_ne _ _ (by decide), hn'],
    by rw [evalF_frame_loc (by decide) he, hs6], by rw [evalF_P he, hP]⟩⟩
  obtain ⟨S7, L7, n7, n8, h7, h8⟩ := evalF_seq_inv he
  obtain ⟨S8, L8, n9, n10, h9, h10⟩ := evalF_seq_inv h8
  have h8c : L8 "idx" ≤ j := by
    rw [evalF_frame_loc (by decide) h9, evalF_frame_loc (by decide) h7]; exact hc6
  obtain ⟨v, -, m, hm⟩ := evalF_ite_inv h10
  split at hm
  · obtain ⟨S11, L11, n11, n12, h11, h12⟩ := evalF_seq_inv hm
    obtain ⟨u, hu, -, e⟩ := evalF_assign_inv h11
    rw [evalF_frame_loc (by decide) h12, e,
      upd_eq]; simp [Exp.ev, Machine.BinOp.eval] at hu; omega
  · simp only [evalF, Res.ok.injEq] at hm; rw [← hm.2.1]; omega

end tab

end OrderMaintenance.Impl
