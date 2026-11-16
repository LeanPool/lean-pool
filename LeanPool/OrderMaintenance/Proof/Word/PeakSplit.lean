/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Word.PeakStep


/-!
# Theorem W, option (A), stage A2: the peak of a split start (`splitChunkStartS`)

The locals at width `K`, except the new tags `ty`, `tz` (`tx − f1` plus a room label) at `K + 1`
(`ΓS`).

* `iaPrep_pk`: the labels and tags of the two new chunks (`roomCall_pk`).
* `childS_pk`: the second new child at position `r + 2`, with `r ≤ lcap children` (`findCall_le`).
* `insertAround_pkok`: the two tags written by `guardedSetTag`, bounded by the split's end state
  (`gstCall_pk`); the second call writes the tag only at `z ≠ y` (`gstCall_frame`).
* `split_pkok`: the split start; the new chunks `y ≠ z` from the push semantics.

Nothing here is used by Theorems A and B.
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model
open OrderMaintenance.Machine (Reg BinOp UnOp State)

variable {K KH W : Nat} {κ : Caps}

section split
variable {s : Core} {L : Loc}
variable (hC : CapsW K κ) (hK : 8 ≤ K) (hW : 2 * K + 4 ≤ W)
include hC hK hW

/-- The labels and tags of the two new chunks (`iaPrepS`). -/
theorem iaPrep_pk (hG : Gd K KH κ (ΓS K) s L) : PK K KH κ (ΓS K) W iaPrepS s L := by
  unfold iaPrepS
  refine PK.safe_seq' hC (by omega) (by omega) (by jsafe) hG (fun _ _ _ _ hG1 => ?_)
  refine PK.safe_seq' hC (by omega) (by omega) (by simp only [lookupP, findP]; jsafe) hG1 (fun _ _ _ _ hG2 => ?_)
  refine PK.safe_seq' hC (by omega) (by omega) (by jsafe) hG2 (fun _ _ _ _ hG3 => ?_)
  refine PK.seq_g (roomCall_pk hC hK hW hG3 (by jsafe) (by simp [ΓS])) (fun _ _ _ _ hG4 => ?_)
  refine PK.seq_g (roomCall_pk hC hK hW hG4 (by jsafe) (by simp [ΓS])) (fun _ _ _ _ hG5 => ?_)
  exact PK.of_safe hC (by omega) (by omega) (by jsafe) hG5

/-- The children of the parent: the second new child at position `r + 2` (`childS`). -/
theorem childS_pk (hG : Gd K KH κ (ΓS K) s L) : PK K KH κ (ΓS K) W childS s L := by
  unfold childS
  refine PK.safe_seq' hC (by omega) (by omega) (by simp only [findP]; jsafe) hG (fun s2 L2 n2 h2 hG2 => ?_)
  have hr := (findCall_le hG.enc h2).1
  refine PK.safe_seq' hC (by omega) (by omega) (by simp only [insertIdxP, swapS]; jsafe) hG2
    (fun s3 L3 n3 h3 hG3 => ?_)
  have hr3 : L3 "r" ≤ κ.lcap .children := by rw [evalF_frame_loc (by decide) h3]; exact hr
  have hl2 := hC.lcap2 .children
  have hev : evList κ s3 L3 ["lp", "r" + 2, "z", 0] = some [L3 "lp", L3 "r" + 2, L3 "z", 0] := by
    simp [evList, Exp.ev, OrderMaintenance.Machine.BinOp.eval]
  have hk : ∀ x, x ≠ "ty" → x ≠ "tz" → L3 x < 2 ^ K := fun x h1 h2 => by simpa [ΓS, h1, h2] using hG3.loc x
  refine PK.callV (Γc := ΓK K) (Γe := ΓK K) hG3 hev (hG3.pkList hC (fun e he => ?_) hev) (fun v hv => ?_)
    (fun _ => le_refl K) (fun hG0 => PK.of_safe hC (by omega) (by omega)
      (by simp only [insertIdxP, swapS]; jsafe) hG0) (by simp [insertIdxP]) (by simp)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl <;> jsafe
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact hk _ (by decide) (by decide)
    · omega
    · exact hk _ (by decide) (by decide)
    · exact Nat.two_pow_pos _

/-- The table entries of the parent chunk's tables (`cinsS`). -/
theorem cins_pk (hG : Gd K KH κ (ΓS K) s L) : PK K KH κ (ΓS K) W cinsS s L := by
  unfold cinsS
  refine PK.safe_seq' hC (by omega) (by omega) (by jsafe) hG (fun s1 L1 n1 h1 hG1 => ?_)
  obtain ⟨M, hM, e1, e2⟩ := evalF_assign_inv h1
  subst e1 e2
  have hMK : M < 2 ^ K := hG.valN hC rfl (by jsafe) hM
  have hm : (Exp.var "m").ev κ s (OrderMaintenance.Machine.State.upd L "m" M) = some M := by simp [Exp.ev]
  refine PK.loop hm (hG1.pk hC (by jsafe) hm) (fun _ S L' => Gd K KH κ (ΓS K) S L') hG1 (fun _ _ _ h => h)
    (fun j S L' hj hGS => ?_)
  have hG5 : Gd K KH κ (ΓS K) S (OrderMaintenance.Machine.State.upd L' "j" j) :=
    ⟨hGS.enc, hGS.vb, upd_lt hGS.loc (by simp [ΓS]; omega)⟩
  have hPK : PK K KH κ (ΓS K) W cinsBody S (OrderMaintenance.Machine.State.upd L' "j" j) := by
    unfold cinsBody
    refine PK.safe_seq' hC (by omega) (by omega) (by jsafe) hG5 (fun _ _ _ _ hG6 => ?_)
    refine PK.seq_g (roomCall_pk hC hK hW hG6 (by jsafe) (by simp [ΓS])) (fun _ _ _ _ hG7 => ?_)
    refine PK.seq_g (roomCall_pk hC hK hW hG7 (by jsafe) (by simp [ΓS])) (fun _ _ _ _ hG8 => ?_)
    refine PK.seq_g (tableInsertCall_pk hC hK hW hG8 (by jsafe) (by simp)) (fun _ _ _ _ hG9 => ?_)
    exact tableInsertCall_pk hC hK hW hG9 (by jsafe) (by simp)
  exact ⟨hPK, fun _ _ _ he => hPK.post he⟩

/-- **The insertion of the two new chunks into the tree** (`insertAroundS`, new chunks `y ≠ z`): the
tags written by `guardedSetTag` are bounded by the split's end state. -/
theorem insertAround_pkok (hG : Gd K KH κ (ΓS K) s L) (hyz : L "y" ≠ L "z")
    (hF : Fin (κ := κ) (FB K KH κ (.c .tag)) insertAroundS s L) : PKok K KH κ (ΓS K) W insertAroundS s L := by
  unfold insertAroundS at hF ⊢
  refine PKok.seqF (PK.ok (iaPrep_pk hC hK hW hG)) hF (fun s1 L1 n1 h1 hG1 hF1 => ?_)
  have hy1 : L1 "y" = L "y" := evalF_frame_loc (by decide) h1
  have hz1 : L1 "z" = L "z" := evalF_frame_loc (by decide) h1
  have hk1 : ∀ x, x ≠ "ty" → x ≠ "tz" → L1 x < 2 ^ K := fun x h1 h2 => by simpa [ΓS, h1, h2] using hG1.loc x
  have hty : L1 "ty" < 2 ^ (2 * K + 2) := by
    have := hG1.loc "ty"; simp [ΓS] at this; exact pow_mono_lt this (by omega)
  have htz : L1 "tz" < 2 ^ (2 * K + 2) := by
    have := hG1.loc "tz"; simp [ΓS] at this; exact pow_mono_lt this (by omega)
  have hyK := hk1 "y" (by decide) (by decide)
  have hzK := hk1 "z" (by decide) (by decide)
  have hKW : 2 ^ (2 * K + 2) ≤ 2 ^ W := pow_le_pow' (by omega)
  have hKW' : 2 ^ K ≤ 2 ^ W := pow_le_pow' (by omega)
  -- the tag of `y`: the rest writes the tag only at `z ≠ y`
  refine PKok.seq_fin (Q' := FBat K KH κ (.c .tag) (L1 "y")) hF1 (fun s2 L2 n2 s' L' n h2 h3 hq => ?_)
    (fun hF2 => gstCall_pk hC hK hW hG1 (a := .var "y") (b := .var "ty") (ja := L1 "y") (vb := L1 "ty")
      (by simp [Exp.ev]) (by simp [Exp.ev])
      hyK hty (by simp only [Exp.pk]; omega) (by simp only [Exp.pk]; omega) hF2) (fun s2 L2 n2 h2 hG2 hF2 => ?_)
  · obtain ⟨s3, L3, n3, n4, h4, h5⟩ := evalF_seq_inv h3
    have hb3 := FB.back frame_split.2.2.1 h5 hq
    have hy2 : L2 "y" = L1 "y" := evalF_frame_loc (by decide) h2
    have hz2 : L2 "z" = L1 "z" := evalF_frame_loc (by decide) h2
    intro hj
    rw [← gstCall_frame (a := .var "z") (ja := L2 "z") h4 (by simp [Exp.ev]) (by simpa [Fld.cap] using hj)
      (by rw [hz2, hy1, hz1]; exact hyz)]
    exact hb3 _ hj
  · have hy2 : L2 "y" = L1 "y" := evalF_frame_loc (by decide) h2
    have hz2 : L2 "z" = L1 "z" := evalF_frame_loc (by decide) h2
    have hty2 : L2 "tz" = L1 "tz" := evalF_frame_loc (by decide) h2
    refine PKok.seq_fb (Γ' := ΓS K) hF2 frame_split.2.2.1 (fun hF3 => ?_) (fun s3 L3 n3 h3 hG3 hF3 => ?_)
    · exact gstCall_pk hC hK hW hG2 (a := .var "z") (b := .var "tz") (ja := L2 "z") (vb := L2 "tz")
        (by simp [Exp.ev]) (by simp [Exp.ev])
        (by rw [hz2]; exact hzK) (by rw [hty2]; exact htz) (by simp only [Exp.pk]; rw [hz2]; omega)
        (by simp only [Exp.pk]; rw [hty2]; omega) (hF3.mono (fun t h => h.at' _))
    · refine PK.ok (PK.seq_g (cins_pk hC hK hW hG3) (fun _ _ _ _ hG4 => ?_))
      refine PK.safe_seq' hC (by omega) (by omega) (by jsafe) hG4 (fun _ _ _ _ hG5 => ?_)
      refine PK.safe_seq' hC (by omega) (by omega) (by simp only [joinCS, copyS, copyBody]; jsafe) hG5
        (fun _ _ _ _ hG6 => ?_)
      refine PK.safe_seq' hC (by omega) (by omega) (by jsafe) hG6 (fun _ _ _ _ hG7 => ?_)
      refine PK.safe_seq' hC (by omega) (by omega) (by simp only [joinCS, copyS, copyBody]; jsafe) hG7
        (fun _ _ _ _ hG8 => ?_)
      exact childS_pk hC hK hW hG8

/-- **A split start** (`splitChunkStartS`), its new tags bounded by the end state. -/
theorem split_pkok (hG : Gd K KH κ (ΓS K) s L)
    (hF : Fin (κ := κ) (FB K KH κ (.c .tag)) splitChunkStartS s L) : PKok K KH κ (ΓS K) W splitChunkStartS s L := by
  unfold splitChunkStartS at hF ⊢
  refine PKok.safe_seq_fin hC (by omega) (by omega) (by jsafe) hG hF (fun s1 L1 n1 h1 hG1 hF1 => ?_)
  refine PKok.safe_seq_fin hC (by omega) (by omega) (by jsafe) hG1 hF1 (fun s2 L2 n2 h2 hG2 hF2 => ?_)
  refine PKok.safe_seq_fin hC (by omega) (by omega) (by jsafe) hG2 hF2 (fun s3 L3 n3 h3 hG3 hF3 => ?_)
  obtain ⟨e1, e2⟩ := evalF_push_inv h2
  obtain ⟨e3, e4⟩ := evalF_push_inv h3
  have hyz : L3 "y" ≠ L3 "z" := by
    rw [e4, upd_eq, upd_ne _ _ (by decide), e2, upd_eq, e1]
    simp [Tbl.size, Tbl.push]
  refine PKok.safe_seq_fin hC (by omega) (by omega)
    (by simp only [linkChunkPairS, lcpY, lcpP, lcpZ, lcpN, lcpX]; jsafe) hG3 hF3
    (fun s4 L4 n4 h4 hG4 hF4 => ?_)
  have hy4 : L4 "y" = L3 "y" := evalF_frame_loc (by decide) h4
  have hz4 : L4 "z" = L3 "z" := evalF_frame_loc (by decide) h4
  refine PKok.seq_fb (Γ' := ΓS K) hF4 frame_split.2.2.2 (fun hF5 => insertAround_pkok hC hK hW hG4
    (by rw [hy4,
      hz4]; exact hyz) hF5) (fun s5 L5 n5 h5 hG5 _ => PK.ok (PK.of_safe hC (by omega) (by omega)
      (by simp only [markSplitS, msX, msY, msZ]; jsafe) hG5))

end split

end OrderMaintenance.Impl
