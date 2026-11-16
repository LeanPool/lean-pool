/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.PeakInit
public import LeanPool.OrderMaintenance.Impl.Finish
public import LeanPool.OrderMaintenance.Impl.Cut
public import LeanPool.OrderMaintenance.Impl.Side


/-!
# Theorem W, option (A), stage A2: the cut of a drain, its side list, and its end

* `drainCut_pk`: the weight sum `t` of at most 511 children (width `K + 9`), the cut count `c`
  (at most the loop index) and the shift `k` (below the children count by its guard).
* `drainSide_pk`, `finishDrain_pk`: safe, but for the filters of `finishDrain` (`filter_pk`).

Nothing here is used by Theorems A and B.
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model
open OrderMaintenance.Machine (Reg BinOp UnOp State)

variable {K KH W : Nat} {κ : Caps}

theorem ΓK_le_ΓD (K : Nat) : ∀ x, ΓK K x ≤ ΓD K x := by intro x; simp only [ΓD, ΓK]; split <;> omega

section cut
variable {s : Core} {L : Loc}
variable (hC : CapsW K κ) (hK : 8 ≤ K) (hW : 2 * K + 4 ≤ W)
include hC hK hW

theorem gdD_K (hG : Gd K KH κ (ΓD K) s L) {x : Reg} (hx : ¬ (x = "t" ∨ x = "b" ∨ x = "ws")) : L x < 2 ^ K := by
  have := hG.loc x; simp only [ΓD] at this; rwa [ite_eq_right hx] at this

/-- `wtS`: the weight of a child (1 at height 1). -/
theorem wt_val {S : Core} {L' : Loc} (hG : Gd K KH κ (ΓD K) S L') {S2 : Core} {L2 : Loc} {n : Nat}
    (h : evalF κ wtS S L' = .ok S2 L2 n) : L2 "w" < 2 ^ K := by
  have := (PK.of_safe (W := W) hC (by omega) (by omega) (by simp only [wtS]; safe_tac) hG).post h
  exact gdD_K hC hK hW this (by decide)

/-- The sum of the children's weights: `t ≤ j·(2^K − 1)` before iteration `j`. -/
theorem sum_pk (hcap : κ.lcap .children < 512) {N : Nat} (hNc : N ≤ κ.lcap .children)
    (hG : Gd K KH κ (ΓD K) s L) (hn : L "n" = N) : PK K KH κ (ΓD K) W sumS s L := by
  have hKe : (2 : Nat) ^ (K + 9) = 512 * 2 ^ K := by rw [pow_add]; norm_num; ring
  have hKp : 1 ≤ 2 ^ K := Nat.one_le_two_pow
  unfold sumS
  refine PK.safe_assign_seq hC hG (by safe_tac) (by safe_tac) (v := 0) rfl (fun hG2 => ?_)
  have hn2 : (Exp.var "n").ev κ s (OrderMaintenance.Machine.State.upd L "t" 0) = some N := by
    simp [Exp.ev, OrderMaintenance.Machine.State.upd, hn]
  refine PK.loop hn2 (hG2.pk hC (by safe_tac) hn2)
    (fun j S L' => Gd K KH κ (ΓD K) S L' ∧ L' "t" ≤ j * (2 ^ K - 1))
    ⟨hG2, by simp [OrderMaintenance.Machine.State.upd]⟩ (fun _ _ _ h => h.1) ?_
  intro j S L' hj ⟨hGS, ht⟩
  have hNK : N < 2 ^ K := lt_of_le_of_lt hNc (hC.lcap _)
  have hG3 : Gd K KH κ (ΓD K) S (OrderMaintenance.Machine.State.upd L' "j" j) :=
    ⟨hGS.enc, hGS.vb, upd_lt hGS.loc (by simp [ΓD]; omega)⟩
  have ht3 : OrderMaintenance.Machine.State.upd L' "j" j "t" ≤ j * (2 ^ K - 1) := by rw [upd_ne _ _ (by decide)]; exact ht
  unfold sumBody
  -- the new sum, from the run of the first two statements
  have hval : ∀ S4 L4 n4, evalF κ ("e" ::= .lrd .children false "v" "j";; wtS) S (OrderMaintenance.Machine.State.upd L' "j" j) =
      .ok S4 L4 n4 → L4 "t" + L4 "w" ≤ (j + 1) * (2 ^ K - 1) := by
    intro S4 L4 n4 h4
    have hG4 := (PK.of_safe (W := W) hC (by omega) (by omega) (by simp only [wtS]; safe_tac) hG3).post h4
    have hw := gdD_K hC hK hW hG4 (x := "w") (by decide)
    rw [evalF_frame_loc (by decide) h4]
    rw [Nat.succ_mul]; omega
  have hPK : PK K KH κ (ΓD K) W ("e" ::= .lrd .children false "v" "j";; wtS;; "t" ::= "t" + "w") S
      (OrderMaintenance.Machine.State.upd L' "j" j) := by
    refine PK.safe_seq' hC (by omega) (by omega) (by safe_tac) hG3 (fun S3 L3 n3 h3 hG3' => ?_)
    refine PK.seq_g (PK.of_safe hC (by omega) (by omega) (by simp only [wtS]; safe_tac) hG3')
      (fun S4 L4 n4 h4 hG4 => ?_)
    have hle := hval S4 L4 (n3 + n4) (by rw [evalF_seq_ok h3, h4]; rfl)
    have hv : (("t" : Exp) + "w").ev κ S4 L4 = some (L4 "t" + L4 "w") := by simp [Exp.ev, OrderMaintenance.Machine.BinOp.eval]
    refine PK.assign hG4 hv (hG4.pk hC (by safe_tac) hv) ?_
    simp only [ΓD]; rw [ite_eq_left (by decide)]
    have : (j + 1) * (2 ^ K - 1) < 2 ^ (K + 9) := by
      rw [hKe]
      have : (j + 1) * (2 ^ K - 1) ≤ 511 * (2 ^ K - 1) := Nat.mul_le_mul_right _ (by omega)
      omega
    omega
  refine ⟨hPK, fun s' L'' c he => ⟨hPK.post he, ?_⟩⟩
  obtain ⟨S3, L3, n3, n4, h3, h4⟩ := evalF_seq_inv he
  obtain ⟨S4, L4, n5, n6, h5, h6⟩ := evalF_seq_inv h4
  obtain ⟨v, hv, -, e2⟩ := evalF_assign_inv h6
  subst e2
  have hle := hval S4 L4 (n3 + n5) (by rw [evalF_seq_ok h3, h5]; rfl)
  simp [Exp.ev, OrderMaintenance.Machine.BinOp.eval] at hv
  rw [upd_eq, ← hv]; exact hle

/-- The cut: the count `c` stays at most the loop index. -/
theorem cut_pk {N : Nat} (hNK : N < 2 ^ K) (hG : Gd K KH κ (ΓD K) s L) (hn : L "n" = N) :
    PK K KH κ (ΓD K) W cutS s L := by
  unfold cutS
  refine PK.safe_seq' hC (by omega) (by omega) (by safe_tac) hG (fun s1 L1 n1 h1 hG1 => ?_)
  refine PK.safe_seq' hC (by omega) (by omega) (by safe_tac) hG1 (fun s2 L2 n2 h2 hG2 => ?_)
  refine PK.safe_seq' hC (by omega) (by omega) (by safe_tac) hG2 (fun s3 L3 n3 h3 hG3 => ?_)
  have h3n : L3 "n" = N := by
    rw [evalF_frame_loc (by decide) h3, evalF_frame_loc (by decide) h2,
      evalF_frame_loc (by decide) h1, hn]
  have h3c : L3 "c" = 0 := by
    rw [evalF_frame_loc (by decide) h3]
    obtain ⟨v, hv, -, e⟩ := evalF_assign_inv h2
    simp only [Exp.ev, Option.some.injEq] at hv; rw [e, upd_eq, ← hv]
  have hm : (Exp.monus "n" 1).ev κ s3 L3 = some (N - 1) := Exp.ev_monus κ s3 L3 (by simp [Exp.ev, h3n]) rfl
  refine PK.loop hm (hG3.pk hC (by safe_tac) hm)
    (fun j S L' => Gd K KH κ (ΓD K) S L' ∧ L' "c" ≤ j ∧ L' "n" = N) ⟨hG3, by omega, h3n⟩ (fun _ _ _ h => h.1) ?_
  intro j S L' hj ⟨hGS, hc, hn'⟩
  have hG4 : Gd K KH κ (ΓD K) S (OrderMaintenance.Machine.State.upd L' "j" j) :=
    ⟨hGS.enc, hGS.vb, upd_lt hGS.loc (by simp [ΓD]; omega)⟩
  have hc4 : OrderMaintenance.Machine.State.upd L' "j" j "c" ≤ j := by rw [upd_ne _ _ (by decide)]; exact hc
  unfold cutBody
  have hPK : PK K KH κ (ΓD K) W ("e" ::= .lrd .children false "v" "j";; wtS;;
      .ite (("d" =ₑ 0) &&ₑ ("w" ≤ₑ "b")) ("c" ::= "c" + 1;; "b" ::= "b" - "w") ("d" ::= 1)) S
      (OrderMaintenance.Machine.State.upd L' "j" j) := by
    refine PK.safe_seq' hC (by omega) (by omega) (by safe_tac) hG4 (fun S5 L5 n5 h5 hG5 => ?_)
    refine PK.seq_g (PK.of_safe hC (by omega) (by omega) (by simp only [wtS]; safe_tac) hG5)
      (fun S6 L6 n6 h6 hG6 => ?_)
    have h6c : L6 "c" ≤ j := by
      rw [evalF_frame_loc (by decide) h6, evalF_frame_loc (by decide) h5]; exact hc4
    refine PK.ite_ok hG6 hC (by safe_tac) (fun _ _ _ => ?_) (fun _ => PK.of_safe hC (by omega) (by omega)
      (by safe_tac) hG6)
    have hv : (("c" : Exp) + 1).ev κ S6 L6 = some (L6 "c" + 1) := by simp [Exp.ev, OrderMaintenance.Machine.BinOp.eval]
    exact PK.assign_seq hG6 hv (hG6.pk hC (by safe_tac) hv) (by simp only [ΓD]; rw [ite_eq_right (by decide)]; omega)
      (fun hG7 => PK.of_safe hC (by omega) (by omega) (by safe_tac) hG7)
  refine ⟨hPK, fun s' L'' c he => ⟨hPK.post he, ?_, by rw [evalF_frame_loc (by decide) he, upd_ne _ _ (by decide),
    hn']⟩⟩
  obtain ⟨S5, L5, n5, n6, h5, h6⟩ := evalF_seq_inv he
  obtain ⟨S6, L6, n7, n8, h7, h8⟩ := evalF_seq_inv h6
  have h6c : L6 "c" ≤ j := by
    rw [evalF_frame_loc (by decide) h7, evalF_frame_loc (by decide) h5]; exact hc4
  obtain ⟨v, -, m, hm⟩ := evalF_ite_inv h8
  split at hm
  · obtain ⟨S9, L9, n9, n10, h9, h10⟩ := evalF_seq_inv hm
    obtain ⟨u, hu, -, e⟩ := evalF_assign_inv h9
    rw [evalF_frame_loc (by decide) h10, e, upd_eq]
    simp [Exp.ev, OrderMaintenance.Machine.BinOp.eval] at hu; omega
  · rw [evalF_frame_loc (by decide) hm]; omega

/-- The shift to the right: `k + 1` only when `k < n`. -/
theorem shR_pk {N : Nat} (hNK : N < 2 ^ K) (hG : Gd K KH κ (ΓD K) s L) (hn : L "n" = N) :
    PK K KH κ (ΓD K) W shRS s L := by
  unfold shRS
  refine PK.safe_seq' hC (by omega) (by omega) (by safe_tac) hG (fun s1 L1 n1 h1 hG1 => ?_)
  have h1n : L1 "n" = N := by rw [evalF_frame_loc (by decide) h1, hn]
  have hm : (Exp.var "n").ev κ s1 L1 = some N := by simp [Exp.ev, h1n]
  refine PK.loop hm (hG1.pk hC (by safe_tac) hm)
    (fun j S L' => Gd K KH κ (ΓD K) S L' ∧ L' "n" = N) ⟨hG1, h1n⟩ (fun _ _ _ h => h.1) ?_
  intro j S L' hj ⟨hGS, hn'⟩
  have hG4 : Gd K KH κ (ΓD K) S (OrderMaintenance.Machine.State.upd L' "j" j) :=
    ⟨hGS.enc, hGS.vb, upd_lt hGS.loc (by simp [ΓD]; omega)⟩
  have hn4 : OrderMaintenance.Machine.State.upd L' "j" j "n" = N := by rw [upd_ne _ _ (by decide)]; exact hn'
  unfold shRBody
  have hPK : PK K KH κ (ΓD K) W (.ite shRC (prS;; .ite prE ("k" ::= "k" + 1) ("d" ::= 1)) ("d" ::= 1)) S
      (OrderMaintenance.Machine.State.upd L' "j" j) := by
    refine PK.ite_ok hG4 hC (by simp only [shRC]; safe_tac) (fun c hc hc0 => ?_) (fun _ => PK.of_safe hC (by omega)
      (by omega) (by safe_tac) hG4)
    have hk : OrderMaintenance.Machine.State.upd L' "j" j "k" < N := by
      simp [shRC, Exp.ev, OrderMaintenance.Machine.BinOp.eval,
        OrderMaintenance.Machine.State.upd] at hc
      rw [upd_ne _ _ (by decide), ← hn']
      by_contra hh
      simp [hh] at hc; exact hc0 hc.symm
    refine PK.safe_seq' hC (by omega) (by omega) (by simp only [prS]; safe_tac) hG4 (fun S5 L5 n5 h5 hG5 => ?_)
    have h5k : L5 "k" < N := by rw [evalF_frame_loc (by decide) h5]; exact hk
    refine PK.ite_ok hG5 hC (by simp only [prE]; safe_tac) (fun _ _ _ => ?_) (fun _ => PK.of_safe hC (by omega)
      (by omega) (by safe_tac) hG5)
    have hv : (("k" : Exp) + 1).ev κ S5 L5 = some (L5 "k" + 1) := by simp [Exp.ev, OrderMaintenance.Machine.BinOp.eval]
    exact PK.assign hG5 hv (hG5.pk hC (by safe_tac) hv) (by simp only [ΓD]; rw [ite_eq_right (by decide)]; omega)
  exact ⟨hPK, fun s' L'' c he => ⟨hPK.post he, by rw [evalF_frame_loc (by decide) he, hn4]⟩⟩

/-- **The cut of a drain** (`drainCut`), with at most 511 children. -/
theorem drainCut_pk (hcap : κ.lcap .children < 512) (hG : Gd K KH κ (ΓD K) s L) :
    PK K KH κ (ΓD K) W drainCutS s L := by
  unfold drainCutS
  refine PK.safe_seq' hC (by omega) (by omega) (by safe_tac) hG (fun s1 L1 n1 h1 hG1 => ?_)
  obtain ⟨N, hN, e1, e2⟩ := evalF_assign_inv h1
  subst e1 e2
  have hNc : N ≤ κ.lcap .children := by
    simp only [Exp.ev, Option.bind_eq_some_iff] at hN
    obtain ⟨x, -, hx⟩ := hN
    split at hx
    · next hxr => cases hx; exact hG.enc.llen _ hxr
    · cases hx
  have hNK : N < 2 ^ K := lt_of_le_of_lt hNc (hC.lcap _)
  refine PK.seq_g (sum_pk hC hK hW hcap hNc hG1 (upd_eq _ _ _)) (fun s2 L2 n2 h2 hG2 => ?_)
  have h2n : L2 "n" = N := by rw [evalF_frame_loc (by decide) h2, upd_eq]
  refine PK.seq_g (cut_pk hC hK hW hNK hG2 h2n) (fun s3 L3 n3 h3 hG3 => ?_)
  have h3n : L3 "n" = N := by rw [evalF_frame_loc (by decide) h3, h2n]
  refine PK.safe_seq' hC (by omega) (by omega) (by safe_tac) hG3 (fun s4 L4 n4 h4 hG4 => ?_)
  have h4n : L4 "n" = N := by rw [evalF_frame_loc (by decide) h4, h3n]
  refine PK.ite_ok hG4 hC (by safe_tac) (fun _ _ _ => ?_) (fun _ => PK.skip hG4)
  refine PK.seq_g (shR_pk hC hK hW hNK hG4 h4n) (fun s5 L5 n5 h5 hG5 => ?_)
  exact PK.ite_ok hG5 hC (by safe_tac) (fun _ _ _ => PK.of_safe hC (by omega) (by omega)
    (by simp only [shLS, shLBody, shLC, prS, prE]; safe_tac) hG5) (fun _ => PK.skip hG5)

theorem drainSide_pk (hG : Gd K KH κ (ΓD K) s L) : PK K KH κ (ΓD K) W drainSideS s L := by
  have hS : drainSideS.Safe K KH (ΓD K) W := by
    simp only [drainSideS, sideBody, fixBody, fixC, assocSetP, findP, lookupP]; safe_tac
  exact PK.of_safe hC (by omega) (by omega) hS hG

theorem filterCall_pk {Γ : Reg → Nat} {k : LK} {args : List Exp} {ds : List Reg} (hG : Gd K KH κ Γ s L)
    (ha : ∀ e ∈ args, e.OK Γ K KH W ∧ e.vw Γ K KH K ≤ K) (hd : ∀ d ∈ ds, K ≤ Γ d) :
    PK K KH κ Γ W ((filterP k).call args ds) s L :=
  PK.callS (Γc := ΓK K) (Γe := ΓK K) hC hG ha (fun _ => le_refl K) (fun vs _ hG0 => filter_pk hC hK hW k hG0)
    (by simp [filterP]) hd

/-- **The end of a drain** (`finishDrain`). -/
theorem finishDrain_pk (hG : Gd K KH κ (ΓK K) s L) : PK K KH κ (ΓK K) W finishDrainS s L := by
  unfold finishDrainS
  peel
  have hS : dtLoopS.Safe K KH (ΓK K) W := by
    simp only [dtLoopS, dtBody, dropS, findP, eraseIdxP, mvS]; safe_tac
  refine PK.seq_g (PK.of_safe hC (by omega) (by omega) hS ‹_›) (fun s2 L2 n2 h2 hG2 => ?_)
  refine PK.seq_g (Γ' := ΓK K) ?_ (fun s3 L3 n3 h3 hG3 => PK.of_safe hC (by omega) (by omega)
    (by simp only [relS]; safe_tac) hG3)
  unfold deLoopS
  refine PK.safe_seq' hC (by omega) (by omega) (by safe_tac) hG2 (fun s4 L4 n4 h4 hG4 => ?_)
  obtain ⟨M, hM, e1, e2⟩ := evalF_assign_inv h4
  subst e1 e2
  have hMK : M < 2 ^ K := hG2.valN hC rfl (by safe_tac) hM
  have hm : (Exp.var "m").ev κ s2 (OrderMaintenance.Machine.State.upd L2 "m" M) = some M := by simp [Exp.ev]
  refine PK.loop hm (hG4.pk hC (by safe_tac) hm) (fun _ S L' => Gd K KH κ (ΓK K) S L') hG4 (fun _ _ _ h => h)
    (fun j S L' hj hGS => ?_)
  have hG5 : Gd K KH κ (ΓK K) S (OrderMaintenance.Machine.State.upd L' "j" j) :=
    ⟨hGS.enc, hGS.vb, upd_lt hGS.loc (by simp only [ΓK]; omega)⟩
  have hPK : PK K KH κ (ΓK K) W deBody S (OrderMaintenance.Machine.State.upd L' "j" j) := by
    unfold deBody
    peel
    refine PK.safe_seq' hC (by omega) (by omega) (by simp only [findP]; safe_tac) ‹_› (fun _ _ _ _ hG6 => ?_)
    peel; peel
    exact PK.seq_g (filterCall_pk hC hK hW ‹_› (by safe_tac) (by simp))
      (fun _ _ _ _ hG7 => filterCall_pk hC hK hW hG7 (by safe_tac) (by simp))
  exact ⟨hPK, fun _ _ _ he => hPK.post he⟩

end cut

end OrderMaintenance.Impl
