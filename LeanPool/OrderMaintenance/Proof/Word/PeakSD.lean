/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Word.PeakJob


/-!
# Theorem W, option (A), stage A2: the peak of a drain start (`startDrain`)

All locals at width `K`, except the weight sums `t`, `b`, `ws` at `K + 9` (`ΓD`).

* `chS_pkok`: the weight of a new node, the sum `ws` of at most 511 child weights, written once:
  its value is the end state's (`Fin`, the weight bound of the job step's end state).
* `stage56_pkok`: the two new nodes `v1 ≠ v2` (`newNodes_ne`, from the push semantics); the second
  `chS` writes the weight only at `v2`, so the first write is the last one at `v1`.
* `stage7_pk`: the insertion position `r + 1`, with `r ≤ lcap children` (`findCall_le`).
* `startDrain_pkok`: the drain start, from `drainCut_pk`, `drainSide_pk`, `roomCall_pk`,
  `tableInsertCall_pk`, `tab_pk` and the above.

Nothing here is used by Theorems A and B.
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model
open OrderMaintenance.Machine (Reg BinOp UnOp State)

variable {K KH W : Nat} {κ : Caps}

/-! ### Runs -/

section runs
variable {s s' : Core} {L L' : Loc} {n : Nat}

theorem evalF_push_inv {t : Tbl} {x : Reg} (h : evalF κ (.push t x) s L = .ok s' L' n) :
    s' = t.push s ∧ L' = State.upd L x (t.size s) := by
  simp only [evalF] at h
  split at h
  · simp only [Res.ok.injEq] at h; exact ⟨h.1.symm, h.2.1.symm⟩
  · cases h

theorem Fld.set_nodes {f : Fld} {i v : Nat} (h : f.set κ s i v = some s') : s'.nodes.size =
  s.nodes.size := by
  cases f with
  | n k =>
    simp only [Fld.set] at h
    split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
    subst h
    simp
  | a k =>
    simp only [Fld.set] at h
    split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
    subst h
    cases k <;> rfl
  | s k =>
    simp only [Fld.set] at h
    split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
    subst h
    cases k <;> rfl
  | e k =>
    simp only [Fld.set] at h
    split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
    subst h
    rfl
  | g k =>
    simp only [Fld.set] at h
    split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
    subst h
    rfl
  | c k =>
    simp only [Fld.set] at h
    split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
    subst h
    rfl

theorem Tbl.push_nodes_N : (Tbl.push s .N).nodes.size = s.nodes.size + 1 := by simp [Tbl.push]

/-- **The two new nodes of a drain start differ.** -/
theorem newNodes_ne (h : evalF κ newNodesS s L = .ok s' L' n) : L' "v1" ≠ L' "v2" := by
  unfold newNodesS at h
  obtain ⟨s1, L1, n1, n2, h1, h2⟩ := evalF_seq_inv h
  obtain ⟨s2, L2, n3, n4, h3, h4⟩ := evalF_seq_inv h2
  obtain ⟨s3, L3, n5, n6, h5, h6⟩ := evalF_seq_inv h4
  obtain ⟨rfl, rfl⟩ := evalF_push_inv h1
  obtain ⟨j1, w1, hj1, hw1, hset, e1⟩ := evalF_wr_inv h3
  obtain ⟨rfl, rfl⟩ := evalF_push_inv h5
  obtain ⟨j2, w2, hj2, hw2, hset2, e2⟩ := evalF_wr_inv h6
  subst e1 e2
  have hs2 := Fld.set_nodes hset
  simp only [Tbl.size, Tbl.push, Array.size_push] at hs2 ⊢
  rw [upd_ne _ _ (by decide), upd_eq, upd_eq]
  omega

/-- **The position found by `find`** is at most the list capacity. -/
theorem findCall_le {k : LK} {a b : Exp} (hE : EncOK κ s)
    (h : evalF κ ((findP k).call [a, b] ["r"]) s L = .ok s' L' n) : L' "r" ≤ κ.lcap k ∧ s' = s := by
  cases ha : evList κ s L [a, b] with
  | none => simp [Proc.call, evalF, ha] at h
  | some vs =>
    simp only [Proc.call, evalF, ha] at h
    revert h
    cases h2 : evalF κ (findP k).body s (State.setLocs (fun _ => 0) (findP k).params vs) <;>
      simp only [
        List.length_cons,
        List.length_nil,
        zero_add,
        Res.ok.injEq,
        and_imp,
        reduceCtorEq,
        IsEmpty.forall_iff]
    rename_i sb Lb nb
    intro e1 e2 _
    subst e1 e2
    have hvs : ∃ vi vx, vs = [vi, vx] := by
      simp only [evList, List.mapM_cons, List.mapM_nil] at ha
      cases e1 : a.ev κ s L <;> cases e2 : b.ev κ s L <;> simp [e1, e2] at ha
      exact ⟨_, _, ha.symm⟩
    obtain ⟨vi, vx, rfl⟩ := hvs
    have hL0i : State.setLocs (fun _ => 0) (findP k).params [vi, vx] "i" = vi := by
      simp [findP, Machine.State.setLocs, Machine.State.upd]
    have hL0x : State.setLocs (fun _ => 0) (findP k).params [vi, vx] "x" = vx := by
      simp [findP, Machine.State.setLocs, Machine.State.upd]
    -- the first statement read the length: `vi` is a record of `k`
    have hir : vi < κ.lrec k := by
      have h2' := h2
      simp only [findP] at h2'
      obtain ⟨s5, L5, n5, n6, h3, h4⟩ := evalF_seq_inv h2'
      obtain ⟨v, hv, -, -⟩ := evalF_assign_inv h3
      simp only [Exp.ev,  Option.bind_eq_some_iff] at hv
      obtain ⟨x, hx, hv⟩ := hv
      simp only [Option.some.injEq] at hx; subst hx
      split at hv
      · assumption
      · cases hv
    obtain ⟨L2, c, e, hr, -⟩ := findP_agree κ k s _ hL0i hL0x hir
    rw [h2] at e
    injection e with e1 e2; subst e1 e2
    refine ⟨?_, rfl⟩
    simp only [findP, Machine.State.setLocs, Machine.State.upd,
      List.map]
    simp only [ite_true]
    rw [hr]
    exact le_trans (List.findIdx_le_length) (hE.llen k hir)

end runs

/-! ### The drain start -/

/-- Sequencing a `PKok` first statement, passing the end-state bound on. -/
theorem PKok.seqF {Γ Γ' : Reg → Nat} {Q : Core → Prop} {c d : Stm} {s : Core} {L : Loc}
    (hc : PKok K KH κ Γ' W c s L) (hF : Fin (κ := κ) Q (c;; d) s L)
    (hd : ∀ s1 L1 n1, evalF κ c s L = .ok s1 L1 n1 → Gd K KH κ Γ' s1 L1 → Fin (κ := κ) Q d s1 L1 →
      PKok K KH κ Γ W d s1 L1) : PKok K KH κ Γ W (c;; d) s L :=
  PKok.seq hc (fun s1 L1 n1 h1 hG1 => hd s1 L1 n1 h1 hG1 (hF.seq_right h1))

section sd
variable {s : Core} {L : Loc}
variable (hC : CapsW K κ) (hK : 8 ≤ K) (hW : 2 * K + 4 ≤ W)
include hC hK hW

omit hC hK hW in
theorem gdD_lt (hG : Gd K KH κ (ΓD K) s L) {x : Reg} (hx : ¬ (x = "t" ∨ x = "b" ∨ x = "ws")) : L
  x < 2 ^ K :=
  gdD_K hG hx

/-- The insertion of the two new nodes into the tables that contain `v` (`insS`); its locals
`a`, `b` (the room labels) at width `K`. -/
theorem insS_pk (hG : Gd K KH κ (ΓD2 K) s L) : PK K KH κ (ΓD2 K) W insS s L := by
  unfold insS
  refine PK.safe_seq' hC (by omega) (by omega) (by jsafe) hG (fun s1 L1 n1 h1 hG1 => ?_)
  obtain ⟨M, hM, e1, e2⟩ := evalF_assign_inv h1
  subst e1 e2
  have hMK : M < 2 ^ K := hG.valN hC rfl (by jsafe) hM
  have hm : (Exp.var "m").ev κ s (Machine.State.upd L "m" M) = some M := by simp [Exp.ev]
  refine PK.loop hm (hG1.pk hC (by jsafe) hm) (fun _ S L' => Gd K KH κ (ΓD2 K) S L') hG1 (fun _
    _ _ h => h)
    (fun j S L' hj hGS => ?_)
  have hG5 : Gd K KH κ (ΓD2 K) S (Machine.State.upd L' "j" j) :=
    ⟨hGS.enc, hGS.vb, upd_lt hGS.loc (by
      simp [ΓD2]
      omega)⟩
  have hPK : PK K KH κ (ΓD2 K) W insBody S (Machine.State.upd L' "j" j) := by
    unfold insBody
    refine PK.safe_seq' hC (by omega) (by omega) (by jsafe) hG5 (fun _ _ _ _ hG6 => ?_)
    refine PK.seq_g (roomCall_pk hC hK hW hG6 (by jsafe) (by simp [ΓD2])) (fun _ _ _ _ hG7 => ?_)
    refine PK.seq_g (roomCall_pk hC hK hW hG7 (by jsafe) (by simp [ΓD2])) (fun _ _ _ _ hG8 => ?_)
    refine PK.seq_g (tableInsertCall_pk hC hK hW hG8 (by jsafe) (by simp)) (fun _ _ _ _ hG9 => ?_)
    exact tableInsertCall_pk hC hK hW hG9 (by jsafe) (by simp)
  exact ⟨hPK, fun _ _ _ he => hPK.post he⟩

/-- The table of a new node (`newTabS`). -/
theorem newTab_pk (hcapT : κ.lcap .table < 512) (hG : Gd K KH κ (ΓD K) s L) : PK K KH κ (ΓD K) W
  newTabS s L := by
  unfold newTabS
  refine PK.safe_seq' hC (by omega) (by omega) (by jsafe) hG (fun _ _ _ _ hG1 => ?_)
  refine PK.safe_seq' hC (by omega) (by omega) (by
    simp only [copyS, copyBody]
    jsafe) hG1 (fun _ _ _ _ hG2 => ?_)
  exact tab_pk hC hK hW hcapT hG2

/-- The tables of the two new nodes (`stage3S`). -/
theorem stage3_pk (hcapT : κ.lcap .table < 512) (hG : Gd K KH κ (ΓD K) s L) : PK K KH κ (ΓD K) W
  stage3S s L := by
  unfold stage3S
  refine PK.safe_seq' hC (by omega) (by omega) (by jsafe) hG (fun _ _ _ _ hG1 => ?_)
  refine PK.safe_seq' hC (by omega) (by omega) (by jsafe) hG1 (fun _ _ _ _ hG2 => ?_)
  refine PK.seq_g (newTab_pk hC hK hW hcapT hG2) (fun _ _ _ _ hG3 => ?_)
  refine PK.safe_seq' hC (by omega) (by omega) (by jsafe) hG3 (fun _ _ _ _ hG4 => ?_)
  refine PK.safe_seq' hC (by omega) (by omega) (by jsafe) hG4 (fun _ _ _ _ hG5 => ?_)
  exact newTab_pk hC hK hW hcapT hG5

/-- **The children of a new node and its weight** (`chS` at `u`): the weight sum of at most 511
children, written once, bounded by the end state. -/
theorem chS_pkok (hcap : κ.lcap .children < 512) (hG : Gd K KH κ (ΓD K) s L)
    (hF : Fin (κ := κ) (FBat K KH κ (.n .weight) (L "u")) chS s L) : PKok K KH κ (ΓD K) W chS s
      L := by
  have hKe : (2 : Nat) ^ (K + 9) = 512 * 2 ^ K := by rw [pow_add]; norm_num; ring
  have hKp : 1 ≤ 2 ^ K := Nat.one_le_two_pow
  unfold chS at hF ⊢
  refine PKok.safe_seq_fin hC (by omega) (by omega) (by jsafe) hG hF (fun s1 L1 n1 h1 hG1 hF1 => ?_)
  obtain ⟨v0, hv0, e1, e2⟩ := evalF_assign_inv h1
  simp only [Exp.ev, Option.some.injEq] at hv0
  subst e1 e2 hv0
  refine PKok.safe_seq_fin hC (by omega) (by omega) (by jsafe) hG1 hF1 (fun s2 L2 n2 h2 hG2 hF2
    => ?_)
  obtain ⟨N, hN, e1, e2⟩ := evalF_assign_inv h2
  subst e1 e2
  have hNc : N ≤ κ.lcap .children := by
    simp only [Exp.ev, Option.bind_eq_some_iff] at hN
    obtain ⟨x, -, hx⟩ := hN
    split at hx
    · next hxr => cases hx; exact hG.enc.llen _ hxr
    · cases hx
  set L2 := Machine.State.upd (Machine.State.upd L "ws" 0) "nk" N
  have hu2 : L2 "u" = L "u" := by simp [L2, Machine.State.upd]
  have hn2 : (Exp.var "nk").ev κ s L2 = some N := by simp [Exp.ev, L2, Machine.State.upd]
  -- the loop: `ws ≤ j·(2^K − 1)` and `u` unchanged
  have hLoop : PK K KH κ (ΓD K) W (.loop "j" "nk" chBody) s L2 := by
    refine PK.loop hn2 (hG2.pk hC (by jsafe) hn2)
      (fun j S L' => Gd K KH κ (ΓD K) S L' ∧ L' "ws" ≤ j * (2 ^ K - 1))
      ⟨hG2, by simp [L2, Machine.State.upd]⟩ (fun _ _ _ h => h.1) ?_
    intro j S L' hj ⟨hGS, hws⟩
    have hG3 : Gd K KH κ (ΓD K) S (Machine.State.upd L' "j" j) :=
      ⟨hGS.enc, hGS.vb, upd_lt hGS.loc (by
        simp [ΓD]
        have := hC.lcap .children
        omega)⟩
    have hws3 : Machine.State.upd L' "j" j "ws" ≤ j * (2 ^ K - 1) := by
      rw [upd_ne _ _ (by decide)]; exact hws
    have hj512 : j + 1 ≤ 512 := by omega
    unfold chBody
    have hPK : PK K KH κ (ΓD K) W chBody S (Machine.State.upd L' "j" j) := by
      unfold chBody
      refine PK.safe_seq' hC (by omega) (by omega) (by jsafe) hG3 (fun S4 L4 n4 h4 hG4 => ?_)
      refine PK.safe_seq' hC (by omega) (by omega) (by
        simp only [lookupP, findP]
        jsafe) hG4
        (fun S5 L5 n5 h5 hG5 => ?_)
      have hws5 : L5 "ws" ≤ j * (2 ^ K - 1) := by
        rw [evalF_frame_loc (by decide) h5, evalF_frame_loc (by decide) h4]; exact hws3
      refine PK.ite_ok hG5 hC (by
        simp only [chSel]
        jsafe) (fun _ _ _ => ?_) (fun _ => PK.skip hG5)
      refine PK.safe_seq' hC (by omega) (by omega) (by
        simp only [setParS]
        jsafe) hG5 (fun S6 L6 n6 h6 hG6 => ?_)
      refine PK.safe_seq' hC (by omega) (by omega) (by jsafe) hG6 (fun S7 L7 n7 h7 hG7 => ?_)
      refine PK.seq_g (PK.of_safe hC (by omega) (by omega) (by
        simp only [wtS]
        jsafe) hG7)
        (fun S8 L8 n8 h8 hG8 => ?_)
      have hws8 : L8 "ws" ≤ j * (2 ^ K - 1) := by
        rw [evalF_frame_loc (by decide) h8, evalF_frame_loc (by decide) h7,
          evalF_frame_loc (by decide) h6]
        exact hws5
      have hw := gdD_K hG8 (x := "w") (by decide)
      have hv : (("ws" : Exp) + "w").ev κ S8 L8 = some (L8 "ws" + L8 "w") := by
        simp [Exp.ev, Machine.BinOp.eval]
      refine PK.assign hG8 hv (hG8.pk hC (by jsafe) hv) ?_
      simp only [ΓD]; rw [ite_eq_left (by decide)]
      have : (j + 1) * (2 ^ K - 1) ≤ 512 * (2 ^ K - 1) := Nat.mul_le_mul_right _ hj512
      rw [Nat.succ_mul] at this
      omega
    refine ⟨hPK, fun s' L'' c he => ⟨hPK.post he, ?_⟩⟩
    -- the new sum
    obtain ⟨S4, L4, n4, n5, h4, h5⟩ := evalF_seq_inv he
    obtain ⟨S5, L5, n6, n7, h6, h7⟩ := evalF_seq_inv h5
    have hws5 : L5 "ws" ≤ j * (2 ^ K - 1) := by
      rw [evalF_frame_loc (by decide) h6, evalF_frame_loc (by decide) h4]; exact hws3
    obtain ⟨v, -, m, hm⟩ := evalF_ite_inv h7
    split at hm
    · obtain ⟨S6, L6, n8, n9, h8, h9⟩ := evalF_seq_inv hm
      obtain ⟨S7, L7, n10, n11, h10, h11⟩ := evalF_seq_inv h9
      obtain ⟨S8, L8, n12, n13, h12, h13⟩ := evalF_seq_inv h11
      have hG8 := (PK.of_safe (W := W) hC (by omega) (by omega) (by
        simp only [wtS]
        jsafe)
        ((PK.of_safe (W := W) hC (by omega) (by omega) (by jsafe)
          ((PK.of_safe (W := W) hC (by omega) (by omega) (by
            simp only [setParS]
            jsafe)
            ((PK.of_safe (W := W) hC (by omega) (by omega) (by
              simp only [lookupP, findP]
              jsafe)
              ((PK.of_safe (W := W) hC (by omega) (by omega) (by jsafe) hG3).post h4)).post
                h6)).post h8)).post h10)).post h12
      have hw := gdD_K hG8 (x := "w") (by decide)
      have hws8 : L8 "ws" ≤ j * (2 ^ K - 1) := by
        rw [evalF_frame_loc (by decide) h12, evalF_frame_loc (by decide) h10,
          evalF_frame_loc (by decide) h8]
        exact hws5
      obtain ⟨u, hu, -, e⟩ := evalF_assign_inv h13
      simp only [Exp.ev, BinOp.eval, Option.bind_some, Option.some.injEq] at hu
      rw [e, upd_eq, ← hu, Nat.succ_mul]; omega
    · rw [evalF_frame_loc (by decide) hm]
      have : j * (2 ^ K - 1) ≤ (j + 1) * (2 ^ K - 1) := Nat.mul_le_mul_right _ (by omega)
      omega
  refine PKok.seq (PK.ok hLoop) (fun s3 L3 n3 h3 hG3 => ?_)
  have hF3 := hF2.seq_right h3
  have hu3 : L3 "u" = L "u" := by rw [evalF_frame_loc (by decide) h3, hu2]
  have hws : L3 "ws" < 2 ^ (K + 9) := by simpa [ΓD] using hG3.loc "ws"
  refine PKok.seq_fin (Q' := FBat K KH κ (.n .weight) (L "u")) hF3
    (fun _ _ _ _ _ _ _ h5 hq => FBat.back (by decide) h5 hq) (fun hF4 => ?_)
    (fun s4 L4 n4 h4 hG4 _ => PK.ok (PK.of_safe hC (by omega) (by omega) (by jsafe) hG4))
  exact PK.ok (PK.wr_finAt hC hG3 (by jsafe) (by jsafe) (by simp [Exp.ev, hu3]) hF4)

/-- **The children of the two new nodes** (`stage56S`), the new nodes `v1 ≠ v2`. -/
theorem stage56_pkok (hcap : κ.lcap .children < 512) (hG : Gd K KH κ (ΓD K) s L) (hne : L "v1" ≠
  L "v2")
    (hF : Fin (κ := κ) (FB K KH κ (.n .weight)) stage56S s L) : PKok K KH κ (ΓD K) W stage56S s
      L := by
  unfold stage56S at hF ⊢
  refine PKok.safe_seq_fin hC (by omega) (by omega) (by jsafe) hG hF (fun s1 L1 n1 h1 hG1 hF1 => ?_)
  refine PKok.safe_seq_fin hC (by omega) (by omega) (by jsafe) hG1 hF1 (fun s2 L2 n2 h2 hG2 hF2
    => ?_)
  have hu2 : L2 "u" = L "v1" := by
    rw [evalF_frame_loc (by decide) h2]
    obtain ⟨v, hv, -, e⟩ := evalF_assign_inv h1
    simp only [Exp.ev, Option.some.injEq] at hv; rw [e, upd_eq, ← hv]
  have hv22 : L2 "v2" = L "v2" := by
    rw [evalF_frame_loc (by decide) h2, evalF_frame_loc (by decide) h1]
  refine PKok.seq_fin (Q' := FBat K KH κ (.n .weight) (L2 "u")) hF2 (fun s3 L3 n3 s' L' n h3 h4
    hq => ?_)
    (fun hF3 => chS_pkok hC hK hW hcap hG2 hF3) (fun s3 L3 n3 h3 hG3 hF3 => ?_)
  · obtain ⟨s4, L4, n4, n5, h5, h6⟩ := evalF_seq_inv h4
    obtain ⟨s5, L5, n6, n7, h7, h8⟩ := evalF_seq_inv h6
    obtain ⟨v, hv, e1, e2⟩ := evalF_assign_inv h5
    obtain ⟨w, -, e3, e4⟩ := evalF_assign_inv h7
    subst e1 e3
    have hu5 : L5 "u" = L "v2" := by
      rw [e4, upd_ne _ _ (by decide), e2, upd_eq]
      simp only [Exp.ev,
        Option.some.injEq] at hv; rw [← hv, evalF_frame_loc frame_chS.2.2.2.2.2.2.2.2 h3, hv22]
    exact FBat.backAt frame_chS.1 frame_chS.2.1 h8 (by
      rw [hu5, hu2]
      exact hne) (hq _)
  · refine PKok.safe_seq_fin hC (by omega) (by omega) (by jsafe) hG3 hF3 (fun s4 L4 n4 h4 hG4
      hF4 => ?_)
    refine PKok.safe_seq_fin hC (by omega) (by omega) (by jsafe) hG4 hF4 (fun s5 L5 n5 h5 hG5
      hF5 => ?_)
    exact chS_pkok hC hK hW hcap hG5 (hF5.mono (fun t h => h.at' _))

/-- **The parent's children** (`stage7S`): the position `r + 1` after `find`. -/
theorem stage7_pk (hG : Gd K KH κ (ΓD K) s L) : PK K KH κ (ΓD K) W stage7S s L := by
  unfold stage7S
  peelSafe
  rename_i hG1
  refine PK.safe_seq' hC (by omega) (by omega) (by
    simp only [findP]
    jsafe) hG1 (fun s2 L2 n2 h2 hG2 => ?_)
  have hr := (findCall_le hG1.enc h2).1
  refine PK.safe_seq' hC (by omega) (by omega) (by jsafe) hG2 (fun s3 L3 n3 h3 hG3 => ?_)
  have hr3 : L3 "r" ≤ κ.lcap .children := by rw [evalF_frame_loc (by decide) h3]; exact hr
  have hl2 := hC.lcap2 .children
  have hev : evList κ s3 L3 ["p", "r" + 1, "v2", 0] = some [L3 "p", L3 "r" + 1, L3 "v2", 0] := by
    simp [evList, Exp.ev, Machine.BinOp.eval]
  refine PK.callV (Γc := ΓK K) (Γe := ΓK K) hG3 hev (hG3.pkList hC (fun e he => ?_) hev) (fun v
    hv => ?_)
    (fun _ => le_refl K) (fun hG0 => PK.of_safe hC (by omega) (by omega)
      (by
        simp only [insertIdxP, swapS]
        jsafe) hG0) (by simp [insertIdxP]) (by simp)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl <;> jsafe
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact gdD_K hG3 (by decide)
    · omega
    · exact gdD_K hG3 (by decide)
    · exact Nat.two_pow_pos _

/-- **The main part of a drain start** (`sdMain`). -/
theorem sdMain_pkok (hcap : κ.lcap .children < 512) (hcapT : κ.lcap .table < 512) (hG : Gd K KH
  κ (ΓD K) s L)
    (hF : Fin (κ := κ) (FB K KH κ (.n .weight)) sdMain s L) : PKok K KH κ (ΓD K) W sdMain s L := by
  unfold sdMain at hF ⊢
  refine PKok.safe_seq_fin hC (by omega) (by omega) (by jsafe) hG hF (fun s1 L1 n1 h1 hG1 hF1 => ?_)
  -- `b` is a child now
  have hb1 : L1 "b" < 2 ^ K := by
    obtain ⟨c, hc, m, hm⟩ := evalF_ite_inv h1
    split at hm
    · obtain ⟨v, hv, -, e⟩ := evalF_assign_inv hm
      rw [e, upd_eq]; exact hG.valW (W := W) hC (by jsafe) (by jsafe) hv
    · obtain ⟨v, hv, -, e⟩ := evalF_assign_inv hm
      simp only [ Exp.ev, Option.some.injEq] at hv
      rw [e, upd_eq, ← hv]; exact Nat.two_pow_pos _
  refine PKok.seqF (PK.ok (drainSide_pk hC hK hW hG1)) hF1 (fun s2 L2 n2 h2 hG2 hF2 => ?_)
  refine PKok.safe_seq_fin hC (by omega) (by omega) (by
    simp only [newNodesS]
    jsafe) hG2 hF2
    (fun s3 L3 n3 h3 hG3 hF3 => ?_)
  have hne3 := newNodes_ne h3
  have hb3 : L3 "b" < 2 ^ K := by
    rw [evalF_frame_loc (by decide) h3, evalF_frame_loc (by decide) h2]; exact hb1
  have hG3' : Gd K KH κ (ΓD2 K) s3 L3 := hG3.of_loc (fun x => by
    by_cases hx : x = "b"
    · subst hx; simpa [ΓD2] using hb3
    · have := hG3.loc x; simp only [ΓD] at this; simp only [ΓD2]; split_ifs at this ⊢ <;> simp_all)
  refine PKok.seqF (PK.ok ((insS_pk hC hK hW hG3').mono (le_refl W) (ΓD2_le K))) hF3
    (fun s4 L4 n4 h4 hG4 hF4 => ?_)
  refine PKok.seqF (PK.ok (stage3_pk hC hK hW hcapT hG4)) hF4 (fun s5 L5 n5 h5 hG5 hF5 => ?_)
  refine PKok.safe_seq_fin hC (by omega) (by omega) (by
    simp only [stage4S, atS, atBody]
    jsafe) hG5 hF5
    (fun s6 L6 n6 h6 hG6 hF6 => ?_)
  have hv1 : L6 "v1" = L3 "v1" := by
    rw [evalF_frame_loc (by decide) h6, evalF_frame_loc (by decide) h5,
      evalF_frame_loc (by decide) h4]
  have hv2 : L6 "v2" = L3 "v2" := by
    rw [evalF_frame_loc (by decide) h6, evalF_frame_loc (by decide) h5,
      evalF_frame_loc (by decide) h4]
  refine PKok.seq_fb (Γ' := ΓD K) hF6 (by decide)
    (fun hF7 => stage56_pkok hC hK hW hcap hG6 (by
      rw [hv1, hv2]
      exact hne3) hF7)
    (fun s7 L7 n7 h7 hG7 _ => PK.ok (PK.seq_g (stage7_pk hC hK hW hG7)
      (fun _ _ _ _ hG8 => PK.of_safe hC (by omega) (by omega) (by
        simp only [stage8S]
        jsafe) hG8)))

/-- **A drain start** (`startDrainS`), the new nodes' weights bounded by the end state. -/
theorem startDrain_pkok (hcap : κ.lcap .children < 512) (hcapT : κ.lcap .table < 512)
    (hG : Gd K KH κ (ΓD K) s L) (hF : Fin (κ := κ) (FB K KH κ (.n .weight)) startDrainS s L) :
    PKok K KH κ (ΓD K) W startDrainS s L := by
  unfold startDrainS at hF ⊢
  refine PKok.safe_seq_fin hC (by omega) (by omega) (by jsafe) hG hF (fun s1 L1 n1 h1 hG1 hF1 => ?_)
  refine PKok.safe_seq_fin hC (by omega) (by omega) (by jsafe) hG1 hF1 (fun s2 L2 n2 h2 hG2 hF2
    => ?_)
  refine PKok.ite_ok hC hG2 (by jsafe) (fun _ _ _ => PK.ok (PK.skip hG2)) (fun hv => ?_)
  refine PKok.seqF (PK.ok (drainCut_pk hC hK hW hcap hG2)) (hF2.ite_f hv) (fun s3 L3 n3 h3 hG3
    hF3 => ?_)
  refine PKok.ite_ok hC hG3 (by
    simp only [sdCond]
    jsafe) (fun _ _ _ => PK.ok (PK.skip hG3))
    (fun hv2 => sdMain_pkok hC hK hW hcap hcapT hG3 (hF3.ite_f hv2))

end sd

end OrderMaintenance.Impl
