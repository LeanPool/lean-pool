/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.PeakTop1
public import LeanPool.OrderMaintenance.Impl.Init


/-!
# Theorem W, option (A), stage A2: the peak of the construction of a core

* `initState_pk`: the centre labels `2^(B − 1)`.
* `initStep_pk`: one stage of the chain above the first chunk: the table label `2^(β − 1)`, the
  next height `h + 1 ≤ H + 1`, and the tag `tg + 2^(β−1)·2^((h−1)β) < 2^(hβ) ≤ 2^K`, given the
  stage invariant `tg < 2^((h−1)β)` (as in `initStepP_mid`).
* `initLoop_pk`, `initCore_pk`, `prepP_pk`: the loop of stages, the construction, and one
  preparation step.

Nothing here is used by Theorems A and B.
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model
open OrderMaintenance.Machine (Reg BinOp UnOp State)

variable {K KH W : Nat} {κ : Caps}

section prep
variable {s : Core} {L : Loc} {Γ : Reg → Nat}

/-- `prepSet` with known values below `2^K`. -/
theorem PK.prepSetV {h b t : Exp} {vh vb vt : Nat} (hG : Gd K KH κ Γ s L) (hv : evList κ s L [h,
  b, t] = some [vh, vb, vt])
    (hpk : pkList κ s L [h, b, t] < 2 ^ W) (h1 : vh < 2 ^ K) (h2 : vb < 2 ^ K) (h3 : vt < 2 ^ K) :
    PK K KH κ Γ W (.prepSet h b t) s L := by
  intro hnb
  refine ⟨by simp only [pkF]; exact hpk, fun s' L' n e => ?_⟩
  have he : h.ev κ s L = some vh ∧ b.ev κ s L = some vb ∧ t.ev κ s L = some vt := by
    simp only [evList, List.mapM_cons, List.mapM_nil] at hv
    cases e1 : h.ev κ s L <;> cases e2 : b.ev κ s L <;> cases e3 : t.ev κ s L <;> simp_all
  obtain ⟨eh, eb, et⟩ := he
  have e' := e
  simp only [evalF, eh, eb, et] at e
  cases hp : s.prep with
  | none => rw [hp] at e; cases e
  | some pr =>
    rw [hp] at e
    simp only [Res.ok.injEq] at e; obtain ⟨rfl, rfl, -⟩ := e
    exact ⟨hG.enc.of_ok e', hG.vb.prepSet hp h1 h2 h3, hG.loc⟩

end prep

theorem isPre_vals {s s1 : Core} {L L1 : Loc} {n : Nat} {pr : Prep} (h : evalF κ isPre s L = .ok
  s1 L1 n)
    (hp : s.prep = some pr) :
    L1 "h" = pr.h ∧ L1 "tg" = pr.tag ∧ L1 "c" = pr.chunk ∧ L1 "bl" = pr.below ∧ s1.prep = s.prep
      := by
  unfold isPre at h
  obtain ⟨sa, La, na, nb, ha, h⟩ := evalF_seq_inv h
  obtain ⟨va, hva, e1, e2⟩ := evalF_assign_inv ha; subst e1 e2
  obtain ⟨sb, Lb, nc, nd, hb, h⟩ := evalF_seq_inv h
  obtain ⟨vb, hvb, e1, e2⟩ := evalF_assign_inv hb; subst e1 e2
  obtain ⟨sc, Lc, ne, nf, hc, h⟩ := evalF_seq_inv h
  obtain ⟨vc, hvc, e1, e2⟩ := evalF_assign_inv hc; subst e1 e2
  obtain ⟨sd, Ld, ng, nh, hd, h⟩ := evalF_seq_inv h
  obtain ⟨vd, hvd, e1, e2⟩ := evalF_assign_inv hd; subst e1 e2
  simp only [Exp.ev, OF.get, hp, Option.some.injEq] at hva hvb hvc hvd
  subst hva hvb hvc hvd
  have hL : L1 = Machine.State.upd (Machine.State.upd (Machine.State.upd (Machine.State.upd L "c"
      pr.chunk) "h" pr.h) "bl" pr.below) "tg" pr.tag := by
    have := evalF_frame_loc (c := .ite ("h" =ₑ 1) (.lclear .cin "c") .skip) (x := "h") (by decide) h
    obtain ⟨v, -, m, hm⟩ := evalF_ite_inv h
    split at hm
    · simp only [evalF] at hm
      split at hm
      · split at hm
        · simp only [Res.ok.injEq] at hm; exact hm.2.1.symm
        · cases hm
      · cases hm
    · simp only [evalF, Res.ok.injEq] at hm; exact hm.2.1.symm
  have hs : s1.prep = s.prep := by
    obtain ⟨v, -, m, hm⟩ := evalF_ite_inv h
    split at hm
    · simp only [evalF] at hm
      split at hm
      · split at hm
        · next s' hs' =>
            simp only [Res.ok.injEq] at hm
            rw [← hm.1]
            unfold LK.set at hs'
            split at hs' <;> simp only [Option.some.injEq, reduceCtorEq] at hs'
            subst hs'
            exact LK.put_prep _ _ _ _
        · cases hm
      · cases hm
    · simp only [evalF, Res.ok.injEq] at hm; rw [← hm.1]
  subst hL
  refine ⟨?_, ?_, ?_, ?_, hs⟩ <;> simp [Machine.State.upd]

section init
variable {s : Core} {L : Loc}
variable (hC : CapsW K κ) (hK : 8 ≤ K) (hW : 2 * K + 4 ≤ W)
include hC hK hW

/-- **One stage of the chain** (`initStep`), given the stage invariant on the tag. -/
theorem initStep_pk (hG : Gd K KH κ (ΓK K) s L)
    (htag : ∀ pr, s.prep = some pr → pr.h ≤ s.P.H → pr.tag < 2 ^ ((pr.h - 1) * s.P.beta) ∧ 1 ≤ pr.h)
    (hb1 : 1 ≤ s.P.beta) : PK K KH κ (ΓK K) W initStepP.body s L := by
  simp only [initStepP]
  refine PK.ite_ok hG hC (by proveSafe) (fun v hv hv0 => ?_) (fun _ => PK.of_safe hC (by omega)
    (by omega)
    (by proveSafe) hG)
  cases hp : s.prep with
  | none => simp [Exp.ev, OF.get, hp, b2n] at hv; exact absurd hv.symm hv0
  | some pr =>
  refine PK.safe_seq' hC (by omega) (by omega) (by
    simp only [isPre]
    proveSafe) hG (fun s1 L1 n1 h1 hG1 => ?_)
  obtain ⟨hh, htg, -, -, hps⟩ := isPre_vals h1 hp
  have hP1 : s1.P = s.P := evalF_P h1
  have hroom := hG.vb.room
  refine PK.ite_ok hG1 hC (by proveSafe) (fun c hc hc0 => ?_) (fun _ => PK.of_safe hC (by omega)
    (by omega)
    (by
      simp only [isFinish]
      proveSafe) hG1)
  have hhH : pr.h ≤ s.P.H := by
    simp [Exp.ev, Machine.BinOp.eval, PF.get, hh, hP1] at hc
    by_contra hn; simp [hn] at hc; exact hc0 hc.symm
  obtain ⟨hpt, hh1⟩ := htag pr hp hhH
  unfold isBuild
  have hcv : (Exp.bin .shl 1 (.prm .beta - 1)).ev κ s1 L1 = some (1 * 2 ^ (s.P.beta - 1)) := by
    simp only [Exp.sub_def, Exp.ofNat_def, Exp.ev, Option.bind_some,
      Machine.BinOp.eval, PF.get, hP1]
    rw [ite_eq_left hb1]; rfl
  have hcs : (Exp.bin .shl 1 (.prm .beta - 1)).ShOK κ s1 L1 K :=
    ⟨trivial, Exp.shOK_of_noShl _ _ _ _ _ rfl, fun _ => by
      simp only [Exp.val, Exp.sub_def, Exp.ofNat_def, Exp.ev, Option.bind_some,
        Machine.BinOp.eval, PF.get, hP1]
      rw [ite_eq_left hb1]; simp; have := hroom.beta; omega⟩
  have hctr : 1 * 2 ^ (s.P.beta - 1) < 2 ^ K := by
    have := hroom.beta
    simp only [one_mul, gt_iff_lt]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  refine PK.assign_seq hG1 hcv (hG1.pkS hC hcs hcv (by proveSafe)) (by simpa using hctr) (fun hG2
    => ?_)
  set L2 := Machine.State.upd L1 "ctr" (1 * 2 ^ (s.P.beta - 1))
  refine PK.safe_seq' hC (by omega) (by omega) (by
    simp only [isNode]
    proveSafe) hG2 (fun s3 L3 n3 h3 hG3 => ?_)
  refine PK.safe_seq' hC (by omega) (by omega) (by
    simp only [isLink]
    proveSafe) hG3 (fun s4 L4 n4 h4 hG4 => ?_)
  have hP4 : s4.P = s.P := (evalF_P h4).trans ((evalF_P h3).trans hP1)
  have f4 : ∀ x, x = "h" ∨ x = "tg" ∨ x = "ctr" → L4 x = L2 x := by
    rintro x (rfl | rfl | rfl) <;>
      rw [evalF_frame_loc (by simp [isLink, Stm.asg]) h4,
        evalF_frame_loc (by simp [isNode, Stm.asg]) h3]
  have h4h : L4 "h" = pr.h := by rw [f4 _ (by simp)]; simp [L2, Machine.State.upd, hh]
  have h4t : L4 "tg" = pr.tag := by rw [f4 _ (by simp)]; simp [L2, Machine.State.upd, htg]
  have h4c : L4 "ctr" = 1 * 2 ^ (s.P.beta - 1) := by
    rw [f4 _ (by simp)]; simp [L2, Machine.State.upd]
  have hvK : L4 "v" < 2 ^ K := by simpa using hG4.loc "v"
  unfold isUp
  -- the tag of the next stage is below `2^(hβ) ≤ 2^K`
  have hexp : (pr.h - 1) * s.P.beta + s.P.beta ≤ K := by
    have hm : (pr.h - 1) * s.P.beta ≤ s.P.H * s.P.beta := Nat.mul_le_mul_right _ (by omega)
    have hHb := hroom.Hb; rw [Nat.add_mul, one_mul] at hHb
    omega
  have htv : pr.tag + 1 * 2 ^ (s.P.beta - 1) * (1 * 2 ^ ((pr.h - 1) * s.P.beta)) < 2 ^ K := by
    have e1 : 1 * 2 ^ (s.P.beta - 1) * (1 * 2 ^ ((pr.h - 1) * s.P.beta)) = 2 ^ ((pr.h - 1) *
      s.P.beta + (s.P.beta - 1)) := by
      rw [pow_add]; ring
    rw [e1]
    have e2 : 2 ^ ((pr.h - 1) * s.P.beta) ≤ 2 ^ ((pr.h - 1) * s.P.beta + (s.P.beta - 1)) :=
      pow_le_pow' (by omega)
    have e3 : 2 ^ ((pr.h - 1) * s.P.beta + (s.P.beta - 1)) * 2 ≤ 2 ^ K := by
      rw [← pow_succ]; exact pow_le_pow' (by omega)
    omega
  have hev : evList κ s4 L4 [("h" : Exp) + 1, "v", ("tg" : Exp) + "ctr" * .bin .shl 1 (("h" - 1)
    * .prm .beta)] =
      some [pr.h + 1, L4 "v", pr.tag + 1 * 2 ^ (s.P.beta - 1) * (1 * 2 ^ ((pr.h - 1) *
        s.P.beta))] := by
    simp [evList, Exp.ev, Machine.BinOp.eval, PF.get, hP4, h4h, h4t, h4c, hh1]
  have hsh : ∀ e ∈ [("h" : Exp) + 1, "v", ("tg" : Exp) + "ctr" * .bin .shl 1 (("h" - 1) * .prm
    .beta)],
      e.ShOK κ s4 L4 K := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro e (rfl | rfl | rfl)
    · exact Exp.shOK_of_noShl _ _ _ _ _ rfl
    · trivial
    · refine ⟨trivial, ⟨trivial, ⟨trivial, Exp.shOK_of_noShl _ _ _ _ _ rfl, fun _ => ?_⟩, fun h
        => by cases h⟩,
        fun h => by cases h⟩
      simp only [Exp.val, Exp.ev, Exp.ofNat_def, Exp.sub_def, h4h, BinOp.eval, Option.bind_some,
          hh1, ↓reduceIte, PF.get, hP4, Option.getD_some]
      have hm : (pr.h - 1) * s.P.beta ≤ s.P.H * s.P.beta := Nat.mul_le_mul_right _ (by omega)
      have hHb := hroom.Hb; rw [Nat.add_mul, one_mul] at hHb
      omega
  have hpk : pkList κ s4 L4 [("h" : Exp) + 1, "v", ("tg" : Exp) + "ctr" * .bin .shl 1 (("h" - 1)
    * .prm .beta)] < 2 ^ W :=
    pkList_lt' (S := K) (hG4.memW hC) hC hG4.loc (fun e he => ⟨hsh e he, by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl <;> proveSafe⟩) hev
  refine PK.seq_g (PK.seq_g (PK.prepSetV hG4 hev hpk (by
    have := hC.pw
    rw [hG.enc.pwH] at this
    omega) hvK htv)
    (fun s5 L5 n5 h5 hG5 => PK.of_safe hC (by omega) (by omega) (by proveSafe) hG5))
    (fun s6 L6 n6 h6 hG6 => PK.of_safe hC (by omega) (by omega) (by proveSafe) hG6)

end init

section init2
variable {s : Core} {L : Loc}
variable (hC : CapsW K κ) (hK : 8 ≤ K) (hW : 2 * K + 4 ≤ W)
include hC hK hW

/-- A write of the centre label `2^(B − 1)` (`B` a parameter, `1 ≤ B ≤ K`). -/
theorem PK.wr_centre {Γ : Reg → Nat} {f : Fld} {i : Exp} {k : PF} (hG : Gd K KH κ Γ s L) (hi :
  i.OK Γ K KH W)
    (hk1 : 1 ≤ k.get s.P) (hkK : k.get s.P ≤ K) (hf : f.wd K KH = K) :
    PK K KH κ Γ W (.wr f i (.bin .shl 1 (.prm k - 1))) s L := by
  intro hnb
  cases hj : i.ev κ s L with
  | none => simp [evalF, hj] at hnb
  | some j =>
    have hv : (Exp.bin .shl 1 (.prm k - 1)).ev κ s L = some (1 * 2 ^ (k.get s.P - 1)) := by
      simp only [Exp.sub_def, Exp.ofNat_def, Exp.ev, Option.bind_some,
        Machine.BinOp.eval]
      rw [ite_eq_left hk1]; rfl
    have hs : (Exp.bin .shl 1 (.prm k - 1)).ShOK κ s L K :=
      ⟨trivial, Exp.shOK_of_noShl _ _ _ _ _ rfl, fun _ => by
        simp only [Exp.val, Exp.sub_def, Exp.ofNat_def, Exp.ev, Option.bind_some,
          Machine.BinOp.eval]
        rw [ite_eq_left hk1]; simp; omega⟩
    refine PK.wr hG hj hv (hG.pk hC hi hj) (hG.pkS hC hs hv (by proveSafe)) ?_ hnb
    rw [hf]; simp only [one_mul]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)

theorem initElt_pk (hG : Gd K KH κ (ΓK K) s L) : PK K KH κ (ΓK K) W initEltS s L := by
  unfold initEltS
  peelSafe; peelSafe; peelSafe
  exact PK.seq_g (PK.wr_centre hC hK hW ‹_› (k := .Be) (by proveSafe) (‹Gd K KH κ (ΓK K) _
    _›.vb.room.Be1)
    (‹Gd K KH κ (ΓK K) _ _›.vb.room.Be) rfl) (fun _ _ _ _ hG4 => PK.of_safe hC (by omega) (by omega)
      (by proveSafe) hG4)

theorem initGrp_pk (hG : Gd K KH κ (ΓK K) s L) : PK K KH κ (ΓK K) W initGrpS s L := by
  unfold initGrpS
  peelSafe; peelSafe; peelSafe
  exact PK.seq_g (PK.wr_centre hC hK hW ‹_› (k := .Bg) (by proveSafe) (‹Gd K KH κ (ΓK K) _
    _›.vb.room.Bg1)
    (‹Gd K KH κ (ΓK K) _ _›.vb.room.Bg) rfl) (fun _ _ _ _ hG4 => PK.of_safe hC (by omega) (by omega)
      (by proveSafe) hG4)

/-- **The initial state** of a core. -/
theorem initState_pk (hG : Gd K KH κ (ΓK K) s L) : PK K KH κ (ΓK K) W initStateS s L := by
  unfold initStateS
  refine PK.seq_g (initElt_pk hC hK hW hG) (fun _ _ _ _ hG1 => PK.seq_g (initGrp_pk hC hK hW hG1)
    (fun _ _ _ _ hG2 => PK.of_safe hC (by omega) (by omega) (by
      simp only [initChkS, initScS]
      proveSafe) hG2))

end init2

section init3
variable {s : Core} {L : Loc}
variable (hC : CapsW K κ) (hK : 8 ≤ K) (hW : 2 * K + 4 ≤ W)
include hC hK hW

/-- **The loop of stages**, along a Level F invariant `I` (as in `initLoopS_agree`). -/
theorem initLoop_pk (I : Nat → Core → Prop) (h0 : I 0 s)
    (hstep : ∀ j t, I j t → j < s.P.H + 1 → ∃ b t' L' n,
      evalF κ initStepP.body t (fun _ => 0) = .ok t' L' n ∧ L' "done" = b2n b ∧
      (b = false → I (j + 1) t') ∧
      (Gd K KH κ (ΓK K) t (fun _ => 0) → PKok K KH κ (ΓK K) W initStepP.body t (fun _ => 0)))
    (hG : Gd K KH κ (ΓK K) s L) : PKok K KH κ (ΓK K) W initLoopS s L := by
  unfold initLoopS
  refine PKok.seq (PK.ok (PK.of_safe hC (by omega) (by omega) (by proveSafe) hG)) (fun s1 L1 n1
    h1 hG1 => ?_)
  obtain ⟨v, hv, e1, e2⟩ := evalF_assign_inv h1
  subst e1 e2
  simp only [Exp.ev, Option.some.injEq] at hv; subst hv
  have hN : (Exp.prm .H + 1).ev κ s (Machine.State.upd L "dn" 0) = some (s.P.H + 1) := by
    simp [Exp.ev, Machine.BinOp.eval, PF.get]
  have hH1 : s.P.H + 1 < 2 ^ K := by have := hC.pw; rw [hG.enc.pwH] at this; exact this
  refine PKok.loop hN (hG1.pk hC (by proveSafe) hN)
    (fun j S L' => Gd K KH κ (ΓK K) S L' ∧ ((L' "dn" = 0 ∧ I j S) ∨ L' "dn" = 1))
    ⟨hG1, Or.inl ⟨by simp [Machine.State.upd], h0⟩⟩ (fun _ _ _ h => h.1) ?_
  intro j S L' hj ⟨hGS, hcase⟩
  simp only [initLoopBody]
  set L2 := Machine.State.upd L' "ii" j
  have hG2 : Gd K KH κ (ΓK K) S L2 := ⟨hGS.enc, hGS.vb, upd_lt hGS.loc (lt_trans hj hH1)⟩
  rcases hcase with ⟨hdn, hI⟩ | hdn
  · have hc0 : ("dn" =ₑ 0 : Exp).ev κ S L2 = some 1 := by
      simp [Exp.ev, Machine.BinOp.eval, L2, Machine.State.upd,
        hdn]
    obtain ⟨b, t', Lg, ng, eg, hok, hI', hPK⟩ := hstep j S hI hj
    have hargs : evList κ S L2 [] = some [] := rfl
    have hG0 : Gd K KH κ (ΓK K) S (fun _ => 0) := ⟨hG2.enc, hG2.vb, zero_locs _⟩
    have hCall : PKok K KH κ (ΓK K) W (initStepP.call [] ["d"]) S L2 :=
      PKok.call hG2 hargs (by simp [pkList]) (hPK hG0) (by simp [initStepP]) (by simp)
    have ec := evalF_call_ok (q := initStepP) (args := []) (ds := ["d"]) (L := L2) hargs eg
    set L3 := Machine.State.setLocs L2 ["d"] (initStepP.rets.map Lg)
    have h3d : L3 "d" = b2n b := by
      simp [L3, initStepP, Machine.State.setLocs, Machine.State.upd, hok]
    have h3dn : L3 "dn" = 0 := by
      simp [L3, L2, initStepP, Machine.State.setLocs, Machine.State.upd, hdn]
    obtain ⟨pc, hG3⟩ := hCall _ _ _ ec
    have hc1 : (Exp.var "d").ev κ t' L3 = some (b2n b) := by simp [Exp.ev, h3d]
    intro s' L'' c he
    have hpk : pkF κ (.ite ("dn" =ₑ 0) (initStepP.call [] ["d"];; .ite "d" ("dn" ::= 1) .skip)
      .skip) S L2
        < 2 ^ W := by
      rw [pkF_ite hc0, ite_eq_left one_ne_zero, pkF_seq_ok ec]
      refine max_lt (hG2.pk hC (by proveSafe) hc0) (max_lt pc ?_)
      rw [pkF_ite hc1]
      refine max_lt (hG3.pk hC (by proveSafe) hc1) ?_
      have : (1 : Nat) < 2 ^ W := Nat.one_lt_two_pow (by omega)
      split
      · simpa [pkF, Exp.pk] using this
      · simp [pkF]
    cases b
    · have et : evalF κ (.ite "d" ("dn" ::= 1) .skip) t' L3 = .ok t' L3 _ :=
        evalF_ite_f (by simpa [b2n] using hc1) evalF_skip
      have he' := evalF_ite_t (f := .skip) hc0 one_ne_zero (evalF_seq_ok2 ec et)
      rw [he'] at he
      cases he
      exact ⟨hpk, hG3, Or.inl ⟨h3dn, hI' rfl⟩⟩
    · have et : evalF κ (.ite "d" ("dn" ::= 1) .skip) t' L3 = .ok t' (Machine.State.upd L3 "dn"
        1) _ :=
        evalF_ite_t (by simpa [b2n] using hc1) one_ne_zero (evalF_assign_ok (v := 1) rfl)
      have he' := evalF_ite_t (f := .skip) hc0 one_ne_zero (evalF_seq_ok2 ec et)
      rw [he'] at he
      cases he
      exact ⟨hpk, ⟨hG3.enc, hG3.vb, upd_lt hG3.loc (by
        simp only [ΓK]
        exact Nat.one_lt_two_pow (by omega))⟩,
        Or.inr (by simp [Machine.State.upd])⟩
  · have hc0 : ("dn" =ₑ 0 : Exp).ev κ S L2 = some 0 := by
      simp [Exp.ev, Machine.BinOp.eval, L2, Machine.State.upd,
        hdn]
    intro s' L'' c he
    rw [evalF_ite_f hc0 evalF_skip] at he
    cases he
    refine ⟨?_, hG2, Or.inr (by simp [L2, Machine.State.upd, hdn])⟩
    rw [pkF_ite hc0, ite_eq_right (by simp)]
    exact max_lt (hG2.pk hC (by proveSafe) hc0) (by simp [pkF])

/-- **The construction of a core** (`initCore`), lazy (`lz = 1`) or eager (`lz = 0`, with the
loop of stages). -/
theorem initCore_pk (hG : Gd K KH κ (ΓK K) s L)
    (hloop : ∀ s1 L1, Gd K KH κ (ΓK K) s1 L1 → PKok K KH κ (ΓK K) W initLoopS s1 L1) :
    PKok K KH κ (ΓK K) W initCoreS s L := by
  unfold initCoreS
  refine PKok.seq (PK.ok (initState_pk hC hK hW hG)) (fun s1 L1 n1 h1 hG1 => ?_)
  refine PKok.seq (PK.ok (PK.of_safe hC (by omega) (by omega) (by proveSafe) hG1)) (fun s2 L2 n2
    h2 hG2 => ?_)
  refine PKok.ite_ok hC hG2 (by proveSafe) (fun _ _ _ => PK.ok (PK.of_safe hC (by omega)
    (by omega)
    (by proveSafe) hG2)) (fun _ => ?_)
  exact PKok.seq (hloop _ _ hG2) (fun _ _ _ _ hG3 => PK.ok (PK.of_safe hC (by omega) (by omega)
    (by proveSafe) hG3))

/-- **A preparation step** (`prepareStep`): one stage when the core is not ready. -/
theorem prepP_pk (hG : Gd K KH κ (ΓK K) s L)
    (hstep : Gd K KH κ (ΓK K) s (fun _ => 0) → PKok K KH κ (ΓK K) W initStepP.body s (fun _ => 0)) :
    PKok K KH κ (ΓK K) W prepP.body s L := by
  simp only [prepP]
  refine PKok.seq ?_ (fun _ _ _ _ hG1 => PK.ok (PK.of_safe hC (by omega) (by omega) (by
    proveSafe) hG1))
  refine PKok.ite_ok hC hG (by proveSafe) (fun _ _ _ => ?_) (fun _ => PK.ok (PK.skip hG))
  refine PKok.seq (PKok.call hG (vs := []) rfl (by simp [pkList]) (hstep ⟨hG.enc, hG.vb,
    zero_locs _⟩)
    (by simp [initStepP]) (by simp)) (fun _ _ _ _ hG2 => ?_)
  exact PK.ok (PK.of_safe hC (by omega) (by omega) (by proveSafe) hG2)

end init3

end OrderMaintenance.Impl
