/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Word.PeakFin


/-!
# Theorem W, option (A), stage A2: the peak of a sweep step (`drainStep`) and of the funding loop

* `dsLab_pk`: the digit weights `e1 = 2^(hβ)`, `e0 = 2^((h−1)β)` (below `2^K`, `h < H`), and the
  old and new tag fields `pv·e1 + vb·e0` at width `2K + 1`.
* `dsTag_pkok`: the new tag `ty − old + new` (width `2K + 2`), written by `guardedSetTag`, bounded
  by the end state's tag (`gstCall_pk`).
* `dsP_pkok`: `drainStep`, its tag bounded by the end state of the job step (`Fin`).
* `fund_pkok`: the funding loop's counter `k + 1`, below `s` by its guard.

The locals of a job step are at width `K` except `pw` (`a^ht ≤ 2^K`) at `K + 1` (`ΓJ`); those
of `drainStep` at `K` except `old`, `new` at `2K + 1` and `tg` at `2K + 2` (`ΓT`).

Nothing here is used by Theorems A and B.
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model
open OrderMaintenance.Machine (Reg BinOp UnOp State)

variable {K KH W : Nat} {κ : Caps}

/-- The locals of a job step: the walk's threshold `pw` at width `K + 1`, every other at `K`. -/
abbrev ΓJ (K : Nat) : Reg → Nat := fun x => if x = "pw" then K + 1 else K
/-- The locals of `drainStep`: the tag fields `old`, `new` at width `2K + 1`, the new tag `tg` at
`2K + 2`, every other at `K`. -/
abbrev ΓT (K : Nat) : Reg → Nat := fun x =>
  if x = "old" ∨ x = "new" then 2 * K + 1 else if x = "tg" then 2 * K + 2 else K

/-- The locals of a drain start after its cut: the sums `t`, `ws` at width `K + 9`, every other
(including `b`, reassigned to a child) at `K`. -/
abbrev ΓD2 (K : Nat) : Reg → Nat := fun x => if x = "t" ∨ x = "ws" then K + 9 else K
/-- The locals of a split start: the new tags `ty`, `tz` (a label plus a digit) at width `K + 1`,
every other at `K`. -/
abbrev ΓS (K : Nat) : Reg → Nat := fun x => if x = "ty" ∨ x = "tz" then K + 1 else K

theorem ΓD2_le (K : Nat) : ∀ x, ΓD2 K x ≤ ΓD K x := by
  intro x; simp only [ΓD2, ΓD]
  by_cases h : x = "t" <;> by_cases h' : x = "ws" <;> by_cases h'' : x = "b" <;> simp [h, h', h'']
theorem ΓS_ge (K : Nat) : ∀ x, K ≤ ΓS K x := by intro x; simp only [ΓS]; split_ifs <;> omega

theorem ΓJ_ge (K : Nat) : ∀ x, K ≤ ΓJ K x := by intro x; simp only [ΓJ]; split <;> omega
theorem ΓT_ge (K : Nat) : ∀ x, K ≤ ΓT K x := by intro x; simp only [ΓT]; split_ifs <;> omega

/-- `proveSafe` with the locals of this file. -/
macro "jsafe" : tactic => `(tactic| (simp [Stm.Safe, Exp.OK, Exp.wq, Exp.vw, Exp.noShl, Fld.wd,
    Machine.BinOp.vw, Machine.BinOp.wd, Machine.UnOp.wd, Exp.maxShape, Exp.isCmp, Exp.isBool,
      Exp.monus, Exp.max,
    Exp.ifz, Exp.ar, Stm.war, Exp.sc, Stm.wsc, Exp.eF, Exp.gF, Exp.cF, Stm.weF, Stm.wgF,
      Stm.wcF, Proc.call,
    ΓK, ΓV, ΓM, ΓH, ΓR, ΓD, ΓJ, ΓT, ΓG, ΓD2, ΓS] <;>
    omega))

/-! ### Helpers -/

section helpers
variable {Γ : Reg → Nat} {s s' : Core} {L L' : Loc} {n : Nat}

/-- A statement that does not write `f` passes the bound of `f` back to its start. -/
theorem FB.back {c : Stm} {f : Fld} (hf : c.wf f = false) (h : evalF κ c s L = .ok s' L' n)
    (hb : FB K KH κ f s') : FB K KH κ f s := fun j hj => by
  rw [← evalF_frame_fld hf h hj]; exact hb j hj

theorem Fin.mono {Q Q' : Core → Prop} {c : Stm} (h : Fin (κ := κ) Q c s L) (hQ : ∀ t, Q t → Q' t) :
    Fin (κ := κ) Q' c s L := fun s' L' n e => hQ _ (h s' L' n e)

theorem FB.at' {f : Fld} {t : Core} (j : Nat) (h : FB K KH κ f t) : FBat K KH κ f j t := h j

theorem Gd.of_loc (hG : Gd K KH κ Γ s L) {Γ' : Reg → Nat} (h : ∀ x, L x < 2 ^ Γ' x) : Gd K KH κ
  Γ' s L :=
  ⟨hG.enc, hG.vb, h⟩

/-- A sequence whose rest does not write `f`: the first statement may assume the bound of `f`
at its own end. -/
theorem PKok.seq_fb {Γ' : Reg → Nat} {c d : Stm} {f : Fld} (hF : Fin (κ := κ) (FB K KH κ f) (c;;
  d) s L)
    (hd0 : d.wf f = false)
    (hc : Fin (κ := κ) (FB K KH κ f) c s L → PKok K KH κ Γ' W c s L)
    (hd : ∀ s1 L1 n1, evalF κ c s L = .ok s1 L1 n1 → Gd K KH κ Γ' s1 L1 → Fin (κ := κ) (FB K KH
      κ f) d s1 L1 →
      PKok K KH κ Γ W d s1 L1) :
    PKok K KH κ Γ W (c;; d) s L :=
  PKok.seq_fin hF (fun _ _ _ _ _ _ _ h2 hq => FB.back hd0 h2 hq) hc hd

/-- `pcSet` with known values below `2^K`. -/
theorem PK.pcSetV {t a b c d : Exp} {vs : List Nat} (hG : Gd K KH κ Γ s L)
    (hv : evList κ s L [t, a, b, c, d] = some vs) (hpk : pkList κ s L [t, a, b, c, d] < 2 ^ W)
    (hvs : ∀ v ∈ vs, v < 2 ^ K) : PK K KH κ Γ W (.pcSet t a b c d) s L := by
  intro hnb
  refine ⟨by simp only [pkF]; exact hpk, fun s' L' n h => ?_⟩
  have h' : evalF κ (.pcSet t a b c d) s L = .ok s' L' n := h
  cases hj : s.resJob with
  | none => simp [evalF, hj] at h
  | some jb =>
    rcases vs with _ | ⟨vt, _ | ⟨va, _ | ⟨vb, _ | ⟨vc, _ | ⟨vd, _ | ⟨_, _⟩⟩⟩⟩⟩⟩ <;>
      simp only [evalF, hj, hv] at h <;> try (cases h)
    split at h
    · next pc hpc =>
      cases h
      exact ⟨hG.enc.of_ok h', hG.vb.pcSet hj hpc (hvs _ (by simp)) (hvs _ (by simp)) (hvs _ (by
        simp))
        (hvs _ (by simp)) (hvs _ (by simp)), hG.loc⟩
    · cases h

/-- A call whose arguments have known values below `2^K`. -/
theorem PK.callV {q : Proc} {args : List Exp} {ds : List Reg} {vs : List Nat} {Γc Γe : Reg → Nat}
    (hG : Gd K KH κ Γ s L) (ha : evList κ s L args = some vs) (hpa : pkList κ s L args < 2 ^ W)
    (hvs : ∀ v ∈ vs, v < 2 ^ K) (hps : ∀ x, K ≤ Γe x)
    (hb : Gd K KH κ Γe s (State.setLocs (fun _ => 0) q.params vs) →
      PK K KH κ Γc W q.body s (State.setLocs (fun _ => 0) q.params vs))
    (hr : ∀ r ∈ q.rets, Γc r ≤ K) (hd : ∀ d ∈ ds, K ≤ Γ d) : PK K KH κ Γ W (q.call args ds) s L :=
  PK.call hG ha hpa (hb ⟨hG.enc, hG.vb, setLocs_lt (zero_locs _) (fun x _ => hps x) hvs⟩) hr hd

/-- A call (normal runs) whose callee may assume the call's end-state bound. -/
theorem PKok.callF {Γc Γe : Reg → Nat} {q : Proc} {args : List Exp} {ds : List Reg} {Q : Core →
  Prop}
    (hC : CapsW K κ) (hG : Gd K KH κ Γ s L)
    (ha : ∀ e ∈ args, e.OK Γ K KH W ∧ e.vw Γ K KH K ≤ K)
    (hps : ∀ x, K ≤ Γe x) (hF : Fin (κ := κ) Q (q.call args ds) s L)
    (hb : ∀ vs, evList κ s L args = some vs → Gd K KH κ Γe s (State.setLocs (fun _ => 0)
      q.params vs) →
      Fin (κ := κ) Q q.body s (State.setLocs (fun _ => 0) q.params vs) →
      PKok K KH κ Γc W q.body s (State.setLocs (fun _ => 0) q.params vs))
    (hr : ∀ r ∈ q.rets, Γc r ≤ K) (hd : ∀ d ∈ ds, K ≤ Γ d) : PKok K KH κ Γ W (q.call args ds) s L :=
  PKok.callS hC hG ha hps (fun vs hvs hG0 => hb vs hvs hG0 (hF.call hvs)) hr hd

/-- The value of a read of a field at the index held by a local. -/
theorem Exp.ev_rdv {f : Fld} {x : Reg} {w : Nat} (h : (Exp.rd f (.var x)).ev κ s L = some w) :
    L x < f.cap κ ∧ w = f.get s (L x) := by
  obtain ⟨j, hj, hjc, rfl⟩ := Exp.ev_rd_inv h
  have e : L x = j := Option.some.inj hj
  subst e; exact ⟨hjc, rfl⟩

end helpers

/-! ### `drainStep` -/

section ds
variable {s : Core} {L : Loc}
variable (hC : CapsW K κ) (hK : 8 ≤ K) (hW : 2 * K + 4 ≤ W)
include hC hK hW

omit hK hW in
/-- `e := 1 <<< (h' · β)` for a height `h' < H`: below `2^K`. -/
theorem shDigit_pk {Γ : Reg → Nat} {d : Stm} {x : Reg} {a : Exp} (hG : Gd K KH κ Γ s L)
    (hna : a.noShl = true) (hwa : (Exp.bin .shl 1 (a * .prm .beta)).wq Γ K KH K ≤ W)
    (hh : ∀ h', a.ev κ s L = some h' → h' < s.P.H) (hx : K ≤ Γ x)
    (hd : ∀ h', a.ev κ s L = some h' → Gd K KH κ Γ s (State.upd L x (2 ^ (h' * s.P.beta))) →
      PK K KH κ Γ W d s (State.upd L x (2 ^ (h' * s.P.beta)))) :
    PK K KH κ Γ W ((x ::= .bin .shl 1 (a * .prm .beta));; d) s L := by
  intro hnb
  cases ha : a.ev κ s L with
  | none => simp [evalF, Exp.ev, ha, Res.bind] at hnb
  | some h' =>
  have hR := hG.vb.room
  have hHb := hR.Hb
  have hb1 := hR.beta1
  have hH := hh h' ha
  have hle : h' * s.P.beta < K := by
    have h1 : (h' + 1) * s.P.beta ≤ (s.P.H + 1) * s.P.beta := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul] at h1; omega
  have hv : (Exp.bin .shl 1 (a * .prm .beta)).ev κ s L = some (2 ^ (h' * s.P.beta)) := by
    simp [Exp.ev, Machine.BinOp.eval, PF.get, ha]
  have hs : (Exp.bin .shl 1 (a * .prm .beta)).ShOK κ s L K :=
    ⟨trivial, Exp.shOK_of_noShl _ _ _ _ _ (by simp [Exp.noShl, hna]), fun _ => by
      simp [Exp.val, Exp.ev, Machine.BinOp.eval, PF.get, ha]; omega⟩
  refine PK.assign_seq hG hv (hG.pkS hC hs hv hwa) ?_ (hd h' ha) hnb
  exact lt_of_lt_of_le (Nat.pow_lt_pow_right (by norm_num) hle) (pow_le_pow' hx)

/-- **The labels and tag fields of a sweep step.** -/
theorem dsLab_pk (hG : Gd K KH κ (ΓT K) s L) : PK K KH κ (ΓT K) W dsLabS s L := by
  unfold dsLabS
  refine PK.seq_g (Γ' := ΓT K) (PK.of_safe hC (by omega) (by omega) (by jsafe) hG) (fun s1 L1 n1
    h1 hG1 => ?_)
  obtain ⟨c, hc, hc0, e1, e2⟩ := guard_ok' h1
  subst e1 e2
  have hH : L "h" < s.P.H := by
    simp [Exp.ev, Machine.BinOp.eval, PF.get] at hc
    by_contra hh; simp [hh] at hc; exact hc0 hc.symm
  refine PK.safe_seq' hC (by omega) (by omega) (by jsafe) hG (fun s2 L2 n2 h2 hG2 => ?_)
  refine PK.safe_seq' hC (by omega) (by omega) (by
    simp only [labS, lookupP, findP]
    jsafe) hG2
    (fun s3 L3 n3 h3 hG3 => ?_)
  refine PK.safe_seq' hC (by omega) (by omega) (by
    simp only [labS, lookupP, findP]
    jsafe) hG3
    (fun s4 L4 n4 h4 hG4 => ?_)
  refine PK.safe_seq' hC (by omega) (by omega) (by
    simp only [labS, lookupP, findP]
    jsafe) hG4
    (fun s5 L5 n5 h5 hG5 => ?_)
  refine PK.safe_seq' hC (by omega) (by omega) (by
    simp only [labS, lookupP, findP]
    jsafe) hG5
    (fun s6 L6 n6 h6 hG6 => ?_)
  have hh6 : L6 "h" = L "h" := by
    rw [evalF_frame_loc (by decide) h6, evalF_frame_loc (by decide) h5,
      evalF_frame_loc (by decide) h4,
      evalF_frame_loc (by decide) h3, evalF_frame_loc (by decide) h2]
  have hP6 : s6.P = s.P := by
    rw [evalF_P h6, evalF_P h5, evalF_P h4, evalF_P h3, evalF_P h2]
  refine shDigit_pk hC hG6 (a := "h") rfl (by jsafe)
    (fun h' e => by simp only [Exp.ev, Option.some.injEq] at e; rw [hP6, ← e, hh6]; exact hH)
    (by simp [ΓT]) (fun _ _ hG7 => ?_)
  refine shDigit_pk hC hG7 (a := Exp.var "h" - 1) rfl (by jsafe)
    (fun h' e => by
      simp [Exp.ev, Machine.BinOp.eval, Machine.State.upd,
        hh6] at e
      rw [hP6]; omega) (by simp [ΓT]) (fun _ _ hG8 => ?_)
  exact PK.of_safe hC (by omega) (by omega) (by jsafe) hG8

/-- **The tag of a sweep step**, bounded by the end state's tag at the moved chunk `y`. -/
theorem dsTag_pkok (hG : Gd K KH κ (ΓT K) s L) (hF : Fin (κ := κ) (FBat K KH κ (.c .tag) (L
  "y")) dsTagS s L) :
    PKok K KH κ (ΓT K) W dsTagS s L := by
  unfold dsTagS at hF ⊢
  refine PKok.safe_seq_fin hC (by omega) (by omega) (by jsafe) hG hF (fun s1 L1 n1 h1 hG1 hF1 => ?_)
  refine PKok.safe_seq_fin hC (by omega) (by omega) (by jsafe) hG1 hF1 (fun s2 L2 n2 h2 hG2 hF2
    => ?_)
  refine PKok.safe_seq_fin hC (by omega) (by omega) (by jsafe) hG2 hF2 (fun s3 L3 n3 h3 hG3 hF3
    => ?_)
  have hy : L3 "y" = L "y" := by
    rw [evalF_frame_loc (by decide) h3, evalF_frame_loc (by decide) h2,
      evalF_frame_loc (by decide) h1]
  have hyK : L3 "y" < 2 ^ K := by simpa [ΓT] using hG3.loc "y"
  have htg : L3 "tg" < 2 ^ (2 * K + 2) := by simpa [ΓT] using hG3.loc "tg"
  exact gstCall_pk hC hK hW hG3 (a := .var "y") (b := .var "tg") (by simp [Exp.ev]) (by
    simp [Exp.ev]) hyK htg
    (by simp only [Exp.pk]; exact pow_mono_lt hyK (by omega))
    (by simp only [Exp.pk]; exact pow_mono_lt htg (by omega)) (by
      rw [hy]
      exact hF3)

/-- **A sweep move** (`dsMoveS`), its tag bounded by the end state. -/
theorem dsMove_pkok (hG : Gd K KH κ (ΓT K) s L) (hF : Fin (κ := κ) (FB K KH κ (.c .tag)) dsMoveS
  s L) :
    PKok K KH κ (ΓT K) W dsMoveS s L := by
  unfold dsMoveS at hF ⊢
  refine PKok.safe_seq_fin hC (by omega) (by omega)
    (by
      simp only [dsPickS, belowS, dsLeftS, dsRightS, lookupP, findP]
      jsafe) hG hF
    (fun s1 L1 n1 h1 hG1 hF1 => ?_)
  refine PKok.seq (PK.ok (dsLab_pk hC hK hW hG1)) (fun s2 L2 n2 h2 hG2 => ?_)
  have hF2 := hF1.seq_right h2
  exact dsMut_fin (hF2.mono (fun t h => h.at' (L2 "y"))) (fun hT => dsTag_pkok hC hK hW hG2 hT)
    (fun s3 L3 n3 h3 hG3 => PK.ok (PK.of_safe hC (by omega) (by omega) (by
      simp only [dsRangeS, dsTgtS]
      jsafe) hG3))

/-- **`drainStep`**, its tag bounded by the end state. -/
theorem dsP_pkok (hG : Gd K KH κ (ΓT K) s L) (hL : ∀ x, L x < 2 ^ K)
    (hF : Fin (κ := κ) (FB K KH κ (.c .tag)) dsP.body s L) : PKok K KH κ (ΓT K) W dsP.body s L := by
  simp only [dsP] at hF ⊢
  refine PKok.ite_ok hC hG (by jsafe) (fun _ _ _ => PK.ok (PK.of_safe hC (by omega) (by
    omega) (by jsafe) hG))
    (fun hv => ?_)
  have hF1 := hF.ite_f hv
  refine PKok.safe_seq_fin hC (by omega) (by omega) (by jsafe) hG hF1 (fun s1 L1 n1 h1 hG1 hF2
    => ?_)
  obtain ⟨u, hu, e1, e2⟩ := evalF_assign_inv h1
  subst e1 e2
  have huK : u < 2 ^ K := by simpa [ΓT] using hG1.loc "h"
  have hL1 : ∀ x, Machine.State.upd L "h" u x < 2 ^ K := fun x => by
    by_cases hx : x = "h"
    · subst hx; rw [upd_eq]; exact huK
    · rw [upd_ne _ _ hx]; exact hL x
  refine PKok.ite_ok hC hG1 (by jsafe) (fun _ _ _ => ?_) (fun hv2 => ?_)
  · refine PKok.seq (Γ' := ΓK K) (PK.ok (finishDrain_pk hC hK hW (hG1.of_loc hL1))) (fun s3 L3
      n3 h3 hG3 => ?_)
    exact PK.ok (PK.of_safe hC (by omega) (by omega) (by jsafe) (hG3.mono (ΓT_ge K)))
  · have hF3 := (hF2.ite_f hv2).seq_assign (fun _ _ => rfl)
    exact PKok.seq (dsMove_pkok hC hK hW hG1 hF3)
      (fun s3 L3 n3 h3 hG3 => PK.ok (PK.of_safe hC (by omega) (by omega) (by jsafe) hG3))

/-- **The funding loop's step** (`fundS`, locals of a job step), the sweep's tag bounded by the
end state. -/
theorem fund_pkok (hG : Gd K KH κ (ΓJ K) s L) (hF : Fin (κ := κ) (FB K KH κ (.c .tag)) fundS s L) :
    PKok K KH κ (ΓJ K) W fundS s L := by
  unfold fundS at hF ⊢
  refine PKok.ite_ok hC hG (by jsafe) (fun c hc hc0 => ?_)
    (fun _ => PK.ok (PK.of_safe hC (by omega) (by omega) (by jsafe) hG))
  have hds : L "jd" < s.P.s := by
    simp [Exp.ev, Machine.BinOp.eval, PF.get] at hc
    by_contra hh; simp [hh] at hc; exact hc0 hc.symm
  have hF1 := hF.ite_t hc hc0
  refine PKok.seq_fb (Γ' := ΓJ K) hF1 (by decide) (fun hF2 => ?_) (fun s1 L1 n1 h1 hG1 _ => ?_)
  · refine PKok.callF (Γc := ΓT K) (Γe := ΓT K) hC hG (by jsafe) (ΓT_ge K) hF2 (fun vs hvs
      hG0 hF0 => ?_)
      (by simp [dsP, ΓT]) (by simp [ΓJ])
    refine dsP_pkok hC hK hW hG0 (fun x => ?_) hF0
    simp only [evList, List.mapM_cons, Exp.ev, List.mapM_nil, Option.pure_def,
        Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hvs
    subst hvs
    have hjc : L "jc" < 2 ^ K := by simpa [ΓJ] using hG.loc "jc"
    simp only [dsP, Machine.State.setLocs, Machine.State.upd]
    split
    · exact hjc
    · exact Nat.two_pow_pos _
  · have hjd : L1 "jd" = L "jd" := evalF_frame_loc (by decide) h1
    have hP1 : s1.P = s.P := evalF_P h1
    refine PKok.ite_ok hC hG1 (by jsafe) (fun _ _ _ => ?_)
      (fun _ => PK.ok (PK.of_safe hC (by omega) (by omega) (by jsafe) hG1))
    have hsK : s.P.s < 2 ^ K := by have := hG.vb.prm .s; simpa [PF.get] using this
    have hk : ∀ x, x ≠ "pw" → L1 x < 2 ^ K := fun x hx => by simpa [ΓJ, hx] using hG1.loc x
    have hev : evList κ s1 L1 [4, "ja", "jb", "jc", "jd" + 1] = some [4, L1 "ja", L1 "jb", L1
      "jc", L1 "jd" + 1] := by
      simp [evList, Exp.ev, Machine.BinOp.eval]
    refine PK.ok (PK.pcSetV hG1 hev ?_ ?_)
    · refine hG1.pkList hC (fun e he => ?_) hev
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl <;> jsafe
    · intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      · exact lt_pow_of_le (by norm_num) (by omega)
      · exact hk "ja" (by decide)
      · exact hk "jb" (by decide)
      · exact hk "jc" (by decide)
      · omega

end ds

end OrderMaintenance.Impl
