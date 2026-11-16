/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Word.PeakTop
public import LeanPool.OrderMaintenance.Proof.Word.TopWB
public import LeanPool.OrderMaintenance.Impl.PeakDrain
public import LeanPool.OrderMaintenance.Impl.GlueCore


/-!
# Theorem W, option (A), stage A2 spike: discharging the end-state bounds of `insertAfter`

The last-write rule (`PK.wr_fin`, `PKok.wr_fin_seq`) takes `Fin Q c s L`: every normal run of `c`
ends in a state satisfying `Q` (some field is small there). This file checks that option (B)
provides these bounds in the form stage A2 needs, for the top-level tree.

* **Where `Fin` comes from.** Option (B) bounds the end state of each *step* of the reservation:
  a job step (`jobStep_wb`, the `step` of `TopWB`) and a split start (the `start` of `TopWB`, then
  `wb_markState`). Theorem A's agreement lemmas (`jobAgree`, `splitAgree_top`) give the Level F run
  of `jobStepS` / `splitChunkStartS` ending in exactly that state, and `evalF` is a function, so
  `Fin (WB K)` holds for the whole step: `fin_jobStep`, `fin_split`.
* **From the step's end back to the write.** `Fin.call` (into a callee: its end state is the call's),
  `PKok.seq_fin` (the first statement may assume a bound of its own end state that follows from
  `Q` at the end of the rest, typically because the rest does not write the field), with the
  frames `FBat.back` (the rest writes no `f`) and `FBat.backAt` (the rest writes `f` only at the
  index held by a local). The syntactic side conditions for every top-level `Fin` site hold by
  `decide` (section *frames*).
* **The write.** `PK.wr_finAt`: `PK.wr_fin` for one index. `gst_pk`, `gstCall_pk`: the guarded tag
  write `guardedSetTag` (the tags of a sweep and of a split), its value of width up to `2K + 2`
  bounded by the end-state bound; `gstCall_frame`: the call writes the tag only at its first
  argument (for the split's first tag, which the second call does not overwrite).
* **Values bounded at the state before the step** (no `Fin` needed): the walk's `weight + 2` and
  height (`walk_lt`, from `walk_weight` and `Shape.htN`), so `powS` (`powS_pk`) needs only the new
  `PRoom.aH : log₂ a · H ≤ K`.
* `proom_wK`: `PRoom (wK P) P` for the proof parameters (with the new field).

Nothing here is used by Theorems A and B.
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model
open OrderMaintenance.Machine (Reg BinOp UnOp State)

variable {K KH W : Nat} {κ : Caps}

/-! ### `Fin` from a run, into a call, and back from the rest -/

section fin
variable {s s1 : Core} {L L1 : Loc} {Q Q' : Core → Prop}

/-- A normal run gives `Fin` of its end state (`evalF` is a function). -/
theorem Fin.of_run {c : Stm} {n1 : Nat} (h : evalF κ c s L = .ok s1 L1 n1) (hQ : Q s1) :
    Fin (κ := κ) Q c s L := fun s' L' n e => by
  rw [h] at e; injection e with e1; subst e1; exact hQ

/-- Into a call: the callee's end state is the call's. -/
theorem Fin.call {q : Proc} {args : List Exp} {ds : List Reg} {vs : List Nat}
    (h : Fin (κ := κ) Q (q.call args ds) s L) (ha : evList κ s L args = some vs) :
    Fin (κ := κ) Q q.body s (State.setLocs (fun _ => 0) q.params vs) := fun s' _ _ e =>
  h s' _ _ (evalF_call_ok ha e)

/-- **Sequencing with an end-state bound passed back**: the first statement may assume `Q'` of its
own end state, where `Q'` follows from `Q` at the end of the rest (e.g. the rest does not write
the field, `FBat.back`). -/
theorem PKok.seq_fin {Γ Γ' : Reg → Nat} {c d : Stm} (hF : Fin (κ := κ) Q (c;; d) s L)
    (hQ : ∀ s1 L1 n1 s' L' n, evalF κ c s L = .ok s1 L1 n1 → evalF κ d s1 L1 = .ok s' L' n → Q s' → Q' s1)
    (hc : Fin (κ := κ) Q' c s L → PKok K KH κ Γ' W c s L)
    (hd : ∀ s1 L1 n1, evalF κ c s L = .ok s1 L1 n1 → Gd K KH κ Γ' s1 L1 → Fin (κ := κ) Q d s1 L1 →
      PKok K KH κ Γ W d s1 L1) :
    PKok K KH κ Γ W (c;; d) s L := by
  intro sF LF nF h
  obtain ⟨s1, L1, n1, n2, h1, h2⟩ := evalF_seq_inv h
  have hc' := hc (Fin.of_run h1 (hQ _ _ _ _ _ _ h1 h2 (hF _ _ _ h)))
  exact PKok.seq hc' (fun s2 L2 n3 h3 hG2 => hd s2 L2 n3 h3 hG2 (hF.seq_right h3)) _ _ _ h

/-- A call whose callee may assume the call's end-state bound. -/
theorem PKok.call_fin {Γ Γc : Reg → Nat} {q : Proc} {args : List Exp} {ds : List Reg} {vs : List Nat}
    (hG : Gd K KH κ Γ s L) (ha : evList κ s L args = some vs) (hpa : pkList κ s L args < 2 ^ W)
    (hF : Fin (κ := κ) Q (q.call args ds) s L)
    (hb : Fin (κ := κ) Q q.body s (State.setLocs (fun _ => 0) q.params vs) →
      PKok K KH κ Γc W q.body s (State.setLocs (fun _ => 0) q.params vs))
    (hr : ∀ r ∈ q.rets, Γc r ≤ K) (hd : ∀ d ∈ ds, K ≤ Γ d) : PKok K KH κ Γ W (q.call args ds) s L :=
  PKok.call hG ha hpa (hb (hF.call ha)) hr hd

end fin

/-! ### One index of a field -/

/-- Field `f` of `t` is small at index `j`. -/
def FBat (K KH : Nat) (κ : Caps) (f : Fld) (j : Nat) (t : Core) : Prop :=
  j < f.cap κ → f.get t j < 2 ^ f.wd K KH

theorem FB.at {f : Fld} {t : Core} (h : FB K KH κ f t) (j : Nat) : FBat K KH κ f j t := h j

section frames
variable {s s' : Core} {L L' : Loc} {n : Nat}

/-- The rest does not write `f`: the bound at its end is the bound at its start. -/
theorem FBat.back {c : Stm} {f : Fld} {j : Nat} (hf : c.wf f = false) (h : evalF κ c s L = .ok s' L' n)
    (hb : FBat K KH κ f j s') : FBat K KH κ f j s := fun hj => by
  rw [← evalF_frame_fld hf h hj]; exact hb hj

/-- The rest writes `f` only at the index held by local `x`, and `j` is another one. -/
theorem FBat.backAt {c : Stm} {f : Fld} {x : Reg} {j : Nat} (hw : c.wfAt f x = true) (hx : c.asg x = false)
    (h : evalF κ c s L = .ok s' L' n) (hne : j ≠ L x) (hb : FBat K KH κ f j s') : FBat K KH κ f j s :=
  fun hj => by rw [← evalF_frame_fldAt hw hx h hj hne]; exact hb hj

end frames

/-- **The last write to index `j` of `f`** (`PK.wr_fin` for one index): its value is the end
state's. -/
theorem PK.wr_finAt (hC : CapsW K κ) {Γ : Reg → Nat} {s : Core} {L : Loc} {f : Fld} {i e : Exp} {j : Nat}
    (hG : Gd K KH κ Γ s L) (hi : i.OK Γ K KH W) (he : e.OK Γ K KH W) (hj : i.ev κ s L = some j)
    (hF : Fin (κ := κ) (FBat K KH κ f j) (.wr f i e) s L) : PK K KH κ Γ W (.wr f i e) s L := by
  intro hnb
  cases hv : e.ev κ s L with
  | none => simp [evalF, hj, hv] at hnb
  | some v =>
    refine ⟨max_lt (hG.pk hC hi hj) (hG.pk hC he hv), fun s' L' n h => ?_⟩
    obtain ⟨j', v', hj', hv', hset, rfl⟩ := evalF_wr_inv h
    rw [hj] at hj'; cases hj'; rw [hv] at hv'; cases hv'
    have hjc := Fld.set_cap hset hG.enc
    have h3 := hF _ _ _ h hjc
    rw [Fld.get_set hset f hjc, ite_eq_left ⟨rfl, rfl⟩] at h3
    exact ⟨hG.enc.of_ok h, hG.vb.set hset h3, hG.loc⟩

/-! ### The syntactic side conditions of the top-level `Fin` sites

The rest of the step after each write that takes its bound from the step's end state. -/

/-- The weights of a drain start's new nodes (`chS` at `u = v1`): the second `chS` writes the
weight only at `u = v2`, and neither the parent's children (`stage7S`), `v`'s fields (`stage8S`)
nor the job record (`pcSet`) write weights. -/
theorem frame_chS : chS.wfAt (.n .weight) "u" = true ∧ chS.asg "u" = false ∧
    stage7S.wf (.n .weight) = false ∧ stage8S.wf (.n .weight) = false ∧
    (Stm.pcSet 3 "wv" "up" 0 0).wf (.n .weight) = false ∧
    -- the indices `v1`, `v2` of the new nodes (`newNodesS`) are kept up to `stage56S`
    (insS;; stage3S;; stage4S).asg "v1" = false ∧ (insS;; stage3S;; stage4S).asg "v2" = false ∧
    chS.asg "v1" = false ∧ chS.asg "v2" = false := by decide

/-- The tag of a sweep (`dsTagS`): the rest of the move and of the job step write no tag. -/
theorem frame_dsTag : (Stm.pwr "y" "h" "t";; dsRangeS;; dsTgtS).wf (.c .tag) = false ∧
    (Stm.assign "ok" (.lit 1)).wf (.c .tag) = false ∧
    (Stm.pcSet 4 "ja" "jb" "jc" ("jd" + 1)).wf (.c .tag) = false := by decide

/-- The tags of a split: `guardedSetTag` writes only at its `c`; after the second tag nothing in
`insertAround` or `markSplit` writes a tag. -/
theorem frame_split : gstP.body.wfAt (.c .tag) "c" = true ∧ gstP.body.asg "c" = false ∧
    (cinsS;; "w" ::= .var "y";; joinCS;; "w" ::= .var "z";; joinCS;; childS).wf (.c .tag) = false ∧
    markSplitS.wf (.c .tag) = false := by decide

/-! ### `guardedSetTag` with its end-state bound -/

/-- The locals of `guardedSetTag`: the tag `t` may be wide (`2K + 2`, the sweep's
`ty - old + new`). -/
def ΓG (K : Nat) (x : Reg) : Nat := if x = "t" then 2 * K + 2 else K

section gst
variable {s : Core} {L : Loc}
variable (hC : CapsW K κ) (hK : 8 ≤ K) (hW : 2 * K + 4 ≤ W)
include hC hK hW

/-- `safe_tac` with the locals of `guardedSetTag`. -/
macro "gsafe" : tactic => `(tactic| (simp [Stm.Safe, Exp.OK, Exp.wq, Exp.vw, Exp.noShl, Fld.wd,
    OrderMaintenance.Machine.BinOp.vw, OrderMaintenance.Machine.BinOp.wd, OrderMaintenance.Machine.UnOp.wd, Exp.maxShape, Exp.isCmp, Exp.isBool, Exp.monus,
    Exp.max, Exp.ifz, Exp.cF, ΓG] <;> omega))

/-- **`guardedSetTag c t`**, the value `t` bounded by the end state's tag at `c`. -/
theorem gst_pk (hG : Gd K KH κ (ΓG K) s L)
    (hF : Fin (κ := κ) (FBat K KH κ (.c .tag) (L "c")) gstP.body s L) :
    PKok K KH κ (ΓG K) W gstP.body s L := by
  simp only [gstP] at hF ⊢
  refine PK.ok (PK.safe_seq' hC (by omega) (by omega) (by gsafe) hG (fun s1 L1 n1 h1 hG1 => ?_))
  have hF1 := hF.seq_right h1
  have hc1 : L1 "c" = L "c" := evalF_frame_loc (by decide) h1
  refine PK.safe_seq' hC (by omega) (by omega) (by gsafe) hG1 (fun s2 L2 n2 h2 hG2 => ?_)
  have hF2 := hF1.seq_right h2
  have hc2 : L2 "c" = L "c" := (evalF_frame_loc (by decide) h2).trans hc1
  refine PK.safe_seq' hC (by omega) (by omega) (by gsafe) hG2 (fun s3 L3 n3 h3 hG3 => ?_)
  have hF3 := hF2.seq_right h3
  have hc3 : L3 "c" = L "c" := (evalF_frame_loc (by decide) h3).trans hc2
  refine PK.safe_seq' hC (by omega) (by omega) (by gsafe) hG3 (fun s4 L4 n4 h4 hG4 => ?_)
  have hF4 := hF3.seq_right h4
  have hc4 : L4 "c" = L "c" := (evalF_frame_loc (by decide) h4).trans hc3
  have hc : (Exp.var "c").ev κ s4 L4 = some (L "c") := by simp [Exp.ev, hc4]
  exact PK.wr_finAt hC hG4 (by gsafe) (by gsafe) hc hF4

/-- **The call `guardedSetTag a b`**, its value of width at most `2K + 2`, bounded by the end
state's tag at index `a`. -/
theorem gstCall_pk {Γ : Reg → Nat} {a b : Exp} {ja vb : Nat} (hG : Gd K KH κ Γ s L)
    (ha : a.ev κ s L = some ja) (hb : b.ev κ s L = some vb) (hja : ja < 2 ^ K) (hvb : vb < 2 ^ (2 * K + 2))
    (hpa : a.pk κ s L < 2 ^ W) (hpb : b.pk κ s L < 2 ^ W)
    (hF : Fin (κ := κ) (FBat K KH κ (.c .tag) ja) (gstP.call [a, b] []) s L) :
    PKok K KH κ Γ W (gstP.call [a, b] []) s L := by
  have hev : evList κ s L [a, b] = some [ja, vb] := by simp [evList, ha, hb]
  have hpk : pkList κ s L [a, b] < 2 ^ W := by
    simp only [pkList, List.map, List.foldr]
    exact max_lt hpa (max_lt hpb (Nat.pos_of_ne_zero (by positivity)))
  refine PKok.call_fin (Γc := ΓG K) hG hev hpk hF (fun hF0 => ?_) (by simp [gstP]) (by simp)
  have hL0 : ∀ x, State.setLocs (fun _ => 0) gstP.params [ja, vb] x < 2 ^ ΓG K x := by
    intro x
    simp only [gstP, ΓG, OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd]
    by_cases h1 : x = "t"
    · subst h1; simp; exact hvb
    · by_cases h2 : x = "c"
      · subst h2; simp; exact hja
      · simp [h1, h2]
  have hc : State.setLocs (fun _ => 0) gstP.params [ja, vb] "c" = ja := by
    simp [gstP, OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd]
  exact gst_pk hC hK hW ⟨hG.enc, hG.vb, hL0⟩ (hc ▸ hF0)

end gst

/-- **The frame of `guardedSetTag a b`**: it writes the tag only at index `a`. -/
theorem gstCall_frame {s s' : Core} {L L' : Loc} {n : Nat} {a b : Exp} {ja : Nat}
    (h : evalF κ (gstP.call [a, b] []) s L = .ok s' L' n) (ha : a.ev κ s L = some ja) {j : Nat}
    (hj : j < κ.tbl .C) (hne : j ≠ ja) : (Fld.c .tag).get s' j = (Fld.c .tag).get s j := by
  cases hb : b.ev κ s L with
  | none => simp [Proc.call, evalF, evList, ha, hb] at h
  | some vb =>
    have hev : evList κ s L [a, b] = some [ja, vb] := by simp [evList, ha, hb]
    simp only [Proc.call, evalF, hev] at h
    revert h
    cases h2 : evalF κ gstP.body s (State.setLocs (fun _ => 0) gstP.params [ja, vb]) <;> simp
    intro e1 _ _; subst e1
    have hc : State.setLocs (fun _ => 0) gstP.params [ja, vb] "c" = ja := by
      simp [gstP, OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd]
    exact evalF_frame_fldAt frame_split.1 frame_split.2.1 h2 (f := .c .tag) (by simpa [Fld.cap] using hj)
      (by rw [hc]; exact hne)

/-- **The composition, at the sweep** (`dsMutS = dsTagS;; rest`): the rest writes no tag, so the
tag write may assume the bound that holds at the end of the move. -/
theorem dsMut_fin {Γ Γ' : Reg → Nat} {s : Core} {L : Loc} {j : Nat}
    (hF : Fin (κ := κ) (FBat K KH κ (.c .tag) j) dsMutS s L)
    (hT : Fin (κ := κ) (FBat K KH κ (.c .tag) j) dsTagS s L → PKok K KH κ Γ' W dsTagS s L)
    (hR : ∀ s1 L1 n1, evalF κ dsTagS s L = .ok s1 L1 n1 → Gd K KH κ Γ' s1 L1 →
      PKok K KH κ Γ W (Stm.pwr "y" "h" "t";; dsRangeS;; dsTgtS) s1 L1) :
    PKok K KH κ Γ W dsMutS s L := by
  unfold dsMutS at hF ⊢
  exact PKok.seq_fin hF (fun _ _ _ _ _ _ _ h2 hq => FBat.back frame_dsTag.1 h2 hq) hT
    (fun s1 L1 n1 h1 hG1 _ => hR s1 L1 n1 h1 hG1)

/-! ### `powS`: the walk's threshold `a ^ ht` -/

/-- **`pw := 1 <<< (log₂ a · ht)`**, given the height bound `ht ≤ H` of the walk node (`walk_lt`)
and `log₂ a · H ≤ K` (`PRoom.aH`). -/
theorem powS_pk {Γ : Reg → Nat} {s : Core} {L : Loc} (hC : CapsW K κ) (hW : 2 * K + 4 ≤ W)
    (hG : Gd K KH κ Γ s L) (hht : L "ht" ≤ s.P.H) (hΓ : Γ "ht" ≤ K) (hpw : K + 1 ≤ Γ "pw") :
    PK K KH κ Γ W powS s L := by
  have hR := hG.vb.room
  have hle : Nat.log2 s.P.a * L "ht" ≤ K := le_trans (Nat.mul_le_mul_left _ hht) hR.aH
  have hv : (Exp.bin .shl 1 (.un .msb (.prm .a) * "ht")).ev κ s L = some (1 * 2 ^ (Nat.log2 s.P.a * L "ht")) := by
    simp [Exp.ev, OrderMaintenance.Machine.BinOp.eval, OrderMaintenance.Machine.UnOp.eval, PF.get]
  have hs : (Exp.bin .shl 1 (.un .msb (.prm .a) * "ht")).ShOK κ s L K :=
    ⟨trivial, Exp.shOK_of_noShl _ _ _ _ _ (by simp [Exp.noShl]), fun _ => by
      simp [Exp.val, Exp.ev, OrderMaintenance.Machine.BinOp.eval,
        OrderMaintenance.Machine.UnOp.eval, PF.get]; exact hle⟩
  refine PK.assign hG hv (hG.pkS hC hs hv ?_) ?_
  · simp [Exp.wq, Exp.vw, OrderMaintenance.Machine.BinOp.vw, OrderMaintenance.Machine.BinOp.wd,
    OrderMaintenance.Machine.UnOp.wd,
      Exp.isCmp, Exp.isBool]
    omega
  · rw [one_mul]
    exact lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) hle) (Nat.pow_lt_pow_right (by norm_num) (by omega))

end OrderMaintenance.Impl

namespace OrderMaintenance.Proof.Word

open OrderMaintenance.Model OrderMaintenance.Proof OrderMaintenance.Proof.Top OrderMaintenance.Impl
open OrderMaintenance.Machine (Reg State)
variable {K KH : Nat} {κ : Caps}

/-! ### Option (B)'s bounds as `Fin` of the reservation's steps -/

/-- The node fields of a core with `WB` are below `2^K`. -/
theorem fld_n_of_WB {s : Core} (hW : WB K s) (hK : 3 ≤ K) (k : NF) (j : Nat) : (Fld.n k).get s j < 2 ^ K := by
  have hK1 : 1 ≤ K := by omega
  obtain ⟨h1, h2, h3', h4, h5, h6, h7, h8, -⟩ := hW.nodes j
  cases k <;> simp only [Fld.get, NF.get] <;> first | assumption | exact b2n_lt hK1 _

/-- The chunk fields of a core with `WB` are below `2^K`. -/
theorem fld_c_of_WB {s : Core} (hW : WB K s) (hK : 3 ≤ K) (k : CF) (j : Nat) : (Fld.c k).get s j < 2 ^ K := by
  have hK1 : 1 ≤ K := by omega
  have h3 : ∀ x : St, x.toN < 2 ^ K := fun x => small_lt hK (le_trans (St.toN_le x) (by norm_num))
  obtain ⟨h1, h2, h3', h4, h5, h6, h7, h8, h9⟩ := hW.C j
  cases k <;> simp only [Fld.get, CF.get] <;> first | assumption | exact b2n_lt hK1 _ | exact h3 _

theorem fbAt_n_of_WB {s : Core} (hW : WB K s) (hK : 3 ≤ K) (k : NF) (j : Nat) : FBat K KH κ (.n k) j s :=
  fun _ => by simpa [Fld.wd] using fld_n_of_WB hW hK k j

theorem fbAt_c_of_WB {s : Core} (hW : WB K s) (hK : 3 ≤ K) (k : CF) (j : Nat) : FBat K KH κ (.c k) j s :=
  fun _ => by simpa [Fld.wd] using fld_c_of_WB hW hK k j

theorem fld_g_of_WB {s : Core} (hW : WB K s) (hK : 3 ≤ K) (k : GF) (j : Nat) : (Fld.g k).get s j < 2 ^ K := by
  have hK1 : 1 ≤ K := by omega
  have h3 : ∀ x : St, x.toN < 2 ^ K := fun x => small_lt hK (le_trans (St.toN_le x) (by norm_num))
  obtain ⟨h1, h2, h3', h4, h5, h6, h7, h8, h9, h10⟩ := hW.Gs j
  cases k <;> simp only [Fld.get, GF.get] <;> first | assumption | exact b2n_lt hK1 _ | exact h3 _

theorem fld_s_of_WB {s : Core} (hW : WB K s) (hK : 3 ≤ K) (k : SF) (j : Nat) : (Fld.s k).get s j < 2 ^ K := by
  have hK1 : 1 ≤ K := by omega
  obtain ⟨h1, h2, h3', h4, h5, h6, h7, h8⟩ := hW.scalars
  cases k <;> simp only [Fld.get, SF.get] <;> first | assumption | exact b2n_lt hK1 _

/-- **The element insertion ends with small sizes** (`Fin` of `insertElem_pkok`): Theorem A's
`insertElem_agree` gives the run, option (B)'s `insertElem_wb` its end state's bound. -/
theorem fin_insertElem {s s' : Core} {x hh y : Nat} (hK : 3 ≤ K) (hrun : (insertElem x hh).run s = .ok y s')
    (hxE : x < s.E.size) (hgG : (s.E.getX x).grp < s.Gs.size)
    (hnE : (s.E.getX x).next = 0 ∨ (s.E.getX x).next < s.E.size) (hE : s.E.size < κ.tbl .E)
    (hG : s.Gs.size ≤ κ.tbl .G) (hW : WB K s) (hL : LabRoom K s.P) (hx : x < 2 ^ K) (hy : s.E.size < 2 ^ K)
    (hg : (s.Gs.getX (s.E.getX x).grp).size + 1 < 2 ^ K) (hc : s.count + 1 < 2 ^ K) :
    OrderMaintenance.Impl.Fin (κ := κ) (fun t => FB K KH κ (.g .size) t ∧ FB K KH κ (.s .count) t) insertElemP.body s
      (State.setLocs (fun _ => 0) ["x", "h"] [x, hh]) := by
  obtain ⟨L', n, e, -, -⟩ := insertElem_agree κ s (State.setLocs (fun _ => 0) ["x", "h"] [x, hh])
    (by simp [OrderMaintenance.Machine.State.setLocs,
      OrderMaintenance.Machine.State.upd]) (by simp [OrderMaintenance.Machine.State.setLocs,
      OrderMaintenance.Machine.State.upd]) hxE hgG hnE hE hG hrun
  obtain ⟨-, hW', -⟩ := insertElem_wb hW hL hrun hx hy hg hc
  exact OrderMaintenance.Impl.Fin.of_run e ⟨fun j _ => by simpa [Fld.wd] using fld_g_of_WB hW' hK .size j,
    fun j _ => by simpa [Fld.wd] using fld_s_of_WB hW' hK .count j⟩

/-- **A job step ends with small stored values** (`Fin (WB K)` of `jobStepS`, at the locals of
`jobP.call`): Theorem A's `jobAgree` gives the run, option (B)'s `jobStep_wb` its end state's
bound. The hypotheses are those `reservation_wb` and `reservationAgree_top` hold at each round. -/
theorem fin_jobStep {t t1 : Core} {job : Job} {r : Option Job} (hT : TopInv t) (hres : t.resJob = some job)
    (hpr : t.prep = none) (hpow : t.P.a = 2 ^ Nat.log2 t.P.a) (hTC : TopCaps κ t) (hW : WB K t)
    (hR : TopRoom K t.P) (hN : t.nodes.size + 2 ≤ 2 ^ K) (hC : t.C.size ≤ 2 ^ K)
    (hr : (jobStep job).run t = .ok r t1) (hT' : TopInv { t1 with resJob := r }) :
    OrderMaintenance.Impl.Fin (κ := κ) (WB K) jobStepS t (State.setLocs (fun _ => 0) [] []) := by
  obtain ⟨L', c, e, -⟩ := jobAgree hT hres hpr hpow hTC r t1 hr
  exact OrderMaintenance.Impl.Fin.of_run e (jobStep_wb hT hres hW hR hN hC hr hT')

/-- **A split start ends with small stored values** (the split branch of `reservation_wb`). -/
theorem split_wb {TI : Core → Prop} {μ : Core → Nat} (hT : TopWB K TI μ) {t t2 : Core} {A : Abs} {c : Nat}
    (hI : INV t A) (hTI : TI t) (hnone : t.resJob = none) (hcL : LiveC t c) (hcq : cSt t c = .quiet)
    (hroom : t.C.size + 2 ≤ 2 ^ K) (hW : WB K t) (hc : c < 2 ^ K)
    (hsc : (splitChunkStart c).run t = .ok () t2) (hTI2 : TI t2) : WB K t2 := by
  obtain ⟨job, s2, hj, rfl⟩ := splitChunkStart_dec hsc
  have hWl := wb_splitLink hW hc hroom
  obtain ⟨hW2, hJ, -⟩ := hT.start _ A c job s2 hI hTI hnone hcL hcq hroom hWl hj hTI2
  exact wb_markState hW2 hc (by omega) (by omega) hJ

/-- **`Fin (WB K)` of `splitChunkStartS`** (at the locals of `splitP.call`), from Theorem A's
`splitAgree_top` and `split_wb`. -/
theorem fin_split {TI : Core → Prop} {μ : Core → Nat} (hT : TopWB K TI μ) (hTI' : ∀ u, TI u → TopInv u)
    {t t2 : Core} {A : Abs} {c : Nat}
    (hI : INV t A) (hTI : TI t) (hnone : t.resJob = none) (hcL : LiveC t c) (hcq : cSt t c = .quiet)
    (hpr : t.prep = none) (hrow : ∀ c, t.C.size ≤ c → ∀ j, (t.path.getX c).getX j = 0) (hTC : TopCaps κ t)
    (hroom : t.C.size + 2 ≤ 2 ^ K) (hW : WB K t) (hc : c < 2 ^ K)
    (hsc : (splitChunkStart c).run t = .ok () t2) (hTI2 : TI t2) :
    OrderMaintenance.Impl.Fin (κ := κ) (WB K) splitChunkStartS t (State.setLocs (fun _ => 0) ["x"] [c]) := by
  obtain ⟨D, -, hA⟩ := splitAgree_top hI (hTI' t hTI) hnone hcL hpr hrow hTC
  obtain ⟨L', n, e, -⟩ := hA t2 hsc
  exact OrderMaintenance.Impl.Fin.of_run e (split_wb hT hI hTI hnone hcL hcq hroom hW hc hsc hTI2)

/-! ### The walk: bounds at the state before the step -/

/-- **The walk node** (`wv` of `walkS`: the job's node, or the leaf parent of `y` for a fresh walk):
its `weight + 2` is below `2^K` (option (B)'s `walk_weight`, the chunk count bounding the true
weight) and its height is at most `H` (`Shape.htN`), at the state before the step. -/
theorem walk_lt {s : Core} {job : Job} (hT : TopInv s) (hres : s.resJob = some job) {v : Nat}
    (hv : job.pc = .walk (some v) ∨ (job.pc = .walk none ∧ v = s.lpar.getX job.y)) (hv0 : v ≠ NIL)
    (hC : s.C.size ≤ 2 ^ K) :
    (s.nodes.getX v).weight + 2 < 2 ^ K ∧ (s.nodes.getX v).height ≤ s.P.H := by
  obtain ⟨-, cl, ord, dr, n0, hL, hCl, hI⟩ := hT
  rw [hres] at hI
  have hcl : CLok s cl := ⟨hL, hCl⟩
  -- the walk at `v`, in the form of `walk_weight`
  obtain ⟨j, hpc, hIj⟩ : ∃ j : Job, j.pc = .walk (some v) ∧ InvJ (ts s) cl ord dr n0 (some j) := by
    rcases hv with hpc | ⟨hpc, rfl⟩
    · have hfin : finS (ts s) (some job) = ts s := by simp only [finS, hpc]
      rw [hfin] at hI
      exact ⟨job, hpc, hI⟩
    · have hfin : finS (ts s) (some job) = ts s := by simp only [finS, hpc]
      rw [hfin] at hI
      exact ⟨_, rfl, (walkNone_inv hpc hI).1⟩
  have S := hIj.shape
  have hlen := CLok.len hcl (S.ord0 ▸ S.ordNodup 0)
  have hww := walk_weight hpc hv0 hIj
  have hvl := walk_live hpc hv0 hIj
  refine ⟨by omega, ?_⟩
  exact (S.htN v hvl.1).2

/-! ### The new `PRoom` field at the candidate word size -/

/-- **`PRoom` at `wK = 64·L`** for the proof parameters, including `log₂ a · H ≤ K` (`a = 8`,
`H = L/3 + 1`: `3·(L/3 + 1) ≤ 64·L`). -/
theorem proom_wK (N : Nat) : PRoom (wK (proofParams N)) (proofParams N) := by
  obtain ⟨hBe, hBg, hHb, -, -, -⟩ := params_room N
  have hL := pL_ge N
  have hK : wK (proofParams N) = 64 * pL N := rfl
  have hb : (proofParams N).beta = 64 := rfl
  have hH : (proofParams N).H = pL N / 3 + 1 := rfl
  have ha : (proofParams N).a = 8 := rfl
  have hBe1 : 1 ≤ (proofParams N).elementBits := by show 1 ≤ _ + (Nat.log2 _ + 2); omega
  have hBg1 : 1 ≤ (proofParams N).groupBits := by show 1 ≤ _ + (Nat.log2 _ + 2); omega
  have hlog : Nat.log2 8 = 3 := by decide
  refine ⟨by omega, by omega, by rw [hb, hK]; omega, by rw [hb, hK]; omega, ?_, hBe1, hBg1,
    by rw [hb]; omega, ?_⟩
  · have : ((proofParams N).H + 1) * (proofParams N).beta ≤ ((proofParams N).H + 2) * (proofParams N).beta :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  · rw [ha, hlog, hH, hK]; omega

end OrderMaintenance.Proof.Word
