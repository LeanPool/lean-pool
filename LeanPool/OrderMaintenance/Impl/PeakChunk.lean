/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.PeakDrive


/-!
# Theorem W, option (A), stage A2: the peak of a chunk split step

The labels of the moved unit (`labLS`, `labRS`: the guarded `afterS`, the centre label), and the
sizes (`msS`): the chunk sizes it writes are the ones the step ends with, so their bound comes
from the stored-value bound of the step's end state (`VB`, from option (B)), and so does the
moved size `mv` (at most the receiving chunk's new size).

Nothing here is used by Theorems A and B.
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model
open OrderMaintenance.Machine (Reg BinOp UnOp State)

variable {K KH W : Nat} {κ : Caps}

/-- The values of field `f` are small. -/
def FB (K KH : Nat) (κ : Caps) (f : Fld) (s : Core) : Prop := ∀ j, j < f.cap κ → f.get s j < 2 ^ f.wd K KH

/-- The end state of every normal run of `c` from `(s, L)` satisfies `Q` (in use: some fields of
it are small, `FB`). -/
def Fin (Q : Core → Prop) (c : Stm) (s : Core) (L : Loc) : Prop :=
  ∀ s' L' n, evalF κ c s L = .ok s' L' n → Q s'

section fin
variable {s s1 : Core} {L L1 : Loc} {Q : Core → Prop}

theorem Fin.seq_right {c d : Stm} {n1 : Nat} (h : Fin (κ := κ) Q (c;; d) s L) (h1 : evalF κ c s L = .ok s1 L1 n1) :
    Fin (κ := κ) Q d s1 L1 := fun s' L' n e => h s' L' (n1 + n) (by rw [evalF_seq_ok h1, e]; rfl)

theorem Fin.seq_assign {c : Stm} {x : Reg} {e : Exp} {v : Nat} (h : Fin (κ := κ) Q (c;; (x ::= e)) s L)
    (he : ∀ s' L', e.ev κ s' L' = some v) : Fin (κ := κ) Q c s L := fun s' L' n e1 =>
  h s' _ _ (by rw [evalF_seq_ok e1]; simp [evalF, he]; rfl)

theorem Fin.ite_t {c : Exp} {t f : Stm} {v : Nat} (h : Fin (κ := κ) Q (.ite c t f) s L) (hv : c.ev κ s L = some v)
    (h0 : v ≠ 0) : Fin (κ := κ) Q t s L := fun s' L' n e =>
  h s' L' _ (by simp only [evalF, hv, ite_eq_left h0, e]; rfl)

theorem Fin.ite_f {c : Exp} {t f : Stm} (h : Fin (κ := κ) Q (.ite c t f) s L) (hv : c.ev κ s L = some 0) :
    Fin (κ := κ) Q f s L := fun s' L' n e =>
  h s' L' _ (by simp only [evalF, hv, ne_eq, not_true_eq_false, ite_false, e]; rfl)

end fin

section finrules
variable {s : Core} {L : Loc} {Γ : Reg → Nat} {Q : Core → Prop}

theorem Fld.set_cap {f : Fld} {j v : Nat} {s' : Core} (h : f.set κ s j v = some s') (hE : EncOK κ s) :
    j < f.cap κ := by
  cases f with
  | e k => simp only [Fld.set] at h; split at h <;> simp at h; have := hE.sle .E; simp [Tbl.size] at this
           simp only [Fld.cap]; omega
  | g k => simp only [Fld.set] at h; split at h <;> simp at h; have := hE.sle .G; simp [Tbl.size] at this
           simp only [Fld.cap]; omega
  | c k => simp only [Fld.set] at h; split at h <;> simp at h; have := hE.sle .C; simp [Tbl.size] at this
           simp only [Fld.cap]; omega
  | n k => simp only [Fld.set] at h; split at h <;> simp at h; have := hE.sle .N; simp [Tbl.size] at this
           simp only [Fld.cap]; omega
  | a k => simp only [Fld.set] at h; split at h <;> simp at h; simp only [Fld.cap]; assumption
  | s k => simp only [Fld.set] at h; split at h <;> simp at h; simp only [Fld.cap]; omega

/-- A safe first statement, the end-state bound passed on. -/
theorem PKok.safe_seq_fin {c d : Stm} (hC : CapsW K κ) (hK : 3 ≤ K) (hW : K ≤ W) (hS : c.Safe K KH Γ W)
    (hG : Gd K KH κ Γ s L) (hF : Fin (κ := κ) Q (c;; d) s L)
    (hd : ∀ s1 L1 n1, evalF κ c s L = .ok s1 L1 n1 → Gd K KH κ Γ s1 L1 → Fin (κ := κ) Q d s1 L1 →
      PKok K KH κ Γ W d s1 L1) : PKok K KH κ Γ W (c;; d) s L :=
  PKok.seq (PK.ok (PK.of_safe hC hK hW hS hG)) (fun s1 L1 n1 h1 hG1 => hd s1 L1 n1 h1 hG1 (hF.seq_right h1))

/-- **A write that the rest never overwrites** (`d` does not write field `f`): its value is the end
state's. -/
theorem PKok.wr_fin_seq (hC : CapsW K κ) {f : Fld} {i e : Exp} {d : Stm} (hG : Gd K KH κ Γ s L)
    (hi : i.OK Γ K KH W) (he : e.OK Γ K KH W) (hd : d.wf f = false)
    (hQ : ∀ t, Q t → FB K KH κ f t) (hF : Fin (κ := κ) Q (.wr f i e;; d) s L)
    (hD : ∀ s1, Gd K KH κ Γ s1 L → Fin (κ := κ) Q d s1 L → PKok K KH κ Γ W d s1 L) :
    PKok K KH κ Γ W (.wr f i e;; d) s L := by
  intro sF LF nF h
  obtain ⟨s1, L1, n1, n2, h1, h2⟩ := evalF_seq_inv h
  obtain ⟨j, v, hj, hv, hset, rfl⟩ := evalF_wr_inv h1
  have hjc : j < f.cap κ := Fld.set_cap hset hG.enc
  have hval : v < 2 ^ f.wd K KH := by
    have h3 := hQ _ (hF _ _ _ h) j hjc
    rw [evalF_frame_fld hd h2 hjc, Fld.get_set hset f hjc, ite_eq_left ⟨rfl, rfl⟩] at h3
    exact h3
  have hW1 := PK.wr hG hj hv (hG.pk hC hi hj) (hG.pk hC he hv) hval
  exact (PKok.seq (PK.ok hW1) (fun s2 L2 n3 h3 hG2 => by
    obtain ⟨-, -, -, -, -, e⟩ := evalF_wr_inv h3; subst e; exact hD s2 hG2 (hF.seq_right h3))) _ _ _ h

end finrules

section chunk
variable {s : Core} {L : Loc}
variable (hC : CapsW K κ) (hK : 8 ≤ K) (hW : 2 * K + 4 ≤ W)
include hC hK hW

/-- `a := e`, `afterS`, then the rest (with `B` unchanged). -/
theorem aAfter_pk {e : Exp} {rest : Stm} (hG : Gd K KH κ (ΓV K) s L) (hB : L "B" ≤ K)
    (he : e.OK (ΓV K) K KH W) (hew : e.vw (ΓV K) K KH K ≤ K)
    (hr : ∀ s' L', Gd K KH κ (ΓV K) s' L' → L' "B" = L "B" → PK K KH κ (ΓV K) W rest s' L') :
    PK K KH κ (ΓV K) W ("a" ::= e;; afterS;; rest) s L := by
  refine PK.safe_seq' hC (by omega) (by omega) ⟨he, by simpa [ΓV] using hew⟩ hG (fun s1 L1 n1 h1 hG1 => ?_)
  have hB1 : L1 "B" = L "B" := evalF_frame_loc (by simp [Stm.asg]) h1
  have hA := afterS_pk hC hK hW hG1 (by rw [hB1]; exact hB) (gd_a hC hK hW hG1 _ (by decide))
    (gd_a hC hK hW hG1 _ (by decide))
  exact PK.seq hA (fun s2 L2 n2 h2 => hr _ _ (hA.post h2) (by rw [evalF_frame_loc (by decide) h2, hB1]))

theorem labLS_pk (hG : Gd K KH κ (ΓV K) s L) : PK K KH κ (ΓV K) W labLS s L := by
  unfold labLS centreG
  refine PK.safe_seq' hC (by omega) (by omega) (by safe_tac) hG (fun s1 L1 n1 h1 hG1 => ?_)
  have hP : s1.P = s.P := evalF_P h1
  refine PK.safe_assign_seq hC hG1 (by safe_tac) (by safe_tac) (v := PF.Bg.get s1.P) rfl (fun hG2 => ?_)
  have hB : OrderMaintenance.Machine.State.upd L1 "B" (PF.Bg.get s1.P) "B" ≤ K := by
    rw [upd_eq, hP]; exact hG.vb.room.Bg
  refine PK.seq_g (PK.ite_ok hG2 hC (by safe_tac)
      (fun _ _ _ => centre_pk hC hK hW hG2 (k := .Bg) (by rw [hP]; exact hG.vb.room.Bg) (by simp [ΓV]))
      (fun _ => aAfter_pk hC hK hW hG2 hB (by safe_tac) (by safe_tac)
        (fun s' L' hG' _ => PK.of_safe hC (by omega) (by omega) (by safe_tac) hG')))
    (fun s3 L3 n3 h3 hG3 => ?_)
  have hB3 : L3 "B" ≤ K := by rw [evalF_frame_loc (by decide) h3]; exact hB
  refine PK.ite_ok hG3 hC (by safe_tac) (fun _ _ _ => ?_) (fun _ => PK.skip hG3)
  refine aAfter_pk hC hK hW hG3 hB3 (by safe_tac) (by safe_tac) (fun s4 L4 hG4 hB4 => ?_)
  refine PK.safe_seq' hC (by omega) (by omega) (by safe_tac) hG4 (fun s5 L5 n5 h5 hG5 => ?_)
  have hB5 : L5 "B" ≤ K := by rw [evalF_frame_loc (by decide) h5, hB4]; exact hB3
  exact aAfter_pk hC hK hW hG5 hB5 (by safe_tac) (by safe_tac)
    (fun s' L' hG' _ => PK.of_safe hC (by omega) (by omega) (by safe_tac) hG')

theorem labRS_pk (hG : Gd K KH κ (ΓV K) s L) : PK K KH κ (ΓV K) W labRS s L := by
  unfold labRS centreG
  refine PK.safe_seq' hC (by omega) (by omega) (by safe_tac) hG (fun s1 L1 n1 h1 hG1 => ?_)
  have hP : s1.P = s.P := evalF_P h1
  refine PK.seq_g (PK.ite_ok hG1 hC (by safe_tac)
    (fun _ _ _ => centre_pk hC hK hW hG1 (k := .Bg) (by rw [hP]; exact hG.vb.room.Bg) (by simp [ΓV]))
    (fun _ => PK.of_safe hC (by omega) (by omega) (by simp only [beforeS]; safe_tac) hG1))
    (fun s2 L2 n2 h2 hG2 => PK.of_safe hC (by omega) (by omega) (by simp only [beforeS]; safe_tac) hG2)

end chunk

theorem Exp.ev_add_inv {a b : Exp} {s : Core} {L : Loc} {w : Nat} (h : (Exp.bin .add a b).ev κ s L = some w) :
    ∃ x y, a.ev κ s L = some x ∧ b.ev κ s L = some y ∧ w = x + y := by
  simp only [Exp.ev, Option.bind_eq_some_iff, OrderMaintenance.Machine.BinOp.eval,
    Option.some.injEq] at h
  obtain ⟨x, hx, y, hy, rfl⟩ := h; exact ⟨x, y, hx, hy, rfl⟩

section chunk2
variable {s : Core} {L : Loc}
variable (hC : CapsW K κ) (hK : 8 ≤ K) (hW : 2 * K + 4 ≤ W)
include hC hK hW

theorem PKok.ite_ok {Γ : Reg → Nat} {c : Exp} {t f : Stm} (hG : Gd K KH κ Γ s L) (hc : c.OK Γ K KH W)
    (ht : ∀ v, c.ev κ s L = some v → v ≠ 0 → PKok K KH κ Γ W t s L)
    (hf : c.ev κ s L = some 0 → PKok K KH κ Γ W f s L) : PKok K KH κ Γ W (.ite c t f) s L := by
  intro s' L' n h
  cases hv : c.ev κ s L with
  | none => simp [evalF, hv] at h
  | some v => exact PKok.ite hv (hG.pk hC hc hv) (ht v hv) (fun h0 => hf (h0 ▸ hv)) _ _ _ h

/-- A call (normal runs), arguments of width `K`. -/
theorem PKok.callS {Γ Γc Γe : Reg → Nat} {q : Proc} {args : List Exp} {ds : List Reg}
    (hG : Gd K KH κ Γ s L) (ha : ∀ e ∈ args, e.OK Γ K KH W ∧ e.vw Γ K KH K ≤ K) (hps : ∀ x, K ≤ Γe x)
    (hb : ∀ vs, evList κ s L args = some vs → Gd K KH κ Γe s (OrderMaintenance.Machine.State.setLocs (fun _ => 0) q.params vs) →
      PKok K KH κ Γc W q.body s (OrderMaintenance.Machine.State.setLocs (fun _ => 0) q.params vs))
    (hr : ∀ r ∈ q.rets, Γc r ≤ K) (hd : ∀ d ∈ ds, K ≤ Γ d) : PKok K KH κ Γ W (q.call args ds) s L := by
  intro s' L' n h
  cases hv : evList κ s L args with
  | none => simp [Proc.call, evalF, hv] at h
  | some vs =>
    have hG0 : Gd K KH κ Γe s (OrderMaintenance.Machine.State.setLocs (fun _ => 0) q.params vs) :=
      ⟨hG.enc, hG.vb, setLocs_lt (zero_locs _) (fun x _ => hps x) (hG.vals hC ha hv)⟩
    exact PKok.call hG hv (hG.pkList hC (fun e he => (ha e he).1) hv) (hb vs hv hG0) hr hd _ _ _ h

/-- A write whose end state has small stored values (`Fin`): its value needs no bound. -/
theorem PK.wr_fin {Γ : Reg → Nat} {Q : Core → Prop} {f : Fld} {i e : Exp} (hG : Gd K KH κ Γ s L)
    (hi : i.OK Γ K KH W) (he : e.OK Γ K KH W) (hQ : ∀ t, Q t → FB K KH κ f t)
    (hF : Fin (κ := κ) Q (.wr f i e) s L) : PK K KH κ Γ W (.wr f i e) s L := by
  intro hnb
  cases hj : i.ev κ s L with
  | none => simp [evalF, hj] at hnb
  | some j =>
    cases hv : e.ev κ s L with
    | none => simp [evalF, hj, hv] at hnb
    | some v =>
      refine ⟨max_lt (hG.pk hC hi hj) (hG.pk hC he hv), fun s' L' n h => ?_⟩
      obtain ⟨j', v', hj', hv', hset, rfl⟩ := evalF_wr_inv h
      rw [hj] at hj'; cases hj'; rw [hv] at hv'; cases hv'
      have hjc := Fld.set_cap hset hG.enc
      have h3 := hQ _ (hF _ _ _ h) j hjc
      rw [Fld.get_set hset f hjc, ite_eq_left ⟨rfl, rfl⟩] at h3
      exact ⟨hG.enc.of_ok h, hG.vb.set hset h3, hG.loc⟩

omit hC hK hW in
theorem ΓV_le_ΓM (K : Nat) : ∀ x, ΓV K x ≤ ΓM K x := by
  intro x; simp only [ΓV, ΓM]; split_ifs <;> omega

theorem msMv_pk (hG : Gd K KH κ (ΓM K) s L) : PK K KH κ (ΓM K) W msMv s L := by
  unfold msMv
  intro hnb
  cases hv : (Exp.gF .size "u0").ev κ s L with
  | none => simp [evalF, hv, Res.bind] at hnb
  | some v0 =>
    have hv0 : v0 < 2 ^ K := hG.valN hC rfl (by safe_tac) hv
    refine PK.assign_seq hG hv (hG.pk hC (by safe_tac) hv) (by simp [ΓM]; exact pow_mono_lt hv0 (by omega))
      (fun hG1 => PK.ite_ok hG1 hC (by safe_tac) (fun _ _ _ => ?_) (fun _ => PK.skip hG1)) hnb
    have hval : ∀ w, (("mv" : Exp) + Exp.gF .size "u1" + Exp.gF .size "u2").ev κ s
        (OrderMaintenance.Machine.State.upd L "mv" v0) = some w → w < 2 ^ (K + 2) := by
      intro w hw
      obtain ⟨a, b, ha, hb, rfl⟩ := Exp.ev_add_inv (by simpa [Exp.add_def] using hw)
      obtain ⟨a1, a2, ha1, ha2, rfl⟩ := Exp.ev_add_inv ha
      simp only [Exp.ev, Option.some.injEq, upd_eq] at ha1; subst ha1
      have h1 := hG1.valN hC rfl (w := K) (by safe_tac) ha2
      have h2 := hG1.valN hC rfl (w := K) (by safe_tac) hb
      have : 2 ^ (K + 2) = 4 * 2 ^ K := by rw [pow_add]; ring
      omega
    intro hnb2
    cases hw : (("mv" : Exp) + Exp.gF .size "u1" + Exp.gF .size "u2").ev κ s (OrderMaintenance.Machine.State.upd L "mv" v0) with
    | none => simp only [Exp.add_def] at hw; simp [evalF, hw] at hnb2
    | some w =>
      exact PK.assign hG1 hw (hG1.pk hC (by safe_tac) hw) (by simpa [ΓM] using hval w hw) hnb2

/-- **The sizes of a chunk move**: the receiving chunk's size is the one the step ends with. -/
theorem msS_pk (hG : Gd K KH κ (ΓM K) s L) (hF : Fin (κ := κ) (FB K KH κ (.c .size)) msS s L) : PK K KH κ (ΓM K) W msS s L := by
  have hM := msMv_pk hC hK hW hG
  unfold msS
  refine PK.seq_g hM (fun s1 L1 n1 h1 hG1 => ?_)
  have hF1 := Fin.seq_right hF h1
  -- `size x := monus (size x) mv` is at most the old size
  have hx : PK K KH κ (ΓM K) W (.wcF .size "x" (Exp.monus (.cF .size "x") "mv")) s1 L1 := by
    intro hnb
    cases hv : (Exp.monus (.cF .size "x") "mv").ev κ s1 L1 with
    | none => simp [evalF, Stm.wcF, hv] at hnb
    | some v =>
      obtain ⟨a, ha, hva⟩ := Exp.ev_monus_le hv
      have := hG1.valN hC rfl (w := K) (by safe_tac) ha
      exact PK.wr (j := L1 "x") hG1 rfl hv (hG1.pk hC (by safe_tac) (show (Exp.var "x").ev κ s1 L1 = some (L1 "x") from rfl))
        (hG1.pk hC (by safe_tac) hv) (by simpa [Fld.wd] using lt_of_le_of_lt hva this) hnb
  exact PK.seq_g hx (fun s2 L2 n2 h2 hG2 => PK.wr_fin hC hK hW hG2 (by safe_tac) (by safe_tac) (fun _ h => h)
    (Fin.seq_right hF1 h2))

end chunk2

section chunk3
variable {s : Core} {L : Loc}
variable (hC : CapsW K κ) (hK : 8 ≤ K) (hW : 2 * K + 4 ≤ W)
include hC hK hW

theorem cssL_pk (hG : Gd K KH κ (ΓV K) s L) : PK K KH κ (ΓV K) W cssL s L := by
  unfold cssL
  refine PK.safe_seq' hC (by omega) (by omega) (by safe_tac) hG (fun s1 L1 n1 h1 hG1 => ?_)
  exact PK.seq_g (labLS_pk hC hK hW hG1) (fun _ _ _ _ hG2 => PK.of_safe hC (by omega) (by omega)
    (by simp only [mgLS, ulS, mgLx, mgLy, mgGS, mgPair]; safe_tac) hG2)

theorem cssR_pk (hG : Gd K KH κ (ΓV K) s L) : PK K KH κ (ΓV K) W cssR s L := by
  unfold cssR
  refine PK.safe_seq' hC (by omega) (by omega) (by safe_tac) hG (fun s1 L1 n1 h1 hG1 => ?_)
  exact PK.seq_g (labRS_pk hC hK hW hG1) (fun _ _ _ _ hG2 => PK.of_safe hC (by omega) (by omega)
    (by simp only [mgRS, ulS, mgRx, mgRy, mgGS, mgPair]; safe_tac) hG2)

theorem cssMove_pk (hG : Gd K KH κ (ΓV K) s L) (hF : Fin (κ := κ) (FB K KH κ (.c .size)) cssMove s L) : PK K KH κ (ΓM K) W cssMove s L := by
  unfold cssMove
  refine PK.safe_seq (Γ := ΓV K) hC (by omega) (by omega) (by simp only [cssDirE]; safe_tac) hG
    (fun s1 L1 n1 h1 hG1 => ?_)
  refine PK.safe_seq (Γ := ΓV K) hC (by omega) (by omega) (by simp only [unitS, unitLE, unitRE]; safe_tac) hG1
    (fun s2 L2 n2 h2 hG2 => ?_)
  have hF2 := Fin.seq_right (Fin.seq_right hF h1) h2
  refine PK.seq_g (Γ' := ΓV K) (PK.ite_ok hG2 hC (by safe_tac) (fun _ _ _ => cssL_pk hC hK hW hG2)
    (fun _ => cssR_pk hC hK hW hG2)) (fun s3 L3 n3 h3 hG3 => ?_)
  exact msS_pk hC hK hW (hG3.mono (ΓV_le_ΓM K)) (Fin.seq_right hF2 h3)

/-- **A chunk split step**, given that its end state has small stored values. -/
theorem chunkSplitStep_pk (hG : Gd K KH κ (ΓK K) s L) (hF : Fin (κ := κ) (FB K KH κ (.c .size)) chunkSplitStepS s L) :
    PK K KH κ (ΓM K) W chunkSplitStepS s L := by
  unfold chunkSplitStepS
  refine PK.safe_seq (Γ := ΓK K) hC (by omega) (by omega) (by safe_tac) hG (fun s1 L1 n1 h1 hG1 => ?_)
  have hF1 := Fin.seq_right hF h1
  have hKM : ∀ x, ΓK K x ≤ ΓM K x := fun x => le_trans (ΓK_le_ΓV K x) (ΓV_le_ΓM K x)
  refine PK.ite_ok (hG1.mono hKM) hC (by safe_tac) (fun _ _ _ => ?_) (fun hv => ?_)
  · exact (PK.of_safe hC (by omega) (by omega)
      (by simp only [removeChunkS, cquietS, cquietE, pqEnterIfAboveP, pqInsertScanP, pqAddP,
        pqLinkAfterP]; safe_tac)
      hG1).mono (le_refl W) hKM
  · have hF3 : Fin (κ := κ) (FB K KH κ (.c .size)) cssMove s1 L1 := (hF1.ite_f hv).seq_assign (fun _ _ => rfl)
    exact PK.seq_g (cssMove_pk hC hK hW (hG1.mono (ΓK_le_ΓV K)) hF3)
      (fun _ _ _ _ hG2 => PK.of_safe hC (by omega) (by omega) (by safe_tac) hG2)

omit hC hK hW in
theorem fin_of_eq {Q : Core → Prop} {c : Stm} {t' : Core} {L' : Loc} {n : Nat} (he : evalF κ c s L = .ok t' L' n)
    (hV : Q t') : Fin (κ := κ) Q c s L := fun s2 L2 n2 h2 => by rw [he] at h2; cases h2; exact hV

/-- **The drive of a splitting chunk**, along a Level F invariant, given the stored-value bound of
each step's end state. -/
theorem driveChunkFrom_pk {p : Nat} (I : Nat → Core → Prop) (h0 : I 0 s)
    (hstep : ∀ j t, I j t → j < s.P.chunkBudget → ∃ b t' L' n,
      evalF κ chunkSplitStepS t (OrderMaintenance.Machine.State.setLocs (fun _ => 0) ["x"] [p]) = .ok t' L' n ∧
      L' "ok" = b2n b ∧ (b = true → I (j + 1) t') ∧ FB K KH κ (.c .size) t')
    (hG : Gd K KH κ (ΓK K) s L) (hg : L "x" = p) : PKok K KH κ (ΓK K) W driveChunkFromS s L := by
  rw [driveChunkFromS_eq]
  refine driveLoop_pk hC hK hW (Γq := ΓM K) rfl rfl (by simp [ΓM]) (by decide) (by decide) (by decide) I h0
    (fun j t hI hj => ?_) hG hg
  obtain ⟨b, t', L', n, he, hok, hI', hV⟩ := hstep j t hI hj
  exact ⟨b, t', L', n, he, hok, hI', fun hG0 => PK.ok (chunkSplitStep_pk hC hK hW hG0 (fin_of_eq he hV))⟩

omit hC hK hW in
/-- What a move leaves: the receiving group `d` is a sibling of `g`, and no size changes. -/
theorem moveElem_d {L0 L1 : Loc} {S1 : Core} {n : Nat} (h : evalF κ moveElemS s L0 = .ok S1 L1 n) :
    (L1 "d" = Fld.get s (L0 "g") (.g .l) ∨ L1 "d" = Fld.get s (L0 "g") (.g .r)) ∧
      ∀ j, j < κ.tbl .G → (S1.Gs.getX j).size = (s.Gs.getX j).size := by
  refine ⟨?_, fun j hj => ?_⟩
  · unfold moveElemS at h
    obtain ⟨s1, L1', n1, n2, h1, h2⟩ := evalF_seq_inv h
    obtain ⟨vl, hvl, e1, e2⟩ := evalF_assign_inv h1
    subst e1 e2
    obtain ⟨jl, hjl, -, rfl⟩ := Exp.ev_rd_inv hvl
    simp only [Exp.ev, Option.some.injEq] at hjl; subst hjl
    obtain ⟨s2, L2, n3, n4, h3, h4⟩ := evalF_seq_inv h2
    obtain ⟨vr, hvr, e1, e2⟩ := evalF_assign_inv h3
    subst e1 e2
    obtain ⟨jr, hjr, -, rfl⟩ := Exp.ev_rd_inv hvr
    simp only [Exp.ev, upd_ne _ _ (show ("g" : Reg) ≠ "gl" by decide),
      Option.some.injEq] at hjr; subst hjr
    obtain ⟨c, hc, m, hm⟩ := evalF_ite_inv h4
    split at hm
    · obtain ⟨s3, L3, n5, n6, h5, h6⟩ := evalF_seq_inv hm
      obtain ⟨s4, L4, n7, n8, h7, h8⟩ := evalF_seq_inv h6
      obtain ⟨vd, hvd, e1, e2⟩ := evalF_assign_inv h7
      subst e1 e2
      left
      rw [evalF_frame_loc (by decide) h8, upd_eq]
      simp only [Exp.ev, Option.some.injEq] at hvd
      rw [← hvd, evalF_frame_loc (by decide) h5, upd_ne _ _ (by decide), upd_eq]
    · obtain ⟨s3, L3, n5, n6, h5, h6⟩ := evalF_seq_inv hm
      obtain ⟨s4, L4, n7, n8, h7, h8⟩ := evalF_seq_inv h6
      obtain ⟨vd, hvd, e1, e2⟩ := evalF_assign_inv h7
      subst e1 e2
      right
      rw [evalF_frame_loc (by decide) h8, upd_eq]
      simp only [Exp.ev, Option.some.injEq] at hvd
      rw [← hvd, evalF_frame_loc (by decide) h5, upd_eq]
  · have := evalF_frame_fld (f := .g .size) (by decide) h (show j < (Fld.g .size).cap κ from hj)
    simpa [Fld.get, GF.get] using this

/-- **A group split step**, given the size bound of the two siblings of the splitting group. -/
theorem groupSplitStep_pk' {p : Nat} (hG : Gd K KH κ (ΓK K) s L) (hg : L "g" = p)
    (hsz : ∀ j, (j = (s.Gs.getX p).l ∨ j = (s.Gs.getX p).r) → (s.Gs.getX j).size + 1 < 2 ^ K) :
    PK K KH κ (ΓV K) W groupSplitStepS s L := by
  refine groupSplitStep_pk hC hK hW hG (fun L0 S1 L1 n hL0 h hj => ?_)
  obtain ⟨hd, hsz'⟩ := moveElem_d h
  rw [hL0, hg] at hd
  rw [hsz' _ hj]
  exact hsz _ (by simpa [Fld.get, GF.get] using hd)

/-- **The drive of a splitting group**, along a Level F invariant, given the size bound of the
groups that receive the moved elements. -/
theorem driveGroupFrom_pk {p : Nat} (I : Nat → Core → Prop) (h0 : I 0 s)
    (hstep : ∀ j t, I j t → j < s.P.groupBudget → ∃ b t' L' n,
      evalF κ groupSplitStepS t (OrderMaintenance.Machine.State.setLocs (fun _ => 0) ["g"] [p]) = .ok t' L' n ∧
      L' "ok" = b2n b ∧ (b = true → I (j + 1) t') ∧
      ∀ j, (j = (t.Gs.getX p).l ∨ j = (t.Gs.getX p).r) → (t.Gs.getX j).size + 1 < 2 ^ K)
    (hG : Gd K KH κ (ΓK K) s L) (hg : L "g" = p) : PKok K KH κ (ΓK K) W driveGroupFromS s L := by
  rw [driveGroupFromS_eq]
  refine driveLoop_pk hC hK hW (Γq := ΓV K) rfl rfl (by simp [ΓV]) (by decide) (by decide) (by decide) I h0
    (fun j t hI hj => ?_) hG hg
  obtain ⟨b, t', L', n, he, hok, hI', hsz⟩ := hstep j t hI hj
  exact ⟨b, t', L', n, he, hok, hI', fun hG0 => PK.ok (groupSplitStep_pk' hC hK hW hG0
    (by simp [OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd]) hsz)⟩

end chunk3

end OrderMaintenance.Impl
