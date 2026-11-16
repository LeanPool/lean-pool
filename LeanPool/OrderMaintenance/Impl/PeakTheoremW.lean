/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.PeakOpsM


/-!
# Theorem W, option (A), stage A3: the per-operation and initialization peak bounds

For a machine state `m` holding (`WEnc om m p`) a wrapper state `om` reached by initialization and
`t` valid operations (`ReachW K_B t om Sp`, option (B)), the machine code of the next valid
operation computes nothing above

  `2^(2·(wKom om + 128) + 4) + 2^KH`,  `KH = log₂(t + 1) + 1`,

i.e. `dpk (opS op) m < 2^(2·(wKom om + 128) + 5) + 2·(t + 1)` (`theoremW_op`): **c₀ = 5, c₁ = 2**.
The word size is that of the state before the operation (`wKom om = 64·max(L_cur, L_nxt)`), plus
128 for a core created during the operation (`N' ≤ 4N`, `L' ≤ L + 2`). Handles enter through the
width `KH`, and `2^KH ≤ 2(t + 1)`.

Initialization: `dpk initWS m < 2^1029` for `K_B < 2^512` (`theoremW_init`): **W₀ = 1029** (the
first core has `L = 8`, `wK = 512`, budget `2^1028 + 2`).

Nothing here is used by Theorems A and B.
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model OrderMaintenance.Proof OrderMaintenance.Proof.Top
  OrderMaintenance.Proof.Word
open OrderMaintenance.Machine (Reg Arr State Out exec Stmt Same Expr BinOp UnOp wp wpB dpk)

variable {K KH : Nat}

/-! ### One operation -/

/-- **One operation within the budget.** -/
theorem opS_pk {om : OrderMaintenance} {m : State} {p : Nat} {Sp : OrderMaintenance.Spec.State}
  {t : Nat} (h : WEnc om m p)
    (hI : MInv om Sp) (hB : WBW t om om.nxt) {op : OrderMaintenance.Spec.Op} (hv : op.Valid Sp)
    (hK : wKom om + 128 ≤ K) (hKB : om.KB < 2 ^ K) (hKH : t + 1 < 2 ^ KH) :
    wpB (BW K KH) (opS op) TT m := by
  obtain ⟨hS, hf, -⟩ := hI.1.w
  have hnhT : om.nextHandle ≤ t := hB.hnd
  have harg : ∀ x : Nat, x ∈ Sp.list → x ≤ BW K KH := fun x hx => by
    have h2 : x < om.nextHandle := by rw [hf]; exact hS.2 x hx
    proveBudget K KH
  cases op <;> unfold opS
  case insertFirst =>
    refine wpB_assign_seq 0 rfl (by simp) (fun s1 hl1 hm1 hc1 => ?_)
    exact insertW_pk (h.congr hm1 hc1) hI hB (hx := none) hv (by
      rw [hl1]
      simp [State.upd, b2n])
      (fun x e => by cases e) hK hKB hKH
  case insertAfter x =>
    refine wpB_assign_seq 1 rfl (by
      simp only [Expr.maxv]
      proveBudget K KH) (fun s1 hl1 hm1 hc1 => ?_)
    refine wpB_assign_seq x rfl (by simpa using harg x hv) (fun s2 hl2 hm2 hc2 => ?_)
    exact insertW_pk ((h.congr hm1 hc1).congr hm2 hc2) hI hB (hx := some x) hv
      (by
        rw [hl2, hl1]
        simp [State.upd, b2n]) (fun x' e => by cases e; rw [hl2]; simp [State.upd]) hK hKB hKH
  case delete x =>
    refine wpB_assign_seq x rfl (by simpa using harg x hv) (fun s1 hl1 hm1 hc1 => ?_)
    exact deleteW_pk (h.congr hm1 hc1) hI hB hv (by
      rw [hl1]
      simp [State.upd]) hK hKB hKH
  case order x y =>
    refine wpB_assign_seq x rfl (by simpa using harg x hv.1) (fun s1 hl1 hm1 hc1 => ?_)
    refine wpB_assign_seq y rfl (by simpa using harg y hv.2) (fun s2 hl2 hm2 hc2 => ?_)
    exact orderW_pk ((h.congr hm1 hc1).congr hm2 hc2) hI hB hv.1 hv.2 (by
      rw [hl2, hl1]
      simp [State.upd])
      (by
        rw [hl2]
        simp [State.upd]) (by omega) hKB hKH

theorem two_pow_log2 (t : Nat) : t + 1 < 2 ^ (Nat.log2 (t + 1) + 1) ∧ 2 ^ (Nat.log2 (t + 1) + 1)
  ≤ 2 * (t + 1) := by
  refine ⟨Nat.lt_log2_self, ?_⟩
  rw [pow_succ]
  have := Nat.log2_self_le (n := t + 1) (by omega)
  omega

/-- **Theorem W, option (A), one operation.** On a machine state holding a wrapper state reached by
initialization and `t` valid operations, the machine code of the next valid operation computes no
value at or above `2^(2·(wKom om + 128) + 5) + 2·(t + 1)`. -/
theorem theoremW_op {KB t : Nat} {om : OrderMaintenance} {Sp : OrderMaintenance.Spec.State} {m :
  State} {p : Nat} (h4 : 4 ≤ KB)
    (hKB : KB < 2 ^ 512) (hR : ReachW KB t om Sp) (h : WEnc om m p) {op :
      OrderMaintenance.Spec.Op} (hv : op.Valid Sp) :
    dpk (opS op) m < 2 ^ (2 * (wKom om + 128) + 5) + 2 * (t + 1) := by
  obtain ⟨hI, hB, hK⟩ := reachW_inv h4 hR
  obtain ⟨hKH, hKH2⟩ := two_pow_log2 t
  have h512 : 512 ≤ wKom om := le_trans (wK_ge512 hI.cmk) wK_cur_le
  have hKB' : om.KB < 2 ^ (wKom om + 128) := by
    rw [hK]; exact lt_pow_mono hKB (by omega)
  have hpk := dpk_le_of (opS_pk (K := wKom om + 128) (KH := Nat.log2 (t + 1) + 1) (m := {
    m with
    peak := 0
  }) (h.congr rfl rfl) hI hB hv
    le_rfl hKB' hKH)
  have e : 2 ^ (2 * (wKom om + 128) + 5) = 2 * 2 ^ (2 * (wKom om + 128) + 4) := by
    rw [pow_succ]
    exact Nat.mul_comm _ _
  have := Nat.two_pow_pos (2 * (wKom om + 128) + 4)
  unfold BW at hpk
  omega

/-! ### Initialization -/

theorem wK_64 : wK (proofParams 64) = 512 := by decide

/-- **Initialization within the budget** `BW 512 1`. -/
theorem initWS_pk {m : State} {KB : Nat} (hkb : m.loc "kb" = KB) (hKB : KB < 2 ^ 512) :
    wpB (BW 512 1) initWS TT m := by
  obtain ⟨n, -, hrun⟩ := newCore_run (P := proofParams minimumCapacity) (lazy := false)
  have hb : (2 : Nat) ^ 512 ≤ BW 512 1 := by have := pow_BW 512; unfold BW; omega
  unfold initWS
  refine wpB_assign_seq 64 rfl (by
    simp
    omega) (fun s1 hl1 hm1 hc1 => ?_)
  have hN1 : s1.loc "nN" = 64 := by rw [hl1]; simp [State.upd]
  refine wpB_seq_ofQ (eagerCore_ok 0 hN1 (by decide) hrun) (eagerCore_pk 0 hN1 (by decide) hrun
    (by rw [wK_64]))
    (fun s2 k2 ⟨hE2, hS2, hl2, hk2⟩ => ?_)
  have hev : ∀ ae ∈ initAllocs, ae.2.noLoad ∧ (ae.2.eval s2).isSome := by
    intro ae hae
    simp only [initAllocs, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hae
    rcases hae with ⟨k, -, rfl⟩ | rfl <;> exact ⟨rfl, rfl⟩
  obtain ⟨a1, -, a3, a4, -⟩ := Machine.exec_allocAll initAllocs s2 hev initAllocs_nodup
  have hc7 := (a4 (wa 7, .lit 1) (by simp only [initAllocs, List.mem_append, List.mem_map,
      List.mem_range, Prod.mk.injEq, and_true,
      List.mem_cons, Expr.lit.injEq, OfNat.one_ne_ofNat,
      and_false, List.not_mem_nil, or_self, or_false]; exact ⟨7, by decide, rfl⟩)).1
  refine wpB_seq_ofQ (Qc := fun s3 _ => s3.loc = s2.loc ∧ s3.cap (wa 7) = 1) ⟨a1, a3, hc7⟩
    (wpB_allocAll s2.loc _ s2 rfl (fun ae hae s _ => by
      simp only [initAllocs, List.mem_append, List.mem_map, List.mem_range,
        List.mem_singleton] at hae
      rcases hae with ⟨k, -, rfl⟩ | rfl
      · exact ⟨rfl, by simp; omega⟩
      · exact ⟨rfl, by simp; omega⟩)) (fun s3 _ ⟨hl3, hc3⟩ => ?_)
  have hkb3 : s3.loc "kb" = KB := by
    rw [hl3, hl2 "kb" (by simp [pLocs]), hl1]; simp [State.upd, hkb]
  exact wpB_T (Machine.wpB_store_g (Q := TT) 0 KB rfl (by simp [Expr.eval, hkb3]) (by
    rw [hc3]
    decide)
    (by simp) (by
      simp [hkb3]
      omega) (fun _ _ _ _ => trivial))

/-- **Theorem W, option (A), initialization.** With `K_B < 2^512` in local `kb`, the
initialization computes no value at or above `2^1029`. -/
theorem theoremW_init {m : State} {KB : Nat} (hkb : m.loc "kb" = KB) (hKB : KB < 2 ^ 512) :
    dpk initWS m < 2 ^ 1029 := by
  have hpk := dpk_le_of (initWS_pk (m := {
    m with
    peak := 0
  }) hkb hKB)
  unfold BW at hpk
  have e : 2 ^ 1029 = 2 * 2 ^ (2 * 512 + 4) := by
    rw [show 1029 = (2 * 512 + 4) + 1 by rfl, pow_succ]
    exact Nat.mul_comm _ _
  have : 4 ≤ 2 ^ (2 * 512 + 4) := by
    calc
      4 = 2 ^ 2 := rfl
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  omega

end OrderMaintenance.Impl
