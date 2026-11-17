/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.TheoremsM


/-!
# M6: the memory of a core

The arrays of a core of capacity `N ≥ 64` (all the arrays `Enc` asks for, with the capacities
`capsOf (proofParams N)`) hold at most `40000 · N` cells (`core_mem`). The large constant comes
from the top structure's per-node lists (162 or 322 entries each); the node count is `O(N / L)`.
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model OrderMaintenance.Proof OrderMaintenance.Proof.Top
open OrderMaintenance.Machine (Reg Arr State Out exec Stmt Same Expr BinOp UnOp wp)

/-- The cells of all the arrays of a core with capacities `κ` (the parameters included). -/
def memOf (κ : Caps) : Nat := (Slot.allNP.map (capOf κ)).sum + 16

theorem memOf_eq (P : Params) :
    memOf (capsOf P) = 5343 + P.N * 37 + cb P * 671 + cb P * P.H + nbMax P * 2596 + P.H * 2 := by
  unfold memOf
  simp only [Slot.allNP, Fld.all, EF.all, GF.all, CF.all, NF.all, AF.all, SF.all, Tbl.all, LK.all,
    OF.all,
    List.map, List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append,
     List.sum_cons, List.sum_nil,  capOf, Fld.cap, capsOf]
  ring

/-- The chunk bound's divisor is at least `L² / 8`. -/
theorem div_bound {L : Nat} (h8 : 8 ≤ L) : L * L ≤ 8 * (vth L + 1 - vcm L) := by
  have hgm : vgm L = L - 1 := by unfold vgm vG; omega
  have hu : vT L / vgm L ≤ 3 * L + 6 := by
    rw [hgm]
    apply Nat.div_le_of_le_mul
    obtain ⟨M, rfl⟩ : ∃ M, L = M + 1 := ⟨L - 1, by omega⟩
    simp only [vT, Nat.add_sub_cancel]
    nlinarith
  have hkc : vkc L ≤ L + 4 := by unfold vkc vuT; omega
  have hkg : vkg L ≤ L := by unfold vkg vG; omega
  have hLL : 8 * L ≤ L * L := Nat.mul_le_mul_right L h8
  have hT : vT L = 3 * (L * L) := by unfold vT; ring
  have hth : vth L = 2 * (L * L) := by unfold vth; ring
  have hcm : 2 * vcm L ≤ vT L + vkc L + (vG L + vkg L) + 1 := by unfold vcm; omega
  unfold vG at hcm
  omega

theorem pow_ge_lin : ∀ k, 6 ≤ k → 8 * (k + 1) ≤ 2 ^ k
  | 0, h | 1, h | 2, h | 3, h | 4, h | 5, h => by omega
  | 6, _ => by decide
  | k + 7, _ => by
    have := pow_ge_lin (k + 6) (by omega)
    rw [pow_succ]; omega

theorem pL_small {N : Nat} (hN : 64 ≤ N) : 8 * pL N ≤ N := by
  rw [pL_eq (by omega)]
  have hk : 6 ≤ Nat.log2 N := (Nat.le_log2 (by omega)).mpr (by simpa using hN)
  have h1 := Nat.log2_self_le (n := N) (by omega)
  have h2 := pow_ge_lin _ hk
  omega

/-- **The memory of a core**: at most `40000 · N` cells. -/
theorem core_mem {N : Nat} (hN : 64 ≤ N) : memOf (capsOf (proofParams N)) ≤ 40000 * N := by
  rw [memOf_eq, nbMax_proof, cb_proof]
  have hL8 := pL_small hN
  set L := pL N
  have h8 : 8 ≤ L := pL_ge N
  have hd := div_bound h8
  set d := vth L + 1 - vcm L
  have hq : N / d * d ≤ N := Nat.div_mul_le_self N d
  set q := N / d
  have hqLL : q * (L * L) ≤ 8 * N := by
    calc q * (L * L) ≤ q * (8 * d) := Nat.mul_le_mul_left q hd
      _ = 8 * (q * d) := by ring
      _ ≤ 8 * N := by omega
  have hqL : q * L ≤ N := by
    have : q * L * 8 ≤ q * L * L := Nat.mul_le_mul_left _ h8
    nlinarith
  have h8q : 8 * q ≤ N := by
    have : q * 8 ≤ q * L := Nat.mul_le_mul_left _ h8
    omega
  have h3H : 3 * vH L ≤ L + 3 := by unfold vH; omega
  have h3qH : 3 * (q * vH L) ≤ q * L + 3 * q := by
    have := Nat.mul_le_mul_left q h3H
    nlinarith
  simp only [vnb, vcb, pp_N, pp_H]
  change 5343 + N * 37 + (2 + 2 * q) * 671 + (2 + 2 * q) * vH L +
    (vH L + 2 + (vH L + 1 + (vH L * 12 + 1)) * (2 + 2 * q)) * 2596 + vH L * 2 ≤ 40000 * N
  have e : 5343 + N * 37 + (2 + 2 * q) * 671 + (2 + 2 * q) * vH L +
      (vH L + 2 + (vH L + 1 + (vH L * 12 + 1)) * (2 + 2 * q)) * 2596 + vH L * 2 =
      22261 + N * 37 + 11726 * q + 70096 * vH L + 67498 * (q * vH L) := by ring
  rw [e]
  omega

/-! ### The memory of the reachable states -/

/-- The cells of slot `p`'s arrays in machine state `m`. -/
def slotMem (m : State) (p : Nat) : Nat := (Slot.allNP.map fun sl => m.cap (arr p sl)).sum +
  m.cap (arr p .prm)

theorem Enc.cap_slot {p : Nat} {κ : Caps} {s : Core} {m : State} (h : Enc p κ s m) :
    ∀ sl, m.cap (arr p sl) = capOf κ sl
  | .f f => h.cap f
  | .sz t => h.scap t
  | .prm => h.pcap
  | .lst k b => h.lcapA k b
  | .len k => h.lcapN k
  | .path => h.wcap
  | .opt o => h.ocap o

theorem Enc.slotMem_eq {p : Nat} {κ : Caps} {s : Core} {m : State} (h : Enc p κ s m) :
  OrderMaintenance.Impl.slotMem m p = memOf κ := by
  unfold OrderMaintenance.Impl.slotMem memOf
  rw [h.cap_slot .prm]
  congr 2
  exact List.map_congr_left fun sl _ => h.cap_slot sl

/-- **The memory of a reachable state**: the slot of `cur` holds at most `40000 · N` cells, and
the slot of `nxt` (during a rebuild) at most `40000 · N'`, with `N' ≤ 4 · N`. (The handle maps are
allocated with `nextHandle + (N − count) + N'` cells, which grows with the number of insertions.) -/
theorem reach_mem {KB : Nat} {m : State} {Sp : OrderMaintenance.Spec.State} (hR : Reach KB m Sp) :
    ∃ om p, WEnc om m p ∧ slotMem m p ≤ 40000 * om.cur.P.N ∧
      ∀ n, om.nxt = some n → slotMem m (1 - p) ≤ 40000 * n.P.N ∧ n.P.N ≤ 4 * om.cur.P.N := by
  obtain ⟨om, p, h, hI, -⟩ := hR
  have hW := hI.1
  obtain ⟨-, -, A, hRA, -, -, -⟩ := hW.w
  have hmk : om.cur.P = proofParams om.cur.P.N := (hW.cur A hRA.inv).pmk
  refine ⟨om, p, h, ?_, fun n hn => ?_⟩
  · rw [h.cur.slotMem_eq, hmk]; exact core_mem hW.big
  · obtain ⟨c₀, live₀, I, D, hRW⟩ := hW.busy n hn
    have hnP := hRW.nP
    have hNn : n.P.N = 4 * max (live₀ + ((c₀ + (om.cur.P.L + 2)) / (om.KB - 1) + 1)) 16 := by
      rw [hnP]; rfl
    have hsm := costSetup.small _ hW.big
    rw [← hmk] at hsm
    have hc0 := hRW.c0
    have hl0 := hRW.l0
    have hkb := hW.kb
    have hdiv : (c₀ + (om.cur.P.L + 2)) / (om.KB - 1) ≤ (c₀ + (om.cur.P.L + 2)) / 3 :=
      Nat.div_le_div_left (by omega) (by norm_num)
    refine ⟨?_, ?_⟩
    · rw [(h.nxt n hn).slotMem_eq, hnP]
      apply core_mem
      show 64 ≤ 4 * max (live₀ + ((c₀ + (om.cur.P.L + 2)) / (om.KB - 1) + 1)) 16
      have := le_max_right (live₀ + ((c₀ + (om.cur.P.L + 2)) / (om.KB - 1) + 1)) 16
      omega
    · rw [hNn]
      have hbig := hW.big
      apply Nat.mul_le_mul_left 4
      apply max_le <;> omega

end OrderMaintenance.Impl
