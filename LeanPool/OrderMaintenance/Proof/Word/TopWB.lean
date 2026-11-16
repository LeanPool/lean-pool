/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Word.TopStart


/-!
# Theorem W, stage B2: the top structure's contract `TopWB`

`topWB`: the top invariant of the cost proof (`TIat TopInv P`, the `TI` of `insertAfter_cost` in
the final theorems, `Impl/Caps.lean`) satisfies `TopWB` with the job measure `topMu`, given room
for labels and tags (`TopRoom`). The split's insertion is `insertAround_wb`, its new tags bounded by
the top invariant after the split; a job step is `jobStep_wb`, and the node budget is `node_step`.

`insertAfter_wb_top` is `insertAfter_wb` at this instance, and `room_wK` gives the room at the
candidate word size `wK P = 64·L`.
-/


@[expose] public section

namespace OrderMaintenance.Proof.Word

open OrderMaintenance.Model OrderMaintenance.Proof OrderMaintenance.Proof.Top
  OrderMaintenance.Impl OrderMaintenance.Zeroing
variable {K : Nat}

theorem markState_tag (t : Core) (x y z : Nat) (j : Job) (c : Nat) :
    ((markState t x y z j).C.getX c).tag = (t.C.getX c).tag := by
  unfold markState
  simp only [Array.getX_modify]
  split_ifs <;> rfl

theorem markState_Csize (t : Core) (x y z : Nat) (j : Job) :
    (markState t x y z j).C.size = t.C.size := by
  unfold markState; simp

/-- **The top structure keeps the stored-value bound**: `TopWB` for the cost proof's top
invariant at parameters `P`, given room for labels and tags. -/
theorem topWB {P : Params} (hR : TopRoom K P) (hK : 1 ≤ K) : TopWB K (TIat TopInv P) topMu := by
  refine ⟨fun s A x job s2 hI hT hres hxL hxq hroom hWl hr hT' => ?_,
    fun s A job r s' hI hT hres hW hN hC hr hT' => ?_⟩
  · -- the split's insertion
    have hR2 : TopRel (linkChunkPair (push2 s) x s.C.size (s.C.size + 1)) s2 := by
      have := top_insertAround x s.C.size (s.C.size + 1) (linkChunkPair (push2 s) x s.C.size
        (s.C.size + 1))
      rw [hr] at this; exact this
    have hts : (linkChunkPair (push2 s) x s.C.size (s.C.size + 1)).C.size = s.C.size + 2 := by
      simp [linkChunkPair, push2]
    have hP2 : s2.P = P := by rw [hR2.rest.1, ← hT.2]; rfl
    have hx := hxL.2
    have htag : ∀ c, 1 ≤ c → c < s.C.size + 2 → (s2.C.getX c).tag < 2 ^ K := fun c h1 h2 => by
      have := tag_lt_of_topInv hT'.1 (c := c) h1 (by
        rw [markState_Csize, hR2.Csize, hts]
        exact h2)
      rw [markState_tag] at this
      exact lt_pow_mono this (by
        change s2.P.H * s2.P.beta ≤ K
        rw [hP2]
        exact hR.tag)
    obtain ⟨hW2, hJ⟩ := insertAround_wb hWl hK (by
      change s.P.beta ≤ K
      rw [hT.2]
      exact hR.beta)
      (by omega) (by omega) (by omega) (by omega) (by
        rw [hts]
        omega) (by
        rw [hts]
        omega) hr
      ⟨htag _ (by omega) (by omega), htag _ (by omega) (by omega)⟩
    refine ⟨hW2, hJ, ?_⟩
    have := ns_insertAround x s.C.size (s.C.size + 1) (linkChunkPair (push2 s) x s.C.size
      (s.C.size + 1))
    rw [hr] at this
    exact this
  · -- a job step
    exact ⟨jobStep_wb hT.1 hres hW (by
      rw [hT.2]
      exact hR) hN hC hr hT'.1, node_step hT.1 hres hr⟩

/-- **A core insertion keeps the stored-value bound**, at the cost proof's top invariant
(`insertAfter_wb` with `TopWB` discharged by `topWB`). The node budget is that of `NodeB`
(`Impl/Caps.lean`): `nodes.size + topMu ≤ nb0 P + topJ P · C.size`. -/
theorem insertAfter_wb_top {P : Params} {n R : Nat} {L : List Nat} {s : Core} {x : Nat}
    (hC : CostInv (TIat TopInv P) topMu (topJ P) n R L s)
    (hx : x ∈ L) (hk : 1 ≤ s.P.reservationBudget) (hRk : topJ P / s.P.reservationBudget + 1 ≤
      R) (hn : 1 ≤ n)
    (hsize : 2 + 2 * ((s.count + 1) / (s.P.theta + 1 - cmax s.P)) ≤ n + 1)
    (hcap : 2 + 2 * ((s.count + 1) / (s.P.theta + 1 - cmax s.P)) ≤ capT s.P)
    (hI5 : (s.P.theta : ℝ) + R * (Hn (n - 1) + 1) ≤ s.P.T) (hh : Nat)
    (hW : WB K s) (hL : LabRoom K s.P) (hTR : TopRoom K P) (hE : 4 * s.E.size + 8 ≤ 2 ^ K)
    (hG : s.Gs.size + 2 ≤ 2 ^ K) (hcnt : 2 * s.count + 4 ≤ 2 ^ K)
    (hNB : OrderMaintenance.Impl.NodeB s) (hsP : s.P = P)
    (hNK : nb0 P + topJ P * (2 + 2 * (s.count + 1)) + 2 ≤ 2 ^ K) :
    ∃ s', (insertAfter x hh).run s = .ok s.E.size s' ∧ WB K s' :=
  insertAfter_wb (topContract'.at P) (topWB hTR hL.K1) hC hx hk hRk hn hsize hcap hI5 hh hW hL
    hE hG hcnt
    (NB0 := nb0 P) (by
      unfold OrderMaintenance.Impl.NodeB at hNB
      rw [hsP] at hNB
      exact hNB) hNK

/-! ### The room at the candidate word size -/

/-- **Room at `wK = 64·L`** for labels, tags and the construction's heights. -/
theorem room_wK (N : Nat) :
    LabRoom (wK (proofParams N)) (proofParams N) ∧ TopRoom (wK (proofParams N)) (proofParams N) ∧
      PrepRoom (wK (proofParams N)) (proofParams N) := by
  obtain ⟨hBe, hBg, hHb, -, -, -⟩ := params_room N
  have hL := pL_ge N
  have hK : wK (proofParams N) = 64 * pL N := rfl
  have hb : (proofParams N).beta = 64 := rfl
  have hH : (proofParams N).H = pL N / 3 + 1 := rfl
  have hK1 : 1 ≤ wK (proofParams N) := by rw [hK]; omega
  have hT : TopRoom (wK (proofParams N)) (proofParams N) :=
    ⟨by rw [hb, hK]; omega, by rw [Nat.add_mul] at hHb; omega⟩
  refine ⟨⟨hK1, by omega, by omega⟩, hT, ⟨hT, by rw [hH]; omega, by rw [hb]; omega, ?_⟩⟩
  have : (proofParams N).H + 1 < wK (proofParams N) := by rw [hH, hK]; omega
  exact lt_trans this Nat.lt_two_pow_self

end OrderMaintenance.Proof.Word
