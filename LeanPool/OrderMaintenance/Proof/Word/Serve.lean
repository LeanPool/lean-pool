/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Word.TopWB
public import LeanPool.OrderMaintenance.Impl.TheoremsM


/-!
# Theorem W, stage B3 (first part): a core insertion of the wrapper keeps the bound

`InService.wb`: an insertion into a core in service (`InService`, which the wrapper's Level M
invariant provides for every core insertion: into `cur`, mirrored into `nxt`, and the copy steps of
a rebuild) keeps `WB` at the core's own word size `wK c.P = 64·L`. The numeric conditions of
`insertAfter_wb_top` come from the capacity predicate `Mc` (`NodeB`, `Gs.size ≤ 2 + 2·count`), the
room `count + 1 ≤ N`, and `E.size ≤ count + 1` (`E_size_le`); all of them are below `2^(2L + 8)`,
far below `2^(64L)`.

`WB.mono`: the bound is monotone in `K`, so the two cores of the wrapper, each bounded at its own
`wK`, are bounded at the larger one.
-/


@[expose] public section

namespace OrderMaintenance.Proof.Word

open OrderMaintenance.Model OrderMaintenance.Proof OrderMaintenance.Proof.Top OrderMaintenance.Impl
/-! ### Monotonicity in `K` -/

section mono
variable {K K' : Nat} (hK : K ≤ K')
include hK

theorem lt_mono {x : Nat} (h : x < 2 ^ K) : x < 2 ^ K' := lt_pow_mono h hK

theorem ElemB.mono {e : Elem} (h : ElemB K e) : ElemB K' e := by
  obtain ⟨a, b, c, d⟩ := h; exact ⟨lt_mono hK a, lt_mono hK b, lt_mono hK c, lt_mono hK d⟩

theorem GroupB.mono {g : Group} (h : GroupB K g) : GroupB K' g := by
  obtain ⟨a, b, c, d, e, f, g, i, j, l⟩ := h
  exact ⟨lt_mono hK a, lt_mono hK b, lt_mono hK c, lt_mono hK d, lt_mono hK e, lt_mono hK f,
    lt_mono hK g,
    lt_mono hK i, lt_mono hK j, lt_mono hK l⟩

theorem ChunkB.mono {c : Chunk} (h : ChunkB K c) : ChunkB K' c := by
  obtain ⟨a, b, c, d, e, f, g, i, j⟩ := h
  exact ⟨lt_mono hK a, lt_mono hK b, lt_mono hK c, lt_mono hK d, lt_mono hK e, lt_mono hK f,
    lt_mono hK g,
    lt_mono hK i, lt_mono hK j⟩

theorem NodeB.mono {n : Node} (h : NodeB K n) : NodeB K' n := by
  obtain ⟨a, b, c, d, e, f, g, i, j, l, m, o⟩ := h
  exact ⟨lt_mono hK a, lt_mono hK b, lt_mono hK c, lt_mono hK d, lt_mono hK e, lt_mono hK f,
    lt_mono hK g,
    lt_mono hK i, fun x hx => lt_mono hK (j x hx), fun p hp => ⟨lt_mono hK (l p hp).1, lt_mono
      hK (l p hp).2⟩,
    fun x hx => lt_mono hK (m x hx), fun p hp => lt_mono hK (o p hp)⟩

theorem JobB.mono {j : Job} (h : JobB K j) : JobB K' j := by
  obtain ⟨a, b, c, d⟩ := h
  refine ⟨lt_mono hK a, lt_mono hK b, lt_mono hK c, ?_⟩
  revert d
  unfold JobPcB
  split
  · exact lt_mono hK
  · exact id
  · exact lt_mono hK
  · exact fun ⟨x, y⟩ => ⟨lt_mono hK x, lt_mono hK y⟩
  · exact fun ⟨x, y, z, w⟩ => ⟨lt_mono hK x, lt_mono hK y, lt_mono hK z, lt_mono hK w⟩

theorem PrepB.mono {p : Prep} (h : PrepB K p) : PrepB K' p := by
  obtain ⟨a, b, c, d, e⟩ := h
  exact ⟨lt_mono hK a, lt_mono hK b, lt_mono hK c, lt_mono hK d, fun v hv => lt_mono hK (e v hv)⟩

theorem ParamsB.mono {P : Params} (h : ParamsB K P) : ParamsB K' P := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16⟩ := h
  exact ⟨lt_mono hK a1, lt_mono hK a2, lt_mono hK a3, lt_mono hK a4, lt_mono hK a5, lt_mono hK a6,
    lt_mono hK a7, lt_mono hK a8, lt_mono hK a9, lt_mono hK a10, lt_mono hK a11, lt_mono hK a12,
    lt_mono hK a13, lt_mono hK a14, lt_mono hK a15, lt_mono hK a16⟩

theorem ArrB.mono {a : Array Nat} (h : ArrB K a) : ArrB K' a := fun i => lt_mono hK (h i)

/-- **The stored-value bound is monotone in `K`.** -/
theorem WB.mono {s : Core} (h : WB K s) : WB K' s := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13⟩ := h
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := s7
  obtain ⟨q1, q2, q3, q4, q5, q6⟩ := s10
  exact ⟨s1.mono hK, fun i => (s2 i).mono hK, fun i => (s3 i).mono hK, fun i => (s4 i).mono hK,
    fun i => (s5 i).mono hK, fun g hg => lt_mono hK (s6 g hg),
    ⟨lt_mono hK c1, lt_mono hK c2, lt_mono hK c3, lt_mono hK c4, lt_mono hK c5, lt_mono hK c6,
      lt_mono hK c7, lt_mono hK c8⟩,
    fun p hp => (s8 p hp).mono hK, fun j hj => (s9 j hj).mono hK,
    ⟨q1.mono hK, q2.mono hK, q3.mono hK, q4.mono hK, q5.mono hK, q6.mono hK⟩,
    fun c => (s11 c).mono hK, fun c t ht => lt_mono hK (s12 c t ht), s13.mono hK⟩

end mono

/-! ### The numeric room at `wK` -/

theorem topJ_le (N : Nat) : topJ (proofParams N) ≤ 16 * pL N := by
  have hL := pL_ge N
  have hH : (proofParams N).H = pL N / 3 + 1 := rfl
  have hs : (proofParams N).s = 11 := rfl
  unfold topJ walkLeft
  rw [hH, hs]
  omega

/-- Everything below `2^(2L + 8)` is below `2^wK`. -/
theorem lt_wK (N : Nat) {x : Nat} (hx : x < 2 ^ (2 * pL N + 8)) : x < 2 ^ wK (proofParams N) :=
  lt_pow_mono hx (by
    have := pL_ge N
    change _ ≤ 64 * pL N
    omega)

/-- **The numeric conditions of `insertAfter_wb_top`** at `wK`, for a core of capacity `N` with
`count + 1 ≤ N`, `E.size ≤ count + 1`, `Gs.size ≤ 2 + 2·count`. -/
theorem room_counts (N : Nat) {E G c : Nat} (hc : c + 1 ≤ N) (hE : E ≤ c + 1) (hG : G ≤ 2 + 2 * c) :
    4 * E + 8 ≤ 2 ^ wK (proofParams N) ∧ G + 2 ≤ 2 ^ wK (proofParams N) ∧
      2 * c + 4 ≤ 2 ^ wK (proofParams N) ∧
      nb0 (proofParams N) + topJ (proofParams N) * (2 + 2 * (c + 1)) + 2 ≤ 2 ^ wK (proofParams
        N) := by
  have hL := pL_ge N
  have hN := N_lt N
  have hJ := topJ_le N
  have h16 := pow_ge_mul (pL N) hL
  have hnb : nb0 (proofParams N) = pL N / 3 + 1 + 2 := rfl
  have hp : 2 ^ (2 * pL N + 8) = 2 ^ pL N * 2 ^ pL N * 256 := by
    rw [show 2 * pL N + 8 = pL N + pL N + 8 by omega, pow_add, pow_add]
    norm_num
  have hb : ∀ x, x < 2 ^ pL N * 2 ^ pL N * 256 → x + 1 ≤ 2 ^ wK (proofParams N) := fun x hx =>
    lt_wK N (by
      rw [hp]
      exact hx)
  have hJc : topJ (proofParams N) * (2 + 2 * (c + 1)) ≤ 2 ^ pL N * (4 * 2 ^ pL N) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hnb' : nb0 (proofParams N) ≤ 2 ^ pL N := by rw [hnb]; omega
  refine ⟨hb _ ?_, hb _ ?_, hb _ ?_, hb _ ?_⟩ <;> nlinarith [Nat.one_le_two_pow (n := pL N)]

/-! ### An insertion into a core in service -/

/-- **An insertion into a core in service keeps the stored-value bound** at the core's word size
`wK c.P = 64·L`. -/
theorem _root_.OrderMaintenance.Impl.InService.wb {c : Core} {L : List Nat} (h : InService c L)
  {x : Nat} (hx : x ∈ L) (hh : Nat)
    (hW : WB (wK c.P) c) {c' : Core} (hr : (insertAfter x hh).run c = .ok c.E.size c') :
    WB (wK c.P) c' := by
  obtain ⟨hk, hR, hn, hsize, hcap, hI5, -⟩ := h.params
  have hmk : c.P = proofParams c.P.N := h.ok.pmk
  obtain ⟨hLR, hTR, -⟩ := room_wK c.P.N
  rw [← hmk] at hLR hTR
  obtain ⟨A, hI, hel⟩ := h.ok.cost.low.inv
  have hE := E_size_le hI
  rw [hel, ← h.ok.cnt] at hE
  obtain ⟨-, hNB, -, -, -, -, -, hGs⟩ := h.mc
  obtain ⟨r1, r2, r3, r4⟩ := room_counts c.P.N h.room hE hGs
  rw [← hmk] at r1 r2 r3 r4
  obtain ⟨c'', hr', hW'⟩ := insertAfter_wb_top (P := c.P) h.ok.cost hx hk hR hn hsize hcap hI5
    hh hW hLR hTR
    r1 r2 r3 hNB rfl r4
  rw [hr] at hr'
  obtain ⟨-, rfl⟩ := EStateM.Result.ok.inj hr'
  exact hW'

/-! ### The other core operations of the wrapper -/

/-- **A fresh core** at the proof parameters is bounded at its word size. -/
theorem newCore_wK {N : Nat} {lazy : Bool} {c : Core} (hc : newCore (proofParams N) lazy = .ok c) :
    WB (wK (proofParams N)) c := by
  obtain ⟨hL, -, hR⟩ := room_wK N
  exact newCore_wb (params_wB N) hL hR (pp_topPP N) hc

/-- **A preparation step** of a core under construction (`PrepM`) at the proof parameters. -/
theorem _root_.OrderMaintenance.Impl.PrepM.wb {n : Core} (hM : PrepM n) (hmk : n.P = proofParams
  n.P.N) (hW : WB (wK n.P) n)
    {b : Bool} {n' : Core} (hr : prepareStep.run n = .ok b n') : WB (wK n.P) n' := by
  obtain ⟨-, -, hR⟩ := room_wK n.P.N
  rw [← hmk] at hR
  exact prepareStep_wb (Or.inr hM.1) hW hR hr

/-- **A copy step of a rebuild** (`copyAtCursor`): the copied element is inserted after the tail
of `nxt`, a core in service (`CopyOK`). -/
theorem copy_wb {om om' : OrderMaintenance} {n n' : Core} (hC : CopyOK om n) (hW : WB (wK n.P) n)
    (hcp : copyAtCursor om n = .ok (om', n')) : WB (wK n'.P) n' := by
  unfold copyAtCursor at hcp
  cases hl : (om.cur.E.getX om.cursor).live with
  | false =>
    simp only [hl, Bool.false_eq_true, ite_false, pure, Except.pure] at hcp
    injection hcp with hcp; injection hcp with h1 h2; subst h2; exact hW
  | true =>
    obtain ⟨B, hS, htl, -⟩ := hC.2 hl
    obtain ⟨c', hr', -, -, -, hP', -⟩ := hS.insert htl (om.cur.E.getX om.cursor).h
      (fun r => if r = "x" then n.tail else (om.cur.E.getX om.cursor).h) (by simp) (by simp)
    simp only [hl, ite_true, bind, Except.bind, runCore, hr', pure, Except.pure] at hcp
    injection hcp with hcp; injection hcp with h1 h2; subst h2
    rw [hP']; exact hS.wb htl _ hW hr'

end OrderMaintenance.Proof.Word
