/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Cost.Params


/-!
# Theorem W (word size): definitions

Groundwork for the word-size theorem (`docs/WORD.md`). Nothing here is used by Theorems A and B.

* `WB K s`: every value stored in the Level F core `s` is below `2^K`. This covers every field
  of every record (live or dead), the scalars, the lists inside nodes, the paths, the queue
  arrays, `lpar`, the job and the deferred construction, and the parameters. The one exception
  is the handle `Elem.h`, which is the insertion counter: the decision of 2026-10-16 bounds
  handles by the number of operations instead, and `OMB` below does that.
* `wK P = 64·L`: the candidate bound. `params_wB` proves that the proof parameters lie below it
  with room to spare: `elementBits + 1`, `groupBits + 1` and `(H + 2)·β` are at most `wK`, and
    `N < 2^L`, so
  the capacities (at most `40000·N` cells, `core_mem`) are far below `2^wK`.

`Bool` and `St` fields are not constrained: the machine encodes them as 0–3. `Side` likewise
(0/1).
-/


@[expose] public section

namespace OrderMaintenance.Proof.Word

open OrderMaintenance.Model OrderMaintenance.Proof

/-! ### Stored values below `2^K` -/

/-- An element's fields, except the handle `h`. -/
def ElemB (K : Nat) (e : Elem) : Prop :=
  e.next < 2 ^ K ∧ e.prev < 2 ^ K ∧ e.grp < 2 ^ K ∧ e.lab < 2 ^ K

/-- Every numerical field stored in a group fits below the word bound. -/
def GroupB (K : Nat) (g : Group) : Prop :=
  g.next < 2 ^ K ∧ g.prev < 2 ^ K ∧ g.first < 2 ^ K ∧ g.last < 2 ^ K ∧ g.chk < 2 ^ K ∧
    g.lab < 2 ^ K ∧ g.size < 2 ^ K ∧ g.src < 2 ^ K ∧ g.l < 2 ^ K ∧ g.r < 2 ^ K

/-- Every numerical field stored in a chunk fits below the word bound. -/
def ChunkB (K : Nat) (c : Chunk) : Prop :=
  c.next < 2 ^ K ∧ c.prev < 2 ^ K ∧ c.first < 2 ^ K ∧ c.last < 2 ^ K ∧ c.size < 2 ^ K ∧
    c.src < 2 ^ K ∧ c.l < 2 ^ K ∧ c.r < 2 ^ K ∧ c.tag < 2 ^ K

/-- A node's numbers, including the entries and labels of its table, its children, the tables
holding it, and the entries of its side map. -/
def NodeB (K : Nat) (n : Node) : Prop :=
  n.height < 2 ^ K ∧ n.livePar < 2 ^ K ∧ n.weight < 2 ^ K ∧ n.first < 2 ^ K ∧ n.last < 2 ^ K ∧
    n.t1 < 2 ^ K ∧ n.t2 < 2 ^ K ∧ n.overflowOf < 2 ^ K ∧
    (∀ c ∈ n.children, c < 2 ^ K) ∧ (∀ p ∈ n.table, p.1 < 2 ^ K ∧ p.2 < 2 ^ K) ∧
    (∀ t ∈ n.inTables, t < 2 ^ K) ∧ (∀ p ∈ n.side, p.1 < 2 ^ K)

/-- The numerical arguments of each background-job program counter fit below the word bound. -/
def JobPcB (K : Nat) : JobPc → Prop
  | .copy j => j < 2 ^ K
  | .walk none => True
  | .walk (some v) => v < 2 ^ K
  | .afterDrain v up => v < 2 ^ K ∧ up < 2 ^ K
  | .fund v up src k => v < 2 ^ K ∧ up < 2 ^ K ∧ src < 2 ^ K ∧ k < 2 ^ K

/-- The three chunk handles and program counter of a job fit below the word bound. -/
def JobB (K : Nat) (j : Job) : Prop := j.x < 2 ^ K ∧ j.y < 2 ^ K ∧ j.z < 2 ^ K ∧ JobPcB K j.pc

/-- All numerical preparation fields and path entries fit below the word bound. -/
def PrepB (K : Nat) (p : Prep) : Prop :=
  p.chunk < 2 ^ K ∧ p.h < 2 ^ K ∧ p.below < 2 ^ K ∧ p.tag < 2 ^ K ∧ ∀ v ∈ p.path, v < 2 ^ K

/-- Every concrete parameter fits below the word bound. -/
def ParamsB (K : Nat) (P : Params) : Prop :=
  P.N < 2 ^ K ∧ P.L < 2 ^ K ∧ P.G < 2 ^ K ∧ P.T < 2 ^ K ∧ P.theta < 2 ^ K ∧ P.elementBits < 2 ^ K ∧
    P.groupBits < 2 ^ K ∧ P.elementSpacing < 2 ^ K ∧ P.groupSpacing < 2 ^ K ∧ P.groupBudget < 2
      ^ K ∧ P.chunkBudget < 2 ^ K ∧
    P.reservationBudget < 2 ^ K ∧ P.a < 2 ^ K ∧ P.s < 2 ^ K ∧ P.beta < 2 ^ K ∧ P.H < 2 ^ K

/-- Every entry of a number array. -/
def ArrB (K : Nat) (a : Array Nat) : Prop := ∀ i, a.getX i < 2 ^ K

/-- **Every value stored in the core is below `2^K`**, handles excepted. -/
structure WB (K : Nat) (s : Core) : Prop where
  P : ParamsB K s.P
  E : ∀ i, ElemB K (s.E.getX i)
  Gs : ∀ i, GroupB K (s.Gs.getX i)
  C : ∀ i, ChunkB K (s.C.getX i)
  nodes : ∀ i, NodeB K (s.nodes.getX i)
  freeG : ∀ g ∈ s.freeG, g < 2 ^ K
  scalars : s.count < 2 ^ K ∧ s.head < 2 ^ K ∧ s.tail < 2 ^ K ∧ s.firstGroup < 2 ^ K ∧
    s.firstChunk < 2 ^ K ∧ s.fallbacks < 2 ^ K ∧ s.pqHi < 2 ^ K ∧ s.pqLo < 2 ^ K
  prep : ∀ p, s.prep = some p → PrepB K p
  job : ∀ j, s.resJob = some j → JobB K j
  pq : ArrB K s.pqHead ∧ ArrB K s.pqNext ∧ ArrB K s.pqPrev ∧ ArrB K s.pqWhere ∧
    ArrB K s.nbNext ∧ ArrB K s.nbPrev
  path : ∀ c, ArrB K (s.path.getX c)
  cin : ∀ c, ∀ t ∈ s.cin.getX c, t < 2 ^ K
  lpar : ArrB K s.lpar

/-- **The wrapper's values**: both cores below `2^K`; element indices below `2^K`; the handle
of every element, the live count, the handle counter and the rebuild counter at most the number
of operations `n` (the handle map arrays are indexed by handles, so their capacity is
`nextHandle` plus a core capacity, `WEnc.roomC`). -/
structure OMB (K n : Nat) (om : OrderMaintenance) : Prop where
  cur : WB K om.cur
  nxt : ∀ c, om.nxt = some c → WB K c
  curIdx : ArrB K om.curIdx
  nxtIdx : ArrB K om.nxtIdx
  hcur : ∀ i, (om.cur.E.getX i).h ≤ n
  hnxt : ∀ c, om.nxt = some c → ∀ i, (c.E.getX i).h ≤ n
  cursor : om.cursor < 2 ^ K
  KB : om.KB < 2 ^ K
  counters : om.live ≤ n ∧ om.nextHandle ≤ n ∧ om.rebuilds ≤ n

/-! ### Defaults -/

theorem pos (K : Nat) : 0 < 2 ^ K := Nat.two_pow_pos K

theorem elemB_default (K : Nat) : ElemB K default := by
  simp only [ElemB]; exact ⟨pos K, pos K, pos K, pos K⟩

theorem groupB_default (K : Nat) : GroupB K default := by
  have := pos K; simp only [GroupB]; exact ⟨this, this, this, this, this, this, this, this,
    this, this⟩

theorem chunkB_default (K : Nat) : ChunkB K default := by
  have := pos K; simp only [ChunkB]; exact ⟨this, this, this, this, this, this, this, this, this⟩

theorem nodeB_default (K : Nat) : NodeB K default := by
  have := pos K
  refine ⟨this, this, this, this, this, this, this, this, ?_, ?_, ?_, ?_⟩ <;> intro _ h <;> cases h

/-- `getX` of an array whose elements all satisfy `p`, where the default does too. -/
theorem getX_of {α : Type} [Inhabited α] {p : α → Prop} {a : Array α} (hd : p default)
    (h : ∀ x ∈ a, p x) (i : Nat) : p (a.getX i) := by
  unfold Array.getX
  rw [Array.getD_eq_getD_getElem?]
  cases hx : a[i]? with
  | none => exact hd
  | some x => exact h x (Array.mem_of_getElem? hx)

@[simp] theorem getX_empty {α : Type} [Inhabited α] (i : Nat) : (#[] : Array α).getX i = default
  := by
  simp only [Array.getX, Array.getD_eq_getD_getElem?, List.size_toArray, List.length_nil,
      not_lt_zero, not_false_eq_true, getElem?_neg, Option.getD_none]

theorem arrB_empty (K : Nat) : ArrB K #[] := fun i => by simp only [getX_empty,
    Nat.default_eq_zero, pos K]

theorem arrB_default (K : Nat) : ArrB K default := arrB_empty K

/-! ### The candidate bound -/

/-- **The candidate word size**: `64·L` bits. -/
def wK (P : Params) : Nat := 64 * P.L

theorem pow_ge_mul (m : Nat) (hm : 8 ≤ m) : 32 * m ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih => rw [pow_succ]; omega

/-- `N < 2^L`. -/
theorem N_lt (N : Nat) : N < 2 ^ pL N :=
  lt_of_lt_of_le (Nat.lt_size_self N) (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))

/-- The group-label width: `HC ≤ 30L + 64` and `groupBits ≤ 31L + 67 ≤ 40L` (`L ≥ 8`). -/
theorem HC_le (N : Nat) : HC (proofParams N) ≤ 30 * pL N + 64 := by
  have hL := pL_ge N
  simp only [HC, csB, rsB, Mu, IC, kC, unitsOf, gmin, proofParams]
  generalize pL N = L at hL
  have hg : (2 * L - 2) / 2 = L - 1 := by omega
  rw [hg]
  have hq := costParameterQuotient_le hL
  generalize hu : 3 * L * L / (L - 1) = q at hq
  have hk := chunkParameterIndex_le hq
  generalize (q + 1) / 3 + 1 = k at hk
  have hcs := chunkParameterSplit_le hL hk
  generalize (3 * L * L + 2 * k) / (L - 1) = cs at hcs
  omega

theorem PC_le (N : Nat) : PC (proofParams N) ≤ 27 * pL N + 56 := by
  have hL := pL_ge N
  simp only [PC, csB, rsB, Mu, IC, kC, unitsOf, gmin, proofParams]
  generalize pL N = L at hL
  have hg : (2 * L - 2) / 2 = L - 1 := by omega
  rw [hg]
  have hq := costParameterQuotient_le hL
  generalize 3 * L * L / (L - 1) = q at hq
  have hk := chunkParameterIndex_le hq
  generalize (q + 1) / 3 + 1 = k at hk
  have hcs := chunkParameterSplit_le hL hk
  generalize (3 * L * L + 2 * k) / (L - 1) = cs at hcs
  omega

theorem Bg_le (N : Nat) : (proofParams N).groupBits ≤ 40 * pL N := by
  have hL := pL_ge N
  have h1 := HC_le N
  have h2 := PC_le N
  have hB : (proofParams N).groupBits = HC (proofParams N) + (Nat.log2 (PC (proofParams N)) +
    2) := rfl
  have hlog : Nat.log2 (PC (proofParams N)) ≤ pL N + 1 := by
    have hp : PC (proofParams N) < 2 ^ (pL N + 2) := by
      have := pow_ge_mul (pL N) hL
      rw [pow_add]; omega
    by_contra hc
    have : 2 ^ (pL N + 2) ≤ PC (proofParams N) :=
      le_trans (Nat.pow_le_pow_right (by norm_num) (by omega))
        (Nat.log2_self_le (by intro h0; rw [h0] at hc; simp only [Nat.log2_zero,
            le_add_iff_nonneg_left,
            zero_le, not_true_eq_false] at hc))
    omega
  omega

theorem UG_le (N : Nat) : UG (proofParams N) ≤ 4 * pL N := by
  have hL := pL_ge N
  simp only [UG, kG, gmin, proofParams]
  omega

theorem Be_le (N : Nat) : (proofParams N).elementBits ≤ 6 * pL N := by
  have hL := pL_ge N
  have hU := UG_le N
  have hB : (proofParams N).elementBits =
      UG (proofParams N) + (Nat.log2 (2 * pL N + (2 * pL N / 3 + 1)) + 2) := rfl
  have hlog : Nat.log2 (2 * pL N + (2 * pL N / 3 + 1)) ≤ pL N := by
    by_contra hc
    have h1 : 2 ^ (pL N + 1) ≤ 2 * pL N + (2 * pL N / 3 + 1) :=
      le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) (Nat.log2_self_le (by omega))
    have := pow_ge_mul (pL N) hL
    rw [pow_succ] at h1; omega
  omega

/-- **The proof parameters lie below the candidate bound**, with room for the intermediate
values: `elementBits + 1`, `groupBits + 1` and `(H + 2)·β` (a digit shifted past the top table)
  are at most
`wK`, and `2^UG`, `2^HC` (the label steps) are below `2^wK`. -/
theorem params_room (N : Nat) :
    (proofParams N).elementBits + 1 ≤ wK (proofParams N) ∧ (proofParams N).groupBits + 1 ≤ wK
      (proofParams N) ∧
      ((proofParams N).H + 2) * (proofParams N).beta ≤ wK (proofParams N) ∧
      UG (proofParams N) < wK (proofParams N) ∧ HC (proofParams N) < wK (proofParams N) ∧
      (proofParams N).N < 2 ^ (proofParams N).L := by
  have hL := pL_ge N
  have hU := UG_le N
  have hH := HC_le N
  have hE := Be_le N
  have hG := Bg_le N
  refine ⟨?_, ?_, ?_, ?_, ?_, N_lt N⟩ <;> simp only [wK] <;>
    try (first | (change _ ≤ 64 * pL N; omega) | (show _ < 64 * pL N; omega))
  change (pL N / 3 + 1 + 2) * 64 ≤ 64 * pL N
  omega

/-- `x < 2^m` and `m ≤ K` give `x < 2^K`. -/
theorem lt_pow_mono {x m K : Nat} (h : x < 2 ^ m) (hm : m ≤ K) : x < 2 ^ K :=
  lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) hm)

/-- **The parameters themselves are below `2^wK`.** -/
theorem params_wB (N : Nat) : ParamsB (wK (proofParams N)) (proofParams N) := by
  obtain ⟨hBe, hBg, hHb, hU, hHC, hN⟩ := params_room N
  have hL := pL_ge N
  have hK : wK (proofParams N) = 64 * pL N := rfl
  have small : ∀ x, x ≤ 64 * pL N → x < 2 ^ wK (proofParams N) := fun x hx =>
    lt_of_le_of_lt (le_trans hx (by rw [hK])) Nat.lt_two_pow_self
  have hL' : (proofParams N).L = pL N := rfl
  refine ⟨lt_pow_mono hN (by rw [hL', hK]; omega), small _ (by simp only [proofParams]; omega),
    small _ (by simp only [proofParams]; omega), ?_, ?_, small _ (by rw [← hK]; omega),
    small _ (by rw [← hK]; omega), ?_, ?_, small _ (by simp only [proofParams]; omega),
    small _ (by simp only [proofParams]; omega), small _ (by simp only [proofParams]; omega),
    small _ (by simp only [proofParams]; omega), small _ (by simp only [proofParams]; omega),
    small _ (by simp only [proofParams, Nat.ofNat_pos, le_mul_iff_one_le_right]; omega),
    small _ (by simp only [proofParams]; omega)⟩
  · -- T = 3L² < 2^(2L + 2) ≤ 2^wK
    have h1 : 3 * pL N * pL N < 2 ^ (2 * pL N + 2) := by
      have := pow_ge_mul (pL N) hL
      have h2 : 2 ^ (2 * pL N + 2) = 4 * (2 ^ pL N * 2 ^ pL N) := by rw [← pow_add]; ring
      rw [h2]; nlinarith
    exact lt_pow_mono h1 (by rw [hK]; omega)
  · have h1 : 2 * pL N * pL N < 2 ^ (2 * pL N + 2) := by
      have := pow_ge_mul (pL N) hL
      have h2 : 2 ^ (2 * pL N + 2) = 4 * (2 ^ pL N * 2 ^ pL N) := by rw [← pow_add]; ring
      rw [h2]; nlinarith
    exact lt_pow_mono h1 (by rw [hK]; omega)
  · exact Nat.pow_lt_pow_right (by norm_num) hU
  · exact Nat.pow_lt_pow_right (by norm_num) hHC

/-! ### The initial core -/

/-- The fresh core's lists respect any bound that the parameters and the two centre labels
respect. -/
theorem initState_wB {K : Nat} {P : Params} (hP : ParamsB K P) (hBe : P.elementBits ≤ K) (hBg :
  P.groupBits ≤ K)
    (hK : 1 ≤ K) : WB K (initState P) := by
  have p0 := pos K
  have h1 : 1 < 2 ^ K := Nat.one_lt_two_pow (by omega)
  have cE : 1 <<< (P.elementBits - 1) < 2 ^ K := by
    rw [Nat.shiftLeft_eq, one_mul]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have cG : 1 <<< (P.groupBits - 1) < 2 ^ K := by
    rw [Nat.shiftLeft_eq, one_mul]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  refine ⟨hP, ?_, ?_, ?_, ?_, by simp only [initState, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true], ?_, by simp only [initState, reduceCtorEq,
      IsEmpty.forall_iff,
      implies_true], by simp only [
      initState,
      reduceCtorEq,
      IsEmpty.forall_iff,
      implies_true], ?_,
    fun c => by simp only [initState, getX_empty]; exact arrB_default K,
    fun c t ht => (by simp only [initState, getX_empty] at ht; cases ht), arrB_empty K⟩
  · refine getX_of (elemB_default K) (fun x hx => ?_)
    simp only [initState, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact elemB_default K
    · exact ⟨p0, p0, h1, cE⟩
  · refine getX_of (groupB_default K) (fun x hx => ?_)
    simp only [initState, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact groupB_default K
    · exact ⟨p0, p0, h1, h1, h1, cG, h1, p0, p0, p0⟩
  · refine getX_of (chunkB_default K) (fun x hx => ?_)
    simp only [initState, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact chunkB_default K
    · exact ⟨p0, p0, h1, h1, h1, p0, p0, p0, p0⟩
  · refine getX_of (nodeB_default K) (fun x hx => ?_)
    simp only [initState, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx; exact nodeB_default K
  · simp only [initState]; exact ⟨h1, h1, h1, h1, h1, p0, p0, p0⟩
  · simp only [initState]
    exact ⟨arrB_empty K, arrB_empty K, arrB_empty K, arrB_empty K, arrB_empty K, arrB_empty K⟩

end OrderMaintenance.Proof.Word
