/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Word.PQ


/-!
# Theorem W, stage B1: the core's write sites

Stored-value bounds for the operations in `OrderMaintenance/Model/Core.lean`, excluding FALLBACK.
The classes of `docs/WORD.md` §2:
* **R** (a value read from the state, `NIL`, a constant, a sublist): no hypothesis.
* **Lab** (a label): bounded by the guards, given `LabRoom K P` (`elementBits, groupBits ≤ K`).
* **F** (a fresh index) and **Sz** (a size or count): the bound is a hypothesis of the lemma
  (`hy : y < 2 ^ K`, `hg : size + 1 < 2 ^ K`, ...). The cost invariants discharge it
  (`OrderMaintenance/Proof/Word/Hooks.lean`).

The pure state functions that the cost proof uses for each step (`linkElem`, `allocGroup`,
`linkGroupPair`, `sizeAdj`, `moveLState`, ..., `cmoveSizes`, `markState`) get lemmas
`wb_*`; the monadic functions get Hoare triples `ht_*`.
-/


@[expose] public section

namespace OrderMaintenance.Proof.Word

open OrderMaintenance.Model OrderMaintenance.Proof
/-- **Room for labels**: the label widths are at most `K`. -/
structure LabRoom (K : Nat) (P : Params) : Prop where
  K1 : 1 ≤ K
  Be : P.elementBits ≤ K
  Bg : P.groupBits ≤ K

theorem shift_lt {B K : Nat} (hB : B ≤ K) : 1 <<< B ≤ 2 ^ K := by
  rw [Nat.shiftLeft_eq, one_mul]; exact Nat.pow_le_pow_right (by norm_num) hB

theorem center_lt {B K : Nat} (hB : B ≤ K) (hK : 1 ≤ K ∨ 1 ≤ B) : 1 <<< (B - 1) < 2 ^ K := by
  rw [Nat.shiftLeft_eq, one_mul]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)

variable {K : Nat} {P0 : Params}

/-- The groups `u` take chunk `y` and the labels `labs`. -/
theorem allX_foldChk {y : Nat} (hy : y < 2 ^ K) :
    ∀ (u labs : List Nat) (a : Array Group), (∀ i, GroupB K (a.getX i)) →
      (∀ l ∈ labs, l < 2 ^ K) →
      ∀ i, GroupB K (((u.zip labs).foldl
        (fun a p => a.modify p.1 fun G => { G with chk := y, lab := p.2 }) a).getX i)
  | [], _, a, ha, _ => by simpa using ha
  | _ :: _, [], a, ha, _ => by simpa using ha
  | g :: u, l :: labs, a, ha, hl => by
    simp only [List.zip_cons_cons, List.foldl_cons]
    have hl0 : l < 2 ^ K := hl l (by simp)
    exact allX_foldChk hy u labs _ (allX_modify ha (fun X hX => by recb) g)
      (fun l' h' => hl l' (by simp [h']))

/-! ### Pure state functions -/

section pure
variable {s : Core} (h : WB K s)
include h

/-- Element insertion: the new index `y` (F), its label (Lab), the group size and the count (Sz). -/
theorem wb_linkElem {x y lab hh : Nat} (hx : x < 2 ^ K) (hy : y < 2 ^ K) (hl : lab < 2 ^ K)
    (hg : (s.Gs.getX (s.E.getX x).grp).size + 1 < 2 ^ K) (hc : s.count + 1 < 2 ^ K) :
    WB K (linkElem s x y lab hh) := by
  unfold linkElem; dsimp only; wbx h; all_goals wbv

/-- Group allocation: a free group (R) or the next index (F). -/
theorem wb_allocGroup {c : Nat} (hc : c < 2 ^ K) (hsz : s.freeG = [] → s.Gs.size < 2 ^ K) :
    WB K (allocGroup s c).2 ∧ (allocGroup s c).1 < 2 ^ K := by
  unfold allocGroup
  split
  · next i rest hf =>
    have hfr := h.freeG
    rw [hf] at hfr
    refine ⟨?_, hfr i (by simp)⟩
    dsimp only
    wbx h
    · exact allX_set! h.Gs (groupB_mk hc) i
    · exact fun g hg => hfr g (by simp [hg])
  · next hf =>
    refine ⟨?_, hsz hf⟩
    dsimp only
    wbx h
    exact allX_push h.Gs (groupB_mk hc)

theorem wb_linkGroupPair {g gl gr labL labR : Nat} (hg : g < 2 ^ K) (hgl : gl < 2 ^ K)
    (hgr : gr < 2 ^ K) (hL : labL < 2 ^ K) (hR : labR < 2 ^ K) :
    WB K (linkGroupPair s g gl gr labL labR) := by
  unfold linkGroupPair; dsimp only; wbx h; all_goals wbv

theorem wb_unlinkGroup {g : Nat} (hg : g < 2 ^ K) : WB K (unlinkGroup s g) := by
  unfold unlinkGroup; dsimp only; wbx h; all_goals wbv

theorem wb_moveFirstLeft {g gl e lab : Nat} (hgl : gl < 2 ^ K) (he : e < 2 ^ K)
    (hl : lab < 2 ^ K) : WB K (moveFirstLeft s g gl e lab) := by
  unfold moveFirstLeft; dsimp only; wbx h; all_goals wbv

theorem wb_moveLastRight {g gr e lab : Nat} (hgr : gr < 2 ^ K) (he : e < 2 ^ K)
    (hl : lab < 2 ^ K) : WB K (moveLastRight s g gr e lab) := by
  unfold moveLastRight; dsimp only; wbx h; all_goals wbv

/-- A size moved from `a` to `b`: the decrement is bounded by the old size (R), the increment
needs the bound (Sz). -/
theorem wb_sizeAdj {a b : Nat} (hb : (s.Gs.getX b).size + 1 < 2 ^ K) : WB K (sizeAdj s a b) := by
  unfold sizeAdj
  dsimp only
  wbx h
  refine allX_modify_at (allX_modify h.Gs (fun X hX => by recb) a) ?_
  rw [Array.getX_modify]
  split <;> (have := h.Gs b; recb)

theorem wb_sizeState {c : Nat} (hc : (s.C.getX c).size + 1 < 2 ^ K) : WB K (sizeState s c) := by
  unfold sizeState; wbx h; wbv

theorem wb_linkChunkPair {x y z : Nat} (hx : x < 2 ^ K) (hy : y < 2 ^ K) (hz : z < 2 ^ K) :
    WB K (linkChunkPair s x y z) := by
  unfold linkChunkPair; dsimp only; wbx h; all_goals wbv

theorem wb_markState {x y z : Nat} {job : Job} (hx : x < 2 ^ K) (hy : y < 2 ^ K) (hz : z < 2 ^ K)
    (hj : JobB K job) : WB K (markState s x y z job) := by
  unfold markState
  dsimp only
  wbx h
  rotate_left
  · intro j hj'; cases hj'; exact hj
  wbv

theorem wb_push2 : WB K (push2 s) := by
  unfold push2; wbx h; wbv

theorem wb_removeState {p : Nat} (hp : p < 2 ^ K) : WB K (removeState s p) := by
  have h1 := wb_unlinkGroup h hp
  unfold removeState quietG
  wbx h1; wbv

theorem wb_cremoveState {x : Nat} : WB K (cremoveState s x) := by
  unfold cremoveState deadC quietC; wbx h; wbv

theorem wb_moveGroupsLeft {x y : Nat} {u labs : List Nat} (hy : y < 2 ^ K)
    (hu : ∀ g ∈ u, g < 2 ^ K) (hl : ∀ l ∈ labs, l < 2 ^ K) :
    WB K (moveGroupsLeft s x y u labs) := by
  have h1 : u.headD NIL < 2 ^ K := by
    cases u with
    | nil => exact pos K
    | cons a t => exact hu a (by simp)
  have h2 : u.getLastD NIL < 2 ^ K := by
    rcases List.eq_nil_or_concat u with e | ⟨L, b, e⟩
    · subst e; exact pos K
    · subst e; simp only [List.concat_eq_append, List.getLastD_eq_getLast?,
      List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.getD_some]; exact hu
        b (by simp)
  unfold moveGroupsLeft
  wbx h
  · exact allX_foldChk hy u labs _ h.Gs hl
  · wbv

theorem wb_moveGroupsRight {x z : Nat} {u labs : List Nat} (hz : z < 2 ^ K)
    (hu : ∀ g ∈ u, g < 2 ^ K) (hl : ∀ l ∈ labs, l < 2 ^ K) :
    WB K (moveGroupsRight s x z u labs) := by
  have h1 : u.headD NIL < 2 ^ K := by
    cases u with
    | nil => exact pos K
    | cons a t => exact hu a (by simp)
  have h2 : u.getLastD NIL < 2 ^ K := by
    rcases List.eq_nil_or_concat u with e | ⟨L, b, e⟩
    · subst e; exact pos K
    · subst e; simp only [List.concat_eq_append, List.getLastD_eq_getLast?,
      List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.getD_some]; exact hu
        b (by simp)
  unfold moveGroupsRight
  wbx h
  · exact allX_foldChk hz u labs _ h.Gs hl
  · wbv

/-- Chunk sizes after a chunk-split move: the decrement is R, the increment needs the bound. -/
theorem wb_cmoveSizes {x dst : Nat} {u : List Nat}
    (hd : (s.C.getX dst).size + (u.map fun g => (s.Gs.getX g).size).sum < 2 ^ K) :
    WB K (cmoveSizes s x dst u) := by
  unfold cmoveSizes
  dsimp only
  wbx h
  refine allX_modify_at (allX_modify h.C (fun X hX => by recb) x) ?_
  rw [Array.getX_modify]
  split <;> (have := h.C dst; recb)

end pure


/-! ### Labels (class Lab) -/

theorem ht_between {a b : Nat} {why : String} (hb : b < 2 ^ K) :
    HT K P0 (between a b why) (· < 2 ^ K) := by
  unfold between; ht
  rename_i hc
  simp only [ge_iff_le, not_le] at hc
  omega

theorem ht_after {a D B : Nat} {why : String} (hB : B ≤ K) : HT K P0 (after a D B why) (· < 2 ^
  K) := by
  unfold after; ht
  rename_i hc
  have := shift_lt (B := B) hB
  simp only [ge_iff_le, Bool.or_eq_true, decide_eq_true_eq, not_or, not_le] at hc
  omega

theorem ht_before {b D : Nat} {why : String} (hb : b < 2 ^ K) : HT K P0 (before b D why) (· < 2
  ^ K) := by
  unfold before; ht
  exact lt_of_le_of_lt (Nat.sub_le _ _) hb

theorem ht_labBefore (g : Nat) : HT K P0 (labBefore g) (· < 2 ^ K) := by
  unfold labBefore
  refine HT.bind HT.getP fun P _ => HT.bind (HT.getG g) fun G hG => HT.bind (HT.getC _) fun C _
    => ?_
  split
  · exact ht_before (by vb)
  · exact HT.bind (HT.getG _) fun G' hG' => ht_between (by vb)

theorem ht_labAfter (g : Nat) (hL : LabRoom K P0) : HT K P0 (labAfter g) (· < 2 ^ K) := by
  unfold labAfter
  refine HT.bind HT.getP fun P hP => HT.bind (HT.getG g) fun G hG => HT.bind (HT.getC _) fun C _
    => ?_
  split
  · exact ht_after (by rw [hP.1]; exact hL.Bg)
  · exact HT.bind (HT.getG _) fun G' hG' => ht_between (by vb)

theorem ht_pushBackLabs {center D B : Nat} (hc : center < 2 ^ K) (hB : B ≤ K) :
    ∀ (prev : Option Nat) (k : Nat), HT K P0 (pushBackLabs center D B prev k) (fun l => ∀ a ∈ l,
      a < 2 ^ K)
  | _, 0 => by unfold pushBackLabs; exact HT.pure (by simp)
  | prev, k + 1 => by
    unfold pushBackLabs
    ht [ht_after hB, ht_pushBackLabs hc hB _ k]
    all_goals
      intro a ha
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · first | assumption | (subst_vars; assumption)
      · solve_by_elim

theorem ht_pushFrontLabs {center D : Nat} (hc : center < 2 ^ K) :
    ∀ (nxt : Option Nat), (∀ n, nxt = some n → n < 2 ^ K) → ∀ k : Nat,
      HT K P0 (pushFrontLabs center D nxt k) (fun l => ∀ a ∈ l, a < 2 ^ K)
  | _, _, 0 => by unfold pushFrontLabs; exact HT.pure (by simp)
  | nxt, hn, k + 1 => by
    unfold pushFrontLabs
    dsimp only
    split
    · refine HT.bind (HT.pure hc) fun l hl =>
        HT.bind (ht_pushFrontLabs hc _ (fun n e => by cases e; exact hl) k) fun r hr => HT.pure ?_
      intro a ha
      simp only [List.mem_append, List.mem_singleton] at ha
      rcases ha with ha | rfl
      · exact hr a ha
      · exact hl
    · next n =>
      refine HT.bind (ht_before (hn n rfl)) fun l hl =>
        HT.bind (ht_pushFrontLabs hc _ (fun n e => by cases e; exact hl) k) fun r hr => HT.pure ?_
      intro a ha
      simp only [List.mem_append, List.mem_singleton] at ha
      rcases ha with ha | rfl
      · exact hr a ha
      · exact hl

/-! ### Queries and deletion (class R) -/

theorem ht_markDead (x : Nat) : HT K P0 (markDead x) (fun _ => True) := by
  unfold markDead modE; ht; htfin

theorem ht_order (x y : Nat) : HT K P0 (order x y) (fun _ => True) := by
  intro s hs hP; rw [order_run]; exact ⟨⟨hs, hP⟩, trivial⟩

/-! ### Chunk sizes (class Sz) -/

/-- The size update of a chunk and the queue's: the increment needs the bound. -/
theorem wb_chunkSize {s : Core} (h : WB K s) {c : Nat} {inc : Bool} (hc : c < 2 ^ K)
    (hsz : inc = true → (s.C.getX c).size + 1 < 2 ^ K) :
    WB K (Result.state ((chunkSize c inc).run s)) := by
  have hnew : (if inc = true then (s.C.getX c).size + 1 else (s.C.getX c).size - 1) < 2 ^ K := by
    split
    · next hi => exact hsz hi
    · exact lt_of_le_of_lt (Nat.sub_le _ _) (h.cSize c)
  unfold chunkSize modC
  simp only [run_getC_bind, run_modify_bind]
  generalize (if inc = true then (s.C.getX c).size + 1 else (s.C.getX c).size - 1) = n at hnew ⊢
  have h1 : WB K { s with C := s.C.modify c fun C => { C with size := n } } := by
    wbx h; wbv
  split
  · exact (ht_pqAdjust (P0 := s.P) hc (h.cSize c) hnew).state h1 rfl |>.1
  · exact h1


/-! ### Element insertion -/

/-- **An element insertion** writes the new element with a label below `2^K` (Lab): the label
is below the next element's (`between`) or below `2^elementBits` (`after`). -/
theorem insertElem_wb {s : Core} (h : WB K s) (hL : LabRoom K s.P) {x hh y : Nat} {s' : Core}
    (hr : (insertElem x hh).run s = .ok y s') (hx : x < 2 ^ K) (hy : s.E.size < 2 ^ K)
    (hg : (s.Gs.getX (s.E.getX x).grp).size + 1 < 2 ^ K) (hc : s.count + 1 < 2 ^ K) :
    y = s.E.size ∧ WB K s' ∧ ∃ lab, s' = linkElem s x s.E.size lab hh := by
  have key : ∃ lab, lab < 2 ^ K ∧
      (insertElem x hh).run s = .ok s.E.size (linkElem s x s.E.size lab hh) := by
    unfold insertElem at hr ⊢
    simp only [run_getP_bind, run_getE_bind, run_getG_bind] at hr ⊢
    by_cases hl : x = (s.Gs.getX (s.E.getX x).grp).last
    · rw [ite_eq_left (beq_iff_eq.mpr hl), run_bind, run_after] at hr ⊢
      by_cases hgd : (s.E.getX x).lab + s.P.elementSpacing ≥ 1 <<< s.P.elementBits ∨
          (s.E.getX x).lab + s.P.elementSpacing ≤ (s.E.getX x).lab
      · rw [ite_eq_left hgd] at hr; cases hr
      · refine ⟨(s.E.getX x).lab + s.P.elementSpacing, ?_, ?_⟩
        · simp only [not_or] at hgd; have := shift_lt hL.Be; omega
        · rw [ite_eq_right hgd]; simp only [run_get_bind, run_modify_bind, run_pure]
    · rw [ite_eq_right (fun h => hl (beq_iff_eq.mp h))] at hr ⊢
      simp only [run_getE_bind] at hr ⊢
      rw [run_bind, run_between] at hr ⊢
      by_cases hgd : (s.E.getX x).lab + 1 ≥ (s.E.getX (s.E.getX x).next).lab
      · rw [ite_eq_left hgd] at hr; cases hr
      · refine ⟨((s.E.getX x).lab + (s.E.getX (s.E.getX x).next).lab) / 2, ?_, ?_⟩
        · have := h.eLab (s.E.getX x).next; omega
        · rw [ite_eq_right hgd]; simp only [run_get_bind, run_modify_bind, run_pure]
  obtain ⟨lab, hl, hrun⟩ := key
  rw [hrun] at hr
  cases hr
  exact ⟨rfl, wb_linkElem h hx hy hl hg hc, lab, rfl⟩

/-! ### Group splits -/

theorem allocGroup_size_le (s : Core) (c : Nat) : (allocGroup s c).2.Gs.size ≤ s.Gs.size + 1 := by
  unfold allocGroup; split <;> simp

theorem allocGroup_P' (s : Core) (c : Nat) : (allocGroup s c).2.P = s.P := by
  unfold allocGroup; split <;> rfl

/-- **A split start**: two fresh groups (F; room for two more groups is the hypothesis) and two
labels (Lab, from `labBefore`/`labAfter`). -/
theorem wb_splitState {s : Core} (h : WB K s) {g labL labR : Nat} (hg : g < 2 ^ K)
    (hlL : labL < 2 ^ K) (hlR : labR < 2 ^ K) (hroom : s.Gs.size + 2 ≤ 2 ^ K) :
    WB K (splitState s g labL labR) := by
  have hc : gC s g < 2 ^ K := h.gChk g
  have a1 := wb_allocGroup h hc (fun _ => by omega)
  have hs1 := allocGroup_size_le s (gC s g)
  have a2 := wb_allocGroup a1.1 hc (fun _ => by omega)
  exact wb_linkGroupPair a2.1 hg a1.2 a2.2 hlL hlR

/-- **A move of the first element of a splitting group to its left sibling**: the label (Lab,
from the room condition of the move) and the sibling's size (Sz, the hypothesis). -/
theorem wb_moveLState {s : Core} (h : WB K s) (hL : LabRoom K s.P) {p : Nat}
    (hroom : gF s (gLl s p) ≠ NIL → eL s (gLs s (gLl s p)) + s.P.elementSpacing < 1 <<<
      s.P.elementBits)
    (hsz : gSz s (gLl s p) + 1 < 2 ^ K) : WB K (moveLState s p) := by
  have hlab : labMoveL s p < 2 ^ K := by
    unfold labMoveL
    split
    · exact center_lt hL.Be (Or.inl hL.K1)
    · next hne => exact lt_of_lt_of_le (hroom hne) (shift_lt hL.Be)
  have h1 := wb_moveFirstLeft h (g := p) (h.gL p) (h.gFirst p) hlab
  unfold moveLState
  refine wb_sizeAdj h1 ?_
  have e : ((moveFirstLeft s p (gLl s p) (gF s p) (labMoveL s p)).Gs.getX (gLl s p)).size =
      gSz s (gLl s p) := by
    simp only [moveFirstLeft, Array.getX_modify, gSz]; split_ifs <;> rfl
  rw [e]; exact hsz

/-- The move to the right sibling. -/
theorem wb_moveRState {s : Core} (h : WB K s) (hL : LabRoom K s.P) {p : Nat}
    (hsz : gSz s (gRr s p) + 1 < 2 ^ K) : WB K (moveRState s p) := by
  have hlab : labMoveR s p < 2 ^ K := by
    unfold labMoveR
    split
    · exact center_lt hL.Be (Or.inl hL.K1)
    · exact lt_of_le_of_lt (Nat.sub_le _ _) (h.eLab _)
  have h1 := wb_moveLastRight h (g := p) (h.gR p) (h.gLast p) hlab
  unfold moveRState
  refine wb_sizeAdj h1 ?_
  have e : ((moveLastRight s p (gRr s p) (gLs s p) (labMoveR s p)).Gs.getX (gRr s p)).size =
      gSz s (gRr s p) := by
    simp only [moveLastRight, Array.getX_modify, gSz]; split_ifs <;> rfl
  rw [e]; exact hsz

/-! ### Chunk splits -/

theorem unitCand_lt {s : Core} (h : WB K s) (x : Nat) (left : Bool) :
    ∀ a ∈ unitCand s x left, a < 2 ^ K := by
  intro a ha
  unfold unitCand at ha
  dsimp only at ha
  repeat' split at ha
  all_goals
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    (try casesm* _ ∨ _)
  all_goals (subst_vars; vb)

theorem foldChk_size_eq {y : Nat} : ∀ (u labs : List Nat) (a : Array Group) (g : Nat),
    (((u.zip labs).foldl (fun a p => a.modify p.1 fun G => { G with chk := y, lab := p.2 })
      a).getX g).size =
      (a.getX g).size
  | [], _, a, g => by simp
  | _ :: _, [], a, g => by simp
  | b :: u, l :: labs, a, g => by
    simp only [List.zip_cons_cons, List.foldl_cons]
    rw [foldChk_size_eq u labs _ g, Array.getX_modify]; split <;> rfl

/-- **A chunk-split move to the left sibling**: the groups' labels (Lab), and the sibling's size
plus the moved groups' sizes (Sz, the hypothesis). -/
theorem wb_cmoveLState {s : Core} (h : WB K s) {x : Nat} {u labs : List Nat}
    (hu : ∀ g ∈ u, g < 2 ^ K) (hl : ∀ l ∈ labs, l < 2 ^ K)
    (hsz : cSz s (cLl s x) + (u.map fun g => gSz s g).sum < 2 ^ K) : WB K (cmoveLState s x u
      labs) := by
  have h1 := wb_moveGroupsLeft h (x := x) (h.cL x) hu hl
  unfold cmoveLState
  refine wb_cmoveSizes h1 ?_
  have eC : ((moveGroupsLeft s x (cLl s x) u labs).C.getX (cLl s x)).size = cSz s (cLl s x) := by
    simp only [moveGroupsLeft, Array.getX_modify, cSz]; split_ifs <;> rfl
  have eG : ∀ g, ((moveGroupsLeft s x (cLl s x) u labs).Gs.getX g).size = gSz s g := fun g =>
    foldChk_size_eq u labs s.Gs g
  rw [eC]; simp only [eG]; exact hsz

theorem wb_cmoveRState {s : Core} (h : WB K s) {x : Nat} {u labs : List Nat}
    (hu : ∀ g ∈ u, g < 2 ^ K) (hl : ∀ l ∈ labs, l < 2 ^ K)
    (hsz : cSz s (cRr s x) + (u.map fun g => gSz s g).sum < 2 ^ K) : WB K (cmoveRState s x u
      labs) := by
  have h1 := wb_moveGroupsRight h (x := x) (h.cR x) hu hl
  unfold cmoveRState
  refine wb_cmoveSizes h1 ?_
  have eC : ((moveGroupsRight s x (cRr s x) u labs).C.getX (cRr s x)).size = cSz s (cRr s x) := by
    simp only [moveGroupsRight, Array.getX_modify, cSz]; split_ifs <;> rfl
  have eG : ∀ g, ((moveGroupsRight s x (cRr s x) u labs).Gs.getX g).size = gSz s g := fun g =>
    foldChk_size_eq u labs s.Gs g
  rw [eC]; simp only [eG]; exact hsz

/-- The labels of a left move are below `2^K` (Lab: `after` with `groupBits ≤ K`, or the centre). -/
theorem ht_pushLabsL {s : Core} (hL : LabRoom K s.P) (x k : Nat) :
    HT K P0 (pushLabsL s x k) (fun l => ∀ a ∈ l, a < 2 ^ K) :=
  ht_pushBackLabs (center_lt hL.Bg (Or.inl hL.K1)) hL.Bg _ k

theorem ht_pushLabsR {s : Core} (h : WB K s) (hL : LabRoom K s.P) (x k : Nat) :
    HT K P0 (pushLabsR s x k) (fun l => ∀ a ∈ l, a < 2 ^ K) := by
  unfold pushLabsR
  refine ht_pushFrontLabs (center_lt hL.Bg (Or.inl hL.K1)) _ (fun n e => ?_) k
  split at e
  · cases e
  · cases e; exact h.gLab _

/-! ### Reservation: the split start's own writes -/

theorem wb_splitLink {t : Core} (h : WB K t) {x : Nat} (hx : x < 2 ^ K) (hroom : t.C.size + 2 ≤
  2 ^ K) :
    WB K (linkChunkPair (push2 t) x t.C.size (t.C.size + 1)) :=
  wb_linkChunkPair (wb_push2 h) hx (by omega) (by omega)

theorem jobB_copy {x y z : Nat} (hK : 1 ≤ K) (hx : x < 2 ^ K) (hy : y < 2 ^ K) (hz : z < 2 ^ K) :
    JobB K { x := x, y := y, z := z, pc := .copy 1 } :=
  ⟨hx, hy, hz, Nat.one_lt_two_pow (by omega)⟩


/-! ### Context-free triples for the remaining steps (classes R and Lab) -/

theorem ht_key (e : Nat) : HT K P0 (key e) (fun _ => True) := by
  unfold key; ht

theorem ht_unlinkStep {g : Nat} (hg : g < 2 ^ K) : HT K P0 (unlinkStep g) (fun _ => True) := by
  unfold unlinkStep
  ht
  intro t ht hP; exact ⟨wb_unlinkGroup ht hg, hP⟩

theorem ht_unit (x : Nat) (left : Bool) : HT K P0 (unit x left) (fun u => ∀ a ∈ u, a < 2 ^ K) := by
  unfold unit
  refine HT.bind HT.get fun st hst => ?_
  refine HT.ite (fun _ => HT.pure (unitCand_lt hst x left)) (fun _ => ?_)
  exact HT.bind HT.require fun _ _ => HT.pure (unitCand_lt hst x left)

theorem ht_markSplit {x y z : Nat} {job : Job} (hx : x < 2 ^ K) (hy : y < 2 ^ K) (hz : z < 2 ^ K)
    (hj : JobB K job) : HT K P0 (markSplit x y z job) (fun _ => True) := by
  intro s hs hP
  rw [markSplit_run]
  exact ⟨⟨wb_markState hs hx hy hz hj, hP⟩, trivial⟩

theorem ht_newChunk : HT K P0 newChunk (fun _ => True) := by
  intro s hs hP
  refine ⟨⟨?_, hP⟩, trivial⟩
  show WB K { s with C := s.C.push {} }
  wbx hs; wbv

/-- A chunk removal: the chunk dies, its siblings become quiet and may enter the queue (R). -/
theorem ht_removeChunk (x : Nat) : HT K P0 (removeChunk x) (fun _ => True) := by
  unfold removeChunk modC
  ht [ht_pqEnterIfAbove ?_]
  all_goals first
    | htfin
    | (simp only [List.mem_cons, List.not_mem_nil, or_false] at *
       casesm* _ ∨ _ <;> subst_vars <;> vb)

/-- A move of one element of a splitting group to a sibling (R, Lab). -/
theorem ht_moveElem (g : Nat) (hL : LabRoom K P0) : HT K P0 (moveElem g) (· < 2 ^ K) := by
  have hcenter := center_lt hL.Be (Or.inl hL.K1)
  unfold moveElem
  ht [ht_after hL.Be, ht_before ?_]
  all_goals first
    | htfin
    | (intro t ht hP; refine ⟨?_, hP⟩; first
        | exact wb_moveFirstLeft ht (by vb) (by vb) (by subst_vars; vb)
        | exact wb_moveLastRight ht (by vb) (by vb) (by subst_vars; vb))

/-- A chunk-split move of a unit of groups (R, Lab). -/
theorem ht_moveUnit (x : Nat) (left : Bool) (hL : LabRoom K P0) :
    HT K P0 (moveUnit x left) (fun r => r.1 < 2 ^ K ∧ ∀ a ∈ r.2, a < 2 ^ K) := by
  have hc := center_lt hL.Bg (Or.inl hL.K1)
  unfold moveUnit
  ht [ht_unit x left, ht_pushBackLabs hc hL.Bg _ _, ht_pushFrontLabs hc _ ?_ _]
  all_goals first
    | htfin
    | (intro t ht hP; refine ⟨?_, hP⟩; first
        | exact wb_moveGroupsLeft ht (by vb) ‹_› ‹_›
        | exact wb_moveGroupsRight ht (by vb) ‹_› ‹_›)
    | exact ⟨by vb, ‹_›⟩
    | (intro n hn; cases hn)
  vb

end OrderMaintenance.Proof.Word
