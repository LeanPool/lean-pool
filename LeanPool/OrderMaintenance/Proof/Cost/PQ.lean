/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Correct


/-!
# The bucket priority queue (`OrderMaintenance/Model/PQ.lean`)

`QRep s k inQ bl nb`: the queue of state `s` holds exactly the chunks `c` with `inQ c`, with key
`k c > θ`. Bucket `b` is the doubly linked list `bl b` (from `pqHead b` along `pqNext`, back along
`pqPrev`); the non-empty buckets form the increasing doubly linked list `nb` (from `pqLo` along
`nbNext`), and `pqHi` is its last bucket.

Results: adding and deleting keep the representation; the `+1` adjustment of a quiet chunk's size
never takes the slow path (K2); `pqPopMax` returns a chunk of largest key; `pqEmpty` is exact.
-/


@[expose] public section

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
structure QRep (s : Core) (k : Nat → Nat) (inQ : Nat → Bool) (bl : Nat → List Nat) (nb : List Nat) :
    Prop where
  where_ : ∀ c, s.pqWhere.getX c = if inQ c then k c else 0
  pos : ∀ c, inQ c = true → s.P.theta < k c
  bucket : ∀ b, LList (fun c => s.pqNext.getX c) (fun c => s.pqPrev.getX c) (s.pqHead.getX b) (bl b)
  bmem : ∀ b c, c ∈ bl b ↔ inQ c = true ∧ k c = b
  nbl : LList (fun b => s.nbNext.getX b) (fun b => s.nbPrev.getX b) s.pqLo nb
  nbmem : ∀ b, b ∈ nb ↔ bl b ≠ []
  sorted : nb.IsChain (· < ·)
  hi : s.pqHi = nb.getLastD 0

/-- The queue holds exactly `inQ`, keyed by `k`. -/
def QInv (s : Core) (k : Nat → Nat) (inQ : Nat → Bool) : Prop := ∃ bl nb, QRep s k inQ bl nb

/-! ### Linked lists under pointwise-equal links -/

theorem LList.congr {nxt prv nxt' prv' : Nat → Nat} {hd hd' : Nat} {l : List Nat}
    (h : LList nxt prv hd l) (hn : ∀ x ∈ l, nxt' x = nxt x) (hp : ∀ x ∈ l, prv' x = prv x)
    (hh : hd' = hd) : LList nxt' prv' hd' l :=
  ⟨h.nodup, h.nonil, hh ▸ h.head, fun x hx => (hn x hx).trans (h.next x hx),
   fun x hx => (hp x hx).trans (h.prev x hx)⟩

theorem LList.nil_iff {nxt prv : Nat → Nat} {hd : Nat} {l : List Nat} (h : LList nxt prv hd l) :
    l = [] ↔ hd = NIL := by
  constructor
  · rintro rfl; exact h.head
  · intro e
    cases l with
    | nil => rfl
    | cons a t => exfalso; have := h.head; simp only [List.headD_eq_head?_getD, List.head?_cons,
        Option.getD_some] at this; exact h.nonil (by rw [← this, e]; simp)

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### The operations as functions of the state -/

/-- `pqLinkAfter s p`: make bucket `s` non-empty, right after bucket `p` (0: at the front). -/
def linkSt (st : Core) (s p : Nat) : Core :=
  let n := if p = 0 then st.pqLo else st.nbNext.getX p
  let st1 : Core := if p = 0 then { st with pqLo := s } else
    { st with nbNext := st.nbNext.setX p s }
  let st2 : Core := { st1 with nbPrev := st1.nbPrev.setX s p, nbNext := st1.nbNext.setX s n }
  if n ≠ 0 then { st2 with nbPrev := st2.nbPrev.setX n s } else { st2 with pqHi := s }

/-- `pqAdd c s p`: push `c` at the head of bucket `s`. -/
def addSt (st : Core) (c s p : Nat) : Core :=
  let hd := st.pqHead.getX s
  let st1 : Core := if hd ≠ NIL then
      { st with pqNext := st.pqNext.setX c hd, pqPrev := (st.pqPrev.setX hd c).setX c NIL,
                pqHead := st.pqHead.setX s c }
    else linkSt { st with pqNext := st.pqNext.setX c NIL, pqPrev := st.pqPrev.setX c NIL,
                          pqHead := st.pqHead.setX s c } s p
  { st1 with pqWhere := st1.pqWhere.setX c s }

/-- `pqDel c`: remove `c` from its bucket, and the bucket from the list if it became empty. -/
def delSt (st : Core) (c : Nat) : Core :=
  let s := st.pqWhere.getX c
  let nx := st.pqNext.getX c
  let pv := st.pqPrev.getX c
  let st1 : Core := { st with pqWhere := st.pqWhere.setX c 0 }
  let st2 : Core := if pv ≠ NIL then { st1 with pqNext := st1.pqNext.setX pv nx }
    else { st1 with pqHead := st1.pqHead.setX s nx }
  let st3 : Core := if nx ≠ NIL then { st2 with pqPrev := st2.pqPrev.setX nx pv } else st2
  if st3.pqHead.getX s = NIL then
    let p := st3.nbPrev.getX s
    let n := st3.nbNext.getX s
    let st4 : Core := { st3 with nbPrev := st3.nbPrev.setX s 0, nbNext := st3.nbNext.setX s 0 }
    let st5 : Core := if p ≠ 0 then { st4 with nbNext := st4.nbNext.setX p n }
      else { st4 with pqLo := n }
    if n ≠ 0 then { st5 with nbPrev := st5.nbPrev.setX n p } else { st5 with pqHi := p }
  else st3

theorem pqLinkAfter_run (st : Core) (s p : Nat) :
    (pqLinkAfter s p).run st = .ok () (linkSt st s p) := by
  unfold pqLinkAfter linkSt
  by_cases hp : p = 0
  · subst hp
    by_cases hn : st.pqLo = 0 <;> simp only [BEq.rfl, ↓reduceIte, bne_iff_ne, ne_eq, ite_not,
        EStateM.run_bind, EStateM.run_get, hn,
        EStateM.run_modify, not_true_eq_false,
        not_false_eq_true]
  · by_cases hn : st.nbNext.getX p = 0 <;> simp only [beq_iff_eq, hp, ↓reduceIte, bne_iff_ne,
      ne_eq, ite_not, EStateM.run_bind,
      EStateM.run_get, hn, EStateM.run_modify,
      not_true_eq_false, not_false_eq_true]

theorem pqAdd_run (st : Core) (c s p : Nat) : (pqAdd c s p).run st = .ok () (addSt st c s p) := by
  unfold pqAdd addSt
  by_cases hh : st.pqHead.getX s = NIL
  · simp only [bne_iff_ne, ne_eq, ite_not, EStateM.run_bind, EStateM.run_get, hh, ↓reduceIte,
      EStateM.run_modify, pqLinkAfter_run, not_true_eq_false]
  · simp only [bne_iff_ne, ne_eq, ite_not, EStateM.run_bind, EStateM.run_get, hh, ↓reduceIte,
      EStateM.run_modify, not_false_eq_true]

theorem pqDel_run (st : Core) (c : Nat) (hw : st.pqWhere.getX c ≠ 0) :
    (pqDel c).run st = .ok () (delSt st c) := by
  unfold pqDel delSt
  simp only [run_get_bind]
  rw [ite_eq_right (by simpa using hw)]
  by_cases hpv : st.pqPrev.getX c = NIL <;> by_cases hnx : st.pqNext.getX c = NIL <;>
    simp only [hpv, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hnx, beq_iff_eq,
        bne_iff_ne, ne_eq, ite_not, EStateM.run_bind, EStateM.run_modify, EStateM.run_get,
        run_ite, EStateM.run_pure, not_true_eq_false, not_false_eq_true] <;> split_ifs <;> simp_all

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### Sorted lists -/

theorem sorted_split {l : List Nat} (hs : l.IsChain (· < ·)) (s : Nat) (hsl : s ∉ l) :
    l = l.filter (· < s) ++ l.filter (s < ·) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    have hst := (List.isChain_cons.mp hs).2
    have hat : ∀ b ∈ t, a < b := by
      have := List.isChain_iff_pairwise.mp hs; exact (List.pairwise_cons.mp this).1
    simp only [List.mem_cons, not_or] at hsl
    by_cases has : a < s
    · simp only [List.filter_cons, has, decide_true, ite_true]
      have : ¬ s < a := by omega
      simp only [this, decide_false, Bool.false_eq_true, ite_false, List.cons_append]
      congr 1; exact ih hst hsl.2
    · have hsa : s < a := by omega
      simp only [List.filter_cons, has, decide_false, Bool.false_eq_true, ite_false, hsa,
        decide_true,
        ite_true]
      have h1 : t.filter (· < s) = [] := by
        rw [List.filter_eq_nil_iff]; intro b hb; have := hat b hb; simp only [decide_eq_true_eq,
            not_lt, ge_iff_le]; omega
      have h2 : t.filter (s < ·) = t := by
        rw [List.filter_eq_self]; intro b hb; have := hat b hb; simp only [decide_eq_true_eq,
            gt_iff_lt]; omega
      rw [h1, h2]; rfl

theorem sorted_insert {l : List Nat} (hs : l.IsChain (· < ·)) (s : Nat) :
    (l.filter (· < s) ++ s :: l.filter (s < ·)).IsChain (· < ·) := by
  rw [List.isChain_iff_pairwise] at hs ⊢
  rw [List.pairwise_append, List.pairwise_cons]
  refine ⟨hs.sublist (List.filter_sublist), ⟨?_, hs.sublist (List.filter_sublist)⟩,
    fun a ha b hb => ?_⟩
  · intro b hb
    simp only [List.mem_filter, decide_eq_true_eq] at hb
    exact hb.2
  · simp only [List.mem_filter, decide_eq_true_eq] at ha
    simp only [List.mem_cons, List.mem_filter, decide_eq_true_eq] at hb
    rcases hb with rfl | ⟨_, hb⟩ <;> omega

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### Linking a bucket into the list of nonempty buckets -/

section link
variable (st : Core) (s p : Nat)

theorem linkSt_nbNext (b : Nat) : (linkSt st s p).nbNext.getX b =
    if b = s then (if p = 0 then st.pqLo else st.nbNext.getX p)
    else if p ≠ 0 ∧ b = p then s else st.nbNext.getX b := by
  unfold linkSt
  by_cases hp : p = 0 <;> simp only [hp] <;> split_ifs <;> simp_all [Array.getX_setX]

theorem linkSt_nbPrev (b : Nat) (hsn : s ≠ (if p = 0 then st.pqLo else st.nbNext.getX p)) :
    (linkSt st s p).nbPrev.getX b =
    if (if p = 0 then st.pqLo else st.nbNext.getX p) ≠ 0 ∧
      b = (if p = 0 then st.pqLo else st.nbNext.getX p)
    then s else if b = s then p else st.nbPrev.getX b := by
  unfold linkSt
  generalize hn : (if p = 0 then st.pqLo else st.nbNext.getX p) = n at hsn ⊢
  by_cases hp : p = 0 <;> simp only [hp, ite_true, ite_false] <;> split_ifs <;>
    simp_all [Array.getX_setX]

theorem linkSt_pqLo : (linkSt st s p).pqLo = if p = 0 then s else st.pqLo := by
  unfold linkSt
  by_cases hp : p = 0 <;> simp only [hp] <;> split_ifs <;> rfl

theorem linkSt_pqHi : (linkSt st s p).pqHi =
    if (if p = 0 then st.pqLo else st.nbNext.getX p) ≠ 0 then st.pqHi else s := by
  unfold linkSt
  by_cases hp : p = 0 <;> simp only [hp] <;> split_ifs <;> rfl

theorem linkSt_rest : (linkSt st s p).pqHead = st.pqHead ∧ (linkSt st s p).pqNext = st.pqNext ∧
    (linkSt st s p).pqPrev = st.pqPrev ∧ (linkSt st s p).pqWhere = st.pqWhere ∧
    (linkSt st s p).P = st.P := by
  unfold linkSt
  by_cases hp : p = 0 <;> simp only [hp] <;> split_ifs <;>
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end link

/-- After `linkSt` with the predecessor `p` and the successor bucket `n` of `s`: the new list. -/
theorem link_llist_core {st : Core} {nb1 nb2 : List Nat}
    (h : LList (fun b => st.nbNext.getX b) (fun b => st.nbPrev.getX b) st.pqLo (nb1 ++ nb2))
    {s p n : Nat} (hsn : s ∉ nb1 ++ nb2) (hs0 : s ≠ 0) (hp : p = nb1.getLastD 0)
    (hn : n = nb2.headD 0) (hn' : (if p = 0 then st.pqLo else st.nbNext.getX p) = n) :
    LList (fun b => (linkSt st s p).nbNext.getX b) (fun b => (linkSt st s p).nbPrev.getX b)
      (linkSt st s p).pqLo (nb1 ++ s :: nb2) := by
  have hsn' : s ≠ n := by
    rw [hn]; intro e
    cases nb2 with
    | nil => exact hs0 e
    | cons a t =>
      apply hsn
      simp only [List.headD_eq_head?_getD, List.head?_cons, Option.getD_some] at e
      simp only [e, List.mem_append, List.mem_cons, true_or, or_true]
  have hn0 : n ≠ 0 → n ∈ nb2 := by
    rw [hn]; intro h0
    cases nb2 with
    | nil => exact absurd rfl h0
    | cons a t => simp only [List.headD_eq_head?_getD, List.head?_cons, Option.getD_some,
        List.mem_cons, true_or]
  have hnext : ∀ b, (linkSt st s p).nbNext.getX b =
      if b = s then n else if p ≠ 0 ∧ b = p then s else st.nbNext.getX b := by
    intro b; rw [linkSt_nbNext, hn']
  have hprev : ∀ b, (linkSt st s p).nbPrev.getX b =
      if n ≠ 0 ∧ b = n then s else if b = s then p else st.nbPrev.getX b := by
    intro b; rw [linkSt_nbPrev st s p b (by rw [hn']; exact hsn'), hn']
  rcases nb1.eq_nil_or_concat with rfl | ⟨nb1', q, rfl⟩
  · have hp0 : p = 0 := by simpa using hp
    subst hp0
    simp only [List.nil_append] at h hsn ⊢
    have hlo : st.pqLo = n := by simpa using hn'
    rw [linkSt_pqLo, ite_eq_left rfl]
    refine LList.insert_front h hsn hs0 (fun z _ => ?_) (fun z hzm => ?_)
    · rw [hnext, hlo]; by_cases hz : z = s <;> simp only [hz, ↓reduceIte, ne_eq,
        not_true_eq_false, false_and]
    · rw [hprev, hlo]
      by_cases hz : z = s
      · subst hz; simp only [ne_eq, hsn', and_false, ↓reduceIte]
      · rw [ite_eq_right hz]
        by_cases hz2 : z = n
        · subst hz2; by_cases hz0 : z = 0
          · exfalso; subst hz0
            rcases List.mem_cons.mp hzm with e | e
            · exact hs0 e.symm
            · exact h.nonil e
          · simp only [ne_eq, hz0, not_false_eq_true, and_self, ↓reduceIte, hz]
        · simp only [ne_eq, hz2, and_false, ↓reduceIte, hz]
  · rw [List.concat_eq_append] at h hsn hp ⊢
    have hpq : p = q := by simpa using hp
    subst hpq
    have hq0 : p ≠ 0 := fun e => h.nonil (by rw [e]; simp)
    rw [linkSt_pqLo, ite_eq_right hq0]
    have h' : LList (fun b => st.nbNext.getX b) (fun b => st.nbPrev.getX b) st.pqLo
        (nb1' ++ p :: nb2) := by simpa using h
    have hsn2 : s ∉ nb1' ++ p :: nb2 := by simpa using hsn
    have hnq : st.nbNext.getX p = n := by simpa [hq0] using hn'
    have e : nb1' ++ [p] ++ s :: nb2 = nb1' ++ p :: s :: nb2 := by
      simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [e]
    refine LList.insert_after h' hsn2 hs0 (fun z _ => ?_) (fun z hzm => ?_)
    · simp only [hnext, hnq]
      by_cases hzp : z = p
      · subst hzp; simp only [show z ≠ s from fun e' => hsn2 (e' ▸ by simp), ↓reduceIte, ne_eq,
          hq0, not_false_eq_true, and_self]
      · by_cases hzs : z = s
        · subst hzs; simp only [↓reduceIte, hzp]
        · simp only [hzs, ↓reduceIte, ne_eq, hzp, and_false]
    · simp only [hprev, hnq]
      by_cases hzs : z = s
      · subst hzs; simp only [ne_eq, hsn', and_false, ↓reduceIte]
      · rw [ite_eq_right hzs]
        by_cases hz2 : z = n
        · subst hz2; by_cases hz0 : z = 0
          · exfalso; subst hz0
            have : (0 : Nat) ∈ nb1' ++ p :: nb2 := by
              simp only [List.mem_append, List.mem_cons] at hzm ⊢
              rcases hzm with h1 | h1 | h1 | h1
              · exact Or.inl h1
              · exact Or.inr (Or.inl h1)
              · exact absurd h1.symm hs0
              · exact Or.inr (Or.inr h1)
            exact h'.nonil this
          · simp only [ne_eq, hz0, not_false_eq_true, and_self, ↓reduceIte, hzs]
        · simp only [ne_eq, hz2, and_false, ↓reduceIte, hzs]

theorem link_llist {st : Core} {nb : List Nat}
    (h : LList (fun b => st.nbNext.getX b) (fun b => st.nbPrev.getX b) st.pqLo nb)
    (hs : nb.IsChain (· < ·)) {s p : Nat} (hsn : s ∉ nb) (hs0 : s ≠ 0)
    (hp : p = (nb.filter (· < s)).getLastD 0) :
    LList (fun b => (linkSt st s p).nbNext.getX b) (fun b => (linkSt st s p).nbPrev.getX b)
      (linkSt st s p).pqLo (nb.filter (· < s) ++ s :: nb.filter (s < ·)) ∧
    (linkSt st s p).pqHi = if nb.filter (s < ·) = [] then s else st.pqHi := by
  have hsplit := sorted_split hs s hsn
  generalize h1 : nb.filter (· < s) = nb1 at hp hsplit ⊢
  generalize h2 : nb.filter (s < ·) = nb2 at hsplit ⊢
  subst hsplit
  -- the bucket after `p`
  have hn : (if p = 0 then st.pqLo else st.nbNext.getX p) = nb2.headD 0 := by
    rcases nb1.eq_nil_or_concat with rfl | ⟨nb1', q, rfl⟩
    · have hp0 : p = 0 := by simpa using hp
      subst hp0; simp only [ite_true]; rw [h.head]; rfl
    · rw [List.concat_eq_append] at h hp
      have hpq : p = q := by simpa using hp
      rw [hpq]
      have hq0 : q ≠ 0 := fun e => h.nonil (by rw [e]; simp)
      rw [ite_eq_right hq0]
      have := h.next q (by simp)
      rw [this, show nb1' ++ [q] ++ nb2 = nb1' ++ q :: nb2 by simp, succOf_mid
        (by have := h.nodup; simpa using this)]
  refine ⟨link_llist_core h hsn hs0 hp rfl hn, ?_⟩
  rw [linkSt_pqHi, hn]
  cases nb2 with
  | nil => simp only [List.headD_eq_head?_getD, List.head?_nil, Option.getD_none, ne_eq,
      not_true_eq_false, ↓reduceIte]
  | cons a t =>
    have ha : a ≠ 0 := fun e => h.nonil (by
      simp only [e, List.mem_append, List.mem_cons, true_or, or_true])
    simp only [List.headD_eq_head?_getD, List.head?_cons, Option.getD_some, ne_eq, ha,
        not_false_eq_true, ↓reduceIte, reduceCtorEq]

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### Adding a chunk -/

theorem QRep.disj {st : Core} {k : Nat → Nat} {inQ : Nat → Bool} {bl : Nat → List Nat}
    {nb : List Nat} (hQ : QRep st k inQ bl nb) {a b c : Nat} (ha : c ∈ bl a) (hb : c ∈ bl b) :
    a = b := by
  rw [hQ.bmem] at ha hb; rw [← ha.2, ← hb.2]

theorem QRep.add {st : Core} {k : Nat → Nat} {inQ : Nat → Bool} {bl : Nat → List Nat}
    {nb : List Nat} (hQ : QRep st k inQ bl nb) {c s p : Nat} (hc : inQ c = false) (hc0 : c ≠ 0)
    (hs : st.P.theta < s) (hp : bl s = [] → p = (nb.filter (· < s)).getLastD 0) :
    QRep (addSt st c s p) (Function.update k c s) (Function.update inQ c true)
      (Function.update bl s (c :: bl s))
      (if bl s = [] then nb.filter (· < s) ++ s :: nb.filter (s < ·) else nb) := by
  have hcb : ∀ b, c ∉ bl b := fun b h => by rw [hQ.bmem] at h; rw [hc] at h; cases h.1
  have hs0 : s ≠ 0 := by omega
  have hsnb : s ∈ nb ↔ bl s ≠ [] := hQ.nbmem s
  -- the facts common to both cases
  have hwhere : ∀ (t : Core), t.pqWhere = st.pqWhere → ∀ d,
      (t.pqWhere.setX c s).getX d = if Function.update inQ c true d then Function.update k c s d
        else 0 := by
    intro t ht d; rw [ht, Array.getX_setX]
    by_cases hd : d = c
    · subst hd; simp only [↓reduceIte, Function.update_self]
    · simp only [ite_eq_right hd, Function.update_of_ne hd]; exact hQ.where_ d
  have hpos : ∀ d, Function.update inQ c true d = true → st.P.theta < Function.update k c s d := by
    intro d hd
    by_cases hdc : d = c
    · subst hdc; simpa using hs
    · rw [Function.update_of_ne hdc] at hd ⊢; exact hQ.pos d hd
  have hbmem : ∀ b d, d ∈ Function.update bl s (c :: bl s) b ↔
      Function.update inQ c true d = true ∧ Function.update k c s d = b := by
    intro b d
    by_cases hb : b = s
    · subst hb
      rw [Function.update_self]
      by_cases hd : d = c
      · subst hd; simp only [List.mem_cons, true_or, Function.update_self, and_self]
      · simp only [List.mem_cons, hd, false_or, Function.update_of_ne hd]; exact hQ.bmem b d
    · rw [Function.update_of_ne hb, hQ.bmem]
      by_cases hd : d = c
      · subst hd; simp only [hc, Bool.false_eq_true, false_and, Function.update_self, Ne.symm hb,
          and_false]
      · simp only [Function.update_of_ne hd]
  by_cases hbe : bl s = []
  · -- an empty bucket: link it in
    have hsn : s ∉ nb := fun h => (hsnb.mp h) hbe
    have hhd : st.pqHead.getX s = NIL := (hQ.bucket s).nil_iff.mp hbe
    let st0 : Core :=
        { st with
          pqNext := st.pqNext.setX c NIL
          pqPrev := st.pqPrev.setX c NIL
          pqHead := st.pqHead.setX s c }
    have hadd : addSt st c s p =
        { (linkSt st0 s p) with pqWhere := (linkSt st0 s p).pqWhere.setX c s } := by
      simp only [addSt, hhd, ne_eq, not_true_eq_false, ite_false]; rfl
    obtain ⟨r1, r2, r3, r4, r5⟩ := linkSt_rest st0 s p
    have hL := link_llist (st := st0) (nb := nb) hQ.nbl hQ.sorted hsn hs0 (hp hbe)
    rw [hadd, ite_eq_left hbe]
    refine ⟨hwhere _ r4, by rw [show (linkSt st0 s p).P = st.P from r5]; exact hpos, fun b => ?_,
      hbmem, hL.1, fun b => ?_, sorted_insert hQ.sorted s, ?_⟩
    · simp only [r1, r2, r3, st0, Array.getX_setX]
      by_cases hb : b = s
      · subst hb
        rw [Function.update_self, hbe]
        refine ⟨by simp, by simp only [List.mem_singleton]; exact fun h => hc0 h.symm, by simp,
          fun z hz => ?_, fun z hz => ?_⟩
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
          subst hz
          simp only [↓reduceIte, succOf]
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
          subst hz
          simp only [↓reduceIte, predOf, List.reverse_cons,
            List.reverse_nil, List.nil_append, succOf_single]
      · rw [Function.update_of_ne hb, ite_eq_right hb]
        refine (hQ.bucket b).congr (fun z hz => ?_) (fun z hz => ?_) rfl
        · rw [ite_eq_right (fun (e : z = c) => hcb b (e ▸ hz))]
        · rw [ite_eq_right (fun (e : z = c) => hcb b (e ▸ hz))]
    · by_cases hb : b = s
      · subst hb; simp only [List.mem_append, List.mem_filter, lt_self_iff_false, decide_false,
          Bool.false_eq_true, and_false, List.mem_cons, or_false, or_true,
          Function.update_self, ne_eq, reduceCtorEq, not_false_eq_true]
      · rw [Function.update_of_ne hb, ← hQ.nbmem b]
        simp only [List.mem_append, List.mem_cons, List.mem_filter, decide_eq_true_eq, hb, false_or]
        constructor
        · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
        · intro h
          rcases Nat.lt_or_gt_of_ne hb with h' | h'
          · exact Or.inl ⟨h, h'⟩
          · exact Or.inr ⟨h, h'⟩
    · change (linkSt st0 s p).pqHi = _
      rw [hL.2]
      have hsplit := sorted_split hQ.sorted s hsn
      by_cases h2 : nb.filter (s < ·) = []
      · rw [ite_eq_left h2, h2]; simp only [List.getLastD_eq_getLast?, List.getLast?_append,
          List.getLast?_singleton, List.getLast?_filter,
          Option.some_or, Option.getD_some]
      · rw [ite_eq_right h2, hQ.hi]
        conv_lhs => rw [hsplit]
        rcases (nb.filter (s < ·)).eq_nil_or_concat with h | ⟨l', a, h⟩
        · exact absurd h h2
        · rw [h, List.concat_eq_append]
          simp only [← List.append_assoc, List.getLastD_concat]
          rw [show nb.filter (· < s) ++ s :: (l' ++ [a]) = (nb.filter (· < s) ++ s :: l') ++ [a]
            by simp,
            List.getLastD_concat]
  · -- a non-empty bucket: push at its head
    have hhd : st.pqHead.getX s ≠ NIL := fun e => hbe ((hQ.bucket s).nil_iff.mpr e)
    have hadd : addSt st c s p =
        { st with
          pqNext := st.pqNext.setX c (st.pqHead.getX s)
          pqPrev := (st.pqPrev.setX (st.pqHead.getX s) c).setX c NIL
          pqHead := st.pqHead.setX s c
          pqWhere := st.pqWhere.setX c s } := by
      simp only [addSt, ne_eq, hhd, not_false_eq_true, ite_true]
    rw [hadd, ite_eq_right hbe]
    have hhdm : st.pqHead.getX s ∈ bl s := by
      have := (hQ.bucket s).head
      cases h : bl s with
      | nil => exact absurd h hbe
      | cons a t => rw [h] at this; simp only [List.headD_eq_head?_getD, List.head?_cons,
          Option.getD_some] at this; rw [this]; simp only [List.mem_cons, true_or]
    refine ⟨hwhere st rfl, hpos, fun b => ?_, hbmem, hQ.nbl, fun b => ?_, hQ.sorted, hQ.hi⟩
    · simp only [Array.getX_setX]
      by_cases hb : b = s
      · subst hb
        rw [Function.update_self, ite_eq_left rfl]
        refine LList.insert_front (hQ.bucket b) (hcb b) hc0 (fun z _ => ?_) (fun z _ => ?_)
        · rfl
        · by_cases hz : z = c
          · simp only [hz, ↓reduceIte]
          · simp only [hz, ↓reduceIte]
      · rw [Function.update_of_ne hb, ite_eq_right hb]
        refine (hQ.bucket b).congr (fun z hz => ?_) (fun z hz => ?_) rfl
        · show (if z = c then _ else _) = _
          rw [ite_eq_right (fun (e : z = c) => hcb b (e ▸ hz))]
        · have hzh : z ≠ st.pqHead.getX s := fun e => hb (hQ.disj hz (e ▸ hhdm))
          change (if z = c then _ else (if z = st.pqHead.getX s then _ else _)) = _
          rw [ite_eq_right (fun (e : z = c) => hcb b (e ▸ hz)), ite_eq_right hzh]
    · by_cases hb : b = s
      · subst hb; rw [Function.update_self]; simp only [ne_eq, reduceCtorEq, not_false_eq_true,
          iff_true]; exact hsnb.mpr hbe
      · rw [Function.update_of_ne hb]; exact hQ.nbmem b

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### Deleting a chunk -/

section del
variable (st : Core) (c : Nat)

/-- The bucket head after unlinking `c`, before the bucket list is touched. -/
def delHead : Array Nat :=
  if st.pqPrev.getX c ≠ NIL then st.pqHead
  else st.pqHead.setX (st.pqWhere.getX c) (st.pqNext.getX c)

theorem delSt_fields :
    (delSt st c).pqWhere = st.pqWhere.setX c 0 ∧
    (delSt st c).pqNext = (if st.pqPrev.getX c ≠ NIL then
      st.pqNext.setX (st.pqPrev.getX c) (st.pqNext.getX c) else st.pqNext) ∧
    (delSt st c).pqPrev = (if st.pqNext.getX c ≠ NIL then
      st.pqPrev.setX (st.pqNext.getX c) (st.pqPrev.getX c) else st.pqPrev) ∧
    (delSt st c).pqHead = delHead st c ∧ (delSt st c).P = st.P := by
  unfold delSt delHead
  by_cases h1 : st.pqPrev.getX c = NIL <;> by_cases h2 : st.pqNext.getX c = NIL <;>
    simp only [h1, h2, ne_eq, not_true_eq_false, not_false_eq_true, ite_true, ite_false] <;>
    split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem delSt_nb_keep (h : (delHead st c).getX (st.pqWhere.getX c) ≠ NIL) :
    (delSt st c).nbNext = st.nbNext ∧ (delSt st c).nbPrev = st.nbPrev ∧
    (delSt st c).pqLo = st.pqLo ∧ (delSt st c).pqHi = st.pqHi := by
  unfold delSt
  unfold delHead at h
  by_cases h1 : st.pqPrev.getX c = NIL <;> by_cases h2 : st.pqNext.getX c = NIL <;>
    simp only [h1, h2, ne_eq, not_true_eq_false, not_false_eq_true, ite_true, ite_false] at h ⊢ <;>
    rw [ite_eq_right h] <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem delSt_nb_drop (h : (delHead st c).getX (st.pqWhere.getX c) = NIL) :
    (∀ b, (delSt st c).nbNext.getX b =
      if st.nbPrev.getX (st.pqWhere.getX c) ≠ 0 ∧ b = st.nbPrev.getX (st.pqWhere.getX c) then
        st.nbNext.getX (st.pqWhere.getX c)
      else if b = st.pqWhere.getX c then 0 else st.nbNext.getX b) ∧
    (∀ b, (delSt st c).nbPrev.getX b =
      if st.nbNext.getX (st.pqWhere.getX c) ≠ 0 ∧ b = st.nbNext.getX (st.pqWhere.getX c) then
        st.nbPrev.getX (st.pqWhere.getX c)
      else if b = st.pqWhere.getX c then 0 else st.nbPrev.getX b) ∧
    (delSt st c).pqLo = (if st.nbPrev.getX (st.pqWhere.getX c) ≠ 0 then st.pqLo
      else st.nbNext.getX (st.pqWhere.getX c)) ∧
    (delSt st c).pqHi = (if st.nbNext.getX (st.pqWhere.getX c) ≠ 0 then st.pqHi
      else st.nbPrev.getX (st.pqWhere.getX c)) := by
  unfold delSt
  unfold delHead at h
  generalize st.pqWhere.getX c = s at h ⊢
  generalize hp : st.nbPrev.getX s = p
  generalize hn : st.nbNext.getX s = n
  by_cases h1 : st.pqPrev.getX c = NIL <;> by_cases h2 : st.pqNext.getX c = NIL <;>
    simp only [h1, h2, ne_eq, not_true_eq_false, not_false_eq_true, ite_true, ite_false] at h ⊢ <;>
    rw [ite_eq_left h] <;> simp only [hp, hn] <;>
    refine ⟨fun b => ?_, fun b => ?_, ?_, ?_⟩ <;>
    by_cases hp0 : p = 0 <;> by_cases hn0 : n = 0 <;> simp only [hn0, not_true_eq_false,
        ↓reduceIte, hp0, Array.getX_setX,
        false_and, not_false_eq_true,
        true_and]

end del

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
theorem getLastD_append_ne {l1 l2 : List Nat} (h : l2 ≠ []) (d : Nat) :
    (l1 ++ l2).getLastD d = l2.getLastD d := by
  rcases l2.eq_nil_or_concat with rfl | ⟨l', a, rfl⟩
  · exact absurd rfl h
  · rw [List.concat_eq_append, ← List.append_assoc, List.getLastD_concat, List.getLastD_concat]

/-- Unlinking a queued chunk erases it from its bucket’bucket doubly linked list. -/
theorem delSt_bucket_erase {st : Core} {c bucket : Nat} {before after : List Nat}
    (hw : st.pqWhere.getX c = bucket)
    (hB : LList (fun z => st.pqNext.getX z) (fun z => st.pqPrev.getX z)
      (st.pqHead.getX bucket) (before ++ c :: after)) :
    LList (fun z => (delSt st c).pqNext.getX z) (fun z => (delSt st c).pqPrev.getX z)
      ((delSt st c).pqHead.getX bucket) (before ++ after) := by
  obtain ⟨_, f2, f3, f4, _⟩ := delSt_fields st c
  have := LList.erase (nxt' := fun z => (delSt st c).pqNext.getX z)
    (prv' := fun z => (delSt st c).pqPrev.getX z) hB (fun z hz => ?_) (fun z hz => ?_)
  · refine this.congr (fun _ _ => rfl) (fun _ _ => rfl) ?_
    rw [f4]; unfold delHead; rw [hw]
    by_cases h : st.pqPrev.getX c = NIL
    · rw [ite_eq_right (by simpa using h), ite_eq_left h, Array.getX_setX, ite_eq_left rfl]
    · rw [ite_eq_left h, ite_eq_right h]
  · have hz0 : z ≠ NIL := fun e => hB.nonil (by
      rw [← e]
      simp only [List.mem_append, List.mem_cons] at hz ⊢
      tauto)
    simp only [f2]
    by_cases h : st.pqPrev.getX c = NIL
    · rw [ite_eq_right (by simpa using h)]; simp only [h]; rw [ite_eq_right hz0]
    · rw [ite_eq_left h, Array.getX_setX]
  · have hz0 : z ≠ NIL := fun e => hB.nonil (by
      rw [← e]
      simp only [List.mem_append, List.mem_cons] at hz ⊢
      tauto)
    simp only [f3]
    by_cases h : st.pqNext.getX c = NIL
    · rw [ite_eq_right (by simpa using h)]; simp only [h]; rw [ite_eq_right hz0]
    · rw [ite_eq_left h, Array.getX_setX]

theorem QRep.del {st : Core} {k : Nat → Nat} {inQ : Nat → Bool} {bl : Nat → List Nat}
    {nb : List Nat} (hQ : QRep st k inQ bl nb) {c : Nat} (hc : inQ c = true) :
    QRep (delSt st c) k (Function.update inQ c false)
      (Function.update bl (k c) ((bl (k c)).erase c))
      (if (bl (k c)).erase c = [] then nb.erase (k c) else nb) := by
  have hw : st.pqWhere.getX c = k c := by rw [hQ.where_, hc]; rfl
  generalize hs : k c = s at hw ⊢
  have hcm : c ∈ bl s := (hQ.bmem s c).mpr ⟨hc, hs⟩
  obtain ⟨l1, l2, hsplit⟩ := List.mem_iff_append.mp hcm
  have hB := hQ.bucket s
  rw [hsplit] at hB
  have hnd := hB.nodup
  have hpv : st.pqPrev.getX c = l1.getLastD NIL := by rw [hB.prev c (by simp), predOf_mid hnd]
  have hnx : st.pqNext.getX c = l2.headD NIL := by rw [hB.next c (by simp), succOf_mid hnd]
  have herase : (bl s).erase c = l1 ++ l2 := by
    rw [hsplit,
      List.erase_append_right _ (fun h => (List.nodup_append.mp hnd).2.2 c h c (by simp) rfl)]
    simp only [List.erase_cons_head]
  obtain ⟨f1, f2, f3, f4, f5⟩ := delSt_fields st c
  -- the bucket of `c` after unlinking
  have hB' := delSt_bucket_erase hw hB
  have hcb : ∀ b, b ≠ s → c ∉ bl b := fun b hb h => hb (hQ.disj h hcm)
  have hpvm : st.pqPrev.getX c = NIL ∨ st.pqPrev.getX c ∈ bl s := by
    rw [hpv, hsplit]; rcases l1.eq_nil_or_concat with rfl | ⟨l', a, rfl⟩
    · left; rfl
    · right; simp only [List.concat_eq_append, List.append_assoc, List.cons_append,
        List.nil_append, List.getLastD_eq_getLast?, List.getLast?_append,
        List.getLast?_singleton, Option.some_or, Option.getD_some, List.mem_append,
        List.mem_cons, true_or, or_true]
  have hnxm : st.pqNext.getX c = NIL ∨ st.pqNext.getX c ∈ bl s := by
    rw [hnx, hsplit]; cases l2 with
    | nil => left; rfl
    | cons a t => right; simp only [List.headD_eq_head?_getD, List.head?_cons, Option.getD_some,
        List.mem_append, List.mem_cons, true_or, or_true]
  have hbucket : ∀ b, b ≠ s → LList (fun z => (delSt st c).pqNext.getX z)
      (fun z => (delSt st c).pqPrev.getX z) ((delSt st c).pqHead.getX b) (bl b) := by
    intro b hb
    refine (hQ.bucket b).congr (fun z hz => ?_) (fun z hz => ?_) ?_
    · have h1 : z ≠ st.pqPrev.getX c := by
        intro e; rcases hpvm with h | h
        · exact (hQ.bucket b).nonil (by rw [← h, ← e]; exact hz)
        · exact hb (hQ.disj hz (e ▸ h))
      simp only [f2]; split <;> simp only [Array.getX_setX, h1, ↓reduceIte]
    · have h1 : z ≠ st.pqNext.getX c := by
        intro e; rcases hnxm with h | h
        · exact (hQ.bucket b).nonil (by rw [← h, ← e]; exact hz)
        · exact hb (hQ.disj hz (e ▸ h))
      simp only [f3]; split <;> simp only [Array.getX_setX, h1, ↓reduceIte]
    · rw [f4]; unfold delHead; rw [hw]; split <;> simp only [Array.getX_setX, hb, ↓reduceIte]
  have hsnb : s ∈ nb := (hQ.nbmem s).mpr (by rw [hsplit]; simp)
  rw [herase]
  by_cases hemp : l1 ++ l2 = []
  · -- the bucket became empty: drop it from the list
    rw [ite_eq_left hemp]
    have hdh : (delHead st c).getX (st.pqWhere.getX c) = NIL := by
      rw [hw, ← f4]; exact hB'.nil_iff.mp hemp
    obtain ⟨g1, g2, g3, g4⟩ := delSt_nb_drop st c hdh
    rw [hw] at g1 g2 g3 g4
    obtain ⟨n1, n2, hnsplit⟩ := List.mem_iff_append.mp hsnb
    have hN := hQ.nbl
    rw [hnsplit] at hN
    have hnnd := hN.nodup
    have hps : st.nbPrev.getX s = n1.getLastD 0 := by rw [hN.prev s (by simp), predOf_mid hnnd]
    have hns : st.nbNext.getX s = n2.headD 0 := by rw [hN.next s (by simp), succOf_mid hnnd]
    have hnerase : nb.erase s = n1 ++ n2 := by
      rw [hnsplit,
        List.erase_append_right _ (fun h => (List.nodup_append.mp hnnd).2.2 s h s (by simp) rfl)]
      simp only [List.erase_cons_head]
    rw [hnerase]
    have hN' := LList.erase (nxt' := fun b => (delSt st c).nbNext.getX b)
      (prv' := fun b => (delSt st c).nbPrev.getX b) hN (fun z hz => ?_) (fun z hz => ?_)
    rotate_left
    · have hz0 : z ≠ 0 := fun e => hN.nonil (by
        have : z ∈ n1 ++ s :: n2 := by simp only [List.mem_append, List.mem_cons] at hz ⊢; tauto
        rw [e] at this; exact this)
      have hzs : z ≠ s := fun e => by
        rw [e] at hz; exact (List.nodup_middle.mp hnnd |> List.nodup_cons.mp).1 hz
      simp only [g1]
      by_cases hp0 : st.nbPrev.getX s = 0
      · simp only [hp0, ne_eq, not_true_eq_false, hz0, and_self, ↓reduceIte, hzs]
      · simp only [ne_eq, hp0, not_false_eq_true, true_and, hzs, ↓reduceIte]
    · have hz0 : z ≠ 0 := fun e => hN.nonil (by
        have : z ∈ n1 ++ s :: n2 := by simp only [List.mem_append, List.mem_cons] at hz ⊢; tauto
        rw [e] at this; exact this)
      have hzs : z ≠ s := fun e => by
        rw [e] at hz; exact (List.nodup_middle.mp hnnd |> List.nodup_cons.mp).1 hz
      simp only [g2]
      by_cases hn0 : st.nbNext.getX s = 0
      · simp only [hn0, ne_eq, not_true_eq_false, hz0, and_self, ↓reduceIte, hzs]
      · simp only [ne_eq, hn0, not_false_eq_true, true_and, hzs, ↓reduceIte]
    refine ⟨fun d => ?_, fun d hd => ?_, fun b => ?_, fun b d => ?_, ?_, fun b => ?_, ?_, ?_⟩
    · rw [f1, Array.getX_setX]
      by_cases hd : d = c
      · subst hd; simp only [↓reduceIte, Function.update_self, Bool.false_eq_true]
      · simp only [ite_eq_right hd, Function.update_of_ne hd]; exact hQ.where_ d
    · rw [f5]
      by_cases hdc : d = c
      · subst hdc; simp only [Function.update_self, Bool.false_eq_true] at hd
      · rw [Function.update_of_ne hdc] at hd; exact hQ.pos d hd
    · by_cases hb : b = s
      · subst hb; rw [Function.update_self]; exact hB'
      · rw [Function.update_of_ne hb]; exact hbucket b hb
    · by_cases hb : b = s
      · subst hb; rw [Function.update_self, hemp]
        simp only [List.not_mem_nil, false_iff, not_and]
        intro hd hk
        by_cases hdc : d = c
        · subst hdc; simp only [Function.update_self, Bool.false_eq_true] at hd
        · rw [Function.update_of_ne hdc] at hd
          have := (hQ.bmem b d).mpr ⟨hd, hk⟩
          rw [← herase] at hemp
          have hmem : d ∈ (bl b).erase c := (List.mem_erase_of_ne hdc).mpr this
          rw [hemp] at hmem; simp only [List.not_mem_nil] at hmem
      · rw [Function.update_of_ne hb, hQ.bmem]
        by_cases hdc : d = c
        · subst hdc; simp only [hc, hs, Ne.symm hb, and_false, Function.update_self,
            Bool.false_eq_true, and_self]
        · rw [Function.update_of_ne hdc]
    · refine hN'.congr (fun _ _ => rfl) (fun _ _ => rfl) ?_
      rw [g3, hps]
      rcases n1.eq_nil_or_concat with rfl | ⟨n1', q, rfl⟩
      · simp only [List.getLastD_eq_getLast?, List.getLast?_nil, Option.getD_none, ne_eq,
          not_true_eq_false, ↓reduceIte]
      · have hq0 : q ≠ 0 := fun e => hN.nonil (by rw [e]; simp)
        simp only [List.concat_eq_append, List.getLastD_eq_getLast?, List.getLast?_append,
            List.getLast?_singleton, Option.some_or, Option.getD_some, ne_eq, hq0,
            not_false_eq_true, ↓reduceIte]
    · by_cases hb : b = s
      · subst hb; rw [Function.update_self, hemp]
        simp only [ne_eq, not_true_eq_false, iff_false]
        exact (List.nodup_middle.mp hnnd |> List.nodup_cons.mp).1
      · rw [Function.update_of_ne hb, ← hQ.nbmem b, hnsplit]
        simp only [List.mem_append, List.mem_cons, hb, false_or]
    · have := hQ.sorted
      rw [hnsplit, List.isChain_iff_pairwise] at this
      rw [List.isChain_iff_pairwise]
      exact this.sublist (List.Sublist.append_left (List.sublist_cons_self s n2) n1)
    · rw [g4, hns, hps]
      cases n2 with
      | nil => simp only [List.headD_eq_head?_getD, List.head?_nil, Option.getD_none, ne_eq,
          not_true_eq_false, ↓reduceIte, List.getLastD_eq_getLast?,
          List.append_nil]
      | cons a t =>
        have ha : a ≠ 0 := fun e => hN.nonil (by
          simp only [e, List.mem_append, List.mem_cons, true_or, or_true])
        simp only [List.headD_cons, ne_eq, ha, not_false_eq_true, ite_true]
        rw [hQ.hi, hnsplit, show n1 ++ s :: a :: t = (n1 ++ [s]) ++ a :: t by simp,
          getLastD_append_ne (by simp), getLastD_append_ne (by simp)]
  · -- the bucket stays: the list of buckets is unchanged
    rw [ite_eq_right hemp]
    have hdh : (delHead st c).getX (st.pqWhere.getX c) ≠ NIL := by
      rw [hw, ← f4]; exact fun e => hemp (hB'.nil_iff.mpr e)
    obtain ⟨g1, g2, g3, g4⟩ := delSt_nb_keep st c hdh
    refine ⟨fun d => ?_, fun d hd => ?_, fun b => ?_, fun b d => ?_, ?_, fun b => ?_, hQ.sorted, ?_⟩
    · rw [f1, Array.getX_setX]
      by_cases hd : d = c
      · subst hd; simp only [↓reduceIte, Function.update_self, Bool.false_eq_true]
      · simp only [ite_eq_right hd, Function.update_of_ne hd]; exact hQ.where_ d
    · rw [f5]
      by_cases hdc : d = c
      · subst hdc; simp only [Function.update_self, Bool.false_eq_true] at hd
      · rw [Function.update_of_ne hdc] at hd; exact hQ.pos d hd
    · by_cases hb : b = s
      · subst hb; rw [Function.update_self]; exact hB'
      · rw [Function.update_of_ne hb]; exact hbucket b hb
    · by_cases hb : b = s
      · subst hb; rw [Function.update_self, ← herase]
        by_cases hdc : d = c
        · subst hdc
          simp only [Function.update_self, Bool.false_eq_true, false_and, iff_false]
          exact List.Nodup.not_mem_erase (hsplit ▸ hnd)
        · rw [List.mem_erase_of_ne hdc, Function.update_of_ne hdc]; exact hQ.bmem b d
      · rw [Function.update_of_ne hb, hQ.bmem]
        by_cases hdc : d = c
        · subst hdc; simp only [hc, hs, Ne.symm hb, and_false, Function.update_self,
            Bool.false_eq_true, and_self]
        · rw [Function.update_of_ne hdc]
    · rw [g1, g2, g3]; exact hQ.nbl
    · by_cases hb : b = s
      · subst hb; rw [Function.update_self]; simp only [ne_eq]; exact ⟨fun _ => hemp, fun _ => hsnb⟩
      · rw [Function.update_of_ne hb]; exact hQ.nbmem b
    · rw [g4]; exact hQ.hi

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### Only queue fields change -/

/-- `st'` differs from `st` at most in the queue's fields. -/
structure PQOnly (st st' : Core) : Prop where
  E : st'.E = st.E
  Gs : st'.Gs = st.Gs
  C : st'.C = st.C
  P : st'.P = st.P
  rest : st'.freeG = st.freeG ∧ st'.count = st.count ∧ st'.head = st.head ∧ st'.tail = st.tail ∧
    st'.firstGroup = st.firstGroup ∧ st'.firstChunk = st.firstChunk ∧ st'.ready = st.ready ∧
    st'.prep = st.prep ∧ st'.resJob = st.resJob ∧ st'.fallbacks = st.fallbacks ∧
    st'.nodes = st.nodes ∧ st'.path = st.path ∧ st'.cin = st.cin ∧
    st'.lpar = st.lpar

theorem PQOnly.refl (st : Core) : PQOnly st st :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem PQOnly.trans {a b c : Core} (h1 : PQOnly a b) (h2 : PQOnly b c) : PQOnly a c := by
  obtain ⟨e1, g1, c1, p1, r1⟩ := h1
  obtain ⟨e2, g2, c2, p2, r2⟩ := h2
  refine ⟨e2.trans e1, g2.trans g1, c2.trans c1, p2.trans p1, ?_⟩
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩ := r1
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14⟩ := r2
  exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5, b6.trans a6,
    b7.trans a7, b8.trans a8, b9.trans a9, b10.trans a10, b11.trans a11, b12.trans a12,
    b13.trans a13, b14.trans a14⟩

theorem linkSt_only (st : Core) (s p : Nat) : PQOnly st (linkSt st s p) := by
  unfold linkSt
  dsimp only
  split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem addSt_only (st : Core) (c s p : Nat) : PQOnly st (addSt st c s p) := by
  unfold addSt
  dsimp only
  split_ifs
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · let st0 : Core :=
      { st with
        pqNext := st.pqNext.setX c NIL
        pqPrev := st.pqPrev.setX c NIL
        pqHead := st.pqHead.setX s c }
    obtain ⟨e, g, c', p', r⟩ := linkSt_only st0 s p
    exact ⟨e, g, c', p', r⟩

theorem delSt_only (st : Core) (c : Nat) : PQOnly st (delSt st c) := by
  unfold delSt; dsimp only; split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### The operations used by the algorithm -/

theorem pqInsertScan_min (st : Core) (c : Nat) :
    (pqInsertScan c (st.P.theta + 1)).run st = .ok () (addSt st c (st.P.theta + 1) 0) := by
  unfold pqInsertScan
  simp only [run_get_bind, Nat.add_sub_cancel, List.range_succ_eq_map, List.forIn_cons]
  rw [run_bind, run_bind]
  simp only [gt_iff_lt, lt_self_iff_false, decide_false, Bool.false_and, Bool.false_eq_true,
      ↓reduceIte, EStateM.run_pure, pqAdd_run]

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-- The bucket list's elements below `s`: all of them are below `s + 1` too, minus `s`. -/
theorem filter_lt_succ_erase {nb : List Nat} (hnd : nb.Nodup) (s : Nat) :
    (nb.erase s).filter (· < s + 1) = nb.filter (· < s) := by
  induction nb with
  | nil => simp only [List.erase_nil, List.filter_nil]
  | cons a t ih =>
    simp only [List.nodup_cons] at hnd
    by_cases has : a = s
    · subst has
      simp only [List.erase_cons_head, List.filter_cons, lt_irrefl, decide_false,
        Bool.false_eq_true, ite_false]
      exact List.filter_congr (fun x hx => by
        have : x ≠ a := fun e => hnd.1 (e ▸ hx); simp only [decide_eq_decide]; omega)
    · rw [List.erase_cons_tail (by simpa using has)]
      simp only [List.filter_cons]
      have : decide (a < s + 1) = decide (a < s) := by simp only [decide_eq_decide]; omega
      rw [this, ih hnd.2]

theorem sorted_split_mem {l : List Nat} (hs : l.IsChain (· < ·)) {s : Nat} (hsl : s ∈ l) :
    l = l.filter (· < s) ++ s :: l.filter (s < ·) := by
  induction l with
  | nil => simp only [List.not_mem_nil] at hsl
  | cons a t ih =>
    have hst := (List.isChain_cons.mp hs).2
    have hat : ∀ b ∈ t, a < b := by
      have := List.isChain_iff_pairwise.mp hs; exact (List.pairwise_cons.mp this).1
    rcases List.mem_cons.mp hsl with rfl | hst'
    · simp only [List.filter_cons, lt_irrefl, decide_false, Bool.false_eq_true, ite_false]
      have h1 : t.filter (· < s) = [] := by
        rw [List.filter_eq_nil_iff]; intro b hb; have := hat b hb; simp only [decide_eq_true_eq,
            not_lt, ge_iff_le]; omega
      have h2 : t.filter (s < ·) = t := by
        rw [List.filter_eq_self]; intro b hb; have := hat b hb; simp only [decide_eq_true_eq,
            gt_iff_lt]; omega
      rw [h1, h2]; rfl
    · have has : a < s := hat s hst'
      simp only [List.filter_cons, has, decide_true, ite_true]
      have : ¬ s < a := by omega
      simp only [this, decide_false, Bool.false_eq_true, ite_false, List.cons_append]
      congr 1; exact ih hst hst'

/-- **Lemma K2 for insertions.** Adjusting a quiet chunk's key by `+1` keeps the representation
and never scans. -/
theorem pqAdjust_inc {st : Core} {k : Nat → Nat} {inQ : Nat → Bool} {bl : Nat → List Nat}
    {nb : List Nat} (hQ : QRep st k inQ bl nb) {c old : Nat} (hc0 : c ≠ 0)
    (hin : inQ c = decide (st.P.theta < old)) (hk : inQ c = true → k c = old) :
    ∃ st', (pqAdjust c old (old + 1)).run st = .ok () st' ∧ PQOnly st st' ∧
      QInv st' (Function.update k c (old + 1))
        (Function.update inQ c (decide (st.P.theta < old + 1))) := by
  unfold pqAdjust
  simp only [run_getP_bind]
  by_cases h1 : old ≤ st.P.theta
  · by_cases h2 : st.P.theta < old + 1
    · -- entering the queue at bucket `θ + 1`, the least possible
      have hold : old = st.P.theta := by omega
      rw [ite_eq_left (by simp only [h1, decide_true, h2, Bool.and_self]), hold, pqInsertScan_min]
      have hcq : inQ c = false := by rw [hin]; simp only [decide_eq_false_iff_not, not_lt]; omega
      have := hQ.add hcq hc0 (s := st.P.theta + 1) (p := 0) (by omega) (fun _ => by
        rw [List.filter_eq_nil_iff.mpr]
        · rfl
        · intro b hb
          have hbne := (hQ.nbmem b).mp hb
          obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil _ hbne
          have := (hQ.bmem b d).mp hd
          have := hQ.pos d this.1
          simp only [decide_eq_true_eq, not_lt, ge_iff_le]; omega)
      have hdec : decide (st.P.theta < st.P.theta + 1) = true := by
        simp only [Nat.lt_add_one, decide_true]
      rw [hdec]
      exact ⟨_, rfl, addSt_only _ _ _ _, _, _, this⟩
    · rw [ite_eq_right (by
        simp only [Bool.and_eq_true, decide_eq_true_eq, not_and, not_lt]
        omega), ite_eq_right (by
      simp only [Bool.and_eq_true, decide_eq_true_eq, not_and, not_lt]; omega),
      ite_eq_right (by
        simp only [gt_iff_lt, Bool.and_eq_true, decide_eq_true_eq, not_and, not_lt]; omega)]
      refine ⟨st, rfl, PQOnly.refl _, bl, nb, ?_⟩
      have hcq : inQ c = false := by rw [hin]; simp only [decide_eq_false_iff_not, not_lt]; omega
      have hnew : decide (st.P.theta < old + 1) = false := by
        simp only [decide_eq_false_iff_not, not_lt]; omega
      rw [hnew]
      refine ⟨fun d => ?_, fun d hd => ?_, hQ.bucket, fun b d => ?_, hQ.nbl, hQ.nbmem,
        hQ.sorted, hQ.hi⟩
      · by_cases hd : d = c
        · subst hd; rw [hQ.where_]; simp only [hcq, Bool.false_eq_true, ↓reduceIte,
            Function.update_self]
        · rw [Function.update_of_ne hd, Function.update_of_ne hd]; exact hQ.where_ d
      · by_cases hdc : d = c
        · subst hdc; simp only [Function.update_self, Bool.false_eq_true] at hd
        · rw [Function.update_of_ne hdc] at hd ⊢; exact hQ.pos d hd
      · rw [hQ.bmem]
        by_cases hd : d = c
        · subst hd; simp only [hcq, Bool.false_eq_true, false_and, Function.update_self]
        · rw [Function.update_of_ne hd, Function.update_of_ne hd]
  · -- moving from bucket `old` to bucket `old + 1`
    have hcq : inQ c = true := by rw [hin]; simp only [decide_eq_true_eq]; omega
    have hkc := hk hcq
    rw [ite_eq_right (by
        simp only [Bool.and_eq_true, decide_eq_true_eq, not_and, not_lt]
        omega), ite_eq_right (by
      simp only [Bool.and_eq_true, decide_eq_true_eq, not_and, not_lt]; omega),
      ite_eq_left (by simp only [gt_iff_lt, Bool.and_eq_true, decide_eq_true_eq]; omega)]
    simp only [run_get_bind, beq_self_eq_true, ite_true]
    have hcm : c ∈ bl old := (hQ.bmem old c).mpr ⟨hcq, hkc⟩
    have hB := hQ.bucket old
    -- `c` is alone in its bucket iff it is the head with no successor
    have halone : (st.pqHead.getX old == c && st.pqNext.getX c == NIL) = true ↔
        (bl old).erase c = [] := by
      obtain ⟨l1, l2, hsplit⟩ := List.mem_iff_append.mp hcm
      rw [hsplit] at hB
      have hnd := hB.nodup
      rw [hsplit, List.erase_append_right _ (fun h =>
        (List.nodup_append.mp hnd).2.2 c h c (by simp) rfl)]
      simp only [List.erase_cons_head, List.append_eq_nil_iff, Bool.and_eq_true, beq_iff_eq]
      rw [hB.head, hB.next c (by simp), succOf_mid hnd]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨?_, ?_⟩
        · cases l1 with
          | nil => rfl
          | cons a t =>
            exfalso; simp only [List.cons_append, List.headD_eq_head?_getD, List.head?_cons,
                Option.getD_some] at h1; subst h1
            exact (List.nodup_append.mp hnd).2.2 a (by simp) a (by simp) rfl
        · cases l2 with
          | nil => rfl
          | cons a t => exfalso; simp only [List.headD_eq_head?_getD, List.head?_cons,
              Option.getD_some] at h2; exact hB.nonil (by
                simp only [h2, List.mem_append, List.mem_cons, true_or, or_true])
      · rintro ⟨rfl, rfl⟩; simp only [List.nil_append, List.headD_eq_head?_getD, List.head?_cons,
          Option.getD_some, List.head?_nil, Option.getD_none,
          and_self]
    have hsortm := sorted_split_mem hQ.sorted ((hQ.nbmem old).mpr (List.ne_nil_of_mem hcm))
    rw [run_bind, pqDel_run st c (by rw [hQ.where_, ite_eq_left hcq]; have := hQ.pos c hcq; omega)]
    simp only
    rw [pqAdd_run]
    have hD := hQ.del hcq
    rw [hkc] at hD
    have hA := hD.add (c := c) (s := old + 1) (by simp) hc0 (by rw [(delSt_only st c).P]; omega)
      (p := if (st.pqHead.getX old == c && st.pqNext.getX c == NIL) = true then st.nbPrev.getX old
        else old) (fun _ => by
          by_cases hal : (st.pqHead.getX old == c && st.pqNext.getX c == NIL) = true
          · rw [ite_eq_left hal, ite_eq_left (halone.mp hal), filter_lt_succ_erase hQ.nbl.nodup]
            -- the predecessor of `old` in the sorted bucket list
            have := hQ.nbl.prev old ((hQ.nbmem old).mpr (List.ne_nil_of_mem hcm))
            rw [this]
            conv_lhs => rw [hsortm]
            rw [predOf_mid (hsortm ▸ hQ.nbl.nodup)]
          · rw [ite_eq_right hal, ite_eq_right (fun h => hal (halone.mpr h))]
            conv_rhs => rw [hsortm]
            rw [List.filter_append, List.filter_cons]
            have e1 : (nb.filter (· < old)).filter (· < old + 1) = nb.filter (· < old) :=
              List.filter_eq_self.mpr (fun b hb => by
                simp only [List.mem_filter, decide_eq_true_eq] at hb ⊢; omega)
            have e2 : (nb.filter (old < ·)).filter (· < old + 1) = [] :=
              List.filter_eq_nil_iff.mpr (fun b hb => by
                simp only [List.mem_filter, decide_eq_true_eq, not_lt] at hb ⊢; omega)
            simp only [e1, e2, show decide (old < old + 1) = true by simp, ite_true]
            simp)
    have hin' : Function.update (Function.update inQ c false) c true =
        Function.update inQ c (decide (st.P.theta < old + 1)) := by
      have hthreshold : decide (st.P.theta < old + 1) = true := by
        simp only [decide_eq_true_eq]
        omega
      rw [hthreshold]
      simp only [Function.update_idem]
    rw [hin'] at hA
    exact ⟨_, rfl, (delSt_only st c).trans (addSt_only _ _ _ _), _, _, hA⟩

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
theorem QRep.empty_iff {st : Core} {k : Nat → Nat} {inQ : Nat → Bool} {bl : Nat → List Nat}
    {nb : List Nat} (hQ : QRep st k inQ bl nb) : st.pqHi = 0 ↔ ∀ d, inQ d = false := by
  rw [hQ.hi]
  constructor
  · intro h d
    by_contra hd
    simp only [Bool.not_eq_false] at hd
    have hm : k d ∈ nb := (hQ.nbmem _).mpr (List.ne_nil_of_mem ((hQ.bmem _ d).mpr ⟨hd, rfl⟩))
    rcases nb.eq_nil_or_concat with rfl | ⟨l, a, rfl⟩
    · simp only [List.not_mem_nil] at hm
    · rw [List.concat_eq_append, List.getLastD_concat] at h
      subst h
      exact hQ.nbl.nonil (by simp)
  · intro h
    cases hnb : nb with
    | nil => rfl
    | cons b t =>
      exfalso
      have hb : bl b ≠ [] := (hQ.nbmem b).mp (by rw [hnb]; simp)
      obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil _ hb
      have := ((hQ.bmem b d).mp hd).1
      rw [h d] at this; cases this

theorem pqEmpty_run (st : Core) : pqEmpty.run st = .ok (st.pqHi == 0) st := rfl

/-- **`pqPopMax`** returns a queued chunk of largest key, and deletes it. -/
theorem pqPopMax_ok {st : Core} {k : Nat → Nat} {inQ : Nat → Bool} {bl : Nat → List Nat}
    {nb : List Nat} (hQ : QRep st k inQ bl nb) (hne : st.pqHi ≠ 0) :
    ∃ c, pqPopMax.run st = .ok c (delSt st c) ∧ inQ c = true ∧
      ∀ d, inQ d = true → k d ≤ k c := by
  have hnb : nb ≠ [] := by intro h; apply hne; rw [hQ.hi, h]; rfl
  obtain ⟨l, b, hl⟩ := (nb.eq_nil_or_concat).resolve_left hnb
  rw [List.concat_eq_append] at hl
  have hhi : st.pqHi = b := by rw [hQ.hi, hl, List.getLastD_concat]
  have hbm : b ∈ nb := by rw [hl]; simp only [List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, or_true]
  have hbl : bl b ≠ [] := (hQ.nbmem b).mp hbm
  have hB := hQ.bucket b
  obtain ⟨c, t, hct⟩ := List.exists_cons_of_ne_nil hbl
  have hc : st.pqHead.getX b = c := by rw [hB.head, hct]; rfl
  have hcm : c ∈ bl b := by rw [hct]; simp only [List.mem_cons, true_or]
  have hc0 : c ≠ NIL := fun e => hB.nonil (e ▸ hcm)
  obtain ⟨hcq, hkc⟩ := (hQ.bmem b c).mp hcm
  refine ⟨c, ?_, hcq, fun d hd => ?_⟩
  · unfold pqPopMax
    simp only [run_get_bind, hhi, hc]
    rw [ite_eq_right (by simpa using hc0)]
    rw [run_bind, pqDel_run st c (by rw [hQ.where_, ite_eq_left hcq]; have := hQ.pos c hcq; omega)]
    rfl
  · rw [hkc]
    have hdm : k d ∈ nb := (hQ.nbmem _).mpr (List.ne_nil_of_mem ((hQ.bmem _ d).mpr ⟨hd, rfl⟩))
    have hs := hQ.sorted
    rw [hl] at hs hdm
    rw [List.isChain_iff_pairwise, List.pairwise_append] at hs
    rcases List.mem_append.mp hdm with h | h
    · exact le_of_lt (hs.2.2 _ h b (by simp))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h; omega

end OrderMaintenance.Proof
