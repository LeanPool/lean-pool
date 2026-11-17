/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Cost.Params


/-!
# The wrapper: cost and Lemma W

Every core the wrapper runs satisfies the cost invariant whenever an operation reaches it, and
its element count stays within its capacity (Lemma W). So no core operation ever takes FALLBACK.
-/


@[expose] public section

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-- A list linked forward from `hd`. -/
structure NList (nxt : Nat → Nat) (hd : Nat) (l : List Nat) : Prop where
  nodup : l.Nodup
  nonil : NIL ∉ l
  head : hd = l.headD NIL
  next : ∀ x ∈ l, nxt x = succOf l x

theorem LList.nlist {nxt prv : Nat → Nat} {hd : Nat} {l : List Nat} (h : LList nxt prv hd l) :
    NList nxt hd l := ⟨h.nodup, h.nonil, h.head, h.next⟩

theorem succOf_cons_ne {a x : Nat} {t : List Nat} (h : a ≠ x) : succOf (a :: t) x = succOf t x := by
  cases t with
  | nil => rfl
  | cons b t => simp only [succOf, ite_eq_right h]

theorem succOf_cons_self {a : Nat} {t : List Nat} : succOf (a :: t) a = t.headD NIL := by
  cases t with
  | nil => rfl
  | cons b t => simp only [succOf, ↓reduceIte, List.headD_eq_head?_getD, List.head?_cons,
      Option.getD_some]

/-- **A forward-linked list is determined by its head.** -/
theorem NList.unique {nxt : Nat → Nat} : ∀ {hd : Nat} {l l' : List Nat},
    NList nxt hd l → NList nxt hd l' → l = l'
  | hd, [], l', h, h' => by
    cases l' with
    | nil => rfl
    | cons a t => exfalso; have := h.head; have := h'.head; simp only [List.headD_eq_head?_getD,
        List.head?_nil,
        Option.getD_none,
        List.head?_cons,
        Option.getD_some] at *; exact h'.nonil (by simp_all)
  | hd, a :: t, l', h, h' => by
    cases l' with
    | nil => exfalso; have := h.head; have := h'.head; simp only [List.headD_eq_head?_getD,
        List.head?_cons, Option.getD_some,
        List.head?_nil, Option.getD_none] at *; exact h.nonil (by simp_all)
    | cons a' t' =>
      have ha : a = a' := by have e1 := h.head; have e2 := h'.head; simp only [
          List.headD_eq_head?_getD,
          List.head?_cons,
          Option.getD_some] at e1 e2; rw [← e1, ← e2]
      subst ha
      have hat : a ∉ t := (List.nodup_cons.mp h.nodup).1
      have hat' : a ∉ t' := (List.nodup_cons.mp h'.nodup).1
      have tl : NList nxt (nxt a) t := ⟨(List.nodup_cons.mp h.nodup).2,
        fun hn => h.nonil (List.mem_cons_of_mem _ hn),
        by rw [h.next a (by simp), succOf_cons_self],
        fun x hx => by
          rw [h.next x (List.mem_cons_of_mem _ hx),
            succOf_cons_ne (fun (e : a = x) => hat (by rw [e]; exact hx))]⟩
      have tl' : NList nxt (nxt a) t' := ⟨(List.nodup_cons.mp h'.nodup).2,
        fun hn => h'.nonil (List.mem_cons_of_mem _ hn),
        by rw [h'.next a (by simp), succOf_cons_self],
        fun x hx => by
          rw [h'.next x (List.mem_cons_of_mem _ hx),
            succOf_cons_ne (fun (e : a = x) => hat' (by rw [e]; exact hx))]⟩
      rw [NList.unique tl tl']

theorem INV.elist_unique {s : Core} {A A' : Abs} (h : INV s A) (h' : INV s A') :
    A.elist = A'.elist := h.eList.nlist.unique h'.eList.nlist

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### The split at the cursor -/

/-- The elements before the cursor. -/
def preOf (l : List Nat) (c : Nat) : List Nat := l.takeWhile (· ≠ c)

/-- The elements from the cursor on. -/
def postOf (l : List Nat) (c : Nat) : List Nat := l.dropWhile (· ≠ c)

/-- A split whose second part starts at `c` is the split at `c`. -/
theorem split_unique {pre post : List Nat} {c : Nat} (hnd : (pre ++ post).Nodup)
    (hnil : NIL ∉ pre ++ post) (hc : c = post.headD NIL) :
    preOf (pre ++ post) c = pre ∧ postOf (pre ++ post) c = post := by
  induction pre with
  | nil =>
    cases post with
    | nil => simp only [preOf, ne_eq, decide_not, List.append_nil, List.takeWhile_nil, postOf,
        List.dropWhile_nil, and_self]
    | cons a t => subst hc; simp only [preOf, ne_eq, decide_not, List.nil_append, decide_true,
        Bool.not_true, Bool.false_eq_true, not_false_eq_true,
        List.takeWhile_cons_of_neg, postOf,
        List.dropWhile_cons_of_neg, and_self]
  | cons a pre ih =>
    have hnd' : (pre ++ post).Nodup := (List.nodup_cons.mp hnd).2
    have hnil' : NIL ∉ pre ++ post := fun h => hnil (List.mem_cons_of_mem _ h)
    obtain ⟨ih1, ih2⟩ := ih hnd' hnil'
    have hac : a ≠ c := by
      intro e
      cases post with
      | nil => exact hnil (by rw [List.cons_append]; simp only [e, hc, List.headD_eq_head?_getD,
          List.head?_nil, Option.getD_none,
          List.append_nil, List.mem_cons,
          true_or])
      | cons b t =>
        simp only [List.headD_eq_head?_getD, List.head?_cons, Option.getD_some] at hc
        have : a ∈ pre ++ b :: t := by rw [e, hc]; simp only [List.mem_append, List.mem_cons,
            true_or, or_true]
        exact (List.nodup_cons.mp hnd).1 this
    simp only [preOf, postOf, List.cons_append, List.takeWhile_cons, List.dropWhile_cons,
      decide_eq_true_eq, hac, ne_eq, not_false_eq_true, ite_true] at ih1 ih2 ⊢
    exact ⟨by rw [ih1], ih2⟩

/-- The element count of a core equals its list's length (an extra invariant the wrapper uses). -/
def CntEq (c : Core) (A : Abs) : Prop := c.count = A.elist.length

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model OrderMaintenance.Zeroing
/-- **What the wrapper's cost proof assumes**: the top structure's contracts (M5), the parameter
conditions, and Lemma R's I5 (M5 fixes `J` and `H`). -/
structure CostSetup (mk : Nat → Params) (TI PI : Core → Prop) (μ : Core → Nat) (ν : Core → Nat)
    (PP : Params → Prop)
    (Jf capf nf Rf : Params → Nat) : Prop where
  top : TopContractP TI μ Jf capf
  prep : PrepContract TI PI ν PP
  pp : ∀ N, PP (mk N)
  core : ∀ N, CoreP (mk N)
  gp : ∀ N, GParams (mk N)
  cp : ∀ N, CParams (mk N)
  lp : ∀ N, LParams (mk N)
  kR : ∀ N, 1 ≤ (mk N).reservationBudget
  R : ∀ N, Jf (mk N) / (mk N).reservationBudget + 1 ≤ Rf (mk N)
  n1 : ∀ N, 1 ≤ nf (mk N)
  I5 : ∀ N, ((mk N).theta : ℝ) + Rf (mk N) * (Hn (nf (mk N) - 1) + 1) ≤ (mk N).T
  size : ∀ N, 2 + 2 * (N / ((mk N).theta + 1 - cmax (mk N))) ≤ nf (mk N) + 1
  capc : ∀ N, 2 + 2 * (N / ((mk N).theta + 1 - cmax (mk N))) ≤ capf (mk N)
  PN : ∀ N, (mk N).N = N
  prepB : ∀ N N', N' ≤ 4 * N → (mk N').H + 1 ≤ (mk N).L + 2
  small : ∀ N, 64 ≤ N → (mk N).L + 6 ≤ N / 2

variable {mk : Nat → Params} {TI PI : Core → Prop} {μ : Core → Nat} {ν : Core → Nat}
  {PP : Params → Prop}
  {Jf capf nf Rf : Params → Nat}

/-- A core in service: the cost invariant for its element list, which it counts. -/
structure CoreOK (mk : Nat → Params) (TI : Core → Prop) (μ : Core → Nat)
    (Jf nf Rf : Params → Nat) (c : Core) (L : List Nat) : Prop where
  cost : CostInv (TIat TI c.P) μ (Jf c.P) (nf c.P) (Rf c.P) L c
  cnt : c.count = L.length
  pmk : c.P = mk c.P.N

theorem CoreOK.inv {c : Core} {L : List Nat} (h : CoreOK mk TI μ Jf nf Rf c L) :
    ∃ A, INV c A ∧ A.elist = L := h.cost.low.inv

/-- **Insertion into a core in service**: no FALLBACK while its count stays within capacity. -/
theorem CoreOK.insert {c : Core} {L : List Nat} (S : CostSetup mk TI PI μ ν PP Jf capf nf Rf)
    (h : CoreOK mk TI μ Jf nf Rf c L) {x : Nat} (hx : x ∈ L) (hcap : c.count + 1 ≤ c.P.N)
    (hh : Nat) :
    ∃ c', (insertAfter x hh).run c = .ok c.E.size c' ∧
      (do let y ← insertElem x hh; background y; pure y).run c = .ok c.E.size c' ∧
      CoreOK mk TI μ Jf nf Rf c' (OrderMaintenance.Spec.insertAfterL x c.E.size L) ∧
      c'.count = c.count + 1 ∧ c'.P = c.P := by
  have hmk := h.pmk
  generalize hN : c.P.N = N at hmk hcap
  have hdiv : (c.count + 1) / (c.P.theta + 1 - cmax c.P) ≤ N / (c.P.theta + 1 - cmax c.P) :=
    Nat.div_le_div_right hcap
  have hs := S.size N
  have hc := S.capc N
  rw [← hmk] at hs hc
  have hTC : TopContract (TIat TI c.P) μ (Jf c.P) capf := S.top.at c.P
  obtain ⟨c', hr, hnf, hC', hcnt, hP⟩ := insertAfter_cost hTC
    h.cost hx (by rw [hmk]; exact S.kR N) (by rw [hmk]; exact S.R N) (by rw [hmk]; exact S.n1 N)
    (by omega) (by omega) (by rw [hmk]; exact S.I5 N) hh
  refine ⟨c', hr, hnf, ⟨by rw [hP]; exact hC', ?_, by rw [hP, hN]; exact hmk⟩, hcnt, hP⟩
  obtain ⟨A, hI, hel⟩ := h.inv
  rw [hcnt, h.cnt, length_insertAfterL hx]

/-- **Deletion in a core in service.** -/
theorem CoreOK.markDead {c : Core} {L : List Nat} (S : CostSetup mk TI PI μ ν PP Jf capf nf Rf)
    (h : CoreOK mk TI μ Jf nf Rf c L) (x : Nat) :
    ∃ c', (OrderMaintenance.Model.markDead x).run c = .ok () c' ∧ CoreOK mk TI μ Jf nf Rf c' L ∧
      c'.count = c.count ∧ c'.P = c.P := by
  have hmk := h.pmk
  have hTC : TopContract (TIat TI c.P) μ (Jf c.P) capf := S.top.at c.P
  obtain ⟨c', hr, hC'⟩ := markDead_cost hTC h.cost x
  have he : c' = { c with E := c.E.modify x fun e => { e with live := false } } := by
    rw [markDead_run] at hr; cases hr; rfl
  subst he
  exact ⟨_, hr, ⟨hC', h.cnt, hmk⟩, rfl, rfl⟩

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model OrderMaintenance.Zeroing
variable {mk : Nat → Params} {TI PI : Core → Prop} {μ : Core → Nat} {ν : Core → Nat}
  {PP : Params → Prop}
  {Jf capf nf Rf : Params → Nat}

/-- A core whose top structure is being built: it holds the sentinel alone. -/
structure PrepOK (mk : Nat → Params) (PI : Core → Prop) (n : Core) : Prop where
  pi : PI n
  low : LowInv n initAbs.elist
  inv : INV n initAbs
  cnt : n.count = 1
  pmk : n.P = mk n.P.N

theorem newCore_run {P : Params} {lazy : Bool} :
    ∃ n, newCore P lazy = .ok n ∧ (initCore lazy).run { P := P } = .ok () n := by
  obtain ⟨n, hr, -, -⟩ := initCore_run lazy { P := P }
  exact ⟨n, by unfold newCore; rw [runCore_ok hr]; rfl, hr⟩

theorem initCore_fields {s n : Core} {lazy : Bool} (h : (initCore lazy).run s = .ok () n) :
    n.count = 1 ∧ n.P = s.P := by
  obtain ⟨n', hr, -, -⟩ := initCore_run lazy s
  rw [hr] at h; cases h
  have hR : LowRel (initState s.P) n := by
    unfold initCore at hr
    simp only [run_getP_bind] at hr
    rw [run_bind, run_set] at hr
    dsimp only at hr
    have := low_initTop lazy (initState s.P)
    rw [hr] at this; exact this
  exact ⟨hR.1.count, hR.1.P⟩

/-- **A lazily built fresh core.** -/
theorem newCore_lazy (S : CostSetup mk TI PI μ ν PP Jf capf nf Rf) (N : Nat) :
    ∃ n, newCore (mk N) true = .ok n ∧ PrepOK mk PI n ∧ ν n ≤ (mk N).H + 1 ∧ n.P = mk N := by
  obtain ⟨n, hnew, hr⟩ := newCore_run (P := mk N) (lazy := true)
  obtain ⟨hcnt, hP⟩ := initCore_fields hr
  obtain ⟨hL, hI⟩ := lowinv_initCore (S.gp N) (S.cp N) (S.lp N) hr
  obtain ⟨hPI, hν⟩ := S.prep.lazy _ _ (S.pp N) hr
  exact ⟨n, hnew, ⟨hPI, hL, hI, hcnt, by rw [hP]; change mk N = mk (mk N).N; rw [S.PN]⟩, hν, hP⟩

/-- **An eagerly built fresh core** is in service. -/
theorem newCore_eager (S : CostSetup mk TI PI μ ν PP Jf capf nf Rf) (N : Nat) :
    ∃ n, newCore (mk N) false = .ok n ∧ CoreOK mk TI μ Jf nf Rf n initAbs.elist ∧ n.count = 1 ∧
      n.P = mk N := by
  obtain ⟨n, hnew, hr⟩ := newCore_run (P := mk N) (lazy := false)
  obtain ⟨hcnt, hP⟩ := initCore_fields hr
  obtain ⟨hL, hI⟩ := lowinv_initCore (S.gp N) (S.cp N) (S.lp N) hr
  obtain ⟨hTI, hres⟩ := S.prep.eager _ _ (S.pp N) hr
  refine ⟨n, hnew, ⟨costInv_fresh hL ⟨hTI, rfl⟩ hres (by rw [hP]; exact S.n1 N) (gval_fresh hL),
    by rw [hcnt, initAbs_elist]; rfl, by rw [hP]; change mk N = mk (mk N).N; rw [S.PN]⟩, hcnt, hP⟩

/-- **A preparation step** of a core being built: it finishes (the core is in service) or it
decreases `ν`. -/
theorem PrepOK.step (S : CostSetup mk TI PI μ ν PP Jf capf nf Rf) {n : Core}
    (h : PrepOK mk PI n) :
    ∃ b n', runCore n prepareStep = .ok (b, n') ∧ n'.count = n.count ∧ n'.P = n.P ∧
      INV n' initAbs ∧
      (b = true → CoreOK mk TI μ Jf nf Rf n' initAbs.elist) ∧
      (b = false → PrepOK mk PI n' ∧ ν n' < ν n) := by
  obtain ⟨b, n', hr, hL', hI', hR⟩ := prepareStep_low h.low h.inv
  obtain ⟨b2, n2, hr2, hT, hF⟩ := S.prep.step n h.pi
  rw [hr] at hr2; cases hr2
  have hP : n'.P = n.P := hR.1.P
  refine ⟨b, n', by rw [runCore_ok hr], hR.1.count, hP, hI', fun hb => ?_, fun hb => ?_⟩
  · obtain ⟨hTI, hres⟩ := hT hb
    have hpm := h.pmk
    have hn1 : 1 ≤ nf n'.P := by rw [hP, hpm]; exact S.n1 _
    have hc1 : n'.count = initAbs.elist.length := by rw [hR.1.count, h.cnt, initAbs_elist]; rfl
    have hpm' : n'.P = mk n'.P.N := by rw [hP]; exact hpm
    exact ⟨costInv_fresh hL' ⟨hTI, rfl⟩ hres hn1 (gval_fresh hL'), hc1, hpm'⟩
  · obtain ⟨hPI, hν⟩ := hF hb
    have hc1 : n'.count = 1 := by rw [hR.1.count, h.cnt]
    have hpm' : n'.P = mk n'.P.N := by rw [hP]; exact h.pmk
    exact ⟨⟨hPI, hL', hI', hc1, hpm'⟩, hν⟩

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model OrderMaintenance.Zeroing
variable {mk : Nat → Params} {TI PI : Core → Prop} {μ : Core → Nat} {ν : Core → Nat}
  {PP : Params → Prop}
  {Jf capf nf Rf : Params → Nat}

/-- **Lemma W's record of a rebuild in progress**: `c₀` elements and `live₀` live ones at the
trigger, `I` insertions and `D` deletions since. The work left (preparation steps, then the
elements not yet scanned) shrinks by `K_B − 1` per insertion's worth of operations. -/
structure RebuildW (mk : Nat → Params) (TI PI : Core → Prop) (μ : Core → Nat) (ν : Core → Nat)
    (Jf nf Rf : Params → Nat) (om : OrderMaintenance) (n : Core) (c₀ live₀ I D : Nat) : Prop where
  c0 : c₀ ≤ om.cur.P.N / 2
  nP : n.P = mk (4 * max (live₀ + ((c₀ + (om.cur.P.L + 2)) / (om.KB - 1) + 1)) 16)
  ccnt : om.cur.count ≤ c₀ + I
  live : om.live + D = live₀ + I
  l0 : live₀ ≤ c₀
  prep : om.cursorSet = false → PrepOK mk PI n ∧
    ν n + om.cur.count + (om.KB - 1) * I ≤ om.cur.P.L + 2 + c₀
  serve : om.cursorSet = true →
    (∀ B, INV n B → CoreOK mk TI μ Jf nf Rf n B.elist ∧
      n.count ≤ 1 + (liveH n B.elist).length + D) ∧
    ∀ A, INV om.cur A → (postOf A.elist om.cursor).length + (om.KB - 1) * I ≤
      om.cur.P.L + 2 + c₀

/-- **The wrapper's cost invariant**: Invariant R, both cores' cost invariants, and Lemma W. -/
structure WC (mk : Nat → Params) (TI PI : Core → Prop) (μ : Core → Nat) (ν : Core → Nat)
    (Jf nf Rf : Params → Nat) (om : OrderMaintenance) (Sp : OrderMaintenance.Spec.State) : Prop
      where
  w : WInv om Sp
  live : om.live = Sp.list.length
  kb : 4 ≤ om.KB
  big : 64 ≤ om.cur.P.N
  cur : ∀ A, INV om.cur A → CoreOK mk TI μ Jf nf Rf om.cur A.elist
  idle : om.nxt = none → om.cur.count < om.cur.P.N / 2
  busy : ∀ n, om.nxt = some n → ∃ c₀ live₀ I D, RebuildW mk TI PI μ ν Jf nf Rf om n c₀ live₀ I D

/-- The work left bounds the insertions of a rebuild. -/
theorem RebuildW.ins_le {om : OrderMaintenance} {n : Core} {c₀ live₀ I D : Nat}
    (h : RebuildW mk TI PI μ ν Jf nf Rf om n c₀ live₀ I D) (hkb : 4 ≤ om.KB)
    (hA : ∃ A, INV om.cur A) :
    3 * I ≤ om.cur.P.L + 2 + c₀ := by
  have h3 : 3 * I ≤ (om.KB - 1) * I := Nat.mul_le_mul_right I (by omega)
  cases hs : om.cursorSet
  · have := (h.prep hs).2; omega
  · obtain ⟨A, hI⟩ := hA
    have := (h.serve hs).2 A hI; omega

/-- The remaining rebuild work bounds its insertion counter. -/
theorem RebuildW.insertions_le {om : OrderMaintenance} {n : Core} {c₀ live₀ I D : Nat}
    (h : RebuildW mk TI PI μ ν Jf nf Rf om n c₀ live₀ I D) (hkb : 4 ≤ om.KB)
    {A : Abs} (hA : INV om.cur A) :
    I ≤ (c₀ + (om.cur.P.L + 2)) / (om.KB - 1) := by
  rw [Nat.le_div_iff_mul_le (by omega), Nat.mul_comm]
  cases hs : om.cursorSet
  · have := (h.prep hs).2; omega
  · have := (h.serve hs).2 A hA; omega

/-- **Lemma W (1)**: `cur` has room for an insertion. -/
theorem WC.cur_room {om : OrderMaintenance} {Sp : OrderMaintenance.Spec.State} (S : CostSetup mk
  TI PI μ ν PP Jf capf nf Rf)
    (h : WC mk TI PI μ ν Jf nf Rf om Sp) : om.cur.count + 1 ≤ om.cur.P.N := by
  have hsm := S.small _ h.big
  have hmk : om.cur.P = mk om.cur.P.N := by
    obtain ⟨A, hR, -⟩ := h.w.core; exact (h.cur A hR.inv).pmk
  have hL : (mk om.cur.P.N).L = om.cur.P.L := by rw [← hmk]
  rw [hL] at hsm
  cases hn : om.nxt with
  | none => have := h.idle hn; omega
  | some n =>
    obtain ⟨c₀, live₀, I, D, hW⟩ := h.busy n hn
    have hI3 := hW.ins_le h.kb (by obtain ⟨A, hR, -⟩ := h.w.core; exact ⟨A, hR.inv⟩)
    have := hW.ccnt
    have := hW.c0
    omega

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model OrderMaintenance.Zeroing
variable {mk : Nat → Params} {TI PI : Core → Prop} {μ : Core → Nat} {ν : Core → Nat}
  {PP : Params → Prop}
  {Jf capf nf Rf : Params → Nat}

/-- The copies in `nxt` are live elements of `cur`, so at most the live count. -/
theorem WC.nxt_live_le {om : OrderMaintenance} {Sp : OrderMaintenance.Spec.State} (h : WC mk TI
  PI μ ν Jf nf Rf om Sp)
    {n : Core} (hn : om.nxt = some n) (hset : om.cursorSet = true) {B : Abs} (hB : INV n B) :
    (liveH n B.elist).length ≤ om.live := by
  obtain ⟨-, -, A, hR, hL, -, hN⟩ := h.w
  unfold NxtR at hN; rw [hn] at hN
  obtain ⟨B', hRB', -, -, hcs⟩ := hN
  rw [ite_eq_left hset] at hcs
  obtain ⟨pre, post, hsplit, -, -, hLB⟩ := hcs
  rw [INV.elist_unique hB hRB'.inv, hLB, h.live, ← hL, hsplit, liveH_append, List.length_append]
  omega

/-- **Lemma W (2)**: `nxt` has room for an insertion. -/
theorem WC.nxt_room {om : OrderMaintenance} {Sp : OrderMaintenance.Spec.State} (S : CostSetup mk
  TI PI μ ν PP Jf capf nf Rf)
    (h : WC mk TI PI μ ν Jf nf Rf om Sp) {n : Core} (hn : om.nxt = some n)
    (hset : om.cursorSet = true) : n.count + 1 ≤ n.P.N := by
  obtain ⟨c₀, live₀, I, D, hW⟩ := h.busy n hn
  obtain ⟨A, hR, -, -, hN⟩ := h.w.core
  obtain ⟨hserve, hpost⟩ := hW.serve hset
  have hB : ∃ B, INV n B := by
    unfold NxtR at hN; rw [hn] at hN
    obtain ⟨B, hRB, -⟩ := hN
    exact ⟨B, hRB.inv⟩
  obtain ⟨B, hB⟩ := hB
  have hc := (hserve B hB).2
  have hl := h.nxt_live_le hn hset hB
  have hlive := hW.live
  have hp := hpost A hR.inv
  have hkb := h.kb
  have hIq := hW.insertions_le hkb hR.inv
  rw [hW.nP, S.PN]
  generalize (c₀ + (om.cur.P.L + 2)) / (om.KB - 1) = q at hIq ⊢
  have : live₀ + (q + 1) ≤ max (live₀ + (q + 1)) 16 := le_max_left _ _
  omega

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
theorem length_insertAfterL_le (x y : Nat) (l : List Nat) :
    (OrderMaintenance.Spec.insertAfterL x y l).length ≤ l.length + 1 := by
  induction l with
  | nil => simp only [Spec.insertAfterL, List.length_nil, zero_add, zero_le]
  | cons a t ih =>
    simp only [OrderMaintenance.Spec.insertAfterL]
    split <;> simp only [List.length_cons, Std.le_refl, add_le_add_iff_right] ; omega

/-- An insertion adds at most one element to the part from the cursor on. -/
theorem postOf_insertAfterL_le {a b c : Nat} (hbc : b ≠ c) (l : List Nat) :
    (postOf (OrderMaintenance.Spec.insertAfterL a b l) c).length ≤ (postOf l c).length + 1 := by
  induction l with
  | nil => simp only [postOf, ne_eq, decide_not, Spec.insertAfterL, List.dropWhile_nil,
      List.length_nil, zero_add, zero_le]
  | cons x t ih =>
    simp only [OrderMaintenance.Spec.insertAfterL]
    by_cases hxa : x = a
    · rw [ite_eq_left hxa]
      by_cases hxc : x = c
      · simp only [postOf, ne_eq, decide_not, hxc, decide_true, Bool.not_true,
          Bool.false_eq_true, not_false_eq_true, List.dropWhile_cons_of_neg,
          List.length_cons, Std.le_refl]
      · simp only [postOf, List.dropWhile_cons, ne_eq, decide_not, hxc,
              hbc] at ih ⊢
        simp only [decide_false, Bool.not_false, ↓reduceIte, le_add_iff_nonneg_right, zero_le]
    · rw [ite_eq_right hxa]
      by_cases hxc : x = c
      · simp only [postOf, List.dropWhile_cons, hxc, ne_eq, not_true_eq_false, decide_false,
           ]
        subst hxc
        have := length_insertAfterL_le a b t
        simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons, add_le_add_iff_right,
            ge_iff_le]; omega
      · simp only [postOf, List.dropWhile_cons, ne_eq, decide_not, hxc,
            ] at ih ⊢
        exact ih

/-- Advancing the cursor drops one element. -/
theorem postOf_succOf {l : List Nat} (hnd : l.Nodup) (hnil : NIL ∉ l) {c : Nat} (hc : c ∈ l) :
    postOf l (succOf l c) = (postOf l c).tail := by
  induction l with
  | nil => simp only [List.not_mem_nil] at hc
  | cons x t ih =>
    have hxt : x ∉ t := (List.nodup_cons.mp hnd).1
    have hx0 : x ≠ NIL := fun e => hnil (by rw [← e]; simp)
    by_cases hxc : x = c
    · subst hxc
      rw [succOf_cons_self]
      cases t with
      | nil => simp [postOf, hx0]
      | cons y t' =>
        have hxy : x ≠ y := fun e => hxt (by rw [e]; simp)
        simp only [postOf, List.headD_eq_head?_getD, List.head?_cons, Option.getD_some, ne_eq,
            decide_not, hxy, decide_false, Bool.not_false, List.dropWhile_cons_of_pos,
            decide_true, Bool.not_true, Bool.false_eq_true, not_false_eq_true,
            List.dropWhile_cons_of_neg, List.tail_cons]
    · have hct : c ∈ t := (List.mem_cons.mp hc).resolve_left (Ne.symm hxc)
      rw [succOf_cons_ne hxc]
      have hxs : x ≠ succOf t c := by
        intro e
        by_cases h : succOf t c = NIL
        · exact hx0 (e.trans h)
        · have : succOf t c ∈ t := by
            obtain ⟨l1, l2, e2⟩ := succOf_split (rfl : succOf t c = succOf t c) h
            have hm : succOf t c ∈ l1 ++ c :: succOf t c :: l2 := by simp only [List.mem_append,
                List.mem_cons,
                true_or,
                or_true]
            rwa [← e2] at hm
          exact hxt (e ▸ this)
      simp only [postOf, List.dropWhile_cons, ne_eq, decide_not, hxs, hxc,
          ]
      exact ih (List.nodup_cons.mp hnd).2 (fun h => hnil (List.mem_cons_of_mem _ h)) hct

theorem postOf_headD {l : List Nat} (hne : l ≠ []) : postOf l (l.headD NIL) = l := by
  cases l with
  | nil => exact absurd rfl hne
  | cons a t => simp only [postOf, List.headD_eq_head?_getD, List.head?_cons, Option.getD_some,
      ne_eq, decide_not, decide_true, Bool.not_true, Bool.false_eq_true,
      not_false_eq_true, List.dropWhile_cons_of_neg]

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model OrderMaintenance.Zeroing
variable {mk : Nat → Params} {TI PI : Core → Prop} {μ : Core → Nat} {ν : Core → Nat}
  {PP : Params → Prop}
  {Jf capf nf Rf : Params → Nat}

/-- **A copy step** keeps the nxt core in service and its fill bound, and advances the cursor. -/
theorem copy_cost (S : CostSetup mk TI PI μ ν PP Jf capf nf Rf)
    {om : OrderMaintenance} {n : Core} {B : Abs} {D : Nat} (hRB : CoreR n B)
    (hok : CoreOK mk TI μ Jf nf Rf n B.elist) (hfill : n.count ≤ 1 + (liveH n B.elist).length + D)
    (hroom : n.count + 1 ≤ n.P.N) :
    ∃ om' n' B', copyAtCursor om n = .ok (om', n') ∧ om'.cursor = eN om.cur om.cursor ∧
      CoreR n' B' ∧ CoreOK mk TI μ Jf nf Rf n' B'.elist ∧
      n'.count ≤ 1 + (liveH n' B'.elist).length + D ∧ n'.P = n.P := by
  unfold copyAtCursor
  by_cases hl : live om.cur om.cursor = true
  · have hl' : (om.cur.E.getX om.cursor).live = true := hl
    simp only [hl', ite_true]
    have htail : n.tail ∈ B.elist := by
      rw [hRB.inv.tail]
      obtain ⟨b, bt, hb⟩ := List.exists_cons_of_ne_nil hRB.ne
      rw [hb]; exact getLastD_cons_mem _ _ _
    obtain ⟨n', B', hr', hRB', hB', hrecB, hlyB, hhyB, hyB, _, _, hP'⟩ :=
      core_insert hRB htail (hdl om.cur om.cursor)
    obtain ⟨n2, hr2, -, hok2, hcnt2, hP2⟩ := hok.insert S htail hroom (hdl om.cur om.cursor)
    rw [hr'] at hr2; cases hr2
    simp only [bind, Except.bind]
    rw [show (om.cur.E.getX om.cursor).h = hdl om.cur om.cursor from rfl, runCore_ok hr']
    have hB'e : B'.elist = B.elist ++ [n.E.size] := by
      rw [hB', hRB.inv.tail]; exact insertAfterL_getLastD hRB.inv.eList.nodup hRB.ne _
    have hLn : liveH n' B'.elist = liveH n B.elist ++ [hdl om.cur om.cursor] := by
      rw [hB'e, liveH_append, liveH_frame hrecB]
      simp only [FM_cons, hlyB, ↓reduceIte, hhyB, FM_nil]
    refine ⟨_, n', B', rfl, rfl, hRB', by rw [hB']; exact hok2, ?_, hP2⟩
    rw [hLn, List.length_append, hcnt2]
    simp only [List.length_cons, List.length_nil, zero_add]
    omega
  · have hl' : (om.cur.E.getX om.cursor).live = false := by simpa [live] using hl
    simp only [hl', Bool.false_eq_true, ite_false]
    exact ⟨_, n, B, rfl, rfl, hRB, hok, hfill, rfl⟩

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model OrderMaintenance.Zeroing
variable {mk : Nat → Params} {TI PI : Core → Prop} {μ : Core → Nat} {ν : Core → Nat}
  {PP : Params → Prop}
  {Jf capf nf Rf : Params → Nat}

/-- The rebuild loop's cost invariant, with `budget` steps left, within the entry potential `Φe`. -/
structure LoopC (mk : Nat → Params) (TI PI : Core → Prop) (μ : Core → Nat) (ν : Core → Nat)
    (Jf nf Rf : Params → Nat) (om : OrderMaintenance) (n : Core) (A : Abs) (budget Φe live₀ I D
      N' : Nat) :
    Prop where
  curok : CoreOK mk TI μ Jf nf Rf om.cur A.elist
  nP : n.P = mk N'
  prep : om.cursorSet = false → PrepOK mk PI n ∧ ν n + om.cur.count + (om.KB - budget) ≤ Φe
  serve : om.cursorSet = true →
    (∀ B, INV n B → CoreOK mk TI μ Jf nf Rf n B.elist ∧
      n.count ≤ 1 + (liveH n B.elist).length + D) ∧
    (postOf A.elist om.cursor).length + (om.KB - budget) ≤ Φe
  room : 1 + live₀ + I + 1 ≤ N'
  live : om.live + D = live₀ + I
  bud : budget ≤ om.KB

/-- What the rebuild loop leaves: the rebuild goes on, having spent the whole budget, or `nxt`
replaced `cur`. -/
def LoopOut (mk : Nat → Params) (TI PI : Core → Prop) (μ : Core → Nat) (ν : Core → Nat)
    (Jf nf Rf : Params → Nat) (om om' : OrderMaintenance) (A : Abs) (Φe live₀ I D N' : Nat) :
      Prop :=
  (∃ n', om'.nxt = some n' ∧ om'.cur = om.cur ∧ om'.KB = om.KB ∧
      LoopC mk TI PI μ ν Jf nf Rf om' n' A 0 Φe live₀ I D N') ∨
    (om'.nxt = none ∧ om'.cur.P = mk N' ∧ om'.KB = om.KB ∧ om'.live = om.live ∧
      (∀ B, INV om'.cur B → CoreOK mk TI μ Jf nf Rf om'.cur B.elist) ∧
      om'.cur.count ≤ 1 + live₀ + I)

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model OrderMaintenance.Zeroing
variable {mk : Nat → Params} {TI PI : Core → Prop} {μ : Core → Nat} {ν : Core → Nat}
  {PP : Params → Prop}
  {Jf capf nf Rf : Params → Nat}

theorem LoopC.congr {om om' : OrderMaintenance} {n : Core} {A : Abs} {budget Φe live₀ I D N' : Nat}
    (h : LoopC mk TI PI μ ν Jf nf Rf om n A budget Φe live₀ I D N') (hc : om'.cur = om.cur)
    (hs : om'.cursorSet = om.cursorSet) (hu : om'.cursor = om.cursor) (hk : om'.KB = om.KB)
    (hl : om'.live = om.live) : LoopC mk TI PI μ ν Jf nf Rf om' n A budget Φe live₀ I D N' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨by rw [hc]; exact h1, h2, fun h => ?_, fun h => ?_, h5, by rw [hl]; exact h6,
    by rw [hk]; exact h7⟩
  · rw [hs] at h; rw [hc, hk]; exact h3 h
  · rw [hs] at h; rw [hu, hk]; exact h4 h

/-- Finishing preparation initializes the shared service invariant at the first cursor. -/
theorem LoopC.prepared {om : OrderMaintenance} {n n' : Core} {A B : Abs}
    {budget Φe live₀ I D N' : Nat}
    (h : LoopC mk TI PI μ ν Jf nf Rf om n A budget Φe live₀ I D N')
    (hR : CoreR om.cur A) (hs : om.cursorSet = false) (hP : n'.P = n.P)
    (hcnt : n'.count = n.count) (hB : INV n' B)
    (hok : CoreOK mk TI μ Jf nf Rf n' B.elist) :
    LoopC mk TI PI μ ν Jf nf Rf
      { om with cursor := (om.cur.E.getX om.cur.head).next, cursorSet := true }
      n' A budget Φe live₀ I D N' := by
  obtain ⟨hprep, hφ⟩ := h.prep hs
  have hcount : om.cur.count = A.elist.length := h.curok.cnt
  have hpost : (postOf A.elist (eN om.cur om.cur.head)).length + 1 = A.elist.length := by
    rw [hR.inv.eList.next _ hR.head, hR.inv.eList.head,
      postOf_succOf hR.inv.eList.nodup hR.inv.eList.nonil
        (by rw [← hR.inv.eList.head]; exact hR.head), postOf_headD hR.ne, List.length_tail]
    have := List.length_pos_of_ne_nil hR.ne; omega
  refine ⟨h.curok, by rw [hP]; exact h.nP, fun hs => by simp at hs,
    fun _ => ⟨fun B' hB' => ?_, ?_⟩, h.room, h.live, h.bud⟩
  · rw [INV.elist_unique hB' hB]
    refine ⟨hok, ?_⟩
    rw [hcnt, hprep.cnt]; omega
  · change (postOf A.elist (eN om.cur om.cur.head)).length + (om.KB - budget) ≤ Φe
    omega

/-- An unfinished preparation spends one budget unit as its potential decreases. -/
theorem LoopC.preparing {om : OrderMaintenance} {n n' : Core} {A : Abs}
    {budget Φe live₀ I D N' : Nat}
    (h : LoopC mk TI PI μ ν Jf nf Rf om n A budget Φe live₀ I D N')
    (hs : om.cursorSet = false) (hP : n'.P = n.P) (hprep : PrepOK mk PI n')
    (hν : ν n' < ν n) :
    LoopC mk TI PI μ ν Jf nf Rf om n' A (budget - 1) Φe live₀ I D N' := by
  have hφ := (h.prep hs).2
  refine ⟨h.curok, by rw [hP]; exact h.nP, fun _ => ⟨hprep, ?_⟩,
    fun ht => by simp [hs] at ht, h.room, h.live, by have := h.bud; omega⟩
  have := h.bud; omega

/-- A copy preserves the service invariant when its cursor drops one remaining element. -/
theorem LoopC.copied {om om' : OrderMaintenance} {n n' : Core} {A B : Abs}
    {budget Φe live₀ I D N' : Nat}
    (h : LoopC mk TI PI μ ν Jf nf Rf om n A budget Φe live₀ I D N')
    (hs : om.cursorSet = true) (hc : om'.cur = om.cur)
    (hset : om'.cursorSet = om.cursorSet) (hl : om'.live = om.live) (hk : om'.KB = om.KB)
    (hP : n'.P = n.P) (hB : INV n' B) (hok : CoreOK mk TI μ Jf nf Rf n' B.elist)
    (hfill : n'.count ≤ 1 + (liveH n' B.elist).length + D)
    (hpost : (postOf A.elist om'.cursor).length + 1 =
      (postOf A.elist om.cursor).length) :
    LoopC mk TI PI μ ν Jf nf Rf om' n' A (budget - 1) Φe live₀ I D N' := by
  have hφ := (h.serve hs).2
  refine ⟨by rw [hc]; exact h.curok, by rw [hP]; exact h.nP,
    fun ht => absurd (hset ▸ ht) (by simp [hs]), fun _ => ⟨fun B' hB' => ?_, ?_⟩,
    h.room, by rw [hl]; exact h.live, by rw [hk]; have := h.bud; omega⟩
  · rw [INV.elist_unique hB' hB]; exact ⟨hok, hfill⟩
  · rw [hk]; have := h.bud; omega

theorem LoopOut.mono {om om1 om' : OrderMaintenance} {A : Abs} {Φe live₀ I D N' : Nat}
    (h : LoopOut mk TI PI μ ν Jf nf Rf om1 om' A Φe live₀ I D N') (hc : om1.cur = om.cur)
    (hk : om1.KB = om.KB) (hl : om1.live = om.live) :
    LoopOut mk TI PI μ ν Jf nf Rf om om' A Φe live₀ I D N' := by
  rcases h with ⟨n', h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4, h5, h6⟩
  · exact Or.inl ⟨n', h1, h2.trans hc, h3.trans hk, h4⟩
  · exact Or.inr ⟨h1, h2, h3.trans hk, h4.trans hl, h5, h6⟩

/-- The live copies are at most the live count, inside the loop. -/
theorem nxtR'_live_le {c : Core} {A : Abs} {om : OrderMaintenance} {n : Core} {Sp :
  OrderMaintenance.Spec.State}
    (hN : NxtR' c A om n) (hL : liveH c A.elist = Sp.list) (hset : om.cursorSet = true)
    {B : Abs} (hB : INV n B) : (liveH n B.elist).length ≤ Sp.list.length := by
  obtain ⟨B', hRB', -, -, hcs⟩ := hN
  rw [ite_eq_left hset] at hcs
  obtain ⟨pre, post, hsplit, -, -, hLB⟩ := hcs
  rw [INV.elist_unique hB hRB'.inv, hLB, ← hL, hsplit, liveH_append, List.length_append]
  omega

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model OrderMaintenance.Zeroing
variable {mk : Nat → Params} {TI PI : Core → Prop} {μ : Core → Nat} {ν : Core → Nat}
  {PP : Params → Prop}
  {Jf capf nf Rf : Params → Nat}

/-- **The rebuild loop** (Lemma W's length argument): every budgeted step shrinks the work left by
one; the loop ends with the budget spent or with the swap. -/
theorem rebuildLoop_cost (S : CostSetup mk TI PI μ ν PP Jf capf nf Rf) {Sp :
  OrderMaintenance.Spec.State}
    (hS : OrderMaintenance.Spec.Inv Sp) {Φe live₀ I D N' : Nat} :
    ∀ fuel budget (om : OrderMaintenance) (n : Core) (A : Abs), CoreR om.cur A →
      liveH om.cur A.elist = Sp.list → IdxOK om.cur A om.curIdx Sp.list → NxtR' om.cur A om n →
      om.nextHandle = Sp.fresh → om.live = Sp.list.length →
      LoopC mk TI PI μ ν Jf nf Rf om n A budget Φe live₀ I D N' →
      budget + (if om.cursorSet then 0 else 1) ≤ fuel →
      ∃ om', rebuildLoop om n fuel budget = .ok om' ∧ WInv om' Sp ∧ om'.live = om.live ∧
        LoopOut mk TI PI μ ν Jf nf Rf om om' A Φe live₀ I D N' := by
  intro fuel
  induction fuel with
  | zero =>
    intro budget om n A hR hL hI hN hf hlv hC hfu
    have hb : budget = 0 := by split at hfu <;> omega
    subst hb
    exact ⟨_, rfl, ⟨hS, hf, A, hR, hL, hI, hN⟩, rfl, Or.inl ⟨n, rfl, rfl, rfl,
      hC.congr rfl rfl rfl rfl rfl⟩⟩
  | succ fuel ih =>
    intro budget om n A hR hL hI hN hf hlv hC hfu
    have hnd : (liveH om.cur A.elist).Nodup := hL ▸ hS.1
    unfold rebuildLoop
    by_cases hb : budget = 0
    · rw [ite_eq_left hb]; subst hb
      exact ⟨_, rfl, ⟨hS, hf, A, hR, hL, hI, hN⟩, rfl, Or.inl ⟨n, rfl, rfl, rfl,
        hC.congr rfl rfl rfl rfl rfl⟩⟩
    rw [ite_eq_right hb]
    by_cases hset : om.cursorSet = true
    · rw [ite_eq_right (by simp only [hset, Bool.not_true, Bool.false_eq_true, not_false_eq_true])]
      obtain ⟨hserve, -⟩ := hC.serve hset
      have hN0 := hN
      obtain ⟨B, hRB, hIB, hzB, hcs⟩ := hN0
      rw [ite_eq_left hset] at hcs
      obtain ⟨pre, post, hsplit, hcpost, hpre, hLB⟩ := hcs
      have hlB := nxtR'_live_le hN hL hset hRB.inv
      have hfill := (hserve B hRB.inv).2
      have hlive := hC.live
      by_cases hc : om.cursor = NIL
      · rw [ite_eq_left hc]
        refine ⟨_, rfl, swap_ok hN hR hL hset hc hS hf, rfl, Or.inr ⟨rfl, hC.nP, rfl, rfl,
          fun B' hB' => (hserve B' hB').1, ?_⟩⟩
        change n.count ≤ 1 + live₀ + I
        omega
      rw [ite_eq_right hc]
      obtain ⟨om', n', hcp, e1, e2, e3, e4, e5, e6, e7, hN'⟩ := copy_ok hN hR hnd hset hc
      have hcurA : om.cursor ∈ A.elist := by
        rw [hsplit, hcpost]
        cases post with
        | nil => exact absurd hcpost hc
        | cons a t => simp only [List.headD_eq_head?_getD, List.head?_cons, Option.getD_some,
            List.mem_append, List.mem_cons, true_or, or_true]
      have hroom : n.count + 1 ≤ n.P.N := by
        rw [hC.nP, S.PN]; have := hC.room; omega
      obtain ⟨om2, n2, B2, hcp2, hcur2, hRB2, hok2, hfill2, hP2⟩ :=
        copy_cost S hRB (hserve B hRB.inv).1 hfill hroom
      rw [hcp] at hcp2
      injection hcp2 with hcp2
      injection hcp2 with h1 h2
      subst h1; subst h2
      simp only [bind, Except.bind, hcp]
      -- the work left after the copy
      have hpo : postOf A.elist om.cursor = post := by
        rw [hsplit]
        exact (split_unique (hsplit ▸ hR.inv.eList.nodup) (hsplit ▸ hR.inv.eList.nonil) hcpost).2
      have hpne : post ≠ [] := by intro h; rw [h] at hcpost; exact hc hcpost
      have hpost' : (postOf A.elist om'.cursor).length + 1 = (postOf A.elist om.cursor).length := by
        rw [hcur2, hR.inv.eList.next _ hcurA,
          postOf_succOf hR.inv.eList.nodup hR.inv.eList.nonil hcurA,
          hpo, List.length_tail]
        have := List.length_pos_of_ne_nil hpne; omega
      have hC' : LoopC mk TI PI μ ν Jf nf Rf om' n' A (budget - 1) Φe live₀ I D N' :=
        hC.copied hset e1 e4 e6 e7 hP2 hRB2.inv hok2 hfill2 hpost'
      by_cases hc' : om'.cursor = NIL
      · rw [ite_eq_left hc']
        have hN'' := e1 ▸ hN'
        obtain ⟨Bx, hRBx, -, -, hcsx⟩ := hN''
        refine ⟨_, rfl, swap_ok (om := om') (e1 ▸ hN') (e1 ▸ hR) (e1 ▸ hL) (e4 ▸ hset) hc' hS
          (e5 ▸ hf), e6, Or.inr ⟨rfl, hC'.nP, e7, e6, fun B' hB' => ((hC'.serve (e4 ▸ hset)).1
            B' hB').1,
          ?_⟩⟩
        change n'.count ≤ 1 + live₀ + I
        have := nxtR'_live_le (e1 ▸ hN') (e1 ▸ hL) (e4 ▸ hset) hRB2.inv
        omega
      · rw [ite_eq_right hc']
        obtain ⟨om'', h1, h2, h3, h4⟩ := ih (budget - 1) om' n' A (e1 ▸ hR) (e1 ▸ hL)
          (e1 ▸ e2 ▸ hI) (e1 ▸ hN') (e5 ▸ hf) (by rw [e6]; exact hlv) hC'
          (by rw [e4, ite_eq_left hset]; rw [ite_eq_left hset] at hfu; omega)
        exact ⟨om'', h1, h2, h3.trans e6, h4.mono e1 e7 e6⟩
    · have hf' : om.cursorSet = false := by simpa using hset
      rw [ite_eq_left (by simp only [hf', Bool.not_false])]
      obtain ⟨hprep, -⟩ := hC.prep hf'
      obtain ⟨ready, n', hr, hN1, hN2⟩ := prepare_ok hN hR hf'
      obtain ⟨b, n2, hr2, hcnt2, hP2, hI2, hT2, hF2⟩ := hprep.step S
      rw [hr] at hr2
      injection hr2 with hr2
      injection hr2 with h1 h2
      subst h1; subst h2
      simp only [bind, Except.bind, hr]
      cases ready with
      | true =>
        rw [ite_eq_left rfl]
        have hok := hT2 rfl
        set om1 : OrderMaintenance := {
          om with
          cursor := (om.cur.E.getX om.cur.head).next
          cursorSet := true } with hom1
        have hC1 : LoopC mk TI PI μ ν Jf nf Rf om1 n' A budget Φe live₀ I D N' :=
          hC.prepared hR hf' hP2 hcnt2 hI2 hok
        obtain ⟨om'', h1, h2, h3, h4⟩ := ih budget om1 n' A hR hL hI (hN2 rfl) hf hlv hC1 (by
          simp only [hom1, ↓reduceIte, add_zero]
          rw [ite_eq_right (by simp only [hf', Bool.false_eq_true,
            not_false_eq_true])] at hfu
          omega)
        exact ⟨om'', h1, h2, h3, h4.mono rfl rfl rfl⟩
      | false =>
        simp only [Bool.false_eq_true, ite_false]
        obtain ⟨hprep', hν⟩ := hF2 rfl
        have hC1 : LoopC mk TI PI μ ν Jf nf Rf om n' A (budget - 1) Φe live₀ I D N' :=
          hC.preparing hf' hP2 hprep' hν
        obtain ⟨om'', h1, h2, h3, h4⟩ := ih (budget - 1) om n' A hR hL hI hN1 hf hlv hC1
          (by
            rw [ite_eq_right (by simp only [hf', Bool.false_eq_true,
              not_false_eq_true])] at hfu ⊢
            omega)
        exact ⟨om'', h1, h2, h3, h4⟩

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model OrderMaintenance.Zeroing
variable {mk : Nat → Params} {TI PI : Core → Prop} {μ : Core → Nat} {ν : Core → Nat}
  {PP : Params → Prop}
  {Jf capf nf Rf : Params → Nat}

/-- Lemma W's record in the middle of an operation: this operation's insertion or deletion is
counted, and its `K_B` rebuild steps are still to come. -/
structure MidW (mk : Nat → Params) (TI PI : Core → Prop) (μ : Core → Nat) (ν : Core → Nat)
    (Jf nf Rf : Params → Nat) (om : OrderMaintenance) (n : Core) (c₀ live₀ I D : Nat) : Prop where
  c0 : c₀ ≤ om.cur.P.N / 2
  nP : n.P = mk (4 * max (live₀ + ((c₀ + (om.cur.P.L + 2)) / (om.KB - 1) + 1)) 16)
  ccnt : om.cur.count ≤ c₀ + I
  live : om.live + D = live₀ + I
  l0 : live₀ ≤ c₀
  Iq : I ≤ (c₀ + (om.cur.P.L + 2)) / (om.KB - 1) + 1
  prep : om.cursorSet = false → PrepOK mk PI n ∧
    ν n + om.cur.count + (om.KB - 1) * I ≤ om.cur.P.L + 2 + c₀ + om.KB
  serve : om.cursorSet = true →
    (∀ B, INV n B → CoreOK mk TI μ Jf nf Rf n B.elist ∧
      n.count ≤ 1 + (liveH n B.elist).length + D) ∧
    ∀ A, INV om.cur A → (postOf A.elist om.cursor).length + (om.KB - 1) * I ≤
      om.cur.P.L + 2 + c₀ + om.KB

/-- The middle-of-operation bounds initialize the rebuild loop's entry potential. -/
theorem MidW.loop_entry {om : OrderMaintenance} {n : Core} {A : Abs} {c₀ live₀ I D : Nat}
    (h : MidW mk TI PI μ ν Jf nf Rf om n c₀ live₀ I D)
    (hok : CoreOK mk TI μ Jf nf Rf om.cur A.elist) :
    LoopC mk TI PI μ ν Jf nf Rf { om with nxt := none } n A om.KB
      (if om.cursorSet then (postOf A.elist om.cursor).length else ν n + om.cur.count)
      live₀ I D (4 * max (live₀ + ((c₀ + (om.cur.P.L + 2)) / (om.KB - 1) + 1)) 16) := by
  have hroom : 1 + live₀ + I + 1 ≤
      4 * max (live₀ + ((c₀ + (om.cur.P.L + 2)) / (om.KB - 1) + 1)) 16 := by
    have := h.Iq
    have := le_max_left (live₀ + ((c₀ + (om.cur.P.L + 2)) / (om.KB - 1) + 1)) 16
    omega
  refine ⟨hok, h.nP, fun hs => ⟨(h.prep hs).1, ?_⟩,
    fun hs => ⟨(h.serve hs).1, ?_⟩, hroom, h.live, le_rfl⟩
  · change ν n + om.cur.count + (om.KB - om.KB) ≤ _
    simp only [show om.cursorSet = false from hs, Bool.false_eq_true, ite_false]; omega
  · change (postOf A.elist om.cursor).length + (om.KB - om.KB) ≤ _
    simp only [show om.cursorSet = true from hs, ite_true]; omega

/-- Insertion advances the counters and spends at most one operation's rebuild allowance. -/
theorem RebuildW.insert_mid {om om' : OrderMaintenance} {n n' : Core} {c₀ live₀ I D : Nat}
    (h : RebuildW mk TI PI μ ν Jf nf Rf om n c₀ live₀ I D) (hkb : 4 ≤ om.KB)
    {A : Abs} (hA : INV om.cur A)
    (hP : om'.cur.P = om.cur.P) (hc : om'.cur.count = om.cur.count + 1)
    (hl : om'.live = om.live + 1) (hk : om'.KB = om.KB)
    (hs : om'.cursorSet = om.cursorSet) (hnP : n'.P = n.P)
    (hprep : om.cursorSet = false → n' = n)
    (hserve : om.cursorSet = true →
      (∀ B, INV n' B → CoreOK mk TI μ Jf nf Rf n' B.elist ∧
        n'.count ≤ 1 + (liveH n' B.elist).length + D) ∧
      ∀ A', INV om'.cur A' → (postOf A'.elist om'.cursor).length ≤
        (postOf A.elist om.cursor).length + 1) :
    MidW mk TI PI μ ν Jf nf Rf om' n' c₀ live₀ (I + 1) D := by
  have hIq := h.insertions_le hkb hA
  refine ⟨?_, ?_, ?_, ?_, h.l0, ?_, ?_, ?_⟩
  · rw [hP]; exact h.c0
  · rw [hnP, hP, hk]; exact h.nP
  · rw [hc]; have := h.ccnt; omega
  · rw [hl]; have := h.live; omega
  · rw [hP, hk]; omega
  · intro hfalse
    rw [hs] at hfalse
    obtain ⟨hp, hb⟩ := h.prep hfalse
    rw [hprep hfalse, hc, hP, hk, Nat.mul_add, Nat.mul_one]
    exact ⟨hp, by omega⟩
  · intro htrue
    rw [hs] at htrue
    obtain ⟨hn, hpost⟩ := hserve htrue
    refine ⟨hn, fun A' hA' => ?_⟩
    rw [hP, hk, Nat.mul_add, Nat.mul_one]
    have := hpost A' hA'
    have := (h.serve htrue).2 A hA
    omega

/-- Deletion advances its counter without spending additional insertion allowance. -/
theorem RebuildW.delete_mid {om om' : OrderMaintenance} {n n' : Core} {c₀ live₀ I D : Nat}
    (h : RebuildW mk TI PI μ ν Jf nf Rf om n c₀ live₀ I D) (hkb : 4 ≤ om.KB)
    {A : Abs} (hA : INV om.cur A) (hpos : 1 ≤ om.live)
    (hP : om'.cur.P = om.cur.P) (hc : om'.cur.count = om.cur.count)
    (hl : om'.live = om.live - 1) (hk : om'.KB = om.KB)
    (hs : om'.cursorSet = om.cursorSet) (hnP : n'.P = n.P)
    (hprep : om.cursorSet = false → n' = n)
    (hserve : om.cursorSet = true →
      (∀ B, INV n' B → CoreOK mk TI μ Jf nf Rf n' B.elist ∧
        n'.count ≤ 1 + (liveH n' B.elist).length + (D + 1)) ∧
      ∀ A', INV om'.cur A' → (postOf A'.elist om'.cursor).length ≤
        (postOf A.elist om.cursor).length) :
    MidW mk TI PI μ ν Jf nf Rf om' n' c₀ live₀ I (D + 1) := by
  have hIq := h.insertions_le hkb hA
  refine ⟨?_, ?_, ?_, ?_, h.l0, ?_, ?_, ?_⟩
  · rw [hP]; exact h.c0
  · rw [hnP, hP, hk]; exact h.nP
  · rw [hc]; exact h.ccnt
  · rw [hl]; have := h.live; omega
  · rw [hP, hk]; omega
  · intro hfalse
    rw [hs] at hfalse
    obtain ⟨hp, hb⟩ := h.prep hfalse
    rw [hprep hfalse, hc, hP, hk]
    exact ⟨hp, by omega⟩
  · intro htrue
    rw [hs] at htrue
    obtain ⟨hn, hpost⟩ := hserve htrue
    refine ⟨hn, fun A' hA' => ?_⟩
    rw [hP, hk]
    have := hpost A' hA'
    have := (h.serve htrue).2 A hA
    omega


end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model OrderMaintenance.Zeroing
variable {mk : Nat → Params} {TI PI : Core → Prop} {μ : Core → Nat} {ν : Core → Nat}
  {PP : Params → Prop}
  {Jf capf nf Rf : Params → Nat}

/-- **The rebuild step** (Lemma W): it restores the wrapper's cost invariant. -/
theorem rebuildStep_cost (S : CostSetup mk TI PI μ ν PP Jf capf nf Rf) {om : OrderMaintenance}
  {Sp : OrderMaintenance.Spec.State}
    (hW : WInv om Sp) (hlv : om.live = Sp.list.length) (hkb : 4 ≤ om.KB)
    (hbig : 64 ≤ om.cur.P.N) (hcur : ∀ A, INV om.cur A → CoreOK mk TI μ Jf nf Rf om.cur A.elist)
    (hidle : om.nxt = none → om.cur.count ≤ om.cur.P.N / 2)
    (hbusy : ∀ n, om.nxt = some n → ∃ c₀ live₀ I D, MidW mk TI PI μ ν Jf nf Rf om n c₀ live₀ I D) :
    ∃ om', om.rebuildStep mk = .ok om' ∧ WC mk TI PI μ ν Jf nf Rf om' Sp := by
  obtain ⟨om', hrs, hW'⟩ := rebuildStep_ok S.core hW
  refine ⟨om', hrs, ?_⟩
  have hW0 := hW
  obtain ⟨hS, hf, A, hR, hL, hI, hN⟩ := hW0
  have hok := hcur A hR.inv
  have hmk : om.cur.P = mk om.cur.P.N := hok.pmk
  have hsm := S.small _ hbig
  have hLeq : (mk om.cur.P.N).L = om.cur.P.L := by rw [← hmk]
  rw [hLeq] at hsm
  have hlc : om.live ≤ om.cur.count := by
    rw [hlv, ← hL, hok.cnt]; unfold liveH FM; rw [List.length_map]; exact List.length_filter_le _ _
  unfold OrderMaintenance.rebuildStep at hrs
  unfold NxtR at hN
  cases hn : om.nxt with
  | none =>
    rw [hn] at hrs
    simp only at hrs
    have hc := hidle hn
    split at hrs
    · -- the trigger
      next htr =>
      obtain ⟨n, hnew, hprep, hν, hnP⟩ := newCore_lazy S om.nextCapacity
      simp only [bind, Except.bind, hnew] at hrs
      cases hrs
      have hN' : om.nextCapacity ≤ 4 * om.cur.P.N := by
        unfold OrderMaintenance.nextCapacity
        have : (om.cur.count + (om.cur.P.L + 2)) / (om.KB - 1) ≤
            (om.cur.count + (om.cur.P.L + 2)) / 3 := Nat.div_le_div_left (by omega) (by norm_num)
        apply Nat.mul_le_mul_left 4
        apply max_le
        · omega
        · omega
      have hHb := S.prepB _ _ hN'
      rw [hLeq] at hHb
      refine ⟨hW', hlv, hkb, hbig, hcur,
        fun h => by simp only [reduceCtorEq] at h, fun n' hn' => ?_⟩
      simp only [Option.some.injEq] at hn'
      subst hn'
      refine ⟨om.cur.count, om.live, 0, 0, ⟨?_, ?_, ?_, ?_, hlc, fun _ => ⟨hprep, ?_⟩,
        fun h => by simp only [Bool.false_eq_true] at h⟩⟩
      · change om.cur.count ≤ om.cur.P.N / 2; exact hc
      · change n.P = mk (4 * max (om.live + ((om.cur.count + (om.cur.P.L + 2)) / (om.KB - 1) +
        1)) 16)
        rw [hnP]; rfl
      · change om.cur.count ≤ om.cur.count + 0; omega
      · change om.live + 0 = om.live + 0; rfl
      · change ν n + om.cur.count + (om.KB - 1) * 0 ≤ om.cur.P.L + 2 + om.cur.count
        omega
    · next htr =>
      cases hrs
      refine ⟨hW', hlv, hkb, hbig, hcur, fun _ => ?_, fun n' hn' => (by rw [hn] at hn'; cases hn')⟩
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at htr
      omega
  | some n0 =>
    rw [hn] at hrs hN
    simp only at hrs
    obtain ⟨c₀, live₀, I, D, hM⟩ := hbusy n0 hn
    -- the entry potential
    set Φe := if om.cursorSet then (postOf A.elist om.cursor).length else ν n0 + om.cur.count
      with hΦe
    have hΦ : Φe + (om.KB - 1) * I ≤ om.cur.P.L + 2 + c₀ + om.KB := by
      cases hs : om.cursorSet
      · simp only [hΦe, hs, Bool.false_eq_true, ite_false]; exact (hM.prep hs).2
      · simp only [hΦe, hs, ite_true]; exact (hM.serve hs).2 A hR.inv
    have hC0 : LoopC mk TI PI μ ν Jf nf Rf { om with nxt := none } n0 A om.KB Φe live₀ I D
        (4 * max (live₀ + ((c₀ + (om.cur.P.L + 2)) / (om.KB - 1) + 1)) 16) :=
      hM.loop_entry hok
    obtain ⟨om2, hr2, hW2, hl2, hout⟩ := rebuildLoop_cost S hS (om.KB + 1) om.KB
      { om with nxt := none } n0 A hR hL hI hN hf hlv hC0 (by split <;> omega)
    rw [hrs] at hr2
    injection hr2 with hr2
    subst hr2
    dsimp only at hl2
    rcases hout with ⟨n', h1, h2, h3, hC'⟩ | ⟨h1, h2, h3, h4, h5, h6⟩
    · -- the rebuild goes on
      dsimp only at h2 h3
      have hcur' : om'.cur = om.cur := h2
      refine ⟨hW', by rw [hl2]; exact hlv, by rw [h3]; exact hkb, by rw [hcur']; exact hbig,
        fun A' hA' => (by rw [hcur'] at hA' ⊢; exact hcur A' hA'),
        fun h => (by rw [h1] at h; cases h), fun n'' hn'' => ?_⟩
      rw [h1] at hn''; cases hn''
      refine ⟨c₀, live₀, I, D, ⟨by rw [hcur']; exact hM.c0, ?_, by rw [hcur']; exact hM.ccnt,
        by rw [hl2]; exact hM.live, hM.l0, fun hs => ⟨(hC'.prep hs).1, ?_⟩,
        fun hs => ⟨(hC'.serve hs).1, fun A' hA' => ?_⟩⟩⟩
      · rw [hC'.nP, hcur', h3]
      · have h0 := (hC'.prep hs).2
        rw [hcur', h3]
        rw [hcur', h3] at h0
        have : (om.KB - 1) * I + om.KB ≤ om.KB * I + om.KB := by
          have := Nat.mul_le_mul_right I (Nat.sub_le om.KB 1); omega
        have hk3 : 3 * I ≤ (om.KB - 1) * I := Nat.mul_le_mul_right I (by omega)
        simp only [Nat.sub_zero] at h0
        omega
      · have h0 := (hC'.serve hs).2
        rw [hcur'] at hA'
        rw [INV.elist_unique hA' hR.inv, hcur', h3]
        rw [h3] at h0
        simp only [Nat.sub_zero] at h0
        omega
    · -- the swap
      dsimp only at h3 h4
      have hPN : om'.cur.P.N = 4 * max (live₀ + ((c₀ + (om.cur.P.L + 2)) / (om.KB - 1) + 1)) 16
        := by
        rw [h2, S.PN]
      have hge : 64 ≤ om'.cur.P.N := by
        rw [hPN]; have := le_max_right (live₀ + ((c₀ + (om.cur.P.L + 2)) / (om.KB - 1) + 1)) 16;
          omega
      refine ⟨hW', by rw [h4]; exact hlv, by rw [h3]; exact hkb, hge, h5, fun _ => ?_,
        fun n'' hn'' => (by rw [h1] at hn''; cases hn'')⟩
      rw [hPN]
      have := hM.Iq
      have : live₀ + ((c₀ + (om.cur.P.L + 2)) / (om.KB - 1) + 1) ≤
          max (live₀ + ((c₀ + (om.cur.P.L + 2)) / (om.KB - 1) + 1)) 16 := le_max_left _ _
      have : 16 ≤ max (live₀ + ((c₀ + (om.cur.P.L + 2)) / (om.KB - 1) + 1)) 16 := le_max_right _ _
      omega

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model OrderMaintenance.Zeroing
variable {mk : Nat → Params} {TI PI : Core → Prop} {μ : Core → Nat} {ν : Core → Nat}
  {PP : Params → Prop}
  {Jf capf nf Rf : Params → Nat}

theorem countP_insertAfterL (p : Nat → Bool) {a b : Nat} {l : List Nat} (ha : a ∈ l) :
    (OrderMaintenance.Spec.insertAfterL a b l).countP p = l.countP p + (if p b then 1 else 0) := by
  induction l with
  | nil => simp only [List.not_mem_nil] at ha
  | cons x t ih =>
    simp only [OrderMaintenance.Spec.insertAfterL]
    by_cases hxa : x = a
    · rw [ite_eq_left hxa]; simp only [List.countP_cons]; split <;> split <;> omega
    · rw [ite_eq_right hxa]
      have hat : a ∈ t := (List.mem_cons.mp ha).resolve_left (Ne.symm hxa)
      simp only [List.countP_cons, ih hat]; split <;> split <;> omega

theorem liveH_length (c : Core) (l : List Nat) : (liveH c l).length = l.countP (live c) := by
  unfold liveH FM; rw [List.length_map, List.countP_eq_length_filter]

/-- An insertion of a live element adds one live copy. -/
theorem liveH_length_ins {c c' : Core} {l : List Nat} {a b : Nat} (ha : a ∈ l)
    (hrec : ∀ e ∈ l, live c' e = live c e ∧ hdl c' e = hdl c e) (hb : live c' b = true) :
    (liveH c' (OrderMaintenance.Spec.insertAfterL a b l)).length = (liveH c l).length + 1 := by
  rw [liveH_length, liveH_length, countP_insertAfterL _ ha, ite_eq_left hb]
  congr 1
  exact List.countP_congr fun e he => by rw [(hrec e he).1]

/-- **Mirroring an insertion** into `nxt` keeps it in service, within its fill bound. -/
theorem mirrorInsert_cost (S : CostSetup mk TI PI μ ν PP Jf capf nf Rf) {om : OrderMaintenance}
  {n : Core}
    {B : Abs} {D : Nat} {hx : Option Nat} {hy : Nat} (hn : om.nxt = some n)
    (hset : om.cursorSet = true) (hRB : CoreR n B) (hok : CoreOK mk TI μ Jf nf Rf n B.elist)
    (hfill : n.count ≤ 1 + (liveH n B.elist).length + D) (hroom : n.count + 1 ≤ n.P.N)
    (hIB : IdxOK n B om.nxtIdx (liveH n B.elist))
    (hzB : ∀ x, om.nxtIdx.getX x ≠ 0 → x ∈ liveH n B.elist) :
    ∃ om2, om.mirrorInsert hx hy = .ok om2 ∧ om2.cur = om.cur ∧ om2.cursorSet = om.cursorSet ∧
      om2.cursor = om.cursor ∧ om2.KB = om.KB ∧ om2.live = om.live ∧
      ∃ n' B', om2.nxt = some n' ∧ CoreR n' B' ∧ CoreOK mk TI μ Jf nf Rf n' B'.elist ∧
        n'.count ≤ 1 + (liveH n' B'.elist).length + D ∧ n'.P = n.P := by
  -- the anchor in `nxt`, when it is copied
  have hins : ∀ xn, xn ∈ B.elist → ∃ y' n' B', runCore n (insertAfter xn hy) = .ok (y', n') ∧
      CoreR n' B' ∧ CoreOK mk TI μ Jf nf Rf n' B'.elist ∧
      n'.count ≤ 1 + (liveH n' B'.elist).length + D ∧ n'.P = n.P := by
    intro xn hxn
    obtain ⟨n', B', hr', hRB', hB', hrecB, hlyB, hhyB, hyB, _, _, hP'⟩ := core_insert hRB hxn hy
    obtain ⟨n2, hr2, -, hok2, hcnt2, hP2⟩ := hok.insert S hxn hroom hy
    rw [hr'] at hr2; cases hr2
    refine ⟨_, n', B', runCore_ok hr', hRB', by rw [hB']; exact hok2, ?_, hP2⟩
    rw [hB', liveH_length_ins hxn hrecB hlyB, hcnt2]; omega
  unfold OrderMaintenance.mirrorInsert
  rw [hn]
  simp only [hset, Bool.true_and]
  cases hx with
  | none =>
    simp only [ite_true]
    obtain ⟨y', n', B', hr, hRB', hok', hfill', hP'⟩ := hins n.head hRB.head
    simp only [bind, Except.bind, hr]
    exact ⟨_, rfl, rfl, by simp only, rfl, rfl, rfl, n', B', rfl, hRB', hok', hfill', hP'⟩
  | some x =>
    simp only
    by_cases hc : (om.nxtIdx.getX x != 0) = true
    · rw [ite_eq_left hc]
      have hx0 : om.nxtIdx.getX x ≠ 0 := by simpa using hc
      obtain ⟨y', n', B', hr, hRB', hok', hfill', hP'⟩ := hins _ (hIB x (hzB x hx0)).1
      simp only [bind, Except.bind, hr]
      exact ⟨_, rfl, rfl, by simp only, rfl, rfl, rfl, n', B', rfl, hRB', hok', hfill', hP'⟩
    · rw [ite_eq_right hc]
      exact ⟨om, rfl, rfl, by simp only [hset], rfl, rfl, rfl, n, B, hn, hRB, hok, hfill, rfl⟩

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model OrderMaintenance.Zeroing
variable {mk : Nat → Params} {TI PI : Core → Prop} {μ : Core → Nat} {ν : Core → Nat}
  {PP : Params → Prop}
  {Jf capf nf Rf : Params → Nat}

theorem step_ins_length (Sp : OrderMaintenance.Spec.State) (hx : Option Nat) (hv : (insOp
  hx).Valid Sp) :
    (OrderMaintenance.Spec.step Sp (insOp hx)).1.list.length = Sp.list.length + 1 := by
  cases hx with
  | none => rfl
  | some x => exact length_insertAfterL (l := Sp.list) hv

/-- **A wrapper insertion** keeps the wrapper's cost invariant: the insertions into `cur` and
`nxt` take no FALLBACK, and Lemma W's record advances. -/
theorem insert_cost (S : CostSetup mk TI PI μ ν PP Jf capf nf Rf) {om : OrderMaintenance} {Sp :
  OrderMaintenance.Spec.State}
    (hW : WC mk TI PI μ ν Jf nf Rf om Sp) (hx : Option Nat) (hv : (insOp hx).Valid Sp) :
    ∃ om', om.insert mk hx = .ok (Sp.fresh, om') ∧
      WC mk TI PI μ ν Jf nf Rf om' (OrderMaintenance.Spec.step Sp (insOp hx)).1 := by
  obtain ⟨hS, hf, A, hR, hL, hI, hN⟩ := hW.w
  have hnd : (liveH om.cur A.elist).Nodup := hL ▸ hS.1
  have hfresh : om.nextHandle ∉ liveH om.cur A.elist := by
    rw [hL, hf]; exact fun h => Nat.lt_irrefl _ (hS.2 _ h)
  obtain ⟨xi, hxi, hxeq, hxn, hxs⟩ := insertion_position hR hI hx hv
  have hok := hW.cur A hR.inv
  obtain ⟨c', A', hr, hR', hA', hrec, hly, hhy, hyA, hy0, hhead, hPc⟩ :=
    core_insert hR hxi om.nextHandle
  obtain ⟨c2, hr2, -, hok', hcnt', hP2⟩ := hok.insert S hxi (hW.cur_room S) om.nextHandle
  rw [hr] at hr2; cases hr2
  let inserted : OrderMaintenance := {
    om with
    cur := c'
    nextHandle := om.nextHandle + 1
    curIdx := om.curIdx.setX om.nextHandle om.cur.E.size }
  obtain ⟨om2, hm, e1, e2, e3, e4, e5, hN2⟩ := mirrorInsert_ok (om := inserted)
    (c' := c') hN hR hnd hxi hxn hxs hA' hyA hrec hly hhy hfresh
  dsimp only [inserted] at hm e1 e2 e3 e4 e5 hN2
  -- Invariant R after the insertion (as in `insert_ok`)
  have hL' : liveH c' A'.elist = (OrderMaintenance.Spec.step Sp (insOp hx)).1.list := by
    rw [hA']
    exact inserted_live_handles hR hf hL hnd hxi hxn hxs hrec hly hhy hyA
  have hW3 : WInv { om2 with live := om2.live + 1 }
      (OrderMaintenance.Spec.step Sp (insOp hx)).1 :=
    WInv.insert_after_mirror hS hf hI hv hR' hL' hA' hxi hrec hly hhy e1 e2 e3 hN2
  -- the cost side of the mirroring
  have hm2 : ∀ om', (inserted : OrderMaintenance).mirrorInsert hx
        om.nextHandle = .ok om' → om' = om2 := by
    intro om' h; rw [hm] at h; injection h with h; exact h.symm
  have hcnt1 : c'.count = om.cur.count + 1 := hcnt'
  have hPc' : c'.P = om.cur.P := hP2
  have hlv3 : om2.live + 1 = (OrderMaintenance.Spec.step Sp (insOp hx)).1.list.length := by
    rw [e4, step_ins_length Sp hx hv, hW.live]
  have hcur3 : ∀ A'', INV om2.cur A'' → CoreOK mk TI μ Jf nf Rf om2.cur A''.elist := by
    intro A'' hA''; rw [e1] at hA'' ⊢
    rw [INV.elist_unique hA'' hR'.inv, hA']; exact hok'
  have hbig3 : 64 ≤ om2.cur.P.N := by rw [e1, hPc']; exact hW.big
  have hcp : om.cur.count + 1 ≤ om.cur.P.N := hW.cur_room S
  have hkb3 : 4 ≤ om2.KB := by rw [e5]; exact hW.kb
  -- the run, once the rebuild step is known
  have finish : ∀ om4, ({ om2 with live := om2.live + 1 } : OrderMaintenance).rebuildStep mk =
    .ok om4 →
      om.insert mk hx = .ok (Sp.fresh, om4) := by
    intro om4 hrb
    unfold OrderMaintenance.insert
    cases hx <;>
    · simp only at hxeq
      subst hxeq
      dsimp only
      rw [onCur_ok hr]
      simp only [bind, Except.bind]
      rw [hm]
      simp only
      rw [hrb, hf]
      rfl
  have hmi_none : om.nxt = none → om2.nxt = none := by
    intro hn
    have : (inserted : OrderMaintenance).mirrorInsert hx
          om.nextHandle = .ok inserted := by
      unfold inserted OrderMaintenance.mirrorInsert; simp only [hn]; rfl
    rw [← hm2 _ this]; exact hn
  cases hn : om.nxt with
  | none =>
    obtain ⟨om4, hrb, hWC4⟩ := rebuildStep_cost S hW3 hlv3 hkb3 hbig3 hcur3
      (fun _ => by
        change om2.cur.count ≤ om2.cur.P.N / 2
        rw [e1, hcnt1, hPc']; have := hW.idle hn; omega)
      (fun n' hn' => by
        exfalso; have := hmi_none hn; simp only at hn'; rw [this] at hn'; cases hn')
    exact ⟨om4, finish om4 hrb, hWC4⟩
  | some n =>
    obtain ⟨c₀, live₀, I, D, hRW⟩ := hW.busy n hn
    have hpostins : ∀ c, c ≠ om.cur.E.size →
        (postOf A'.elist c).length ≤ (postOf A.elist c).length + 1 := by
      intro c hc; rw [hA']; exact postOf_insertAfterL_le (Ne.symm hc) _
    unfold NxtR at hN; rw [hn] at hN
    obtain ⟨B, hRB, hIB, hzB, hcs⟩ := hN
    cases hs : om.cursorSet with
    | false =>
      have hmi : (inserted : OrderMaintenance).mirrorInsert hx om.nextHandle = .ok inserted := by
        unfold inserted OrderMaintenance.mirrorInsert; simp only [hn, hs, Bool.false_and,
          Bool.false_eq_true, ite_false]; rfl
      have h2 := hm2 _ hmi
      subst h2
      dsimp only [inserted] at *
      obtain ⟨om4, hrb, hWC4⟩ := rebuildStep_cost S hW3 hlv3 hkb3 hbig3 hcur3
        (fun h => by simp only [hn] at h; cases h)
        (fun n' hn' => by
          simp only [hn, Option.some.injEq] at hn'
          subst hn'
          refine ⟨c₀, live₀, I + 1, D, ?_⟩
          exact hRW.insert_mid hW.kb hR.inv
            hPc' hcnt1 rfl rfl rfl rfl (fun _ => rfl)
            (by intro h; rw [hs] at h; cases h))
      exact ⟨om4, finish om4 hrb, hWC4⟩
    | true =>
      obtain ⟨hserve, -⟩ := hRW.serve hs
      obtain ⟨hok0, hfill0⟩ := hserve B hRB.inv
      have hroom := hW.nxt_room S hn hs
      rw [ite_eq_left hs] at hcs
      obtain ⟨pre, post, hsplit, hcpost, -, -⟩ := hcs
      obtain ⟨om2', hmi, f1, f2, f3, f4, f5, n', B', hn2, hRB', hok', hfill', hP'⟩ :=
        mirrorInsert_cost (om := inserted)
          (hx := hx) (hy := om.nextHandle) S hn hs hRB hok0 hfill0 hroom hIB hzB
      have h2 := hm2 _ hmi
      subst h2
      have g1 : om2'.cur = c' := f1
      have g2 : om2'.cursorSet = om.cursorSet := f2
      have g3 : om2'.cursor = om.cursor := f3
      have g4 : om2'.KB = om.KB := f4
      have g5 : om2'.live = om.live := f5
      have hcurNe : om.cursor ≠ om.cur.E.size := by
        intro e
        cases post with
        | nil =>
          simp only [List.headD_eq_head?_getD, List.head?_nil, Option.getD_none] at hcpost
          rw [hcpost] at e
          exact hy0 e.symm
        | cons a t =>
          simp only [List.headD_eq_head?_getD, List.head?_cons, Option.getD_some] at hcpost
          exact hyA (by rw [hsplit, ← e, hcpost]; simp)
      obtain ⟨om4, hrb, hWC4⟩ := rebuildStep_cost S hW3 hlv3 hkb3 hbig3 hcur3
        (fun h => by simp only at h; rw [hn2] at h; cases h)
        (fun n'' hn'' => by
          simp only [hn2, Option.some.injEq] at hn''
          subst hn''
          refine ⟨c₀, live₀, I + 1, D, ?_⟩
          apply hRW.insert_mid (om' := { om2' with live := om2'.live + 1 }) hW.kb hR.inv
            (by change om2'.cur.P = om.cur.P; rw [g1, hPc'])
            (by change om2'.cur.count = _; rw [g1, hcnt1])
            (by change om2'.live + 1 = om.live + 1; rw [g5])
            g4 g2 hP' (by intro h; rw [hs] at h; cases h)
          intro _
          refine ⟨fun B'' hB'' => ?_, fun A'' hA'' => ?_⟩
          · rw [INV.elist_unique hB'' hRB'.inv]; exact ⟨hok', hfill'⟩
          · change INV om2'.cur A'' at hA''
            rw [g1] at hA''
            change (postOf A''.elist om2'.cursor).length ≤ _
            rw [g3, INV.elist_unique hA'' hR'.inv]
            exact hpostins om.cursor hcurNe)
      exact ⟨om4, finish om4 hrb, hWC4⟩

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model OrderMaintenance.Zeroing
variable {mk : Nat → Params} {TI PI : Core → Prop} {μ : Core → Nat} {ν : Core → Nat}
  {PP : Params → Prop}
  {Jf capf nf Rf : Params → Nat}

/-- **Mirroring a deletion** into `nxt` keeps it in service; the fill bound counts the deletion. -/
theorem mirrorDelete_cost (S : CostSetup mk TI PI μ ν PP Jf capf nf Rf) {om : OrderMaintenance}
  {n : Core}
    {B : Abs} {D x : Nat} (hn : om.nxt = some n) (hRB : CoreR n B)
    (hok : CoreOK mk TI μ Jf nf Rf n B.elist) (hfill : n.count ≤ 1 + (liveH n B.elist).length + D)
    (hIB : IdxOK n B om.nxtIdx (liveH n B.elist))
    (hzB : ∀ x, om.nxtIdx.getX x ≠ 0 → x ∈ liveH n B.elist) (hndB : (liveH n B.elist).Nodup) :
    ∃ om2, om.mirrorDelete x = .ok om2 ∧ om2.cur = om.cur ∧ om2.cursorSet = om.cursorSet ∧
      om2.cursor = om.cursor ∧ om2.KB = om.KB ∧ om2.live = om.live ∧
      ∃ n', om2.nxt = some n' ∧ CoreR n' B ∧ CoreOK mk TI μ Jf nf Rf n' B.elist ∧
        n'.count ≤ 1 + (liveH n' B.elist).length + (D + 1) ∧ n'.P = n.P := by
  unfold OrderMaintenance.mirrorDelete
  rw [hn]
  simp only
  by_cases hc : (om.nxtIdx.getX x != 0) = true
  · rw [ite_eq_left hc]
    have hx0 : om.nxtIdx.getX x ≠ 0 := by simpa using hc
    obtain ⟨hxn, hlx, hhx⟩ := hIB x (hzB x hx0)
    obtain ⟨n', hr, hRB', hL', -, -, -, -⟩ := core_kill hRB hxn hlx hndB
    obtain ⟨n2, hr2, hok2, hcnt2, hP2⟩ := hok.markDead S (om.nxtIdx.getX x)
    rw [hr] at hr2; cases hr2
    simp only [bind, Except.bind, runCore_ok hr]
    refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, n', rfl, hRB', hok2, ?_, hP2⟩
    have hmem : hdl n (om.nxtIdx.getX x) ∈ liveH n B.elist := FM_mem_of _ _ hxn hlx
    rw [hL', List.length_erase_of_mem hmem, hcnt2]
    have := List.length_pos_of_mem hmem
    omega
  · rw [ite_eq_right hc]
    exact ⟨om, rfl, rfl, rfl, rfl, rfl, rfl, n, hn, hRB, hok, by omega, rfl⟩

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model OrderMaintenance.Zeroing
variable {mk : Nat → Params} {TI PI : Core → Prop} {μ : Core → Nat} {ν : Core → Nat}
  {PP : Params → Prop}
  {Jf capf nf Rf : Params → Nat}

/-- **A wrapper deletion** keeps the wrapper's cost invariant. -/
theorem delete_cost (S : CostSetup mk TI PI μ ν PP Jf capf nf Rf) {om : OrderMaintenance} {Sp :
  OrderMaintenance.Spec.State}
    (hW : WC mk TI PI μ ν Jf nf Rf om Sp) {x : Nat} (hv : x ∈ Sp.list) :
    ∃ om', om.delete mk x = .ok om' ∧ WC mk TI PI μ ν Jf nf Rf om' (OrderMaintenance.Spec.step
      Sp (.delete x)).1 := by
  obtain ⟨hS, hf, A, hR, hL, hI, hN⟩ := hW.w
  have hnd : (liveH om.cur A.elist).Nodup := hL ▸ hS.1
  obtain ⟨hxi, hlx, hhx⟩ := hI x hv
  obtain ⟨c', hr, hR', hL', hrec, hhdl, _, hdead⟩ := core_kill hR hxi hlx hnd
  have hok := hW.cur A hR.inv
  obtain ⟨c2, hr2, hok', hcnt', hP2⟩ := hok.markDead S (om.curIdx.getX x)
  rw [hr] at hr2; cases hr2
  obtain ⟨om2, hm, e1, e2, e3, e4, e5, hN2⟩ := mirrorDelete_ok (om := { om with
      cur := c'
      curIdx := om.curIdx.setX x 0 }) (c' := c') hN hR hnd hxi hlx hhx hrec hhdl hdead
  have hW3 : WInv { om2 with live := om2.live - 1 }
      (OrderMaintenance.Spec.step Sp (.delete x)).1 :=
    WInv.delete_after_mirror hS hf hI hv hR' (by rw [hL', hhx, hL]) hhx hrec hhdl
      e1 e2 e3 hN2
  have finish : ∀ om4, ({ om2 with live := om2.live - 1 } : OrderMaintenance).rebuildStep mk =
    .ok om4 →
      om.delete mk x = .ok om4 := by
    intro om4 hrb
    unfold OrderMaintenance.delete
    rw [onCur_ok hr]
    simp only [bind, Except.bind]
    rw [hm]
    exact hrb
  have hm2 : ∀ om', ({ om with cur := c', curIdx := om.curIdx.setX x 0 } :
    OrderMaintenance).mirrorDelete x = .ok om' → om' = om2 := by
    intro om' h; rw [hm] at h; injection h with h; exact h.symm
  have hlen : 1 ≤ Sp.list.length := List.length_pos_of_mem hv
  have hlv3 : om2.live - 1 = (OrderMaintenance.Spec.step Sp (.delete x)).1.list.length := by
    rw [e4, hW.live]; change _ = (Sp.list.erase x).length; rw [List.length_erase_of_mem hv]
  have hcur3 : ∀ A'', INV om2.cur A'' → CoreOK mk TI μ Jf nf Rf om2.cur A''.elist := by
    intro A'' hA''; rw [e1] at hA'' ⊢; rw [INV.elist_unique hA'' hR'.inv]; exact hok'
  have hPc' : c'.P = om.cur.P := hP2
  have hbig3 : 64 ≤ om2.cur.P.N := by rw [e1, hPc']; exact hW.big
  have hkb3 : 4 ≤ om2.KB := by rw [e5]; exact hW.kb
  have hlv0 : om.live = Sp.list.length := hW.live
  cases hn : om.nxt with
  | none =>
    have hmi : ({ om with cur := c', curIdx := om.curIdx.setX x 0 } :
      OrderMaintenance).mirrorDelete x = .ok { om with cur := c', curIdx := om.curIdx.setX x 0 }
        := by
      unfold OrderMaintenance.mirrorDelete; simp only [hn]; rfl
    have h2 := hm2 _ hmi
    subst h2
    obtain ⟨om4, hrb, hWC4⟩ := rebuildStep_cost S hW3 hlv3 hkb3 hbig3 hcur3
      (fun _ => by
        change c'.count ≤ c'.P.N / 2
        rw [hcnt', hPc']; have := hW.idle hn; omega)
      (fun n' hn' => by simp only [hn] at hn'; cases hn')
    exact ⟨om4, finish om4 hrb, hWC4⟩
  | some n =>
    obtain ⟨c₀, live₀, I, D, hRW⟩ := hW.busy n hn
    have hN0 := hN
    unfold NxtR at hN0; rw [hn] at hN0
    obtain ⟨B, hRB, hIB, hzB, hcs⟩ := hN0
    cases hs : om.cursorSet with
    | false =>
      rw [ite_eq_right (by simp only [hs, Bool.false_eq_true, not_false_eq_true])] at hcs
      subst hcs
      have hx0 : om.nxtIdx.getX x = 0 := by
        by_contra h; have := hzB x h; rw [liveH_initAbs hRB] at this; simp only [
            List.not_mem_nil] at this
      have hmi : ({ om with cur := c', curIdx := om.curIdx.setX x 0 } :
        OrderMaintenance).mirrorDelete x = .ok { om with cur := c', curIdx := om.curIdx.setX x 0
          } := by
        unfold OrderMaintenance.mirrorDelete; simp only [hn, hx0, bne_self_eq_false,
          Bool.false_eq_true, ite_false]
        rfl
      have h2 := hm2 _ hmi
      subst h2
      obtain ⟨om4, hrb, hWC4⟩ := rebuildStep_cost S hW3 hlv3 hkb3 hbig3 hcur3
        (fun h => by simp only [hn] at h; cases h)
        (fun n' hn' => by
          simp only [hn, Option.some.injEq] at hn'
          subst hn'
          refine ⟨c₀, live₀, I, D + 1, ?_⟩
          exact hRW.delete_mid hW.kb hR.inv (by rw [hW.live]; exact hlen)
            hPc' hcnt' rfl rfl rfl rfl (fun _ => rfl)
            (by intro h; rw [hs] at h; cases h))
      exact ⟨om4, finish om4 hrb, hWC4⟩
    | true =>
      obtain ⟨hserve, -⟩ := hRW.serve hs
      obtain ⟨hok0, hfill0⟩ := hserve B hRB.inv
      rw [ite_eq_left hs] at hcs
      obtain ⟨pre, post, hsplit, hcpost, -, hLB⟩ := hcs
      have hndB : (liveH n B.elist).Nodup := by
        rw [hLB]; exact (FM_sub_nodup (hsplit ▸ hnd)).1
      obtain ⟨om2', hmi, f1, f2, f3, f4, f5, n', hn2, hRB', hok', hfill', hP'⟩ :=
        mirrorDelete_cost (om := { om with cur := c', curIdx := om.curIdx.setX x 0 }) (x := x)
          S hn hRB hok0 hfill0 hIB hzB hndB
      have h2 := hm2 _ hmi
      subst h2
      have g1 : om2'.cur = c' := f1
      have g2 : om2'.cursorSet = om.cursorSet := f2
      have g3 : om2'.cursor = om.cursor := f3
      have g4 : om2'.KB = om.KB := f4
      have g5 : om2'.live = om.live := f5
      obtain ⟨om4, hrb, hWC4⟩ := rebuildStep_cost S hW3 hlv3 hkb3 hbig3 hcur3
        (fun h => by simp only at h; rw [hn2] at h; cases h)
        (fun n'' hn'' => by
          simp only [hn2, Option.some.injEq] at hn''
          subst hn''
          refine ⟨c₀, live₀, I, D + 1, ?_⟩
          apply hRW.delete_mid (om' := { om2' with live := om2'.live - 1 }) hW.kb hR.inv
            (by rw [hW.live]; exact hlen)
            (by change om2'.cur.P = om.cur.P; rw [g1, hPc'])
            (by change om2'.cur.count = _; rw [g1, hcnt'])
            (by change om2'.live - 1 = om.live - 1; rw [g5])
            g4 g2 hP' (by intro h; rw [hs] at h; cases h)
          intro _
          refine ⟨fun B'' hB'' => ?_, fun A'' hA'' => ?_⟩
          · rw [INV.elist_unique hB'' hRB'.inv]; exact ⟨hok', hfill'⟩
          · change INV om2'.cur A'' at hA''
            rw [g1] at hA''
            change (postOf A''.elist om2'.cursor).length ≤ _
            rw [g3, INV.elist_unique hA'' hR'.inv])
      exact ⟨om4, finish om4 hrb, hWC4⟩

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model OrderMaintenance.Zeroing
variable {mk : Nat → Params} {TI PI : Core → Prop} {μ : Core → Nat} {ν : Core → Nat}
  {PP : Params → Prop}
  {Jf capf nf Rf : Params → Nat}

/-- **Initialization** establishes the wrapper's cost invariant. -/
theorem init_cost (S : CostSetup mk TI PI μ ν PP Jf capf nf Rf) {KB : Nat} (hKB : 4 ≤ KB) :
    ∃ om, OrderMaintenance.init mk KB = .ok om ∧ WC mk TI PI μ ν Jf nf Rf om
      OrderMaintenance.Spec.State.empty := by
  obtain ⟨om, hinit, hW⟩ := init_ok S.core KB
  obtain ⟨n, hn, hok, hcnt, hP⟩ := newCore_eager S minimumCapacity
  have hom : om = { cur := n, KB := KB } := by
    unfold OrderMaintenance.init at hinit
    simp only [bind, Except.bind, hn] at hinit
    injection hinit with h; exact h.symm
  subst hom
  refine ⟨_, hinit, hW, rfl, hKB, ?_, fun A hA => ?_, fun _ => ?_, fun n' hn' => by cases hn'⟩
  · change 64 ≤ n.P.N; rw [hP, S.PN]; rfl
  · obtain ⟨A0, hA0, hel⟩ := hok.inv
    rw [INV.elist_unique hA hA0, hel]; exact hok
  · change n.count < n.P.N / 2; rw [hcnt, hP, S.PN]; decide

/-- **Each operation** keeps the wrapper's cost invariant. -/
theorem apply_cost (S : CostSetup mk TI PI μ ν PP Jf capf nf Rf) {om : OrderMaintenance} {Sp :
  OrderMaintenance.Spec.State}
    (hW : WC mk TI PI μ ν Jf nf Rf om Sp) {op : OrderMaintenance.Spec.Op} (hv : op.Valid Sp) :
    ∃ om', om.apply mk op = .ok ((OrderMaintenance.Spec.step Sp op).2, om') ∧
      WC mk TI PI μ ν Jf nf Rf om' (OrderMaintenance.Spec.step Sp op).1 := by
  cases op with
  | insertFirst =>
    obtain ⟨om', h, hW'⟩ := insert_cost S hW none hv
    exact ⟨om', by simp only [OrderMaintenance.apply, bind, Except.bind, h]; rfl, hW'⟩
  | insertAfter x =>
    obtain ⟨om', h, hW'⟩ := insert_cost S hW (some x) hv
    exact ⟨om', by simp only [OrderMaintenance.apply, bind, Except.bind, h]; rfl, hW'⟩
  | delete x =>
    obtain ⟨om', h, hW'⟩ := delete_cost S hW hv
    exact ⟨om', by simp only [OrderMaintenance.apply, bind, Except.bind, h]; rfl, hW'⟩
  | order x y =>
    exact ⟨om, by
      simp only [OrderMaintenance.apply, bind, Except.bind, order_ok hW.w hv.1 hv.2]
      rfl, hW⟩

/-- **The wrapper's cost theorem (Level F).** Under the setup, the structure initializes into a
state satisfying the cost invariant, and every valid operation keeps it. In every such state,
both cores satisfy the cost invariant within their capacities, so each of their insertions takes
no FALLBACK (`CoreOK.insert`, `insertAfter_cost`). -/
theorem wrapper_cost (S : CostSetup mk TI PI μ ν PP Jf capf nf Rf) {KB : Nat} (hKB : 4 ≤ KB) :
    (∃ om, OrderMaintenance.init mk KB = .ok om ∧ WC mk TI PI μ ν Jf nf Rf om
      OrderMaintenance.Spec.State.empty) ∧
    ∀ om Sp op, WC mk TI PI μ ν Jf nf Rf om Sp → op.Valid Sp →
      ∃ om', om.apply mk op = .ok ((OrderMaintenance.Spec.step Sp op).2, om') ∧
        WC mk TI PI μ ν Jf nf Rf om' (OrderMaintenance.Spec.step Sp op).1 :=
  ⟨init_cost S hKB, fun _ _ _ hW hv => apply_cost S hW hv⟩

/-- In a state satisfying the wrapper's cost invariant, `cur` is a core in service with room for
an insertion, and so is `nxt` once its preparation is over. -/
theorem WC.cores {om : OrderMaintenance} {Sp : OrderMaintenance.Spec.State} (S : CostSetup mk TI
  PI μ ν PP Jf capf nf Rf)
    (h : WC mk TI PI μ ν Jf nf Rf om Sp) :
    (∀ A, INV om.cur A → CoreOK mk TI μ Jf nf Rf om.cur A.elist) ∧
      om.cur.count + 1 ≤ om.cur.P.N ∧
      ∀ n, om.nxt = some n → om.cursorSet = true →
        (∀ B, INV n B → CoreOK mk TI μ Jf nf Rf n B.elist) ∧ n.count + 1 ≤ n.P.N := by
  refine ⟨h.cur, h.cur_room S, fun n hn hs => ⟨fun B hB => ?_, h.nxt_room S hn hs⟩⟩
  obtain ⟨c₀, live₀, I, D, hRW⟩ := h.busy n hn
  exact ((hRW.serve hs).1 B hB).1

end OrderMaintenance.Proof
