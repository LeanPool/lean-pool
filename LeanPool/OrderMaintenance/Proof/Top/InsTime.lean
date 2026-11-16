/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Top.InsShape


/-!
# M5: weights, drain timing and label room after a chunk split

After the split, `y` and `z` sit below `x`'s live ancestors, so those weigh 2 more while their
stored weights lag: they are the job's pending nodes. A ghost one of whose targets is above `x`
is funded by the job.
-/


@[expose] public section

namespace OrderMaintenance.Proof.Top

open OrderMaintenance.Model OrderMaintenance.Proof
/-! ### The live ancestors as an up-chain -/

theorem Shape.upChain_anc {s : TS} {cl : List Nat} {ord : Nat → List Nat} (S : Shape s cl ord)
    {c : Nat} (hc : c ∈ cl) :
    ∀ n j, 1 ≤ j → j + n = s.P.H → ∀ v, v ∈ upChain s (n + 2) (anc s c j) ↔
      ∃ k, j ≤ k ∧ k ≤ s.P.H ∧ v = anc s c k
  | 0, j, hj, hn, v => by
    have hj' : j = s.P.H := by omega
    subst hj'
    have hne : anc s c s.P.H ≠ NIL := (S.anc_live hc _ hj le_rfl).1.1.1
    have hup : (nd s (anc s c s.P.H)).livePar = NIL := by rw [S.anc_root hc]; exact S.root.2.2
    simp only [upChain, ite_eq_right hne, hup,  ↓reduceIte, List.mem_singleton]
    constructor
    · intro h; exact ⟨s.P.H, le_rfl, le_rfl, h⟩
    · rintro ⟨k, h1, h2, h3⟩; rw [h3, show k = s.P.H by omega]
  | n + 1, j, hj, hn, v => by
    have hne : anc s c j ≠ NIL := (S.anc_live hc j hj (by omega)).1.1.1
    have e : upChain s (n + 1 + 2) (anc s c j) = anc s c j :: upChain s (n + 2) (anc s c (j + 1)) := by
      rw [anc_succ c j hj]; simp only [upChain, ite_eq_right hne]
    rw [e, List.mem_cons, S.upChain_anc hc n (j + 1) (by omega) (by omega) v]
    constructor
    · rintro (h | ⟨k, h1, h2, h3⟩)
      · exact ⟨j, le_rfl, by omega, h⟩
      · exact ⟨k, by omega, h2, h3⟩
    · rintro ⟨k, h1, h2, h3⟩
      rcases Nat.eq_or_lt_of_le h1 with e | e
      · left; rw [h3, e]
      · right; exact ⟨k, by omega, h2, h3⟩

/-- A live node is on the up-chain from chunk `c`'s parent iff it is an ancestor of `c`. -/
theorem Shape.upChain_lpr {s : TS} {cl : List Nat} {ord : Nat → List Nat} (S : Shape s cl ord)
    {c : Nat} (hc : c ∈ cl) {v : Nat} (hv : liveN s v) :
    v ∈ upChain s (s.P.H + 1) (lpr s c) ↔ anc s c (ht s v) = v := by
  have h3 := S.H3
  have e : s.P.H + 1 = (s.P.H - 1) + 2 := by omega
  rw [e, show lpr s c = anc s c 1 from rfl, S.upChain_anc hc (s.P.H - 1) 1 le_rfl (by omega) v]
  obtain ⟨h1, h2⟩ := S.htN v hv.1
  constructor
  · rintro ⟨k, hk1, hk2, rfl⟩
    rw [(S.anc_live hc k hk1 hk2).2]
  · intro h; exact ⟨ht s v, h1, h2, h.symm⟩

/-! ### Sums over entries -/

/-- Raising one entry's term by at most 2 raises a sum over distinct entries by at most 2. -/
theorem foldr_bump {l : List Nat} (hl : l.Nodup) (f g : Nat → Nat) (e0 : Nat)
    (hfg : ∀ e ∈ l, e ≠ e0 → g e ≤ f e) (h0 : g e0 ≤ f e0 + 2) :
    l.foldr (fun e acc => acc + g e) 0 ≤ l.foldr (fun e acc => acc + f e) 0 + (if e0 ∈ l then 2 else 0) := by
  induction l with
  | nil => simp
  | cons a r ih =>
    have hn := List.nodup_cons.mp hl
    have ih' := ih hn.2 (fun e he hne => hfg e (by simp [he]) hne)
    simp only [List.foldr_cons, List.mem_cons]
    by_cases ha : a = e0
    · subst ha
      have : a ∉ r := hn.1
      simp only [true_or, ite_true]
      rw [ite_eq_right this] at ih'
      omega
    · have := hfg a (by simp) ha
      by_cases hr : e0 ∈ r
      · simp only [hr, or_true, ite_true]; rw [ite_eq_left hr] at ih'; omega
      · simp only [Ne.symm ha, hr, or_self, ite_false, false_or]; rw [ite_eq_right hr] at ih'; omega

/-! ### Weights after the split -/

section weights
variable {s : Core} {cl : List Nat} {ord : Nat → List Nat} {dr n0 : Nat → Nat}
  (hI : InvJ (ts s) cl ord dr n0 none)
  (hcs : ∀ c, c ∈ cl ↔ 1 ≤ c ∧ c < s.C.size) {x : Nat} (hx : x ∈ cl)
  {f1x i1 : Nat} {t : TS} (F : InsFrame s x f1x i1 t)
include hI hcs hx F

/-- Filtering the chunk list after the split, for a predicate on the chunk each one stands for. -/
theorem ins_filter_len (p : Nat → Nat → Prop) [∀ a b, Decidable (p a b)] (u : Nat) :
    ((clIns cl x s.C.size (s.C.size + 1)).filter fun c =>
        decide (p (if c = s.C.size ∨ c = s.C.size + 1 then x else c) u)).length =
      (cl.filter fun c => decide (p c u)).length + (if p x u then 2 else 0) := by
  obtain ⟨A, B, hcl, hA, hB, hcl'⟩ := ins_cl hI hcs hx
  obtain ⟨hy, hz⟩ := ins_fresh hI hcs hx
  have hxs := (hcs x).mp hx
  have hfr : ∀ c, c ∈ A ∨ c ∈ B → ¬(c = s.C.size ∨ c = s.C.size + 1) := fun c hc => by
    have : c ∈ cl := by rw [hcl]; simp only [List.mem_append, List.mem_cons]; tauto
    rintro (rfl | rfl)
    · exact hy this
    · exact hz this
  have eA : (A.filter fun c => decide (p (if c = s.C.size ∨ c = s.C.size + 1 then x else c) u)) =
      A.filter fun c => decide (p c u) :=
    List.filter_congr (fun c hc => by rw [ite_eq_right (hfr c (Or.inl hc))])
  have eB : (B.filter fun c => decide (p (if c = s.C.size ∨ c = s.C.size + 1 then x else c) u)) =
      B.filter fun c => decide (p c u) :=
    List.filter_congr (fun c hc => by rw [ite_eq_right (hfr c (Or.inr hc))])
  rw [hcl', hcl, List.filter_append, List.filter_append, eA]
  simp only [List.filter_cons, true_or, or_true, ite_true,
    ite_eq_right (show ¬(x = s.C.size ∨ x = s.C.size + 1) by omega)]
  rw [eB]
  by_cases hp : p x u
  · simp only [hp, decide_true, ite_true, List.length_append, List.length_cons]; omega
  · simp only [hp, decide_false, Bool.false_eq_true, ite_false, Nat.add_zero]

theorem ins_tw {u : Nat} (hu : 1 ≤ ht (ts s) u) :
    tw t (clIns cl x s.C.size (s.C.size + 1)) u =
      tw (ts s) cl u + (if anc (ts s) x (ht (ts s) u) = u then 2 else 0) := by
  have h := ins_filter_len hI hcs hx F (fun c u => anc (ts s) c (ht (ts s) u) = u) u
  unfold tw; rw [F.ht, ← h]
  congr 1
  apply List.filter_congr
  intro c _
  by_cases hc : c = s.C.size ∨ c = s.C.size + 1
  · rw [ite_eq_left hc, F.anc_new c hc _ hu]
  · rw [ite_eq_right hc]; push Not at hc; rw [F.anc_old c hc.1 hc.2]

theorem ins_rng_len {u : Nat} (hu : 1 ≤ ht (ts s) u) (hH : ht (ts s) u ≤ s.P.H) :
    (rng t (clIns cl x s.C.size (s.C.size + 1)) u).length =
      (rng (ts s) cl u).length + (if pp (ts s) x (ht (ts s) u) = u then 2 else 0) := by
  have h := ins_filter_len hI hcs hx F (fun c u => pp (ts s) c (ht (ts s) u) = u) u
  unfold rng; rw [F.ht, ← h]
  congr 1
  apply List.filter_congr
  intro c _
  by_cases hc : c = s.C.size ∨ c = s.C.size + 1
  · rw [ite_eq_left hc, F.pp_new c hc _ hu hH]
  · rw [ite_eq_right hc]; push Not at hc; rw [F.pp_old c hc.1 hc.2]

theorem ins_ew_live {u : Nat} (hu : liveN (ts s) u) :
    ew t (clIns cl x s.C.size (s.C.size + 1)) u =
      ew (ts s) cl u + (if anc (ts s) x (ht (ts s) u) = u then 2 else 0) := by
  have h1 := (hI.shape.htN u hu.1).1
  unfold ew; rw [F.draining, ite_eq_right (by rw [hu.2]; simp), ite_eq_right (by rw [hu.2]; simp)]
  exact ins_tw hI hcs hx F h1

theorem ins_ew_ghost {u : Nat} (hu : ghostN (ts s) u) :
    ew t (clIns cl x s.C.size (s.C.size + 1)) u =
      ew (ts s) cl u + (if anc (ts s) x (ht (ts s) u) = (nd (ts s) u).t1 ∨
        anc (ts s) x (ht (ts s) u) = (nd (ts s) u).t2 then 2 else 0) := by
  have S := hI.shape
  obtain ⟨g1, g2, g3, g4, -, -, -, -, -, -, -, -, g13⟩ := S.ghost u hu
  have hne : (nd (ts s) u).t1 ≠ (nd (ts s) u).t2 := by
    have hnd := (S.ordNodup (ht (ts s) u)).sublist g13.sublist
    simp at hnd; exact hnd.1.2
  unfold ew; rw [F.draining, ite_eq_left hu.2, ite_eq_left hu.2, F.t1, F.t2]
  have e1 := ins_tw hI hcs hx F (u := (nd (ts s) u).t1) (by rw [g3]; exact (S.htN u hu.1).1)
  have e2 := ins_tw hI hcs hx F (u := (nd (ts s) u).t2) (by rw [g4]; exact (S.htN u hu.1).1)
  rw [g3] at e1; rw [g4] at e2
  rw [e1, e2]
  by_cases h1 : anc (ts s) x (ht (ts s) u) = (nd (ts s) u).t1
  · have h2 : anc (ts s) x (ht (ts s) u) ≠ (nd (ts s) u).t2 := fun e => hne (h1.symm.trans e)
    rw [ite_eq_left h1, ite_eq_right h2, ite_eq_left (Or.inl h1)]; omega
  · by_cases h2 : anc (ts s) x (ht (ts s) u) = (nd (ts s) u).t2
    · rw [ite_eq_right h1, ite_eq_left h2, ite_eq_left (Or.inr h2)]; omega
    · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right (by tauto)]; omega

theorem ins_upChain : ∀ f v, upChain t f v = upChain (ts s) f v
  | 0, _ => rfl
  | f + 1, v => by simp only [upChain, F.livePar, ins_upChain f]

/-- The split's pending nodes are `x`'s live ancestors. -/
theorem ins_pend {v : Nat} (hv : liveN (ts s) v) :
    v ∈ pend t (some (insJob s x)) ↔ anc (ts s) x (ht (ts s) v) = v := by
  unfold pend wStart
  simp only [insJob]
  rw [F.P, ins_upChain hI hcs hx F, F.lpar, ite_eq_left (Or.inl rfl)]
  exact hI.shape.upChain_lpr hx hv

theorem ins_anc_y (h : Nat) (hh : 1 ≤ h) : anc t (insJob s x).y h = anc (ts s) x h :=
  F.anc_new _ (Or.inl rfl) h hh

theorem ins_funded {v : Nat} (hv : ghostN (ts s) v) :
    funded t (some (insJob s x)) v ↔ (anc (ts s) x (ht (ts s) v) = (nd (ts s) v).t1 ∨
      anc (ts s) x (ht (ts s) v) = (nd (ts s) v).t2) := by
  have h1 := (hI.shape.htN v hv.1).1
  show anc t (insJob s x).y (ht t v) = (nd t v).t1 ∨ anc t (insJob s x).y (ht t v) = (nd t v).t2 ↔ _
  rw [F.ht, F.t1, F.t2, ins_anc_y hI hcs hx F _ h1]

theorem ins_slack (hTP : TopParams s.P) {v : Nat} (hv : ghostN (ts s) v) :
    slack t (some (insJob s x)) v = if anc (ts s) x (ht (ts s) v) = (nd (ts s) v).t1 ∨
      anc (ts s) x (ht (ts s) v) = (nd (ts s) v).t2 then s.P.s else 0 := by
  have h1 := (hI.shape.htN v hv.1).1
  have hfu := ins_funded hI hcs hx F hv
  have hcur : curH t (insJob s x) = 1 := rfl
  show (if anc t (insJob s x).y (ht t v) = (nd t v).t1 ∨ anc t (insJob s x).y (ht t v) = (nd t v).t2 then
    (if curH t (insJob s x) ≤ ht t v then t.P.s else _) else 0) = _
  by_cases hC : anc (ts s) x (ht (ts s) v) = (nd (ts s) v).t1 ∨
      anc (ts s) x (ht (ts s) v) = (nd (ts s) v).t2
  · rw [ite_eq_left (show anc t (insJob s x).y (ht t v) = (nd t v).t1 ∨
      anc t (insJob s x).y (ht t v) = (nd t v).t2 from hfu.mpr hC), ite_eq_left hC, hcur, F.ht, ite_eq_left h1, F.P]
  · rw [ite_eq_right (show ¬(anc t (insJob s x).y (ht t v) = (nd t v).t1 ∨
      anc t (insJob s x).y (ht t v) = (nd t v).t2) from fun h => hC (hfu.mp h)), ite_eq_right hC]

/-- **The drain timing after the split**, the job at its start. -/
theorem ins_time (hTP : TopParams s.P) :
    Timing t (clIns cl x s.C.size (s.C.size + 1)) (some (insJob s x)) := by
  have S := hI.shape
  have Ti := hI.time
  have hs3 := hTP.s3
  have eP : (ts s).P = s.P := rfl
  refine ⟨fun v hv => ?_, fun v hv hp hs => ?_, fun v hv => ?_, fun v hv => ?_, fun v hv => ?_,
    fun v hv => ?_, fun v hv hH => ?_, fun u hu hs => ?_, ?_, ?_⟩
  · rw [F.liveN] at hv
    have h1 := (S.htN v hv.1).1
    have hw := Ti.wts v hv
    simp only [pend, List.not_mem_nil, ite_false, Nat.add_zero] at hw
    rw [F.weight, ins_tw hI hcs hx F h1, ← hw]
    by_cases hp : anc (ts s) x (ht (ts s) v) = v
    · rw [ite_eq_left ((ins_pend hI hcs hx F hv).mpr hp), ite_eq_left hp]
    · rw [ite_eq_right (fun h => hp ((ins_pend hI hcs hx F hv).mp h)), ite_eq_right hp]
  · rw [F.liveN] at hv; rw [F.livePar] at hp; rw [F.srcOf] at hs
    rw [F.weight, F.ht, F.P]; exact Ti.wA v hv hp hs
  · rw [F.ghostN] at hv; rw [F.weight, F.ht, F.P]; exact Ti.wB v hv
  · rw [F.ghostN] at hv
    rw [F.weight, ins_ew_ghost hI hcs hx F hv]
    obtain ⟨a1, a2⟩ := Ti.wF v hv
    split
    · refine ⟨by omega, ?_⟩
      rw [show ew (ts s) cl v + 2 - (nd (ts s) v).weight = ew (ts s) cl v - (nd (ts s) v).weight + 2 by omega]
      omega
    · exact ⟨by omega, by simpa using a2⟩
  · rw [F.ghostN] at hv
    obtain ⟨h1, hH⟩ := S.htN v hv.1
    have hw := Ti.wC v hv
    simp only [slack, Nat.add_zero] at hw
    rw [eP] at hw
    unfold fundOf at hw ⊢
    have hF := Ti.wF v hv
    rw [ins_rng_len hI hcs hx F h1 hH, F.weight, ins_ew_ghost hI hcs hx F hv,
      ins_slack hI hcs hx F hTP hv, F.P]
    by_cases hfd : anc (ts s) x (ht (ts s) v) = (nd (ts s) v).t1 ∨
        anc (ts s) x (ht (ts s) v) = (nd (ts s) v).t2
    · rw [ite_eq_left hfd, ite_eq_left hfd]
      have e : (ew (ts s) cl v + 2 - (nd (ts s) v).weight) / 2 =
          (ew (ts s) cl v - (nd (ts s) v).weight) / 2 + 1 := by omega
      rw [e, Nat.mul_succ]
      split <;> omega
    · rw [ite_eq_right hfd, ite_eq_right hfd, ite_eq_right]
      · simpa using hw
      · intro hp
        rcases S.P x hx _ h1 hH with e | ⟨-, e⟩
        · rw [hp] at e
          have := (S.anc_live hx _ h1 hH).1
          rw [← e] at this; exact absurd hv.2 (by rw [this.2]; simp)
        · rw [hp] at e; exact hfd e
  · rw [F.ghostN] at hv
    have h1 := (S.htN v hv.1).1
    have hw := Ti.wC' v hv
    simp only [funded, ite_false, Nat.sub_zero] at hw
    rw [eP] at hw
    unfold fundOf at hw ⊢
    have hF := Ti.wF v hv
    have hfu := ins_funded hI hcs hx F hv
    rw [F.weight, ins_ew_ghost hI hcs hx F hv, F.P]
    by_cases hfd : anc (ts s) x (ht (ts s) v) = (nd (ts s) v).t1 ∨
        anc (ts s) x (ht (ts s) v) = (nd (ts s) v).t2
    · rw [ite_eq_left hfd, ite_eq_left (hfu.mpr hfd)]
      have e : (ew (ts s) cl v + 2 - (nd (ts s) v).weight) / 2 =
          (ew (ts s) cl v - (nd (ts s) v).weight) / 2 + 1 := by omega
      rw [e, Nat.add_sub_cancel]; exact hw
    · rw [ite_eq_right hfd, ite_eq_right (fun h => hfd (hfu.mp h))]; simpa using hw
  · rw [F.liveN] at hv; rw [F.P] at hH
    have h1 := (S.htN v hv.1).1
    rw [F.ht, F.P, ins_tw hI hcs hx F h1]
    have := Ti.wD v hv hH
    rw [eP] at this
    omega
  · rw [F.liveN] at hu; rw [F.srcOf] at hs; rw [F.P]; exact Ti.big u hu hs
  · intro u hu hH; rw [F.isN] at hu; rw [F.P] at hH; rw [F.ht]; exact Ti.chain u hu hH
  · intro u hu; rw [F.liveN] at hu
    have h1 := (S.htN u hu.1).1
    rw [ins_tw hI hcs hx F h1]; have := Ti.tw1 u hu; omega

theorem ins_ew_ge {u : Nat} (hu : isN (ts s) u) :
    ew (ts s) cl u ≤ ew t (clIns cl x s.C.size (s.C.size + 1)) u := by
  by_cases hd : (nd (ts s) u).draining = true
  · rw [ins_ew_ghost hI hcs hx F ⟨hu, hd⟩]; omega
  · rw [ins_ew_live hI hcs hx F ⟨hu, by simpa using hd⟩]; omega

/-- A node whose table holds `x`'s live ancestor of height `h - 1` serves 2 more after the split. -/
theorem ins_ew_up {X h : Nat} (hX : isN (ts s) X) (hh : ht (ts s) X = h) (h1 : 1 ≤ h)
    (hH : h ≤ s.P.H) (hm : anc (ts s) x (h - 1) ∈ order (ts s) X)
    (hl : h = 1 ∨ liveN (ts s) (anc (ts s) x (h - 1))) :
    ew (ts s) cl X + 2 ≤ ew t (clIns cl x s.C.size (s.C.size + 1)) X := by
  have S := hI.shape
  have hH' : h ≤ (ts s).P.H := hH
  have hent : Ent ord (h - 1) (anc (ts s) x (h - 1)) := S.anc_mem hx (by omega)
  have hT : X ∈ tabs (ts s) (h - 1) (anc (ts s) x (h - 1)) :=
    (S.tabsIff _ _ X hent).mpr ⟨hX, by omega, hm⟩
  have hpar : par (ts s) (h - 1) (anc (ts s) x (h - 1)) = anc (ts s) x h := by
    rw [par_live (hl.elim (fun e => Or.inl (by omega)) Or.inr)]
    by_cases h0 : h - 1 = 0
    · rw [ite_eq_left h0]; rw [show h = 1 by omega]; rfl
    · rw [ite_eq_right h0, ← anc_succ x _ (by omega), show h - 1 + 1 = h by omega]
  obtain ⟨hal, hah⟩ := S.anc_live hx h h1 hH
  rcases S.Q _ _ X hent hT with e | e <;> rw [hpar] at e
  · subst e
    rw [ins_ew_live hI hcs hx F hal, hah, ite_eq_left rfl]
  · have hsn : srcOf (ts s) (anc (ts s) x h) ≠ NIL := fun h' => hX.1 (e.trans h')
    obtain ⟨hg, htg⟩ := S.src _ hal hsn
    rw [← e] at hg htg
    obtain ⟨-, -, g3, -⟩ := S.ghost X hg
    rw [ins_ew_ghost hI hcs hx F hg, hh, ite_eq_left]
    rcases htg with e' | e' <;> [exact Or.inl e'; exact Or.inr e']

/-- The insertion events of the split: one more in each table holding `x`. -/
def drIns (dr : Nat → Nat) (tabs : List Nat) (T : Nat) : Nat := if T ∈ tabs then dr T + 1 else dr T

/-- **The label room after the split.** -/
theorem ins_room (hTP : TopParams s.P) :
    Room t (clIns cl x s.C.size (s.C.size + 1)) (drIns dr (s.cin.getX x)) n0 := by
  have S := hI.shape
  have Ro := hI.room
  have eP : (ts s).P = s.P := rfl
  refine ⟨fun X hX => ?_, fun X hX => ?_, fun X hX h1 => ?_, fun X hX h2 => ?_⟩
  · rw [F.isN] at hX; rw [F.P]
    unfold drIns
    by_cases hXc : X ∈ s.cin.getX x
    · obtain ⟨A', le, Bs, a, b, -, -, htab', hg, -⟩ := ins_table hI hcs hx F hTP hXc
      rw [ite_eq_left hXc]; unfold labs; rw [htab']; exact hg
    · rw [ite_eq_right hXc, ins_labs_old hI hcs hx F hXc]; exact Ro.gaps X hX
  · rw [F.isN] at hX; rw [F.ht, F.P]; exact Ro.n0le X hX
  · rw [F.isN] at hX; rw [F.ht] at h1; rw [F.P]
    have hp := Ro.pot1 X hX h1
    rw [eP] at hp
    have hge := ins_ew_ge hI hcs hx F hX
    unfold drIns
    by_cases hXc : X ∈ s.cin.getX x
    · rw [ite_eq_left hXc]
      have hx1 : x ∈ order (ts s) X := (ins_cinX hI hcs hx hXc).2.2
      have := ins_ew_up hI hcs hx F hX h1 le_rfl (by have : 3 ≤ s.P.H := S.H3; omega) hx1 (Or.inl rfl)
      omega
    · rw [ite_eq_right hXc]; omega
  · rw [F.isN] at hX; rw [F.ht] at h2; rw [F.P, F.ht]
    have hXc : X ∉ s.cin.getX x := fun h => by have := (ins_cinX hI hcs hx h).2.1; omega
    unfold drIns; rw [ite_eq_right hXc]
    have hp := Ro.pot2 X hX h2
    rw [eP] at hp
    have hge := ins_ew_ge hI hcs hx F hX
    have hH := (S.htN X hX).2
    -- old live entries are unchanged
    have hold : oldLive t X = oldLive (ts s) X := by
      unfold oldLive; rw [ins_order_old hI hcs hx F hXc]
      congr 1; apply List.filter_congr; intro e _
      simp only [F.liveN]
    -- growth rises by at most what the node gains
    set e0 := anc (ts s) x (ht (ts s) X - 1) with he0
    have hgr : growth t (clIns cl x s.C.size (s.C.size + 1)) X ≤
        growth (ts s) cl X + (if e0 ∈ (order (ts s) X).filter
          (fun e => decide (liveN (ts s) e) && decide (X < e)) then 2 else 0) := by
      unfold growth
      rw [ins_order_old hI hcs hx F hXc, F.ht, F.P]
      have hfl : ((order (ts s) X).filter fun e => decide (liveN t e) && decide (X < e)) =
          (order (ts s) X).filter fun e => decide (liveN (ts s) e) && decide (X < e) := by
        apply List.filter_congr; intro e _; simp only [F.liveN]
      rw [hfl]
      have hnd : ((order (ts s) X).filter fun e => decide (liveN (ts s) e) && decide (X < e)).Nodup := by
        have := (S.ordNodup _).sublist (S.O1 X hX)
        exact this.filter _
      have hht : ∀ e ∈ order (ts s) X, ht (ts s) e = ht (ts s) X - 1 := fun e he => by
        have hE := S.tabEnt X hX e he
        exact ((S.ordMem _ (by omega) (by omega) e).mp hE).2
      apply foldr_bump hnd
      · intro e he hne
        have hm := (List.mem_filter.mp he).1
        rw [ins_tw hI hcs hx F (by rw [hht e hm]; omega), hht e hm,
          ite_eq_right (fun h => hne h.symm)]
        rw [eP]; omega
      · have h1' : 1 ≤ ht (ts s) e0 := by
          rw [(S.anc_live hx _ (by omega) (by omega)).2]; omega
        rw [ins_tw hI hcs hx F h1', eP]
        split <;> omega
    by_cases hm : e0 ∈ (order (ts s) X).filter (fun e => decide (liveN (ts s) e) && decide (X < e))
    · rw [ite_eq_left hm] at hgr
      have hm' := List.mem_filter.mp hm
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hm'
      have := ins_ew_up hI hcs hx F hX rfl (by omega) hH hm'.1 (Or.inr hm'.2.1)
      rw [hold]; omega
    · rw [ite_eq_right hm] at hgr
      rw [hold]; omega

end weights

end OrderMaintenance.Proof.Top
