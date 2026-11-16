/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Top.Inv


/-!
# M5: consequences of the order invariant

* live ancestors: `anc c j` is a live node of height `j` (`Shape.anc_live`), the root at `H`;
* children are exactly the live entries whose parent is the node (`Shape.mem_children`);
* true weights add up over children (`Shape.tw_kids`);
* ranges are contiguous (`Shape.rng_between`).
-/


@[expose] public section

namespace OrderMaintenance.Proof.Top

open OrderMaintenance.Model OrderMaintenance.Proof
/-! ### Counting -/

theorem sum_ite_eq_count {f : Nat} (K : List Nat) :
    (K.map fun e => if f = e then 1 else 0).sum = K.count f := by
  induction K with
  | nil => simp only [List.map_nil, List.sum_nil,  List.count_nil]
  | cons e K ih =>
    simp only [List.map_cons, List.sum_cons, ih, List.count_cons]
    by_cases h : f = e
    · subst h; simp only [↓reduceIte, BEq.rfl]; omega
    · simp only [h, ↓reduceIte, zero_add, beq_iff_eq, Ne.symm h, add_zero]

/-- Counting by the value of `f`, over a list of distinct values. -/
theorem length_filter_mem (cl K : List Nat) (f : Nat → Nat) (hK : K.Nodup) :
    (cl.filter fun c => f c ∈ K).length = (K.map fun e => (cl.filter fun c => f c =
      e).length).sum := by
  induction cl with
  | nil => simp only [List.filter_nil, List.length_nil, List.map_const', List.sum_replicate,
      nsmul_zero]
  | cons c cl ih =>
    have hsplit : (K.map fun e => ((c :: cl).filter fun c => f c = e).length) =
        (K.map fun e => (if f c = e then 1 else 0) + (cl.filter fun c => f c = e).length) := by
      apply List.map_congr_left; intro e _
      rw [List.filter_cons]; split <;> simp_all ; omega
    rw [hsplit, List.sum_map_add, ← ih, sum_ite_eq_count, List.filter_cons]
    by_cases hm : f c ∈ K
    · rw [List.count_eq_one_of_mem hK hm]; simp only [hm, decide_true, ↓reduceIte,
        List.length_cons]; omega
    · rw [List.count_eq_zero_of_not_mem hm]; simp only [hm, decide_false, Bool.false_eq_true,
        ↓reduceIte, zero_add]

/-- Two nodup lists with the same members have the same length. -/
theorem length_eq_of_mem_iff {l l' : List Nat} (h : l.Nodup) (h' : l'.Nodup)
    (hm : ∀ x, x ∈ l ↔ x ∈ l') : l.length = l'.length := by
  have := List.Perm.length_eq ((List.perm_ext_iff_of_nodup h h').mpr hm)
  exact this

variable {s : TS} {cl : List Nat} {ord : Nat → List Nat}

/-! ### Live ancestors -/

theorem Shape.anc_live (S : Shape s cl ord) {c : Nat} (hc : c ∈ cl) :
    ∀ j, 1 ≤ j → j ≤ s.P.H → liveN s (anc s c j) ∧ ht s (anc s c j) = j
  | 0, h, _ => absurd h (by omega)
  | 1, _, _ => ⟨(S.lp c hc).1, (S.lp c hc).2.1⟩
  | j + 2, _, hj => by
    obtain ⟨hl, hh⟩ := S.anc_live hc (j + 1) (by omega) (by omega)
    obtain ⟨h1, h2, -⟩ := S.up _ hl (by omega)
    exact ⟨h1, by rw [show anc s c (j + 2) = (nd s (anc s c (j + 1))).livePar from rfl, h2, hh]⟩

theorem anc_succ (c j : Nat) (hj : 1 ≤ j) : anc s c (j + 1) = (nd s (anc s c j)).livePar := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rfl

theorem Shape.anc_mem (S : Shape s cl ord) {c : Nat} (hc : c ∈ cl) {j : Nat} (hj : j ≤ s.P.H) :
    anc s c j ∈ ord j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj1
  · rw [S.ord0]; exact hc
  · obtain ⟨hl, hh⟩ := S.anc_live hc j hj1 hj
    exact (S.ordMem j hj1 hj _).mpr ⟨hl.1, hh⟩

theorem Shape.anc_root (S : Shape s cl ord) {c : Nat} (hc : c ∈ cl) : anc s c s.P.H = s.P.H := by
  have := S.anc_mem hc (le_refl s.P.H)
  rw [S.root.1] at this; simpa using this

theorem Shape.anc_top (S : Shape s cl ord) {c : Nat} (hc : c ∈ cl) :
    anc s c (s.P.H + 1) = NIL := by
  rw [anc_succ c _ (by have := S.H3; omega), S.anc_root hc]; exact S.root.2.2

/-! ### Children -/

/-- The parent of a live node or chunk at height `h` is its live parent. -/
theorem par_live {h e : Nat} (he : h = 0 ∨ liveN s e) :
    par s h e = if h = 0 then lpr s e else (nd s e).livePar := by
  unfold par
  by_cases h0 : h = 0
  · simp only [h0, ↓reduceIte]
  · rcases he with he | he
    · exact absurd he h0
    · simp only [h0, ↓reduceIte, he.2, Bool.false_eq_true]

/-- The children of a live node are the live entries (chunks at height 1) whose parent it is. -/
theorem Shape.mem_children (S : Shape s cl ord) {u : Nat} (hu : liveN s u) {e : Nat} :
    e ∈ (nd s u).children ↔
      (if ht s u = 1 then e ∈ cl else liveN s e ∧ ht s e = ht s u - 1) ∧
        par s (ht s u - 1) e = u := by
  obtain ⟨hnd, hsub, hk⟩ := S.kids u hu
  obtain ⟨hh1, hhH⟩ := S.htN u hu.1
  constructor
  · intro he
    obtain ⟨hp, hl⟩ := hk e he
    refine ⟨?_, hp⟩
    have hmem := hsub.subset he
    split
    · next h1 => rw [h1, Nat.sub_self, S.ord0] at hmem; exact hmem
    · next h1 =>
      have hl' := hl (by omega)
      exact ⟨hl', ((S.ordMem (ht s u - 1) (by omega) (by omega) e).mp hmem).2⟩
  · rintro ⟨hm, hp⟩
    split at hm
    · next h1 =>
      rw [h1, Nat.sub_self] at hp
      rw [par_live (Or.inl rfl)] at hp; simp only [↓reduceIte] at hp
      have := (S.lp e hm).2.2; rw [hp] at this; exact this
    · next h1 =>
      obtain ⟨hl, hhe⟩ := hm
      rw [par_live (Or.inr hl), ite_eq_right (by omega)] at hp
      have := (S.up e hl (by omega)).2.2; rw [hp] at this; exact this

/-! ### Weights -/

/-- A chunk is below a live node of height `h ≥ 2` iff it is below one of its children. -/
theorem Shape.anc_eq_iff (S : Shape s cl ord) {u : Nat} (hu : liveN s u) (h2 : 2 ≤ ht s u)
    {c : Nat} (hc : c ∈ cl) :
    anc s c (ht s u) = u ↔ anc s c (ht s u - 1) ∈ (nd s u).children := by
  obtain ⟨hh1, hhH⟩ := S.htN u hu.1
  obtain ⟨hl, hh⟩ := S.anc_live hc (ht s u - 1) (by omega) (by omega)
  rw [S.mem_children hu, ite_eq_right (by omega), par_live (Or.inr hl), ite_eq_right (by omega)]
  have e : anc s c (ht s u) = (nd s (anc s c (ht s u - 1))).livePar := by
    rw [← anc_succ c _ (by omega)]; congr 1; omega
  rw [e]
  exact ⟨fun h => ⟨⟨hl, hh⟩, h⟩, fun h => h.2⟩

/-- **True weights add up**: a live node of height `≥ 2` weighs the sum of its children. -/
theorem Shape.tw_kids (S : Shape s cl ord) {u : Nat} (hu : liveN s u) (h2 : 2 ≤ ht s u) :
    tw s cl u = ((nd s u).children.map (tw s cl)).sum := by
  obtain ⟨hnd, -, hk⟩ := S.kids u hu
  unfold tw
  have h1 : (cl.filter fun c => anc s c (ht s u) = u) =
      (cl.filter fun c => anc s c (ht s u - 1) ∈ (nd s u).children) := by
    apply List.filter_congr; intro c hc
    rw [decide_eq_decide]; exact S.anc_eq_iff hu h2 hc
  rw [h1, length_filter_mem _ _ _ hnd]
  congr 1
  apply List.map_congr_left; intro e he
  have hl := (hk e he).2 h2
  have hhe : ht s e = ht s u - 1 := by
    have := ((S.mem_children hu).mp he).1; rw [ite_eq_right (by omega)] at this; exact this.2
  rw [hhe]

/-- A live node of height 1 weighs its number of children. -/
theorem Shape.tw_one (S : Shape s cl ord) {u : Nat} (hu : liveN s u) (h1 : ht s u = 1) :
    tw s cl u = (nd s u).children.length := by
  obtain ⟨hnd, -, -⟩ := S.kids u hu
  unfold tw
  rw [h1]
  refine length_eq_of_mem_iff ((S.ord0 ▸ S.ordNodup 0).filter _) hnd fun c => ?_
  rw [S.mem_children hu, ite_eq_left h1, h1, Nat.sub_self, par_live (Or.inl rfl), ite_eq_left rfl,
    List.mem_filter]
  simp only [anc]
  exact ⟨fun h => ⟨h.1, of_decide_eq_true h.2⟩, fun h => ⟨h.1, decide_eq_true h.2⟩⟩

theorem tw_le (cl : List Nat) (u : Nat) : tw s cl u ≤ cl.length := List.length_filter_le _ _

/-! ### Ranges -/

/-- **Ranges are contiguous.** -/
theorem Shape.rng_between (S : Shape s cl ord) {u c d e : Nat} (hu : isN s u)
    (hc : c ∈ rng s cl u) (hd : d ∈ rng s cl u) (hce : Before cl c e) (hed : Before cl e d) :
    e ∈ rng s cl u := by
  obtain ⟨hh1, hhH⟩ := S.htN u hu
  simp only [rng, List.mem_filter, decide_eq_true_eq] at hc hd ⊢
  refine ⟨hce.mem_right, ?_⟩
  rcases S.O2 _ hhH c e hce with h1 | h1
  · rw [← h1, hc.2]
  · rcases S.O2 _ hhH e d hed with h2 | h2
    · rw [h2, hd.2]
    · rw [hc.2] at h1; rw [hd.2] at h2
      exact absurd h2 (h1.asymm (S.ordNodup _))

/-! ### The walk's chain -/

/-- Nodes up from a live node are live and at least as high. -/
theorem Shape.upChain_mem (S : Shape s cl ord) :
    ∀ f u x, liveN s u → x ∈ upChain s f u → liveN s x ∧ ht s u ≤ ht s x
  | 0, _, _, _, hx => by simp only [upChain, List.not_mem_nil] at hx
  | f + 1, u, x, hu, hx => by
    unfold upChain at hx
    rw [ite_eq_right hu.1.1] at hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨hu, le_rfl⟩
    · by_cases hH : ht s u < s.P.H
      · obtain ⟨hl, hh, -⟩ := S.up u hu hH
        obtain ⟨h1, h2⟩ := S.upChain_mem f _ x hl hx
        exact ⟨h1, by omega⟩
      · have hroot : u = s.P.H := by
          have := S.htN u hu.1
          have hm := (S.ordMem s.P.H (by have := S.H3; omega) le_rfl u).mpr ⟨hu.1, by omega⟩
          rw [S.root.1] at hm; simpa using hm
        rw [hroot, S.root.2.2] at hx
        cases f <;> simp only [upChain, List.not_mem_nil, ↓reduceIte] at hx

/-! ### Paths and ancestors -/

/-- The parent of the path entry at level `j - 1` is the live ancestor at level `j`. -/
theorem Shape.par_pp (S : Shape s cl ord) {c : Nat} (hc : c ∈ cl) {j : Nat} (hj1 : 1 ≤ j)
    (hj : j ≤ s.P.H) : par s (j - 1) (pp s c (j - 1)) = anc s c j := by
  rcases Nat.lt_or_ge j 2 with h1 | h2
  · have : j = 1 := by omega
    subst this
    simp only [par, tsub_self, ↓reduceIte, pp, anc]
  · have hP := S.P c hc (j - 1) (by omega) (by omega)
    obtain ⟨hl, hh⟩ := S.anc_live hc (j - 1) (by omega) (by omega)
    have e : anc s c j = (nd s (anc s c (j - 1))).livePar := by
      rw [← anc_succ c _ (by omega)]; congr 1; omega
    rw [e]
    rcases hP with hP | ⟨hg, ht⟩
    · rw [hP, par_live (Or.inr hl), ite_eq_right (by omega)]
    · unfold par
      rw [ite_eq_right (by omega), ite_eq_left hg.2]
      obtain ⟨-, -, -, -, -, -, -, -, -, -, hlp, -⟩ := S.ghost _ hg
      rcases ht with ht | ht
      · rw [ht]
      · rw [ht, ← hlp]

/-- Live ancestors are monotone along the chunk list. -/
theorem Shape.anc_mono (S : Shape s cl ord) {c d : Nat} (hcd : Before cl c d) :
    ∀ j, j ≤ s.P.H → anc s c j = anc s d j ∨ Before (ord j) (anc s c j) (anc s d j)
  | 0, _ => Or.inr (by rw [S.ord0]; exact hcd)
  | j + 1, hj => by
    have hc := hcd.mem_left
    have hd := hcd.mem_right
    by_cases he : anc s c (j + 1) = anc s d (j + 1)
    · exact Or.inl he
    · right
      have hmc := S.anc_mem hc hj
      have hmd := S.anc_mem hd hj
      rcases before_total hmc hmd he with h1 | h1
      · exact h1
      · exfalso
        obtain ⟨hlc, hhc⟩ := S.anc_live hc (j + 1) (by omega) hj
        obtain ⟨hld, hhd⟩ := S.anc_live hd (j + 1) (by omega) hj
        have hpc := S.par_pp hc (j := j + 1) (by omega) hj
        have hpd := S.par_pp hd (j := j + 1) (by omega) hj
        simp only [Nat.add_sub_cancel] at hpc hpd
        -- the parents are in the wrong order, so the children are too
        have hlow := S.OT (j + 1) (by omega) hj _ _ (pp s d j) (pp s c j) hld hlc h1
          (by simpa using S.pathEnt d hd j (by omega)) (by simpa using S.pathEnt c hc j (by omega))
          (by simpa using hpd) (by simpa using hpc)
        simp only [Nat.add_sub_cancel] at hlow
        rcases S.O2 j (by omega) c d hcd with h2 | h2
        · exact hlow.ne (S.ordNodup j) h2.symm
        · exact hlow.asymm (S.ordNodup j) h2

end OrderMaintenance.Proof.Top
