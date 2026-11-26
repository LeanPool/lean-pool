/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import LeanPool.FiniteIntegralRelationAlgebras.Cert.Prim
public import LeanPool.FiniteIntegralRelationAlgebras.Cert.Bits

/-!
# Sums over orbit representatives of a group of bit permutations

Fix `t`. A *bit permutation* is given by two lists `(p, q)` describing inverse permutations of
`[0, t)`; it acts on the numbers below `2 ^ t` by moving bit `i` to position `p[i]`
(`RACert.actBits`). For a finite group of bit permutations, given as a list `perms` with the
rows of the multiplication table of a set of generators and a list of inverses
(`RACert.checkBitGroup`), and a function `F` that is
invariant under the group, the sum of `F` over `[0, 2 ^ t)` is the sum of `F` over the minima of
the orbits, weighted by the orbit sizes.

The list of orbit minima is certified in segments: `RACert.checkSeg` checks by computation that
the listed numbers in `[lo, hi)` are minima of their orbits and computes the orbit sizes by
orbit–stabilizer, `RACert.OrbitSeg` is the resulting proposition, `RACert.OrbitSeg.append` glues
adjacent segments, and `RACert.OrbitSeg.sum_eq` is the final identity: no completeness check of
the list of minima is needed beyond the total of the orbit sizes being `2 ^ t`.

The definitions on the hot path (`actBits`, `checkSeg`) are written with recursors and the raw
functions `Nat.lor`, `Nat.shiftLeft`, ... for fast kernel reduction.
-/

@[expose] public section

namespace RACert

/-! ### List access -/

theorem nth_eq_getElem {α : Type} (d : α) {l : List α} {i : ℕ} (h : i < l.length) :
    nth d l i = l[i] := by
  rw [nth_eq_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

theorem nth_mem {α : Type} (d : α) {l : List α} {i : ℕ} (h : i < l.length) : nth d l i ∈ l := by
  rw [nth_eq_getElem d h]
  exact List.getElem_mem h

theorem nth_tail (l : List ℕ) (i : ℕ) : nth 0 l.tail i = nth 0 l (i + 1) := by
  cases l <;> rfl

theorem countP_eq_card_filter_range {α : Type} (d : α) (p : α → Bool) (l : List α) :
    l.countP p = ((Finset.range l.length).filter fun i => p (nth d l i) = true).card := by
  rw [Finset.card_filter]
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.countP_cons, List.length_cons, Finset.sum_range_succ', ih]
    rfl

/-! ### Orbit sums for a finite group acting on `[0, B)` -/

/-- The maps `g 0, …, g (N - 1)` form a group of permutations of `[0, B)`, listed without
repetition. -/
structure IsActGroup (N B : ℕ) (g : ℕ → ℕ → ℕ) : Prop where
  /-- The group is nonempty. -/
  pos : 0 < N
  /-- The maps preserve `[0, B)`. -/
  act_lt : ∀ i < N, ∀ α < B, g i α < B
  /-- The first map is the identity. -/
  one_act : ∀ α < B, g 0 α = α
  /-- The maps are closed under composition. -/
  mul : ∀ i < N, ∀ j < N, ∃ c < N, ∀ α < B, g c α = g i (g j α)
  /-- The maps are closed under inverses. -/
  inv : ∀ i < N, ∃ c < N, ∀ α < B, g c (g i α) = α
  /-- The maps are pairwise distinct. -/
  inj : ∀ i < N, ∀ j < N, (∀ α < B, g i α = g j α) → i = j

/-- The orbit of `α`. -/
def actOrbit (N : ℕ) (g : ℕ → ℕ → ℕ) (α : ℕ) : Finset ℕ :=
  (Finset.range N).image fun i => g i α

/-- The indices of the maps fixing `α`. -/
def actStab (N : ℕ) (g : ℕ → ℕ → ℕ) (α : ℕ) : Finset ℕ :=
  (Finset.range N).filter fun i => g i α = α

namespace IsActGroup

variable {N B : ℕ} {g : ℕ → ℕ → ℕ}

theorem act_inj (h : IsActGroup N B g) {i : ℕ} (hi : i < N) {x y : ℕ} (hx : x < B) (hy : y < B)
    (e : g i x = g i y) : x = y := by
  obtain ⟨c, _, hc⟩ := h.inv i hi
  rw [← hc x hx, e, hc y hy]

theorem mul_cancel (h : IsActGroup N B g) {i j j' c : ℕ} (hi : i < N) (hj : j < N) (hj' : j' < N)
    (hc : ∀ α < B, g c α = g i (g j α)) (hc' : ∀ α < B, g c α = g i (g j' α)) : j = j' :=
  h.inj j hj j' hj' fun α hα =>
    h.act_inj hi (h.act_lt j hj α hα) (h.act_lt j' hj' α hα) (by rw [← hc α hα, hc' α hα])

theorem orbit_subset (h : IsActGroup N B g) {α : ℕ} (hα : α < B) :
    actOrbit N g α ⊆ Finset.range B := by
  intro β hβ
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hβ
  exact Finset.mem_range.mpr (h.act_lt i (Finset.mem_range.mp hi) α hα)

/-- All fibers of `i ↦ g i α` have the size of the stabilizer. -/
theorem card_fiber (h : IsActGroup N B g) {α : ℕ} (hα : α < B) {j : ℕ} (hj : j < N) :
    ((Finset.range N).filter fun i => g i α = g j α).card = (actStab N g α).card := by
  obtain ⟨k, hk, hkact⟩ := h.inv j hj
  apply le_antisymm
  · have hmul := h.mul k hk
    choose! m hm hmact using hmul
    refine Finset.card_le_card_of_injOn m ?_ ?_
    · intro i hi
      simp only [actStab, Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hi ⊢
      exact ⟨hm i hi.1, by rw [hmact i hi.1 α hα, hi.2, hkact α hα]⟩
    · intro i hi i' hi' e
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hi hi'
      exact h.mul_cancel hk hi.1 hi'.1 (hmact i hi.1) (by rw [e]; exact hmact i' hi'.1)
  · have hmul := h.mul j hj
    choose! m hm hmact using hmul
    refine Finset.card_le_card_of_injOn m ?_ ?_
    · intro i hi
      simp only [actStab, Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hi ⊢
      exact ⟨hm i hi.1, by rw [hmact i hi.1 α hα, hi.2]⟩
    · intro i hi i' hi' e
      simp only [actStab, Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hi hi'
      exact h.mul_cancel hj hi.1 hi'.1 (hmact i hi.1) (by rw [e]; exact hmact i' hi'.1)

/-- Orbit–stabilizer. -/
theorem card_orbit_mul_card_stab (h : IsActGroup N B g) {α : ℕ} (hα : α < B) :
    (actOrbit N g α).card * (actStab N g α).card = N := by
  have h1 := Finset.card_eq_sum_card_image (fun i => g i α) (Finset.range N)
  have h2 : ∀ β ∈ (Finset.range N).image (fun i => g i α),
      ((Finset.range N).filter fun i => g i α = β).card = (actStab N g α).card := by
    intro β hβ
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hβ
    exact h.card_fiber hα (Finset.mem_range.mp hj)
  rw [Finset.sum_const_nat h2, Finset.card_range] at h1
  exact h1.symm

/-- If the orbits of `α` and `α'` meet and `α` is the minimum of its orbit, then `α ≤ α'`. -/
theorem le_of_orbit_inter (h : IsActGroup N B g) {α α' : ℕ} (hα : α < B) (hα' : α' < B)
    (hmin : ∀ i < N, α ≤ g i α) {i j : ℕ} (hi : i < N) (hj : j < N) (e : g i α = g j α') :
    α ≤ α' := by
  obtain ⟨k, hk, hkact⟩ := h.inv j hj
  obtain ⟨c, hc, hcact⟩ := h.mul k hk i hi
  have h1 : g c α = α' := by rw [hcact α hα, e, hkact α' hα']
  rw [← h1]
  exact hmin c hc

/-- The union of the orbits of a list of distinct orbit minima. -/
theorem exists_union (h : IsActGroup N B g) {F : ℕ → ℕ}
    (hF : ∀ i < N, ∀ α < B, F (g i α) = F α) :
    ∀ seg : List (ℕ × ℕ), seg.Pairwise (fun a b => a.1 < b.1) →
      (∀ e ∈ seg, e.1 < B ∧ (∀ i < N, e.1 ≤ g i e.1) ∧ e.2 * (actStab N g e.1).card = N) →
      ∃ U : Finset ℕ, U ⊆ Finset.range B ∧ (∀ β ∈ U, ∃ e ∈ seg, β ∈ actOrbit N g e.1) ∧
        U.card = (seg.map Prod.snd).sum ∧ ∑ β ∈ U, F β = (seg.map fun e => e.2 * F e.1).sum
  | [], _, _ => ⟨∅, by simp⟩
  | e :: seg, hp, hall => by
    obtain ⟨hp1, hp2⟩ := List.pairwise_cons.mp hp
    obtain ⟨U, hU1, hU2, hU3, hU4⟩ :=
      h.exists_union hF seg hp2 fun e' he' => hall e' (List.mem_cons_of_mem _ he')
    obtain ⟨hα, hmin, hm⟩ := hall e List.mem_cons_self
    have hcard : (actOrbit N g e.1).card = e.2 := by
      have h1 := h.card_orbit_mul_card_stab hα
      have hpos : 0 < (actStab N g e.1).card := by
        rcases Nat.eq_zero_or_pos (actStab N g e.1).card with h0 | h0
        · rw [h0, Nat.mul_zero] at h1
          exact absurd h1.symm (Nat.pos_iff_ne_zero.mp h.pos)
        · exact h0
      exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans hm.symm)
    have hdisj : Disjoint (actOrbit N g e.1) U := by
      rw [Finset.disjoint_left]
      intro β hβ hβU
      obtain ⟨e', he', hβ'⟩ := hU2 β hβU
      obtain ⟨hα', hmin', _⟩ := hall e' (List.mem_cons_of_mem _ he')
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hβ
      obtain ⟨j, hj, e2⟩ := Finset.mem_image.mp hβ'
      rw [Finset.mem_range] at hi hj
      have h1 : e'.1 ≤ e.1 := h.le_of_orbit_inter hα' hα hmin' hj hi e2
      have h2 : e.1 < e'.1 := hp1 e' he'
      omega
    refine ⟨actOrbit N g e.1 ∪ U, ?_, ?_, ?_, ?_⟩
    · exact Finset.union_subset (h.orbit_subset hα) hU1
    · intro β hβ
      rcases Finset.mem_union.mp hβ with hβ | hβ
      · exact ⟨e, List.mem_cons_self, hβ⟩
      · obtain ⟨e', he', hβ'⟩ := hU2 β hβ
        exact ⟨e', List.mem_cons_of_mem _ he', hβ'⟩
    · rw [Finset.card_union_of_disjoint hdisj, hcard, hU3, List.map_cons, List.sum_cons]
    · rw [Finset.sum_union hdisj, hU4, List.map_cons, List.sum_cons,
        Finset.sum_const_nat (m := F e.1), hcard]
      intro β hβ
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hβ
      exact hF i (Finset.mem_range.mp hi) e.1 hα

/-- A sum of an invariant function is a weighted sum over the minima of the orbits; the list of
minima is complete as soon as the orbit sizes add up to `B`. -/
theorem sum_eq (h : IsActGroup N B g) {F : ℕ → ℕ} (hF : ∀ i < N, ∀ α < B, F (g i α) = F α)
    {seg : List (ℕ × ℕ)} (hp : seg.Pairwise (fun a b => a.1 < b.1))
    (hall : ∀ e ∈ seg, e.1 < B ∧ (∀ i < N, e.1 ≤ g i e.1) ∧ e.2 * (actStab N g e.1).card = N)
    (hM : (seg.map Prod.snd).sum = B) :
    ∑ α ∈ Finset.range B, F α = (seg.map fun e => e.2 * F e.1).sum := by
  obtain ⟨U, hU1, _, hU3, hU4⟩ := h.exists_union hF seg hp hall
  have hU : U = Finset.range B :=
    Finset.eq_of_subset_of_card_le hU1 (by rw [Finset.card_range, hU3, hM])
  rw [← hU, hU4]

end IsActGroup

/-! ### Bit permutations -/

/-- `p` and `q` are inverse permutations of `[0, t)`. -/
noncomputable def checkBitPerm (t : ℕ) (p q : List ℕ) : Bool :=
  allRange t fun i => Nat.blt (nth 0 p i) t && (Nat.blt (nth 0 q i) t &&
    (Nat.beq (nth 0 q (nth 0 p i)) i && Nat.beq (nth 0 p (nth 0 q i)) i))

theorem checkBitPerm_spec {t : ℕ} {p q : List ℕ} (h : checkBitPerm t p q = true) {i : ℕ}
    (hi : i < t) :
    nth 0 p i < t ∧ nth 0 q i < t ∧ nth 0 q (nth 0 p i) = i ∧ nth 0 p (nth 0 q i) = i := by
  have h1 := allRange_iff.mp h i hi
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h1
  exact h1

/-- The loop of `actBits`: move the lowest `n` bits of `α` to the positions listed in `p`
(position `0` beyond the end of `p`), accumulating into `acc`. -/
noncomputable def actAux (n : ℕ) : List ℕ → ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => List ℕ → ℕ → ℕ → ℕ) (fun _ _ acc => acc)
    (fun _ ih p α acc =>
      List.rec (motive := fun _ => ℕ)
        (ih [] (Nat.shiftRight α 1) (Nat.lor acc (Nat.land α 1)))
        (fun x xs _ =>
          ih xs (Nat.shiftRight α 1) (Nat.lor acc (Nat.shiftLeft (Nat.land α 1) x))) p) n

theorem actAux_zero (p : List ℕ) (α acc : ℕ) : actAux 0 p α acc = acc := rfl

theorem actAux_succ (n : ℕ) (p : List ℕ) (α acc : ℕ) :
    actAux (n + 1) p α acc = actAux n p.tail (α >>> 1) (acc ||| ((α &&& 1) <<< nth 0 p 0)) := by
  cases p <;> rfl

theorem testBit_actAux : ∀ (n : ℕ) (p : List ℕ) (α acc j : ℕ),
    (actAux n p α acc).testBit j = true ↔
      acc.testBit j = true ∨ ∃ i < n, nth 0 p i = j ∧ α.testBit i = true
  | 0, p, α, acc, j => by simp [actAux_zero]
  | n + 1, p, α, acc, j => by
    rw [actAux_succ, testBit_actAux n, Nat.exists_lt_succ_left, Nat.testBit_or, Bool.or_eq_true,
      or_assoc]
    refine or_congr Iff.rfl (or_congr ?_ (exists_congr fun i => and_congr Iff.rfl ?_))
    · rcases Nat.mod_two_eq_zero_or_one α with h | h
      · simp [Nat.testBit_zero, h]
      · simp only [Nat.and_one_is_mod, h, Nat.testBit_shiftLeft, ge_iff_le, Bool.and_eq_true,
          decide_eq_true_iff, Nat.testBit_one_eq_true_iff_self_eq_zero, Nat.testBit_zero,
          and_true]
        omega
    · rw [nth_tail, Nat.testBit_shiftRight, Nat.add_comm]

/-- Move bit `i` of `α` to position `p[i]`, for `i < t`. -/
noncomputable def actBits (t : ℕ) (p : List ℕ) (α : ℕ) : ℕ := actAux t p α 0

theorem testBit_actBits {t : ℕ} {p q : List ℕ} (h : checkBitPerm t p q = true) (α j : ℕ) :
    (actBits t p α).testBit j = (decide (j < t) && α.testBit (nth 0 q j)) := by
  rw [Bool.eq_iff_iff, actBits, testBit_actAux, Bool.and_eq_true, decide_eq_true_iff]
  simp only [Nat.zero_testBit, Bool.false_eq_true, false_or]
  constructor
  · rintro ⟨i, hi, rfl, hα⟩
    obtain ⟨h1, _, h3, _⟩ := checkBitPerm_spec h hi
    exact ⟨h1, by rw [h3]; exact hα⟩
  · rintro ⟨hj, hα⟩
    obtain ⟨_, h2, _, h4⟩ := checkBitPerm_spec h hj
    exact ⟨nth 0 q j, h2, h4, hα⟩

theorem actBits_lt {t : ℕ} {p q : List ℕ} (h : checkBitPerm t p q = true) (α : ℕ) :
    actBits t p α < 2 ^ t :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by
    rw [testBit_actBits h, decide_eq_false (Nat.not_lt.mpr hi), Bool.false_and]

theorem testBit_eq_false_of_lt {α t j : ℕ} (hα : α < 2 ^ t) (hj : ¬ j < t) :
    α.testBit j = false :=
  Nat.testBit_lt_two_pow
    (Nat.lt_of_lt_of_le hα (Nat.pow_le_pow_right (by omega) (Nat.not_lt.mp hj)))

/-! ### Groups of bit permutations -/

/-- The forward list of the `i`-th permutation. -/
noncomputable def pAt (perms : List (List ℕ × List ℕ)) (i : ℕ) : List ℕ :=
  (nth ([], []) perms i).1

/-- The backward list of the `i`-th permutation. -/
noncomputable def qAt (perms : List (List ℕ × List ℕ)) (i : ℕ) : List ℕ :=
  (nth ([], []) perms i).2

/-- The first `t` entries of `p` as a number in base `t`, most significant digit first. For lists
with entries below `t`, comparing codes is comparing the first `t` entries lexicographically. -/
noncomputable def permCode (t : ℕ) (p : List ℕ) : ℕ :=
  ((List.range t).map (nth 0 p)).foldl (fun acc d => Nat.add (Nat.mul acc t) d) 0

theorem permCode_congr {t : ℕ} {p p' : List ℕ} (h : ∀ x < t, nth 0 p x = nth 0 p' x) :
    permCode t p = permCode t p' := by
  unfold permCode
  rw [List.map_congr_left fun x hx => h x (List.mem_range.mp hx)]

/-- `a < l[0] < l[1] < …`. -/
def increasingFrom : ℕ → List ℕ → Bool
  | _, [] => true
  | a, b :: l => Nat.blt a b && increasingFrom b l

/-- `l[0] < l[1] < …`. -/
def increasing : List ℕ → Bool
  | [] => true
  | a :: l => increasingFrom a l

theorem increasingFrom_spec : ∀ {a : ℕ} {l : List ℕ}, increasingFrom a l = true →
    (∀ x ∈ l, a < x) ∧ l.Pairwise (· < ·)
  | _, [], _ => by simp
  | a, b :: l, h => by
    rw [increasingFrom, Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨h1, h2⟩ := increasingFrom_spec h.2
    refine ⟨fun x hx => ?_, List.pairwise_cons.mpr ⟨h1, h2⟩⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact Nat.lt_trans h.1 (h1 x hx)

theorem increasing_spec {l : List ℕ} (h : increasing l = true) : l.Pairwise (· < ·) := by
  cases l with
  | nil => exact List.Pairwise.nil
  | cons a l =>
    obtain ⟨h1, h2⟩ := increasingFrom_spec (a := a) (l := l) h
    exact List.pairwise_cons.mpr ⟨h1, h2⟩

/-- `f l[j] r[j]` for all `j < l.length` (with `r[j] = d` beyond the end of `r`). -/
def allZip {α β : Type} (d : β) (f : α → β → Bool) : List α → List β → Bool
  | [], _ => true
  | a :: l, r => f a (r.headD d) && allZip d f l r.tail

theorem allZip_spec {α β : Type} (d' : α) (d : β) {f : α → β → Bool} :
    ∀ {l : List α} {r : List β}, allZip d f l r = true →
      ∀ j < l.length, f (nth d' l j) (nth d r j) = true
  | [], _, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | a :: l, r, h, j, hj => by
    rw [allZip, Bool.and_eq_true] at h
    cases j with
    | zero => cases r <;> exact h.1
    | succ j =>
      have h1 := allZip_spec d' d h.2 j (Nat.lt_of_succ_lt_succ hj)
      cases r <;> exact h1

/-- `a[x] = b[c[x]]` for all `x < n`, walking along `a` and `c`. -/
noncomputable def eqComp (b : List ℕ) : ℕ → List ℕ → List ℕ → Bool
  | 0, _, _ => true
  | n + 1, a, c => Nat.beq (a.headD 0) (nth 0 b (c.headD 0)) && eqComp b n a.tail c.tail

theorem eqComp_spec {b : List ℕ} : ∀ {n : ℕ} {a c : List ℕ}, eqComp b n a c = true →
    ∀ x < n, nth 0 a x = nth 0 b (nth 0 c x)
  | 0, _, _, _, x, hx => absurd hx (Nat.not_lt_zero x)
  | n + 1, a, c, h, x, hx => by
    rw [eqComp, Bool.and_eq_true, Nat.beq_eq] at h
    cases x with
    | zero =>
      have h1 := h.1
      cases a <;> cases c <;> exact h1
    | succ x =>
      have h1 := eqComp_spec h.2 x (Nat.lt_of_succ_lt_succ hx)
      rw [nth_tail, nth_tail] at h1
      exact h1

/-- `a[x] = b[x]` for all `x < t`. -/
noncomputable def eqOn (t : ℕ) (a b : List ℕ) : Bool :=
  allRange t fun x => Nat.beq (nth 0 a x) (nth 0 b x)

/-- `l` cut into `n` consecutive blocks of length `b`, for faster access to its entries. -/
def blocks {α : Type} (b : ℕ) : ℕ → List α → List (List α)
  | 0, _ => []
  | n + 1, l => l.take b :: blocks b n (l.drop b)

theorem nth_blocks {α : Type} (d : α) {b : ℕ} : ∀ (n : ℕ) (l : List α) (i j : ℕ), i < n → j < b →
    nth d (nth [] (blocks b n l) i) j = nth d l (i * b + j)
  | 0, _, i, _, hi, _ => absurd hi (Nat.not_lt_zero i)
  | n + 1, l, 0, j, _, hj => by
    rw [blocks, nth_cons_zero, nth_eq_getD, nth_eq_getD, List.getD_eq_getElem?_getD,
      List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left hj, Nat.zero_mul, Nat.zero_add]
  | n + 1, l, i + 1, j, hi, hj => by
    rw [blocks, nth_cons_succ, nth_blocks d n _ i j (Nat.lt_of_succ_lt_succ hi) hj, nth_eq_getD,
      nth_eq_getD, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop,
      Nat.succ_mul, Nat.add_comm (i * b) b, Nat.add_assoc]

/-- The block length used by `checkBitGroup`. -/
def blockLen : ℕ := 32

/-- The forward list of the `c`-th permutation, from the list cut into blocks. -/
noncomputable def pAtB (bl : List (List (List ℕ × List ℕ))) (c : ℕ) : List ℕ :=
  (nth ([], []) (nth [] bl (Nat.div c blockLen)) (Nat.mod c blockLen)).1

theorem pAtB_blocks {perms : List (List ℕ × List ℕ)} {c : ℕ} (hc : c < perms.length) :
    pAtB (blocks blockLen perms.length perms) c = pAt perms c := by
  have h1 : c / blockLen < perms.length := Nat.lt_of_le_of_lt (Nat.div_le_self c blockLen) hc
  have h2 : c % blockLen < blockLen := Nat.mod_lt c (by decide)
  rw [pAtB, pAt]
  change (nth ([], []) (nth [] (blocks blockLen perms.length perms) (c / blockLen))
    (c % blockLen)).1 = _
  rw [nth_blocks ([], []) _ _ _ _ h1 h2, Nat.div_add_mod']

/-- The entries `row[k]` with `j + k < row[k]`. -/
def childrenFrom : ℕ → List ℕ → List ℕ
  | _, [] => []
  | j, c :: cs => bif Nat.blt j c then c :: childrenFrom (j + 1) cs else childrenFrom (j + 1) cs

theorem exists_of_mem_childrenFrom : ∀ {j : ℕ} {row : List ℕ} {i : ℕ}, i ∈ childrenFrom j row →
    ∃ k, j + k < i ∧ nth 0 row k = i
  | _, [], _, h => absurd h List.not_mem_nil
  | j, c :: cs, i, h => by
    rw [childrenFrom] at h
    cases hb : Nat.blt j c with
    | false =>
      rw [hb, Bool.cond_false] at h
      obtain ⟨k, hk, e⟩ := exists_of_mem_childrenFrom h
      exact ⟨k + 1, by omega, e⟩
    | true =>
      rw [hb, Bool.cond_true] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨0, Nat.blt_eq.mp hb, rfl⟩
      · obtain ⟨k, hk, e⟩ := exists_of_mem_childrenFrom h
        exact ⟨k + 1, by omega, e⟩

/-- Verify that a generator's multiplication row agrees with composition of permutations. -/
noncomputable def checkMultiplicationRow (t : ℕ) (perms : List (List ℕ × List ℕ))
    (g : ℕ × List ℕ) : Bool :=
  allZip 0 (fun e c => Nat.blt c perms.length &&
    eqComp (pAt perms g.1) t (pAtB (blocks blockLen perms.length perms) c) e.1) perms g.2

/-- Verify that the inverse row agrees with the inverse permutations in the table. -/
noncomputable def checkInverseRow (t : ℕ) (perms : List (List ℕ × List ℕ))
    (inv : List ℕ) : Bool :=
  allZip 0 (fun e c => Nat.blt c perms.length &&
    eqOn t (pAtB (blocks blockLen perms.length perms) c) e.2) perms inv

/-- Group certificate. `perms` is a list of pairs `(p, q)`, and `gens` a list of pairs `(g, row)`
of the index of a generator and its row of the multiplication table, such that

* every pair in `perms` consists of inverse permutations of `[0, t)` (`checkBitPerm`);
* `perms` is nonempty and its first entry is the identity;
* the codes `permCode t p` are strictly increasing along the list: the `p`'s are sorted
  strictly lexicographically by their first `t` entries (in particular they are distinct);
* for every `(g, row)` in `gens` and `j < perms.length`, `row[j]` is an index `c` with
  `p_c[x] = p_g[p_j[x]]` for all `x < t`;
* every index `i ≠ 0` occurs as `row[j]` for some `(g, row)` in `gens` and some `j < i` (so that
  every permutation in the list is a product of generators);
* `inv[i]` is an index `c` with `p_c[x] = q_i[x]` for all `x < t`.

Taking all indices as generators, `gens` is the full multiplication table. -/
noncomputable def checkBitGroup (t : ℕ) (perms : List (List ℕ × List ℕ))
    (gens : List (ℕ × List ℕ)) (inv : List ℕ) : Bool :=
  perms.all (fun e => checkBitPerm t e.1 e.2) &&
  (Nat.blt 0 perms.length &&
  ((allRange t fun x => Nat.beq (nth 0 (pAt perms 0) x) x) &&
  (increasing (perms.map fun e => permCode t e.1) &&
  (gens.all (checkMultiplicationRow t perms) &&
  (Nat.beq (Nat.lor (maskOf (gens.flatMap fun g => childrenFrom 0 g.2)) 1)
      (Nat.sub (Nat.pow 2 perms.length) 1) &&
  checkInverseRow t perms inv)))))

private theorem multiplicationRow_spec {t : ℕ} {perms : List (List ℕ × List ℕ)}
    {g : ℕ × List ℕ} (h : checkMultiplicationRow t perms g = true)
    {j : ℕ} (hj : j < perms.length) : nth 0 g.2 j < perms.length ∧ ∀ x < t,
      nth 0 (pAt perms (nth 0 g.2 j)) x = nth 0 (pAt perms g.1) (nth 0 (pAt perms j) x) := by
  have hrow := allZip_spec ([], []) 0 h j hj
  rw [Bool.and_eq_true, Nat.blt_eq] at hrow
  rw [pAtB_blocks hrow.1] at hrow
  exact ⟨hrow.1, eqComp_spec hrow.2⟩

private theorem generatorReach {N : ℕ} {gens : List (ℕ × List ℕ)}
    (h : Nat.beq (Nat.lor (maskOf (gens.flatMap fun g => childrenFrom 0 g.2)) 1)
      (Nat.sub (Nat.pow 2 N) 1) = true) {i : ℕ} (hpos : 0 < i) (hi : i < N) :
    ∃ g ∈ gens, ∃ j < i, nth 0 g.2 j = i := by
  have hbit : (maskOf (gens.flatMap fun g => childrenFrom 0 g.2) ||| 1).testBit i =
      (2 ^ N - 1).testBit i :=
    congrArg (fun mask => mask.testBit i) (Nat.beq_eq.mp h)
  rw [Nat.testBit_or, testBit_maskOf, Nat.testBit_two_pow_sub_one, decide_eq_true hi,
    Bool.or_eq_true, decide_eq_true_iff, Nat.testBit_one_eq_true_iff_self_eq_zero] at hbit
  rcases hbit with hmem | hzero
  · obtain ⟨g, hg, hchild⟩ := List.mem_flatMap.mp hmem
    obtain ⟨j, hj, hindex⟩ := exists_of_mem_childrenFrom hchild
    exact ⟨g, hg, j, by omega, hindex⟩
  · omega

/-- Every nonidentity permutation in the checked group is one generator times an earlier entry. -/
theorem generatorStep {t : ℕ} {perms : List (List ℕ × List ℕ)}
    {gens : List (ℕ × List ℕ)} {inv : List ℕ} (h : checkBitGroup t perms gens inv = true)
    {i : ℕ} (hpos : 0 < i) (hi : i < perms.length) :
    ∃ g ∈ gens, ∃ j < i, ∀ x < t,
      nth 0 (pAt perms i) x = nth 0 (pAt perms g.1) (nth 0 (pAt perms j) x) := by
  simp only [checkBitGroup, Bool.and_eq_true] at h
  obtain ⟨_, _, _, _, hrows, hcover, _⟩ := h
  obtain ⟨g, hg, j, hj, hindex⟩ := generatorReach hcover hpos hi
  have hrow := (multiplicationRow_spec (List.all_eq_true.mp hrows g hg) (hj.trans hi)).2
  rw [hindex] at hrow
  exact ⟨g, hg, j, hj, hrow⟩

theorem checkBitGroup_spec {t : ℕ} {perms : List (List ℕ × List ℕ)} {gens : List (ℕ × List ℕ)}
    {inv : List ℕ} (h : checkBitGroup t perms gens inv = true) :
    (∀ i < perms.length, checkBitPerm t (pAt perms i) (qAt perms i) = true) ∧
    0 < perms.length ∧
    (∀ x < t, nth 0 (pAt perms 0) x = x) ∧
    (∀ i < perms.length, ∀ j < perms.length,
      (∀ x < t, nth 0 (pAt perms i) x = nth 0 (pAt perms j) x) → i = j) ∧
    (∀ i < perms.length, ∀ j < perms.length, ∃ c < perms.length,
      ∀ x < t, nth 0 (pAt perms c) x = nth 0 (pAt perms i) (nth 0 (pAt perms j) x)) ∧
    (∀ i < perms.length, ∃ c < perms.length,
      ∀ x < t, nth 0 (pAt perms c) x = nth 0 (qAt perms i) x) := by
  simp only [checkBitGroup, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  have hperm : ∀ i < perms.length, checkBitPerm t (pAt perms i) (qAt perms i) = true :=
    fun i hi => List.all_eq_true.mp h1 _ (nth_mem _ hi)
  have hone : ∀ x < t, nth 0 (pAt perms 0) x = x :=
    fun x hx => Nat.beq_eq.mp (allRange_iff.mp h3 x hx)
  have hrow : ∀ g ∈ gens, ∀ j < perms.length, nth 0 g.2 j < perms.length ∧ ∀ x < t,
      nth 0 (pAt perms (nth 0 g.2 j)) x = nth 0 (pAt perms g.1) (nth 0 (pAt perms j) x) :=
    fun g hg j hj => multiplicationRow_spec (List.all_eq_true.mp h5 g hg) hj
  refine ⟨hperm, Nat.blt_eq.mp h2, hone, fun i hi j hj e => ?_, fun i => ?_, fun i hi => ?_⟩
  · have hpw := List.pairwise_iff_getElem.mp (List.pairwise_map.mp (increasing_spec h4))
    have hcode : permCode t (pAt perms i) = permCode t (pAt perms j) := permCode_congr e
    rw [pAt, pAt, nth_eq_getElem _ hi, nth_eq_getElem _ hj] at hcode
    rcases Nat.lt_trichotomy i j with hij | hij | hij
    · exact absurd hcode (Nat.ne_of_lt (hpw i j hi hj hij))
    · exact hij
    · exact absurd hcode.symm (Nat.ne_of_lt (hpw j i hj hi hij))
  · induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi j hj
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · exact ⟨j, hj, fun x hx => (hone _ (checkBitPerm_spec (hperm j hj) hx).1).symm⟩
      · obtain ⟨g, hg, k, hk, hki⟩ := generatorReach h6 hpos hi
        have hk' : k < perms.length := Nat.lt_trans hk hi
        obtain ⟨c, hc, hcx⟩ := ih k hk hk' j hj
        have hgk := (hrow g hg k hk').2
        rw [hki] at hgk
        refine ⟨nth 0 g.2 c, (hrow g hg c hc).1, fun x hx => ?_⟩
        rw [(hrow g hg c hc).2 x hx, hcx x hx, hgk _ (checkBitPerm_spec (hperm j hj) hx).1]
  · unfold checkInverseRow at h7
    have h8 := allZip_spec ([], []) 0 h7 i hi
    rw [Bool.and_eq_true, Nat.blt_eq] at h8
    rw [pAtB_blocks h8.1] at h8
    exact ⟨_, h8.1, fun x hx => Nat.beq_eq.mp (allRange_iff.mp h8.2 x hx)⟩

/-- The action of the `i`-th permutation of the list. -/
noncomputable def bitAct (t : ℕ) (perms : List (List ℕ × List ℕ)) (i α : ℕ) : ℕ :=
  actBits t (pAt perms i) α

/-- Pointwise composition of permutations induces composition of their bit actions. -/
theorem bitAct_comp_of_pointwise {t i j k : ℕ} {perms : List (List ℕ × List ℕ)}
    (hi : checkBitPerm t (pAt perms i) (qAt perms i) = true)
    (hj : checkBitPerm t (pAt perms j) (qAt perms j) = true)
    (hk : checkBitPerm t (pAt perms k) (qAt perms k) = true)
    (h : ∀ x < t, nth 0 (pAt perms i) x =
      nth 0 (pAt perms j) (nth 0 (pAt perms k) x)) (α : ℕ) :
    bitAct t perms i α = bitAct t perms j (bitAct t perms k α) := by
  refine Nat.eq_of_testBit_eq fun y => ?_
  rw [bitAct, bitAct, bitAct, testBit_actBits hi, testBit_actBits hj, testBit_actBits hk]
  by_cases hy : y < t
  · obtain ⟨_, hjlt, _, hjinv⟩ := checkBitPerm_spec hj hy
    obtain ⟨_, hklt, _, hkinv⟩ := checkBitPerm_spec hk hjlt
    obtain ⟨_, _, hiinv, _⟩ := checkBitPerm_spec hi hklt
    rw [h _ hklt, hkinv, hjinv] at hiinv
    rw [hiinv, decide_eq_true hjlt, Bool.true_and]
  · rw [decide_eq_false hy, Bool.false_and, Bool.false_and]

theorem isActGroup_of_check {t : ℕ} {perms : List (List ℕ × List ℕ)} {gens : List (ℕ × List ℕ)}
    {inv : List ℕ} (h : checkBitGroup t perms gens inv = true) :
    IsActGroup perms.length (2 ^ t) (bitAct t perms) := by
  obtain ⟨hperm, hpos, hone, hinj, hmul, hinv⟩ := checkBitGroup_spec h
  refine ⟨hpos, fun i hi α _ => actBits_lt (hperm i hi) α, fun α hα => ?_, fun i hi j hj => ?_,
    fun i hi => ?_, fun i hi j hj e => hinj i hi j hj fun x hx => ?_⟩
  · refine Nat.eq_of_testBit_eq fun y => ?_
    rw [bitAct, testBit_actBits (hperm 0 hpos)]
    by_cases hy : y < t
    · obtain ⟨_, _, h3, _⟩ := checkBitPerm_spec (hperm 0 hpos) hy
      rw [hone y hy] at h3
      rw [h3, decide_eq_true hy, Bool.true_and]
    · rw [decide_eq_false hy, Bool.false_and, testBit_eq_false_of_lt hα hy]
  · obtain ⟨c, hc, hcx⟩ := hmul i hi j hj
    exact ⟨c, hc, fun α _ => bitAct_comp_of_pointwise (hperm c hc) (hperm i hi) (hperm j hj) hcx α⟩
  · obtain ⟨c, hc, hcx⟩ := hinv i hi
    refine ⟨c, hc, fun α hα => Nat.eq_of_testBit_eq fun y => ?_⟩
    rw [bitAct, bitAct, testBit_actBits (hperm c hc), testBit_actBits (hperm i hi)]
    by_cases hy : y < t
    · obtain ⟨_, c2, _, c4⟩ := checkBitPerm_spec (hperm c hc) hy
      rw [hcx _ c2] at c4
      rw [c4, decide_eq_true hy, decide_eq_true c2, Bool.true_and, Bool.true_and]
    · rw [decide_eq_false hy, Bool.false_and, testBit_eq_false_of_lt hα hy]
  · obtain ⟨i1, _, i3, _⟩ := checkBitPerm_spec (hperm i hi) hx
    obtain ⟨_, _, _, j4⟩ := checkBitPerm_spec (hperm j hj) i1
    have h1 := congrArg (fun β => β.testBit (nth 0 (pAt perms i) x))
      (e (2 ^ x) (Nat.pow_lt_pow_right (by omega) hx))
    simp only [bitAct, testBit_actBits (hperm i hi), testBit_actBits (hperm j hj),
      Nat.testBit_two_pow, i3, decide_eq_true i1, Bool.true_and, decide_true] at h1
    rw [← of_decide_eq_true h1.symm] at j4
    exact j4.symm

/-! ### The images of a number under all permutations at once

For a number `α`, the images `β_g = actBits t p_g α` under all `N` permutations of the list are
computed simultaneously as the rows of a bit matrix, stored in one number `M`: bit `j * (N + 1) + g`
of `M` is bit `j` of `β_g`, and bit `j * (N + 1) + N` is bit `j` of `α`. The matrix is the union of
precomputed columns `col N i perms`, one for each bit `i` of `α` that is set. -/

/-- The loop of `col`: add the bits `p_g[i] * N' + g` for the permutations of the list, where `g`
starts from the given index. -/
noncomputable def colLoop (N' i : ℕ) (perms : List (List ℕ × List ℕ)) : ℕ → ℕ → ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ acc => acc)
    (fun e _ ih g acc => ih (Nat.succ g)
      (Nat.lor acc (Nat.shiftLeft 1 (Nat.add (Nat.mul (nth 0 e.1 i) N') g)))) perms

theorem testBit_colLoop (N' i : ℕ) : ∀ (l : List (List ℕ × List ℕ)) (g acc x : ℕ),
    (colLoop N' i l g acc).testBit x = true ↔
      acc.testBit x = true ∨ ∃ k < l.length, nth 0 (pAt l k) i * N' + (g + k) = x
  | [], g, acc, x => by simp [colLoop]
  | e :: l, g, acc, x => by
    change (colLoop N' i l (g + 1) (acc ||| 1 <<< (nth 0 e.1 i * N' + g))).testBit x = true ↔ _
    rw [testBit_colLoop N' i l, List.length_cons, Nat.exists_lt_succ_left, Nat.testBit_or,
      Bool.or_eq_true, or_assoc, Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_iff]
    refine or_congr Iff.rfl (or_congr Iff.rfl (exists_congr fun k => and_congr Iff.rfl ?_))
    rw [show pAt (e :: l) (k + 1) = pAt l k from rfl, Nat.add_assoc g, Nat.add_comm 1 k]

/-- The matrix of a number with the single bit `i`: the bits `p_g[i] * (N + 1) + g` for all `g`,
and the bit `i * (N + 1) + N`. -/
noncomputable def col (N i : ℕ) (perms : List (List ℕ × List ℕ)) : ℕ :=
  colLoop (Nat.succ N) i perms 0 (Nat.shiftLeft 1 (Nat.add (Nat.mul i (Nat.succ N)) N))

theorem testBit_col (N i : ℕ) (perms : List (List ℕ × List ℕ)) (x : ℕ) :
    (col N i perms).testBit x = true ↔
      i * (N + 1) + N = x ∨ ∃ k < perms.length, nth 0 (pAt perms k) i * (N + 1) + k = x := by
  rw [col, testBit_colLoop]
  change (1 <<< (i * (N + 1) + N)).testBit x = true ∨ _ ↔ _
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_iff]
  simp only [Nat.zero_add]

/-- The columns for the bits `0, …, t - 1`. -/
noncomputable def cols (t N : ℕ) (perms : List (List ℕ × List ℕ)) : List ℕ :=
  (List.range t).map fun i => col N i perms

theorem length_cols (t N : ℕ) (perms : List (List ℕ × List ℕ)) : (cols t N perms).length = t := by
  rw [cols, List.length_map, List.length_range]

theorem nth_cols {t N : ℕ} (perms : List (List ℕ × List ℕ)) {i : ℕ} (hi : i < t) :
    nth 0 (cols t N perms) i = col N i perms := by
  rw [nth_eq_getD, cols, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

/-- The union of the columns `cs[i]` for the bits `i` of `α` that are set, added to `acc`. -/
noncomputable def matLoop (cs : List ℕ) : ℕ → ℕ → ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ acc => acc)
    (fun P _ ih αs acc => Nat.rec (motive := fun _ => ℕ) (ih (Nat.shiftRight αs 1) acc)
      (fun _ _ => ih (Nat.shiftRight αs 1) (Nat.lor acc P)) (Nat.land αs 1)) cs

theorem matLoop_cons (P : ℕ) (cs : List ℕ) (α acc : ℕ) :
    matLoop (P :: cs) α acc = Nat.rec (motive := fun _ => ℕ) (matLoop cs (α >>> 1) acc)
      (fun _ _ => matLoop cs (α >>> 1) (acc ||| P)) (α % 2) := by
  rw [← Nat.and_one_is_mod]
  rfl

theorem testBit_matLoop : ∀ (cs : List ℕ) (α acc x : ℕ),
    (matLoop cs α acc).testBit x = true ↔
      acc.testBit x = true ∨ ∃ i < cs.length, α.testBit i = true ∧ (nth 0 cs i).testBit x = true
  | [], α, acc, x => by simp [matLoop]
  | P :: cs, α, acc, x => by
    have hs : ∀ i, (α >>> 1).testBit i = α.testBit (i + 1) := fun i => by
      rw [Nat.testBit_shiftRight, Nat.add_comm]
    rw [matLoop_cons, List.length_cons, Nat.exists_lt_succ_left, Nat.testBit_zero]
    simp only [nth_cons_zero, nth_cons_succ, ← hs]
    rcases Nat.mod_two_eq_zero_or_one α with h | h <;> rw [h]
    · change (matLoop cs (α >>> 1) acc).testBit x = true ↔ _
      rw [testBit_matLoop cs]
      simp
    · change (matLoop cs (α >>> 1) (acc ||| P)).testBit x = true ↔ _
      rw [testBit_matLoop cs, Nat.testBit_or, Bool.or_eq_true, or_assoc]
      simp

theorem mul_add_inj {n a r a' r' : ℕ} (hr : r < n) (hr' : r' < n) (h : a * n + r = a' * n + r') :
    a = a' ∧ r = r' := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le r) hr
  have h1 : (a * n + r) / n = a := by
    rw [Nat.mul_comm, Nat.mul_add_div hn, Nat.div_eq_of_lt hr, Nat.add_zero]
  have h2 : (a' * n + r') / n = a' := by
    rw [Nat.mul_comm, Nat.mul_add_div hn, Nat.div_eq_of_lt hr', Nat.add_zero]
  have h3 : a = a' := by rw [← h1, h, h2]
  subst h3
  exact ⟨rfl, Nat.add_left_cancel h⟩

/-- The matrix of `α`. -/
noncomputable def imgMat (t : ℕ) (perms : List (List ℕ × List ℕ)) (α : ℕ) : ℕ :=
  matLoop (cols t perms.length perms) α 0

theorem testBit_imgMat (t : ℕ) (perms : List (List ℕ × List ℕ)) (α x : ℕ) :
    (imgMat t perms α).testBit x = true ↔ ∃ i < t, α.testBit i = true ∧
      (i * (perms.length + 1) + perms.length = x ∨
        ∃ k < perms.length, nth 0 (pAt perms k) i * (perms.length + 1) + k = x) := by
  rw [imgMat, testBit_matLoop, length_cols]
  simp only [Nat.zero_testBit, Bool.false_eq_true, false_or]
  refine exists_congr fun i => and_congr_right fun hi => ?_
  rw [nth_cols perms hi, testBit_col]

/-- Row `j` of the matrix, at the column of the `g`-th permutation, is bit `j` of the image of
`α` under this permutation. -/
theorem testBit_imgMat_perm (t : ℕ) (perms : List (List ℕ × List ℕ)) (α j : ℕ) {g : ℕ}
    (hg : g < perms.length) :
    (imgMat t perms α).testBit (j * (perms.length + 1) + g) =
      (actBits t (pAt perms g) α).testBit j := by
  rw [Bool.eq_iff_iff, testBit_imgMat, actBits, testBit_actAux]
  simp only [Nat.zero_testBit, Bool.false_eq_true, false_or]
  refine exists_congr fun i => and_congr_right fun _ =>
    ⟨?_, fun ⟨h1, h2⟩ => ⟨h2, Or.inr ⟨g, hg, by rw [h1]⟩⟩⟩
  rintro ⟨hα, h | ⟨k, hk, h⟩⟩
  · exact absurd (mul_add_inj (Nat.lt_succ_self _) (Nat.lt_succ_of_lt hg) h).2 (Nat.ne_of_gt hg)
  · obtain ⟨h1, h2⟩ := mul_add_inj (Nat.lt_succ_of_lt hk) (Nat.lt_succ_of_lt hg) h
    subst h2
    exact ⟨h1, hα⟩

/-- Row `j` of the matrix, at the last column, is bit `j` of `α`. -/
theorem testBit_imgMat_self (t : ℕ) (perms : List (List ℕ × List ℕ)) (α : ℕ) {j : ℕ} (hj : j < t) :
    (imgMat t perms α).testBit (j * (perms.length + 1) + perms.length) = α.testBit j := by
  rw [Bool.eq_iff_iff, testBit_imgMat]
  refine ⟨?_, fun h => ⟨j, hj, h, Or.inl rfl⟩⟩
  rintro ⟨i, _, hα, h | ⟨k, hk, h⟩⟩
  · rw [(mul_add_inj (Nat.lt_succ_self _) (Nat.lt_succ_self _) h).1] at hα
    exact hα
  · exact absurd (mul_add_inj (Nat.lt_succ_of_lt hk) (Nat.lt_succ_self _) h).2 (Nat.ne_of_lt hk)

/-! ### Comparing a number with all its images, most significant bit first -/

theorem and_two_pow_eq_zero_iff (x n : ℕ) : x &&& 2 ^ n = 0 ↔ x.testBit n = false := by
  constructor
  · intro h
    have h1 := congrArg (fun z => z.testBit n) h
    simpa [Nat.testBit_and, Nat.testBit_two_pow] using h1
  · intro h
    refine Nat.eq_of_testBit_eq fun i => ?_
    rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
    by_cases hi : n = i
    · subst hi
      rw [h, Bool.false_and]
    · rw [decide_eq_false hi, Bool.and_false]

theorem shiftRight_eq_of_testBit {x y j : ℕ} (h : x >>> (j + 1) = y >>> (j + 1))
    (hb : x.testBit j = y.testBit j) : x >>> j = y >>> j := by
  rw [Nat.shiftRight_succ, Nat.shiftRight_succ] at h
  have h1 := congrArg Bool.toNat hb
  rw [Nat.toNat_testBit, Nat.toNat_testBit, ← Nat.shiftRight_eq_div_pow,
    ← Nat.shiftRight_eq_div_pow] at h1
  omega

theorem lt_of_testBit {x y j : ℕ} (h : x >>> (j + 1) = y >>> (j + 1)) (hx : x.testBit j = false)
    (hy : y.testBit j = true) : x < y := by
  rw [Nat.shiftRight_succ, Nat.shiftRight_succ] at h
  have h1 := congrArg Bool.toNat hx
  have h2 := congrArg Bool.toNat hy
  rw [Nat.toNat_testBit, ← Nat.shiftRight_eq_div_pow] at h1 h2
  change _ = 0 at h1
  change _ = 1 at h2
  by_contra hlt
  have h3 : y >>> j ≤ x >>> j := by
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
    exact Nat.div_le_div_right (Nat.not_lt.mp hlt)
  omega

/-- Compare `α` with all its images, from bit `n - 1` downwards, given the matrix `M` of `α`.
`E` is the set of permutations whose image agrees with `α` on the bits from `n` upwards (as a
bit mask); the other permutations have a larger image. The result is the set of permutations
fixing `α`, or `0` if some image is smaller than `α`. Here `N'` is the number of columns of the
matrix and `twoN = 2 ^ (N' - 1)` selects the last column. -/
noncomputable def rowLoop (N' twoN M : ℕ) (n : ℕ) : ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun E => E)
    (fun j ih E =>
      Nat.rec (motive := fun _ => ℕ)
        (ih (Nat.xor E (Nat.land E (Nat.shiftRight M (Nat.mul j N')))))
        (fun _ _ => Bool.rec (motive := fun _ => ℕ) 0 (ih E)
          (Nat.beq (Nat.land E (Nat.shiftRight M (Nat.mul j N'))) E))
        (Nat.land (Nat.shiftRight M (Nat.mul j N')) twoN)) n

theorem rowLoop_zero (N' twoN M E : ℕ) : rowLoop N' twoN M 0 E = E := rfl

theorem rowLoop_succ (N' twoN M j E : ℕ) :
    rowLoop N' twoN M (j + 1) E =
      Nat.rec (motive := fun _ => ℕ)
        (rowLoop N' twoN M j (E ^^^ (E &&& M >>> (j * N'))))
        (fun _ _ => Bool.rec (motive := fun _ => ℕ) 0 (rowLoop N' twoN M j E)
          (Nat.beq (E &&& M >>> (j * N')) E))
        (M >>> (j * N') &&& twoN) := rfl

theorem rowLoop_spec {t N M α : ℕ} {β : ℕ → ℕ}
    (hrow : ∀ j < t, ∀ g < N, (M >>> (j * (N + 1))).testBit g = (β g).testBit j)
    (hself : ∀ j < t, (M >>> (j * (N + 1))).testBit N = α.testBit j) :
    ∀ n ≤ t, ∀ E : ℕ, (∀ g, E.testBit g = true → g < N ∧ β g >>> n = α >>> n) →
      (∀ g < N, E.testBit g = false → α < β g) → rowLoop (N + 1) (2 ^ N) M n E ≠ 0 →
      (∀ g, (rowLoop (N + 1) (2 ^ N) M n E).testBit g = true → g < N ∧ β g = α) ∧
        ∀ g < N, (rowLoop (N + 1) (2 ^ N) M n E).testBit g = false → α < β g
  | 0, _, E, h1, h2, _ => ⟨h1, h2⟩
  | j + 1, hj, E, h1, h2, h0 => by
    rw [rowLoop_succ] at h0 ⊢
    have hj' : j < t := Nat.lt_of_succ_le hj
    rcases Nat.eq_zero_or_pos (M >>> (j * (N + 1)) &&& 2 ^ N) with hz | hz
    · have ha : α.testBit j = false := by
        rw [← hself j hj']
        exact (and_two_pow_eq_zero_iff _ _).mp hz
      rw [hz] at h0 ⊢
      refine rowLoop_spec hrow hself j (Nat.le_of_succ_le hj) _ (fun g hg => ?_) (fun g hg hE => ?_)
        h0
      · rw [Nat.testBit_xor, Nat.testBit_and] at hg
        have hE : E.testBit g = true := by
          cases h : E.testBit g
          · rw [h] at hg
            exact absurd hg (by simp)
          · rfl
        rw [hE] at hg
        obtain ⟨hgN, hs⟩ := h1 g hE
        refine ⟨hgN, shiftRight_eq_of_testBit hs ?_⟩
        rw [← hrow j hj' g hgN, ha]
        cases h : (M >>> (j * (N + 1))).testBit g
        · rfl
        · rw [h] at hg
          exact absurd hg (by simp)
      · rw [Nat.testBit_xor, Nat.testBit_and] at hE
        cases h : E.testBit g
        · exact h2 g hg h
        · rw [h] at hE
          have hb : (β g).testBit j = true := by
            rw [← hrow j hj' g hg]
            cases h' : (M >>> (j * (N + 1))).testBit g
            · rw [h'] at hE
              exact absurd hE (by simp)
            · rfl
          exact lt_of_testBit (h1 g h).2.symm ha hb
    · have ha : α.testBit j = true := by
        rw [← hself j hj']
        cases h : (M >>> (j * (N + 1))).testBit N
        · rw [(and_two_pow_eq_zero_iff _ _).mpr h] at hz
          exact absurd hz (Nat.lt_irrefl 0)
        · rfl
      obtain ⟨k, hk⟩ : ∃ k, M >>> (j * (N + 1)) &&& 2 ^ N = k + 1 :=
        ⟨_, (Nat.succ_pred_eq_of_pos hz).symm⟩
      rw [hk] at h0 ⊢
      change (Bool.rec (motive := fun _ => ℕ) 0 (rowLoop (N + 1) (2 ^ N) M j E)
        (Nat.beq (E &&& M >>> (j * (N + 1))) E)) ≠ 0 at h0
      change (∀ g, (Bool.rec (motive := fun _ => ℕ) 0 (rowLoop (N + 1) (2 ^ N) M j E)
        (Nat.beq (E &&& M >>> (j * (N + 1))) E)).testBit g = true → _) ∧
        ∀ g < N, (Bool.rec (motive := fun _ => ℕ) 0 (rowLoop (N + 1) (2 ^ N) M j E)
          (Nat.beq (E &&& M >>> (j * (N + 1))) E)).testBit g = false → _
      cases hb : Nat.beq (E &&& M >>> (j * (N + 1))) E
      · rw [hb] at h0
        exact absurd rfl h0
      · rw [hb] at h0
        have hsub : E &&& M >>> (j * (N + 1)) = E := Nat.beq_eq.mp hb
        refine rowLoop_spec hrow hself j (Nat.le_of_succ_le hj) E (fun g hg => ?_) h2 h0
        obtain ⟨hgN, hs⟩ := h1 g hg
        refine ⟨hgN, shiftRight_eq_of_testBit hs ?_⟩
        have h3 := congrArg (fun z => z.testBit g) hsub
        simp only [Nat.testBit_and, hg, Bool.true_and] at h3
        rw [← hrow j hj' g hgN, h3, ha]

/-- The number of elements of `E`, with a shortcut for `E = {0}`. -/
noncomputable def stabCount (b E : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (popcount b E) 1 (Nat.beq E 1)

theorem stabCount_eq {b N E : ℕ} (hN : N ≤ 2 ^ b) (hE : ∀ g, E.testBit g = true → g < N) :
    stabCount b E = ((Finset.range N).filter fun g => E.testBit g = true).card := by
  have hlt : E < 2 ^ 2 ^ b := Nat.lt_of_lt_of_le
    (Nat.lt_pow_two_of_testBit E fun i hi => by
      cases h : E.testBit i
      · rfl
      · exact absurd (hE i h) (Nat.not_lt.mpr hi))
    (Nat.pow_le_pow_right (by omega) hN)
  have hpop : popcount b E = ((Finset.range N).filter fun g => E.testBit g = true).card := by
    rw [popcount_eq hlt]
    congr 1
    ext g
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => ⟨hE g h.2, h.2⟩, fun h => ⟨Nat.lt_of_lt_of_le h.1 hN, h.2⟩⟩
  unfold stabCount
  cases h : Nat.beq E 1
  · exact hpop
  · rw [← hpop, Nat.beq_eq.mp h]
    change 1 = popcount b 1
    rw [popcount_eq (Nat.one_lt_two_pow (Nat.ne_of_gt (Nat.two_pow_pos b)))]
    have h1 : ((Finset.range (2 ^ b)).filter fun p => Nat.testBit 1 p = true) = {0} := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton,
        Nat.testBit_one_eq_true_iff_self_eq_zero]
      exact ⟨fun h => h.2, fun h => ⟨by rw [h]; exact Nat.two_pow_pos b, h⟩⟩
    rw [h1, Finset.card_singleton]

/-! ### Certified segments of orbit minima -/

/-- `α` is the minimum of its orbit, and the orbit has `m` elements (by orbit–stabilizer: `m`
times the number of permutations fixing `α` is the order of the group). The images are reduced
modulo `2 ^ t`, which changes nothing for lists `perms` passing `checkBitGroup`. -/
def IsRep (t : ℕ) (perms : List (List ℕ × List ℕ)) (α m : ℕ) : Prop :=
  (∀ e ∈ perms, α ≤ actBits t e.1 α % 2 ^ t) ∧
    m * perms.countP (fun e => decide (actBits t e.1 α % 2 ^ t = α)) = perms.length

/-- The check of one entry `(α, m)` of a segment: no image of `α` is below `α`, and `m` times the
number of permutations fixing `α` is `N`. Here `cs` are the columns of the list of permutations,
`twoN = 2 ^ N`, `full = 2 ^ N - 1` and `N ≤ 2 ^ b`. -/
noncomputable def repCheck (t N b full twoN : ℕ) (cs : List ℕ) (α m : ℕ) : Bool :=
  Nat.beq (Nat.mul m (stabCount b (rowLoop (Nat.succ N) twoN (matLoop cs α 0) t full))) N

theorem repCheck_spec {t : ℕ} {perms : List (List ℕ × List ℕ)} {α m : ℕ} (hα : α < 2 ^ t)
    (h : repCheck t perms.length (Nat.succ (Nat.log2 perms.length))
      (Nat.sub (Nat.pow 2 perms.length) 1) (Nat.pow 2 perms.length)
      (cols t perms.length perms) α m = true) : IsRep t perms α m := by
  rcases Nat.eq_zero_or_pos perms.length with hN | hN
  · rw [List.length_eq_zero_iff.mp hN]
    exact ⟨by simp, by simp⟩
  have hb : perms.length ≤ 2 ^ (perms.length.log2 + 1) := Nat.le_of_lt Nat.lt_log2_self
  have hM : matLoop (cols t perms.length perms) α 0 = imgMat t perms α := rfl
  have hmod : ∀ x j, (x % 2 ^ t).testBit j = (decide (j < t) && x.testBit j) :=
    fun x j => Nat.testBit_mod_two_pow x t j
  have hrow : ∀ j < t, ∀ g < perms.length,
      (imgMat t perms α >>> (j * (perms.length + 1))).testBit g =
        (actBits t (pAt perms g) α % 2 ^ t).testBit j := fun j hj g hg => by
    rw [Nat.testBit_shiftRight, testBit_imgMat_perm t perms α j hg, hmod, decide_eq_true hj,
      Bool.true_and]
  have hself : ∀ j < t,
      (imgMat t perms α >>> (j * (perms.length + 1))).testBit perms.length = α.testBit j :=
    fun j hj => by rw [Nat.testBit_shiftRight, testBit_imgMat_self t perms α hj]
  have hfull : ∀ g, (2 ^ perms.length - 1).testBit g = true →
      g < perms.length ∧ (actBits t (pAt perms g) α % 2 ^ t) >>> t = α >>> t := fun g hg => by
    rw [Nat.testBit_two_pow_sub_one, decide_eq_true_iff] at hg
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hα,
      Nat.div_eq_of_lt (Nat.mod_lt _ (Nat.two_pow_pos t))]
    exact ⟨hg, rfl⟩
  have hfull' : ∀ g < perms.length, (2 ^ perms.length - 1).testBit g = false →
      α < actBits t (pAt perms g) α % 2 ^ t := fun g hg h => by
    rw [Nat.testBit_two_pow_sub_one, decide_eq_true hg] at h
    exact absurd h (by simp)
  rw [repCheck, Nat.beq_eq, hM] at h
  change m * stabCount (perms.length.log2 + 1)
    (rowLoop (perms.length + 1) (2 ^ perms.length) (imgMat t perms α) t (2 ^ perms.length - 1)) =
      perms.length at h
  have hspec := rowLoop_spec hrow hself t (Nat.le_refl t) _ hfull hfull'
  generalize rowLoop (perms.length + 1) (2 ^ perms.length) (imgMat t perms α) t
    (2 ^ perms.length - 1) = R at h hspec
  have hne : R ≠ 0 := by
    intro h0
    rw [h0] at h
    have h1 : stabCount (perms.length.log2 + 1) 0 = 0 := by
      rw [stabCount_eq hb (E := 0) (fun g hg => absurd hg (by simp))]
      simp
    rw [h1, Nat.mul_zero] at h
    exact absurd h (Nat.ne_of_lt hN)
  obtain ⟨hfix, hgt⟩ := hspec hne
  rw [stabCount_eq hb fun g hg => (hfix g hg).1] at h
  refine ⟨fun e he => ?_, ?_⟩
  · obtain ⟨g, hg, rfl⟩ := List.mem_iff_getElem.mp he
    rw [← nth_eq_getElem ([], []) hg]
    cases hE : R.testBit g
    · exact Nat.le_of_lt (hgt g hg hE)
    · exact Nat.le_of_eq (hfix g hE).2.symm
  · have hfil : ((Finset.range perms.length).filter fun g =>
        decide (actBits t (nth ([], []) perms g).1 α % 2 ^ t = α) = true) =
        (Finset.range perms.length).filter fun g => R.testBit g = true := by
      refine Finset.filter_congr fun g hg => ?_
      rw [Finset.mem_range] at hg
      rw [decide_eq_true_iff]
      constructor
      · intro h1
        cases hE : R.testBit g
        · exact absurd h1 (Nat.ne_of_gt (hgt g hg hE))
        · rfl
      · exact fun h1 => (hfix g h1).2
    rw [countP_eq_card_filter_range ([], [])
      (fun e => decide (actBits t e.1 α % 2 ^ t = α)), hfil]
    exact h

/-- Lazy conjunction of three Booleans. (A definition, so that the kernel evaluates loops going
through it iteratively.) -/
noncomputable def and3 (a b c : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false c b) a

theorem and3_eq_true {a b c : Bool} : and3 a b c = true ↔ a = true ∧ b = true ∧ c = true := by
  cases a <;> cases b <;> cases c <;> simp [and3]

/-- The loop over a segment: the entries `(α, m)` have strictly increasing `α` in `[lo, hi)`, and
each passes `repCheck`. -/
noncomputable def segLoop (t N b full twoN hi : ℕ) (cs : List ℕ) (seg : List (ℕ × ℕ)) :
    ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun lo => Nat.ble lo hi)
    (fun e _ ih lo => Prod.rec (motive := fun _ => Bool)
      (fun α m => and3 (Nat.ble lo α) (repCheck t N b full twoN cs α m) (ih (Nat.succ α))) e) seg

theorem segLoop_nil (t N b full twoN hi lo : ℕ) (cs : List ℕ) :
    segLoop t N b full twoN hi cs [] lo = Nat.ble lo hi := rfl

theorem segLoop_cons (t N b full twoN hi lo α m : ℕ) (cs : List ℕ) (seg : List (ℕ × ℕ)) :
    segLoop t N b full twoN hi cs ((α, m) :: seg) lo =
      and3 (Nat.ble lo α) (repCheck t N b full twoN cs α m)
        (segLoop t N b full twoN hi cs seg (Nat.succ α)) := rfl

theorem segLoop_spec {t hi : ℕ} {perms : List (List ℕ × List ℕ)} (hhi : hi ≤ 2 ^ t) :
    ∀ (seg : List (ℕ × ℕ)) (lo : ℕ),
      segLoop t perms.length (Nat.succ (Nat.log2 perms.length))
        (Nat.sub (Nat.pow 2 perms.length) 1) (Nat.pow 2 perms.length) hi
        (cols t perms.length perms) seg lo = true →
      lo ≤ hi ∧ seg.Pairwise (fun a b => a.1 < b.1) ∧
        ∀ e ∈ seg, lo ≤ e.1 ∧ e.1 < hi ∧ IsRep t perms e.1 e.2
  | [], lo, h => ⟨Nat.le_of_ble_eq_true h, List.Pairwise.nil, by simp⟩
  | (α, m) :: seg, lo, h => by
    rw [segLoop_cons, and3_eq_true] at h
    obtain ⟨h1, h2, h3⟩ := h
    obtain ⟨g1, g2, g3⟩ := segLoop_spec hhi seg _ h3
    have hlo : lo ≤ α := Nat.le_of_ble_eq_true h1
    have hrep : IsRep t perms α m := repCheck_spec (Nat.lt_of_lt_of_le g1 hhi) h2
    refine ⟨Nat.le_trans hlo (Nat.le_of_succ_le g1),
      List.pairwise_cons.mpr ⟨fun e he => (g3 e he).1, g2⟩, fun e he => ?_⟩
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨hlo, g1, hrep⟩
    · exact ⟨Nat.le_trans hlo (Nat.le_of_succ_le (g3 e he).1), (g3 e he).2⟩

/-- Check an orbit segment using its precomputed group-action columns. -/
noncomputable def checkSegUsingColumns (t size lo hi : ℕ) (columns : List ℕ)
    (segment : List (ℕ × ℕ)) : Bool :=
  and3 (Nat.ble hi (Nat.pow 2 t)) (Nat.ble lo hi)
    (segLoop t size (Nat.succ (Nat.log2 size))
      (Nat.sub (Nat.pow 2 size) 1) (Nat.pow 2 size) hi columns segment lo)

/-- Segment check. `seg` lists pairs `(α, m)`. Checks: `lo ≤ hi ≤ 2 ^ t`; the `α`'s are strictly
increasing and lie in `[lo, hi)`; each `α` is the minimum of its orbit (`α ≤ actBits t p α` for
every `(p, q)` in `perms`); and `m` times the number of permutations in `perms` fixing `α` is
`perms.length` (so that `m` is the size of the orbit).

The images of `α` under all permutations are compared with `α` simultaneously, bit by bit, on a
bit matrix (see `imgMat` and `rowLoop`), so that the cost per entry is `O(t)` operations on
numbers with `t * (perms.length + 1)` bits. -/
noncomputable def checkSeg (t : ℕ) (perms : List (List ℕ × List ℕ)) (lo hi : ℕ)
    (seg : List (ℕ × ℕ)) : Bool :=
  checkSegUsingColumns t perms.length lo hi (cols t perms.length perms) seg

/-- A certified part of an orbit sum: there is a list of orbit minima in `[lo, hi)`, with their
orbit sizes, with total orbit size `M` and weighted sum `W`. -/
def OrbitSeg (t : ℕ) (perms : List (List ℕ × List ℕ)) (F : ℕ → ℕ) (lo hi M W : ℕ) : Prop :=
  lo ≤ hi ∧ hi ≤ 2 ^ t ∧ ∃ seg : List (ℕ × ℕ), seg.Pairwise (fun a b => a.1 < b.1) ∧
    (∀ e ∈ seg, lo ≤ e.1 ∧ e.1 < hi ∧ IsRep t perms e.1 e.2) ∧
    (seg.map Prod.snd).sum = M ∧ (seg.map fun e => e.2 * F e.1).sum = W

theorem OrbitSeg.of_check {t : ℕ} {perms : List (List ℕ × List ℕ)} {F : ℕ → ℕ} {lo hi : ℕ}
    {seg : List (ℕ × ℕ)} {M W : ℕ} (h : checkSeg t perms lo hi seg = true)
    (hM : (seg.map Prod.snd).sum = M) (hW : (seg.map fun e => e.2 * F e.1).sum = W) :
    OrbitSeg t perms F lo hi M W := by
  rw [checkSeg, checkSegUsingColumns, and3_eq_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hhi : hi ≤ 2 ^ t := Nat.le_of_ble_eq_true h1
  obtain ⟨_, g2, g3⟩ := segLoop_spec hhi seg lo h3
  exact ⟨Nat.le_of_ble_eq_true h2, hhi, seg, g2, g3, hM, hW⟩

theorem OrbitSeg.append {t : ℕ} {perms : List (List ℕ × List ℕ)} {F : ℕ → ℕ}
    {lo mid hi M₁ W₁ M₂ W₂ : ℕ} (h₁ : OrbitSeg t perms F lo mid M₁ W₁)
    (h₂ : OrbitSeg t perms F mid hi M₂ W₂) : OrbitSeg t perms F lo hi (M₁ + M₂) (W₁ + W₂) := by
  obtain ⟨a1, _, seg₁, p1, r1, m1, w1⟩ := h₁
  obtain ⟨a2, b2, seg₂, p2, r2, m2, w2⟩ := h₂
  refine ⟨Nat.le_trans a1 a2, b2, seg₁ ++ seg₂, ?_, fun e he => ?_, ?_, ?_⟩
  · exact List.pairwise_append.mpr ⟨p1, p2, fun a ha b hb =>
      Nat.lt_of_lt_of_le (r1 a ha).2.1 (r2 b hb).1⟩
  · rcases List.mem_append.mp he with he | he
    · exact ⟨(r1 e he).1, Nat.lt_of_lt_of_le (r1 e he).2.1 a2, (r1 e he).2.2⟩
    · exact ⟨Nat.le_trans a1 (r2 e he).1, (r2 e he).2⟩
  · rw [List.map_append, List.sum_append, m1, m2]
  · rw [List.map_append, List.sum_append, w1, w2]

/-- **Sum over orbit representatives.** If `F` is invariant under the group and the certified
orbits of minima in `[0, 2 ^ t)` have total size `2 ^ t`, then the sum of `F` over `[0, 2 ^ t)`
is the weighted sum over the minima. -/
theorem OrbitSeg.sum_eq {t : ℕ} {perms : List (List ℕ × List ℕ)} {gens : List (ℕ × List ℕ)}
    {inv : List ℕ} {F : ℕ → ℕ} {W : ℕ} (hgrp : checkBitGroup t perms gens inv = true)
    (hF : ∀ e ∈ perms, ∀ α < 2 ^ t, F (actBits t e.1 α) = F α)
    (h : OrbitSeg t perms F 0 (2 ^ t) (2 ^ t) W) :
    ∑ α ∈ Finset.range (2 ^ t), F α = W := by
  obtain ⟨_, _, seg, hp, hall, hM, hW⟩ := h
  have hG := isActGroup_of_check hgrp
  have hperm := (checkBitGroup_spec hgrp).1
  have hmod : ∀ i < perms.length, ∀ α,
      actBits t (nth ([], []) perms i).1 α % 2 ^ t = bitAct t perms i α :=
    fun i hi α => Nat.mod_eq_of_lt (actBits_lt (hperm i hi) α)
  rw [← hW]
  refine hG.sum_eq (fun i hi α hα => hF _ (nth_mem _ hi) α hα) hp (fun e he => ?_) hM
  obtain ⟨_, hlt, hmin, hcnt⟩ := hall e he
  have hst : actStab perms.length (bitAct t perms) e.1 = (Finset.range perms.length).filter
      fun i => decide (actBits t (nth ([], []) perms i).1 e.1 % 2 ^ t = e.1) = true := by
    refine Finset.filter_congr fun i hi => ?_
    rw [decide_eq_true_iff, hmod i (Finset.mem_range.mp hi)]
  refine ⟨hlt, fun i hi => ?_, ?_⟩
  · rw [← hmod i hi]
    exact hmin _ (nth_mem _ hi)
  · rw [hst, ← countP_eq_card_filter_range ([], [])
      (fun e' => decide (actBits t e'.1 e.1 % 2 ^ t = e.1))]
    exact hcnt

end RACert
