/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import LeanPool.DeciSigma1.Readers.Basic
public import LeanPool.DeciSigma1.Words.Basic
import Mathlib.Order.SuccPred.Nat
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Tactic.Ring.RingNF

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Simple paths in forests and periodic runs

Two finite counting facts used to bound the shortening of periodic factors.

The first bounds the length of a duplicate-free path whose consecutive vertices are comparable
in a forest order: if every chain of path vertices has at most `H` elements, the path has at
most `2^H - 1` vertices (`simplePath_le_pow_local`). In the occurrence form the vertices carry
words and comparability is the prefix order (`simplePath_le_pow_prefix`); this bounds the
height of the occurrences of periodic factors.

The second concerns runs of a finite automaton on a periodic word. The orbit of a self-map of a
finite set `β` is periodic after `|β|` steps, with a period dividing `|β|!`
(`iterate_card_add_factorial`). Hence along a word of period `d`, the states at cuts of at least
`|S| · d` repeat with period `d · |S|!` (`periodic_run_stable`, `runFrom_take_periodic`), so a
block of that length may be deleted from a long periodic factor without changing later states.

## Main declarations

- `simplePath_le_pow_local`, `simplePath_le_pow_prefix`: simple paths in forests.
- `iterate_card_add_factorial`: eventual periodicity of iteration on a finite type.
- `periodic_run_stable`, `runFrom_take_periodic`: periodic runs on periodic words.
-/

@[expose] public section


namespace DeciSigma1.Arithmetic

variable {β : Type*}

/-! ## Propagation along a path -/

/-- A property that is invariant across every step of a path holds on the whole path as soon
as it holds at one vertex. -/
theorem isChain_forall_of_exists {R : β → β → Prop} {Q : β → Prop} :
    ∀ {p : List β}, p.IsChain R → (∀ x ∈ p, ∀ y ∈ p, R x y → (Q x ↔ Q y)) →
      (∃ x ∈ p, Q x) → ∀ x ∈ p, Q x
  | [], _, _, ⟨_, hx, _⟩ => absurd hx List.not_mem_nil
  | [a], _, _, ⟨x, hx, hq⟩ => by
    intro y hy
    rw [List.mem_singleton] at hx hy
    subst hx; subst hy; exact hq
  | a :: b :: l, hc, hR, ⟨x, hx, hq⟩ => by
    rw [List.isChain_cons_cons] at hc
    have hR' : ∀ x ∈ b :: l, ∀ y ∈ b :: l, R x y → (Q x ↔ Q y) :=
      fun x hx y hy => hR x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)
    have hex : ∃ x ∈ b :: l, Q x := by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨b, List.mem_cons_self, (hR x List.mem_cons_self b
          (List.mem_cons_of_mem _ List.mem_cons_self) hc.1).mp hq⟩
      · exact ⟨x, hx, hq⟩
    have ih := isChain_forall_of_exists hc.2 hR' hex
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact (hR y List.mem_cons_self b (List.mem_cons_of_mem _ List.mem_cons_self) hc.1).mpr
        (ih b List.mem_cons_self)
    · exact ih y hy

/-- Conjunction of two path conditions. -/
theorem isChain_and {R R' : β → β → Prop} :
    ∀ {p : List β}, p.IsChain R → p.IsChain R' → p.IsChain (fun x y => R x y ∧ R' x y)
  | [], _, _ => List.IsChain.nil
  | [_], _, _ => List.IsChain.singleton _
  | _ :: _ :: _, h, h' => by
    rw [List.isChain_cons_cons] at h h' ⊢
    exact ⟨⟨h.1, h'.1⟩, isChain_and h.2 h'.2⟩

/-! ## The forest bound, local form -/

/-- A minimal vertex of a nonempty path for a strict order. -/
private theorem exists_minimal_mem (r : β → β → Prop) [IsStrictOrder β r] {p : List β}
    (hne : p ≠ []) : ∃ m ∈ p, ∀ y ∈ p, ¬ r y m := by
  classical
  have hnon : p.toFinset.Nonempty := by
    obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil p hne
    exact ⟨a, List.mem_toFinset.mpr ha⟩
  obtain ⟨m, hm, hmin⟩ := p.toFinset.exists_min_image
    (fun x => (p.toFinset.filter (fun y => r y x)).card) hnon
  refine ⟨m, List.mem_toFinset.mp hm, fun y hy hym => ?_⟩
  have hle := hmin y (List.mem_toFinset.mpr hy)
  have hsub : p.toFinset.filter (fun z => r z y) ⊂ p.toFinset.filter (fun z => r z m) := by
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨y, ?_, ?_⟩
      · simp only [Finset.mem_filter, List.mem_toFinset]; exact ⟨hy, hym⟩
      · simp only [Finset.mem_filter, List.mem_toFinset, not_and]
        exact fun _ => irrefl_of r y
    · intro z
      simp only [Finset.mem_filter, List.mem_toFinset]
      exact fun ⟨hz, hzy⟩ => ⟨hz, trans_of r hzy hym⟩
  exact absurd (Finset.card_lt_card hsub) (not_lt.mpr hle)

/-- A duplicate-free path whose consecutive vertices are comparable for a strict order `r` has
at most `2^H - 1` vertices, provided the vertices of the path below any of its vertices are
pairwise comparable and every chain of path vertices has at most `H` elements. All hypotheses
concern only the vertices of the path. -/
theorem simplePath_le_pow_local (r : β → β → Prop) [IsStrictOrder β r] (H : ℕ) :
    ∀ (p : List β), p.Nodup → p.IsChain (fun x y => r x y ∨ r y x) →
      (∀ x ∈ p, ∀ y ∈ p, ∀ z ∈ p, r y x → r z x → y = z ∨ r y z ∨ r z y) →
      (∀ c : Finset β, (∀ x ∈ c, x ∈ p) → IsChain r (c : Set β) → c.card ≤ H) →
      p.length ≤ 2 ^ H - 1 := by
  classical
  induction H with
  | zero =>
    intro p _ _ _ hH
    cases p with
    | nil => simp
    | cons a l =>
      exfalso
      have := hH {a} (by simp) (by simp)
      simp at this
  | succ H ih =>
    intro p hnd hp hf hH
    rcases eq_or_ne p [] with rfl | hne
    · simp
    obtain ⟨m, hm, hmin⟩ := exists_minimal_mem r hne
    -- every vertex of the path lies above `m`
    have hstep : ∀ x ∈ p, ∀ y ∈ p, (r x y ∨ r y x) → (x = m ∨ r m x) → (y = m ∨ r m y) := by
      intro x hx y hy hxy hQx
      rcases hxy with hxy | hyx
      · right
        rcases hQx with rfl | hmx
        · exact hxy
        · exact trans_of r hmx hxy
      · rcases hQx with rfl | hmx
        · exact absurd hyx (hmin y hy)
        · rcases hf x hx m hm y hy hmx hyx with h | h | h
          · exact Or.inl h.symm
          · exact Or.inr h
          · exact absurd h (hmin y hy)
    have habove : ∀ x ∈ p, x = m ∨ r m x :=
      isChain_forall_of_exists hp
        (fun x hx y hy hxy => ⟨hstep x hx y hy hxy, hstep y hy x hx hxy.symm⟩)
        ⟨m, hm, Or.inl rfl⟩
    -- split the path at `m`
    obtain ⟨s, t, rfl⟩ := List.append_of_mem hm
    have hnd' := List.nodup_middle.mp hnd
    rw [List.nodup_cons, List.mem_append, not_or] at hnd'
    obtain ⟨⟨hms, hmt⟩, hst⟩ := hnd'
    have hs_nd : s.Nodup := (List.nodup_append.mp hst).1
    have ht_nd : t.Nodup := (List.nodup_append.mp hst).2.1
    have hsplit := List.isChain_split.mp hp
    have hs_ch : s.IsChain (fun x y => r x y ∨ r y x) := (List.isChain_append.mp hsplit.1).1
    have ht_ch : t.IsChain (fun x y => r x y ∨ r y x) := hsplit.2.tail
    -- the induction hypothesis applies to each side
    have hside : ∀ q : List β, (∀ x ∈ q, x ∈ s ++ m :: t) → m ∉ q → q.Nodup →
        q.IsChain (fun x y => r x y ∨ r y x) → q.length ≤ 2 ^ H - 1 := by
      intro q hq hmq hqnd hqch
      refine ih q hqnd hqch (fun x hx y hy z hz => hf x (hq x hx) y (hq y hy) z (hq z hz)) ?_
      intro c hc hch
      have hmc : m ∉ c := fun h => hmq (hc m h)
      have hins : IsChain r ((insert m c : Finset β) : Set β) := by
        rw [Finset.coe_insert]
        refine hch.insert fun b hb hne => ?_
        rcases habove b (hq b (hc b hb)) with h | h
        · exact absurd h.symm hne
        · exact Or.inl h
      have := hH (insert m c) (by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hm
        · exact hq x (hc x hx)) hins
      rw [Finset.card_insert_of_notMem hmc] at this
      omega
    have h1 := hside s (fun x hx => List.mem_append_left _ hx) hms hs_nd hs_ch
    have h2 := hside t (fun x hx => List.mem_append_right _ (List.mem_cons_of_mem _ hx)) hmt
      ht_nd ht_ch
    have hpos : 1 ≤ 2 ^ H := Nat.one_le_two_pow
    rw [List.length_append, List.length_cons, Nat.pow_succ]
    omega

/-! ## Paths of prefix-comparable words -/

/-- Vertices carry words `f x`. A duplicate-free path whose consecutive vertices carry
prefix-comparable words, and in which every set of vertices with pairwise prefix-comparable
words has at most `H` elements, has at most `2^H - 1` vertices. Distinct vertices may carry
equal words. -/
theorem simplePath_le_pow_prefix {γ : Type*} (f : β → List γ) (H : ℕ) (p : List β)
    (hnd : p.Nodup) (hp : p.IsChain (fun x y => f x <+: f y ∨ f y <+: f x))
    (hH : ∀ c : Finset β, (∀ x ∈ c, x ∈ p) →
      (∀ x ∈ c, ∀ y ∈ c, f x <+: f y ∨ f y <+: f x) → c.card ≤ H) :
    p.length ≤ 2 ^ H - 1 := by
  classical
  -- strict prefix, ties broken by the position in the path
  let r : β → β → Prop := fun x y =>
    (f x <+: f y ∧ f x ≠ f y) ∨ (f x = f y ∧ p.idxOf x < p.idxOf y)
  have : IsStrictOrder β r :=
    { irrefl := fun a h => by
        rcases h with ⟨_, h⟩ | ⟨_, h⟩
        · exact h rfl
        · exact lt_irrefl _ h
      trans := fun a b c hab hbc => by
        rcases hab with ⟨hab, hne⟩ | ⟨heq, hlt⟩ <;> rcases hbc with ⟨hbc, hne'⟩ | ⟨heq', hlt'⟩
        · refine Or.inl ⟨hab.trans hbc, fun h => hne ?_⟩
          rw [← h] at hbc
          exact hab.eq_of_length (le_antisymm hab.length_le hbc.length_le)
        · exact Or.inl ⟨heq' ▸ hab, heq' ▸ hne⟩
        · exact Or.inl ⟨heq ▸ hbc, heq ▸ hne'⟩
        · exact Or.inr ⟨heq.trans heq', hlt.trans hlt'⟩ }
  have hkey : ∀ x y, r x y → f x <+: f y := by
    intro x y h
    rcases h with ⟨h, _⟩ | ⟨h, _⟩
    · exact h
    · exact h ▸ List.prefix_refl _
  have hcomp : ∀ x ∈ p, ∀ y ∈ p, x ≠ y → (f x <+: f y ∨ f y <+: f x) → r x y ∨ r y x := by
    intro x hx y _ hxy h
    by_cases he : f x = f y
    · have hi : p.idxOf x ≠ p.idxOf y := fun hi => hxy ((List.idxOf_inj hx).mp hi)
      rcases Nat.lt_or_gt_of_ne hi with hi | hi
      · exact Or.inl (Or.inr ⟨he, hi⟩)
      · exact Or.inr (Or.inr ⟨he.symm, hi⟩)
    · rcases h with h | h
      · exact Or.inl (Or.inl ⟨h, he⟩)
      · exact Or.inr (Or.inl ⟨h, Ne.symm he⟩)
  have hne_ch : p.IsChain (fun x y => x ≠ y) := hnd.isChain
  refine simplePath_le_pow_local r H p hnd ?_ ?_ ?_
  · refine (isChain_and hne_ch hp).imp_of_mem_imp ?_
    intro x y hx hy ⟨hxy, h⟩
    exact hcomp x hx y hy hxy h
  · intro x hx y hy z hz hyx hzx
    by_cases hyz : y = z
    · exact Or.inl hyz
    · right
      have h1 := hkey y x hyx
      have h2 := hkey z x hzx
      have hyz' : f y <+: f z ∨ f z <+: f y := by
        rcases le_total (f y).length (f z).length with h | h
        · exact Or.inl (List.prefix_of_prefix_length_le h1 h2 h)
        · exact Or.inr (List.prefix_of_prefix_length_le h2 h1 h)
      exact hcomp y hy z hz hyz hyz'
  · intro c hc hch
    refine hH c hc ?_
    intro x hx y hy
    by_cases hxy : x = y
    · subst hxy; exact Or.inl (List.prefix_refl _)
    · rcases hch hx hy hxy with h | h
      · exact Or.inl (hkey x y h)
      · exact Or.inr (hkey y x h)

/-! ## Periodic runs -/

section Runs

open DeciSigma1.Readers DeciSigma1.Words

variable {α S : Type} {k : ℕ}

/-- After `card β` steps the orbit of a self-map of a finite type repeats with a period that
divides `(card β)!`. -/
theorem iterate_card_add_factorial {β : Type} [Fintype β] (f : β → β) (x : β) (m : ℕ) :
    f^[Fintype.card β + m * (Fintype.card β).factorial] x = f^[Fintype.card β] x := by
  set n := Fintype.card β
  obtain ⟨i, j, hij, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (n + 1) => f^[i] x) (by simp [n])
  -- order the two indices
  obtain ⟨a, c, ha, hc, hcn, hac⟩ : ∃ a c : ℕ, a ≤ n ∧ 0 < c ∧ c ≤ n ∧
      f^[a + c] x = f^[a] x := by
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
    · refine ⟨i, j - i, by omega, by omega, by omega, ?_⟩
      rw [show (i : ℕ) + (j - i) = j by omega]; exact heq.symm
    · refine ⟨j, i - j, by omega, by omega, by omega, ?_⟩
      rw [show (j : ℕ) + (i - j) = i by omega]; exact heq
  have hstep : ∀ t, a ≤ t → f^[t + c] x = f^[t] x := by
    intro t ht
    have := congrArg (f^[t - a]) hac
    rwa [← Function.iterate_add_apply, ← Function.iterate_add_apply,
      show t - a + (a + c) = t + c by omega, show t - a + a = t by omega] at this
  have hrep : ∀ q t, a ≤ t → f^[t + q * c] x = f^[t] x := by
    intro q
    induction q with
    | zero => intro t _; simp
    | succ q ih =>
      intro t ht
      rw [show t + (q + 1) * c = (t + q * c) + c by ring, hstep _ (by omega), ih t ht]
  obtain ⟨q, hq⟩ := Nat.dvd_factorial hc hcn
  rw [hq, show m * (c * q) = (m * q) * c by ring]
  exact hrep _ _ ha

theorem streamPeriod_mul {ξ : ℕ → α} {d : ℕ} (h : StreamPeriod ξ d) (a j : ℕ) :
    ξ (a + j * d) = ξ a := by
  induction j with
  | zero => simp
  | succ j ih => rw [show a + (j + 1) * d = (a + j * d) + d by ring, h, ih]

/-- Along an infinite word of period `d`, the states of a run at cuts of at least `|S| · d`
repeat with period `d · |S|!`. -/
theorem periodic_run_stable [Fintype S] (T : Table α S k) (q : S) (ξ : ℕ → α) {d p : ℕ}
    (hξ : StreamPeriod ξ d) (hp : Fintype.card S * d ≤ p) (m : ℕ) :
    runFrom T.step q (streamPrefix ξ (p + m * (d * (Fintype.card S).factorial))) =
      runFrom T.step q (streamPrefix ξ p) := by
  set N := Fintype.card S
  set r := p - N * d
  let F : S → S := fun s => runFrom T.step s (streamPrefix (fun i => ξ (r + i)) d)
  have hblock : ∀ j, runFrom T.step q (streamPrefix ξ (r + j * d)) =
      F^[j] (runFrom T.step q (streamPrefix ξ r)) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [show r + (j + 1) * d = (r + j * d) + d by ring, streamPrefix_add,
        runFrom_append, ih, Function.iterate_succ_apply']
      congr 2
      funext i
      rw [show r + j * d + i = (r + i) + j * d by ring, streamPeriod_mul hξ]
  have h1 : p = r + N * d := by omega
  have h2 : p + m * (d * N.factorial) = r + (N + m * N.factorial) * d := by rw [h1]; ring
  rw [h2, hblock, h1, hblock]
  exact iterate_card_add_factorial F _ m

/-- Along a finite word of period `d`, the states of a run at cuts of at least `|S| · d` repeat
with period `d · |S|!`, as long as the cuts stay inside the word. -/
theorem runFrom_take_periodic [Fintype S] (T : Table α S k) (q : S) {u : List α} {d o : ℕ}
    (hd : 0 < d) (hper : Words.PeriodicOn u d 0 u.length) (ho : Fintype.card S * d ≤ o) (m : ℕ)
    (hlen : o + m * (d * (Fintype.card S).factorial) ≤ u.length) :
    runFrom T.step q (u.take (o + m * (d * (Fintype.card S).factorial))) =
      runFrom T.step q (u.take o) := by
  have hN : 0 < Fintype.card S := Fintype.card_pos_iff.mpr ⟨q⟩
  have hdu : d ≤ u.length := by
    have : d ≤ Fintype.card S * d := Nat.le_mul_of_pos_left d hN
    omega
  let ξ : ℕ → α := fun i => u[i % d]'(by have := Nat.mod_lt i hd; omega)
  have hξ : StreamPeriod ξ d := by intro i; simp [ξ]
  have htake : ∀ n ≤ u.length, streamPrefix ξ n = u.take n := by
    intro n hn
    apply List.ext_getElem (by simp; omega)
    intro i h1 h2
    simp only [streamPrefix, List.getElem_ofFn, List.getElem_take, ξ]
    have hi : i < u.length := by simp at h1; omega
    have := hper.eq_of_mod (p := i % d) (q := i) (Nat.zero_le _) (Nat.zero_le _)
      (by have := Nat.mod_lt i hd; omega) hi (Nat.mod_mod i d)
    rw [List.getElem?_eq_getElem (by have := Nat.mod_lt i hd; omega),
      List.getElem?_eq_getElem hi] at this
    exact Option.some.inj this
  rw [← htake _ hlen, ← htake _ (by omega)]
  exact periodic_run_stable T q ξ hξ ho m

end Runs

end DeciSigma1.Arithmetic
