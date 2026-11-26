/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.GapExtremal.Completion
public import LeanPool.SplitCliqueGap.GapExtremal.Global
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto

/-!
# The bridge `gap ≥ F - I` (ledger §8–§9, L9.1)

A split graph `hostGraph N` has core `V` (a clique) and hosts `H` (independent), host `h` seeing
its palette
`N h`. Let `B` be a graph on the core. Under `HostHyp` (palettes independent in `B`; every non-`B`
pair
`{x, y}` assigned to a host `φ x y` whose palette contains it; assignments with a fixed endpoint
injective):

* `gain_le` (integer side): every clique partition has gain `≤ I + 2 |J|` if all core packings have
  residual value `≤ I`;
* `cpStar_le_of_source` (fractional side): a fractional residual packing of value `Fv` gives
  `cp* ≤ E2 - (Fv + 2 |J|)`;
* `gap_ge`: hence `gap ≥ Fv - I`.

Pairs are encoded as two-element `Finset`s.
-/

@[expose] public section

namespace GapExtremal

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (B : SimpleGraph V) [DecidableRel B.Adj]
variable {H : Type*} [Fintype H] [DecidableEq H]

/-! ### Pairs -/

/-- `B`-adjacent two-element subsets of `S`. -/
def adjPairs (S : Finset V) : Finset (Finset V) :=
  (S.powersetCard 2).filter fun p => ∃ x ∈ p, ∃ y ∈ p, B.Adj x y

/-- Non-adjacent two-element subsets of `S` (the marked pairs `J` inside `S`). -/
def jPairs (S : Finset V) : Finset (Finset V) :=
  (S.powersetCard 2).filter fun p => ¬ ∃ x ∈ p, ∃ y ∈ p, B.Adj x y

omit [DecidableEq V] [Fintype V] in
theorem card_adj_add_j (S : Finset V) :
    (adjPairs B S).card + (jPairs B S).card = S.card.choose 2 := by
  unfold adjPairs jPairs
  rw [Finset.card_filter_add_card_filter_not, Finset.card_powersetCard]

theorem e_eq_card_adjPairs (S : Finset V) : e B S = (adjPairs B S).card := by
  unfold e adjPairs
  refine Finset.card_bij (fun s _ => s.toFinset) ?_ ?_ ?_
  · intro s hs
    induction s using Sym2.ind with
    | h u v =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hs
      simp only [Sym2.toFinset_mk_eq, Finset.mem_filter, Finset.mem_powersetCard]
      refine ⟨⟨?_, Finset.card_pair hs.1.ne⟩, u, by simp, v, by simp, hs.1⟩
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      exacts [hs.2.1, hs.2.2]
  · intro s hs t _ hst
    induction s using Sym2.ind with
    | h a b =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hs
      have hab := hs.1
      have ha : a ∈ t.toFinset := hst ▸ (by simp)
      have hb : b ∈ t.toFinset := hst ▸ (by simp)
      rw [Sym2.mem_toFinset] at ha hb
      exact ((Sym2.mem_and_mem_iff hab.ne).mp ⟨ha, hb⟩).symm
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_powersetCard] at hp
    obtain ⟨⟨hpS, h2⟩, x, hx, y, hy, hxy⟩ := hp
    refine ⟨s(x, y), ?_, ?_⟩
    · rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      exact ⟨hxy, hpS hx, hpS hy⟩
    · simp only [Sym2.toFinset_mk_eq]
      exact Finset.eq_of_subset_of_card_le (fun z hz => by
        simp only [mem_insert, mem_singleton] at hz
        rcases hz with rfl | rfl <;> assumption) (by rw [h2, card_pair hxy.ne])

theorem w_add_two_j (S : Finset V) :
    w B S + 2 * (jPairs B S).card = ((S.card.choose 2 : ℕ) : ℤ) - 1 := by
  have h1 := card_adj_add_j B S
  have h2 := e_eq_card_adjPairs B S
  unfold w
  rw [h2]
  have : ((S.card.choose 2 : ℕ) : ℤ) = (adjPairs B S).card + (jPairs B S).card := by
    rw [← h1]; push_cast; ring
  rw [this]; ring

theorem jPairs_eq_filter (S : Finset V) : jPairs B S = (jPairs B univ).filter (· ⊆ S) := by
  ext p
  simp only [jPairs, Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
  tauto

/-! ### The split graph with hosts -/

variable (N : H → Finset V)

/-- The split graph: core `V` (clique), hosts `H` (independent), host `h` adjacent to `N h`. -/
def hostGraph : SimpleGraph (V ⊕ H) where
  Adj a b :=
    match a, b with
    | .inl x, .inl y => x ≠ y
    | .inl x, .inr h => x ∈ N h
    | .inr h, .inl x => x ∈ N h
    | .inr _, .inr _ => False
  symm := ⟨fun a b h => by
    rcases a with x | h <;> rcases b with y | h' <;> simp_all [eq_comm]⟩
  loopless := ⟨fun a h => by rcases a with x | h <;> simp_all⟩

instance : DecidableRel (hostGraph N).Adj := fun a b =>
  match a, b with
  | .inl x, .inl y => inferInstanceAs (Decidable (x ≠ y))
  | .inl x, .inr h => inferInstanceAs (Decidable (x ∈ N h))
  | .inr h, .inl x => inferInstanceAs (Decidable (x ∈ N h))
  | .inr _, .inr _ => inferInstanceAs (Decidable False)

omit [DecidableEq H] [DecidableEq V] [Fintype H] [Fintype V] in
@[simp] theorem hostGraph_inl_inl (x y : V) : (hostGraph N).Adj (.inl x) (.inl y) ↔ x ≠ y := Iff.rfl
omit [DecidableEq H] [DecidableEq V] [Fintype H] [Fintype V] in
@[simp] theorem hostGraph_inl_inr (x : V) (h : H) : (hostGraph N).Adj (.inl x) (.inr h) ↔ x ∈ N h :=
  Iff.rfl
omit [DecidableEq H] [DecidableEq V] [Fintype H] [Fintype V] in
@[simp] theorem hostGraph_inr_inl (x : V) (h : H) : (hostGraph N).Adj (.inr h) (.inl x) ↔ x ∈ N h :=
  Iff.rfl
omit [DecidableEq H] [DecidableEq V] [Fintype H] [Fintype V] in
@[simp] theorem hostGraph_inr_inr (h h' : H) : ¬ (hostGraph N).Adj (.inr h) (.inr h') := id

/-- Hypotheses on palettes and on the assignment `φ` of marked pairs to hosts. -/
structure HostHyp (φ : V → V → H) : Prop where
  indep : ∀ h, ∀ x ∈ N h, ∀ y ∈ N h, ¬ B.Adj x y
  cover : ∀ x y, x ≠ y → ¬ B.Adj x y → x ∈ N (φ x y) ∧ y ∈ N (φ x y)
  symm : ∀ x y, φ x y = φ y x
  inj : ∀ x y y', x ≠ y → ¬ B.Adj x y → x ≠ y' → ¬ B.Adj x y' → φ x y = φ x y' → y = y'

variable {B N}

omit [DecidableEq H] [DecidableEq V] [Fintype H] [Fintype V] in
/-- In a clique of `hostGraph`, at most one host. -/
theorem card_toRight_le {Q : Finset (V ⊕ H)} (hQ : IsClq (hostGraph N) Q) : Q.toRight.card ≤ 1 := by
  rw [Finset.card_le_one]
  intro h hh h' hh'
  by_contra hne
  exact hostGraph_inr_inr N h h' (hQ.2 _ (Finset.mem_toRight.mp hh) _ (Finset.mem_toRight.mp hh')
    (by simpa using hne))

omit [DecidableEq H] in
/-- **Integer side.** -/
theorem cp_ge {φ : V → V → H} (hH : HostHyp B N φ) (I : ℤ)
    (hI : ∀ T : Finset (Finset V), IsPack T → ∑ S ∈ T, w B S ≤ I) :
    (E2 (hostGraph N) : ℤ) - I - 2 * (jPairs B univ).card ≤ (hostGraph N).cliquePartitionNumber :=
      by
  classical
  obtain ⟨P, hP, hcard⟩ := SimpleGraph.exists_isCliquePartition_card_eq (hostGraph N)
  rw [← hcard, card_eq_of_partition _ hP]
  -- pointwise bound on gains
  have hpt : ∀ Q ∈ P, ((Q.card.choose 2 : ℕ) : ℤ) - 1 ≤
      (if Q.toRight = ∅ then w B Q.toLeft else 0) + 2 * (jPairs B Q.toLeft).card := by
    intro Q hQ
    have hsplit := Finset.card_toLeft_add_card_toRight (u := Q)
    have hR := card_toRight_le (hP.isClq hQ)
    split_ifs with hRe
    · rw [hRe, Finset.card_empty, add_zero] at hsplit
      rw [← hsplit, ← w_add_two_j B]
    · obtain ⟨h, hh⟩ : ∃ h, h ∈ Q.toRight := Finset.nonempty_iff_ne_empty.mpr hRe
      have hR1 : Q.toRight.card = 1 := le_antisymm hR (Finset.card_pos.mpr ⟨h, hh⟩)
      have hpal : ∀ x ∈ Q.toLeft, x ∈ N h := fun x hx =>
        (hostGraph_inl_inr N x h).mp ((hP.isClq hQ).2 _ (Finset.mem_toLeft.mp hx) _
          (Finset.mem_toRight.mp hh) (by simp))
      have hadj0 : (adjPairs B Q.toLeft).card = 0 := by
        rw [Finset.card_eq_zero, adjPairs, Finset.filter_eq_empty_iff]
        rintro p hp ⟨x, hx, y, hy, hxy⟩
        have hp' := (Finset.mem_powersetCard.mp hp).1
        exact hH.indep h x (hpal x (hp' hx)) y (hpal y (hp' hy)) hxy
      have hj := card_adj_add_j B Q.toLeft
      rw [hadj0, zero_add] at hj
      rw [hR1] at hsplit
      rw [← hsplit, hj]
      set s := Q.toLeft.card
      have c1 := two_mul_choose_two_int (s + 1)
      have c2 := two_mul_choose_two_int s
      push_cast at c1 ⊢
      nlinarith [sq_nonneg ((s : ℤ) - 1), sq_nonneg ((s : ℤ) - 2)]
  -- core pieces form a packing
  set Pc := P.filter (fun Q => Q.toRight = ∅) with hPc
  have hinjL : Set.InjOn (fun Q : Finset (V ⊕ H) => Q.toLeft) (Pc : Set _) := by
    intro Q hQ Q' hQ' heq
    have h1 := (Finset.mem_filter.mp hQ).2
    have h2 := (Finset.mem_filter.mp hQ').2
    rw [← Finset.toLeft_disjSum_toRight (u := Q), ← Finset.toLeft_disjSum_toRight (u := Q'), h1, h2]
    simp only at heq
    rw [heq]
  -- two pieces sharing two core points coincide
  have hshare : ∀ Q ∈ P, ∀ Q' ∈ P, ∀ a b : V, a ≠ b → a ∈ Q.toLeft → b ∈ Q.toLeft →
      a ∈ Q'.toLeft → b ∈ Q'.toLeft → Q = Q' := by
    intro Q hQ Q' hQ' a b hab ha hb ha' hb'
    obtain ⟨R, -, hR⟩ := hP.existsUnique (.inl a) (.inl b) (by simpa using hab)
    rw [hR Q ⟨hQ, Finset.mem_toLeft.mp ha, Finset.mem_toLeft.mp hb⟩,
      hR Q' ⟨hQ', Finset.mem_toLeft.mp ha', Finset.mem_toLeft.mp hb'⟩]
  have hpack : IsPack (Pc.image fun Q => Q.toLeft) := by
    intro S hS S' hS' hne
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨Q', hQ', rfl⟩ := Finset.mem_image.mp hS'
    rw [Finset.card_le_one]
    intro a ha b hb
    by_contra hab
    have ha' := Finset.mem_inter.mp ha
    have hb' := Finset.mem_inter.mp hb
    exact hne (by rw [hshare Q (Finset.mem_filter.mp hQ).1 Q' (Finset.mem_filter.mp hQ').1 a b hab
      ha'.1 hb'.1 ha'.2 hb'.2])
  have hcore : ∑ Q ∈ P, (if Q.toRight = ∅ then w B Q.toLeft else 0) ≤ I := by
    rw [← Finset.sum_filter, ← hPc, ← Finset.sum_image hinjL]
    exact hI _ hpack
  -- marked pairs are used at most once
  have hJ : ∑ Q ∈ P, ((jPairs B Q.toLeft).card : ℤ) ≤ (jPairs B univ).card := by
    have : ∑ Q ∈ P, (jPairs B Q.toLeft).card ≤ (jPairs B univ).card := by
      rw [← Finset.card_sigma]
      refine Finset.card_le_card_of_injOn (fun x => x.2) ?_ ?_
      · rintro ⟨Q, p⟩ hx
        simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe] at hx
        rw [jPairs_eq_filter B Q.toLeft] at hx
        exact (Finset.mem_filter.mp hx.2).1
      · rintro ⟨Q, p⟩ hx ⟨Q', p'⟩ hx' (heq : p = p')
        subst heq
        simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe] at hx hx'
        have hp := Finset.mem_powersetCard.mp (Finset.mem_filter.mp hx.2).1
        have hp' := Finset.mem_powersetCard.mp (Finset.mem_filter.mp hx'.2).1
        obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hp.2
        have := hshare Q hx.1 Q' hx'.1 a b hab (hp.1 (by simp)) (hp.1 (by simp))
          (hp'.1 (by simp)) (hp'.1 (by simp))
        subst this
        rfl
    exact_mod_cast this
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  linarith

/-! ### Fractional side -/

/-- A fractional residual packing on the core (capacity 1 on every pair). -/
structure ResPack (y : Finset V → ℝ) : Prop where
  nonneg : ∀ S, 0 ≤ y S
  two : ∀ S, y S ≠ 0 → 2 ≤ S.card
  load : ∀ a b, a ≠ b → ∑ S, (if a ∈ S ∧ b ∈ S then y S else 0) ≤ 1

/-- Residual load on a set of core points. -/
noncomputable def resLoad (y : Finset V → ℝ) (p : Finset V) : ℝ := ∑ S, if p ⊆ S then y S else 0

theorem resLoad_pair (y : Finset V → ℝ) (a b : V) :
    resLoad y {a, b} = ∑ S, (if a ∈ S ∧ b ∈ S then y S else 0) := by
  unfold resLoad
  refine Finset.sum_congr rfl fun S _ => if_congr ?_ rfl rfl
  constructor
  · intro h; exact ⟨h (by simp), h (by simp)⟩
  · rintro ⟨ha, hb⟩ x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption

omit [DecidableEq V] in
theorem two_of_mem_jPairs {p : Finset V} (hp : p ∈ jPairs B univ) : p.card = 2 :=
  (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hp).1).2

omit [DecidableEq V] in
theorem nonadj_of_mem_jPairs {p : Finset V} (hp : p ∈ jPairs B univ) :
    ∀ x ∈ p, ∀ y ∈ p, ¬ B.Adj x y := by
  intro x hx y hy h
  exact (Finset.mem_filter.mp hp).2 ⟨x, hx, y, hy, h⟩

variable (B) in
/-- Index type: core pieces of size `≥ 2`, and marked pairs. -/
abbrev KIdx := {S : Finset V // 2 ≤ S.card} ⊕ {p : Finset V // p ∈ jPairs B univ}

variable (B) in
/-- The two endpoints of a marked pair. -/
noncomputable def ends (k : {p : Finset V // p ∈ jPairs B univ}) : V × V :=
  let h := Finset.card_eq_two.mp (two_of_mem_jPairs k.2)
  (h.choose, h.choose_spec.choose)

theorem ends_spec (k : {p : Finset V // p ∈ jPairs B univ}) :
    (ends B k).1 ≠ (ends B k).2 ∧ k.1 = {(ends B k).1, (ends B k).2} :=
  (Finset.card_eq_two.mp (two_of_mem_jPairs k.2)).choose_spec.choose_spec

variable (B) in
/-- The cliques of the fractional packing. -/
noncomputable def cliqueOf (φ : V → V → H) : KIdx B → Finset (V ⊕ H)
  | .inl S => S.1.disjSum ∅
  | .inr k => k.1.disjSum {φ (ends B k).1 (ends B k).2}

variable (B) in
/-- The weights of the fractional packing. -/
noncomputable def weightOf (y : Finset V → ℝ) : KIdx B → ℝ
  | .inl S => y S.1
  | .inr k => 1 - resLoad y k.1

omit [DecidableEq H] [Fintype H] in
theorem host_of_ends {φ : V → V → H} (hH : HostHyp B N φ) (k : {p : Finset V // p ∈ jPairs B univ})
    {a : V} (ha : a ∈ k.1) : ∃ b, a ≠ b ∧ k.1 = {a, b} ∧ φ (ends B k).1 (ends B k).2 = φ a b := by
  obtain ⟨hne, hk⟩ := ends_spec k
  rw [hk] at ha
  simp only [mem_insert, mem_singleton] at ha
  rcases ha with rfl | rfl
  · exact ⟨_, hne, hk, rfl⟩
  · exact ⟨_, hne.symm, by rw [hk, Finset.pair_comm], hH.symm _ _⟩


theorem resLoad_nonneg {y : Finset V → ℝ} (hy : ResPack y) (p : Finset V) : 0 ≤ resLoad y p :=
  Finset.sum_nonneg fun S _ => by split_ifs <;> simp [hy.nonneg S]

omit [Fintype H] in
theorem load_host {φ : V → V → H} (hH : HostHyp B N φ) {y : Finset V → ℝ} (hy : ResPack y)
    (a : V) (h : H) :
    loadQ (weightOf B y) (cliqueOf B φ) {Sum.inl a, Sum.inr h} ≤ 1 := by
  classical
  unfold loadQ
  rw [Fintype.sum_sum_type]
  have h1 : ∑ S : {S : Finset V // 2 ≤ S.card},
      (if ({Sum.inl a, Sum.inr h} : Finset (V ⊕ H)) ⊆ cliqueOf B φ (Sum.inl S)
        then weightOf B y (Sum.inl S) else 0) = 0 := by
    refine Finset.sum_eq_zero fun S _ => ite_eq_right ?_
    intro hsub
    have := hsub (by simp : (Sum.inr h : V ⊕ H) ∈ ({Sum.inl a, Sum.inr h} : Finset (V ⊕ H)))
    simp [cliqueOf] at this
  rw [h1, zero_add]
  set f := fun k : {p : Finset V // p ∈ jPairs B univ} =>
    (if ({Sum.inl a, Sum.inr h} : Finset (V ⊕ H)) ⊆ cliqueOf B φ (Sum.inr k)
      then weightOf B y (Sum.inr k) else 0) with hf
  have hcond : ∀ k, ({Sum.inl a, Sum.inr h} : Finset (V ⊕ H)) ⊆ cliqueOf B φ (Sum.inr k) →
      a ∈ k.1 ∧ h = φ (ends B k).1 (ends B k).2 := by
    intro k hsub
    have ha := hsub (by simp : (Sum.inl a : V ⊕ H) ∈ ({Sum.inl a, Sum.inr h} : Finset (V ⊕ H)))
    have hh := hsub (by simp : (Sum.inr h : V ⊕ H) ∈ ({Sum.inl a, Sum.inr h} : Finset (V ⊕ H)))
    simp only [cliqueOf, Finset.inl_mem_disjSum, Finset.inr_mem_disjSum, Finset.mem_singleton]
      at ha hh
    exact ⟨ha, hh⟩
  by_cases hex : ∃ k0, ({Sum.inl a, Sum.inr h} : Finset (V ⊕ H)) ⊆ cliqueOf B φ (Sum.inr k0)
  · obtain ⟨k0, hk0⟩ := hex
    rw [Finset.sum_eq_single k0]
    · rw [ite_eq_left hk0]
      simp only [weightOf]
      linarith [resLoad_nonneg hy k0.1]
    · intro k _ hne
      refine ite_eq_right fun hsub => hne ?_
      obtain ⟨ha, hh⟩ := hcond k hsub
      obtain ⟨ha0, hh0⟩ := hcond k0 hk0
      obtain ⟨b, hab, hk, hφ⟩ := host_of_ends hH k ha
      obtain ⟨b0, hab0, hk0', hφ0⟩ := host_of_ends hH k0 ha0
      have hn : ¬ B.Adj a b := nonadj_of_mem_jPairs k.2 a (by rw [hk]; simp) b (by rw [hk]; simp)
      have hn0 : ¬ B.Adj a b0 :=
        nonadj_of_mem_jPairs k0.2 a (by rw [hk0']; simp) b0 (by rw [hk0']; simp)
      have hbb : b = b0 := hH.inj a b b0 hab hn hab0 hn0 (by rw [← hφ, ← hφ0, ← hh, ← hh0])
      exact Subtype.ext (by rw [hk, hk0', hbb])
    · simp
  · push Not at hex
    rw [Finset.sum_eq_zero fun k _ => ite_eq_right (hex k)]
    norm_num

omit [Fintype H] in
theorem load_core {φ : V → V → H} {y : Finset V → ℝ} (hy : ResPack y) (a b : V) (hab : a ≠ b) :
    loadQ (weightOf B y) (cliqueOf B φ) {Sum.inl a, Sum.inl b} ≤ 1 := by
  classical
  unfold loadQ
  rw [Fintype.sum_sum_type]
  have hsubS : ∀ S : Finset V, ({Sum.inl a, Sum.inl b} : Finset (V ⊕ H)) ⊆ S.disjSum ∅ ↔
      a ∈ S ∧ b ∈ S := by
    intro S
    constructor
    · intro h
      have ha := h (by simp : (Sum.inl a : V ⊕ H) ∈ ({Sum.inl a, Sum.inl b} : Finset (V ⊕ H)))
      have hb := h (by simp : (Sum.inl b : V ⊕ H) ∈ ({Sum.inl a, Sum.inl b} : Finset (V ⊕ H)))
      rw [Finset.inl_mem_disjSum] at ha hb
      exact ⟨ha, hb⟩
    · rintro ⟨ha, hb⟩ x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl <;> rw [Finset.inl_mem_disjSum] <;> assumption
  have hsubT : ∀ k : {p : Finset V // p ∈ jPairs B univ},
      ({Sum.inl a, Sum.inl b} : Finset (V ⊕ H)) ⊆ cliqueOf B φ (Sum.inr k) ↔ k.1 = {a, b} := by
    intro k
    simp only [cliqueOf]
    constructor
    · intro h
      have ha := h (by simp : (Sum.inl a : V ⊕ H) ∈ ({Sum.inl a, Sum.inl b} : Finset (V ⊕ H)))
      have hb := h (by simp : (Sum.inl b : V ⊕ H) ∈ ({Sum.inl a, Sum.inl b} : Finset (V ⊕ H)))
      rw [Finset.inl_mem_disjSum] at ha hb
      symm
      refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_
      · simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      · rw [two_of_mem_jPairs k.2, card_pair hab]
    · intro hk x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl <;> rw [Finset.inl_mem_disjSum, hk] <;> simp
  -- first part is at most the residual load
  have hp1 : ∑ S : {S : Finset V // 2 ≤ S.card},
      (if ({Sum.inl a, Sum.inl b} : Finset (V ⊕ H)) ⊆ cliqueOf B φ (Sum.inl S)
        then weightOf B y (Sum.inl S) else 0) ≤ resLoad y {a, b} := by
    rw [resLoad_pair]
    calc _ = ∑ S ∈ (univ.filter fun S : Finset V => 2 ≤ S.card),
          (if a ∈ S ∧ b ∈ S then y S else 0) := by
            rw [Finset.sum_subtype (univ.filter fun S : Finset V => 2 ≤ S.card)
              (p := fun S : Finset V => 2 ≤ S.card) (fun S => by simp)
              (fun S => if a ∈ S ∧ b ∈ S then y S else 0)]
            refine Finset.sum_congr rfl fun S _ => ?_
            simp only [cliqueOf, weightOf]
            exact if_congr (hsubS S.1) rfl rfl
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun S _ _ => by split_ifs <;> simp [hy.nonneg S])
  have hp2 : ∑ k : {p : Finset V // p ∈ jPairs B univ},
      (if ({Sum.inl a, Sum.inl b} : Finset (V ⊕ H)) ⊆ cliqueOf B φ (Sum.inr k)
        then weightOf B y (Sum.inr k) else 0) =
      if ({a, b} : Finset V) ∈ jPairs B univ then 1 - resLoad y {a, b} else 0 := by
    rw [← Finset.sum_coe_sort (jPairs B univ) (fun p => if p = {a, b} then 1 - resLoad y p else 0)
      |>.trans (Finset.sum_ite_eq' _ _ _)]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [weightOf]
    exact if_congr (hsubT k) rfl rfl
  rw [hp2]
  have hl := hy.load a b hab
  rw [← resLoad_pair] at hl
  split_ifs <;> linarith

/-- The fractional bridge, retaining the completion and its piece-size bound. -/
theorem host_fractional_partition {φ : V → V → H} (hH : HostHyp B N φ) {y : Finset V → ℝ}
    (hy : ResPack y) :
    ∃ x, (hostGraph N).IsFracCliquePartition x ∧
      ((∀ S, y S ≠ 0 → S.card ≤ 3) → ∀ Q, x Q ≠ 0 → Q.card ≤ 3) ∧
      ∑ Q ∈ (hostGraph N).cliqueSets, x Q =
        (E2 (hostGraph N) : ℝ) - (∑ S, y S * w B S + 2 * (jPairs B univ).card) := by
  classical
  have hres : ∀ p ∈ jPairs B univ, resLoad y p ≤ 1 := by
    intro p hp
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp (two_of_mem_jPairs hp)
    rw [resLoad_pair]; exact hy.load a b hab
  have hcl : ∀ k, IsClq (hostGraph N) (cliqueOf B φ k) := by
    rintro (⟨S, hS⟩ | k)
    · refine ⟨by simpa [cliqueOf, Finset.card_disjSum] using hS, ?_⟩
      intro u hu v hv huv
      simp only [cliqueOf, Finset.mem_disjSum, Finset.notMem_empty] at hu hv
      rcases u with x | h <;> rcases v with x' | h' <;> simp_all
    · obtain ⟨hne, hk⟩ := ends_spec k
      have h1 : (ends B k).1 ∈ k.1 := by rw [hk]; simp
      have h2 : (ends B k).2 ∈ k.1 := by rw [hk]; simp
      have hnadj := nonadj_of_mem_jPairs k.2 _ h1 _ h2
      have hcov := hH.cover _ _ hne hnadj
      refine ⟨?_, ?_⟩
      · simp [cliqueOf, Finset.card_disjSum, two_of_mem_jPairs k.2]
      · intro u hu v hv huv
        simp only [cliqueOf] at hu hv
        rcases u with x | h <;> rcases v with x' | h'
        · simpa using huv
        · rw [Finset.inl_mem_disjSum, hk] at hu
          rw [Finset.inr_mem_disjSum, Finset.mem_singleton] at hv
          rw [hostGraph_inl_inr, hv]
          simp only [mem_insert, mem_singleton] at hu
          rcases hu with rfl | rfl
          exacts [hcov.1, hcov.2]
        · rw [Finset.inl_mem_disjSum, hk] at hv
          rw [Finset.inr_mem_disjSum, Finset.mem_singleton] at hu
          rw [hostGraph_inr_inl, hu]
          simp only [mem_insert, mem_singleton] at hv
          rcases hv with rfl | rfl
          exacts [hcov.1, hcov.2]
        · rw [Finset.inr_mem_disjSum, Finset.mem_singleton] at hu hv
          exact absurd (by rw [hu, hv]) huv
  have hz : ∀ k, 0 ≤ weightOf B y k := by
    rintro (S | k)
    · exact hy.nonneg _
    · simp only [weightOf]; linarith [hres k.1 k.2]
  -- loads
  have hload : ∀ u v, (hostGraph N).Adj u v → loadQ (weightOf B y) (cliqueOf B φ) {u, v} ≤ 1 := by
    rintro (a | h) (b | h') huv
    · exact load_core hy a b (by simpa using huv)
    · exact load_host hH hy a h'
    · rw [Finset.pair_comm]; exact load_host hH hy b h
    · exact absurd huv (hostGraph_inr_inr N h h')
  have hval : ∑ k, weightOf B y k * ((((cliqueOf B φ k).card.choose 2 : ℕ) : ℝ) - 1) =
      ∑ S, y S * w B S + 2 * (jPairs B univ).card := by
    rw [Fintype.sum_sum_type]
    have hA : ∑ S : {S : Finset V // 2 ≤ S.card}, weightOf B y (Sum.inl S) *
        ((((cliqueOf B φ (Sum.inl S)).card.choose 2 : ℕ) : ℝ) - 1) =
        ∑ S, y S * ((((S.card.choose 2 : ℕ) : ℝ)) - 1) := by
      simp only [weightOf, cliqueOf, Finset.card_disjSum, Finset.card_empty, add_zero]
      rw [← Finset.sum_subtype (univ.filter fun S : Finset V => 2 ≤ S.card)
        (p := fun S : Finset V => 2 ≤ S.card) (fun S => by simp)
        (fun S => y S * ((((S.card.choose 2 : ℕ) : ℝ)) - 1)), Finset.sum_filter]
      refine Finset.sum_congr rfl fun S _ => ?_
      split_ifs with h
      · rfl
      · have : y S = 0 := by
          by_contra h'
          exact h (hy.two S h')
        simp [this]
    have hB : ∑ k : {p : Finset V // p ∈ jPairs B univ}, weightOf B y (Sum.inr k) *
        ((((cliqueOf B φ (Sum.inr k)).card.choose 2 : ℕ) : ℝ) - 1) =
        ∑ p ∈ jPairs B univ, 2 * (1 - resLoad y p) := by
      rw [← Finset.sum_coe_sort (jPairs B univ)]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [weightOf, cliqueOf, Finset.card_disjSum, Finset.card_singleton,
        two_of_mem_jPairs k.2]
      norm_num
      ring
    have hw : ∀ S, y S * ((((S.card.choose 2 : ℕ) : ℝ)) - 1) =
        y S * w B S + 2 * (y S * (jPairs B S).card) := by
      intro S
      have h1 := w_add_two_j B S
      have h' : ((((S.card.choose 2 : ℕ) : ℝ)) - 1) = (w B S : ℝ) + 2 * (jPairs B S).card := by
        exact_mod_cast h1.symm
      rw [h']
      ring
    have hdouble : ∑ S, y S * ((jPairs B S).card : ℝ) = ∑ p ∈ jPairs B univ, resLoad y p := by
      unfold resLoad
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun S _ => ?_
      rw [jPairs_eq_filter B S, Finset.card_filter]
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      split_ifs <;> simp
    rw [hA, hB, Finset.sum_congr rfl fun S _ => hw S, Finset.sum_add_distrib, ← Finset.mul_sum,
      hdouble]
    have h2 : ∑ p ∈ jPairs B univ, 2 * (1 - resLoad y p) =
        2 * (jPairs B univ).card - 2 * ∑ p ∈ jPairs B univ, resLoad y p := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      ring
    rw [h2]
    ring
  refine ⟨_, completion_isFrac hz hcl hload, ?_, ?_⟩
  · intro hsmall
    apply completion_card_le (by decide)
    rintro (S | p) hn
    · simpa [cliqueOf] using hsmall S.1 hn
    · simp [cliqueOf, Finset.card_disjSum, two_of_mem_jPairs p.2]
  · rw [completion_sum hcl, hval]

/-- **Fractional side.** -/
theorem cpStar_le {φ : V → V → H} (hH : HostHyp B N φ) {y : Finset V → ℝ} (hy : ResPack y) :
    (hostGraph N).fracCliquePartitionNumber ≤
      (E2 (hostGraph N) : ℝ) - (∑ S, y S * w B S + 2 * (jPairs B univ).card) := by
  obtain ⟨x,hx,_,hval⟩ := host_fractional_partition hH hy
  rw [← hval]
  exact SimpleGraph.fracCliquePartitionNumber_le_sum_cliqueSets hx

/-- **The bridge.** `gap ≥ Fv - I`. -/
theorem gap_ge {φ : V → V → H} (hH : HostHyp B N φ) (I : ℤ)
    (hI : ∀ T : Finset (Finset V), IsPack T → ∑ S ∈ T, w B S ≤ I)
    {y : Finset V → ℝ} (hy : ResPack y) :
    ∑ S, y S * w B S - I ≤ gap (hostGraph N) := by
  have h1 := cp_ge hH I hI
  have h2 := cpStar_le hH hy
  have h1' : ((E2 (hostGraph N) : ℤ) : ℝ) - I - 2 * (jPairs B univ).card ≤ (hostGraph
    N).cliquePartitionNumber := by
    exact_mod_cast h1
  unfold gap
  push_cast at h1'
  linarith

theorem gapWithFracFour_ge {φ : V → V → H} (hH : HostHyp B N φ) (I : ℤ)
    (hI : ∀ T : Finset (Finset V), IsPack T → ∑ S ∈ T, w B S ≤ I)
    {y : Finset V → ℝ} (hy : ResPack y) (hsmall : ∀ S, y S ≠ 0 → S.card ≤ 3) :
    ∑ S, y S * w B S - I ≤ gapWithFracFour (hostGraph N) := by
  classical
  obtain ⟨x,hx,hcard,hval⟩ := host_fractional_partition hH hy
  have hf := fracPartitionFour_le hx (fun Q hQ => (hcard hsmall Q hQ).trans (by decide : 3 ≤ 4))
  have hs : ∑ Q ∈ (hostGraph N).cliqueSets, x Q = ∑ Q, x Q :=
    sum_subset (subset_univ _) fun Q _ hQ => by
      by_contra hn
      exact hQ (SimpleGraph.mem_cliqueSets.mpr (hx.support Q hn))
  rw [← hs, hval] at hf
  have hi : ((E2 (hostGraph N) : ℤ) : ℝ) - I - 2 * (jPairs B univ).card ≤
      (hostGraph N).cliquePartitionNumber := by exact_mod_cast cp_ge hH I hI
  unfold gapWithFracFour
  push_cast at hi
  linarith

end GapExtremal
