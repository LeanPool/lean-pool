/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Int
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Data.Finset.Max
public import Mathlib.Order.SuccPred.Nat
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.Ring.RingNF

/-!
# Path-level reflection identity for ±1 walks (André 1887, algebraic core)

For paths `ω : Fin n → Bool` (each entry: `+1` if `true`, `−1` if `false`),
**reflection after time `τ`** is the path that agrees with `ω` strictly
before time `τ` and *negates* every step from time `τ` onwards.

The algebraic core of André's reflection principle is the position identity

  **For any `τ ≤ k`,**
    `walkPos (reflectAfter τ ω) k = 2 · walkPos ω τ − walkPos ω k`.

Equivalently: the trajectory after time `τ` of the reflected path is the
mirror image of the original trajectory through the horizontal line at
height `walkPos ω τ`.

Combined with a hitting-time argument (the first `τ` with `walkPos ω τ = a`
when `ω` reaches level `a`), this identity yields the bijection between
*paths that touch level `a` and end at `b ≤ a`* and *paths that end at
`2a − b`*. That bijection is the counting backbone of barrier-option
pricing in the binomial tree.

This file formalises **both halves**: the algebraic core (the
path-position identity and involution) *and* the hitting-time bijection
itself (`reflectionPrincipleEquiv`, `reflectionPrincipleEquivBelow`), with
the discrete IVT (`HitsLevel_of_walkPos_endpoint_ge`) discharging the
redundant hitting condition on the reflected side. The counting form is
wired to the corpus as `mf-reflection-principle-counting`.

## Why this is more than algebra

The identity is non-trivial because reflection *changes* the path at every
position from `τ` onwards. The proof requires splitting each path sum into
a prefix (`< τ`) — preserved by reflection — and a suffix (`τ ≤ · < k`) —
negated step-by-step by reflection. The prefix contributes `walkPos ω τ`
to both sides, and the suffix-sign-flip is what produces the
`2 · walkPos ω τ − walkPos ω k` form.

## Main definitions

* `walkStep`, `walkPos`: the step `±1` of a flip and the position of the walk at time `k`, the sum
  of the first `k` steps.
* `reflectAfter`: the path that agrees with `ω` before time `τ` and flips every step from `τ` on.
* `hittingSet`, `HitsLevel`: the times `k ≤ n` at which the walk is at level `a`, and the
  predicate that this set is nonempty.
* `firstHit`: the first hitting time of level `a` on a path that hits it.
* `reflectAtFirstHit`: reflection after the first hitting time of `a`.
* `reflectionPrincipleEquiv`: the bijection between paths that hit `a` and end at `b`, and paths
  that hit `a` and end at `2a − b`, given by `reflectAtFirstHit a`.
* `hitsLevelEquivAbove`: for `0 < a ≤ b`, the paths that hit `a` and end at `b` are in
  bijection with the paths that end at `b`.
* `reflectionPrincipleEquivBelow`: for `0 < a` and `b ≤ a`, the paths that hit `a` and end at
  `b` are in bijection with the paths that end at `2a − b`.

## Main results

* `reflectAfter_involutive`: reflection at fixed `τ` is its own inverse.
* `walkPos_reflectAfter_le`: positions at `k ≤ τ` are unchanged.
* `walkPos_reflectAfter_ge`: positions at `k ≥ τ` reflect through
  `walkPos ω τ`.
* `walkPos_reflectAfter_endpoint`: endpoint statement: if the original
  hits `a` at `τ` and ends at `b`, the reflected ends at `2a − b`.
* `reflectAtFirstHit_involutive`: reflection at the first hit is its own inverse.
* `HitsLevel_of_walkPos_endpoint_ge`: discrete IVT — a walk ending at or
  above a level `a ≥ 0` has hit `a`.

## References

* [André (1887)][Andre1887]

## Tags

reflection principle, André, random walk, first hitting time, barrier option, ballot problem,
MSC 60G50, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

variable {n : ℕ}

/-- Step value: `+1` if `true` (up), `−1` if `false` (down). -/
def walkStep (b : Bool) : ℤ := if b then 1 else -1

/-- **Step-value negation under boolean flip**: `walkStep !b = -walkStep b`. -/
lemma walkStep_not (b : Bool) : walkStep (!b) = -walkStep b := by
  unfold walkStep
  cases b <;> simp

/-- Position of the walk at time `k`: sum of the first `k` steps.

For `k = 0` the sum is empty and the position is `0`. For `k ≥ n` all
steps are included. -/
def walkPos (ω : Fin n → Bool) (k : ℕ) : ℤ :=
  ∑ i ∈ (Finset.univ : Finset (Fin n)).filter (fun (i : Fin n) ↦ i.val < k),
    walkStep (ω i)

@[simp]
lemma walkPos_zero (ω : Fin n → Bool) : walkPos ω 0 = 0 := by
  unfold walkPos
  simp

/-- **Reflection after time `τ`**: flip every step at index `≥ τ`. -/
def reflectAfter (τ : ℕ) (ω : Fin n → Bool) : Fin n → Bool :=
  fun (i : Fin n) ↦ if i.val < τ then ω i else !(ω i)

/-- **Reflection at fixed `τ` is involutive**: applying it twice recovers the
original path. -/
lemma reflectAfter_involutive (τ : ℕ) :
    Function.Involutive (reflectAfter τ : (Fin n → Bool) → Fin n → Bool) := by
  intro ω
  funext i
  unfold reflectAfter
  by_cases h : i.val < τ
  · simp [h]
  · simp [h]

/-- **Positions before `τ` are unchanged**: for `k ≤ τ`, the reflected walk's
position equals the original's. (The flip only takes effect from index `τ`
onwards.) -/
lemma walkPos_reflectAfter_le (τ : ℕ) (ω : Fin n → Bool) {k : ℕ} (hk : k ≤ τ) :
    walkPos (reflectAfter τ ω) k = walkPos ω k := by
  unfold walkPos
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_filter] at hi
  have h_i_lt_τ : i.val < τ := lt_of_lt_of_le hi.2 hk
  unfold reflectAfter
  rw [ite_eq_left h_i_lt_τ]

/-- **Position-reflection identity** (the algebraic core of André's principle).

For any `τ ≤ k`:

  `walkPos (reflectAfter τ ω) k = 2 · walkPos ω τ − walkPos ω k`.

Proof: decompose each path sum into the prefix `{i.val < τ}` (preserved by
reflection, contributing `walkPos ω τ`) and the suffix `{τ ≤ i.val < k}`
(negated step-by-step by reflection). Combining

  `walkPos (reflect) k = (prefix) − (suffix of ω)`
  `walkPos ω k         = (prefix) + (suffix of ω)`
  `walkPos ω τ         = (prefix)`

gives `walkPos (reflect) k = 2·walkPos ω τ − walkPos ω k`. -/
lemma walkPos_reflectAfter_ge (τ : ℕ) (ω : Fin n → Bool) {k : ℕ} (hτk : τ ≤ k) :
    walkPos (reflectAfter τ ω) k = 2 * walkPos ω τ - walkPos ω k := by
  let Pτ : Finset (Fin n) := Finset.univ.filter (fun (i : Fin n) ↦ i.val < τ)
  let Pτk : Finset (Fin n) :=
    Finset.univ.filter (fun (i : Fin n) ↦ τ ≤ i.val ∧ i.val < k)
  let Pk : Finset (Fin n) := Finset.univ.filter (fun (i : Fin n) ↦ i.val < k)
  have h_disj : Disjoint Pτ Pτk := by
    rw [Finset.disjoint_filter]
    intros i _ hi1 hi2
    exact absurd hi1 (not_lt.mpr hi2.1)
  have h_union : Pk = Pτ ∪ Pτk := by
    ext i
    simp only [Pk, Pτ, Pτk, Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨_, h_ik⟩
      by_cases h_iτ : i.val < τ
      · exact Or.inl ⟨Finset.mem_univ _, h_iτ⟩
      · exact Or.inr ⟨Finset.mem_univ _, not_lt.mp h_iτ, h_ik⟩
    · rintro (⟨_, h1⟩ | ⟨_, h2, h3⟩)
      · exact ⟨Finset.mem_univ _, lt_of_lt_of_le h1 hτk⟩
      · exact ⟨Finset.mem_univ _, h3⟩
  have h_split_σ : walkPos (reflectAfter τ ω) k =
      (∑ i ∈ Pτ, walkStep (reflectAfter τ ω i)) +
      (∑ i ∈ Pτk, walkStep (reflectAfter τ ω i)) := by
    unfold walkPos
    change ∑ i ∈ Pk, walkStep (reflectAfter τ ω i) = _
    rw [h_union, Finset.sum_union h_disj]
  have h_split_ω : walkPos ω k =
      (∑ i ∈ Pτ, walkStep (ω i)) + (∑ i ∈ Pτk, walkStep (ω i)) := by
    unfold walkPos
    change ∑ i ∈ Pk, walkStep (ω i) = _
    rw [h_union, Finset.sum_union h_disj]
  have h_τ_eq : walkPos ω τ = ∑ i ∈ Pτ, walkStep (ω i) := rfl
  have h_prefix :
      (∑ i ∈ Pτ, walkStep (reflectAfter τ ω i)) = ∑ i ∈ Pτ, walkStep (ω i) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Pτ, Finset.mem_filter] at hi
    unfold reflectAfter
    rw [ite_eq_left hi.2]
  have h_suffix :
      (∑ i ∈ Pτk, walkStep (reflectAfter τ ω i)) = -∑ i ∈ Pτk, walkStep (ω i) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Pτk, Finset.mem_filter] at hi
    unfold reflectAfter
    rw [ite_eq_right (not_lt.mpr hi.2.1), walkStep_not]
  rw [h_split_σ, h_prefix, h_suffix, h_split_ω, h_τ_eq]
  ring

/-- **Endpoint statement of the reflection identity**: if `ω` hits level `a` at
time `τ` (`walkPos ω τ = a`) and ends at `b` (`walkPos ω n = b`), then the
reflected path ends at `2a − b`.

This statement drives the counting argument in barrier-option pricing: a
path-to-`b`-touching-`a` and a path-to-`(2a−b)` are in bijection via
reflection at the first hitting time of `a`. -/
theorem walkPos_reflectAfter_endpoint (τ : ℕ) (ω : Fin n → Bool) (hτ : τ ≤ n)
    (a b : ℤ) (h_hit : walkPos ω τ = a) (h_end : walkPos ω n = b) :
    walkPos (reflectAfter τ ω) n = 2 * a - b := by
  rw [walkPos_reflectAfter_ge τ ω hτ, h_hit, h_end]

/-! ## Hitting time and the counting bijection

The reflection identity above is the algebraic spine. To turn it into a
counting statement we choose a canonical `τ` — the **first time** the walk
hits a given level `a` — and reflect there. The bijection is then between
paths that hit `a` and end at one level and paths that hit `a` and end at
its mirror image.

The construction:

1. `hittingSet ω a`: the (finite) set of times `k ∈ {0,…,n}` with
   `walkPos ω k = a`.
2. `HitsLevel`: the predicate that `hittingSet` is nonempty.
3. `firstHit ω a h`: the smallest hit time on a hit-path.
4. `reflectAtFirstHit a`: the partial map `ω ↦ reflectAfter (firstHit ω a h) ω`
   (defaulting to identity when `ω` doesn't hit `a`).
5. **Key invariance**: `firstHit (reflectAtFirstHit ω) a = firstHit ω a`,
   because reflection preserves positions on `[0, τ]`, hence both hits at τ
   (and doesn't hit earlier).
6. **Involution**: applying reflection twice at the same `τ` is identity,
   so `reflectAtFirstHit` is an involution on `{ω : HitsLevel ω a}`.
7. **Endpoint flip**: combining with `walkPos_reflectAfter_endpoint`,
   reflection maps `{ω : hits a, ends at b}` to
   `{ω : hits a, ends at 2a − b}` bijectively.
-/

variable {a : ℤ}

/-- The (finite) set of times `k ∈ {0, …, n}` at which the walk hits level `a`. -/
def hittingSet (ω : Fin n → Bool) (a : ℤ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun k ↦ walkPos ω k = a)

/-- A path **hits level `a`** if `hittingSet` is nonempty. -/
abbrev HitsLevel (a : ℤ) (ω : Fin n → Bool) : Prop := (hittingSet ω a).Nonempty

/-- First hitting time of level `a` on a hit-path. -/
noncomputable def firstHit (ω : Fin n → Bool) (a : ℤ) (h : HitsLevel a ω) : ℕ :=
  (hittingSet ω a).min' h

lemma firstHit_mem_hittingSet (ω : Fin n → Bool) (a : ℤ) (h : HitsLevel a ω) :
    firstHit ω a h ∈ hittingSet ω a :=
  (hittingSet ω a).min'_mem h

lemma firstHit_le (ω : Fin n → Bool) (a : ℤ) (h : HitsLevel a ω) :
    firstHit ω a h ≤ n := by
  have h_lt : firstHit ω a h < n + 1 :=
    Finset.mem_range.mp (Finset.mem_filter.mp (firstHit_mem_hittingSet ω a h)).1
  omega

lemma walkPos_firstHit (ω : Fin n → Bool) (a : ℤ) (h : HitsLevel a ω) :
    walkPos ω (firstHit ω a h) = a :=
  (Finset.mem_filter.mp (firstHit_mem_hittingSet ω a h)).2

/-- **Minimality of the first hit**: any `k ≤ n` with `walkPos ω k = a` is at
least `firstHit ω a`. -/
lemma firstHit_le_of_hit (ω : Fin n → Bool) (a : ℤ) (h : HitsLevel a ω)
    {k : ℕ} (hk : k ≤ n) (h_eq : walkPos ω k = a) : firstHit ω a h ≤ k := by
  apply Finset.min'_le
  rw [hittingSet, Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, h_eq⟩

/-- **Reflected path hits level `a`** when the original does. The reflected
hits at the same `firstHit` time (proven separately below). -/
lemma HitsLevel.reflectAfter_firstHit (ω : Fin n → Bool) (a : ℤ) (h : HitsLevel a ω) :
    HitsLevel a (reflectAfter (firstHit ω a h) ω) := by
  refine ⟨firstHit ω a h, ?_⟩
  unfold hittingSet
  rw [Finset.mem_filter, Finset.mem_range]
  refine ⟨by have := firstHit_le ω a h; omega, ?_⟩
  rw [walkPos_reflectAfter_le _ _ (le_refl _)]
  exact walkPos_firstHit ω a h

/-- **First hit is invariant under reflection at the first hit time.** Crucial
for the involution property of `reflectAtFirstHit`.

Proof: both bounds.
* `firstHit σ a ≤ τ` because `σ` hits `a` at `τ` (positions agree up to `τ`).
* `firstHit σ a ≥ τ` because positions on `[0, τ)` agree with `ω`, where `ω`
  doesn't hit `a` (minimality of `τ`). -/
theorem firstHit_reflectAfter_firstHit (ω : Fin n → Bool) (a : ℤ) (h : HitsLevel a ω) :
    firstHit (reflectAfter (firstHit ω a h) ω) a
        (HitsLevel.reflectAfter_firstHit ω a h) = firstHit ω a h := by
  let hσ := HitsLevel.reflectAfter_firstHit ω a h
  apply le_antisymm
  · -- τσ ≤ τ: σ hits a at τ (positions agree up to τ).
    apply firstHit_le_of_hit _ a hσ (firstHit_le ω a h)
    rw [walkPos_reflectAfter_le _ _ (le_refl _)]
    exact walkPos_firstHit ω a h
  · -- τ ≤ τσ: if τσ < τ, positions agree there with ω; ω doesn't hit a before τ.
    by_contra h_ge_not
    have h_lt : firstHit (reflectAfter (firstHit ω a h) ω) a hσ < firstHit ω a h :=
      not_le.mp h_ge_not
    have h_τσ_le_n : firstHit (reflectAfter (firstHit ω a h) ω) a hσ ≤ n :=
      firstHit_le _ _ _
    have h_walkPos_σ :
        walkPos (reflectAfter (firstHit ω a h) ω)
            (firstHit (reflectAfter (firstHit ω a h) ω) a hσ) = a :=
      walkPos_firstHit _ _ _
    have h_walkPos_ω :
        walkPos ω (firstHit (reflectAfter (firstHit ω a h) ω) a hσ) = a := by
      rw [← walkPos_reflectAfter_le (firstHit ω a h) ω (le_of_lt h_lt)]
      exact h_walkPos_σ
    have h_ge : firstHit ω a h ≤ firstHit (reflectAfter (firstHit ω a h) ω) a hσ :=
      firstHit_le_of_hit ω a h h_τσ_le_n h_walkPos_ω
    exact absurd h_ge (not_le.mpr h_lt)

/-- **Reflection at the first hitting time of `a`**: the path-level map that
reflects every step after `firstHit ω a`. Defaulted to identity off the
hit-set. -/
noncomputable def reflectAtFirstHit (a : ℤ) (ω : Fin n → Bool) : Fin n → Bool :=
  if h : HitsLevel a ω then reflectAfter (firstHit ω a h) ω else ω

/-- **Involution**: reflecting twice at the (preserved) first hit recovers
the original path.

Proof: on the hit-set, `firstHit` is invariant under reflection
(`firstHit_reflectAfter_firstHit`), and `reflectAfter τ` is involutive
(`reflectAfter_involutive`). Off the hit-set, the map is identity. -/
theorem reflectAtFirstHit_involutive (a : ℤ) :
    Function.Involutive (reflectAtFirstHit (n := n) a) := by
  intro ω
  by_cases h1 : HitsLevel a ω
  · -- ω hits a.
    have h2 : HitsLevel a (reflectAfter (firstHit ω a h1) ω) :=
      HitsLevel.reflectAfter_firstHit ω a h1
    have h_τ_eq : firstHit (reflectAfter (firstHit ω a h1) ω) a h2 = firstHit ω a h1 :=
      firstHit_reflectAfter_firstHit ω a h1
    change reflectAtFirstHit a (reflectAtFirstHit a ω) = ω
    unfold reflectAtFirstHit
    rw [dite_eq_left h1]
    rw [dite_eq_left h2]
    rw [h_τ_eq]
    exact reflectAfter_involutive (firstHit ω a h1) ω
  · -- ω doesn't hit a; reflectAtFirstHit acts as identity.
    show reflectAtFirstHit a (reflectAtFirstHit a ω) = ω
    unfold reflectAtFirstHit
    rw [dite_eq_right h1, dite_eq_right h1]

/-- **Endpoint flip under reflection at first hit**: if `ω` hits `a` and ends
at `b`, then `reflectAtFirstHit a ω` ends at `2a − b`. -/
theorem walkPos_reflectAtFirstHit_endpoint (ω : Fin n → Bool) (a b : ℤ)
    (h : HitsLevel a ω) (h_end : walkPos ω n = b) :
    walkPos (reflectAtFirstHit a ω) n = 2 * a - b := by
  unfold reflectAtFirstHit
  rw [dite_eq_left h]
  exact walkPos_reflectAfter_endpoint (firstHit ω a h) ω (firstHit_le ω a h)
    a b (walkPos_firstHit ω a h) h_end

/-! ## Discrete intermediate value theorem and the maximal distribution

The reflection principle's *counting* statement, in its cleanest form, drops
the `HitsLevel` hypothesis on one side: any path that *ends* above level `a`
automatically *hits* level `a`. This is the discrete intermediate value
theorem for ±1 walks. Combined with the bijection above, it gives the
classical maximal-distribution counting identity

  `|{ω : HitsLevel a ω}| = 2 · |{ω : a ≤ walkPos ω n}| − |{ω : walkPos ω n = a}|`

for `a ≥ 0`. The bijection above together with the discrete intermediate value
theorem *reduces* this maximal-distribution identity to the endpoint
distribution — the mechanism behind barrier-option pricing. This file delivers
that bijection (`reflectionPrincipleEquiv`) and the IVT direction
(`walkPos_reflectAfter_endpoint`); the `Fintype.card` identity is their
immediate corollary and is not separately stated here.
-/

/-- **Step relation**: the walk's position at time `k + 1` equals the position
at `k` plus the step value at index `k`. -/
lemma walkPos_succ (ω : Fin n → Bool) {k : ℕ} (hk : k < n) :
    walkPos ω (k + 1) = walkPos ω k + walkStep (ω ⟨k, hk⟩) := by
  unfold walkPos
  have h_split :
      (Finset.univ.filter (fun (i : Fin n) ↦ i.val < k + 1)) =
      (Finset.univ.filter (fun (i : Fin n) ↦ i.val < k)) ∪ {⟨k, hk⟩} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_union,
      Finset.mem_singleton, true_and]
    constructor
    · intro h_lt_succ
      by_cases h_eq : i.val = k
      · exact Or.inr (Fin.ext h_eq)
      · exact Or.inl (by omega)
    · rintro (h_lt | h_eq)
      · omega
      · simp [h_eq]
  have h_disj : Disjoint
      (Finset.univ.filter (fun (i : Fin n) ↦ i.val < k))
      ({⟨k, hk⟩} : Finset (Fin n)) := by
    rw [Finset.disjoint_singleton_right, Finset.mem_filter]
    intro h
    exact Nat.lt_irrefl k h.2
  rw [h_split, Finset.sum_union h_disj, Finset.sum_singleton]

/-- **Discrete intermediate value theorem for ±1 walks**: if the walk
ends at or above level `a ≥ 0`, it hits level `a` at some time `k ≤ n`.

Proof: take `τ` = smallest `k ≤ n` with `walkPos ω k ≥ a`. Either `τ = 0`
(so `walkPos ω 0 = 0 ≥ a ≥ 0`, hence `a = 0` and we hit at 0), or `τ > 0`
with `walkPos ω (τ−1) < a` (minimality) and `walkPos ω τ ≥ a`. Since each
step is `±1`, `walkPos τ = walkPos (τ−1) ± 1`; the `-1` case would give
`walkPos τ < a`, contradicting `≥ a`; the `+1` case gives
`walkPos τ = walkPos (τ−1) + 1 ≤ a`, combined with `≥ a` gives `= a`. -/
theorem HitsLevel_of_walkPos_endpoint_ge (ω : Fin n → Bool) (a : ℤ)
    (ha : 0 ≤ a) (h_end : a ≤ walkPos ω n) : HitsLevel a ω := by
  -- Use Finset.min' on the set of k ≤ n with walkPos ω k ≥ a.
  let S : Finset ℕ :=
    (Finset.range (n + 1)).filter (fun k ↦ a ≤ walkPos ω k)
  have h_n_mem : n ∈ S := by
    show n ∈ S
    rw [show S = _ from rfl, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_self n, h_end⟩
  have hS_nonempty : S.Nonempty := ⟨n, h_n_mem⟩
  let τ := S.min' hS_nonempty
  have h_τ_mem_filter :
      τ ∈ (Finset.range (n + 1)).filter (fun k ↦ a ≤ walkPos ω k) :=
    S.min'_mem hS_nonempty
  have h_τ_lt : τ < n + 1 :=
    Finset.mem_range.mp (Finset.mem_filter.mp h_τ_mem_filter).1
  have h_τ_le_n : τ ≤ n := by omega
  have h_τ_ge : a ≤ walkPos ω τ := (Finset.mem_filter.mp h_τ_mem_filter).2
  have h_min : ∀ k < τ, ¬ (a ≤ walkPos ω k) := by
    intro k hk h_ge
    have h_k_in : k ∈ S := by
      show k ∈ S
      rw [show S = _ from rfl, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, h_ge⟩
    have : τ ≤ k := S.min'_le k h_k_in
    omega
  -- Show walkPos ω τ = a.
  have h_eq : walkPos ω τ = a := by
    rcases Nat.eq_zero_or_pos τ with hτ_zero | hτ_pos
    · have h_walkPos_zero : walkPos ω τ = 0 := by rw [hτ_zero]; exact walkPos_zero ω
      rw [h_walkPos_zero] at h_τ_ge
      rw [h_walkPos_zero]
      omega
    · obtain ⟨m, h_eq_m⟩ := Nat.exists_eq_succ_of_ne_zero hτ_pos.ne'
      have h_m_lt_n : m < n := by rw [h_eq_m] at h_τ_le_n; omega
      have h_walkPos_m_lt : walkPos ω m < a := by
        by_contra h_ge
        have h_ge' : a ≤ walkPos ω m := not_lt.mp h_ge
        have h_m_lt_τ : m < τ := by rw [h_eq_m]; omega
        exact h_min m h_m_lt_τ h_ge'
      have h_succ := walkPos_succ ω h_m_lt_n
      have h_walkPos_τ_eq : walkPos ω τ = walkPos ω (m + 1) := by rw [h_eq_m]
      rw [h_walkPos_τ_eq] at h_τ_ge
      rw [h_walkPos_τ_eq]
      have h_step_or : walkStep (ω ⟨m, h_m_lt_n⟩) = 1 ∨
                        walkStep (ω ⟨m, h_m_lt_n⟩) = -1 := by
        unfold walkStep
        by_cases hb : ω ⟨m, h_m_lt_n⟩
        · left; simp [hb]
        · right; simp [hb]
      rcases h_step_or with h_up | h_down
      · rw [h_up] at h_succ; omega
      · rw [h_down] at h_succ; omega
  refine ⟨τ, ?_⟩
  rw [hittingSet, Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, h_eq⟩

/-- **Endpoint-above-barrier ⟹ hits barrier** (alias / corollary).
Same as `HitsLevel_of_walkPos_endpoint_ge`, stated as a one-line use. -/
lemma HitsLevel_of_endpoint_gt {ω : Fin n → Bool} {a : ℤ} (ha : 0 ≤ a)
    (h : a < walkPos ω n) : HitsLevel a ω :=
  HitsLevel_of_walkPos_endpoint_ge ω a ha (le_of_lt h)

/-- **The reflection-principle bijection** (André 1887, counting form).

For any `a, b : ℤ`, the set of paths that hit level `a` and end at `b` is in
bijection with the set of paths that hit level `a` and end at `2a − b`,
via `reflectAtFirstHit a`.

The bijection is an involution (when applied twice, recovers the original
path). -/
noncomputable def reflectionPrincipleEquiv (a b : ℤ) :
    {ω : Fin n → Bool // HitsLevel a ω ∧ walkPos ω n = b} ≃
    {ω : Fin n → Bool // HitsLevel a ω ∧ walkPos ω n = 2 * a - b} where
  toFun ω :=
    ⟨reflectAtFirstHit a ω.val,
     by
       constructor
       · -- Reflected hits a.
         unfold reflectAtFirstHit
         rw [dite_eq_left ω.property.1]
         exact HitsLevel.reflectAfter_firstHit ω.val a ω.property.1
       · exact walkPos_reflectAtFirstHit_endpoint ω.val a b ω.property.1 ω.property.2⟩
  invFun ω :=
    ⟨reflectAtFirstHit a ω.val,
     by
       constructor
       · unfold reflectAtFirstHit
         rw [dite_eq_left ω.property.1]
         exact HitsLevel.reflectAfter_firstHit ω.val a ω.property.1
       · -- Reflected ends at 2a - (2a - b) = b.
         have h := walkPos_reflectAtFirstHit_endpoint ω.val a (2 * a - b)
           ω.property.1 ω.property.2
         linarith⟩
  left_inv ω := Subtype.ext (reflectAtFirstHit_involutive a ω.val)
  right_inv ω := Subtype.ext (reflectAtFirstHit_involutive a ω.val)

/-- **Endpoint-above-`a` implies `HitsLevel`** — packaged as an `Equiv`
between `{ω : hits a, ends at b}` and `{ω : ends at b}` for `b ≥ a > 0`.

By the IVT, `walkPos ω n = b ≥ a > 0` automatically implies `HitsLevel a ω`,
so the `HitsLevel` condition is redundant. -/
noncomputable def hitsLevelEquivAbove (a b : ℤ) (ha : 0 < a) (hb : a ≤ b) :
    {ω : Fin n → Bool // HitsLevel a ω ∧ walkPos ω n = b} ≃
    {ω : Fin n → Bool // walkPos ω n = b} where
  toFun ω := ⟨ω.val, ω.property.2⟩
  invFun ω :=
    ⟨ω.val,
     HitsLevel_of_walkPos_endpoint_ge ω.val a (le_of_lt ha)
       (by rw [ω.property]; exact hb),
     ω.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Reflection bijection (below-the-barrier form)** — clean counting Equiv
between paths-touching-`a`-ending-at-`b` (with `b ≤ a`) and paths-ending-
at-`(2a − b)` (no hitting condition on the right, by IVT, since `2a − b ≥ a`).

This is the form actually used in barrier-option pricing: the LHS is "paths
that touch the barrier and end at `b`," the RHS is the simple endpoint
distribution at `2a − b`. -/
noncomputable def reflectionPrincipleEquivBelow
    (a b : ℤ) (ha : 0 < a) (hb : b ≤ a) :
    {ω : Fin n → Bool // HitsLevel a ω ∧ walkPos ω n = b} ≃
    {ω : Fin n → Bool // walkPos ω n = 2 * a - b} :=
  (reflectionPrincipleEquiv (n := n) a b).trans
    (hitsLevelEquivAbove a (2 * a - b) ha (by linarith))

/-! ## `firstHit?` (Option-returning) for ergonomic downstream use

The `firstHit` function requires a `HitsLevel a ω` proof as input. For
downstream barrier-option code that doesn't have the hit hypothesis upfront
(e.g. computing over all paths and discriminating by hit/no-hit at runtime),
the `Option`-returning variant is cleaner. -/

/-- **First hitting time (Option-returning)**: `some τ` if the path hits
level `a` (with `τ` the first hit time), else `none`. -/
noncomputable def firstHit? (ω : Fin n → Bool) (a : ℤ) : Option ℕ :=
  if h : HitsLevel a ω then some (firstHit ω a h) else none

lemma firstHit?_eq_some_of_hitsLevel (ω : Fin n → Bool) (a : ℤ)
    (h : HitsLevel a ω) : firstHit? ω a = some (firstHit ω a h) := by
  unfold firstHit?; rw [dite_eq_left h]

lemma firstHit?_eq_none_iff_not_hitsLevel (ω : Fin n → Bool) (a : ℤ) :
    firstHit? ω a = none ↔ ¬ HitsLevel a ω := by
  refine ⟨fun h h_hit ↦ ?_, fun h_not_hit ↦ ?_⟩
  · unfold firstHit? at h
    rw [dite_eq_left h_hit] at h
    exact Option.some_ne_none _ h
  · unfold firstHit?; exact dite_eq_right h_not_hit

lemma firstHit?_isSome_iff (ω : Fin n → Bool) (a : ℤ) :
    (firstHit? ω a).isSome ↔ HitsLevel a ω := by
  refine ⟨fun h ↦ ?_, fun h_hit ↦ ?_⟩
  · by_contra h_not_hit
    unfold firstHit? at h
    rw [dite_eq_right h_not_hit] at h
    exact Bool.false_ne_true h
  · unfold firstHit?; rw [dite_eq_left h_hit]; rfl

end MathFin
