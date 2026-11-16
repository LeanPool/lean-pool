/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

import Mathlib.Tactic.Positivity.Basic

public import LeanPool.DeciSigma1.Arithmetic.DifferenceConstraints
public import LeanPool.DeciSigma1.Arithmetic.FinitePaths
public import LeanPool.DeciSigma1.Holes.Periodic.Deletion
import Mathlib.Order.SuccPred.Nat
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.Linarith

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Admissible deletions that leave short pieces

The deletion counts for a period class solve a system of difference constraints (`shiftSystem`).
Pieces joined by a follower edge with nearly equal lengths get equal shifts, and shorter pieces
keep their gaps to longer ones. Each shift has a floor that leaves at least `fixedMargin` letters.
The zero shift solves the system, so there is a least solution above the floors.

Every value in the least solution is reached along a duplicate-free path of tight constraints
from a piece at its floor. An `OccurrenceSplit` partitions the class into heads of comparable
height at most `h` and at most `t` tails. Splitting a path at its tails and applying
`Arithmetic.simplePath_le_pow_prefix` to the head segments bounds its length by
`(t + 1) * 2 ^ h - 1`. Each tight step increases the retained length by less than
`comparisonGap + statePeriodModulus`, giving the cap `pieceLengthBound N |ρ| h t`.

## Main declarations

- `shiftFloor`, `shiftSystem`, `deletionCounts`: the difference system and its deletion counts.
- `simplePath_le_pow_split`: a prefix-comparability path bound with heads and tails.
- `OccurrenceSplit`, `occurrence_path_bound`: the partition and follower-path bound.
- `cap_exists`: an admissible deletion whose retained pieces satisfy the split cap.
-/

@[expose] public section


namespace DeciSigma1.Holes.Periodic

open DeciSigma1.Arithmetic DeciSigma1.Words

section

variable {α : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α} {ρ : List α}

/-- The lower bound on the shift of a piece: minus the number of blocks that can be deleted while
keeping `fixedMargin` letters; `0` for a short piece. -/
def shiftFloor (N : ℕ) (P : Piece W ρ.length) : ℤ :=
  -(((P.len - fixedMargin N ρ.length) / statePeriodModulus N ρ.length : ℕ) : ℤ)

/-- The difference system of the shifts: pieces joined by a follower edge whose lengths differ by
less than `comparisonGap` get equal shifts, and a shorter piece keeps a gap of `comparisonGap`
to a longer one. -/
def shiftSystem (W : Fin k → List α) (ρ : List α) (N : ℕ) :
    DifferenceSystem {P // P ∈ piecesOf W ρ} where
  edgeWeight P Q := if FollowerEdge P.val Q.val then
    if P.val.len < Q.val.len + comparisonGap N ρ.length ∧ Q.val.len < P.val.len +
        comparisonGap N ρ.length then
      some 0
    else if P.val.len + comparisonGap N ρ.length ≤ Q.val.len then
      some (-(((Q.val.len - P.val.len - comparisonGap N ρ.length) / statePeriodModulus N ρ.length :
          ℕ) : ℤ))
    else none
  else none

/-- The zero shift, which deletes nothing, solves the system. -/
theorem shiftSystem_zero (N : ℕ) : (shiftSystem W ρ N).Sat (fun _ => 0) := by
  intro P Q c hc
  change 0 + c ≤ 0
  simp only [zero_add]
  simp only [shiftSystem] at hc
  split_ifs at hc with hg hn hf <;> simp only [Option.some.injEq] at hc
  · subst c; exact le_rfl
  · subst c; exact neg_nonpos.mpr (Int.natCast_nonneg _)

/-- The least solution above the floors: it is nonpositive, and every piece is reached by a
duplicate-free path of tight constraints from a piece at its floor. -/
theorem least_shifts (N : ℕ) :
    ∃ z : {P // P ∈ piecesOf W ρ} → ℤ,
      (shiftSystem W ρ N).Sat z ∧ (∀ P, shiftFloor N P.val ≤ z P) ∧
      (∀ y, (shiftSystem W ρ N).Sat y → (∀ P, shiftFloor N P.val ≤ y P) → z ≤ y) ∧
      (∀ P, z P ≤ 0) ∧
      ∀ P, ∃ p : List {P // P ∈ piecesOf W ρ}, p.Nodup ∧ p.getLast? = some P ∧
        (∃ Q, p.head? = some Q ∧ z Q = shiftFloor N Q.val) ∧
        p.IsChain ((shiftSystem W ρ N).IsTight z) := by
  have hf : (fun P : {P // P ∈ piecesOf W ρ} => shiftFloor N P.val) ≤ (fun _ => 0) := by
    intro P; exact neg_nonpos.mpr (Int.natCast_nonneg _)
  obtain ⟨z, hz, hfloor, hleast, hpath⟩ :=
    (shiftSystem W ρ N).least_above _ _ (shiftSystem_zero N) hf
  exact ⟨z, hz, hfloor, hleast, hleast _ (shiftSystem_zero N) hf, hpath⟩

/-- A nonpositive shift `z` at or above the floor `-((L - F) / M)` deletes at most `L` letters,
nothing from a piece shorter than `F`, and otherwise leaves at least `F` letters. -/
theorem floor_edit {L F M : ℕ} {z : ℤ}
    (hz : -(((L - F) / M : ℕ) : ℤ) ≤ z) (hz0 : z ≤ 0) :
    M * (-z).toNat ≤ L ∧ (L < F → (-z).toNat = 0) ∧
      ((-z).toNat ≠ 0 → F + M * (-z).toNat ≤ L) := by
  have hq : (-z).toNat ≤ (L - F) / M := by omega
  have hmul := Nat.mul_le_mul_left M hq
  have hdiv := Nat.mul_div_le (L - F) M
  rw [Nat.mul_comm M] at hmul
  have hbound : M * (-z).toNat ≤ L - F := by nlinarith
  refine ⟨by omega, ?_, ?_⟩
  · intro hL
    have : L - F = 0 := by omega
    simp only [this, Nat.zero_div] at hq
    omega
  · intro hn
    by_cases hL : L < F
    · have : L - F = 0 := by omega
      simp only [this, Nat.zero_div] at hq
      omega
    · omega

/-- At the floor, fewer than `F + M` letters remain. -/
theorem floor_remainder_lt {L F M : ℕ} (hM : 0 < M) :
    (L : ℤ) + (M : ℤ) * (-(((L - F) / M : ℕ) : ℤ)) < (F : ℤ) + M := by
  have hmod := Nat.mod_lt (L - F) hM
  have hdiv := Nat.mod_add_div (L - F) M
  have hdivZ : (((L - F) % M : ℕ) : ℤ) + (M : ℤ) * ((L - F) / M : ℕ) = (L - F : ℕ) := by
    exact_mod_cast hdiv
  by_cases hLF : F ≤ L
  · have hsub : ((L - F : ℕ) : ℤ) = (L : ℤ) - F := by omega
    rw [hsub] at hdivZ
    have hmodZ : (((L - F) % M : ℕ) : ℤ) < M := by exact_mod_cast hmod
    nlinarith
  · have hzero : L - F = 0 := by omega
    simp only [hzero, Nat.zero_div, Nat.cast_zero, neg_zero, mul_zero, add_zero]
    omega

/-- A constraint between pieces of lengths `L + K ≤ Q` keeps the gap: the edited lengths satisfy
`L + M a + K ≤ Q + M b`. -/
theorem far_weight {L Q K M : ℕ} {a b : ℤ} (hM : 0 < M) (hfar : L + K ≤ Q)
    (h : a - (((Q - L - K) / M : ℕ) : ℤ) ≤ b) :
    (L : ℤ) + M * a + K ≤ (Q : ℤ) + M * b := by
  have hd := Nat.mul_div_le (Q - L - K) M
  have hdZ : (M : ℤ) * ((Q - L - K) / M : ℕ) ≤ (Q - L - K : ℕ) := by
    exact_mod_cast hd
  have he : ((Q - L - K : ℕ) : ℤ) = (Q : ℤ) - L - K := by omega
  rw [he] at hdZ
  have hMZ : (0 : ℤ) < M := by exact_mod_cast hM
  nlinarith

/-- Along a tight constraint between pieces of lengths `L + K ≤ Q`, the edited length increases by
less than `K + M`. -/
theorem far_tight {L Q K M : ℕ} {a b : ℤ} (hM : 0 < M) (hfar : L + K ≤ Q)
    (h : a - (((Q - L - K) / M : ℕ) : ℤ) = b) :
    (Q : ℤ) + M * b < (L : ℤ) + M * a + K + M := by
  have hr := Nat.mod_lt (Q - L - K) hM
  have he := Nat.mod_add_div (Q - L - K) M
  have heZ : (((Q - L - K) % M : ℕ) : ℤ) + (M : ℤ) * ((Q - L - K) / M : ℕ) =
      (Q - L - K : ℕ) := by exact_mod_cast he
  have hsub : ((Q - L - K : ℕ) : ℤ) = (Q : ℤ) - L - K := by omega
  have hrZ : (((Q - L - K) % M : ℕ) : ℤ) < M := by exact_mod_cast hr
  rw [hsub] at heZ
  nlinarith

/-- The deletion counts of a solution: minus the shift, and `0` off the class. -/
def deletionCounts (z : {P // P ∈ piecesOf W ρ} → ℤ) (P : Piece W ρ.length) : ℕ :=
  if h : P ∈ piecesOf W ρ then (-z ⟨P, h⟩).toNat else 0

variable {N : ℕ} {z : {P // P ∈ piecesOf W ρ} → ℤ}

theorem deletionCounts_val (P : {P // P ∈ piecesOf W ρ}) :
    deletionCounts z P.val = (-z P).toNat := by simp [deletionCounts, P.property]

/-- Retained natural lengths agree with the signed length formula. -/
theorem retained_cast (hf : ∀ P, shiftFloor N P.val ≤ z P) (hz0 : ∀ P, z P ≤ 0)
    (P : {P // P ∈ piecesOf W ρ}) :
    ((P.val.len - statePeriodModulus N ρ.length * deletionCounts z P.val : ℕ) : ℤ) =
      (P.val.len : ℤ) + statePeriodModulus N ρ.length * z P := by
  rw [deletionCounts_val]
  have hb := (floor_edit (hf P) (hz0 P)).1
  have hz : ((-z P).toNat : ℤ) = -z P := Int.toNat_of_nonneg (by have := hz0 P; omega)
  rw [Int.natCast_sub hb, Nat.cast_mul, hz]
  ring

/-- Every nonpositive solution above the floors gives an admissible deletion. -/
theorem admissible_deletionCounts (hs : (shiftSystem W ρ N).Sat z)
    (hf : ∀ P, shiftFloor N P.val ≤ z P) (hz0 : ∀ P, z P ≤ 0)
    (hM : 0 < statePeriodModulus N ρ.length) : AdmissibleDeletion W ρ N (deletionCounts z) where
  supp := by
    intro P hp
    by_contra hnot
    simp [deletionCounts, hnot] at hp
  long := by
    intro P hP hmove
    rw [deletionCounts_val (⟨P, hP⟩ : {P // P ∈ piecesOf W ρ})] at hmove ⊢
    exact (floor_edit (hf ⟨P, hP⟩) (hz0 ⟨P, hP⟩)).2.2 hmove
  near := by
    intro P hP Q hQ hg hPQ hQP
    have h1 := hs ⟨P, hP⟩ ⟨Q, hQ⟩ 0 (by simp [shiftSystem, hg, hPQ, hQP])
    have h2 := hs ⟨Q, hQ⟩ ⟨P, hP⟩ 0 (by simp [shiftSystem, hg.symm, hPQ, hQP])
    have he : z ⟨P, hP⟩ = z ⟨Q, hQ⟩ := by omega
    simp only [deletionCounts, dite_eq_left hP, dite_eq_left hQ, he]
  far := by
    intro P hP Q hQ hg hfar
    have hnot : ¬
        (P.len < Q.len + comparisonGap N ρ.length ∧ Q.len < P.len + comparisonGap N
            ρ.length) := by omega
    have he := hs ⟨P, hP⟩ ⟨Q, hQ⟩
      (-(((Q.len - P.len - comparisonGap N ρ.length) / statePeriodModulus N ρ.length : ℕ) : ℤ))
      (by simp [shiftSystem, hg, hnot, hfar])
    have hw := far_weight hM hfar (by simpa only [sub_eq_add_neg] using he)
    have hp := retained_cast hf hz0 ⟨P, hP⟩
    have hq := retained_cast hf hz0 ⟨Q, hQ⟩
    dsimp only at hp hq hw
    omega

/-- Each tight constraint joins two pieces by a follower edge and increases the retained length
by less than `comparisonGap + statePeriodModulus`. -/
theorem tight_step (hM : 0 < statePeriodModulus N ρ.length)
    {P Q : {P // P ∈ piecesOf W ρ}} (ht : (shiftSystem W ρ N).IsTight z P Q) :
    FollowerEdge P.val Q.val ∧
      (Q.val.len : ℤ) + statePeriodModulus N ρ.length * z Q <
        (P.val.len : ℤ) + statePeriodModulus N ρ.length * z P + comparisonGap N ρ.length +
            statePeriodModulus N ρ.length := by
  obtain ⟨c, hc, he⟩ := ht
  simp only [shiftSystem] at hc
  split_ifs at hc with hg hn hfar
  · simp only [Option.some.injEq] at hc
    subst c
    have heq : z P = z Q := by omega
    refine ⟨hg, ?_⟩
    rw [heq]
    have hlen : (Q.val.len : ℤ) < (P.val.len : ℤ) +
        comparisonGap N ρ.length := by exact_mod_cast hn.2
    omega
  · simp only [Option.some.injEq] at hc
    subst c
    exact ⟨hg, far_tight hM hfar (by simpa only [sub_eq_add_neg] using he)⟩

/-- A prefix-comparability path is bounded by its number of tails and the comparable height
of its heads. -/
theorem simplePath_le_pow_split {β γ : Type*} (f : β → List γ) (head : β → Prop)
    [DecidablePred head] (h : ℕ) (p : List β) (hnd : p.Nodup)
    (hp : p.IsChain (fun x y => f x <+: f y ∨ f y <+: f x))
    (hh : ∀ c : Finset β, (∀ x ∈ c, x ∈ p) → (∀ x ∈ c, head x) →
      (∀ x ∈ c, ∀ y ∈ c, f x <+: f y ∨ f y <+: f x) → c.card ≤ h) :
    p.length + 1 ≤ ((p.filter (fun x => decide (¬ head x))).length + 1) * 2 ^ h := by
  classical
  generalize he : p.length = n
  induction n using Nat.strong_induction_on generalizing p with
  | h n ih =>
    by_cases hall : ∀ x ∈ p, head x
    · have hb := simplePath_le_pow_prefix f h p hnd hp
        (fun c hc hcomp => hh c hc (fun x hx => hall x (hc x hx)) hcomp)
      have hempty : p.filter (fun x => decide (¬ head x)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro x hx
        simp [hall x hx]
      rw [hempty]
      simp only [List.length_nil, zero_add, one_mul]
      have : 1 ≤ 2 ^ h := Nat.one_le_two_pow
      omega
    · obtain ⟨m, hm⟩ := not_forall.mp hall
      obtain ⟨hm, hmtail⟩ := not_imp.mp hm
      obtain ⟨s, t, rfl⟩ := List.append_of_mem hm
      have hnd' := List.nodup_middle.mp hnd
      rw [List.nodup_cons] at hnd'
      have hs_nd := (List.nodup_append.mp hnd'.2).1
      have ht_nd := (List.nodup_append.mp hnd'.2).2.1
      have hsplit := List.isChain_split.mp hp
      have hs_ch := (List.isChain_append.mp hsplit.1).1
      have ht_ch := hsplit.2.tail
      have hside : ∀ q : List β, (∀ x ∈ q, x ∈ s ++ m :: t) → q.length < n →
          q.Nodup → q.IsChain (fun x y => f x <+: f y ∨ f y <+: f x) →
          q.length + 1 ≤ ((q.filter (fun x => decide (¬ head x))).length + 1) * 2 ^ h := by
        intro q hq hqn hqnd hqch
        exact ih q.length hqn q hqnd hqch
          (fun c hc => hh c (fun x hx => hq x (hc x hx))) rfl
      have hs := hside s (fun x hx => List.mem_append_left _ hx)
        (by simp only [List.length_append, List.length_cons] at he; omega) hs_nd hs_ch
      have ht := hside t (fun x hx => List.mem_append_right _ (List.mem_cons_of_mem _ hx))
        (by simp only [List.length_append, List.length_cons] at he; omega) ht_nd ht_ch
      simp only [List.length_append, List.length_cons] at he
      simp [List.filter_append, hmtail] at hs ht ⊢
      nlinarith

/-- A partition of a period class into heads of bounded comparable height and a bounded
number of tails. -/
structure OccurrenceSplit (W : Fin k → List α) (ρ : List α) (h t : ℕ) where
  /-- Pieces charged to the bounded initial part of the occurrence split. -/
  head : Piece W ρ.length → Prop
  head_bound : ∀ c : Finset (Piece W ρ.length), c ⊆ piecesOf W ρ →
    (∀ P ∈ c, head P) → (∀ P ∈ c, ∀ Q ∈ c, FollowerEdge P Q) → c.card ≤ h
  tail_bound : ∀ c : Finset (Piece W ρ.length), c ⊆ piecesOf W ρ →
    (∀ P ∈ c, ¬ head P) → c.card ≤ t

/-- A simple follower path with head height `h` and at most `t` tails has at most
`(t + 1) * 2 ^ h - 1` vertices. -/
theorem occurrence_path_bound {h t : ℕ} (split : OccurrenceSplit W ρ h t)
    (p : List {P // P ∈ piecesOf W ρ}) (hnd : p.Nodup)
    (hp : p.IsChain (fun P Q => FollowerEdge P.val Q.val)) :
    p.length ≤ (t + 1) * 2 ^ h - 1 := by
  classical
  let head : {P // P ∈ piecesOf W ρ} → Prop := fun P => split.head P.val
  have hb := simplePath_le_pow_split (fun P : {P // P ∈ piecesOf W ρ} => P.val.follower)
    head h p hnd hp (by
      intro c _ hc hcomp
      let c' := c.image (fun P => P.val)
      have hcard : c'.card = c.card := Finset.card_image_of_injective _ Subtype.val_injective
      rw [← hcard]
      apply split.head_bound c'
      · intro P hP
        obtain ⟨Q, _, rfl⟩ := Finset.mem_image.mp hP
        exact Q.property
      · intro P hP
        obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hP
        exact hc Q hQ
      · intro P hP Q hQ
        obtain ⟨P', hP', rfl⟩ := Finset.mem_image.mp hP
        obtain ⟨Q', hQ', rfl⟩ := Finset.mem_image.mp hQ
        exact hcomp P' hP' Q' hQ')
  let q := p.filter (fun P => decide (¬ head P))
  have hqnd : q.Nodup := hnd.filter _
  have ht : q.length ≤ t := by
    let c := q.toFinset.image (fun P => P.val)
    have hc : c.card = q.length := by
      rw [Finset.card_image_of_injective _ Subtype.val_injective, List.toFinset_card_of_nodup hqnd]
    rw [← hc]
    apply split.tail_bound c
    · intro P hP
      obtain ⟨Q, _, rfl⟩ := Finset.mem_image.mp hP
      exact Q.property
    · intro P hP
      obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hP
      have := List.mem_filter.mp (List.mem_toFinset.mp hQ)
      exact of_decide_eq_true this.2
  have hmul := Nat.mul_le_mul_right (2 ^ h) (Nat.add_le_add_right ht 1)
  change p.length + 1 ≤ (q.length + 1) * 2 ^ h at hb
  omega

/-- If each step of a path increases `v` by at most `B`, the whole path increases `v` by at most
its number of steps times `B`. -/
theorem path_length_bound {ι : Type} (v : ι → ℤ) (B : ℤ) (r : ι → ι → Prop)
    (hstep : ∀ i j, r i j → v j ≤ v i + B) :
    ∀ (i : ι) (p : List ι), (i :: p).IsChain r →
      v ((i :: p).getLast (List.cons_ne_nil _ _)) ≤ v i + p.length * B := by
  intro i p
  induction p generalizing i with
  | nil => simp
  | cons j p ih =>
    intro h
    have hchain := List.isChain_cons_cons.mp h
    have h1 := hstep i j hchain.1
    have h2 := ih j hchain.2
    simp only [List.getLast_cons_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    nlinarith

/-- There is an admissible deletion after which every piece of the class has at most
`pieceLengthBound N |ρ| h t` letters. -/
theorem cap_exists (N : ℕ) {h t : ℕ} (hρ : IsPrimitive ρ)
    (split : OccurrenceSplit W ρ h t) :
    ∃ x, AdmissibleDeletion W ρ N x ∧
      ∀ P ∈ piecesOf W ρ, P.len - statePeriodModulus N ρ.length * x P ≤
          pieceLengthBound N ρ.length h t := by
  have hd : 0 < ρ.length := List.length_pos_iff.mpr hρ.ne_nil
  have hM : 0 < statePeriodModulus N ρ.length := lt_of_lt_of_le hd (d_le_statePeriodModulus _ _)
  obtain ⟨z, hs, hf, _, hz0, hpath⟩ := least_shifts (W := W) (ρ := ρ) N
  refine ⟨deletionCounts z, admissible_deletionCounts hs hf hz0 hM, ?_⟩
  intro P hP
  obtain ⟨p, hnd, hlast, ⟨Q, hhead, hanchor⟩, ht⟩ := hpath ⟨P, hP⟩
  have hg : p.IsChain (fun P Q => FollowerEdge P.val Q.val) :=
    ht.imp (fun _ _ h => (tight_step hM h).1)
  have hplen := occurrence_path_bound split p hnd hg
  cases p with
  | nil => simp at hlast
  | cons R p =>
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst R
    let v : {P // P ∈ piecesOf W ρ} → ℤ :=
        fun P => (P.val.len : ℤ) + statePeriodModulus N ρ.length * z P
    have hsteps : ∀ A B, (shiftSystem W ρ N).IsTight z A B →
        v B ≤ v A + (comparisonGap N ρ.length + statePeriodModulus N ρ.length : ℕ) := by
      intro A B h
      have := (tight_step hM h).2
      dsimp [v]
      omega
    have hb := path_length_bound v (comparisonGap N ρ.length + statePeriodModulus N ρ.length : ℕ)
      ((shiftSystem W ρ N).IsTight z) hsteps Q p ht
    have hlast' : (Q :: p).getLast (List.cons_ne_nil _ _) = ⟨P, hP⟩ := by
      rw [List.getLast?_eq_some_getLast (List.cons_ne_nil _ _)] at hlast
      exact Option.some.inj hlast
    rw [hlast'] at hb
    have hfloor : v Q < (fixedMargin N ρ.length : ℤ) + statePeriodModulus N ρ.length := by
      dsimp [v]; rw [hanchor]; exact floor_remainder_lt hM
    have hlen : (p.length : ℤ) ≤ ((t + 1) * 2 ^ h - 1 : ℕ) := by
      simp only [List.length_cons] at hplen
      omega
    have hB : (0 : ℤ) ≤
        (comparisonGap N ρ.length + statePeriodModulus N ρ.length : ℕ) := by positivity
    have hmult := mul_le_mul_of_nonneg_right hlen hB
    have hcast := retained_cast hf hz0 ⟨P, hP⟩
    change ((P.len - statePeriodModulus N ρ.length * deletionCounts z P : ℕ) : ℤ) =
        v ⟨P, hP⟩ at hcast
    have hcap : ((pieceLengthBound N ρ.length h t : ℕ) : ℤ) =
        fixedMargin N ρ.length + statePeriodModulus N ρ.length + ((t + 1) * 2 ^ h - 1 : ℕ) *
          (comparisonGap N ρ.length + statePeriodModulus N ρ.length :
              ℕ) := by simp [pieceLengthBound]
    omega

end

end DeciSigma1.Holes.Periodic
