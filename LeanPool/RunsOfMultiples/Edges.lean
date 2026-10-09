/-
Copyright (c) 2026 Jason Hoelscher-Obermaier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hoelscher-Obermaier, Claude Opus 5.5
-/
module

-- Adapted for Lean Pool: module visibility, imports, and proof organization.

public import LeanPool.RunsOfMultiples.OneStep

/-!
# Counting prime edges with entropy (Lemma 4)

For each prime `p`, the fibres of the `p`-smooth part split `T`; on each fibre Lemma 3 applies
with level `v_p`. Summing over primes and using the chain rule gives the edge bound.
-/

open Finset Real

@[expose] public section

namespace RunsOfMultiples

/-- Per prime: if `p * m ∈ T` for all `m ∈ G ⊆ T`, then the fibrewise Lemma 3 bounds hold. -/
lemma mem_fibre_of_prime_mul {T : Finset ℕ} (hT : ∀ m ∈ T, 0 < m) {p q : ℕ} (hp : p.Prime)
    (hqp : q ≤ p) {m : ℕ} (hm : m ∈ T) (hpm : p * m ∈ T) :
    p * m ∈ T.filter (fun x => key q x = key q m) := by
  rw [mem_filter]
  exact ⟨hpm, key_prime_mul hp hqp (hT m hm).ne'⟩

/-- `D T p ≥ (log 2 / 2) |G|` whenever multiplication by the prime `p` maps `G ⊆ T` into `T`. -/
lemma D_ge_log_two (T : Finset ℕ) (hT : ∀ m ∈ T, 0 < m) {p : ℕ} (hp : p.Prime)
    (G : Finset ℕ) (hGT : G ⊆ T) (hG : ∀ m ∈ G, p * m ∈ T) :
    log 2 / 2 * G.card ≤ D T p := by
  unfold D
  have hcard : (G.card : ℝ) =
      ∑ c ∈ T.image (key p), ((G.filter (fun m => key p m = c)).card : ℝ) := by
    rw [← Nat.cast_sum, card_eq_sum_card_fiberwise (f := key p)]
    intro m hm
    exact mem_image_of_mem _ (hGT hm)
  rw [hcard, mul_sum]
  refine sum_le_sum fun c _ => ?_
  refine ent_ge_log_two _ _ _ p hp.pos ?_ ?_
  · intro m hm
    rw [mem_filter] at hm ⊢
    exact ⟨hGT hm.1, hm.2⟩
  · intro m hm
    rw [mem_filter] at hm
    have hmT := hGT hm.1
    refine ⟨?_, factorization_prime_mul_self hp (hT m hmT).ne'⟩
    rw [mem_filter]
    refine ⟨hG m hm.1, ?_⟩
    rw [key_prime_mul hp le_rfl (hT m hmT).ne', hm.2]

/-- **Lemma 4** (edge count). -/
theorem edge_bound (T : Finset ℕ) (hT : ∀ m ∈ T, 0 < m) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (E : ℕ → Finset ℕ) (hET : ∀ p ∈ P, E p ⊆ T) (hE : ∀ p ∈ P, ∀ m ∈ E p, p * m ∈ T) :
    log 2 / 2 * ∑ p ∈ P, ((E p).card : ℝ) ≤ T.card * log T.card := by
  set B := T.sup id + 1
  have hB : ∀ m ∈ T, m < B := fun m hm => Nat.lt_succ_of_le (le_sup (f := id) hm)
  -- primes with a nonempty `E p` are below `B`
  have hsplit : ∑ p ∈ P, ((E p).card : ℝ) = ∑ p ∈ P.filter (· < B), ((E p).card : ℝ) := by
    rw [sum_filter]
    refine sum_congr rfl fun p hp => ?_
    split_ifs with h
    · rfl
    · push Not at h
      rw [card_eq_zero.2, Nat.cast_zero]
      rw [eq_empty_iff_forall_notMem]
      intro m hm
      have hpm := hB _ (hE p hp m hm)
      have hm0 := hT m (hET p hp hm)
      have : p ≤ p * m := Nat.le_mul_of_pos_right p hm0
      omega
  rw [hsplit, mul_sum]
  calc ∑ p ∈ P.filter (· < B), log 2 / 2 * ((E p).card : ℝ)
      ≤ ∑ p ∈ P.filter (· < B), D T p := by
        refine sum_le_sum fun p hp => ?_
        rw [mem_filter] at hp
        exact D_ge_log_two T hT (hP p hp.1) (E p) (hET p hp.1) (hE p hp.1)
    _ ≤ T.card * log T.card := by
        refine sum_D_le T hT hB _ ?_
        intro p hp
        rw [mem_filter] at hp
        exact mem_range.2 hp.2

end RunsOfMultiples
