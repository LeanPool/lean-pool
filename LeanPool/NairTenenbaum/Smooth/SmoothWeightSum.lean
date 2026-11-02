/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Smooth.SmoothMoment

/-! # Smooth moments and tails in the paper's weight notation

Exact reindexing of weighted-mass fibers identifies the smooth dagger-tuple
bounds with bounds for the one-variable weight (16). No tuple is discarded,
and no prime-support condition is weakened.
-/

@[expose] public section

namespace NairTenenbaum

open Polynomial Finset

theorem coordinate_dvd_weightedMass {k r : ℕ} (γ : Fin k → Fin r → ℕ)
    (hγ : ∀ i, 0 < totalExponent γ i) (n : Tuple r) (i : Fin r) :
    (n i : ℕ) ∣ weightedMass γ n :=
  (dvd_pow_self _ (Nat.ne_of_gt (hγ i))).trans
    (Finset.dvd_prod_of_mem (fun j => (n j : ℕ) ^ totalExponent γ j) (Finset.mem_univ i))

theorem weightedMass_mem_factoredNumbers_iff {k r : ℕ} (γ : Fin k → Fin r → ℕ)
    (hγ : ∀ i, 0 < totalExponent γ i) (n : Tuple r) (s : Finset ℕ) :
    weightedMass γ n ∈ Nat.factoredNumbers s ↔ ∀ i, (n i : ℕ) ∈ Nat.factoredNumbers s := by
  constructor
  · intro hn i
    exact Nat.mem_factoredNumbers_of_dvd hn (coordinate_dvd_weightedMass γ hγ n i)
  · intro hn
    have hone : 1 ∈ Nat.factoredNumbers s :=
      Nat.mem_factoredNumbers_of_primeFactors_subset (by decide) (by simp)
    have hpow (i : Fin r) (ν : ℕ) : (n i : ℕ) ^ ν ∈ Nat.factoredNumbers s := by
      induction ν with
      | zero => simpa using hone
      | succ ν ih => simpa only [pow_succ] using Nat.mul_mem_factoredNumbers ih (hn i)
    unfold weightedMass
    exact Finset.prod_induction _ _ (fun _ _ => Nat.mul_mem_factoredNumbers) hone
      (fun i _ => hpow i _)

/-- A scalar multiplier may depend arbitrarily on the weighted mass. -/
theorem sum_weight_mul_eq_sum_weightUpTo {k r : ℕ} (γ : Fin k → Fin r → ℕ)
    (hγ : ∀ i, 0 < totalExponent γ i) (D : ℕ) (F : ArithmeticMap k)
    (θ : Fin r → ℕ → ℝ) (φ : ℕ+ → ℝ) (N : ℕ+) :
    (∑ m ∈ Finset.Icc 1 N, φ m * weight γ D F θ m) =
      ∑ n ∈ weightUpTo γ D N, φ ⟨weightedMass γ n, weightedMass_pos γ n⟩ *
        (pullback γ F n * ∏ i, θ i (n i) / (n i : ℝ)) := by
  classical
  let M : Tuple r → ℕ+ := fun n => ⟨weightedMass γ n, weightedMass_pos γ n⟩
  have hmap : ∀ n ∈ weightUpTo γ D N, M n ∈ Finset.Icc 1 N := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨one_le, ((mem_weightUpTo γ hγ D N n).mp hn).1⟩
  have hfiber (m : ℕ+) (hm : m ∈ Finset.Icc 1 N) :
      (weightUpTo γ D N).filter (fun n => M n = m) = weightFiber γ D m := by
    ext n
    simp only [Finset.mem_filter, mem_weightUpTo γ hγ, mem_weightFiber γ hγ]
    have heq : M n = m ↔ weightedMass γ n = (m : ℕ) := Subtype.ext_iff
    rw [heq]
    constructor
    · rintro ⟨⟨_, hd⟩, he⟩
      exact ⟨he, hd⟩
    · rintro ⟨he, hd⟩
      exact ⟨⟨he ▸ (Finset.mem_Icc.mp hm).2, hd⟩, he⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  apply Finset.sum_congr rfl
  intro m hm
  rw [hfiber m hm, weight, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have he : (⟨weightedMass γ n, weightedMass_pos γ n⟩ : ℕ+) = m :=
    Subtype.ext ((mem_weightFiber γ hγ D m n).mp hn).1
  rw [he]

open Classical in
/-- Reindexing with an arbitrary scalar predicate on the weighted mass. -/
theorem sum_weight_filter_eq {k r : ℕ} (γ : Fin k → Fin r → ℕ)
    (hγ : ∀ i, 0 < totalExponent γ i) (D : ℕ) (F : ArithmeticMap k)
    (θ : Fin r → ℕ → ℝ) (P : ℕ+ → Prop) [DecidablePred P] (N : ℕ+) :
    (∑ m ∈ (Finset.Icc 1 N).filter P, weight γ D F θ m) =
      ∑ n ∈ (weightUpTo γ D N).filter (fun n => P ⟨weightedMass γ n, weightedMass_pos γ n⟩),
        pullback γ F n * ∏ i, θ i (n i) / (n i : ℝ) := by
  classical
  simpa only [Finset.sum_filter, ite_mul, one_mul, zero_mul] using
    sum_weight_mul_eq_sum_weightUpTo γ hγ D F θ (fun m => if P m then 1 else 0) N

/-- The smooth restriction in the scalar weight is exactly coordinatewise
smoothness on its dagger tuples. -/
theorem sum_smooth_weight_eq {k r : ℕ} (γ : Fin k → Fin r → ℕ)
    (hγ : ∀ i, 0 < totalExponent γ i) (D : ℕ) (F : ArithmeticMap k)
    (Q : Fin r → ℤ[X]) (s : Finset ℕ) (N : ℕ+) :
    (∑ m ∈ (Finset.Icc 1 N).filter (fun m : ℕ+ => (m : ℕ) ∈ Nat.factoredNumbers s),
      weight γ D F (fun i m => (rootCount (Q i) m : ℝ)) m) =
      ∑ n ∈ smoothWeightUpTo γ D s N, rootTupleWeight γ F Q n := by
  rw [sum_weight_filter_eq γ hγ]
  simp only [PNat.mk_coe, weightedMass_mem_factoredNumbers_iff γ hγ, smoothWeightUpTo,
      rootTupleWeight]

/-- The same exact reindexing with a lower bound for the tail. -/
theorem sum_smooth_weight_tail_eq {k r : ℕ} (γ : Fin k → Fin r → ℕ)
    (hγ : ∀ i, 0 < totalExponent γ i) (D : ℕ) (F : ArithmeticMap k)
    (Q : Fin r → ℤ[X]) (s : Finset ℕ) (N : ℕ+) (x : ℝ) :
    (∑ m ∈ (Finset.Icc 1 N).filter
        (fun m : ℕ+ => (m : ℕ) ∈ Nat.factoredNumbers s ∧ x < (m : ℝ)),
      weight γ D F (fun i m => (rootCount (Q i) m : ℝ)) m) =
      ∑ n ∈ (smoothWeightUpTo γ D s N).filter (fun n => x < (weightedMass γ n : ℝ)),
        rootTupleWeight γ F Q n := by
  classical
  rw [sum_weight_filter_eq γ hγ]
  simp only [PNat.mk_coe, weightedMass_mem_factoredNumbers_iff γ hγ, smoothWeightUpTo,
      rootTupleWeight,
    Finset.filter_filter]

/-- The root-weighted Rankin bound in the paper's one-variable notation.
The smooth sum on the right still runs up to `N`; shrinking it to `z` is a
separate step in Lemma 2. -/
theorem PolynomialSystem.weight_smooth_tail_bound {k r : ℕ} (P : PolynomialSystem k r)
    {A B ε κ z x : ℝ} {F : ArithmeticMap k} (hF : Admissible A B ε F)
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε) (hκ : 0 ≤ κ) (hz : 2 ≤ z) (hx : 0 < x)
    (hzκ : (4 : ℝ) ^ ((P.total.natDegree : ℝ) * κ) ≤ z)
    (hεγ : ∀ i, (totalExponent P.exponent i : ℝ) * ε ≤ 1 / 8) (N : ℕ+) :
    (∑ m ∈ (Finset.Icc 1 N).filter (fun m : ℕ+ =>
        (m : ℕ) ∈ Nat.factoredNumbers (Finset.Icc 0 ⌊z⌋₊) ∧ x < (m : ℝ)), P.weight F m) ≤
      Real.exp (-κ * Real.log x / Real.log z) *
        ((∏ i, Real.exp (momentPrimeBound A B κ (7 / 8) (totalExponent P.exponent i)
          (max (P.R i).natDegree (P.badDiscriminant ^ 3)))) *
            ∑ m ∈ (Finset.Icc 1 N).filter
              (fun m : ℕ+ => (m : ℕ) ∈ Nat.factoredNumbers (Finset.Icc 0 ⌊z⌋₊)), P.weight F m) := by
  change (∑ m ∈ _, NairTenenbaum.weight P.exponent P.discriminant F
    (fun i m => (rootCount (P.R i) m : ℝ)) m) ≤ _
  rw [sum_smooth_weight_tail_eq P.exponent P.exponent_pos]
  have heq := sum_smooth_weight_eq P.exponent P.exponent_pos P.discriminant F P.R
    (Finset.Icc 0 ⌊z⌋₊) N
  change (∑ m ∈ _, P.weight F m) = _ at heq
  rw [heq]
  exact P.smooth_tail_bound hF hA hB hε hκ hz hx hzκ hεγ N

end NairTenenbaum
