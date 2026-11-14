/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.TupleComparison

/-! # Truncated dagger tuples and the weight sum

The finite domains used in the global comparison, their closure under whole
prime-power removal, and the exact reindexing of equation (16).
-/

@[expose] public section

namespace NairTenenbaum

open Finset

theorem unitaryPart_dvd (n : ℕ+) (s : Finset ℕ) : (unitaryPart n s : ℕ) ∣ n := by
  use (unitaryRest n s : ℕ)
  exact congrArg (fun x : ℕ+ => (x : ℕ)) (unitaryPart_mul_rest n s).symm

theorem unitaryRest_dvd (n : ℕ+) (s : Finset ℕ) : (unitaryRest n s : ℕ) ∣ n := by
  use (unitaryPart n s : ℕ)
  simpa only [PNat.mul_coe, mul_comm] using congrArg (fun x : ℕ+ => (x : ℕ)) (unitaryPart_mul_rest
      n s).symm

theorem Dagger.of_coordinate_dvd {r D : ℕ} {n m : Tuple r} (hn : Dagger D n)
    (hm : ∀ i, (m i : ℕ) ∣ n i) : Dagger D m := by
  exact ⟨fun i j hij => Nat.Coprime.of_dvd (hm i) (hm j) (hn.1 i j hij),
    fun i => Nat.Coprime.of_dvd (hm i) (dvd_refl D) (hn.2 i)⟩

theorem Dagger.of_tupleUnitaryRest {r D : ℕ} {n : Tuple r} (hn : Dagger D n)
    (t : Fin r → Finset ℕ) : Dagger D (tupleUnitaryRest n t) :=
  hn.of_coordinate_dvd (fun i => unitaryRest_dvd (n i) (t i))

theorem Dagger.of_tupleUnitaryPart {r D : ℕ} {n : Tuple r} (hn : Dagger D n)
    (t : Fin r → Finset ℕ) : Dagger D (tupleUnitaryPart n t) :=
  hn.of_coordinate_dvd (fun i => unitaryPart_dvd (n i) (t i))

/-- Independently chosen coordinate splittings are cross-coprime on dagger tuples. -/
theorem Dagger.unitary_cross_coprime {r D : ℕ} {n : Tuple r} (hn : Dagger D n)
    (t : Fin r → Finset ℕ) (i j : Fin r) :
    Nat.Coprime (tupleUnitaryPart n t i) (tupleUnitaryRest n t j) := by
  by_cases hij : i = j
  · subst j
    exact unitaryPart_coprime_rest (n i) (t i)
  · exact Nat.Coprime.of_dvd (unitaryPart_dvd (n i) (t i)) (unitaryRest_dvd (n j) (t j))
      (hn.1 i j hij)

/-- Dagger tuples with weighted mass at most the specified cutoff. -/
noncomputable def weightUpTo {k r : ℕ} (γ : Fin k → Fin r → ℕ) (D : ℕ) (N : ℕ+) :
    Finset (Tuple r) := by
  classical
  exact (tupleBox r N).filter (fun n => weightedMass γ n ≤ N ∧ Dagger D n)

theorem mem_weightUpTo {k r : ℕ} (γ : Fin k → Fin r → ℕ)
    (hγ : ∀ i, 0 < totalExponent γ i) (D : ℕ) (N : ℕ+) (n : Tuple r) :
    n ∈ weightUpTo γ D N ↔ weightedMass γ n ≤ N ∧ Dagger D n := by
  classical
  simp only [weightUpTo, Finset.mem_filter]
  refine ⟨And.right, fun hn => ⟨mem_tupleBox.mpr (fun i => ?_), hn⟩⟩
  exact (coordinate_le_weightedMass γ hγ n i).trans hn.1

theorem weightUpTo_coordinate_le {k r : ℕ} (γ : Fin k → Fin r → ℕ) (D : ℕ) (N : ℕ+)
    {n : Tuple r} (hn : n ∈ weightUpTo γ D N) (i : Fin r) : n i ≤ N := by
  classical
  exact mem_tupleBox.mp (Finset.mem_filter.mp hn).1 i

theorem weightedMass_unitaryRest_le {k r : ℕ} (γ : Fin k → Fin r → ℕ)
    (n : Tuple r) (t : Fin r → Finset ℕ) : weightedMass γ (tupleUnitaryRest n t) ≤ weightedMass γ
        n := by
  have h := Nat.le_mul_of_pos_left (weightedMass γ (tupleUnitaryRest n t))
    (weightedMass_pos γ (tupleUnitaryPart n t))
  rwa [← weightedMass_mul, tupleUnitaryPart_mul_rest] at h

theorem tupleUnitaryRest_mem_weightUpTo {k r : ℕ} (γ : Fin k → Fin r → ℕ)
    (hγ : ∀ i, 0 < totalExponent γ i) (D : ℕ) (N : ℕ+) {n : Tuple r}
    (hn : n ∈ weightUpTo γ D N) (t : Fin r → Finset ℕ) :
    tupleUnitaryRest n t ∈ weightUpTo γ D N := by
  rw [mem_weightUpTo γ hγ] at hn ⊢
  exact ⟨(weightedMass_unitaryRest_le γ n t).trans hn.1, hn.2.of_tupleUnitaryRest t⟩

/-- Every original fiber sum is retained exactly once by the truncated tuple sum. -/
theorem sum_weight_eq_sum_weightUpTo {k r : ℕ} (γ : Fin k → Fin r → ℕ)
    (hγ : ∀ i, 0 < totalExponent γ i) (D : ℕ) (F : ArithmeticMap k)
    (θ : Fin r → ℕ → ℝ) (N : ℕ+) :
    (∑ m ∈ Finset.Icc 1 N, weight γ D F θ m) =
      ∑ n ∈ weightUpTo γ D N, pullback γ F n * ∏ i, θ i (n i) / (n i : ℝ) := by
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
  rw [hfiber m hm]
  rfl

end NairTenenbaum
