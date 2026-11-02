/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Polynomials.IrreducibleSystem
public import LeanPool.NairTenenbaum.Progressions.ProgressionIntervals

/-! # The explicit tuple main term for irreducible polynomial families -/

@[expose] public section

namespace NairTenenbaum

/-- Adding the progression modulus to the discriminant restriction. -/
theorem dagger_mul_iff {k D q : ℕ} (n : Tuple k) :
    Dagger (D * q) n ↔ Dagger D n ∧ ∀ i, Nat.Coprime q (n i) := by
  constructor
  · rintro ⟨hp, hc⟩
    exact ⟨⟨hp, fun i => ((Nat.coprime_mul_iff_right).mp (hc i)).1⟩,
      fun i => (((Nat.coprime_mul_iff_right).mp (hc i)).2).symm⟩
  · rintro ⟨⟨hp, hc⟩, hq⟩
    exact ⟨hp, fun i => Nat.coprime_mul_iff_right.mpr ⟨hc i, (hq i).symm⟩⟩

/-- Positive tuples with product at most `x`, pairwise coprime coordinates,
and every coordinate coprime to both `D` and `q`. -/
noncomputable def irreducibleProgressionTuples (k D q : ℕ) (x : ℝ) : Finset (Tuple k) := by
  classical
  exact (tupleBox k (Nat.toPNat' ⌊x⌋₊)).filter (fun n => (mass n : ℝ) ≤ x ∧ Dagger (D * q) n)

theorem mem_irreducibleProgressionTuples {k D q : ℕ} {x : ℝ} {n : Tuple k} :
    n ∈ irreducibleProgressionTuples k D q x ↔ (mass n : ℝ) ≤ x ∧ Dagger (D * q) n := by
  classical
  simp only [irreducibleProgressionTuples, Finset.mem_filter]
  refine ⟨And.right, fun H => ⟨mem_tupleBox.mpr (fun i => ?_), H⟩⟩
  have hm : (1 : ℝ) ≤ mass n := by exact_mod_cast mass_pos n
  have hfloor : 0 < ⌊x⌋₊ := Nat.floor_pos.mpr (hm.trans H.1)
  change (n i : ℕ) ≤ (Nat.toPNat' ⌊x⌋₊ : ℕ)
  rw [PNat.toPNat'_coe hfloor]
  apply (Nat.le_floor_iff (by linarith : 0 ≤ x)).mpr
  have Hcoord : (n i : ℕ) ≤ mass n := by
    simpa only [weightedMass_identity] using
      coordinate_le_weightedMass (identityExponents k) (by intro j; simp) n i
  exact (by exact_mod_cast Hcoord : (n i : ℝ) ≤ mass n).trans H.1

/-- Exact reindexing of the identity-exponent weight with the progression
coprimality condition. No arithmetic positivity assumption is needed. -/
theorem sum_identity_weight_coprime_eq {k : ℕ} (D q : ℕ) (F : ArithmeticMap k)
    (θ : Fin k → ℕ → ℝ) (x : ℝ) :
    (∑ N ∈ (positiveUpTo x).filter (fun N : ℕ+ => Nat.Coprime q N),
      weight (identityExponents k) D F θ N) =
    ∑ n ∈ irreducibleProgressionTuples k D q x, F n * ∏ i, θ i (n i) / (n i : ℝ) := by
  classical
  let S := irreducibleProgressionTuples k D q x
  let T := (positiveUpTo x).filter (fun N : ℕ+ => Nat.Coprime q N)
  let M : Tuple k → ℕ+ := fun n => ⟨mass n, mass_pos n⟩
  have hγ : ∀ i, 0 < totalExponent (identityExponents k) i := by intro i; simp
  have hmass (n : Tuple k) : Nat.Coprime q (mass n) ↔ ∀ i, Nat.Coprime q (n i) := by
    simpa only [weightedMass_identity] using coprime_weightedMass_iff (identityExponents k) hγ q n
  have hmap : ∀ n ∈ S, M n ∈ T := by
    intro n hn
    have H := mem_irreducibleProgressionTuples.mp hn
    exact Finset.mem_filter.mpr ⟨(mem_positiveUpTo _ _).mpr H.1,
      (hmass n).mpr ((dagger_mul_iff n).mp H.2).2⟩
  have hfiber (N : ℕ+) (hN : N ∈ T) :
      S.filter (fun n => M n = N) = weightFiber (identityExponents k) D N := by
    ext n
    rw [Finset.mem_filter, mem_weightFiber _ hγ]
    change (n ∈ irreducibleProgressionTuples k D q x ∧ M n = N) ↔ _
    rw [mem_irreducibleProgressionTuples, weightedMass_identity, dagger_mul_iff]
    have heq : M n = N ↔ mass n = (N : ℕ) := Subtype.ext_iff
    rw [heq]
    constructor
    · rintro ⟨⟨_, hd, _⟩, he⟩
      exact ⟨he, hd⟩
    · rintro ⟨he, hd⟩
      have HN := Finset.mem_filter.mp hN
      refine ⟨⟨?_, hd, ?_⟩, he⟩
      · simpa only [he] using (mem_positiveUpTo N x).mp HN.1
      · exact (hmass n).mp (he.symm ▸ HN.2)
  change (∑ N ∈ T, weight (identityExponents k) D F θ N) =
    ∑ n ∈ S, F n * ∏ i, θ i (n i) / (n i : ℝ)
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  apply Finset.sum_congr rfl
  intro N hN
  rw [hfiber N hN]
  simp only [weight, pullback, substitute_identity]

/-- The right-hand side of (20), without its implicit constant. -/
noncomputable def irreducibleProgressionMainTerm {k : ℕ} (Q : Fin k → Polynomial ℤ)
    (F : ArithmeticMap k) (q : ℕ) (x y : ℝ) : ℝ :=
  (y / q) * progressionSieveProduct (∏ j, Q j) q x *
    ∑ n ∈ irreducibleProgressionTuples k (∏ j, Q j).discr.natAbs q x,
      F n * ∏ j, (rootCount (Q j) (n j) : ℝ) / (n j : ℝ)

theorem ofIrreducible_progressionMainTerm {k : ℕ} (Q : Fin k → Polynomial ℤ)
    (hQ : ∀ j, Irreducible ((Q j).map (Int.castRingHom ℚ)))
    (hcoprime : ∀ i j, i ≠ j → IsCoprime ((Q i).map (Int.castRingHom ℚ)) ((Q j).map
        (Int.castRingHom ℚ)))
    (hfixed : NoFixedPrimeDivisor (∏ j, Q j)) (F : ArithmeticMap k) (q : ℕ) (x y : ℝ) :
    progressionMainTerm (PolynomialSystem.ofIrreducible Q hQ hcoprime hfixed) F q x y =
      irreducibleProgressionMainTerm Q F q x y := by
  unfold progressionMainTerm irreducibleProgressionMainTerm
  rw [PolynomialSystem.ofIrreducible_total]
  congr 1
  exact sum_identity_weight_coprime_eq _ _ _ _ x

end NairTenenbaum
