/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Hooley.HooleyDivisorEulerBound
public import LeanPool.NairTenenbaum.NumberFields.PrimeIdealRootComparison

/-! # The ideal-norm series is bounded by the root Euler exponential -/

@[expose] public section

namespace NairTenenbaum

open Finset Real Polynomial NumberField Ideal UniqueFactorizationMonoid

variable {K : Type*} [Field K] [NumberField K]

/-- The finite set of integral ideals with a specified absolute norm. -/
noncomputable def idealsOfNorm (n : ℕ) : Finset (Ideal (𝓞 K)) :=
  (Ideal.finite_setOfPred_absNorm_eq n).toFinset

@[simp] theorem mem_idealsOfNorm (I : Ideal (𝓞 K)) (n : ℕ) :
    I ∈ idealsOfNorm n ↔ Ideal.absNorm I = n := Set.Finite.mem_toFinset _

theorem card_idealsOfNorm (n : ℕ) : (idealsOfNorm (K := K) n).card = idealNormCount K n := by
  change _ = Set.ncard {I : Ideal (𝓞 K) | Ideal.absNorm I = n}
  exact (Set.ncard_eq_toFinset_card _ (Ideal.finite_setOfPred_absNorm_eq n)).symm

theorem idealNormCount_sum_eq (T : Finset ℕ) (w : ℕ → ℝ) :
    (∑ n ∈ T, (idealNormCount K n : ℝ) * w n) =
      ∑ I ∈ T.biUnion (idealsOfNorm (K := K)), w (Ideal.absNorm I) := by
  classical
  let U := T.biUnion (idealsOfNorm (K := K))
  have hU (I : Ideal (𝓞 K)) : I ∈ U ↔ Ideal.absNorm I ∈ T := by simp [U]
  rw [← sum_fiberwise_of_maps_to (g := Ideal.absNorm) (s := U) (t := T)
    (fun I hI => (hU I).mp hI)]
  apply sum_congr rfl
  intro n hn
  have HF : U.filter (fun I => Ideal.absNorm I = n) = idealsOfNorm n := by
    ext I
    simp only [mem_filter, hU, mem_idealsOfNorm]
    exact ⟨fun h => h.2, fun h => ⟨h ▸ hn, h⟩⟩
  rw [HF]
  calc
    _ = ∑ _I ∈ idealsOfNorm (K := K) n, w n := by simp [card_idealsOfNorm]
    _ = _ := sum_congr rfl (fun I hI => congrArg w (mem_idealsOfNorm I n |>.mp hI).symm)

/-- The local error in comparing root and ideal Euler factors. -/
noncomputable def idealRootEulerError (θ : 𝓞 K) : ℝ :=
  (Module.finrank ℚ K : ℝ) * ((RingOfIntegers.exponent θ).primeFactors.card +
    3 * ∑' n : ℕ, (n : ℝ) ^ (-2 : ℝ))

theorem finite_idealNorm_sum_le_root_exp (θ : 𝓞 K) (hD : RingOfIntegers.exponent θ ≠ 0)
    (T : Finset (Ideal (𝓞 K))) (hT : ∀ I ∈ T, I ≠ ⊥) {σ : ℝ} (hσ : 1 ≤ σ)
    (hs : Summable (fun p : Nat.Primes => (rootCount (minpoly ℤ θ) p.1 : ℝ) * (p.1 : ℝ) ^ (-σ))) :
    (∑ I ∈ T, (Ideal.absNorm I : ℝ) ^ (-σ)) ≤
      Real.exp (rootPrimePowerSum (minpoly ℤ θ) σ + idealRootEulerError θ) := by
  classical
  let S := T.biUnion (fun I => (normalizedFactors I).toFinset)
  have hS (P : Ideal (𝓞 K)) (hP : P ∈ S) : Prime P := by
    obtain ⟨I, _, hI⟩ := mem_biUnion.mp hP
    exact prime_of_normalized_factor P (Multiset.mem_toFinset.mp hI)
  have HF := finite_idealNorm_sum_le_exp T S hT hS
    (fun I hI P hP => mem_biUnion.mpr ⟨I, hI, hP⟩) hσ
  apply HF.trans (Real.exp_le_exp.mpr ?_)
  apply (primeIdeals_eulerExponent_le θ hD S hS hσ).trans
  change _ + idealRootEulerError θ ≤ _ + idealRootEulerError θ
  apply add_le_add _ le_rfl
  exact prime_finset_sum_le_tsum (fun p : ℕ => (rootCount (minpoly ℤ θ) p : ℝ) * (p : ℝ) ^ (-σ))
      (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    hs (S.image rationalPrimeBelow) (by
      intro p hp
      obtain ⟨P, hP, rfl⟩ := mem_image.mp hp
      exact rationalPrimeBelow_prime (hS P hP))

theorem idealNormDirichlet_le_root_exp (θ : 𝓞 K) (hD : RingOfIntegers.exponent θ ≠ 0)
    {σ : ℝ} (hσ : 1 < σ)
    (hs : Summable (fun p : Nat.Primes => (rootCount (minpoly ℤ θ) p.1 : ℝ) * (p.1 : ℝ) ^ (-σ))) :
    idealNormDirichlet K σ ≤ Real.exp (rootPrimePowerSum (minpoly ℤ θ) σ + idealRootEulerError θ)
        := by
  classical
  apply Real.tsum_le_of_sum_le (fun n => mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg
      (Nat.cast_nonneg _) _))
  intro T
  have HE : (∑ n ∈ T, (idealNormCount K n : ℝ) * (n : ℝ) ^ (-σ)) =
      ∑ n ∈ T.filter (fun n => n ≠ 0), (idealNormCount K n : ℝ) * (n : ℝ) ^ (-σ) := by
    symm
    apply sum_subset (filter_subset _ _)
    intro n hn hnot
    have hn₀ : n = 0 := by simpa only [mem_filter, hn, true_and, not_not] using hnot
    subst n
    simp [Real.zero_rpow (by linarith : -σ ≠ 0)]
  rw [HE, idealNormCount_sum_eq]
  apply finite_idealNorm_sum_le_root_exp θ hD _ _ hσ.le hs
  intro I hI hzero
  obtain ⟨n, hn, hIn⟩ := mem_biUnion.mp hI
  have H := (mem_idealsOfNorm I n).mp hIn
  rw [hzero, Ideal.absNorm_bot] at H
  exact (mem_filter.mp hn).2 H.symm

end NairTenenbaum
