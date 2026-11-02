/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.NumberFields.NumberFieldPrimeNormRoots
public import LeanPool.NairTenenbaum.NumberFields.PrimeIdealErrorBounds

/-! # The degree-one prime-ideal sum and the polynomial root sum -/

@[expose] public section

namespace NairTenenbaum

open Finset Real Polynomial NumberField Ideal

variable {K : Type*} [Field K] [NumberField K]

theorem primeIdeals_degreeOne_sum_le (θ : 𝓞 K) (S : Finset (Ideal (𝓞 K)))
    (hS : ∀ P ∈ S, Prime P) (hdeg : ∀ P ∈ S, Ideal.absNorm P = rationalPrimeBelow P)
    (hgood : ∀ P ∈ S, (rationalPrimeBelow P).Coprime (RingOfIntegers.exponent θ)) (σ : ℝ) :
    (∑ P ∈ S, (Ideal.absNorm P : ℝ) ^ (-σ)) ≤
      ∑ p ∈ S.image rationalPrimeBelow, (rootCount (minpoly ℤ θ) p : ℝ) * (p : ℝ) ^ (-σ) := by
  classical
  rw [← sum_fiberwise_of_maps_to (g := rationalPrimeBelow) (s := S) (t := S.image
      rationalPrimeBelow) (fun P hP => mem_image.mpr ⟨P, hP, rfl⟩)]
  apply sum_le_sum
  intro p hp
  obtain ⟨P, hP, hPb⟩ := mem_image.mp hp
  have hp' : p.Prime := hPb ▸ rationalPrimeBelow_prime (hS P hP)
  have hc : p.Coprime (RingOfIntegers.exponent θ) := hPb ▸ hgood P hP
  let T := S.filter (fun P => rationalPrimeBelow P = p)
  let f : T → {I : Ideal (𝓞 K) // Ideal.absNorm I = p} :=
    fun I => ⟨I.1, (hdeg I.1 (mem_filter.mp I.2).1).trans (mem_filter.mp I.2).2⟩
  have hf : Function.Injective f := fun I J h => Subtype.ext
    (show I.1 = J.1 from congrArg (fun x => x.1) h)
  let : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = p} := (Ideal.finite_setOfPred_absNorm_eq
      p).to_subtype
  have hcard : T.card ≤ rootCount (minpoly ℤ θ) p := by
    rw [rootCount_minpoly_eq_idealNormCount θ hp' hc]
    simpa [idealNormCount] using Nat.card_le_card_of_injective f hf
  calc
    _ = (T.card : ℝ) * (p : ℝ) ^ (-σ) := by
      calc
        _ = ∑ _I ∈ T, (p : ℝ) ^ (-σ) := sum_congr rfl (fun I hI => by
          rw [hdeg I (mem_filter.mp hI).1, (mem_filter.mp hI).2])
        _ = _ := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by
      exact_mod_cast hcard) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem primeIdeals_bad_sum_le {D : ℕ} (hD : D ≠ 0) (S : Finset (Ideal (𝓞 K)))
    (hS : ∀ P ∈ S, Prime P) (hbad : ∀ P ∈ S, rationalPrimeBelow P ∣ D)
    {σ : ℝ} (hσ : 1 ≤ σ) :
    (∑ P ∈ S, (Ideal.absNorm P : ℝ) ^ (-σ)) ≤
      (Module.finrank ℚ K : ℝ) * D.primeFactors.card := by
  have hcard : (S.card : ℝ) ≤ (Module.finrank ℚ K : ℝ) * (S.image rationalPrimeBelow).card := by
    simpa using primeIdeals_sum_baseWeight_le S hS (fun _ => 1) (fun _ => zero_le_one)
  have hsub : S.image rationalPrimeBelow ⊆ D.primeFactors := by
    intro p hp
    obtain ⟨P, hP, rfl⟩ := mem_image.mp hp
    exact Nat.mem_primeFactors.mpr ⟨rationalPrimeBelow_prime (hS P hP), hbad P hP, hD⟩
  calc
    _ ≤ ∑ _P ∈ S, (1 : ℝ) := sum_le_sum (fun P hP => (idealNorm_prime_weight_le_half (hS P hP)
        hσ).trans (by
      norm_num))
    _ = S.card := by simp
    _ ≤ _ := hcard.trans (mul_le_mul_of_nonneg_left (by
      exact_mod_cast card_le_card hsub) (Nat.cast_nonneg _))

theorem primeIdeals_sum_le_rootSum_add_error (θ : 𝓞 K) (hD : RingOfIntegers.exponent θ ≠ 0)
    (S : Finset (Ideal (𝓞 K))) (hS : ∀ P ∈ S, Prime P) {σ : ℝ} (hσ : 1 ≤ σ) :
    (∑ P ∈ S, (Ideal.absNorm P : ℝ) ^ (-σ)) ≤
      (∑ p ∈ S.image rationalPrimeBelow, (rootCount (minpoly ℤ θ) p : ℝ) * (p : ℝ) ^ (-σ)) +
      (Module.finrank ℚ K : ℝ) * ((RingOfIntegers.exponent θ).primeFactors.card +
        ∑' n : ℕ, (n : ℝ) ^ (-2 : ℝ)) := by
  classical
  let T := S.filter (fun P => Ideal.absNorm P = rationalPrimeBelow P)
  let G := T.filter (fun P => (rationalPrimeBelow P).Coprime (RingOfIntegers.exponent θ))
  let B := T.filter (fun P => ¬(rationalPrimeBelow P).Coprime (RingOfIntegers.exponent θ))
  have hT (P : Ideal (𝓞 K)) (hP : P ∈ T) := hS P (mem_filter.mp hP).1
  have HG := primeIdeals_degreeOne_sum_le θ G
    (fun P hP => hT P (mem_filter.mp hP).1)
    (fun P hP => (mem_filter.mp (mem_filter.mp hP).1).2)
    (fun P hP => (mem_filter.mp hP).2) σ
  have HGE : (∑ P ∈ G, (Ideal.absNorm P : ℝ) ^ (-σ)) ≤
      ∑ p ∈ S.image rationalPrimeBelow, (rootCount (minpoly ℤ θ) p : ℝ) * (p : ℝ) ^ (-σ) := by
    apply HG.trans
    apply sum_le_sum_of_subset_of_nonneg (image_subset_image ?_)
    · exact fun p _ _ => mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    · exact (filter_subset _ _).trans (filter_subset _ _)
  have HB := primeIdeals_bad_sum_le hD B (fun P hP => hT P (mem_filter.mp hP).1)
    (fun P hP => by
      have hp := rationalPrimeBelow_prime (hT P (mem_filter.mp hP).1)
      exact not_not.mp (fun hn => (mem_filter.mp hP).2 (hp.coprime_iff_not_dvd.mpr hn))) hσ
  have HH := primeIdeal_higherDegree_sum_le S hS hσ
  have HE₁ := sum_filter_add_sum_filter_not S (fun P => Ideal.absNorm P = rationalPrimeBelow P)
    (fun P => (Ideal.absNorm P : ℝ) ^ (-σ))
  have HE₂ := sum_filter_add_sum_filter_not T
    (fun P => (rationalPrimeBelow P).Coprime (RingOfIntegers.exponent θ))
    (fun P => (Ideal.absNorm P : ℝ) ^ (-σ))
  change (∑ P ∈ G, _) + (∑ P ∈ B, _) = ∑ P ∈ T, _ at HE₂
  change (∑ P ∈ T, _) + _ = _ at HE₁
  nlinarith

theorem primeIdeals_eulerExponent_le (θ : 𝓞 K) (hD : RingOfIntegers.exponent θ ≠ 0)
    (S : Finset (Ideal (𝓞 K))) (hS : ∀ P ∈ S, Prime P) {σ : ℝ} (hσ : 1 ≤ σ) :
    (∑ P ∈ S, ((Ideal.absNorm P : ℝ) ^ (-σ) + 2 * ((Ideal.absNorm P : ℝ) ^ (-σ)) ^ 2)) ≤
      (∑ p ∈ S.image rationalPrimeBelow, (rootCount (minpoly ℤ θ) p : ℝ) * (p : ℝ) ^ (-σ)) +
      (Module.finrank ℚ K : ℝ) * ((RingOfIntegers.exponent θ).primeFactors.card +
        3 * ∑' n : ℕ, (n : ℝ) ^ (-2 : ℝ)) := by
  have H := primeIdeals_sum_le_rootSum_add_error θ hD S hS hσ
  have H₂ := primeIdeal_square_error_sum_le S hS hσ
  rw [sum_add_distrib, ← mul_sum]
  nlinarith

end NairTenenbaum
