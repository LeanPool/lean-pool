/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Smooth.PrimeBandCutoff

/-! # Covering prefixes by logarithmic prime bands -/

@[expose] public section

namespace NairTenenbaum

/-- A prefix with a prime factor above `w₀`, all of whose primes are at most
`x^u`, lies in an eligible dyadic band. Its existing next-prime cutoff is already
large enough to sift at the lower edge of that band. -/
theorem primeSelect_mem_dyadic_band {r : ℕ} (n : Tuple r) (q : ℕ)
    {x u w₀ : ℝ} (hx : 1 < x) (hw₀ : 1 ≤ w₀)
    (hupper : ∀ i p, p ∈ (primeSelect n (Finset.range q) i : ℕ).primeFactors → (p : ℝ) ≤ x ^ u)
    (hlower : ∃ i p, p ∈ (primeSelect n (Finset.range q) i : ℕ).primeFactors ∧ w₀ < (p : ℝ)) :
    ∃ j : ℕ, w₀ < x ^ (2 * (u / 2 ^ (j + 1))) ∧ x ^ (u / 2 ^ (j + 1)) < (q : ℝ) ∧
      ∀ i, (primeSelect n (Finset.range q) i : ℕ) ∈
        Nat.factoredNumbers (Finset.Icc 0 ⌊x ^ (2 * (u / 2 ^ (j + 1)))⌋₊) := by
  classical
  let S := (Finset.univ : Finset (Fin r)).biUnion
    (fun i => (primeSelect n (Finset.range q) i : ℕ).primeFactors)
  obtain ⟨i, p, hp, hwp⟩ := hlower
  have hpS : p ∈ S := Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hp⟩
  obtain ⟨p₀, hp₀, heq⟩ := Finset.exists_mem_eq_sup S ⟨p, hpS⟩ id
  have hmax : ∀ p ∈ S, p ≤ p₀ := by
    intro p hp
    have H : p ≤ S.sup id := Finset.le_sup (f := id) hp
    simpa only [heq, id_eq] using H
  obtain ⟨i₀, _, hi₀⟩ := Finset.mem_biUnion.mp hp₀
  have hwp₀ : w₀ < (p₀ : ℝ) := hwp.trans_le (by exact_mod_cast hmax p hpS)
  have hp₀q : p₀ < q := primeSelect_range_prime_lt n q i₀ hi₀
  obtain ⟨j, hjlo, hjhi⟩ := exists_dyadic_primeBand hx (hw₀.trans_lt hwp₀) (hupper i₀ p₀ hi₀)
  refine ⟨j, hwp₀.trans_le hjhi, hjlo.trans (by exact_mod_cast hp₀q), ?_⟩
  intro i
  apply Nat.mem_factoredNumbers_of_primeFactors_subset (primeSelect n (Finset.range q) i).ne_zero
  intro p hp
  have hp₀' : (p : ℝ) ≤ p₀ := by
    exact_mod_cast hmax p (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hp⟩)
  exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, (Nat.le_floor_iff
    (Real.rpow_nonneg (by linarith : 0 ≤ x) _)).mpr (hp₀'.trans hjhi)⟩

/-- The middle range of largest prefix primes. The two outside ranges will be
handled by the bounded-smoothness and large-next-prime estimates respectively. -/
def PolynomialSystem.HasIntermediatePrefix {k r : ℕ} (P : PolynomialSystem k r)
    (N : ℕ+) (X w₀ x u : ℝ) (t : ℤ) : Prop :=
  ∃ (n : Tuple r) (q : ℕ), (∀ i, (n i : ℕ) = ((P.R i).eval t).natAbs) ∧
    weightedMass P.exponent (primeSelect n (Finset.range q)) ≤ N ∧
    X < (weightedMass P.exponent (primeSelect n (Finset.range q)) : ℝ) ∧
    (∀ i p, p ∈ (primeSelect n (Finset.range q) i : ℕ).primeFactors → (p : ℝ) ≤ x ^ u) ∧
    ∃ i p, p ∈ (primeSelect n (Finset.range q) i : ℕ).primeFactors ∧ w₀ < (p : ℝ)

/-- The weighted contribution of prefixes in the intermediate prime range. -/
noncomputable def PolynomialSystem.intermediatePrefixContribution {k r : ℕ} (P : PolynomialSystem
    k r)
    (F : ArithmeticMap k) (N : ℕ+) (X w₀ x u : ℝ) (a b : ℤ) : ℝ := by
  classical
  exact ∑ t ∈ (Finset.Ioc a b).filter (P.HasIntermediatePrefix N X w₀ x u),
    extendArithmeticMap F (fun j => ((P.Q j).eval t).natAbs)

theorem PolynomialSystem.HasIntermediatePrefix.exists_band {k r : ℕ} {P : PolynomialSystem k r}
    {N : ℕ+} {X w₀ x u : ℝ} {t : ℤ} (h : P.HasIntermediatePrefix N X w₀ x u t)
    (hx : 1 < x) (hw₀ : 1 ≤ w₀) :
    ∃ j : ℕ, w₀ < x ^ (2 * (u / 2 ^ (j + 1))) ∧
      P.HasSmoothTailPrefix N (Finset.Icc 0 ⌊x ^ (2 * (u / 2 ^ (j + 1)))⌋₊)
        X (x ^ (u / 2 ^ (j + 1))) t := by
  obtain ⟨n, q, hn, hN, hX, hu, hw⟩ := h
  obtain ⟨j, hjw, hjq, hjs⟩ := primeSelect_mem_dyadic_band n q hx hw₀ hu hw
  exact ⟨j, hjw, n, q, hn, hN, hjs, hX, hjq⟩

/-- A finite weighted set covered by eligible finite sets uses only finitely
many of them. Overlap is harmless for nonnegative weights. -/
theorem exists_finset_sum_le_cover {ι κ : Type*} [Nonempty κ]
    (T : Finset ι) (U : κ → Finset ι) (eligible : κ → Prop) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hcover : ∀ i ∈ T, ∃ j, eligible j ∧ i ∈ U j) :
    ∃ J : Finset κ, (∀ j ∈ J, eligible j) ∧ (∑ i ∈ T, w i) ≤ ∑ j ∈ J, ∑ i ∈ U j, w i := by
  classical
  choose! f hf using hcover
  refine ⟨T.image f, ?_, ?_⟩
  · intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact (hf i hi).1
  · have hmap : ∀ i ∈ T, f i ∈ T.image f := fun i hi => Finset.mem_image.mpr ⟨i, hi, rfl⟩
    rw [← Finset.sum_fiberwise_of_maps_to hmap]
    apply Finset.sum_le_sum
    intro j _
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro i hi
      obtain ⟨hi, heq⟩ := Finset.mem_filter.mp hi
      exact heq ▸ (hf i hi).2
    · exact fun i _ _ => hw i

/-- The finite interval needs only finitely many eligible bands. Overlap causes
no loss because all arithmetic weights are nonnegative. -/
theorem PolynomialSystem.intermediatePrefixContribution_le_bands {k r : ℕ} (P : PolynomialSystem k
    r)
    {F : ArithmeticMap k} (hF : ∀ n, 0 ≤ F n) (N : ℕ+) (X w₀ x u : ℝ) (a b : ℤ)
    (hx : 1 < x) (hw₀ : 1 ≤ w₀) :
    ∃ J : Finset ℕ, (∀ j ∈ J, w₀ < x ^ (2 * (u / 2 ^ (j + 1)))) ∧
      P.intermediatePrefixContribution F N X w₀ x u a b ≤
        ∑ j ∈ J, P.smoothTailPrefixContribution F N
          (Finset.Icc 0 ⌊x ^ (2 * (u / 2 ^ (j + 1)))⌋₊) X a b (x ^ (u / 2 ^ (j + 1))) := by
  classical
  let T := (Finset.Ioc a b).filter (P.HasIntermediatePrefix N X w₀ x u)
  apply exists_finset_sum_le_cover T
    (fun j => (Finset.Ioc a b).filter (fun t => P.HasSmoothTailPrefix N (Finset.Icc 0 ⌊x ^ (2 * (u /
      2 ^ (j + 1)))⌋₊)
        X (x ^ (u / 2 ^ (j + 1))) t))
    (fun j => w₀ < x ^ (2 * (u / 2 ^ (j + 1))))
    (fun t => extendArithmeticMap F (fun j => ((P.Q j).eval t).natAbs))
    (fun _ => extendArithmeticMap_nonneg hF _)
  intro t ht
  obtain ⟨j, hj, hprefix⟩ := ((Finset.mem_filter.mp ht).2).exists_band hx hw₀
  exact ⟨j, hj, Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ht).1, hprefix⟩⟩

end NairTenenbaum
