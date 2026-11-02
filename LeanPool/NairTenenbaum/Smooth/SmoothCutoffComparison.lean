/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Smooth.PrimeBandBounds

/-! # Comparison of two smoothness cutoffs

Splitting off all primes above the smaller cutoff is injective. The dagger
conditions supply the cross-coprimality needed by the arithmetic majorant, and
the removed part is bounded by the prime-band Euler product.
-/

@[expose] public section

namespace NairTenenbaum

open Polynomial Finset

/-- A finite positive-integer sum embeds in the corresponding smooth series. -/
theorem sum_positive_factored_le_tsum {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (s : Finset ℕ)
    (hs : Summable (fun n : Nat.factoredNumbers s => f n)) (T : Finset ℕ+)
    (hT : ∀ n ∈ T, (n : ℕ) ∈ Nat.factoredNumbers s) :
    (∑ n ∈ T, f n) ≤ ∑' n : Nat.factoredNumbers s, f n := by
  classical
  let e : {n : ℕ+ // n ∈ T} → Nat.factoredNumbers s := fun n => ⟨n.1, hT n.1 n.2⟩
  have he : Function.Injective e := by
    intro n m h
    apply Subtype.ext
    exact PNat.coe_injective
      (show (n.1 : ℕ) = (m.1 : ℕ) from congrArg (fun x : Nat.factoredNumbers s => (x : ℕ)) h)
  have hb := hs.sum_le_tsum (T.attach.image e) (fun n _ => hf n)
  rw [Finset.sum_image (fun n _ m _ h => he h)] at hb
  change (∑ n ∈ T.attach, f (n.1 : ℕ)) ≤ _ at hb
  rw [Finset.sum_attach T (fun n : ℕ+ => f (n : ℕ))] at hb
  exact hb

theorem rootAuxiliary_sum_le_product {A B ε : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hε : 0 < ε) (γ : ℕ) (hγ : (γ : ℝ) * ε < 1) (Q : ℤ[X])
    (C : ℕ) (hρ : ∀ p, p.Prime → ∀ ν, rootCount Q (p ^ ν) ≤ C)
    (s : Finset ℕ) (T : Finset ℕ+) (hT : ∀ n ∈ T, (n : ℕ) ∈ Nat.factoredNumbers s) :
    (∑ n ∈ T, rootAuxiliary A B ε γ Q n) ≤
      ∏ p ∈ s.filter Nat.Prime, ∑' ν : ℕ, rootAuxiliary A B ε γ Q (p ^ ν) := by
  have H := rootAuxiliary_smooth_hasSum hA hB hε γ hγ Q C hρ s
  exact (sum_positive_factored_le_tsum (rootAuxiliary_nonneg hA (zero_le_one.trans hB) γ Q)
    s H.summable T hT).trans_eq H.tsum_eq

theorem weightedMass_unitaryPart_le {k r : ℕ} (γ : Fin k → Fin r → ℕ)
    (n : Tuple r) (t : Fin r → Finset ℕ) : weightedMass γ (tupleUnitaryPart n t) ≤ weightedMass γ
        n := by
  have h := Nat.le_mul_of_pos_right (weightedMass γ (tupleUnitaryPart n t))
    (weightedMass_pos γ (tupleUnitaryRest n t))
  rwa [← weightedMass_mul, tupleUnitaryPart_mul_rest] at h

/-- Selecting primes in a set always produces an integer factored over that set. -/
theorem unitaryPart_mem_factoredNumbers (n : ℕ+) (s : Finset ℕ) :
    (unitaryPart n s : ℕ) ∈ Nat.factoredNumbers s := by
  apply Nat.mem_factoredNumbers_of_primeFactors_subset (unitaryPart n s).ne_zero
  rw [unitaryPart_primeFactors]
  exact Finset.inter_subset_right

/-- The complement to the smaller smooth part has every prime in the band. -/
theorem unitaryRest_mem_primeBand {w z : ℝ} (hw : 0 ≤ w) {n : ℕ+}
    (hn : (n : ℕ) ∈ Nat.factoredNumbers (Finset.Icc 0 ⌊z⌋₊)) :
    (unitaryRest n (Finset.Icc 0 ⌊w⌋₊) : ℕ) ∈ Nat.factoredNumbers (primeBandNumbers w z) := by
  apply Nat.mem_factoredNumbers_of_primeFactors_subset (unitaryRest n _).ne_zero
  intro p hp
  rw [unitaryRest, primeFactors_primeReject] at hp
  obtain ⟨hpn, hpw⟩ := Finset.mem_sdiff.mp hp
  apply Finset.mem_filter.mpr
  refine ⟨Nat.primeFactors_subset_of_mem_factoredNumbers hn hpn, ?_⟩
  exact lt_of_not_ge (fun h => hpw (Finset.mem_Icc.mpr ⟨Nat.zero_le p, (Nat.le_floor_iff hw).mpr
      h⟩))

/-- Shrinking the smoothness cutoff costs only the Euler product over the
removed band. The finite weighted-mass bound remains unchanged. -/
theorem smoothWeightUpTo_cutoff_le_product {k r : ℕ} {A B ε w z : ℝ} {F : ArithmeticMap k}
    (hF : Admissible A B ε F) (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε) (hw : 0 ≤ w)
    (γ : Fin k → Fin r → ℕ) (hγ : ∀ i, 0 < totalExponent γ i)
    (hγε : ∀ i, (totalExponent γ i : ℝ) * ε < 1) (Q : Fin r → ℤ[X])
    (C : Fin r → ℕ) (hρ : ∀ i p, p.Prime → ∀ ν, rootCount (Q i) (p ^ ν) ≤ C i)
    (D : ℕ) (N : ℕ+) :
    (∑ n ∈ smoothWeightUpTo γ D (Finset.Icc 0 ⌊z⌋₊) N, rootTupleWeight γ F Q n) ≤
      (∏ i, ∏ p ∈ (primeBandNumbers w z).filter Nat.Prime,
        ∑' ν : ℕ, rootAuxiliary A B ε (totalExponent γ i) (Q i) (p ^ ν)) *
          ∑ n ∈ smoothWeightUpTo γ D (Finset.Icc 0 ⌊w⌋₊) N, rootTupleWeight γ F Q n := by
  classical
  let S := smoothWeightUpTo γ D (Finset.Icc 0 ⌊z⌋₊) N
  let W := smoothWeightUpTo γ D (Finset.Icc 0 ⌊w⌋₊) N
  let t := fun _ : Fin r => Finset.Icc 0 ⌊w⌋₊
  let T := (Finset.Icc 1 N).filter (fun n : ℕ+ => (n : ℕ) ∈ Nat.factoredNumbers (primeBandNumbers
      w z))
  let f : Tuple r → Tuple r × Tuple r := fun n => (tupleUnitaryRest n t, tupleUnitaryPart n t)
  have hfmem : ∀ n ∈ S, f n ∈ Fintype.piFinset (fun _ : Fin r => T) ×ˢ W := by
    intro n hn
    obtain ⟨⟨hmass, hd⟩, hs⟩ := (mem_smoothWeightUpTo γ hγ D _ N n).mp hn
    apply Finset.mem_product.mpr
    constructor
    · apply Fintype.mem_piFinset.mpr
      intro i
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨one_le,
        (unitaryRest_le _ _).trans (weightUpTo_coordinate_le γ D N (Finset.mem_filter.mp hn).1 i)⟩,
        unitaryRest_mem_primeBand hw (hs i)⟩
    · apply (mem_smoothWeightUpTo γ hγ D _ N _).mpr
      exact ⟨⟨(weightedMass_unitaryPart_le γ n t).trans hmass, hd.of_tupleUnitaryPart t⟩,
        fun i => unitaryPart_mem_factoredNumbers (n i) _⟩
  have hfinj : Function.Injective f := by
    intro n m h
    have hb := congrArg Prod.fst h
    have ha := congrArg Prod.snd h
    rw [← tupleUnitaryPart_mul_rest n t, ← tupleUnitaryPart_mul_rest m t]
    exact congrArg₂ (· * ·) ha hb
  have hbound : ∀ n ∈ S, rootTupleWeight γ F Q n ≤
      (∏ i, rootAuxiliary A B ε (totalExponent γ i) (Q i) ((f n).1 i)) *
        rootTupleWeight γ F Q (f n).2 := by
    intro n hn
    have hd := ((mem_smoothWeightUpTo γ hγ D _ N n).mp hn).1.2
    have H := hF.rootTupleWeight_mul_le hA hB γ Q
      (tupleUnitaryRest n t) (tupleUnitaryPart n t)
      (fun i j => (hd.unitary_cross_coprime t j i).symm)
    simpa only [mul_comm (tupleUnitaryRest n t), tupleUnitaryPart_mul_rest] using H
  calc
    _ ≤ ∑ x ∈ Fintype.piFinset (fun _ : Fin r => T) ×ˢ W,
        (∏ i, rootAuxiliary A B ε (totalExponent γ i) (Q i) (x.1 i)) * rootTupleWeight γ F Q x.2 :=
      Finset.sum_le_sum_of_injOn f hfinj.injOn (Finset.image_subset_iff.mpr hfmem) hbound
        (fun x _ _ => mul_nonneg (Finset.prod_nonneg (fun i _ =>
          rootAuxiliary_nonneg hA (zero_le_one.trans hB) _ _ _)) (rootTupleWeight_nonneg γ
              hF.nonneg Q _))
    _ = (∏ i, ∑ a ∈ T, rootAuxiliary A B ε (totalExponent γ i) (Q i) a) *
        ∑ n ∈ W, rootTupleWeight γ F Q n := by
      rw [Finset.sum_product]
      dsimp only
      rw [← Finset.sum_mul_sum]
      congr 1
      exact (Finset.prod_univ_sum (fun _ : Fin r => T)
        (fun i a => rootAuxiliary A B ε (totalExponent γ i) (Q i) a)).symm
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _
        (Finset.sum_nonneg (fun n _ => rootTupleWeight_nonneg γ hF.nonneg Q n))
      apply Finset.prod_le_prod₀
      · intro i _
        exact Finset.sum_nonneg (fun n _ => rootAuxiliary_nonneg hA (zero_le_one.trans hB) _ _ _)
      · intro i _
        exact rootAuxiliary_sum_le_product hA hB hε _ (hγε i) _ (C i) (hρ i)
          (primeBandNumbers w z) T (fun n hn => (Finset.mem_filter.mp hn).2)

/-- A uniform comparison between two smoothness cutoffs with bounded logarithm
ratio, including the weighted-mass bound and all dagger restrictions. -/
theorem smoothWeightUpTo_cutoff_uniform {k r : ℕ} {A B ε σ L w z : ℝ} {F : ArithmeticMap k}
    (hF : Admissible A B ε F) (hA : 0 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε) (hσ : σ < 1 / 2)
    (hw : 2 ≤ w) (hz : 2 ≤ z) (hlog : Real.log z / Real.log w ≤ L)
    (γ : Fin k → Fin r → ℕ) (hγ : ∀ i, 0 < totalExponent γ i)
    (hγε : ∀ i, (totalExponent γ i : ℝ) * ε ≤ σ) (Q : Fin r → ℤ[X])
    (C : Fin r → ℕ) (hρ : ∀ i p, p.Prime → ∀ ν, rootCount (Q i) (p ^ ν) ≤ C i)
    (D : ℕ) (N : ℕ+) :
    (∑ n ∈ smoothWeightUpTo γ D (Finset.Icc 0 ⌊z⌋₊) N, rootTupleWeight γ F Q n) ≤
      (∏ i, primeBandBound A B σ L (totalExponent γ i) (C i)) *
        ∑ n ∈ smoothWeightUpTo γ D (Finset.Icc 0 ⌊w⌋₊) N, rootTupleWeight γ F Q n := by
  refine (smoothWeightUpTo_cutoff_le_product (z := z) hF hA hB hε (show 0 ≤ w by linarith) γ hγ
    (fun i => (hγε i).trans_lt (by linarith)) Q C hρ D N).trans ?_
  apply mul_le_mul_of_nonneg_right _
    (Finset.sum_nonneg (fun n _ => rootTupleWeight_nonneg γ hF.nonneg Q n))
  apply Finset.prod_le_prod₀
  · intro i _
    exact Finset.prod_nonneg (fun p _ => tsum_nonneg
      (fun _ => rootAuxiliary_nonneg hA (zero_le_one.trans hB) _ _ _))
  · intro i _
    exact rootAuxiliary_primeBand_product_le hA hB hε hσ hw hz hlog _ (hγε i) _ (C i) (hρ i)

end NairTenenbaum
