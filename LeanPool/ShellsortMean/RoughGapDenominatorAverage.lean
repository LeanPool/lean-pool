/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.RoughGapFareyGrid
public import LeanPool.ShellsortMean.RoughGapFiniteFourier
public import Mathlib.Analysis.SpecificLimits.Basic

/-! Group repeated rational samples by their actual reduced denominator. -/
@[expose] public noncomputable section
namespace Shellsort.RoughGapDenominatorAverage
open Finset Shellsort.RoughGapFareyGrid

abbrev Fraction := ℕ × ℕ
def mult (p : Fraction) := p.1.gcd p.2
def reduced (p : Fraction) : Fraction := (p.1 / mult p, p.2 / mult p)

def energy {m : ℕ} (start : ℤ) (v : Fin m → ℂ) (p : Fraction) : ℝ :=
  ‖∑ j : Fin m, Complex.exp (-2 * (Real.pi : ℂ) * Complex.I *
    ((start : ℂ) + j.val) * p.1 / p.2) * v j‖ ^ 2

private theorem rep (p : Fraction) :
    (reduced p).1 * mult p = p.1 ∧ (reduced p).2 * mult p = p.2 :=
  ⟨Nat.div_mul_cancel (Nat.gcd_dvd_left ..), Nat.div_mul_cancel (Nat.gcd_dvd_right ..)⟩

private theorem energy_reduced {m : ℕ} (start : ℤ) (v : Fin m → ℂ)
    (p : Fraction) (proper : p.1 < p.2) : energy start v p = energy start v (reduced p) := by
  have d := Nat.gcd_pos_of_pos_right p.1 (Nat.zero_lt_of_lt proper)
  have nz : (mult p : ℂ) ≠ 0 := by exact_mod_cast d.ne'
  have a : ((reduced p).1 : ℂ) * (mult p : ℂ) = p.1 := by exact_mod_cast (rep p).1
  have b : ((reduced p).2 : ℂ) * (mult p : ℂ) = p.2 := by exact_mod_cast (rep p).2
  have term (z : ℂ) : z * p.1 / p.2 = z * (reduced p).1 / (reduced p).2 := by
    rw [←a, ←b, ←mul_assoc, mul_div_mul_right _ _ nz]
  simp only [energy, term]

private theorem same {p t : Fraction} (hp : p.1.Coprime p.2) (ht : t.1.Coprime t.2)
    (pd : 0 < p.2) (eq : p.1 * t.2 = t.1 * p.2) : p = t := by
  have L : p.2 ∣ p.1 * t.2 := eq ▸ dvd_mul_left _ _
  have R : t.2 ∣ t.1 * p.2 := eq ▸ dvd_mul_left _ _
  have hd := Nat.dvd_antisymm (hp.symm.dvd_of_dvd_mul_left L)
    (ht.symm.dvd_of_dvd_mul_left R)
  apply Prod.ext _ hd
  rw [←hd] at eq
  exact Nat.eq_of_mul_eq_mul_right pd eq

/-- The fiber is injected into the scalar multiples 1,...,B/Q. -/
theorem multiplicity (S : Finset Fraction) (u : Fraction) {B Q : ℕ} (hQ : 0 < Q)
    (size : ∀ p ∈ S, p.1 < p.2 ∧ p.2 ≤ B) (hu : Q ≤ u.2) :
    (S.filter (fun p ↦ reduced p = u)).card ≤ B / Q := by
  have key {p : Fraction} (hp : p ∈ S.filter (fun p ↦ reduced p = u)) :
      0 < mult p ∧ u.1 * mult p = p.1 ∧ u.2 * mult p = p.2 ∧ p.2 ≤ B := by
    obtain ⟨hs, hr⟩ := mem_filter.mp hp
    have d := size p hs
    obtain ⟨one, two⟩ := rep p
    rw [hr] at one two
    exact ⟨Nat.gcd_pos_of_pos_right _ (Nat.zero_lt_of_lt d.1), one, two, d.2⟩
  have h : (S.filter (fun p ↦ reduced p = u)).card ≤ (range (B / Q)).card := by
    apply card_le_card_of_injOn (fun p : Fraction ↦ mult p - 1)
    · intro p hp
      have e := key hp
      have bound : mult p ≤ B / Q := (Nat.le_div_iff_mul_le hQ).mpr
        ((Nat.mul_le_mul_left (mult p) hu).trans (by rw [mul_comm, e.2.2.1]; exact e.2.2.2))
      apply mem_range.mpr
      change mult p - 1 < B / Q
      omega
    · intro p hp t ht eq
      have e := key hp
      have f := key ht
      change mult p - 1 = mult t - 1 at eq
      have mt : mult p = mult t := by omega
      apply Prod.ext <;> simp_all
  simpa using h

theorem one_band {m B Q : ℕ} (hQ : 0 < Q) (S : Finset Fraction)
    (size : ∀ p ∈ S, p.1 < p.2 ∧ p.2 ≤ B)
    (band : ∀ p ∈ S, Q ≤ (reduced p).2 ∧ (reduced p).2 ≤ 2 * Q)
    (start : ℤ) (v : Fin m → ℂ) :
    (∑ p ∈ S, energy start v p) ≤
      ((B : ℝ) / Q) * (((2 * (Q : ℝ)) ^ 2 + Real.pi * m) * ∑ j, ‖v j‖ ^ 2) := by
  classical
  let U := S.image reduced
  have key (u : ↥U) : u.val.1 < u.val.2 ∧ u.val.1.Coprime u.val.2 ∧ Q ≤ u.val.2 ∧ u.val.2 ≤ 2 *
    Q := by
    obtain ⟨p, hp, hr⟩ := mem_image.mp u.property
    rw [←hr]
    have d := size p hp
    have gg := Nat.gcd_pos_of_pos_right p.1 (Nat.zero_lt_of_lt d.1)
    exact ⟨(Nat.div_lt_div_right gg.ne' (Nat.gcd_dvd_right ..)).mpr d.1,
      Nat.coprime_div_gcd_div_gcd gg, band p hp⟩
  have sieve := short_interval_sieve (2 * Q) m (by omega) start
    (fun u : ↥U ↦ u.val.1) (fun u ↦ u.val.2)
    (fun u ↦ (key u).1) (fun u ↦ (key u).2.2.2)
    (fun {i j} eq ↦ Subtype.ext (same (key i).2.1 (key j).2.1 (Nat.zero_lt_of_lt (key i).1) eq)) v
  have compressed : (∑ u ∈ U, energy start v u) ≤
      ((2 * (Q : ℝ)) ^ 2 + Real.pi * m) * ∑ j, ‖v j‖ ^ 2 := by
    rw [sum_subtype U (fun _ ↦ Iff.rfl)]
    simpa only [energy, Nat.cast_mul, Nat.cast_ofNat] using sieve
  have sumEq := sum_fiberwise_of_maps_to (g := reduced) (t := U) (s := S)
    (fun p hp ↦ mem_image_of_mem _ hp) (energy start v)
  rw [← sumEq]
  calc
    _ ≤ ∑ u ∈ U, ((B : ℝ) / Q) * energy start v u := by
      apply sum_le_sum
      intro u hu
      have e := key ⟨u, hu⟩
      let A := S.filter (fun p ↦ reduced p = u)
      have inner : (∑ p ∈ A, energy start v p) = ∑ _p ∈ A, energy start v u := by
        apply sum_congr rfl; intro p hp
        obtain ⟨hs, hr⟩ := mem_filter.mp hp
        simpa only [hr] using energy_reduced start v p (size p hs).1
      change ∑ p ∈ A, energy start v p ≤ _
      rw [inner, sum_const, nsmul_eq_mul]
      have card := multiplicity S u hQ size e.2.2.1
      have realBound : (A.card : ℝ) ≤ (B : ℝ) / Q := by
        apply (le_div_iff₀ (by exact_mod_cast hQ)).mpr
        exact_mod_cast (Nat.le_div_iff_mul_le hQ).mp card
      exact mul_le_mul_of_nonneg_right realBound (sq_nonneg _)
    _ = _ := (mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left compressed (by positivity)

/-- All high reduced denominators of an arbitrary finite family of actual
samples, summed with multiplicity. The sample set may contain every numerator
for all permitted moduli or any subfamily. -/
theorem high_denominator_sum {m B D : ℕ} (hD : 0 < D) (hDB : D ≤ B)
    (S : Finset Fraction) (size : ∀ p ∈ S, p.1 < p.2 ∧ p.2 ≤ B)
    (high : ∀ p ∈ S, D ≤ (reduced p).2) (start : ℤ) (v : Fin m → ℂ) :
    (∑ p ∈ S, energy start v p) ≤
      B * (8 * (B : ℝ) + 2 * Real.pi * m / D) * (∑ j, ‖v j‖ ^ 2) := by
  classical
  let K := fun (p : Fraction) ↦ ((reduced p).2 / D).log2
  let T := (B / D).log2 + 1
  let Q (k : ℕ) := 2 ^ k * D
  let E := ∑ j, ‖v j‖ ^ 2
  have pref (p : Fraction) (hp : p ∈ S) :
      K p < T ∧ Q (K p) ≤ (reduced p).2 ∧ (reduced p).2 < 2 * Q (K p) := by
    let d := (reduced p).2
    have A : 0 < d / D := Nat.div_pos (high p hp) hD
    have Bp : d ≤ B := (Nat.div_le_self ..).trans (size p hp).2
    have bpos : 0 < B / D := Nat.div_pos hDB hD
    have qlow := Nat.log2_self_le A.ne'
    have low : Q (K p) ≤ d := (Nat.le_div_iff_mul_le hD).mp qlow
    have up := (Nat.div_lt_iff_lt_mul hD).mp (Nat.lt_log2_self (n := d / D))
    have index : (d / D).log2 ≤ (B / D).log2 := (Nat.le_log2 bpos.ne').mpr
      (qlow.trans (Nat.div_le_div_right Bp))
    exact ⟨Nat.lt_succ_of_le index, low, by simpa [Q, K, d, pow_succ, mul_assoc, mul_comm,
      mul_left_comm] using up⟩
  have split := sum_fiberwise_of_maps_to (g := K) (t := range T) (s := S)
    (fun p hp ↦ mem_range.mpr (pref p hp).1) (energy start v)
  have group (k : ℕ) :
      (∑ p ∈ S.filter (fun p ↦ K p = k), energy start v p) ≤
      ((B : ℝ) * (4 * (Q k : ℝ)) + ((B : ℝ) * Real.pi * m / D) * (1 / (2 : ℝ)) ^ k) * E := by
    have pos : 0 < Q k := Nat.mul_pos (pow_pos (by decide) _) hD
    have use := one_band pos (S.filter (fun p ↦ K p = k))
      (fun p hp ↦ size p (mem_filter.mp hp).1) (B := B)
      (fun p hp ↦ by
        obtain ⟨h, ek⟩ := mem_filter.mp hp
        rw [←ek]
        exact ⟨(pref p h).2.1, (pref p h).2.2.le⟩) start v
    apply use.trans_eq
    dsimp [Q, E]
    push_cast
    simp only [div_pow, one_pow]
    field_simp; ring
  have tBound : (2 : ℕ) ^ T * D ≤ 2 * B := by
    have bpos := Nat.div_pos hDB hD
    have a := (Nat.le_div_iff_mul_le hD).mp (Nat.log2_self_le bpos.ne')
    dsimp [T]; rw [pow_succ]
    nlinarith
  have sa : (∑ k ∈ range T, (Q k : ℝ)) ≤ 2 * B := by
    have geom (t : ℕ) : ∑ k ∈ range t, (2 : ℝ) ^ k = 2 ^ t - 1 := by
      induction t with
      | zero => simp
      | succ t ih => rw [sum_range_succ, ih, pow_succ]; ring
    simp only [Q, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, ← sum_mul, geom]
    have tb : (2 : ℝ) ^ T * D ≤ 2 * B := by exact_mod_cast tBound
    nlinarith
  rw [←split]
  apply (sum_le_sum (s := range T) (fun k _ ↦ group k)).trans
  rw [←sum_mul, sum_add_distrib, ←mul_sum, ←mul_sum, ←mul_sum]
  have s2 := sum_geometric_two_le T
  apply mul_le_mul_of_nonneg_right _ (by dsimp [E]; positivity)
  have b0 : 0 ≤ (B : ℝ) := by positivity
  have b1 : 0 ≤ (B : ℝ) * Real.pi * m / D := by positivity
  have t1 : 4 * (∑ k ∈ range T, (Q k : ℝ)) ≤ 4 * (2 * B : ℝ) := by gcongr
  have one := mul_le_mul_of_nonneg_left t1 b0
  have two := mul_le_mul_of_nonneg_left s2 b1
  calc
    _ ≤ _ := add_le_add one two
    _ = B * (8 * (B : ℝ) + 2 * Real.pi * m / D) := by ring

/-- Normalization by at least δH moduli and the upper cutoff B=2H.
This directly matches the high-frequency term of the block estimate. -/
theorem high_denominator_mean {m H D : ℕ} (hD : 0 < D) (hDH : D ≤ 2 * H)
    (S : Finset Fraction) (size : ∀ p ∈ S, p.1 < p.2 ∧ p.2 ≤ 2 * H)
    (high : ∀ p ∈ S, D ≤ (reduced p).2) (start : ℤ) (v : Fin m → ℂ)
    (weight δ : ℝ) (hδ : 0 < δ) (large : δ * H ≤ weight) :
    (∑ p ∈ S, energy start v p) / weight ≤
      (32 * H + 4 * Real.pi * m / D) / δ * (∑ j, ‖v j‖ ^ 2) := by
  have hp : 0 < H := by omega
  have hpr : 0 < (H : ℝ) := by exact_mod_cast hp
  have wpos := (mul_pos hδ hpr).trans_le large
  have bound := high_denominator_sum hD hDH S size high start v
  push_cast at bound
  apply (div_le_iff₀ wpos).mpr
  have z : 0 ≤ (32 * (H : ℝ) + 4 * Real.pi * m / D) / δ * (∑ j, ‖v j‖ ^ 2) := by positivity
  apply bound.trans
  apply le_trans _ (mul_le_mul_of_nonneg_left large z)
  field_simp; ring_nf; rfl





end Shellsort.RoughGapDenominatorAverage
