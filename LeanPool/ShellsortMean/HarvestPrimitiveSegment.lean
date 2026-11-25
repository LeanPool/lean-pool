/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.HarvestProjectedFar
public import LeanPool.ShellsortMean.Actual214PhysicalLowGrid
public import Mathlib.Algebra.Order.Chebyshev

/-! Sum the energy of an entire primitive-denominator packet on one
signed chain segment. -/
@[expose] public noncomputable section
namespace Shellsort.HarvestPrimitiveSegment
open Finset ZMod HarvestProjectedFar Actual214
open scoped ComplexConjugate

/-- The geometric sum for consecutive powers along a gap progression on the frequency grid. -/
def segment (d g a b : ℕ) : ℂ :=
  ∑ j ∈ range b, (((negGridRoot d) ^ a) ^ g) ^ j

private theorem segment_coeff {d : ℕ} [NeZero d] (g a b : ℕ) :
    segment d g a b =
      coeff (fun i : Fin b => g * i.val) (fun _ => 1) (a : ZMod d) := by
  rw [coeff_exp]
  unfold segment
  rw [← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro i _
  simp only [mul_one, negGridRoot, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private theorem truncate {d g a : ℕ} (hd : 0 < d) (ha : a.Coprime d) (off : ¬ d ∣ g)
    (b : ℕ) : segment d g a b = segment d g a (b % (d / d.gcd g)) := by
  let w := ((negGridRoot d) ^ a) ^ g
  have prim := ((negGridRoot_primitive hd).pow_of_coprime a ha).pow_div_gcd g
    (Nat.gcd_pos_of_pos_left g hd).ne'
  have nz : w ≠ 1 := fun e => off (((negGridRoot_primitive hd).pow_of_coprime a
    ha).dvd_of_pow_eq_one g e)
  have eqpow : w ^ (b % (d / d.gcd g)) = w ^ b := by
    calc
      _ = w ^ (b % (d / d.gcd g)) * ((w ^ (d / d.gcd g)) ^ (b / (d / d.gcd g))) := by
        rw [prim.pow_eq_one]
        simp
      _ = _ := by rw [← pow_mul w (d / d.gcd g), ←pow_add, Nat.mod_add_div]
  apply mul_right_cancel₀ (sub_ne_zero.mpr nz) (b := w - 1)
  change (∑ j ∈ range b, w ^ j) * (w - 1) = (∑ j ∈ range _, w ^ j) * (w - 1)
  rw [geom_sum_mul, geom_sum_mul, eqpow]

/-- Orthogonality on an interval shorter than or equal to the step period.
No primitivity requirement is imposed on the grid index here. -/
theorem short_full_grid {d g b : ℕ} [NeZero d] (hb : b ≤ d / d.gcd g) :
    (∑ a ∈ range d, ‖segment d g a b‖ ^ 2) = (d : ℝ) * b := by
  let loc (i : Fin b) := g * i.val
  let X (a : ℕ) := coeff loc (fun _ => (1 : ℂ)) (a : ZMod d)
  have inj {i j : Fin b} (eq : (loc i : ZMod d) = (loc j : ZMod d)) : i = j := by
    have m := (natCast_eq_natCast_iff _ _ _).mp eq
    have t := Nat.ModEq.cancel_left_div_gcd (NeZero.pos d) (show g * i.val ≡ g * j.val [MOD d]
      from m)
    exact Fin.ext (t.eq_of_lt_of_lt (lt_of_lt_of_le i.isLt hb) (lt_of_lt_of_le j.isLt hb))
  have kernel (i : Fin b) : (∑ a ∈ range d, X a * stdAddChar ((loc i : ZMod d) * (a : ZMod d))) =
      (d : ℂ) := by
    rw [show (∑ a ∈ range d, X a * stdAddChar ((loc i : ZMod d) * (a : ZMod d))) =
        _ from full_kernel loc (fun _ => (1 : ℂ)) (loc i)]
    have eq (j : Fin b) : (loc j : ZMod d) = (loc i : ZMod d) ↔ j = i := ⟨inj, fun z => z ▸ rfl⟩
    simp [eq]
  have cv (a : ℕ) : conj (X a) = ∑ j, stdAddChar ((loc j : ZMod d) * (a : ZMod d)) := by
    simp [X, coeff, FiniteFourier.stdAddChar_conj_neg]
  have whole : (∑ a ∈ range d, X a * conj (X a)) = (d : ℂ) * b := by
    simp_rw [cv, mul_sum]
    rw [sum_comm]
    simp_rw [kernel]
    simp [mul_comm]
  apply Complex.ofReal_injective
  push_cast
  simp_rw [Complex.mul_conj, ← Complex.sq_norm] at whole
  simpa only [X, loc, segment_coeff, Complex.ofReal_pow] using whole

/-- All primitive frequencies at denominator d together cost at most d times
the residual segment length. The stride may have a nontrivial gcd with d. -/
theorem primitive_segment_energy {d g : ℕ} (hd : 0 < d) (off : ¬d ∣ g) (b : ℕ) :
    (∑ a ∈ (range d).filter (fun a => a.Coprime d), ‖segment d g a b‖ ^ 2) ≤
      (d : ℝ) * (b % (d / d.gcd g) : ℕ) := by
  let : NeZero d := ⟨hd.ne'⟩
  have hp : 0 < d / d.gcd g := Nat.div_pos (Nat.gcd_le_left g hd) (Nat.gcd_pos_of_pos_left g hd)
  rw [← short_full_grid (g := g) (Nat.mod_lt b hp).le]
  calc
    _ = ∑ a ∈ (range d).filter (fun a => a.Coprime d), ‖segment d g a (b % (d / d.gcd g))‖ ^ 2 :=
      sum_congr rfl (fun a ha => by rw [truncate hd (mem_filter.mp ha).2 off b])
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset ..) (by intros; positivity)



/-- Complex phases include the start and sign of each chain's discrepancy
segment. They may depend arbitrarily on the numerator. -/
theorem primitive_chain_packet {d g : ℕ} (hd : 0 < d) (off : ¬d ∣ g)
    (b : Fin g → ℕ) (phase : Fin g → ℕ → ℂ) (unit : ∀ r a, ‖phase r a‖ ≤ 1) :
    (∑ a ∈ (range d).filter (fun a => a.Coprime d),
      ‖∑ r, phase r a * segment d g a (b r)‖ ^ 2) ≤
      ((g : ℝ) * d)*∑ r, (b r : ℝ) := by
  let S := (range d).filter (fun a => a.Coprime d)
  have each (a : ℕ) : ‖∑ r, phase r a * segment d g a (b r)‖ ^ 2 ≤
      (g : ℝ) * ∑ r, ‖segment d g a (b r)‖ ^ 2 := by
    have triangle := norm_sum_le (univ : Finset (Fin g)) (fun r => phase r a * segment d g a (b r))
    have bound : ‖∑ r, phase r a * segment d g a (b r)‖ ≤ ∑ r, ‖segment d g a (b r)‖ := by
      apply triangle.trans
      apply sum_le_sum
      intro r _
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (unit r a)
    exact (pow_le_pow_left₀ (norm_nonneg _) bound 2).trans
      (by simpa using sq_sum_le_card_mul_sum_sq (s := univ) (f := fun r => ‖segment d g a (b r)‖))
  apply (sum_le_sum (s := S) (fun a _ => each a)).trans
  rw [←mul_sum, sum_comm, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [mul_sum]
  apply sum_le_sum
  intro r _
  exact (primitive_segment_energy hd off (b r)).trans
    (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.mod_le (b r) (d / d.gcd g)) (by positivity))


private def segLength (a b : ℕ) := if a ≤ b then b - a else a - b
private def segPhase (a b : ℕ) (w : ℂ) := if a ≤ b then w ^ a else - (w ^ b)

private theorem seg_num (a b : ℕ) (w : ℂ) :
    (segPhase a b w * ∑ i ∈ range (segLength a b), w ^ i) * (w - 1) =
      w ^ b - w ^ a := by
  rw [mul_assoc, geom_sum_mul]
  by_cases hab : a ≤ b
  · simp only [segPhase, segLength, hab, ite_true]
    rw [mul_sub, ← pow_add, Nat.add_sub_of_le hab, mul_one]
  · simp only [segPhase, segLength, hab, ite_false, neg_mul, mul_sub, ← pow_add,
      Nat.add_sub_of_le (Nat.le_of_not_ge hab), mul_one]
    ring

open RoughGapEndpoint in
/-- Packet on the actual threshold state after an ordinary pass; the mass is
the output mass of that same pass. -/
theorem primitive_after_gap {n d g : ℕ} (p : RankPlacement n) (T : ℕ) (hT : T ≤ n)
    (hg : 0 < g) (hd : 0 < d) (off : ¬d ∣ g) :
    (∑ a ∈ (range d).filter (fun a => a.Coprime d),
      ‖amplitude (gapSort p g) T ((negGridRoot d) ^ a)‖ ^ 2) ≤
      ((g : ℝ) * d)*∑ i, |(slotError (gapSort p g) T i : ℝ)| := by
  let A (r : Fin g) := residuePrefixCount g r.val T
  let B (r : Fin g) := chainLowerCount (thresholdSet p T) g r.val
  let L (r : Fin g) := segLength (A r) (B r)
  let z (a : ℕ) := (negGridRoot d) ^ a
  let phase (r : Fin g) (a : ℕ) := (z a) ^ r.val * segPhase (A r) (B r) ((z a) ^ g)
  have unit (r : Fin g) (a : ℕ) : ‖phase r a‖ ≤ 1 := by
    have hu : ‖z a‖ = 1 := by simp [z, norm_pow, (negGridRoot_primitive hd).norm'_eq_one hd.ne']
    by_cases hb : A r ≤ B r <;> simp [phase, segPhase, hb, norm_pow, hu]
  have eq (a : ℕ) (ha : a.Coprime d) :
      amplitude (gapSort p g) T (z a) = ∑ r, phase r a * segment d g a (L r) := by
    have hp := (negGridRoot_primitive hd).pow_of_coprime a ha
    apply mul_right_cancel₀ (b := (z a) ^ g - 1) (sub_ne_zero.mpr (fun e => off
      (hp.dvd_of_pow_eq_one g e)))
    rw [gapSort_amplitude_numerator p T hT hg, sum_mul]
    apply sum_congr rfl
    intro r _
    symm
    change ((z a ^ r.val * segPhase (A r) (B r) ((z a) ^ g)) *
      (∑ i ∈ range (segLength (A r) (B r)), ((z a) ^ g) ^ i)) * ((z a) ^ g - 1) =
      z a ^ r.val * (((z a) ^ g) ^ (B r) - ((z a) ^ g) ^ (A r))
    simpa only [mul_assoc] using congrArg (fun x : ℂ => z a ^ r.val * x) (seg_num (A r) (B r) ((z
      a) ^ g))
  have Lmass : ∑ r, (L r : ℝ) = ∑ i, |(slotError (gapSort p g) T i : ℝ)| := by
    have e := gapSort_abs_error_exact p T hT hg
    have er : ∑ i, |(slotError (gapSort p g) T i : ℝ)| = ∑ r : Fin g, |(residueError p g T
      r.val : ℝ)| := by
      exact_mod_cast e
    rw [er]
    apply sum_congr rfl
    intro r _
    change (segLength (A r) (B r) : ℝ) = |(((B r : ℤ) - (A r : ℤ) : ℤ) : ℝ)|
    by_cases le : A r ≤ B r
    · simp [segLength, le, Nat.cast_sub le, abs_of_nonneg (sub_nonneg.mpr (show (A r : ℝ) ≤ B
      r by exact_mod_cast le))]
    · have ba := Nat.le_of_not_ge le
      simp [segLength, le, Nat.cast_sub ba, abs_of_nonpos (sub_nonpos.mpr (show (B r : ℝ) ≤ A
        r by exact_mod_cast ba))]
  rw [←Lmass]
  calc
    _ = ∑ a ∈ (range d).filter (fun a => a.Coprime d), ‖∑ r, phase r a * segment d g a (L r)‖ ^ 2 :=
      sum_congr rfl (fun a ha => by rw [←eq a (mem_filter.mp ha).2])
    _ ≤ _ := primitive_chain_packet hd off L phase unit


open RoughGapEndpoint in
private theorem mass_after_gap {n g : ℕ} (p : RankPlacement n) (T : ℕ) (hT : T ≤ n) (hg : 0 < g) :
    (∑ i, |(slotError (gapSort p g) T i : ℝ)|) ≤ ∑ i, |(slotError p T i : ℝ)| := by
  have hm := (gapSort_abs_error_exact p T hT hg).trans_le (sum_abs_residueError_le p T hT hg)
  exact_mod_cast hm

open RoughGapEndpoint in
/-- The genuine two-retained-pass packet, uniformly charged to the state
before either pass. A later divisible gap preserves every mode of this packet. -/
theorem primitive_after_retained {n d g₁ g₂ : ℕ} (p : RankPlacement n) (T : ℕ) (hT : T ≤ n)
    (hg : 0 < g₂) (hle : g₂ ≤ g₁) (hd : 0 < d) (off : ¬d ∣ g₁ ∨ ¬d ∣ g₂) :
    (∑ a ∈ (range d).filter (fun a => a.Coprime d),
      ‖amplitude (gapSort (gapSort p g₁) g₂) T ((negGridRoot d) ^ a)‖ ^ 2) ≤
      ((g₁ : ℝ) * d)*∑ i, |(slotError p T i : ℝ)| := by
  have hg₁ := lt_of_lt_of_le hg hle
  have m₁ := mass_after_gap p T hT hg₁
  by_cases div₂ : d ∣ g₂
  · have stable (a : ℕ) : amplitude (gapSort (gapSort p g₁) g₂) T ((negGridRoot d) ^ a) =
        amplitude (gapSort p g₁) T ((negGridRoot d) ^ a) := by
      have unity : ((negGridRoot d) ^ a) ^ d = 1 := by
        rw [←pow_mul, Nat.mul_comm, pow_mul, (negGridRoot_primitive hd).pow_eq_one, one_pow]
      exact divisible_word_amplitude (gapSort p g₁) [g₂] (by simpa using div₂) T hT hd _ unity
    simp_rw [stable]
    exact (primitive_after_gap p T hT hg₁ hd (off.resolve_right (not_not_intro div₂))).trans
      (mul_le_mul_of_nonneg_left m₁ (by positivity))
  · apply (primitive_after_gap (gapSort p g₁) T hT hg hd div₂).trans
    have m₂ := (mass_after_gap (gapSort p g₁) T hT hg).trans m₁
    gcongr

end Shellsort.HarvestPrimitiveSegment
