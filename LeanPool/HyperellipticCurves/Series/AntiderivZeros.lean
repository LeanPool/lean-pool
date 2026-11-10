/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.ForMathlib.LocalRing
public import LeanPool.HyperellipticCurves.Series.Strassmann

import LeanPool.HyperellipticCurves.ForMathlib.PadicValNat

/-!
# Zeros of antiderivatives of power series

Let `O` be a local ring with uniformizer `π`, residue characteristic `p` and absolute
ramification index at most `e < p - 1` (`IsLocalRing.IsUniformizer`), let `w ∈ O⟦X⟧` have a
unit coefficient in degree `m`, and let `G = c + ∑ (bₖ/(k+1)) z^(k+1)` be an antiderivative
of `w` (over the fraction field). The substitution `z = π·u` produces a series `H` with
coefficients in `O`, characterized without any division by
`(k+1)·coeff (k+1) H = π^(k+1)·coeff k w`; this is how `H` enters the Lean statements, and
`ChabautyColeman.PSeries.exists_substituted_antideriv` constructs it — integrality is that
`k+1` divides `π^(k+1)` in `O`, which is where the ramification bound is spent
(`IsLocalRing.IsUniformizer.natCast_dvd_pow`).
If `p > m + e + 1` then `H` has at most `m + 1` zeros in `O`
(`ChabautyColeman.PSeries.antideriv_zeros_le`, with finiteness
`ChabautyColeman.PSeries.antideriv_zeros_finite`) — hence `G` has at most `m + 1` zeros
in `𝔪`, via the injection `z = π·u`. (Constant terms `c` of negative valuation give
`G` without zeros in `𝔪`, so restricting to `c ∈ O` — forced here by `H ∈ O⟦X⟧` —
loses nothing.)

The coefficient of `H` in degree `k + 1` is divisible by `π^(k+1-e·v_p(k+1))`
(`ChabautyColeman.PSeries.pow_dvd_coeff_antideriv`); by the index-valuation inequality
(`Nat.add_mul_padicValNat_lt`) these exponents exceed `m + 1` beyond degree `m + 1`, while
in degree `m + 1` the valuation is exactly `m + 1`. Dividing by the minimal power of `π`
therefore yields a series with unit content and top unit index at most `m + 1`, to which
Strassmann's theorem applies.

Blueprint nodes: `lem:padic-index`, `thm:antideriv-zeros`.
-/

@[expose] public section

open PowerSeries IsLocalRing Filter Topology

namespace ChabautyColeman

namespace PSeries

section scaling

variable {O : Type*} [CommRing O] [UniformSpace O] [IsLocalRing O]
  [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O] [CompleteSpace O] [T2Space O]
  [IsTopologicalRing O] [IsDomain O]

-- multiplying by a nonzero constant does not change the zero set
private lemma setOf_evalT_eq {H H' : O⟦X⟧} {a : O} (ha : a ≠ 0)
    (hcoeff : ∀ i, coeff i H = a * coeff i H')
    (hdec : Tendsto (fun k ↦ coeff k H') atTop (𝓝 0)) :
    {u : O | evalT u H = 0} = {u : O | evalT u H' = 0} := by
  ext u
  simp only [Set.mem_ofPred_eq]
  have hsum : Summable fun k ↦ coeff k H' * u ^ k := summable_mul_of_tendsto_zero hdec
  have hkey : evalT u H = a * evalT u H' := by
    rw [evalT_eq_tsum, evalT_eq_tsum, ← hsum.tsum_mul_left]
    exact tsum_congr fun k ↦ by rw [hcoeff k]; ring
  rw [hkey, mul_eq_zero, or_iff_right ha]

end scaling

variable {O : Type*} [CommRing O] [IsLocalRing O]
  {π : O} {p e : ℕ} (hram : IsUniformizer π p e) (hpe : e + 1 < p)

include hram

include hpe in
/-- **The substituted antiderivative exists over `O`**: the series `H` with `H(0) = 0` and
`(k+1)·H_{k+1} = π^{k+1}·W_k`, i.e. `H(u) = G(π·u)` for `G` the antiderivative of `W` over
the fraction field, has coefficients in `O`. -/
theorem exists_substituted_antideriv (W : O⟦X⟧) :
    ∃ H : O⟦X⟧, constantCoeff H = 0 ∧
      ∀ k : ℕ, ((k : O) + 1) * coeff (k + 1) H = π ^ (k + 1) * coeff k W := by
  have hdvd (k : ℕ) : ((k : O) + 1) ∣ π ^ (k + 1) * coeff k W := by
    have hev : e * padicValNat p (k + 1) ≤ k + 1 := by lia [Nat.mul_padicValNat_le hpe (k + 1)]
    have hcast : ((k : O) + 1) = ((k + 1 : ℕ) : O) := by push_cast; ring
    exact hcast ▸ (hram.natCast_dvd_pow k.succ_ne_zero hev).mul_right _
  choose c hc using hdvd
  exact ⟨mk fun n ↦ if n = 0 then 0 else c (n - 1), by simp, fun k ↦ by simpa using (hc k).symm⟩

variable [IsDomain O] [CharZero O] {w H : O⟦X⟧} {m : ℕ}
  (hH : ∀ k : ℕ, ((k : O) + 1) * coeff (k + 1) H = π ^ (k + 1) * coeff k w)

include hH

/-- The coefficient of `H` at index `m + 1` is not divisible by `π ^ (m + 2)`, i.e. its
`π`-adic valuation is at most `m + 1`, when `w` has a unit coefficient in degree `m`. The
matching lower bound is `pow_dvd_coeff_antideriv`, which gives valuation exactly `m + 1` only
under the extra assumption `m + 1 < p`; that is not assumed here. -/
lemma not_pow_dvd_coeff_antideriv (hmu : IsUnit (coeff m w)) :
    ¬ π ^ (m + 2) ∣ coeff (m + 1) H := by
  intro hdvd
  obtain ⟨y, hy⟩ := hdvd
  have hπne : π ^ (m + 1) ≠ 0 := pow_ne_zero _ hram.ne_zero
  have hcancel : coeff m w = π * (((m + 1 : ℕ) : O) * y) := by
    refine mul_left_cancel₀ hπne ?_
    calc π ^ (m + 1) * coeff m w = ((m : O) + 1) * coeff (m + 1) H := (hH m).symm
      _ = ((m : O) + 1) * (π ^ (m + 2) * y) := by rw [hy]
      _ = π ^ (m + 1) * (π * (((m + 1 : ℕ) : O) * y)) := by push_cast; ring
  exact hram.isUnit_iff_not_dvd.mp hmu ⟨_, hcancel⟩

include hpe in
/-- The key divisibility: the substituted antiderivative coefficient at index `k + 1`
is divisible by `π^(k + 1 - e·v_p(k + 1))`. -/
lemma pow_dvd_coeff_antideriv (k : ℕ) :
    π ^ (k + 1 - e * padicValNat p (k + 1)) ∣ coeff (k + 1) H := by
  obtain ⟨u, hu⟩ := exists_units_natCast_eq hram.prime hram.natCast_mem k.succ_ne_zero
  set v := padicValNat p (k + 1)
  obtain ⟨c, hcmem, hc⟩ := hram.exists_pow_eq (v := v) (k := k + 1)
    (by lia [Nat.mul_padicValNat_le hpe (k + 1)])
  have h1 : ((k : O) + 1) = (p : O) ^ v * u := by rw [← hu]; push_cast; ring
  have hpne : (p : O) ^ v ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hram.prime.ne_zero)
  have hcancel : (u : O) * coeff (k + 1) H = c * coeff k w :=
    mul_left_cancel₀ hpne (by rw [← mul_assoc, ← mul_assoc, ← h1, ← hc]; exact hH k)
  obtain ⟨y, hy⟩ := hram.mem_pow_iff.mp hcmem
  refine ⟨(↑u⁻¹ : O) * (y * coeff k w), ?_⟩
  linear_combination (↑u⁻¹ : O) * hcancel + (↑u⁻¹ : O) * coeff k w * hy
    - coeff (k + 1) H * u.inv_mul

variable [UniformSpace O] [Fact (IsAdic (maximalIdeal O))]

include hpe in
/-- Coefficient decay of the substituted antiderivative. -/
lemma tendsto_coeff_antideriv : Tendsto (fun k ↦ coeff k H) atTop (𝓝 0) := by
  rw [(Fact.out : IsAdic (maximalIdeal O)).hasBasis_nhds_zero.tendsto_right_iff]
  intro M _
  rw [eventually_atTop]
  refine ⟨(e + 2) * M + 1, fun k hk ↦ ?_⟩
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by lia⟩
  rw [SetLike.mem_coe, hram.mem_pow_iff]
  refine (pow_dvd_pow _ ?_).trans (pow_dvd_coeff_antideriv hram hpe hH k')
  lia [Nat.add_mul_padicValNat_le hpe (B := M) (n := k' + 1) (by lia)]

omit hH [CharZero O] in
/-- Coefficient decay descends along division by `π ^ s`. -/
lemma tendsto_coeff_of_mul (hπ : π ≠ 0) {H₁ H₂ : O⟦X⟧} {s : ℕ}
    (hcoeff : ∀ i, coeff i H₁ = π ^ s * coeff i H₂)
    (hdec : Tendsto (fun k ↦ coeff k H₁) atTop (𝓝 0)) :
    Tendsto (fun k ↦ coeff k H₂) atTop (𝓝 0) := by
  rw [(Fact.out : IsAdic (maximalIdeal O)).hasBasis_nhds_zero.tendsto_right_iff] at hdec ⊢
  intro M _
  filter_upwards [hdec (M + s) trivial] with k hk
  rw [SetLike.mem_coe, hram.mem_pow_iff] at hk ⊢
  obtain ⟨y, hy⟩ := hk
  rw [hcoeff k, show M + s = s + M by lia, pow_add, mul_assoc] at hy
  exact ⟨y, mul_left_cancel₀ (pow_ne_zero s hπ) hy⟩

/-- Normalization: dividing the substituted antiderivative by the minimal power of `π`
yields a series with unit content and top unit index at most `m + 1`. -/
private lemma exists_normalized (hpm : m + e + 1 < p) (hmu : IsUnit (coeff m w)) :
    ∃ (H' : O⟦X⟧) (s N : ℕ), (∀ i, coeff i H = π ^ s * coeff i H') ∧ N ≤ m + 1 ∧
      IsUnit (coeff N H') ∧ (∀ k, N < k → coeff k H' ∈ maximalIdeal O) ∧
      Tendsto (fun k ↦ coeff k H') atTop (𝓝 0) := by
  classical
  have hpe : e + 1 < p := by lia
  have hπ0 : π ≠ 0 := hram.ne_zero
  set P : ℕ → Prop := fun n ↦ ∃ i, ¬ π ^ (n + 1) ∣ coeff i H with hP
  have hPm1 : P (m + 1) := ⟨m + 1, not_pow_dvd_coeff_antideriv hram hH hmu⟩
  have hPex : ∃ n, P n := ⟨m + 1, hPm1⟩
  set s := Nat.find hPex
  have hsle : s ≤ m + 1 := Nat.find_le hPm1
  have hall (i : ℕ) : π ^ s ∣ coeff i H := by
    rcases Nat.eq_zero_or_pos s with h0 | h1
    · simp [h0]
    · have hmin := Nat.find_min hPex (show s - 1 < s by lia)
      rw [hP] at hmin
      push Not at hmin
      have := hmin i
      rwa [show s - 1 + 1 = s by lia] at this
  set H' : O⟦X⟧ := PowerSeries.mk fun i ↦ (hall i).choose with hH'
  have hcoeff (i : ℕ) : coeff i H = π ^ s * coeff i H' := by
    rw [hH', coeff_mk]
    exact (hall i).choose_spec
  -- the unit criterion for the normalized coefficients
  have hcrit (i : ℕ) : IsUnit (coeff i H') ↔ ¬ π ^ (s + 1) ∣ coeff i H := by
    rw [hcoeff i, pow_succ, mul_dvd_mul_iff_left (pow_ne_zero s hπ0)]
    exact hram.isUnit_iff_not_dvd
  -- indices beyond `m + 1` are non-units after normalization
  have hbig (k : ℕ) (hk : m + 1 < k) : π ^ (s + 1) ∣ coeff k H := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by lia⟩
    refine (pow_dvd_pow _ ?_).trans (pow_dvd_coeff_antideriv hram hpe hH k')
    lia [Nat.add_mul_padicValNat_lt (m := m) (e := e) (k := k') hpm (by lia)]
  obtain ⟨i₀, hi₀⟩ : P s := Nat.find_spec hPex
  have hi₀m : i₀ ≤ m + 1 := by
    by_contra hgt
    exact hi₀ ((pow_dvd_pow _ le_rfl).trans (hbig i₀ (by lia)))
  set N := Nat.findGreatest (fun i ↦ IsUnit (coeff i H')) (m + 1)
  refine ⟨H', s, N, hcoeff, Nat.findGreatest_le _, ?_, ?_, ?_⟩
  · exact Nat.findGreatest_spec (P := fun i ↦ IsUnit (coeff i H')) hi₀m ((hcrit i₀).mpr hi₀)
  · intro k hk
    by_cases hkle : k ≤ m + 1
    · have := Nat.findGreatest_is_greatest (P := fun i ↦ IsUnit (coeff i H')) hk hkle
      exact (IsLocalRing.mem_maximalIdeal _).mpr this
    · exact (IsLocalRing.mem_maximalIdeal _).mpr fun hu ↦ ((hcrit k).mp hu)
        (hbig k (by lia))
  · exact tendsto_coeff_of_mul hram hπ0 hcoeff (tendsto_coeff_antideriv hram hpe hH)

variable [IsUniformAddGroup O] [CompleteSpace O] [T2Space O] [IsTopologicalRing O]

/-- The zero set of the substituted antiderivative is finite. -/
theorem antideriv_zeros_finite (hpm : m + e + 1 < p) (hmu : IsUnit (coeff m w)) :
    {u : O | evalT u H = 0}.Finite := by
  obtain ⟨H', s, N, hcoeff, -, hNu, hN, hdec⟩ := exists_normalized hram hH hpm hmu
  rw [setOf_evalT_eq (pow_ne_zero s hram.ne_zero) hcoeff hdec]
  exact strassmann_finite hdec hNu hN

/-- Antiderivative zero count: if `w` has a unit coefficient in degree `m`,
`p > m + e + 1`, and `H` is the substituted antiderivative of `w` (characterized by
`(k+1)·coeff (k+1) H = π^(k+1)·coeff k w`, i.e. `H(u) = G(π·u)` for an antiderivative
`G` of `w`), then `H` has at most `m + 1` zeros in `O`. -/
theorem antideriv_zeros_le (hpm : m + e + 1 < p) (hmu : IsUnit (coeff m w)) :
    {u : O | evalT u H = 0}.ncard ≤ m + 1 := by
  obtain ⟨H', s, N, hcoeff, hNle, hNu, hN, hdec⟩ := exists_normalized hram hH hpm hmu
  rw [setOf_evalT_eq (pow_ne_zero s hram.ne_zero) hcoeff hdec]
  exact (strassmann hdec hNu hN).trans hNle

end PSeries

end ChabautyColeman

end
