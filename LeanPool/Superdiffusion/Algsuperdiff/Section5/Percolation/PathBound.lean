/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Percolation.LargeScale

/-!
# PathBound

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The multiscale percolation path bound

This file counts the crossing paths of a given vertex length, absorbs that
count into the fixed-path exponent, and sums over lengths to obtain the path
clause of the general percolation estimate.
-/

namespace Algsuperdiff.Section5.Percolation

open MeasureTheory ProbabilityTheory
open HCPolySupport.IndependentSums
open scoped BigOperators

private theorem cast_card_pathsOfLength_le_exp {d k n : ℕ}
    (hkn : 3 ^ k ≤ n) :
    ((pathsOfLength d k n).card : ℝ) ≤
      Real.exp (4 * ((d : ℝ) + 1) * n) := by
  have hcardNat := card_pathsOfLength_le d k n
  have hcard : ((pathsOfLength d k n).card : ℝ) ≤
      (3 : ℝ) ^ (d * k) * ((3 : ℝ) ^ d) ^ n := by
    exact_mod_cast hcardNat
  have hthree : (3 : ℝ) ≤ Real.exp 2 := by
    have hexp := Real.add_one_le_exp (2 : ℝ)
    norm_num at hexp ⊢
    exact hexp
  have hfirst : (3 : ℝ) ^ (d * k) ≤
      Real.exp (((d * k : ℕ) : ℝ) * 2) := by
    calc
      (3 : ℝ) ^ (d * k) ≤ (Real.exp 2) ^ (d * k) :=
        pow_le_pow_left₀ (by norm_num) hthree _
      _ = Real.exp (((d * k : ℕ) : ℝ) * 2) := by
        rw [← Real.exp_nat_mul]
  have hsecond : ((3 : ℝ) ^ d) ^ n ≤
      Real.exp (((d * n : ℕ) : ℝ) * 2) := by
    rw [← pow_mul]
    calc
      (3 : ℝ) ^ (d * n) ≤ (Real.exp 2) ^ (d * n) :=
        pow_le_pow_left₀ (by norm_num) hthree _
      _ = Real.exp (((d * n : ℕ) : ℝ) * 2) := by
        rw [← Real.exp_nat_mul]
  have hk3 : k ≤ 3 ^ k := by
    have h := two_mul_le_three_pow k
    omega
  have hkn' : k ≤ n := hk3.trans hkn
  have hdkdn : d * k ≤ d * n := Nat.mul_le_mul_left d hkn'
  have hexponent : (((d * k : ℕ) : ℝ) * 2) +
      ((d * n : ℕ) : ℝ) * 2 ≤ 4 * ((d : ℝ) + 1) * n := by
    have hcast : ((d * k : ℕ) : ℝ) ≤ (d * n : ℕ) := by exact_mod_cast hdkdn
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    calc
      ((d * k : ℕ) : ℝ) * 2 + ((d * n : ℕ) : ℝ) * 2 ≤
          ((d * n : ℕ) : ℝ) * 2 + ((d * n : ℕ) : ℝ) * 2 :=
        add_le_add (mul_le_mul_of_nonneg_right hcast (by norm_num)) le_rfl
      _ = 4 * (d : ℝ) * n := by push_cast; ring
      _ ≤ 4 * ((d : ℝ) + 1) * n := by
        have hdle : (d : ℝ) ≤ d + 1 := by linarith only [hd0]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hdle (by norm_num)) hn0
  calc
    ((pathsOfLength d k n).card : ℝ) ≤
        (3 : ℝ) ^ (d * k) * ((3 : ℝ) ^ d) ^ n := hcard
    _ ≤ Real.exp (((d * k : ℕ) : ℝ) * 2) * ((3 : ℝ) ^ d) ^ n :=
      mul_le_mul_of_nonneg_right hfirst (by positivity)
    _ ≤ Real.exp (((d * k : ℕ) : ℝ) * 2) *
          Real.exp (((d * n : ℕ) : ℝ) * 2) :=
      mul_le_mul_of_nonneg_left hsecond (Real.exp_pos _).le
    _ = Real.exp ((((d * k : ℕ) : ℝ) * 2) +
          ((d * n : ℕ) : ℝ) * 2) := by rw [Real.exp_add]
    _ ≤ Real.exp (4 * ((d : ℝ) + 1) * n) :=
      Real.exp_le_exp.mpr hexponent

/-- The event that a path of the prescribed length meets the weighted bad-cube threshold. -/
noncomputable def fixedLengthWeightedPathEvent
    {Ω : Type*} {d : ℕ} (B : ℕ → Site d → Set Ω)
    (lam : ℝ) (k n : ℕ) : Set Ω := by
  classical
  exact ⋃ Γ ∈ pathsOfLength d k n,
    if IsPath Γ then weightedCubeEvent B Γ (lam * n / 2) else ∅

private theorem measureReal_fixedLengthWeightedPathEvent_le
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℕ → Site d → Set Ω) (a T lam : ℝ)
    (hBmeas : ∀ L z, MeasurableSet (B L z))
    (hsep : SepIndep P B)
    (hBtail : ∀ L z,
      P.real (B L z) ≤ Real.exp (-(T ^ 2 * (3 : ℝ) ^ (a * L))))
    (ha : 1 < a) (had : a ≤ d) (hTone : 1 ≤ T)
    (hlam : 0 < lam) (hlamOne : lam < 1)
    (hgate : pathBoundGateConst d * lam⁻¹ * (a - 1)⁻¹ ≤ T)
    (k n : ℕ) (hkn : 3 ^ k ≤ n) (hnpos : 0 < n)
    (hentropy : 8 * ((d : ℝ) + 1) ≤
      fixedPathRateConst d * ((a - 1) * T * lam) ^ 2) :
    P.real (fixedLengthWeightedPathEvent B lam k n) ≤
      Real.exp (-(pathLengthRateConst d *
        ((a - 1) * T * lam) ^ 2 * n)) := by
  classical
  let R : ℝ := fixedPathRateConst d * ((a - 1) * T * lam) ^ 2
  have hpath : ∀ Γ ∈ pathsOfLength d k n,
      P.real (if IsPath Γ then weightedCubeEvent B Γ (lam * n / 2) else ∅) ≤
        Real.exp (-(R * n)) := by
    intro Γ hΓmem
    split_ifs with hΓ
    · have hlen := length_eq_of_mem_pathsOfLength hΓmem
      have htail := measureReal_weightedCubeEvent_le_fixedPath
        P B a T lam hBmeas hsep hBtail ha had hTone hlam hlamOne hgate
          Γ hΓ (by omega)
      simpa only [hlen, R, mul_assoc] using htail
    · simp only [measureReal_empty]
      exact (Real.exp_pos _).le
  have hcount := cast_card_pathsOfLength_le_exp (d := d) (k := k) hkn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hentropyN : 4 * ((d : ℝ) + 1) * n ≤ R * n / 2 := by
    dsimp only [R]
    have hhalf : 4 * ((d : ℝ) + 1) ≤
        fixedPathRateConst d * ((a - 1) * T * lam) ^ 2 / 2 := by
      linarith only [hentropy]
    calc
      4 * ((d : ℝ) + 1) * n ≤
          (fixedPathRateConst d * ((a - 1) * T * lam) ^ 2 / 2) * n :=
        mul_le_mul_of_nonneg_right hhalf hn0
      _ = (fixedPathRateConst d * ((a - 1) * T * lam) ^ 2) * n / 2 := by ring
  rw [fixedLengthWeightedPathEvent]
  calc
    P.real (⋃ Γ ∈ pathsOfLength d k n,
        if IsPath Γ then weightedCubeEvent B Γ (lam * n / 2) else ∅) ≤
        ∑ Γ ∈ pathsOfLength d k n,
          P.real (if IsPath Γ then
            weightedCubeEvent B Γ (lam * n / 2) else ∅) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _Γ ∈ pathsOfLength d k n, Real.exp (-(R * n)) :=
      Finset.sum_le_sum hpath
    _ = ((pathsOfLength d k n).card : ℝ) * Real.exp (-(R * n)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ Real.exp (4 * ((d : ℝ) + 1) * n) * Real.exp (-(R * n)) :=
      mul_le_mul_of_nonneg_right hcount (Real.exp_pos _).le
    _ = Real.exp (4 * ((d : ℝ) + 1) * n - R * n) := by
      rw [← Real.exp_add]
      congr 1
    _ ≤ Real.exp (-(R * n / 2)) := by
      rw [Real.exp_le_exp]
      linarith only [hentropyN]
    _ = Real.exp (-(pathLengthRateConst d *
        ((a - 1) * T * lam) ^ 2 * n)) := by
      unfold pathLengthRateConst
      dsimp only [R]
      congr 1
      ring

private theorem lightPathEvent_subset_fixedLength_union
    {Ω : Type*} {d : ℕ} (B : ℕ → Site d → Set Ω)
    {lam : ℝ} (hlamOne : lam < 1) (k : ℕ) :
    lightPathEvent B lam k ⊆
      ⋃ m : ℕ, fixedLengthWeightedPathEvent B lam k (3 ^ k + m) := by
  classical
  intro ω hω
  obtain ⟨Δ, hΔ, hgood⟩ := hω
  obtain ⟨Γ, hΓ⟩ := exists_preferredPath B ω ⟨Δ, hΔ⟩
  have hlower : 3 ^ k ≤ Γ.length :=
    (Nat.le_add_right (3 ^ k) 1).trans hΓ.1.length_lower_bound
  let m := Γ.length - 3 ^ k
  have hlen : Γ.length = 3 ^ k + m := by
    dsimp only [m]
    omega
  have hweighted :=
    hΓ.mem_weightedCubeEvent_of_competitor_goodVertexCount_lt hΔ hlen hgood
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hthreshold : lam * (3 ^ k + m) / 2 ≤ (lam * 3 ^ k + m) / 2 := by
    have hlamLe : lam * (m : ℝ) ≤ m := by
      have := mul_le_mul_of_nonneg_right hlamOne.le hm0
      simpa only [one_mul] using this
    linarith only [hlamLe]
  obtain ⟨scales, hmass⟩ := hweighted
  have hweightedSmall :
      ω ∈ weightedCubeEvent B Γ (lam * (3 ^ k + m) / 2) :=
    ⟨scales, hthreshold.trans_lt hmass⟩
  apply Set.mem_iUnion.mpr
  refine ⟨m, ?_⟩
  rw [fixedLengthWeightedPathEvent]
  apply Set.mem_iUnion.mpr
  refine ⟨Γ, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
  · rw [← hlen]
    exact hΓ.1.mem_pathsOfLength
  · have hΓpath : IsPath Γ := by
      cases Γ with
      | nil => exact False.elim hΓ.1
      | cons x xs => exact hΓ.1.1
    rw [ite_eq_left hΓpath]
    simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat] using hweightedSmall

/-- The path clause of the general percolation estimate, as stated in the
pinned manuscript, lines 14222--14233. Only the path clause is formalized
here; the density and maximal-diameter clauses are not asserted.

The source's independence across scales is not assumed: the path clause uses
only the separation hypothesis, through the colouring of a single scale.
`ScaleIndep` remains available for the density and maximal-diameter clauses.

The hypothesis `a ≤ d` is load-bearing.  The scale summation
`∑_L 3 ^ ((1 - a) * L / 2) ≤ C * (a - 1)⁻¹` behind the small-scale estimate is
not uniform in `a`: the geometric tail factor `(1 - 3 ^ (-(a - 1) / 2))⁻¹`
tends to `1` as `a` grows, so no bound of that shape holds with a
dimension-free constant.  Under `1 < a ≤ d` the factor is at most
`2 * (d + 1) * (a - 1)⁻¹`, which is the form used here. -/
theorem path_bound (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : ℕ → Site d → Set Ω) (a T lam : ℝ) (k : ℕ),
        (∀ L z, MeasurableSet (B L z)) → SepIndep P B →
        (∀ L z, P.real (B L z) ≤
          Real.exp (-(T ^ 2 * (3 : ℝ) ^ (a * L)))) →
        1 < a → a ≤ d → 1 ≤ T → 0 < lam → lam < 1 →
        C * lam⁻¹ * (a - 1)⁻¹ ≤ T →
      P.real {ω | ∃ Γ : List (Site d), IsPathFrom k Γ ∧
          ∑ z ∈ Γ.toFinset,
            (badSet B z)ᶜ.indicator (fun _ => (1 : ℝ)) ω <
              (1 - lam) * 3 ^ k}
        ≤ Real.exp (-(c * (a - 1) ^ 2 * T ^ 2 * lam ^ 2 * 3 ^ k)) := by
  refine ⟨pathBoundGateConst d, pathBoundGateConst_pos d,
    pathBoundRateConst d, pathBoundRateConst_pos d, ?_⟩
  intro Ω _ P _ B a T lam k hBmeas hsep hBtail ha had hTone
    hlam hlamOne hgate
  change P.real (lightPathEvent B lam k) ≤ _
  let q : ℝ := (a - 1) * T * lam
  let R : ℝ := pathLengthRateConst d * q ^ 2
  let N : ℕ := 3 ^ k
  let E : ℕ → Set Ω := fun m => fixedLengthWeightedPathEvent B lam k (N + m)
  have hentropy := entropy_le_fixedPathRate_of_gate ha hlam hgate
  have hRfour : 4 ≤ R := by
    have hdOne : (1 : ℝ) ≤ d + 1 := by norm_num
    dsimp only [R, q, pathLengthRateConst]
    nlinarith only [hentropy, hdOne]
  have hRpos : 0 < R := zero_lt_four.trans_le hRfour
  have hNpos : 0 < N := by dsimp only [N]; positivity
  have hNOne : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
  have hterm : ∀ m, P.real (E m) ≤ Real.exp (-(R * (N + m))) := by
    intro m
    have hbound := measureReal_fixedLengthWeightedPathEvent_le
      P B a T lam hBmeas hsep hBtail ha had hTone hlam hlamOne hgate
        k (N + m) (by dsimp only [N]; omega) (by omega) hentropy
    simpa only [E, N, R, q, Nat.cast_add, mul_assoc] using hbound
  have hsubset : lightPathEvent B lam k ⊆ ⋃ m, E m := by
    simpa only [E, N] using lightPathEvent_subset_fixedLength_union B hlamOne k
  have hr0 : 0 ≤ Real.exp (-R) := (Real.exp_pos _).le
  have hrLt : Real.exp (-R) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith only [hRpos])
  have hexpR : (2 : ℝ) ≤ Real.exp R := by
    have hexp := Real.add_one_le_exp R
    linarith only [hexp, hRfour]
  have hrHalf : Real.exp (-R) ≤ 1 / 2 := by
    rw [Real.exp_neg]
    have hinv := inv_anti₀ (by norm_num : (0 : ℝ) < 2) hexpR
    norm_num at hinv ⊢
    exact hinv
  have hsummable : Summable fun m : ℕ =>
      Real.exp (-(R * N)) * Real.exp (-R) ^ m :=
    (summable_geometric_of_lt_one hr0 hrLt).mul_left _
  have htermEq : ∀ m : ℕ, Real.exp (-(R * (N + m))) =
      Real.exp (-(R * N)) * Real.exp (-R) ^ m := by
    intro m
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  have hsum : ∑' m : ℕ,
      Real.exp (-(R * N)) * Real.exp (-R) ^ m =
        Real.exp (-(R * N)) * (1 - Real.exp (-R))⁻¹ := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hrLt]
  let S : ℝ := Real.exp (-(R * N)) * (1 - Real.exp (-R))⁻¹
  have hS0 : 0 ≤ S := by
    dsimp only [S]
    have hden : 0 < 1 - Real.exp (-R) := by linarith only [hrLt]
    exact mul_nonneg (Real.exp_pos _).le (inv_nonneg.mpr hden.le)
  have hmeasure : P (lightPathEvent B lam k) ≤ ENNReal.ofReal S := by
    apply (measure_mono hsubset).trans
    rw [show S = ∑' m : ℕ,
        Real.exp (-(R * N)) * Real.exp (-R) ^ m by
      exact hsum.symm]
    rw [ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) hsummable]
    refine (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun m => ?_)
    rw [← ENNReal.ofReal_toReal (measure_ne_top P (E m))]
    apply ENNReal.ofReal_le_ofReal
    rw [← htermEq]
    exact hterm m
  have hden : 1 / 2 ≤ 1 - Real.exp (-R) := by
    linarith only [hrHalf]
  have hdenInv : (1 - Real.exp (-R))⁻¹ ≤ 2 := by
    have hinv := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) hden
    norm_num at hinv ⊢
    exact hinv
  have hRNtwo : 2 ≤ R * N / 2 := by
    have hRN : 4 ≤ R * N := by
      calc
        (4 : ℝ) = 4 * 1 := by ring
        _ ≤ R * N := mul_le_mul hRfour hNOne (by norm_num) hRpos.le
    linarith only [hRN]
  have htwoExp : (2 : ℝ) ≤ Real.exp (R * N / 2) := by
    have htwo : (2 : ℝ) ≤ Real.exp 1 := Real.exp_one_gt_d9.le.trans' (by norm_num)
    exact htwo.trans (Real.exp_le_exp.mpr (by linarith only [hRNtwo]))
  calc
    P.real (lightPathEvent B lam k) = (P (lightPathEvent B lam k)).toReal := rfl
    _ ≤ (ENNReal.ofReal S).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hmeasure
    _ = S := ENNReal.toReal_ofReal hS0
    _ ≤ 2 * Real.exp (-(R * N)) := by
      dsimp only [S]
      calc
        Real.exp (-(R * N)) * (1 - Real.exp (-R))⁻¹ ≤
            Real.exp (-(R * N)) * 2 :=
          mul_le_mul_of_nonneg_left hdenInv (Real.exp_pos _).le
        _ = 2 * Real.exp (-(R * N)) := by ring
    _ ≤ Real.exp (R * N / 2) * Real.exp (-(R * N)) :=
      mul_le_mul_of_nonneg_right htwoExp (Real.exp_pos _).le
    _ = Real.exp (-(R * N / 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ = Real.exp (-(pathBoundRateConst d * (a - 1) ^ 2 * T ^ 2 *
        lam ^ 2 * 3 ^ k)) := by
      dsimp only [R, q, N, pathBoundRateConst]
      congr 1
      rw [Nat.cast_pow, Nat.cast_ofNat]
      ring

end Algsuperdiff.Section5.Percolation
