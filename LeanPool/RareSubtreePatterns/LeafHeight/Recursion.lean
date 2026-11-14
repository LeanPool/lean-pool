/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Bienayme.Defs

/-!
# The root leaf-height recursion

Section 7 of the paper (source lines 2911–2958). For an offspring law `μ`, put
`g(x) = ∑_{j ≥ 1} μ_j x^j = G_μ(x) - μ_0` and define `π_0 = 1`, `π_{k+1} = g(π_k)`.
For the Bienaymé tree, `π_k = P(λ_∅(𝒯) ≥ k)` (this identification is proved separately);
here `π_k` is the purely analytic sequence (inventory item U10).

The paper sets `π_k = 1` for `k ≤ 0`; this convention is encoded by `piSeqZ`, indexed by `ℤ`.

We also define `κ = min{j ≥ 1 : μ_j > 0}` (source lines 2913 and 3031) and prove the basic
two-sided bound `μ_κ x^κ ≤ g(x) ≤ μ_κ x^κ + x^{κ+1}` on `[0, 1]`, together with
`g(x) ≤ (1 - μ_0) x`. For a critical `μ` with `μ_1 ≠ 1`, these give that `π_k` is positive,
strictly decreasing and tends to zero (item (a) of the analysis of Lemma `lem:ell_asymp`).
-/

@[expose] public section

open Filter Topology
open scoped ENNReal

namespace PoissonDeclumping
namespace LeafHeight

variable (μ : PMF ℕ)

/-- The real offspring mass `μ_j`. -/
noncomputable def mass (j : ℕ) : ℝ := (μ j).toReal

/-- The function `g(x) = ∑_{j ≥ 1} μ_j x^j` of the proof of Lemma `lem:ell_asymp`. -/
noncomputable def g (x : ℝ) : ℝ := ∑' j : ℕ, mass μ (j + 1) * x ^ (j + 1)

/-- The sequence `π_0 = 1`, `π_{k+1} = g(π_k)`. For a Bienaymé tree it is the tail
`P(λ_∅(𝒯) ≥ k)` of the root leaf-height. -/
noncomputable def piSeq : ℕ → ℝ
  | 0 => 1
  | k + 1 => g μ (piSeq k)

/-- The paper's convention `π_k = 1` for `k ≤ 0`, as an integer-indexed sequence. -/
noncomputable def piSeqZ (k : ℤ) : ℝ := piSeq μ k.toNat

/-- `ℓ_k = π_k - π_{k+1}`, which is `P(λ_∅(𝒯) = k)` for a Bienaymé tree. -/
noncomputable def ellSeq (k : ℕ) : ℝ := piSeq μ k - piSeq μ (k + 1)

/-- `κ = min{j ≥ 1 : μ_j > 0}` (source lines 2913, 3031). -/
noncomputable def kappa : ℕ := sInf {j : ℕ | 1 ≤ j ∧ 0 < μ j}

variable {μ}

@[simp] theorem piSeq_zero : piSeq μ 0 = 1 := rfl

theorem piSeq_succ (k : ℕ) : piSeq μ (k + 1) = g μ (piSeq μ k) := rfl

theorem piSeqZ_natCast (k : ℕ) : piSeqZ μ k = piSeq μ k := by
  simp [piSeqZ]

theorem piSeqZ_of_nonpos {k : ℤ} (hk : k ≤ 0) : piSeqZ μ k = 1 := by
  simp [piSeqZ, Int.toNat_eq_zero.mpr hk]

/-! ### Real masses -/

theorem mass_nonneg (j : ℕ) : 0 ≤ mass μ j := ENNReal.toReal_nonneg

theorem mass_le_one (j : ℕ) : mass μ j ≤ 1 := by
  have := ENNReal.toReal_mono ENNReal.one_ne_top (μ.coe_le_one j)
  simpa [mass] using this

theorem mass_pos_iff (j : ℕ) : 0 < mass μ j ↔ 0 < μ j := by
  simp [mass, ENNReal.toReal_pos_iff, μ.apply_lt_top j]

theorem hasSum_mass : HasSum (mass μ) 1 := by
  have hs := ENNReal.summable_toReal μ.tsum_coe_ne_top
  have h := hs.hasSum
  rwa [← ENNReal.tsum_toReal_eq (fun a => μ.apply_ne_top a), μ.tsum_coe,
    ENNReal.toReal_one] at h

theorem summable_mass : Summable (mass μ) := hasSum_mass.summable

theorem tsum_mass : ∑' j, mass μ j = 1 := hasSum_mass.tsum_eq

/-- The mean of `μ`, in real numbers, for a critical law. -/
theorem hasSum_mean (hc : IsCritical μ) : HasSum (fun j : ℕ => (j : ℝ) * mass μ j) 1 := by
  have hne : ∀ j : ℕ, (j : ℝ≥0∞) * μ j ≠ ∞ := fun j =>
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top j) (μ.apply_ne_top j)
  have hs := ENNReal.summable_toReal (f := fun j : ℕ => (j : ℝ≥0∞) * μ j)
    (by rw [show (∑' j : ℕ, (j : ℝ≥0∞) * μ j) = 1 from hc]; exact ENNReal.one_ne_top)
  have h := hs.hasSum
  rw [← ENNReal.tsum_toReal_eq hne, show (∑' j : ℕ, (j : ℝ≥0∞) * μ j) = 1 from hc,
    ENNReal.toReal_one] at h
  simpa [mass, ENNReal.toReal_mul] using h

/-- A critical law with `μ_1 ≠ 1` charges some `j ≥ 2`. -/
theorem exists_two_le_pos (hc : IsCritical μ) (h1 : μ 1 ≠ 1) : ∃ j, 2 ≤ j ∧ 0 < μ j := by
  by_contra! h
  apply h1
  have hc' : ∑' j : ℕ, (j : ℝ≥0∞) * μ j = 1 := hc
  rw [tsum_eq_single 1] at hc'
  · simpa using hc'
  · intro j hj
    rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · have : j = 0 := by omega
      simp [this]
    · simp [nonpos_iff_eq_zero.mp (h j hj2)]

/-- A critical law with `μ_1 ≠ 1` has `μ_0 > 0`. -/
theorem mass_zero_pos (hc : IsCritical μ) (h1 : μ 1 ≠ 1) : 0 < mass μ 0 := by
  obtain ⟨j, hj, hjpos⟩ := exists_two_le_pos hc h1
  have hdiff : HasSum (fun i : ℕ => (i : ℝ) * mass μ i - mass μ i) 0 := by
    simpa using (hasSum_mean hc).sub hasSum_mass
  have htail := (hasSum_nat_add_iff' 1).mpr hdiff
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_mul, zero_sub,
    sub_neg_eq_add, zero_add, Nat.cast_add, Nat.cast_one] at htail
  have hle := le_hasSum htail (j - 1) (fun i _ => by
    have := mass_nonneg (μ := μ) (i + 1)
    nlinarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)])
  have hj' : ((j - 1 : ℕ) : ℝ) + 1 = j := by
    rw [Nat.cast_sub (by omega)]; simp
  have hm : 0 < mass μ j := (mass_pos_iff j).mpr hjpos
  have hj2 : (2 : ℝ) ≤ j := by exact_mod_cast hj
  rw [show j - 1 + 1 = j by omega, hj'] at hle
  nlinarith

theorem mass_zero_le_one : mass μ 0 ≤ 1 := mass_le_one 0

/-! ### The index `κ` -/

theorem kappa_mem (hc : IsCritical μ) (h1 : μ 1 ≠ 1) :
    1 ≤ kappa μ ∧ 0 < μ (kappa μ) := by
  obtain ⟨j, hj, hjpos⟩ := exists_two_le_pos hc h1
  exact Nat.sInf_mem (s := {j : ℕ | 1 ≤ j ∧ 0 < μ j}) ⟨j, by omega, hjpos⟩

theorem one_le_kappa (hc : IsCritical μ) (h1 : μ 1 ≠ 1) : 1 ≤ kappa μ :=
  (kappa_mem hc h1).1

theorem mass_kappa_pos (hc : IsCritical μ) (h1 : μ 1 ≠ 1) : 0 < mass μ (kappa μ) :=
  (mass_pos_iff _).mpr (kappa_mem hc h1).2

theorem mass_eq_zero_of_lt_kappa {j : ℕ} (hj : 1 ≤ j) (hjk : j < kappa μ) :
    mass μ j = 0 := by
  have := Nat.notMem_of_lt_sInf hjk
  simp only [Set.mem_ofPred_eq, not_and, not_lt, nonpos_iff_eq_zero] at this
  simp [mass, this hj]

theorem kappa_eq_one (hpos : 0 < μ 1) : kappa μ = 1 :=
  le_antisymm (Nat.sInf_le ⟨le_rfl, hpos⟩)
    (by
      by_contra! h
      have h0 : kappa μ = 0 := by omega
      have hne : ({j : ℕ | 1 ≤ j ∧ 0 < μ j}).Nonempty := ⟨1, le_rfl, hpos⟩
      have := Nat.sInf_mem hne
      rw [show sInf {j : ℕ | 1 ≤ j ∧ 0 < μ j} = kappa μ from rfl, h0] at this
      exact absurd this.1 (by omega))

theorem two_le_kappa (hc : IsCritical μ) (h1 : μ 1 ≠ 1) (h0 : μ 1 = 0) : 2 ≤ kappa μ := by
  obtain ⟨hk, hkpos⟩ := kappa_mem hc h1
  by_contra! h
  have : kappa μ = 1 := by omega
  rw [this, h0] at hkpos
  exact lt_irrefl _ hkpos

/-- When `μ_1 = 0`, `κ` is the index `min{j ≥ 2 : μ_j > 0}` of Theorem `thm:max_lh`(ii). -/
theorem kappa_eq_sInf_two (h0 : μ 1 = 0) : kappa μ = sInf {j : ℕ | 2 ≤ j ∧ 0 < μ j} := by
  unfold kappa
  congr 1
  ext j
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hj, hjpos⟩
    refine ⟨?_, hjpos⟩
    by_contra! h
    have : j = 1 := by omega
    rw [this, h0] at hjpos
    exact lt_irrefl _ hjpos
  · rintro ⟨hj, hjpos⟩
    exact ⟨by omega, hjpos⟩

/-! ### Bounds on `g` -/

section Bounds

variable {x : ℝ}

theorem summable_g (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Summable (fun j : ℕ => mass μ (j + 1) * x ^ (j + 1)) :=
  Summable.of_nonneg_of_le (fun _ => mul_nonneg (mass_nonneg _) (pow_nonneg hx0 _))
    (fun _ => mul_le_of_le_one_right (mass_nonneg _) (pow_le_one₀ hx0 hx1))
    ((summable_nat_add_iff 1).mpr summable_mass)

theorem g_nonneg (hx0 : 0 ≤ x) : 0 ≤ g μ x :=
  tsum_nonneg fun _ => mul_nonneg (mass_nonneg _) (pow_nonneg hx0 _)

/-- `g = G_μ - μ_0` on `[0, 1]`, where `G_μ` is the generating function of `μ`. -/
theorem g_eq_pgf_sub (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    g μ x = (∑' j : ℕ, mass μ j * x ^ j) - mass μ 0 := by
  have hs : Summable (fun j : ℕ => mass μ j * x ^ j) :=
    (summable_nat_add_iff 1).mp (summable_g hx0 hx1)
  rw [hs.tsum_eq_zero_add]
  simp [g]

theorem tsum_mass_succ : ∑' j : ℕ, mass μ (j + 1) = 1 - mass μ 0 := by
  have h := (hasSum_nat_add_iff' 1).mpr (hasSum_mass (μ := μ))
  simpa using h.tsum_eq

/-- `g(x) ≤ (1 - μ_0) x` on `[0, 1]`. -/
theorem g_le_mul (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : g μ x ≤ (1 - mass μ 0) * x := by
  rw [← tsum_mass_succ, ← tsum_mul_right]
  exact (summable_g hx0 hx1).tsum_le_tsum
    (fun j => mul_le_mul_of_nonneg_left (pow_le_of_le_one hx0 hx1 (Nat.succ_ne_zero j))
      (mass_nonneg _))
    (((summable_nat_add_iff 1).mpr summable_mass).mul_right x)

/-- Each term gives a lower bound: `μ_m x^m ≤ g(x)` for `m ≥ 1` and `x ∈ [0, 1]`. -/
theorem mass_mul_pow_le_g {m : ℕ} (hm : 1 ≤ m) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    mass μ m * x ^ m ≤ g μ x := by
  have h := (summable_g (μ := μ) hx0 hx1).le_tsum (m - 1)
    (fun j _ => mul_nonneg (mass_nonneg _) (pow_nonneg hx0 _))
  rwa [Nat.sub_add_cancel hm] at h

/-- Upper bound: if `μ_j = 0` for `1 ≤ j < m`, then `g(x) ≤ μ_m x^m + x^{m+1}` on `[0, 1]`. -/
theorem g_le_mass_mul_pow_add {m : ℕ} (hm : 1 ≤ m)
    (hzero : ∀ j, 1 ≤ j → j < m → mass μ j = 0) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    g μ x ≤ mass μ m * x ^ m + x ^ (m + 1) := by
  have hs := summable_g (μ := μ) hx0 hx1
  rw [g, ← hs.sum_add_tsum_nat_add m]
  gcongr
  · rw [Finset.sum_eq_single (m - 1)]
    · rw [Nat.sub_add_cancel hm]
    · intro j hj hjne
      rw [hzero (j + 1) (by omega) (by simp at hj; omega), zero_mul]
    · intro h
      exact absurd (Finset.mem_range.mpr (by omega)) h
  · have hsm : Summable (fun j : ℕ => mass μ (j + m + 1)) :=
      (summable_nat_add_iff (m + 1)).mpr summable_mass |>.congr fun j => by
        rw [Nat.add_assoc]
    calc ∑' j : ℕ, mass μ (j + m + 1) * x ^ (j + m + 1)
        ≤ ∑' j : ℕ, mass μ (j + m + 1) * x ^ (m + 1) :=
          ((summable_nat_add_iff m).mpr hs).tsum_le_tsum
            (fun j => mul_le_mul_of_nonneg_left
              (pow_le_pow_of_le_one hx0 hx1 (by omega)) (mass_nonneg _))
            (hsm.mul_right _)
      _ = (∑' j : ℕ, mass μ (j + m + 1)) * x ^ (m + 1) := tsum_mul_right
      _ ≤ 1 * x ^ (m + 1) := by
          gcongr
          rw [← tsum_mass (μ := μ)]
          exact tsum_comp_le_tsum_of_inj summable_mass (fun j => mass_nonneg j)
            (i := fun j => j + m + 1) (fun a b h => by simpa using h)
      _ = x ^ (m + 1) := one_mul _

/-- The two-sided bound `μ_κ x^κ ≤ g(x) ≤ μ_κ x^κ + x^{κ+1}` on `[0, 1]`. -/
theorem g_bounds (hc : IsCritical μ) (h1 : μ 1 ≠ 1) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    mass μ (kappa μ) * x ^ kappa μ ≤ g μ x ∧
      g μ x ≤ mass μ (kappa μ) * x ^ kappa μ + x ^ (kappa μ + 1) :=
  ⟨mass_mul_pow_le_g (one_le_kappa hc h1) hx0 hx1,
    g_le_mass_mul_pow_add (one_le_kappa hc h1)
      (fun _ hj hjk => mass_eq_zero_of_lt_kappa hj hjk) hx0 hx1⟩

end Bounds

/-! ### Item (a): positivity, strict decrease and convergence to zero -/

section Decrease

variable (hc : IsCritical μ) (h1 : μ 1 ≠ 1)
include hc h1

theorem piSeq_pos_le_one (k : ℕ) : 0 < piSeq μ k ∧ piSeq μ k ≤ 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨h0, h1'⟩ := ih
    rw [piSeq_succ]
    refine ⟨lt_of_lt_of_le ?_ (g_bounds hc h1 h0.le h1').1, ?_⟩
    · exact mul_pos (mass_kappa_pos hc h1) (pow_pos h0 _)
    · calc g μ (piSeq μ k) ≤ (1 - mass μ 0) * piSeq μ k := g_le_mul h0.le h1'
        _ ≤ 1 * 1 := mul_le_mul (by linarith [mass_nonneg (μ := μ) 0]) h1' h0.le zero_le_one
        _ = 1 := one_mul 1

theorem piSeq_pos (k : ℕ) : 0 < piSeq μ k := (piSeq_pos_le_one hc h1 k).1

theorem piSeq_le_one (k : ℕ) : piSeq μ k ≤ 1 := (piSeq_pos_le_one hc h1 k).2

theorem piSeq_succ_le_mul (k : ℕ) : piSeq μ (k + 1) ≤ (1 - mass μ 0) * piSeq μ k :=
  g_le_mul (piSeq_pos hc h1 k).le (piSeq_le_one hc h1 k)

theorem piSeq_succ_lt (k : ℕ) : piSeq μ (k + 1) < piSeq μ k := by
  have := piSeq_succ_le_mul hc h1 k
  have := mass_zero_pos hc h1
  have := piSeq_pos hc h1 k
  nlinarith

/-- `π_k` is strictly decreasing. -/
theorem strictAnti_piSeq : StrictAnti (piSeq μ) :=
  strictAnti_nat_of_succ_lt (piSeq_succ_lt hc h1)

theorem antitone_piSeq : Antitone (piSeq μ) := (strictAnti_piSeq hc h1).antitone

theorem piSeq_le_pow (k : ℕ) : piSeq μ k ≤ (1 - mass μ 0) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc piSeq μ (k + 1) ≤ (1 - mass μ 0) * piSeq μ k := piSeq_succ_le_mul hc h1 k
      _ ≤ (1 - mass μ 0) * (1 - mass μ 0) ^ k := by
          gcongr
          linarith [mass_le_one (μ := μ) 0]
      _ = (1 - mass μ 0) ^ (k + 1) := by ring

/-- `π_k → 0` (extinction of the critical non-degenerate process). -/
theorem tendsto_piSeq_zero : Tendsto (piSeq μ) atTop (𝓝 0) := by
  have h0 := mass_zero_pos hc h1
  have h0' := mass_le_one (μ := μ) 0
  exact squeeze_zero (fun k => (piSeq_pos hc h1 k).le) (piSeq_le_pow hc h1)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith))

theorem ellSeq_pos (k : ℕ) : 0 < ellSeq μ k := by
  have := piSeq_succ_lt hc h1 k
  simp only [ellSeq]
  linarith

end Decrease

end LeafHeight
end PoissonDeclumping
