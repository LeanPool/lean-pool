/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Analysis.Maximal.HardyLittlewoodMaximal
public import LeanPool.FunctionSpaces.Rd.LocalMeans.LocalMeans
public import LeanPool.FunctionSpaces.Rd.Differences.PointwiseMultipliers
public import LeanPool.FunctionSpaces.Analysis.Differences.DomainModuli

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Atomic synthesis

Atomic decompositions in the sense of Schneider–Vybíral, for `1 ≤ p < ∞`. A **regular atom** of
level `j ∈ ℕ`, exponent `σ > 0` and order `r` with centre `c` (`Rd.IsRegularAtom`) vanishes
outside the ball `B(c, d 2^(-j))` and satisfies, with a constant `C`,

`‖a‖_p ≤ C 2^(-jn/p)`,  `‖Δ_h^r a‖_p ≤ C 2^(-jn/p) min(1, (2^j ‖h‖)^σ)`,

`n = dim V`. Lip atoms (Schneider–Vybíral, Definition 2.1: `|a| ≤ 1`, `|a(x) - a(y)| ≤ 2^j |x - y|`)
are regular with `σ = r = 1`, smooth `K`-atoms (`|D^α a| ≤ 2^(j|α|)`, Definition 1.3) with
`σ = r = K`; both follow from pointwise bounds (`Rd.isRegularAtom_of_pointwise`).

**Synthesis** (`Rd.modNorm_le_coeffNorm`) is the regular-atom analogue of the synthesis
in Schneider–Vybíral, Theorem 2.6. Their Corollary 2.8 uses Lipschitz atoms and `0 < s < 1`.
If the centres of each level have bounded overlap and `F = ∑_j f_j` with the level
sums `f_j = ∑_m λ_{j,m} a_{j,m}`, then for `0 < s < σ`

`‖F‖_p + ‖(2^(ks) ω_r(F, 2^(-k))_p)_k‖_{ℓ_q} ≤ K ‖λ‖_{b^s_{p,q}}`,
`‖λ‖_{b^s_{p,q}} = ‖(2^(j(s - n/p)) ‖λ_{j,·}‖_{ℓ_p})_j‖_{ℓ_q}` (`Rd.coeffNorm`).

The proof: by bounded overlap (`Rd.eLpNorm_rpow_le_of_overlap`),
`‖f_j‖_p ≲ 2^(-jn/p) ‖λ_{j,·}‖_{ℓ_p}` and
`ω_r(f_j, 2^(-k))_p ≲ 2^(-jn/p) ‖λ_{j,·}‖_{ℓ_p} min(1, 2^(-(k-j)σ))`
(`Rd.eLpNorm_levelSum_le`, `Rd.modulus_levelSum_le`); the almost diagonal lemma with exponent `σ`
sums the levels. Smooth functions with `‖D^l a‖ ≤ A 2^(jl)` for `l ≤ r` satisfy the pointwise
bounds with `σ = r` (`Rd.enorm_higherDiff_le_of_iteratedFDeriv`).

**Atoms on a set.** A regular atom on a measurable set `Ω` (`Rd.IsRegularAtomOn`) satisfies the
bounds with `‖1_Ω a‖_p` and with the differences restricted to the step sets `Ω_{rh}`; regular
atoms are the regular atoms on `V`. The synthesis on `Ω` (`Rd.modNormOn_le_coeffNorm`) bounds
`‖1_Ω F‖_p + ‖(2^(ks) ω_r(F, 2^(-k), Ω)_p)_k‖_{ℓ_q}` in the same way, with the same proof.
-/

@[expose] public section

open MeasureTheory Filter Topology Module Metric
open scoped ENNReal

open ENNReal (lqNorm dyadicWeight)

namespace Rd

/-! ### Regular atoms -/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- A **regular atom on `Ω`** of level `j`, exponent `σ` and order `r` with centre `c`, radius
factor `d` and constant `C`: `a = 0` outside `B(c, d 2^(-j))`, `‖a‖_{L_p(Ω)} ≤ C 2^(-jn/p)` and
`‖Δ_h^r a‖_{L_p(Ω_{rh})} ≤ C 2^(-jn/p) min(1, (2^j ‖h‖)^σ)`, where `Ω_{rh}` are the points whose
steps `x + l h`, `l ≤ r`, stay in `Ω` (`Rd.stepSet`). Only the values of `a` on `Ω` enter. -/
structure IsRegularAtomOn (Ω : Set V) (p : ℝ≥0∞) (σ : ℝ) (r : ℕ) (d : ℝ) (C : ℝ≥0∞) (j : ℕ)
    (c : V) (a : V → ℂ) : Prop where
  aestronglyMeasurable : AEStronglyMeasurable a volume
  eq_zero : ∀ x, d / 2 ^ j < ‖x - c‖ → a x = 0
  eLpNorm_le : eLpNorm (Ω.indicator a) p volume ≤ C * dyadicWeight (-(finrank ℝ V / p.toReal)) j
  eLpNorm_higherDiff_le : ∀ h : V, eLpNorm ((stepSet Ω r h).indicator ((fwdDiff h)^[r] a)) p
    volume ≤
    C * dyadicWeight (-(finrank ℝ V / p.toReal)) j * min 1 (ENNReal.ofReal (2 ^ j * ‖h‖) ^ σ)

/-- A **regular atom** of level `j`, exponent `σ` and order `r` with centre `c`, radius factor `d`
and constant `C`: a regular atom on `V`, that is, `a = 0` outside `B(c, d 2^(-j))`,
`‖a‖_p ≤ C 2^(-jn/p)` and `‖Δ_h^r a‖_p ≤ C 2^(-jn/p) min(1, (2^j ‖h‖)^σ)`. -/
abbrev IsRegularAtom (p : ℝ≥0∞) (σ : ℝ) (r : ℕ) (d : ℝ) (C : ℝ≥0∞) (j : ℕ) (c : V)
    (a : V → ℂ) : Prop :=
  IsRegularAtomOn (Set.univ : Set V) p σ r d C j c a

/-- The `ℓ_p`-norm `‖λ_{j,·}‖_{ℓ_p}` of the coefficients of one level. -/
noncomputable def levelNorm (p : ℝ≥0∞) {ι : Type*} [MeasurableSpace ι] (coef : ι → ℂ) : ℝ≥0∞ :=
  lqNorm p fun m => ‖coef m‖ₑ

/-- For `0 < p < ∞`, `‖λ_{j,·}‖_{ℓ_p} = (∑_m |λ_{j,m}|^p)^(1/p)`. -/
theorem levelNorm_eq_tsum {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞) {ι : Type*} [MeasurableSpace ι]
    [Countable ι] [MeasurableSingletonClass ι] (coef : ι → ℂ) :
    levelNorm p coef = (∑' m, ‖coef m‖ₑ ^ p.toReal) ^ (1 / p.toReal) :=
  ENNReal.lqNorm_eq_tsum hp0 hp _

/-- The `ℓ_p`-norm of the coefficients is monotone in their moduli. -/
theorem levelNorm_mono (p : ℝ≥0∞) {ι : Type*} [MeasurableSpace ι] [Countable ι]
    [MeasurableSingletonClass ι] {coef coef' : ι → ℂ} (h : ∀ m, ‖coef m‖ₑ ≤ ‖coef' m‖ₑ) :
    levelNorm p coef ≤ levelNorm p coef' :=
  ENNReal.lqNorm_mono h

/-- The **coefficient quasi-norm** `‖λ‖_{b^s_{p,q}} = ‖(2^(j(s - n/p)) ‖λ_{j,·}‖_{ℓ_p})_j‖_{ℓ_q}`.
-/
noncomputable def coeffNorm (p : ℝ≥0∞) (n : ℕ) (s : ℝ) (q : ℝ≥0∞) {ι : Type*} [MeasurableSpace ι]
    (coef : ℕ → ι → ℂ) : ℝ≥0∞ :=
  lqNorm q (fun j => dyadicWeight (s - n / p.toReal) j * levelNorm p (coef j))

/-! ### Level sums -/

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- Differences of a pointwise convergent sum are the sums of the differences, if the sums
converge at all the points of the difference. -/
theorem higherDiff_tsum_apply [NormedSpace ℝ V] {ι : Type*} (g : ι → V → ℂ)
    (hg : ∀ y, Summable fun m => g m y) (r : ℕ) (h x : V) :
    (fwdDiff h)^[r] (fun y => ∑' m, g m y) x = ∑' m, (fwdDiff h)^[r] (g m) x := by
  simp_rw [higherDiff_apply]
  rw [Summable.tsum_finsetSum fun l _ => (hg _).mul_left _]
  exact Finset.sum_congr rfl fun l _ => (tsum_mul_left).symm

/-- From `X^p ≤ N^(p-1) ∑ (b_m |λ_m|)^p` with `b_m ≤ B` to `X ≤ N^(1-1/p) B ‖λ‖_{ℓ_p}`. -/
theorem le_of_rpow_le_overlap {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {ι : Type*} [MeasurableSpace ι]
    [Countable ι] [MeasurableSingletonClass ι] {X B : ℝ≥0∞}
    {N : ℕ} {b : ι → ℝ≥0∞} (hb : ∀ m, b m ≤ B) (coef : ι → ℂ)
    (hX : X ^ p.toReal ≤ (N : ℝ≥0∞) ^ (p.toReal - 1) * ∑' m, (‖coef m‖ₑ * b m) ^ p.toReal) :
    X ≤ (N : ℝ≥0∞) ^ (1 - 1 / p.toReal) * B * levelNorm p coef := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  have hpos : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  rw [← ENNReal.rpow_le_rpow_iff hpos]
  refine hX.trans ?_
  rw [levelNorm_eq_tsum hp0 hp, ENNReal.mul_rpow_of_nonneg _ _ hpos.le,
    ENNReal.mul_rpow_of_nonneg _ _ hpos.le,
    ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, show (1 - 1 / p.toReal) * p.toReal = p.toReal - 1 by
      field_simp, show 1 / p.toReal * p.toReal = 1 by field_simp, ENNReal.rpow_one, mul_assoc]
  refine mul_le_mul' le_rfl ?_
  rw [← ENNReal.tsum_mul_left]
  refine tsum_le_tsum fun m => ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ hpos.le, mul_comm]
  exact mul_le_mul' (ENNReal.rpow_le_rpow (hb m) hpos.le) le_rfl

/-- The pointwise sums of a level converge: at most `N` atoms of the level with nonzero
coefficients are nonzero at a point. -/
theorem summable_levelSum {ι : Type*} {Ω : Set V} {p : ℝ≥0∞} {σ : ℝ} {r : ℕ} {d : ℝ}
    {C : ℝ≥0∞} {j N : ℕ} (c : ι → V) (a : ι → V → ℂ) (coef : ι → ℂ)
    (hN : ∀ x (S : Finset ι), (∀ m ∈ S, coef m ≠ 0 ∧ ‖x - c m‖ ≤ (d + r) / 2 ^ j) → S.card ≤ N)
    (ha : ∀ m, IsRegularAtomOn Ω p σ r d C j (c m) (a m)) (y : V) :
    Summable fun m => coef m * a m y := by
  have hd : ∀ m, coef m * a m y ≠ 0 → coef m ≠ 0 ∧ ‖y - c m‖ ≤ (d + r) / 2 ^ j := fun m hm => by
    have ha' : a m y ≠ 0 := right_ne_zero_of_mul hm
    have h1 : ‖y - c m‖ ≤ d / 2 ^ j := not_lt.1 fun h => ha' ((ha m).eq_zero y h)
    exact ⟨left_ne_zero_of_mul hm, h1.trans (div_le_div_of_nonneg_right
      (by linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)]) (by positivity))⟩
  obtain ⟨T, hT, -⟩ := exists_finset_of_card_le (P := fun m => coef m * a m y ≠ 0)
    fun S hS => hN y S fun m hm => hd m (hS m hm)
  exact summable_of_ne_finset_zero fun m hm => by_contra fun h => hm (hT m h)

/-- **The level sums in `L_p(Ω)`**: `‖∑_m λ_m a_m‖_{L_p(Ω)} ≤ N^(1-1/p) C 2^(-jn/p) ‖λ‖_{ℓ_p}` for
regular atoms on `Ω`. -/
theorem eLpNorm_indicator_levelSum_le {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {Ω : Set V}
    (hΩ : MeasurableSet Ω) {ι : Type*} [Countable ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] {σ : ℝ} {r : ℕ} {d : ℝ} {C : ℝ≥0∞} {j N : ℕ} (c : ι → V)
    (a : ι → V → ℂ) (coef : ι → ℂ)
    (hN : ∀ x (S : Finset ι), (∀ m ∈ S, coef m ≠ 0 ∧ ‖x - c m‖ ≤ (d + r) / 2 ^ j) → S.card ≤ N)
    (ha : ∀ m, IsRegularAtomOn Ω p σ r d C j (c m) (a m)) {F : V → ℂ}
    (hF : AEStronglyMeasurable F volume) (hFa : ∀ᵐ x ∂volume, F x = ∑' m, coef m * a m x) :
    eLpNorm (Ω.indicator F) p volume ≤ (N : ℝ≥0∞) ^ (1 - 1 / p.toReal) *
      (C * dyadicWeight (-(finrank ℝ V / p.toReal)) j) * levelNorm p coef := by
  have hg : ∀ m, AEStronglyMeasurable (fun x => coef m * Ω.indicator (a m) x) volume := fun m =>
    aestronglyMeasurable_const.mul ((ha m).aestronglyMeasurable.indicator hΩ)
  have hover : ∀ x (S : Finset ι), (∀ m ∈ S, coef m * Ω.indicator (a m) x ≠ 0) → S.card ≤ N :=
    fun x S hS => hN x S fun m hm => by
      have hne := hS m hm
      have ha' : a m x ≠ 0 := fun h0 =>
        right_ne_zero_of_mul hne (Set.indicator_apply_eq_zero.2 fun _ => h0)
      have h1 : ‖x - c m‖ ≤ d / 2 ^ j := not_lt.1 fun h => ha' ((ha m).eq_zero x h)
      exact ⟨left_ne_zero_of_mul hne, h1.trans (div_le_div_of_nonneg_right
        (by linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)]) (by positivity))⟩
  have hFa' : ∀ᵐ x ∂volume, Ω.indicator F x = ∑' m, coef m * Ω.indicator (a m) x := by
    filter_upwards [hFa] with x hx
    by_cases hxΩ : x ∈ Ω
    · simp only [Set.indicator_of_mem hxΩ]
      exact hx
    · simp [Set.indicator_of_notMem hxΩ]
  have h := eLpNorm_rpow_le_of_overlap hp1 hp hg hover (hF.indicator hΩ) hFa'
  refine le_of_rpow_le_overlap hp1 hp (fun m => (ha m).eLpNorm_le) coef (h.trans_eq ?_)
  congr 2
  funext m
  rw [show (fun x => coef m * Ω.indicator (a m) x) = coef m • Ω.indicator (a m) from rfl,
    eLpNorm_const_smul]

/-- **The level sums in `L_p`**: `‖∑_m λ_m a_m‖_p ≤ N^(1-1/p) C 2^(-jn/p) ‖λ‖_{ℓ_p}`, the case
`Ω = V` of `Rd.eLpNorm_indicator_levelSum_le`. -/
theorem eLpNorm_levelSum_le {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {ι : Type*} [Countable ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {σ : ℝ} {r : ℕ} {d : ℝ} {C : ℝ≥0∞} {j N : ℕ} (c : ι → V) (a : ι → V → ℂ) (coef : ι → ℂ)
    (hN : ∀ x (S : Finset ι), (∀ m ∈ S, coef m ≠ 0 ∧ ‖x - c m‖ ≤ (d + r) / 2 ^ j) → S.card ≤ N)
    (ha : ∀ m, IsRegularAtom p σ r d C j (c m) (a m)) {F : V → ℂ} (hF : AEStronglyMeasurable F
      volume)
    (hFa : ∀ᵐ x ∂volume, F x = ∑' m, coef m * a m x) :
    eLpNorm F p volume ≤ (N : ℝ≥0∞) ^ (1 - 1 / p.toReal) *
      (C * dyadicWeight (-(finrank ℝ V / p.toReal)) j) * levelNorm p coef := by
  simpa using eLpNorm_indicator_levelSum_le hp1 hp MeasurableSet.univ c a coef hN ha hF hFa

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **Bounded overlap of the differences of atoms**: if the atoms `a_m` vanish outside the balls
`B(c_m, d 2^(-j))` and at most `N` centres with `λ_m ≠ 0` lie in a ball of radius
`(d + r) 2^(-j)`, then for `‖h‖ ≤ 2^(-j)` at most `N` of the functions `λ_m Δ_h^r a_m` are nonzero
at any point, since `Δ_h^r a_m(x) ≠ 0` needs some `x + l h`, `l ≤ r`, in the ball of `a_m`. -/
theorem card_le_of_higherDiff_ne_zero {ι : Type*} {r : ℕ} {d : ℝ} {j N : ℕ} (c : ι → V)
    (a : ι → V → ℂ) (coef : ι → ℂ)
    (hN : ∀ x (S : Finset ι), (∀ m ∈ S, coef m ≠ 0 ∧ ‖x - c m‖ ≤ (d + r) / 2 ^ j) → S.card ≤ N)
    (ha : ∀ m x, d / 2 ^ j < ‖x - c m‖ → a m x = 0) {h : V} (hhk : ‖h‖ ≤ 1 / 2 ^ j) (x : V)
    (S : Finset ι) (hS : ∀ m ∈ S, coef m * (fwdDiff h)^[r] (a m) x ≠ 0) : S.card ≤ N := by
  refine hN x S fun m hm => ?_
  have hne : (fwdDiff h)^[r] (a m) x ≠ 0 := right_ne_zero_of_mul (hS m hm)
  rw [higherDiff_apply] at hne
  obtain ⟨l, hl, hl0⟩ : ∃ l ∈ Finset.range (r + 1), a m (x + (l : ℝ) • h) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hne (Finset.sum_eq_zero fun l hl => by rw [hcon l hl, mul_zero])
  have h1 : ‖x + (l : ℝ) • h - c m‖ ≤ d / 2 ^ j := not_lt.1 fun h' => hl0 (ha m _ h')
  have hl' : (l : ℝ) ≤ r := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
  have h2 : ‖(l : ℝ) • h‖ ≤ r / 2 ^ j := by
    rw [norm_smul, Real.norm_of_nonneg (Nat.cast_nonneg l)]
    calc (l : ℝ) * ‖h‖ ≤ r * (1 / 2 ^ j) :=
          mul_le_mul hl' hhk (norm_nonneg h) (Nat.cast_nonneg r)
      _ = r / 2 ^ j := by ring
  refine ⟨left_ne_zero_of_mul (hS m hm), ?_⟩
  calc ‖x - c m‖ = ‖(x + (l : ℝ) • h - c m) - (l : ℝ) • h‖ := by congr 1; abel
    _ ≤ ‖x + (l : ℝ) • h - c m‖ + ‖(l : ℝ) • h‖ := norm_sub_le _ _
    _ ≤ d / 2 ^ j + r / 2 ^ j := add_le_add h1 h2
    _ = (d + r) / 2 ^ j := by ring

/-- **Moduli of the level sums on `Ω`**: `ω_r(∑_m λ_m a_m, 2^(-k), Ω)_p ≤
2^r N^(1-1/p) C 2^(-jn/p) ‖λ‖_{ℓ_p} c_{kj}` with `c_{kj} = 2^(-(k-j)σ)` for `j ≤ k` and `1`
otherwise, for regular atoms on `Ω`. -/
theorem modulusOn_levelSum_le {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {Ω : Set V}
    (hΩ : MeasurableSet Ω) {ι : Type*} [Countable ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] {σ : ℝ} (hσ : 0 ≤ σ) {r : ℕ} {d : ℝ} {C : ℝ≥0∞} {j N : ℕ}
    (c : ι → V) (a : ι → V → ℂ) (coef : ι → ℂ)
    (hN : ∀ x (S : Finset ι), (∀ m ∈ S, coef m ≠ 0 ∧ ‖x - c m‖ ≤ (d + r) / 2 ^ j) → S.card ≤ N)
    (ha : ∀ m, IsRegularAtomOn Ω p σ r d C j (c m) (a m)) {F : V → ℂ}
    (hF : AEStronglyMeasurable F volume) (hFa : ∀ᵐ x ∂volume, F x = ∑' m, coef m * a m x)
    (k : ℕ) :
    modulusOn volume Ω r p F (1 / 2 ^ k) ≤ 2 ^ r * ((N : ℝ≥0∞) ^ (1 - 1 / p.toReal) *
      (C * dyadicWeight (-(finrank ℝ V / p.toReal)) j) * levelNorm p coef) *
        (if j ≤ k then dyadicWeight (-σ) (k - j) else 1) := by
  set B := (N : ℝ≥0∞) ^ (1 - 1 / p.toReal) * (C * dyadicWeight (-(finrank ℝ V / p.toReal)) j) *
    levelNorm p coef
  split_ifs with hjk
  · refine iSup₂_le fun h hh => ?_
    set T := stepSet Ω r h
    have hT : MeasurableSet T := measurableSet_stepSet hΩ r h
    have hsum : ∀ y, Summable fun m => coef m * a m y := summable_levelSum c a coef hN ha
    have hae : T.indicator ((fwdDiff h)^[r] F) =ᵐ[volume]
        fun x => ∑' m, coef m * T.indicator ((fwdDiff h)^[r] (a m)) x := by
      filter_upwards [higherDiff_congr_ae hFa r h] with x hx
      by_cases hxT : x ∈ T
      · simp only [Set.indicator_of_mem hxT]
        rw [hx, higherDiff_tsum_apply _ hsum]
        refine tsum_congr fun m => ?_
        rw [show (fun y => coef m * a m y) = coef m • a m from rfl, fwdDiff_iter_const_smul]
        rfl
      · simp [Set.indicator_of_notMem hxT]
    have hg : ∀ m, AEStronglyMeasurable
        (fun x => coef m * T.indicator ((fwdDiff h)^[r] (a m)) x) volume := fun m =>
      aestronglyMeasurable_const.mul
        ((aestronglyMeasurable_higherDiff (ha m).aestronglyMeasurable r h).indicator hT)
    have hhk : ‖h‖ ≤ 1 / 2 ^ j := hh.trans (one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_right₀ one_le_two hjk))
    have hover : ∀ x (S : Finset ι), (∀ m ∈ S, coef m * T.indicator ((fwdDiff h)^[r] (a m)) x ≠ 0) →
        S.card ≤ N := fun x S hS =>
      card_le_of_higherDiff_ne_zero c a coef hN (fun m => (ha m).eq_zero) hhk x S fun m hm => by
        have h1 := hS m hm
        by_cases hxT : x ∈ T
        · rwa [Set.indicator_of_mem hxT] at h1
        · rw [Set.indicator_of_notMem hxT, mul_zero] at h1
          exact absurd rfl h1
    have hbound := eLpNorm_rpow_le_of_overlap hp1 hp hg hover
      ((aestronglyMeasurable_higherDiff hF r h).indicator hT) hae
    have hmin : min 1 (ENNReal.ofReal (2 ^ j * ‖h‖) ^ σ) ≤ dyadicWeight (-σ) (k - j) :=
      (min_le_right _ _).trans (ENNReal.ofReal_two_pow_mul_rpow_le hjk hh hσ)
    calc eLpNorm (T.indicator ((fwdDiff h)^[r] F)) p volume
        ≤ (N : ℝ≥0∞) ^ (1 - 1 / p.toReal) * (C * dyadicWeight (-(finrank ℝ V / p.toReal)) j *
            dyadicWeight (-σ) (k - j)) * levelNorm p coef :=
          le_of_rpow_le_overlap hp1 hp (fun m => ((ha m).eLpNorm_higherDiff_le h).trans
            (mul_le_mul' le_rfl hmin)) coef (hbound.trans_eq (by
              congr 2
              funext m
              rw [show (fun x => coef m * T.indicator ((fwdDiff h)^[r] (a m)) x) =
                coef m • T.indicator ((fwdDiff h)^[r] (a m)) from rfl, eLpNorm_const_smul]))
      _ ≤ 2 ^ r * B * dyadicWeight (-σ) (k - j) := by
          calc (N : ℝ≥0∞) ^ (1 - 1 / p.toReal) * (C * dyadicWeight (-(finrank ℝ V / p.toReal)) j *
                dyadicWeight (-σ) (k - j)) * levelNorm p coef
              = 1 * B * dyadicWeight (-σ) (k - j) := by
                simp only [B]
                ring
            _ ≤ 2 ^ r * B * dyadicWeight (-σ) (k - j) := by
                gcongr
                exact one_le_pow₀ one_le_two
  · rw [mul_one]
    exact (modulusOn_le hF hΩ hp1 r _).trans (mul_le_mul' le_rfl
      (eLpNorm_indicator_levelSum_le hp1 hp hΩ c a coef hN ha hF hFa))

/-- **Moduli of the level sums**: `ω_r(∑_m λ_m a_m, 2^(-k))_p ≤
2^r N^(1-1/p) C 2^(-jn/p) ‖λ‖_{ℓ_p} c_{kj}` with `c_{kj} = 2^(-(k-j)σ)` for `j ≤ k` and `1`
otherwise, the case `Ω = V` of `Rd.modulusOn_levelSum_le`. -/
theorem modulus_levelSum_le {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {ι : Type*} [Countable ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {σ : ℝ} (hσ : 0 ≤ σ) {r : ℕ} {d : ℝ} {C : ℝ≥0∞} {j N : ℕ} (c : ι → V) (a : ι → V → ℂ)
    (coef : ι → ℂ)
    (hN : ∀ x (S : Finset ι), (∀ m ∈ S, coef m ≠ 0 ∧ ‖x - c m‖ ≤ (d + r) / 2 ^ j) → S.card ≤ N)
    (ha : ∀ m, IsRegularAtom p σ r d C j (c m) (a m)) {F : V → ℂ} (hF : AEStronglyMeasurable F
      volume)
    (hFa : ∀ᵐ x ∂volume, F x = ∑' m, coef m * a m x) (k : ℕ) :
    modulus volume r p F (1 / 2 ^ k) ≤ 2 ^ r * ((N : ℝ≥0∞) ^ (1 - 1 / p.toReal) *
      (C * dyadicWeight (-(finrank ℝ V / p.toReal)) j) * levelNorm p coef) *
        (if j ≤ k then dyadicWeight (-σ) (k - j) else 1) := by
  rw [← modulusOn_univ]
  exact modulusOn_levelSum_le hp1 hp MeasurableSet.univ hσ c a coef hN ha hF hFa k

/-! ### The synthesis theorem -/

/-- The constant `N^(1-1/p) C ((1 - 2^(-s))⁻¹ + 2^r ((1 - 2^(-(σ-s)))⁻¹ + (1 - 2^(-s))⁻¹))` of the
atomic synthesis. -/
noncomputable def atomSynthConst (p : ℝ≥0∞) (N : ℕ) (C : ℝ≥0∞) (r : ℕ) (s σ : ℝ) : ℝ≥0∞ :=
  (N : ℝ≥0∞) ^ (1 - 1 / p.toReal) * C * ((1 - (2 : ℝ≥0∞) ^ (-s))⁻¹ +
    2 ^ r * ((1 - (2 : ℝ≥0∞) ^ (-(σ - s)))⁻¹ + (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹))

/-- The constant of the atomic synthesis is finite for `C < ∞` and `0 < s < σ`. -/
theorem atomSynthConst_ne_top {p : ℝ≥0∞} (hp1 : 1 ≤ p) (N : ℕ) {C : ℝ≥0∞}
    (hC : C ≠ ∞) (r : ℕ) {s σ : ℝ} (hs : 0 < s) (hsσ : s < σ) :
    atomSynthConst p N C r s σ ≠ ∞ := by
  have hexp : 0 ≤ 1 - 1 / p.toReal := one_sub_one_div_toReal_nonneg hp1
  refine ENNReal.mul_ne_top (ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg hexp (ENNReal.natCast_ne_top N)) hC)
    (ENNReal.add_ne_top.2 ⟨ENNReal.one_sub_two_rpow_neg_inv_ne_top hs,
      ENNReal.mul_ne_top (by simp) (ENNReal.add_ne_top.2
        ⟨ENNReal.one_sub_two_rpow_neg_inv_ne_top (by linarith),
          ENNReal.one_sub_two_rpow_neg_inv_ne_top hs⟩)⟩)

/-- **The norm on `Ω` of a series**: if `∑_{j ≤ J} f_j → F` in `L_p`, then
`‖F‖_{L_p(Ω)} ≤ ∑_j ‖f_j‖_{L_p(Ω)}`. -/
theorem eLpNorm_indicator_le_tsum {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set V} (hΩ : MeasurableSet Ω)
    {f : ℕ → Lp ℂ p (volume : Measure V)} {F : Lp ℂ p (volume : Measure V)}
    (hF : Tendsto (fun J => ∑ j ∈ Finset.range (J + 1), f j) atTop (𝓝 F)) :
    eLpNorm (Ω.indicator F) p volume ≤ ∑' j, eLpNorm (Ω.indicator (f j)) p volume :=
  ENNReal.le_tsum_of_tendsto_sum
    (Q := fun G : Lp ℂ p (volume : Measure V) => eLpNorm (Ω.indicator G) p volume) (C := 1)
    ENNReal.one_ne_top (fun x y => by
      have hxy : Ω.indicator ⇑(x + y) =ᵐ[volume] Ω.indicator ⇑x + Ω.indicator ⇑y := by
        filter_upwards [Lp.coeFn_add x y] with z hz
        by_cases hzΩ : z ∈ Ω
        · rw [Pi.add_apply, Set.indicator_of_mem hzΩ, Set.indicator_of_mem hzΩ,
            Set.indicator_of_mem hzΩ, hz, Pi.add_apply]
        · rw [Pi.add_apply, Set.indicator_of_notMem hzΩ, Set.indicator_of_notMem hzΩ,
            Set.indicator_of_notMem hzΩ, add_zero]
      rw [eLpNorm_congr_ae hxy]
      exact eLpNorm_add_le Fact.out)
    (fun x => by rw [one_mul, Lp.eNorm_def]; exact eLpNorm_indicator_le _ hΩ.nullMeasurableSet) hF

/-- **The modulus on `Ω` of a series**: if `∑_{j ≤ J} f_j → F` in `L_p`, then
`ω_r(F, 2^(-k), Ω)_p ≤ ∑_j ω_r(f_j, 2^(-k), Ω)_p`. -/
theorem lpModulusOn_le_tsum {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set V} (hΩ : MeasurableSet Ω)
    {f : ℕ → Lp ℂ p (volume : Measure V)} {F : Lp ℂ p (volume : Measure V)}
    (hF : Tendsto (fun J => ∑ j ∈ Finset.range (J + 1), f j) atTop (𝓝 F)) (r k : ℕ) :
    lpModulusOn p Ω r F k ≤ ∑' j, lpModulusOn p Ω r (f j) k :=
  ENNReal.le_tsum_of_tendsto_sum (C := 2 ^ r) (by simp)
    (fun x y => lpModulusOn_add_le Ω r x y k) (fun x => lpModulusOn_le hΩ r x k) hF

/-- **Atomic synthesis on `Ω`**: if the centres of the atoms with nonzero coefficients have overlap
at most `N` on balls of radius `(d + r) 2^(-j)` at every level `j`, `F = ∑_j f_j` in `L_p` with the
level sums `f_j = ∑_m λ_{j,m} a_{j,m}` of regular atoms on `Ω` of exponent `σ` and order `r`, and
`0 < s < σ`, then
`‖F‖_{L_p(Ω)} + ‖(2^(ks) ω_r(F, 2^(-k), Ω)_p)_k‖_{ℓ_q} ≤ K ‖λ‖_{b^s_{p,q}}`. -/
theorem modNormOn_le_coeffNorm {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) {Ω : Set V}
    (hΩ : MeasurableSet Ω) {ι : Type*} [Countable ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {σ : ℝ} {r : ℕ} {d : ℝ} {C : ℝ≥0∞} {N : ℕ} (c : ℕ → ι → V) (a : ℕ → ι → V → ℂ)
    (coef : ℕ → ι → ℂ)
    (hN : ∀ j x (S : Finset ι), (∀ m ∈ S, coef j m ≠ 0 ∧ ‖x - c j m‖ ≤ (d + r) / 2 ^ j) →
      S.card ≤ N)
    (ha : ∀ j m, IsRegularAtomOn Ω p σ r d C j (c j m) (a j m))
    {f : ℕ → Lp ℂ p (volume : Measure V)}
    (hf : ∀ j, ∀ᵐ x ∂volume, f j x = ∑' m, coef j m * a j m x)
    {F : Lp ℂ p (volume : Measure V)}
    (hF : Tendsto (fun J => ∑ j ∈ Finset.range (J + 1), f j) atTop (𝓝 F))
    {s : ℝ} (hs : 0 < s) (hsσ : s < σ) {q : ℝ≥0∞} (hq : 1 ≤ q) :
    eLpNorm (Ω.indicator F) p volume + lqNorm q (fun k => dyadicWeight s k * lpModulusOn p Ω r F
      k) ≤
      atomSynthConst p N C r s σ * coeffNorm p (finrank ℝ V) s q coef := by
  have hp1 : 1 ≤ p := Fact.out
  set K0 := (N : ℝ≥0∞) ^ (1 - 1 / p.toReal) * C
  set b : ℕ → ℝ≥0∞ := fun j => dyadicWeight (-(finrank ℝ V / p.toReal)) j * levelNorm p (coef j)
  set X := lqNorm q (fun j => dyadicWeight s j * b j)
  have hX : coeffNorm p (finrank ℝ V) s q coef = X := by
    simp only [coeffNorm, X, b]
    congr 1
    funext j
    rw [← mul_assoc, ← ENNReal.dyadicWeight_add, ← sub_eq_add_neg]
  -- the level sums
  have hlevel : ∀ j, eLpNorm (Ω.indicator (f j)) p volume ≤ K0 * b j := fun j => by
    refine (eLpNorm_indicator_levelSum_le hp1 hp hΩ (c j) (a j) (coef j) (hN j) (ha j)
      (Lp.aestronglyMeasurable (f j)) (hf j)).trans_eq ?_
    simp only [K0, b]
    ring
  have hlevelMod : ∀ j k, lpModulusOn p Ω r (f j) k ≤
      2 ^ r * K0 * ((if j ≤ k then dyadicWeight (-σ) (k - j) else 1) * b j) := fun j k => by
    rw [lpModulusOn]
    refine (modulusOn_levelSum_le hp1 hp hΩ (hs.le.trans hsσ.le) (c j) (a j) (coef j) (hN j)
      (ha j) (Lp.aestronglyMeasurable (f j)) (hf j) k).trans_eq ?_
    simp only [K0, b]
    ring
  -- the norm on `Ω`
  have hnorm : eLpNorm (Ω.indicator F) p volume ≤ K0 * (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹ * X := by
    calc eLpNorm (Ω.indicator F) p volume ≤ ∑' j, K0 * b j :=
          (eLpNorm_indicator_le_tsum hΩ hF).trans (tsum_le_tsum hlevel)
      _ = K0 * ∑' j, b j := ENNReal.tsum_mul_left
      _ ≤ K0 * ((1 - (2 : ℝ≥0∞) ^ (-s))⁻¹ * X) :=
          mul_le_mul' le_rfl (ENNReal.tsum_le_lqNorm_dyadicWeight hq s b)
      _ = _ := (mul_assoc _ _ _).symm
  -- the moduli
  have hmod : ∀ k, lpModulusOn p Ω r F k ≤ 2 ^ r * K0 *
      ∑' j, (if j ≤ k then dyadicWeight (-σ) (k - j) else 1) * b j := fun k => by
    refine (lpModulusOn_le_tsum hΩ hF r k).trans ?_
    rw [← ENNReal.tsum_mul_left]
    exact tsum_le_tsum fun j => hlevelMod j k
  have hlq : lqNorm q (fun k => dyadicWeight s k * lpModulusOn p Ω r F k) ≤
      2 ^ r * K0 * ENNReal.almostDiagonalConst s σ * X :=
    ENNReal.lqNorm_le_almostDiagonalConst_mul_of_le hq s σ hmod
  rw [hX]
  calc eLpNorm (Ω.indicator F) p volume +
        lqNorm q (fun k => dyadicWeight s k * lpModulusOn p Ω r F k)
      ≤ K0 * (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹ * X +
          2 ^ r * K0 * ENNReal.almostDiagonalConst s σ * X :=
        add_le_add hnorm hlq
    _ = atomSynthConst p N C r s σ * X := by
        simp only [atomSynthConst, K0, ENNReal.almostDiagonalConst]
        ring

/-- **Atomic synthesis** for regular atoms. If the centres of the atoms with nonzero
coefficients have overlap at most `N` on balls of radius
`(d + r) 2^(-j)` at every level `j`,
`F = ∑_j f_j` in `L_p` with the level sums `f_j = ∑_m λ_{j,m} a_{j,m}` of regular atoms of
exponent `σ` and order `r`, and `0 < s < σ`, then
`‖F‖_p + ‖(2^(ks) ω_r(F, 2^(-k))_p)_k‖_{ℓ_q} ≤ K ‖λ‖_{b^s_{p,q}}`, the case `Ω = V` of
`Rd.modNormOn_le_coeffNorm`. -/
theorem modNorm_le_coeffNorm {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) {ι : Type*} [Countable ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {σ : ℝ} {r : ℕ} {d : ℝ} {C : ℝ≥0∞} {N : ℕ} (c : ℕ → ι → V) (a : ℕ → ι → V → ℂ)
    (coef : ℕ → ι → ℂ)
    (hN : ∀ j x (S : Finset ι), (∀ m ∈ S, coef j m ≠ 0 ∧ ‖x - c j m‖ ≤ (d + r) / 2 ^ j) →
      S.card ≤ N)
    (ha : ∀ j m, IsRegularAtom p σ r d C j (c j m) (a j m)) {f : ℕ → Lp ℂ p (volume : Measure V)}
    (hf : ∀ j, ∀ᵐ x ∂volume, f j x = ∑' m, coef j m * a j m x)
    {F : Lp ℂ p (volume : Measure V)}
    (hF : Tendsto (fun J => ∑ j ∈ Finset.range (J + 1), f j) atTop (𝓝 F))
    {s : ℝ} (hs : 0 < s) (hsσ : s < σ) {q : ℝ≥0∞} (hq : 1 ≤ q) :
    ‖F‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p r F k) ≤
      atomSynthConst p N C r s σ * coeffNorm p (finrank ℝ V) s q coef := by
  have h := modNormOn_le_coeffNorm hp MeasurableSet.univ c a coef hN ha hf hF hs hsσ hq
  have e : ∀ k, lpModulusOn p Set.univ r F k = lpModulus p r F k := fun k => modulusOn_univ r p _ _
  simpa only [Set.indicator_univ, e, ← Lp.eNorm_def] using h

/-- The zero function is a regular atom on every set at every level. -/
theorem isRegularAtomOn_zero {Ω : Set V} {p : ℝ≥0∞} {σ : ℝ} {r : ℕ} {d : ℝ} {C : ℝ≥0∞} {j : ℕ}
    {c : V} : IsRegularAtomOn Ω p σ r d C j c (0 : V → ℂ) where
  aestronglyMeasurable := aestronglyMeasurable_const
  eq_zero _ _ := rfl
  eLpNorm_le := by simp
  eLpNorm_higherDiff_le h := by
    have h0 : (fwdDiff h)^[r] (0 : V → ℂ) = 0 := by
      induction r with
      | zero => rfl
      | succ r ih =>
        rw [Function.iterate_succ_apply', ih, fwdDiff_eq_sub]
        funext x
        simp
    simp [h0]

/-- **Synthesis of one level**: for regular atoms of level `j` with overlap `N` and
`F = ∑_m λ_m a_m` in `L_p`, `0 < s < σ`:
`‖F‖_p + ‖(2^(ks) ω_r(F, 2^(-k))_p)_k‖_{ℓ_q} ≤ K 2^(j(s - n/p)) ‖λ‖_{ℓ_p}`, the case of
`Rd.modNorm_le_coeffNorm` with one nonzero level. -/
theorem modNorm_level_le {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) {ι : Type*} [Countable ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {σ : ℝ} {r : ℕ} {d : ℝ} {C : ℝ≥0∞} {N : ℕ} (j : ℕ) (c : ι → V) (a : ι → V → ℂ)
    (coef : ι → ℂ)
    (hN : ∀ x (S : Finset ι), (∀ m ∈ S, coef m ≠ 0 ∧ ‖x - c m‖ ≤ (d + r) / 2 ^ j) → S.card ≤ N)
    (ha : ∀ m, IsRegularAtom p σ r d C j (c m) (a m)) {F : Lp ℂ p (volume : Measure V)}
    (hF : ∀ᵐ x ∂volume, F x = ∑' m, coef m * a m x) {s : ℝ} (hs : 0 < s) (hsσ : s < σ)
    {q : ℝ≥0∞} (hq : 1 ≤ q) :
    ‖F‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p r F k) ≤
      atomSynthConst p N C r s σ *
        (dyadicWeight (s - finrank ℝ V / p.toReal) j * levelNorm p coef) := by
  classical
  have hp1 : 1 ≤ p := Fact.out
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  have hpos : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  set coef' : ℕ → ι → ℂ := fun i m => if i = j then coef m else 0
  set a' : ℕ → ι → V → ℂ := fun i m => if i = j then a m else 0
  set f' : ℕ → Lp ℂ p (volume : Measure V) := fun i => if i = j then F else 0
  have hN' : ∀ i x (S : Finset ι), (∀ m ∈ S, coef' i m ≠ 0 ∧ ‖x - c m‖ ≤ (d + r) / 2 ^ i) →
      S.card ≤ N := fun i x S hS => by
    by_cases hij : i = j
    · subst hij
      exact hN x S fun m hm => by simpa [coef'] using hS m hm
    · have hS0 : S = ∅ := Finset.eq_empty_of_forall_notMem fun m hm =>
        (hS m hm).1 (by simp [coef', hij])
      simp [hS0]
  have ha' : ∀ i m, IsRegularAtom p σ r d C i (c m) (a' i m) := fun i m => by
    by_cases hij : i = j
    · subst hij
      simpa [a'] using ha m
    · simpa [a', hij] using (isRegularAtomOn_zero : IsRegularAtom p σ r d C i (c m) 0)
  have hf' : ∀ i, ∀ᵐ x ∂volume, f' i x = ∑' m, coef' i m * a' i m x := fun i => by
    by_cases hij : i = j
    · subst hij
      simpa [f', coef', a'] using hF
    · filter_upwards [Lp.coeFn_zero ℂ p (volume : Measure V)] with x hx
      simp [f', coef', a', hij]
  have hF' : Tendsto (fun J => ∑ i ∈ Finset.range (J + 1), f' i) atTop (𝓝 F) := by
    refine tendsto_atTop_of_eventually_const (i₀ := j) fun J hJ => ?_
    rw [Finset.sum_ite_eq' (Finset.range (J + 1)) j (fun _ => F)]
    simp [Finset.mem_range, Nat.lt_succ_of_le hJ]
  refine (modNorm_le_coeffNorm hp (fun _ => c) (fun i => a' i) coef' hN' ha' hf' hF' hs hsσ
    hq).trans_eq ?_
  congr 1
  rw [coeffNorm]
  have hseq : (fun i => dyadicWeight (s - finrank ℝ V / p.toReal) i * levelNorm p (coef' i)) =
      fun i => if i = j then dyadicWeight (s - finrank ℝ V / p.toReal) j * levelNorm p coef
        else 0 := funext fun i => by
    by_cases hij : i = j
    · subst hij
      simp [coef']
    · have h0 : levelNorm p (coef' i) = 0 := by
        simp [levelNorm, coef', hij]
      simp [hij, h0]
  rw [hseq, ENNReal.lqNorm_ite_eq (zero_lt_one.trans_le hq).ne']

/-! ### Atoms from pointwise bounds -/

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- `‖g‖_p ≤ B μ(S)^(1/p)` for a function with `|g| ≤ B` that vanishes outside `S`. -/
theorem eLpNorm_le_of_bound_of_support {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p : ℝ≥0∞} {g : α → ℂ} (hg : AEStronglyMeasurable g μ) {S : Set α}
    (hS : ∀ x ∉ S, g x = 0) {B : ℝ≥0∞} (hB : ∀ x, ‖g x‖ₑ ≤ B) :
    eLpNorm g p μ ≤ B * μ S ^ (1 / p.toReal) := by
  have hsupp : Function.support g ⊆ S := fun x hx => by
    by_contra h
    exact (Function.mem_support.1 hx) (hS x h)
  rw [← eLpNorm_restrict_eq_of_support_subset hg hsupp]
  refine (eLpNorm_le_of_ae_eNorm_bound hg.restrict (Eventually.of_forall hB)).trans_eq ?_
  rw [Measure.restrict_apply_univ, one_div, smul_eq_mul]

/-- **Atoms on `Ω` from pointwise bounds**: a function that vanishes outside `closedBall(c, d
2^(-j))`
with `|a| ≤ A` on `Ω` and `|Δ_h^r a(x)| ≤ A min(1, (2^j ‖h‖)^σ)` at the points `x` whose steps stay
in `Ω` is a regular atom on `Ω` with the constant `A ((r + 1) d^n |B_1|)^(1/p)`. The support of
`Δ_h^r a` lies in `r + 1` translated balls. -/
theorem isRegularAtomOn_of_pointwise {p : ℝ≥0∞} {σ : ℝ} {r : ℕ} {d : ℝ} (hd : 0 ≤ d)
    {A : ℝ≥0∞} {j : ℕ} {c : V} {a : V → ℂ} {Ω : Set V} (hΩ : MeasurableSet Ω)
    (hm : AEStronglyMeasurable a volume)
    (h0 : ∀ x, d / 2 ^ j < ‖x - c‖ → a x = 0) (hle : ∀ x ∈ Ω, ‖a x‖ₑ ≤ A)
    (hdiff : ∀ h, ∀ x ∈ stepSet Ω r h,
      ‖(fwdDiff h)^[r] a x‖ₑ ≤ A * min 1 (ENNReal.ofReal (2 ^ j * ‖h‖) ^ σ)) :
    IsRegularAtomOn Ω p σ r d (A * (((r + 1 : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (d ^ finrank ℝ V) *
      volume (ball (0 : V) 1))) ^ (1 / p.toReal)) j c a := by
  set K := ENNReal.ofReal (d ^ finrank ℝ V) * volume (ball (0 : V) 1)
  have hexp : 0 ≤ 1 / p.toReal := div_nonneg zero_le_one ENNReal.toReal_nonneg
  have hball : ∀ z : V, volume (closedBall z (d / 2 ^ j)) ^ (1 / p.toReal) ≤
      (((r + 1 : ℕ) : ℝ≥0∞) * K) ^ (1 / p.toReal) * dyadicWeight (-(finrank ℝ V / p.toReal)) j :=
    fun z => by
      rw [volume_closedBall_div_two_pow hd j z, ← ENNReal.rpow_mul_dyadicWeight_neg]
      refine ENNReal.rpow_le_rpow ?_ hexp
      rw [mul_assoc (((r + 1 : ℕ) : ℝ≥0∞))]
      exact le_mul_of_one_le_left' (by exact_mod_cast Nat.succ_pos r)
  refine ⟨hm, h0, ?_, fun h => ?_⟩
  · refine (eLpNorm_le_of_bound_of_support (hm.indicator hΩ) (S := closedBall c (d / 2 ^ j))
      (B := A) (fun x hx => ?_) (fun x => ?_)).trans ?_
    · rw [mem_closedBall, dist_eq_norm, not_le] at hx
      exact Set.indicator_apply_eq_zero.2 fun _ => h0 x hx
    · by_cases hx : x ∈ Ω
      · rw [Set.indicator_of_mem hx]
        exact hle x hx
      · rw [Set.indicator_of_notMem hx, eNorm_zero]
        exact zero_le
    · rw [mul_assoc]
      exact mul_le_mul' le_rfl (hball c)
  · set T := ⋃ l ∈ Finset.range (r + 1), closedBall (c - (l : ℝ) • h) (d / 2 ^ j)
    have hT : ∀ x ∉ T, (fwdDiff h)^[r] a x = 0 := fun x hx => by
      rw [higherDiff_apply]
      refine Finset.sum_eq_zero fun l hl => ?_
      have hxl : x ∉ closedBall (c - (l : ℝ) • h) (d / 2 ^ j) := fun hx' =>
        hx (Set.mem_biUnion hl hx')
      rw [mem_closedBall, dist_eq_norm, not_le] at hxl
      rw [h0 _ (by rwa [show x + (l : ℝ) • h - c = x - (c - (l : ℝ) • h) by abel]), mul_zero]
    have hvol : volume T ^ (1 / p.toReal) ≤
        (((r + 1 : ℕ) : ℝ≥0∞) * K) ^ (1 / p.toReal) *
          dyadicWeight (-(finrank ℝ V / p.toReal)) j := by
      rw [← ENNReal.rpow_mul_dyadicWeight_neg]
      refine ENNReal.rpow_le_rpow ((measure_biUnion_finset_le _ _).trans_eq ?_) hexp
      simp_rw [volume_closedBall_div_two_pow hd j]
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      simp only [K]
      push_cast
      ring
    refine (eLpNorm_le_of_bound_of_support
      ((aestronglyMeasurable_higherDiff hm r h).indicator (measurableSet_stepSet hΩ r h))
      (B := A * min 1 (ENNReal.ofReal (2 ^ j * ‖h‖) ^ σ))
      (fun x hx => Set.indicator_apply_eq_zero.2 fun _ => hT x hx) (fun x => ?_)).trans ?_
    · by_cases hx : x ∈ stepSet Ω r h
      · rw [Set.indicator_of_mem hx]
        exact hdiff h x hx
      · rw [Set.indicator_of_notMem hx, eNorm_zero]
        exact zero_le
    calc A * min 1 (ENNReal.ofReal (2 ^ j * ‖h‖) ^ σ) * volume T ^ (1 / p.toReal)
        ≤ A * min 1 (ENNReal.ofReal (2 ^ j * ‖h‖) ^ σ) * ((((r + 1 : ℕ) : ℝ≥0∞) * K) ^
            (1 / p.toReal) * dyadicWeight (-(finrank ℝ V / p.toReal)) j) :=
          mul_le_mul' le_rfl hvol
      _ = _ := by ring

/-- **Atoms from pointwise bounds**: a function that vanishes outside `closedBall(c, d 2^(-j))` with
`|a| ≤ A` and `|Δ_h^r a| ≤ A min(1, (2^j ‖h‖)^σ)` is a regular atom with the constant
`A ((r + 1) d^n |B_1|)^(1/p)`, the case `Ω = V` of `Rd.isRegularAtomOn_of_pointwise`. -/
theorem isRegularAtom_of_pointwise {p : ℝ≥0∞} {σ : ℝ} {r : ℕ} {d : ℝ} (hd : 0 ≤ d)
    {A : ℝ≥0∞} {j : ℕ} {c : V} {a : V → ℂ} (hm : AEStronglyMeasurable a volume)
    (h0 : ∀ x, d / 2 ^ j < ‖x - c‖ → a x = 0) (hle : ∀ x, ‖a x‖ₑ ≤ A)
    (hdiff : ∀ h x, ‖(fwdDiff h)^[r] a x‖ₑ ≤ A * min 1 (ENNReal.ofReal (2 ^ j * ‖h‖) ^ σ)) :
    IsRegularAtom p σ r d (A * (((r + 1 : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (d ^ finrank ℝ V) *
      volume (ball (0 : V) 1))) ^ (1 / p.toReal)) j c a :=
  isRegularAtomOn_of_pointwise hd MeasurableSet.univ hm h0 (fun x _ => hle x)
    (fun h x _ => hdiff h x)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **Smooth atoms**: a smooth function vanishing outside `closedBall(c, d 2^(-j))` with
`‖D^l a‖ ≤ A 2^(jl)` for `l ≤ r` satisfies the pointwise bounds of `Rd.isRegularAtom_of_pointwise`
with exponent `σ = r` and the constant `2^r A`: `|Δ_h^r a| ≤ A (2^j ‖h‖)^r` by the
mean value theorem and `|Δ_h^r a| ≤ 2^r A`. -/
theorem enorm_higherDiff_le_of_iteratedFDeriv {a : V → ℂ}
    (ha : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a) {r j : ℕ} {A : ℝ} (hA : 0 ≤ A)
    (hD : ∀ l ≤ r, ∀ x, ‖iteratedFDeriv ℝ l a x‖ ≤ A * 2 ^ (j * l)) (h x : V) :
    ‖(fwdDiff h)^[r] a x‖ₑ ≤
      ENNReal.ofReal (2 ^ r * A) * min 1 (ENNReal.ofReal (2 ^ j * ‖h‖) ^ (r : ℝ)) := by
  have h1 : ‖(fwdDiff h)^[r] a x‖ ≤ A * 2 ^ (j * r) * ‖h‖ ^ r :=
    norm_higherDiff_le_of_iteratedFDeriv ha (hD r le_rfl) h x
  have h2 : ‖(fwdDiff h)^[r] a x‖ₑ ≤ ENNReal.ofReal (2 ^ r * A) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat]
    refine enorm_higherDiff_le_of_bound (fun y => ?_) r h x
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (by simpa using hD 0 (Nat.zero_le r) y)
  rcases le_total 1 (ENNReal.ofReal (2 ^ j * ‖h‖) ^ (r : ℝ)) with hmin | hmin
  · rwa [min_eq_left hmin, mul_one]
  · rw [min_eq_right hmin, ← ofReal_norm,
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (Nat.cast_nonneg r),
      Real.rpow_natCast, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal (h1.trans ?_)
    rw [mul_pow, pow_mul]
    have hr : (1 : ℝ) ≤ 2 ^ r := one_le_pow₀ one_le_two
    calc A * (2 ^ j) ^ r * ‖h‖ ^ r = 1 * (A * ((2 ^ j) ^ r * ‖h‖ ^ r)) := by ring
      _ ≤ 2 ^ r * (A * ((2 ^ j) ^ r * ‖h‖ ^ r)) :=
          mul_le_mul_of_nonneg_right hr (by positivity)
      _ = 2 ^ r * A * ((2 ^ j) ^ r * ‖h‖ ^ r) := by ring

end Rd
