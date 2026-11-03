/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import LeanPool.TrilinearHilbertTransform.Auto.Sec092ChartFourierSeparation.SepOneAtomExpansion

/-!
# Trilinear Hilbert transform: progressionSeparation
-/

@[expose] public section

section
open scoped FourierTransform
namespace TrilinearHT.Auto
open MeasureTheory Metric
open scoped FourierTransform

open scoped Classical in
private def ProgressionSeparationConclusion12Statement : Prop :=
  ∀ (c₀ : ℕ)
    (_ : (1 : ℕ) ≤ c₀)
    (ψ : ℝ → ℝ)
    (Kψ : ℕ)
    (_ : (1 : ℕ) ≤ Kψ)
    (hψ : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (_ : ∀ (x : ℝ), |ψ x| ≤ (1 : ℝ))
    (hψ0 : ∀ (x : ℝ), (2 : ℝ) ≤ |x| → ψ x = (0 : ℝ))
    (_ : ∀ (i : ℕ) (x : ℝ), |iteratedDeriv i ψ x| ≤ ((↑Kψ : ℝ) * ((↑i : ℝ) + (1 : ℝ))) ^ (Kψ
      * (i + (1 : ℕ))))
    (_ : ℕ)
    (Da : ℕ)
    (_ : (1 : ℕ) ≤ Da),
  let K : ℝ :=
    sepFactorConst Kψ
  ∀ (_ : (0 : ℝ) ≤ K),
  let Dc : ℕ :=
    ⌈Real.log (K * (21175 : ℝ) + (1 : ℝ))⌉₊
  ∀ (d : ℕ)
    (e : ℕ)
    (H : ℝ)
    (A : QuadraticChartData d)
    (A' : QuadraticChartData e)
    (_ : QuadraticChartComplexity c₀ H A)
    (_ : QuadraticChartComplexity c₀ H A')
    (i : ℤ)
    (k : ℤ)
    (a : ℤ)
    (b : ℤ)
    (_ : |i| ≤ (3 : ℤ))
    (_ : |k| ≤ (3 : ℤ))
    (_ : |a| ≤ (3 : ℤ))
    (_ : |b| ≤ (3 : ℤ)),
  let X : ℝ :=
    (1 : ℝ) + Real.log H
  let Ki : Finset (Fin d → ℤ) :=
    slowValueBox d ⌈H + (1 : ℝ) + |(↑(i - a) : ℝ)|⌉₊
  let Kb : Finset (Fin d → ℤ) :=
    slowValueBox d ⌈(2 : ℝ) + |(↑(b - a) : ℝ)|⌉₊
  let Ki' : Finset (Fin e → ℤ) :=
    slowValueBox e ⌈H + (1 : ℝ) + |(↑(k - a) : ℝ)|⌉₊
  let Kb' : Finset (Fin e → ℤ) :=
    slowValueBox e ⌈(2 : ℝ) + |(↑(b - a) : ℝ)|⌉₊
  ∀ (_ : (1 : ℝ) ≤ H)
    (_ : (1 : ℝ) ≤ X),
  let Dm : ℕ :=
    Dc + (2 : ℕ) * Da + (4 : ℕ)
  ∀ (_ : Dm = Dc + (2 : ℕ) * Da + (4 : ℕ)),
  ∀ (q : ((↥Ki × ↥Kb) × (Fin (d + d + d) → ℤ)) × (↥Ki' × ↥Kb') × (Fin (e + e + e) →
    ℤ)), QuadraticChartComplexity ((2 : ℕ) * Kψ) ((Real.exp ((↑Dm : ℝ) * X ^ Dm) *
    (fun (q : ((↥Ki × ↥Kb) × (Fin (d + d + d) → ℤ)) × (↥Ki' × ↥Kb') × (Fin (e + e + e)
    → ℤ)) => max ((1 : ℝ) + frequencyLength q.1.2) ((1 : ℝ) + frequencyLength q.2.2))
    q) ^ (6 : ℕ)) ((fun (q : ((↥Ki × ↥Kb) × (Fin (d + d + d) → ℤ)) × (↥Ki' × ↥Kb') ×
    (Fin (e + e + e) → ℤ)) => sepPairChartA A A' hψ hψ0 i k a b (↑q.1.1.1 : Fin d → ℤ)
    (↑q.2.1.1 : Fin e → ℤ) q.1.2 q.2.2) q) ∧ QuadraticChartComplexity ((2 : ℕ) * Kψ)
    ((Real.exp ((↑Dm : ℝ) * X ^ Dm) * (fun (q : ((↥Ki × ↥Kb) × (Fin (d + d + d) → ℤ))
    × (↥Ki' × ↥Kb') × (Fin (e + e + e) → ℤ)) => max ((1 : ℝ) + frequencyLength q.1.2)
    ((1 : ℝ) + frequencyLength q.2.2)) q) ^ (6 : ℕ)) ((fun (q : ((↥Ki × ↥Kb) × (Fin (d
    + d + d) → ℤ)) × (↥Ki' × ↥Kb') × (Fin (e + e + e) → ℤ)) => sepPairChartB A A' hψ
    hψ0 i k a b (↑q.1.1.1 : Fin d → ℤ) (↑q.1.1.2 : Fin d → ℤ) (↑q.2.1.1 : Fin e → ℤ)
    (↑q.2.1.2 : Fin e → ℤ) q.1.2 q.2.2) q) ∧ QuadraticChartComplexity ((2 : ℕ) * Kψ)
    ((Real.exp ((↑Dm : ℝ) * X ^ Dm) * (fun (q : ((↥Ki × ↥Kb) × (Fin (d + d + d) → ℤ))
    × (↥Ki' × ↥Kb') × (Fin (e + e + e) → ℤ)) => max ((1 : ℝ) + frequencyLength q.1.2)
    ((1 : ℝ) + frequencyLength q.2.2)) q) ^ (6 : ℕ)) ((fun (q : ((↥Ki × ↥Kb) × (Fin (d
    + d + d) → ℤ)) × (↥Ki' × ↥Kb') × (Fin (e + e + e) → ℤ)) => sepPairChartT A A' hψ
    hψ0 i k a b q.1.2 q.2.2) q)




private theorem progressionSeparation_conclusion_12 : ProgressionSeparationConclusion12Statement
  := by
  classical
  intro c₀ hc ψ Kψ hKψ hψ hψ1' hψ0 hψd Kρ Da hDa K hK0 Dc d e H A A' hA hA' i k a b hi hk ha hb X
    Ki Kb Ki' Kb' hH1 hX1 Dm hDm q
  have hsz : 1 ≤ max (1 + frequencyLength q.1.2) (1 + frequencyLength q.2.2) := by
    have := frequencyLength_nonneg q.1.2
    exact le_trans (by linarith) (le_max_left _ _)
  refine sepPairCharts_complexity hA hA' hψ hψ1' hψ0 hKψ hψd i k a b q.1.1.1 q.1.1.2
    q.2.1.1 q.2.1.2 q.1.2 q.2.2 ?_
  set sz := max (1 + frequencyLength q.1.2) (1 + frequencyLength q.2.2) with hsz'
  have hQ : max (sepQ i a b) (sepQ k a b) ^ 2 ≤ 3025 := by
    have h1 := sepQ_le hi ha hb
    have h2 := sepQ_le hk ha hb
    have h0 := one_le_sepQ i a b
    have : max (sepQ i a b) (sepQ k a b) ≤ 55 := max_le h1 h2
    have : 0 ≤ max (sepQ i a b) (sepQ k a b) := le_trans (by linarith) (le_max_left _ _)
    nlinarith
  have hlogH0 : 0 ≤ Real.log H := Real.log_nonneg hH1
  have hHX : H ^ 2 ≤ Real.exp (2 * X) := by
    have : H = Real.exp (Real.log H) := (Real.exp_log (by linarith)).symm
    rw [this, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    push_cast
    simp only [X]; nlinarith only
  have hl1 : frequencyLength q.1.2 ≤ sz := by
    have := le_max_left (1 + frequencyLength q.1.2) (1 + frequencyLength q.2.2)
    rw [← hsz'] at this; linarith
  have hl2 : frequencyLength q.2.2 ≤ sz := by
    have := le_max_right (1 + frequencyLength q.1.2) (1 + frequencyLength q.2.2)
    rw [← hsz'] at this; linarith
  have hp1 : ∑ l, |(q.1.2 l : ℝ)| ≤ (d + d + d : ℕ) * sz :=
    (sum_abs_le_card_mul_length q.1.2).trans (mul_le_mul_of_nonneg_left hl1 (Nat.cast_nonneg _))
  have hp2 : ∑ l, |(q.2.2 l : ℝ)| ≤ (e + e + e : ℕ) * sz :=
    (sum_abs_le_card_mul_length q.2.2).trans (mul_le_mul_of_nonneg_left hl2 (Nat.cast_nonneg _))
  have hdX : (d : ℝ) ≤ X := by have := hA.dimension; simp only [X]; linarith
  have heX : (e : ℝ) ≤ X := by have := hA'.dimension; simp only [X]; linarith
  have hsum : 1 + ∑ l, |(q.1.2 l : ℝ)| + ∑ l, |(q.2.2 l : ℝ)| ≤ 7 * Real.exp X * sz := by
    push_cast at hp1 hp2
    have h7 : 1 + 6 * X ≤ 7 * Real.exp X := by
      have := Real.add_one_le_exp X; nlinarith only [hX1, this]
    nlinarith only [hsz, hdX, heX, hp1, hp2, h7]
  have hS0 : 0 ≤ 1 + ∑ l, |(q.1.2 l : ℝ)| + ∑ l, |(q.2.2 l : ℝ)| := by positivity
  calc K * max (sepQ i a b) (sepQ k a b) ^ 2 * H ^ 2 *
        (1 + ∑ l, |(q.1.2 l : ℝ)| + ∑ l, |(q.2.2 l : ℝ)|) ≤
      K * 3025 * Real.exp (2 * X) * (7 * Real.exp X * sz) := by gcongr
    _ = (K * 21175) * Real.exp (3 * X) * sz := by
        have h3 : Real.exp (3 * X) = Real.exp (2 * X) * Real.exp X := by
          rw [← Real.exp_add]; congr 1; ring
        rw [h3]; ring
    _ ≤ Real.exp (Dm * X ^ Dm) * sz := by
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        have hc : K * 21175 ≤ Real.exp (Dc) := by
          have h1 : K * 21175 ≤ K * 21175 + 1 := by linarith
          refine h1.trans ?_
          rw [← Real.exp_log (by positivity : (0 : ℝ) < K * 21175 + 1)]
          exact Real.exp_le_exp.mpr (Nat.le_ceil _)
        calc K * 21175 * Real.exp (3 * X) ≤ Real.exp Dc * Real.exp (3 * X) :=
              mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le
          _ ≤ Real.exp ((Dc + 3 : ℝ) * X ^ 1) := by
              rw [← Real.exp_add]
              apply Real.exp_le_exp.mpr
              have : (0 : ℝ) ≤ Dc := Nat.cast_nonneg _
              rw [pow_one]; nlinarith only [hX1]
          _ ≤ Real.exp (Dm * X ^ Dm) := exp_poly_le hX1 (by omega) (by
              rw [hDm]; push_cast; linarith)


/-- Blueprint lem:separation (Declaration separation, line 1413,
`THT.Chart.progressionSeparation`): two atoms in distinct slots `i, k` have an exact
absolutely convergent expansion `φ_i(y_i) φ_k(y_k) = Σ c ψ_a(y_a) ψ_b(y_b) Q(t)` with bounded
factor atoms; the coefficients have total mass and shell tails `D T^{-100}`, and the factors
of a term in shell `T` have complexity at most `(DT)^6` at a fixed Gevrey order, with `D`
quasipolynomial in `H`. The single-scale form bound, the separated phase and the uniform
kernel approximation are `separated_form_le`, `separatedPhase` and `separatedKernelApprox`. -/
theorem progressionSeparation (c₀ : ℕ) (hc : 1 ≤ c₀) :
    ∃ c₁ D : ℕ, 1 ≤ c₁ ∧ 1 ≤ D ∧ ∀ {d e : ℕ} (H : ℝ) (A : QuadraticChartData d)
      (A' : QuadraticChartData e), 1 ≤ d → 1 ≤ e → QuadraticChartComplexity c₀ H A →
      QuadraticChartComplexity c₀ H A' → ∀ i k a b : ℤ, a ≠ b → |i| ≤ 3 → |k| ≤ 3 →
      |a| ≤ 3 → |b| ≤ 3 →
      let X := 1 + Real.log H
      ∃ (τ : Type) (_ : Countable τ) (cf : τ → ℂ) (φa φb φt : τ → QuadraticChartData (d + e))
        (size : τ → ℝ),
        (∀ x t : ℝ, HasSum (fun q => cf q * quadraticChartAtom (φa q) (x + a * t) *
            quadraticChartAtom (φb q) (x + b * t) * quadraticChartAtom (φt q) t)
          (quadraticChartAtom A (x + i * t) * quadraticChartAtom A' (x + k * t))) ∧
        (∀ q, IsBoundedQuadraticChart (φa q) ∧ IsBoundedQuadraticChart (φb q) ∧
          IsBoundedQuadraticChart (φt q)) ∧
        (∀ q, 1 ≤ size q) ∧
        Summable (fun q => ‖cf q‖) ∧ (∑' q, ‖cf q‖) ≤ Real.exp (D * X ^ D) ∧
        (∀ T : ℝ, 1 ≤ T → (∑' q, if T ≤ size q then ‖cf q‖ else 0) ≤
          Real.exp (D * X ^ D) / T ^ 100) ∧
        (∀ q, QuadraticChartComplexity c₁ ((Real.exp (D * X ^ D) * size q) ^ 6) (φa q) ∧
          QuadraticChartComplexity c₁ ((Real.exp (D * X ^ D) * size q) ^ 6) (φb q) ∧
          QuadraticChartComplexity c₁ ((Real.exp (D * X ^ D) * size q) ^ 6) (φt q)) ∧
        (∀ T : ℝ, 1 ≤ T → ∃ Qs : Finset τ, (∀ q, size q ≤ T → q ∈ Qs) ∧
          (Qs.card : ℝ) ≤ Real.exp (10 * X ^ 2) * (3 * T) ^ (3 * (d + e))) ∧
        ∀ q, (φt q).horizontal = Fin.append A.horizontal A'.horizontal ∧
          (φt q).matrix = chartBlockMatrix (((i - a) * (i - b) : ℚ) • A.matrix)
            (((k - a) * (k - b) : ℚ) • A'.matrix) ∧
          (φt q).quadratic = (((i - a) * (i - b) : ℚ) : ℝ) * A.quadratic +
            (((k - a) * (k - b) : ℚ) : ℝ) * A'.quadratic := by
  obtain ⟨ψ, Kψ, hKψ, hψ, hψ1', hψ1, hψ0, hψd⟩ := exists_plateau_cutoff
  obtain ⟨Kρ, hKρ, hρd⟩ := gevreyPartition_exists_derivative_bound
  obtain ⟨Da, hDa, hatom⟩ := sepAtomFamily_bounds c₀ hc hψ hψ1' hψ1 hψ0 hKψ hψd hKρ hρd
  set K := sepFactorConst Kψ with hK
  have hK0 : 0 ≤ K := by unfold sepFactorConst at hK; rw [hK]; positivity
  set Dc : ℕ := ⌈Real.log (K * 21175 + 1)⌉₊ with hDc
  refine ⟨2 * Kψ, Dc + 2 * Da + 4, by omega, by omega, ?_⟩
  intro d e H A A' hd he hA hA' i k a b hab hi hk ha hb X
  obtain ⟨hfs, hfm, hft⟩ := hatom H A hd hA i a b hi ha hb
  obtain ⟨hgs, hgm, hgt⟩ := hatom H A' he hA' k a b hk ha hb
  set Ki := slowValueBox d ⌈H + 1 + |((i - a : ℤ) : ℝ)|⌉₊ with hKi
  set Kb := slowValueBox d ⌈2 + |((b - a : ℤ) : ℝ)|⌉₊ with hKb
  set Ki' := slowValueBox e ⌈H + 1 + |((k - a : ℤ) : ℝ)|⌉₊ with hKi'
  set Kb' := slowValueBox e ⌈2 + |((b - a : ℤ) : ℝ)|⌉₊ with hKb'
  set fA : (Ki × Kb) × (Fin (d + d + d) → ℤ) → ℂ := fun q =>
    sepCoeff A.amplitude ψ i a b q.1.1 q.1.2 q.2 * ((6 ^ d : ℝ) : ℂ) ^ 3 with hfA
  set fB : (Ki' × Kb') × (Fin (e + e + e) → ℤ) → ℂ := fun q =>
    sepCoeff A'.amplitude ψ k a b q.1.1 q.1.2 q.2 * ((6 ^ e : ℝ) : ℂ) ^ 3 with hfB
  have hH1 : 1 ≤ H := by linarith [hA.lower, Real.add_one_le_exp (2 : ℝ)]
  have hX1 : 1 ≤ X := by have := Real.log_nonneg hH1; simp only [X]; linarith
  set EA := Real.exp (Da * X ^ Da) with hEA
  have hEA1 : 1 ≤ EA := Real.one_le_exp (by positivity)
  set Dm := Dc + 2 * Da + 4 with hDm
  have hEA2 : EA * EA ≤ Real.exp (Dm * X ^ Dm) := by
    rw [hEA, ← Real.exp_add]
    refine (Real.exp_le_exp.mpr (le_of_eq (by ring))).trans
      (exp_poly_le (c := 2 * Da) hX1 (by omega) (by rw [hDm]; push_cast; linarith))
  have hEA3 : 2 * (EA * EA) ≤ Real.exp (Dm * X ^ Dm) := by
    have h2 : 2 * (EA * EA) ≤ Real.exp ((2 * Da + 1 : ℝ) * X ^ Da) := by
      rw [hEA, ← Real.exp_add]
      have h3 : (2 : ℝ) ≤ Real.exp (X ^ Da) := by
        have := Real.add_one_le_exp (X ^ Da)
        have : (1 : ℝ) ≤ X ^ Da := one_le_pow₀ hX1
        linarith
      calc 2 * Real.exp (Da * X ^ Da + Da * X ^ Da) ≤
          Real.exp (X ^ Da) * Real.exp (Da * X ^ Da + Da * X ^ Da) :=
            mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
        _ = Real.exp ((2 * Da + 1 : ℝ) * X ^ Da) := by rw [← Real.exp_add]; congr 1; ring
    exact h2.trans (exp_poly_le hX1 (by omega) (by rw [hDm]; push_cast; linarith))
  refine ⟨((Ki × Kb) × (Fin (d + d + d) → ℤ)) × ((Ki' × Kb') × (Fin (e + e + e) → ℤ)),
    inferInstance, fun q => fA q.1 * fB q.2,
    fun q => sepPairChartA A A' hψ hψ0 i k a b q.1.1.1 q.2.1.1 q.1.2 q.2.2,
    fun q => sepPairChartB A A' hψ hψ0 i k a b q.1.1.1 q.1.1.2 q.2.1.1 q.2.1.2 q.1.2 q.2.2,
    fun q => sepPairChartT A A' hψ hψ0 i k a b q.1.2 q.2.2,
    fun q => max (1 + frequencyLength q.1.2) (1 + frequencyLength q.2.2), ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, fun q => ⟨rfl, rfl, rfl⟩⟩
  · intro x t
    have h := sep_pair_expansion_normalized hd he A A' hA.support hA'.support hψ hψ1' hψ1 hψ0
      i k a b hab x t
    rw [← Equiv.hasSum_iff (Equiv.prodProdProdComm _ _ _ _)] at h
    convert h using 1
    funext q
    simp only [Function.comp, Equiv.prodProdProdComm_apply, hfA, hfB]
    ring
  · intro q
    exact sepPairCharts_bounded A A' hψ hψ1' hψ0 i k a b q.1.1.1 q.1.1.2 q.2.1.1 q.2.1.2 q.1.2
      q.2.2
  · intro q
    have := frequencyLength_nonneg q.1.2
    exact le_trans (by linarith) (le_max_left _ _)
  · exact (product_family_tail fA fB hfs hgs (fun x => 1 + frequencyLength x.2)
      (fun y => 1 + frequencyLength y.2) 1 (hft 1 le_rfl).1 (hgt 1 le_rfl).1).1
  · obtain ⟨-, hm, -⟩ := product_family_tail fA fB hfs hgs (fun x => 1 + frequencyLength x.2)
      (fun y => 1 + frequencyLength y.2) 1 (hft 1 le_rfl).1 (hgt 1 le_rfl).1
    rw [hm]
    exact (mul_le_mul hfm hgm (tsum_nonneg fun _ => norm_nonneg _) (by linarith)).trans hEA2
  · intro T hT
    obtain ⟨-, -, htl⟩ := product_family_tail fA fB hfs hgs (fun x => 1 + frequencyLength x.2)
      (fun y => 1 + frequencyLength y.2) T (hft T hT).1 (hgt T hT).1
    have hT0 : 0 < T ^ 100 := by positivity
    have hMa : 0 ≤ ∑' x, ‖fA x‖ := tsum_nonneg fun _ => norm_nonneg _
    have hta : 0 ≤ ∑' x, (if T ≤ 1 + frequencyLength x.2 then ‖fA x‖ else 0) :=
      tsum_nonneg fun x => by split_ifs <;> simp
    refine htl.trans ?_
    calc (∑' x, if T ≤ 1 + frequencyLength x.2 then ‖fA x‖ else 0) * (∑' y, ‖fB y‖) +
          (∑' x, ‖fA x‖) * ∑' y, (if T ≤ 1 + frequencyLength y.2 then ‖fB y‖ else 0) ≤
        EA / T ^ 100 * EA + EA * (EA / T ^ 100) := by
          gcongr
          · exact (hft T hT).2
          · exact (hgt T hT).2
      _ = 2 * (EA * EA) / T ^ 100 := by ring
      _ ≤ Real.exp (Dm * X ^ Dm) / T ^ 100 := div_le_div_of_nonneg_right hEA3 hT0.le
  · expose_names
    exact @progressionSeparation_conclusion_12 c₀ hc ψ Kψ hKψ hψ hψ1' hψ0 hψd Kρ Da hDa hK0 d e H
      A A' hA hA' i k a b hi hk ha hb hH1 hX1 hDm
  · intro T hT
    have hH7 : 7 ≤ H := by
      have he := Real.exp_one_gt_d9
      have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      have : (7 : ℝ) ≤ Real.exp 1 ^ 2 := by nlinarith only [he]
      linarith [hA.lower]
    refine ⟨((Finset.univ : Finset (↥Ki × ↥Kb)) ×ˢ frequencyBox (d + d + d) ⌊T⌋₊) ×ˢ
      ((Finset.univ : Finset (↥Ki' × ↥Kb')) ×ˢ frequencyBox (e + e + e) ⌊T⌋₊),
      fun q hq => ?_, ?_⟩
    · have h1 := le_max_left (1 + frequencyLength q.1.2) (1 + frequencyLength q.2.2)
      have h2 := le_max_right (1 + frequencyLength q.1.2) (1 + frequencyLength q.2.2)
      have hf1 : frequencyLength q.1.2 ≤ (⌊T⌋₊ : ℝ) := by
        have := Nat.lt_floor_add_one T; linarith
      have hf2 : frequencyLength q.2.2 ≤ (⌊T⌋₊ : ℝ) := by
        have := Nat.lt_floor_add_one T; linarith
      exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _,
        mem_frequencyBox_of_length_le hf1⟩, Finset.mem_product.mpr ⟨Finset.mem_univ _,
        mem_frequencyBox_of_length_le hf2⟩⟩
    · rw [Finset.card_product, Finset.card_product, Finset.card_product, Finset.card_univ,
        Finset.card_univ, card_frequencyBox, card_frequencyBox]
      push_cast
      have hc1 := slowBox_pair_card_exp_le (d := d) hH7 hA.dimension i a b hi ha hb
      have hc2 := slowBox_pair_card_exp_le (d := e) hH7 hA'.dimension k a b hk ha hb
      have hT3 : (2 * (⌊T⌋₊ : ℝ) + 1) ≤ 3 * T := by
        have := Nat.floor_le (show 0 ≤ T by linarith); linarith
      have hb1 : (2 * (⌊T⌋₊ : ℝ) + 1) ^ (d + d + d) ≤ (3 * T) ^ (3 * d) := by
        rw [show d + d + d = 3 * d by ring]
        exact pow_le_pow_left₀ (by positivity) hT3 _
      have hb2 : (2 * (⌊T⌋₊ : ℝ) + 1) ^ (e + e + e) ≤ (3 * T) ^ (3 * e) := by
        rw [show e + e + e = 3 * e by ring]
        exact pow_le_pow_left₀ (by positivity) hT3 _
      have hX2 : Real.exp (5 * (1 + Real.log H) ^ 2) * Real.exp (5 * (1 + Real.log H) ^ 2) =
          Real.exp (10 * X ^ 2) := by rw [← Real.exp_add]; simp only [X]; ring_nf
      have hTpow : (3 * T) ^ (3 * d) * (3 * T) ^ (3 * e) = (3 * T) ^ (3 * (d + e)) := by
        rw [← pow_add]; ring_nf
      calc (Fintype.card (↥Ki × ↥Kb) : ℝ) * (2 * (⌊T⌋₊ : ℝ) + 1) ^ (d + d + d) *
            ((Fintype.card (↥Ki' × ↥Kb') : ℝ) * (2 * (⌊T⌋₊ : ℝ) + 1) ^ (e + e + e))
          ≤ Real.exp (5 * (1 + Real.log H) ^ 2) * (3 * T) ^ (3 * d) *
            (Real.exp (5 * (1 + Real.log H) ^ 2) * (3 * T) ^ (3 * e)) := by
            gcongr
        _ = Real.exp (10 * X ^ 2) * (3 * T) ^ (3 * (d + e)) := by
            rw [← hX2, ← hTpow]; ring

end TrilinearHT.Auto

end
