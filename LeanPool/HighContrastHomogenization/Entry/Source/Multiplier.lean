/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Source.Subdivision
public import LeanPool.HighContrastHomogenization.Entry.Source.GaugeMoments
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# High-contrast homogenization: Entry.Source.Multiplier

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The source stopping minimum

Near `e.source.multiplier`, `l.source.whitney`. The finite source-center success events,
stationary union and Markov bounds, and measurable least successful offset.
The multiplier is returned as a characterized existential witness: there is no new
definition. Failure at every depth receives representative offset zero;
the source moment estimate proves that exceptional event null.
-/

open HCPolySupport.HighContrast (CoeffSpace measurable_translateCoeff translateCoeff)
open HCPolySupport.HighContrast (centeredCube standardCellCenter)
namespace HCPolySupport.HighContrast.Source
open Set MeasureTheory Filter Geometry
open scoped ENNReal
noncomputable section

/-- The success events in the printed minimum are measurable. -/
theorem measurableSet_source_success {d : ℕ} (S : CoeffSpace d → ℝ)
    (hS : Measurable S) (jStar r : ℕ) :
    MeasurableSet {a | ∀ w : Fin d → ℤ,
      standardCellCenter ((jStar + r : ℕ) : ℤ) w ∈
        centeredCube d ((2 * jStar + r : ℕ) : ℤ) →
      S (translateCoeff (fun i => (3 : ℤ) ^ (jStar + r) * w i) a) ≤
        (3 : ℝ) ^ (jStar + r)} := by
  simp only [ofPred_forall]
  apply MeasurableSet.iInter
  intro w
  apply MeasurableSet.iInter
  intro _
  exact measurableSet_le (hS.comp (measurable_translateCoeff _)) measurable_const

/-- Stationarity and Markov's inequality bound failure at one depth. Independence is unused. -/
theorem source_failure_probability_le {d : ℕ} (P : Measure (CoeffSpace d))
    [IsProbabilityMeasure P] (S : CoeffSpace d → ℝ) (hS : Measurable S)
    (hS0 : ∀ a, 0 ≤ S a) (hstat : IsStationaryLaw P)
    (p : ℝ) (hp : 0 < p) (hi : Integrable (fun a => S a ^ p) P)
    (jStar r : ℕ) :
    P.real {a | ¬ ∀ w : Fin d → ℤ,
      standardCellCenter ((jStar + r : ℕ) : ℤ) w ∈
        centeredCube d ((2 * jStar + r : ℕ) : ℤ) →
      S (translateCoeff (fun i => (3 : ℤ) ^ (jStar + r) * w i) a) ≤
        (3 : ℝ) ^ (jStar + r)} ≤
      (3 : ℝ) ^ (d * jStar) * (∫ a, S a ^ p ∂P) /
        ((3 : ℝ) ^ (jStar + r)) ^ p := by
  classical
  let W : Set (Fin d → ℤ) := {w | standardCellCenter ((jStar + r : ℕ) : ℤ) w ∈
    centeredCube d ((2 * jStar + r : ℕ) : ℤ)}
  let hW := (sourceCenterSet_finite_card d jStar r).1
  let F := hW.toFinset
  let t : ℝ := (3 : ℝ) ^ (jStar + r)
  have ht : 0 < t := by dsimp [t]; positivity
  have htp : 0 < t ^ p := Real.rpow_pos_of_pos ht _
  have hmarkov : P.real {a | t < S a} ≤ (∫ a, S a ^ p ∂P) / t ^ p := by
    apply (le_div_iff₀ htp).mpr
    calc
      P.real {a | t < S a} * t ^ p ≤ P.real {a | t ^ p ≤ S a ^ p} * t ^ p := by
        apply mul_le_mul_of_nonneg_right (measureReal_mono _) htp.le
        intro a ha
        exact Real.rpow_le_rpow ht.le ha.le hp.le
      _ ≤ _ := by
        simpa [mul_comm] using mul_meas_ge_le_integral_of_nonneg
          (ae_of_all _ (fun a => Real.rpow_nonneg (hS0 a) p)) hi (t ^ p)
  have hshift (w : Fin d → ℤ) :
      P.real {a | t < S (translateCoeff (fun i => (3 : ℤ) ^ (jStar + r) * w i) a)} =
        P.real {a | t < S a} := by
    simpa only [hstat (fun i => (3 : ℤ) ^ (jStar + r) * w i)] using! (map_measureReal_apply (μ := P)
      (measurable_translateCoeff (fun i => (3 : ℤ) ^ (jStar + r) * w i))
      (measurableSet_lt (measurable_const (a := t)) hS)).symm
  have hset : {a | ¬ ∀ w : Fin d → ℤ, w ∈ W →
      S (translateCoeff (fun i => (3 : ℤ) ^ (jStar + r) * w i) a) ≤ t} =
      ⋃ w ∈ F, {a | t < S (translateCoeff (fun i => (3 : ℤ) ^ (jStar + r) * w i) a)} := by
    ext a
    simp [F, W]
  change P.real {a | ¬ ∀ w : Fin d → ℤ, w ∈ W →
      S (translateCoeff (fun i => (3 : ℤ) ^ (jStar + r) * w i) a) ≤ t} ≤ _
  rw [hset]
  calc
    _ ≤ ∑ w ∈ F, P.real {a | t < S (translateCoeff (fun i => (3 : ℤ) ^ (jStar + r) * w i) a)} :=
      measureReal_biUnion_finset_le _ _
    _ = (F.card : ℝ) * P.real {a | t < S a} := by simp_rw [hshift]; simp
    _ ≤ (F.card : ℝ) * ((∫ a, S a ^ p ∂P) / t ^ p) := by gcongr
    _ = _ := by
      have hcard : F.card = 3 ^ (d * jStar) := by
        rw [← Set.ncard_eq_toFinset_card _ hW]
        exact (sourceCenterSet_finite_card d jStar r).2
      rw [hcard]
      push_cast
      ring

/-- Finite source moments make the all-failure event null, without a lower-scale burn. -/
theorem ae_exists_source_success {d : ℕ} (P : Measure (CoeffSpace d))
    [IsProbabilityMeasure P] (S : CoeffSpace d → ℝ) (hS : Measurable S)
    (hS0 : ∀ a, 0 ≤ S a) (hstat : IsStationaryLaw P)
    (p : ℝ) (hp : 0 < p) (hi : Integrable (fun a => S a ^ p) P)
    (jStar : ℕ) :
    ∀ᵐ a ∂P, ∃ r : ℕ, ∀ w : Fin d → ℤ,
      standardCellCenter ((jStar + r : ℕ) : ℤ) w ∈
        centeredCube d ((2 * jStar + r : ℕ) : ℤ) →
      S (translateCoeff (fun i => (3 : ℤ) ^ (jStar + r) * w i) a) ≤
        (3 : ℝ) ^ (jStar + r) := by
  let Good : ℕ → CoeffSpace d → Prop := fun r a => ∀ w : Fin d → ℤ,
    standardCellCenter ((jStar + r : ℕ) : ℤ) w ∈
      centeredCube d ((2 * jStar + r : ℕ) : ℤ) →
    S (translateCoeff (fun i => (3 : ℤ) ^ (jStar + r) * w i) a) ≤
      (3 : ℝ) ^ (jStar + r)
  let A : ℝ := (3 : ℝ) ^ (d * jStar) * (∫ a, S a ^ p ∂P) /
    ((3 : ℝ) ^ jStar) ^ p
  have hbound (r : ℕ) : P.real {a | ¬ ∃ n, Good n a} ≤ A * ((3 : ℝ) ^ (-p)) ^ r := by
    calc
      _ ≤ P.real {a | ¬ Good r a} := measureReal_mono (show {a | ¬ ∃ n, Good n a} ⊆ {a | ¬ Good r a} from fun a ha hr => ha ⟨r, hr⟩)
      _ ≤ _ := source_failure_probability_le P S hS hS0 hstat p hp hi jStar r
      _ = _ := by
        simp only [A, pow_add, Real.mul_rpow (by positivity : 0 ≤ (3 : ℝ) ^ jStar)
          (by positivity : 0 ≤ (3 : ℝ) ^ r),
          ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3),
          div_eq_mul_inv, mul_inv_rev, inv_pow]
        ring
  have hq : (3 : ℝ) ^ (-p) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hp])
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) (-p)) hq).const_mul A
  have hz : P.real {a | ¬ ∃ n, Good n a} = 0 := by
    apply le_antisymm _ measureReal_nonneg
    simpa only [mul_zero] using ge_of_tendsto' ht hbound
  rw [ae_iff]
  exact (measureReal_eq_zero_iff).mp hz

/-- A measurable least successful offset, with value zero if every attempt fails.
The events need not be monotone. This is a measurable representative on the original
sigma algebra, so no completion of the probability space is required. -/
theorem measurable_least_offset {Ω : Type*} [MeasurableSpace Ω]
    (Good : ℕ → Ω → Prop) (hm : ∀ r, MeasurableSet {a | Good r a}) :
    ∃ ell : Ω → ℕ, Measurable ell ∧
      (∀ a, (∃ r, Good r a) → Good (ell a) a ∧ ∀ r, Good r a → ell a ≤ r) ∧
      (∀ a, ¬ (∃ r, Good r a) → ell a = 0) ∧
      (∀ a r, r < ell a → ¬ Good r a) := by
  classical
  let p : Ω → ℕ → Prop := fun a r => Good r a ∨ ¬ ∃ n, Good n a
  have hp : ∀ a, ∃ r, p a r := by
    intro a
    by_cases ha : ∃ r, Good r a
    · obtain ⟨r, hr⟩ := ha
      exact ⟨r, Or.inl hr⟩
    · exact ⟨0, Or.inr ha⟩
  have he : MeasurableSet {a | ∃ n, Good n a} := by
    simpa only [ofPred_exists] using MeasurableSet.iUnion hm
  have hpm : ∀ r, MeasurableSet {a | p a r} := by
    intro r
    exact (hm r).union he.compl
  refine ⟨fun a => Nat.find (hp a), measurable_find hp hpm, ?_, ?_, ?_⟩
  · intro a ha
    refine ⟨(Nat.find_spec (hp a)).resolve_right (not_not.mpr ha), ?_⟩
    intro r hr
    exact Nat.find_min' (hp a) (Or.inl hr)
  · intro a ha
    exact Nat.eq_zero_of_le_zero (Nat.find_min' (hp a) (Or.inr ha : p a 0))
  · intro a r hr hg
    exact (Nat.not_le_of_lt hr) (Nat.find_min' (hp a) (Or.inl hg))

/-- The printed source minimum is attained almost surely. The representative is one
on the all-failure null set, and is identically one when the exponent is zero.
No rounding or source lower-scale threshold is needed for attainment alone. -/
theorem source_minimum {d : ℕ} (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) :
    let Good : ℕ → CoeffSpace d → Prop := fun r a => ∀ w : Fin d → ℤ,
      standardCellCenter ((jStar + r : ℕ) : ℤ) w ∈
        centeredCube d ((2 * jStar + r : ℕ) : ℤ) →
      S (translateCoeff (fun i => (3 : ℤ) ^ (jStar + r) * w i) a) ≤
        (3 : ℝ) ^ (jStar + r)
    ∃ (ell : CoeffSpace d → ℕ) (X : CoeffSpace d → ℝ),
      Measurable ell ∧ Measurable X ∧
      (∀ a, X a = (3 : ℝ) ^ (γ * (ell a : ℝ))) ∧
      (∀ a, ¬ (∃ r, Good r a) → ell a = 0) ∧
      (∀ᵐ a ∂P, Good (ell a) a ∧
        (∀ r, Good r a → ell a ≤ r) ∧
        (∀ r, Good r a → X a ≤ (3 : ℝ) ^ (γ * (r : ℝ)))) ∧
      (γ = 0 → ∀ a, X a = 1) ∧
      (∀ p : ℝ, 1 ≤ p → ∀ r : ℕ,
        P.real {a | r < ell a} ≤
          (3 : ℝ) ^ (d * jStar) * (∫ a, S a ^ p ∂P) /
            ((3 : ℝ) ^ (jStar + r)) ^ p) := by
  intro Good
  obtain ⟨ell, hell, hleast, hdefault, hfail⟩ :=
    measurable_least_offset Good (measurableSet_source_success S hdag.source_measurable jStar)
  let X : CoeffSpace d → ℝ := fun a => (3 : ℝ) ^ (γ * (ell a : ℝ))
  have hX : Measurable X := by dsimp [X]; fun_prop
  have hmom (p : ℝ) (hp : 1 ≤ p) : Integrable (fun a => S a ^ p) P := by
    obtain ⟨C, _, hC⟩ := CoarseEllipticityDagger.source_moment_bound p hp
    exact (hC P γ E Ψ K S hdag).2.1
  have hex : ∀ᵐ a ∂P, ∃ r, Good r a :=
    ae_exists_source_success P S hdag.source_measurable hdag.source_nonneg hstat
      1 (by norm_num) (hmom 1 le_rfl) jStar
  refine ⟨ell, X, hell, hX, fun _ => rfl, hdefault, ?_, ?_, ?_⟩
  · filter_upwards [hex] with a ha
    obtain ⟨hgood, hmin⟩ := hleast a ha
    refine ⟨hgood, hmin, ?_⟩
    intro r hr
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hmin r hr) hdag.g_mem.1)
  · intro hγ a
    simp [X, hγ]
  · intro p hp r
    calc
      P.real {a | r < ell a} ≤ P.real {a | ¬ Good r a} :=
        measureReal_mono (fun a ha => hfail a r ha)
      _ ≤ _ := source_failure_probability_le P S hdag.source_measurable
        hdag.source_nonneg hstat p (zero_lt_one.trans_le hp) (hmom p hp) jStar r

/-- Summing the upper tail of a natural offset gives a finite exponential moment.
This is an extended-integral estimate; integrability is a consequence, not a premise. -/
theorem stopping_lintegral_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ell : Ω → ℕ) (hell : Measurable ell)
    (b A q : ℝ) (hb : 0 ≤ b) (hA : 0 ≤ A) (hq : 0 ≤ q) (hbq : b * q < 1)
    (htail : ∀ r : ℕ, μ.real {a | r < ell a} ≤ A * q ^ r) :
    (∫⁻ a, ENNReal.ofReal (b ^ ell a) ∂μ) ≤
      ENNReal.ofReal (1 + b * A / (1 - b * q)) := by
  classical
  have hden : 0 < 1 - b * q := sub_pos.mpr hbq
  let F : ℕ → Ω → ℝ≥0∞ := fun r =>
    {a | r < ell a}.indicator (fun _ => ENNReal.ofReal (b ^ (r + 1)))
  have hset (r : ℕ) : MeasurableSet {a | r < ell a} :=
    measurableSet_lt measurable_const hell
  have hF (r : ℕ) : Measurable (F r) := measurable_const.indicator (hset r)
  have hdom (a : Ω) : ENNReal.ofReal (b ^ ell a) ≤ 1 + ∑' r, F r a := by
    rcases hn : ell a with _ | n
    · simp
    · have ht := ENNReal.le_tsum (f := fun r => F r a) n
      have hmem : a ∈ {a | n < ell a} := by simp [hn]
      simpa only [F, indicator_of_mem hmem, hn] using ht.trans (le_add_self :
        (∑' r, F r a) ≤ 1 + ∑' r, F r a)
  have hterm (r : ℕ) : (∫⁻ a, F r a ∂μ) ≤ ENNReal.ofReal (b * A * (b * q) ^ r) := by
    rw [show F r = {a | r < ell a}.indicator (fun _ => ENNReal.ofReal (b ^ (r + 1))) from rfl,
      lintegral_indicator_const (hset r)]
    have hμ : μ {a | r < ell a} = ENNReal.ofReal (μ.real {a | r < ell a}) :=
      (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    rw [hμ, ← ENNReal.ofReal_mul (pow_nonneg hb _)]
    apply ENNReal.ofReal_le_ofReal
    calc
      b ^ (r + 1) * μ.real {a | r < ell a} ≤ b ^ (r + 1) * (A * q ^ r) :=
        mul_le_mul_of_nonneg_left (htail r) (pow_nonneg hb _)
      _ = _ := by rw [pow_succ, mul_pow]; ring
  have hs : Summable (fun r : ℕ => b * A * (b * q) ^ r) :=
    (summable_geometric_of_lt_one (mul_nonneg hb hq) hbq).mul_left _
  calc
    _ ≤ ∫⁻ a, 1 + ∑' r, F r a ∂μ := lintegral_mono hdom
    _ = 1 + ∑' r, ∫⁻ a, F r a ∂μ := by
      rw [lintegral_add_left measurable_const, lintegral_tsum (fun r => (hF r).aemeasurable)]
      simp
    _ ≤ 1 + ∑' r, ENNReal.ofReal (b * A * (b * q) ^ r) :=
      add_le_add le_rfl (ENNReal.tsum_le_tsum hterm)
    _ = _ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun r => by positivity) hs,
        tsum_mul_left, tsum_geometric_of_lt_one (mul_nonneg hb hq) hbq,
        ← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1)]
      · rw [div_eq_mul_inv]
      · positivity

/-- An explicit constant for the closed source lower-scale threshold. The formula
is fixed before the growth witness and scale, and introduces no additive burn. -/
theorem source_threshold_constant (C B δ : ℝ) (hC : 0 < C) (hB : 0 < B) (hδ : 0 < δ) :
    let Csrc : ℝ := (C + max 1 (Real.logb 2 B)) / δ
    0 < Csrc ∧ ∀ (K : ℝ), 1 < K → ∀ (jStar : ℕ),
      ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
      B * K ^ C ≤ (3 : ℝ) ^ (δ * (jStar : ℝ)) := by
  let D : ℝ := max 1 (Real.logb 2 B)
  have hD : 0 < D := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨div_pos (add_pos hC hD) hδ, ?_⟩
  intro K hK jStar hj
  have hK0 : 0 < K := zero_lt_one.trans hK
  have h2K : 0 < 2 * K := by positivity
  have hBpow : B ≤ (2 * K) ^ D := by
    calc
      B = (2 : ℝ) ^ Real.logb 2 B := (Real.rpow_logb (by norm_num) (by norm_num) hB).symm
      _ ≤ (2 : ℝ) ^ D := Real.rpow_le_rpow_of_exponent_le (by norm_num) (le_max_right _ _)
      _ ≤ _ := Real.rpow_le_rpow (by norm_num) (by linarith only [hK]) hD.le
  have hjR : (C + D) / δ * Real.logb 3 (2 * K) ≤ (jStar : ℝ) := by
    exact_mod_cast Int.ceil_le.mp hj
  have hexp : Real.logb 3 (2 * K) * (C + D) ≤ δ * (jStar : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hjR hδ.le
    have heq : δ * ((C + D) / δ * Real.logb 3 (2 * K)) =
        Real.logb 3 (2 * K) * (C + D) := by field_simp
    rwa [heq] at hh
  calc
    B * K ^ C ≤ (2 * K) ^ D * (2 * K) ^ C :=
      mul_le_mul hBpow (Real.rpow_le_rpow hK0.le (by linarith only [hK0]) hC.le)
        (by positivity) (by positivity)
    _ = (2 * K) ^ (C + D) := by rw [← Real.rpow_add h2K]; congr 1; ring
    _ = (3 : ℝ) ^ (Real.logb 3 (2 * K) * (C + D)) := by
      rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
        Real.rpow_logb (by norm_num : (0 : ℝ) < 3) (by norm_num) h2K]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp

/-- Separate the fixed source-window factor from the geometric offset tail. -/
theorem source_tail_power_identity (d jStar r : ℕ) (p M : ℝ) :
    (3 : ℝ) ^ (d * jStar) * M / ((3 : ℝ) ^ (jStar + r)) ^ p =
      M / (3 : ℝ) ^ ((p - (d : ℝ)) * (jStar : ℝ)) * ((3 : ℝ) ^ (-p)) ^ r := by
  simp only [div_eq_mul_inv, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
    ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), Nat.cast_mul, Nat.cast_add]
  calc
    _ = M * ((3 : ℝ) ^ ((d : ℝ) * (jStar : ℝ)) *
      (3 : ℝ) ^ (-(((jStar : ℝ) + (r : ℝ)) * p))) := by ring
    _ = M * (3 : ℝ) ^ (-((p - (d : ℝ)) * (jStar : ℝ)) + -p * (r : ℝ)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 2
      ring
    _ = _ := by rw [Real.rpow_add (by norm_num : (0 : ℝ) < 3)]; ring

/-- A finite nonnegative moment supplies membership before its actual norm is bounded. -/
theorem memLp_and_norm_le_two_of_lintegral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (hX : Measurable X) (hX0 : ∀ a, 0 ≤ X a)
    (Q : ℕ) (hQ : 0 < Q)
    (hbound : (∫⁻ a, ENNReal.ofReal (X a ^ Q) ∂μ) ≤ ENNReal.ofReal ((2 : ℝ) ^ Q)) :
    MemLp X (ENNReal.ofReal (Q : ℝ)) μ ∧ Integrable (fun a => X a ^ Q) μ ∧
      (∫ a, X a ^ Q ∂μ) ≤ (2 : ℝ) ^ Q ∧
      eLpNorm X (ENNReal.ofReal (Q : ℝ)) μ ≤ ENNReal.ofReal 2 := by
  have hQR : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have hn : 0 ≤ᵐ[μ] (fun a => X a ^ Q) := ae_of_all _ (fun a => pow_nonneg (hX0 a) _)
  have hi : Integrable (fun a => X a ^ Q) μ :=
    (lintegral_ofReal_ne_top_iff_integrable (hX.pow_const Q).aestronglyMeasurable hn).1
      (ne_of_lt (hbound.trans_lt ENNReal.ofReal_lt_top))
  have hlp : MemLp X (ENNReal.ofReal (Q : ℝ)) μ := by
    apply (integrable_norm_rpow_iff hX.aestronglyMeasurable
      (ENNReal.ofReal_ne_zero_iff.mpr hQR) ENNReal.ofReal_ne_top).1
    simpa only [ENNReal.toReal_ofReal hQR.le, Real.norm_eq_abs, abs_of_nonneg (hX0 _),
      Real.rpow_natCast] using hi
  have hib : (∫ a, X a ^ Q ∂μ) ≤ (2 : ℝ) ^ Q := by
    rw [integral_eq_lintegral_of_nonneg_ae hn hi.aestronglyMeasurable]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq
      (ENNReal.toReal_ofReal (by positivity))
  refine ⟨hlp, hi, hib, ?_⟩
  rw [hlp.eLpNorm_eq_integral_rpow_norm (ENNReal.ofReal_ne_zero_iff.mpr hQR) ENNReal.ofReal_ne_top]
  simp only [ENNReal.toReal_ofReal hQR.le, Real.norm_eq_abs, abs_of_nonneg (hX0 _), Real.rpow_natCast]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ((2 : ℝ) ^ Q) ^ ((Q : ℝ)⁻¹) := Real.rpow_le_rpow
      (integral_nonneg (fun a => pow_nonneg (hX0 a) _)) hib (by positivity)
    _ = 2 := by
      rw [Real.pow_rpow_inv_natCast (by norm_num : (0 : ℝ) ≤ 2) hQ.ne']

/-- The printed, characterized source multiplier and its fixed selection-moment bound.
Write `p=2*(d+Q)`, `b=3^(γ*Q)`, `q=3^(-p)`, and let `C` be the source-moment
constant supplied by `source_selection_moment_bound`. We choose, once before the
law, `B=C*b/(1-b*q)` and `Csrc=(C+max 1 (logb 2 B))/(p-d)`. The standing threshold
is closed, with no extra burn. -/
theorem source_multiplier (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc : ℝ, 0 < Csrc ∧
      ∀ (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
        (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ),
        IsStationaryLaw P → CoarseEllipticityDagger P γ E Ψ K S →
        ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
          ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
          let Good : ℕ → CoeffSpace d → Prop := fun r a =>
            ∀ w : Fin d → ℤ,
              standardCellCenter ((jStar + r : ℕ) : ℤ) w ∈
                centeredCube d ((2 * jStar + r : ℕ) : ℤ) →
              S (translateCoeff (fun i => (3 : ℤ) ^ (jStar + r) * w i) a) ≤
                (3 : ℝ) ^ (jStar + r)
          ∃ (ell : CoeffSpace d → ℕ) (X : CoeffSpace d → ℝ),
            Measurable ell ∧ Measurable X ∧
            (∀ a, X a = (3 : ℝ) ^ (γ * (ell a : ℝ))) ∧
            (∀ᵐ a ∂P, Good (ell a) a ∧
              (∀ r : ℕ, Good r a → ell a ≤ r) ∧
              (∀ r : ℕ, Good r a → X a ≤ (3 : ℝ) ^ (γ * (r : ℝ)))) ∧
            MemLp X (ENNReal.ofReal (bigQ d γ : ℝ)) P ∧
            Integrable (fun a => X a ^ bigQ d γ) P ∧
            (∫ a, X a ^ bigQ d γ ∂P) ≤ (2 : ℝ) ^ bigQ d γ ∧
            eLpNorm X (ENNReal.ofReal (bigQ d γ : ℝ)) P ≤ ENNReal.ofReal 2 := by
  obtain ⟨C, hC, hp, hdmargin, hqmargin, hsource⟩ := source_selection_moment_bound d hd γ hγ
  let Q : ℕ := bigQ d γ
  let p : ℝ := (Multiscale.sourceMomentExponent d γ : ℝ)
  let δ : ℝ := p - (d : ℝ)
  let b : ℝ := (3 : ℝ) ^ (γ * (Q : ℝ))
  let q : ℝ := (3 : ℝ) ^ (-p)
  have hQ : 0 < Q := Multiscale.bigQ_pos d γ hγ
  have hdQ : 0 < (d : ℝ) + (Q : ℝ) := by positivity
  have hδ : 0 < δ := hdQ.trans_le hdmargin
  have hgap : 0 < p - γ * (Q : ℝ) := by
    dsimp [p, Q]
    linarith only [hqmargin, hdQ]
  have hb : 0 < b := by dsimp [b]; positivity
  have hq : 0 < q := by dsimp [q]; positivity
  have hbq : b * q < 1 := by
    dsimp [b, q]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hgap])
  have hden : 0 < 1 - b * q := sub_pos.mpr hbq
  let B : ℝ := C * b / (1 - b * q)
  have hB : 0 < B := by dsimp [B]; positivity
  let Csrc : ℝ := (C + max 1 (Real.logb 2 B)) / δ
  obtain ⟨hCsrc, hburn⟩ := source_threshold_constant C B δ hC hB hδ
  refine ⟨Csrc, hCsrc, ?_⟩
  intro P _ E Ψ K S hstat hdag jStar _hj hsrc Good
  obtain ⟨ell, X, hell, hX, hform, _hdefault, hmin, _hzero, htail⟩ :=
    source_minimum P γ E Ψ K S hstat hdag jStar
  have hX0 (a : CoeffSpace d) : 0 ≤ X a := by rw [hform a]; positivity
  have hpow (a : CoeffSpace d) : X a ^ Q = b ^ ell a := by
    rw [hform a]
    dsimp [b]
    simp only [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  have hpR : 1 ≤ p := by dsimp [p]; exact_mod_cast hp
  have hI : (∫ a, S a ^ p ∂P) ≤ C * K ^ C := (hsource P E Ψ K S hdag).2.2
  have hK0 : 0 < K := zero_lt_one.trans hdag.one_lt_growthWitness
  let A : ℝ := C * K ^ C / (3 : ℝ) ^ (δ * (jStar : ℝ))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have ht (r : ℕ) : P.real {a | r < ell a} ≤ A * q ^ r := by
    calc
      _ ≤ _ := htail p hpR r
      _ ≤ (3 : ℝ) ^ (d * jStar) * (C * K ^ C) / ((3 : ℝ) ^ (jStar + r)) ^ p := by
        gcongr
      _ = _ := source_tail_power_identity d jStar r p (C * K ^ C)
  have hsum := stopping_lintegral_le P ell hell b A q hb.le hA hq.le hbq ht
  have hsmall : b * A / (1 - b * q) ≤ 1 := by
    have heq : b * A / (1 - b * q) = B * K ^ C / (3 : ℝ) ^ (δ * (jStar : ℝ)) := by
      dsimp [A, B]
      ring
    rw [heq, div_le_one (by positivity : 0 < (3 : ℝ) ^ (δ * (jStar : ℝ)))]
    exact hburn K hdag.one_lt_growthWitness jStar hsrc
  have htwoQ : (2 : ℝ) ≤ 2 ^ Q := by
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show 1 ≤ Q by omega)
  have hmoment : (∫⁻ a, ENNReal.ofReal (X a ^ Q) ∂P) ≤ ENNReal.ofReal ((2 : ℝ) ^ Q) := by
    simp_rw [hpow]
    exact hsum.trans ((ENNReal.ofReal_le_ofReal (by linarith only [hsmall] : 1 + b * A / (1 - b * q) ≤ 2)).trans
      (ENNReal.ofReal_le_ofReal htwoQ))
  obtain ⟨hlp, hi, hbound, hnorm⟩ := memLp_and_norm_le_two_of_lintegral P X hX hX0 Q hQ hmoment
  exact ⟨ell, X, hell, hX, hform, hmin, hlp, hi, hbound, hnorm⟩

end
end HCPolySupport.HighContrast.Source
