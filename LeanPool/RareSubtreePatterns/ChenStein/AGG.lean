/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.ChenStein.SteinSolution
public import LeanPool.RareSubtreePatterns.Probability.PoissonTV


/-!
# The Arratia–Goldstein–Gordon Chen–Stein bound

Proposition `prop:AGG` of the source (lines 1597–1614). For indicators `I_i = 1_{E_i}` on a
probability space, with `q_i = P(E_i)`, `λ = ∑ q_i`, `W = ∑ I_i`, and neighbourhoods `B_i ∋ i`,
there is one function `f` with `‖f‖_∞ ≤ 1` such that

  `d_TV(W, Po(λ)) ≤ 2 (b_1 + b_2 + b_3)`,

where `b_1 = ∑_i ∑_{j ∈ B_i} q_i q_j`, `b_2 = ∑_i ∑_{j ∈ B_i \ {i}} E[I_i I_j]` and
`b_3 = ∑_i |E[(I_i - q_i) f(1 + ∑_{j ∉ B_i} I_j)]|`; `d_TV` is the probability-normalized
distance `paperTVDist`.

The proof is the standard Chen–Stein argument: choose an event `A` attaining the distance, take
the Stein solution `f = f_A` (bounded by one, `PoissonDeclumping.ChenStein.SteinSolution`), and
decompose `λ f(W+1) - W f(W)` along the neighbourhoods. Instead of AGG's sharper Stein factors
we use only `‖f_A‖ ≤ 1`, hence `|f_A(x + d) - f_A(x)| ≤ 2d`; this gives the slightly stronger
`d_TV ≤ 2 b_1 + 2 b_2 + b_3` (`exists_paperTVDist_le_two_mul_add`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace PoissonDeclumping.ChenStein

/-- The pointwise neighbourhood estimate behind the Chen–Stein decomposition. Here
`n = I_i`, `u = ∑_{j ∈ B_i \ {i}} I_j`, `v = ∑_{j ∉ B_i} I_j`, so `W = n + u + v`. -/
lemma abs_pointwise_le {f : ℕ → ℝ} (hf : ∀ k, |f k| ≤ 1) {q : ℝ} (hq : 0 ≤ q) {n u v : ℕ}
    (hn : n ≤ 1) :
    |q * (f (n + u + v + 1) - f (1 + v)) - (n : ℝ) * (f (n + u + v) - f (1 + v))| ≤
      2 * q * ((n : ℝ) + u) + 2 * ((n : ℝ) * u) := by
  have h1 : |f (n + u + v + 1) - f (1 + v)| ≤ 2 * ((n : ℝ) + u) := by
    have := abs_sub_le_two_mul_of_abs_le_one hf (1 + v) (n + u)
    rw [show 1 + v + (n + u) = n + u + v + 1 by ring] at this
    simpa using this
  have h2 : |(n : ℝ) * (f (n + u + v) - f (1 + v))| ≤ 2 * ((n : ℝ) * u) := by
    interval_cases n
    · simp
    · have := abs_sub_le_two_mul_of_abs_le_one hf (1 + v) u
      rw [show 1 + v + u = 1 + u + v by ring] at this
      simpa using this
  calc _ ≤ |q * (f (n + u + v + 1) - f (1 + v))| + |(n : ℝ) * (f (n + u + v) - f (1 + v))| :=
        abs_sub _ _
    _ ≤ q * (2 * ((n : ℝ) + u)) + 2 * ((n : ℝ) * u) := by
        rw [abs_mul, abs_of_nonneg hq]
        exact add_le_add (mul_le_mul_of_nonneg_left h1 hq) h2
    _ = _ := by ring

/-- The natural-number and real indicators agree after casting. -/
lemma natCast_indicator_one {Ω : Type*} (s : Set Ω) (ω : Ω) :
    ((s.indicator (1 : Ω → ℕ) ω : ℕ) : ℝ) = s.indicator (1 : Ω → ℝ) ω := by
  by_cases h : ω ∈ s <;> simp [h]

lemma indicator_one_le_one {Ω : Type*} (s : Set Ω) (ω : Ω) : s.indicator (1 : Ω → ℕ) ω ≤ 1 := by
  by_cases h : ω ∈ s <;> simp [h]

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]

/-- **Chen–Stein bound for a fixed event.** For every rate `r > 0` equal to `∑ P(E_i)` and every
`A ⊆ ℕ`, the discrepancy `P(W ∈ A) - Po(r)(A)` is bounded by `2 b_1 + 2 b_2 + b_3(f_A)` with the
Stein solution `f_A = steinSolution r A`. -/
theorem abs_map_sub_poissonMeasure_le (P : Measure Ω) [IsProbabilityMeasure P]
    (E : ι → Set Ω) (hE : ∀ i, MeasurableSet (E i)) (B : ι → Finset ι) (hB : ∀ i, i ∈ B i)
    {r : ℝ≥0} (hr : 0 < r) (hrE : (r : ℝ) = ∑ i, P.real (E i)) (A : Set ℕ) :
    |(P.map (fun ω => ∑ i, (E i).indicator (1 : Ω → ℕ) ω)).real A -
        (poissonMeasure r).real A| ≤
      2 * ∑ i, ∑ j ∈ B i, P.real (E i) * P.real (E j) +
        2 * ∑ i, ∑ j ∈ B i \ {i}, P.real (E i ∩ E j) +
        ∑ i, |∫ ω, ((E i).indicator (1 : Ω → ℝ) ω - P.real (E i)) *
          steinSolution r A (1 + ∑ j ∈ Finset.univ \ B i, (E j).indicator (1 : Ω → ℕ) ω) ∂P| := by
  -- notation
  set f := steinSolution r A with hfdef
  have hf : ∀ k, |f k| ≤ 1 := abs_steinSolution_le_one r A
  set N : ι → Ω → ℕ := fun j ω => (E j).indicator (1 : Ω → ℕ) ω with hNdef
  set Ir : ι → Ω → ℝ := fun j ω => (E j).indicator (1 : Ω → ℝ) ω with hIrdef
  set q : ι → ℝ := fun i => P.real (E i) with hqdef
  set W : Ω → ℕ := fun ω => ∑ j, N j ω with hWdef
  set V : ι → Ω → ℕ := fun i ω => ∑ j ∈ Finset.univ \ B i, N j ω with hVdef
  set U : ι → Ω → ℕ := fun i ω => ∑ j ∈ B i \ {i}, N j ω with hUdef
  have hNle : ∀ j ω, N j ω ≤ 1 := fun j ω => indicator_one_le_one _ _
  have hNcast : ∀ j ω, (N j ω : ℝ) = Ir j ω := fun j ω => natCast_indicator_one _ _
  have hq0 : ∀ i, 0 ≤ q i := fun i => measureReal_nonneg
  -- decomposition of `W`
  have hWdec : ∀ i ω, W ω = N i ω + U i ω + V i ω := by
    intro i ω
    have h1 := Finset.sum_sdiff (f := fun j => N j ω) (Finset.subset_univ (B i))
    have h2 := Finset.sum_sdiff (f := fun j => N j ω)
      (Finset.singleton_subset_iff.mpr (hB i))
    simp only [Finset.sum_singleton] at h2
    simp only [hWdef, hVdef, hUdef]
    omega
  have hSdec : ∀ i ω, (∑ j ∈ B i, Ir j ω) = Ir i ω + U i ω := by
    intro i ω
    have h2 := Finset.sum_sdiff (f := fun j => Ir j ω)
      (Finset.singleton_subset_iff.mpr (hB i))
    simp only [Finset.sum_singleton] at h2
    simp only [hUdef, Nat.cast_sum, hNcast]
    linarith
  have hIU : ∀ i ω, Ir i ω * U i ω = ∑ j ∈ B i \ {i}, Ir i ω * Ir j ω := by
    intro i ω
    simp only [hUdef, Nat.cast_sum, hNcast, Finset.mul_sum]
  -- measurability
  have hNm : ∀ j, Measurable (N j) := fun j => measurable_one.indicator (hE j)
  have hWm : Measurable W := Finset.measurable_sum _ (fun j _ => hNm j)
  have hVm : ∀ i, Measurable (V i) := fun i => Finset.measurable_sum _ (fun j _ => hNm j)
  -- integrability
  have hIrint : ∀ j, Integrable (Ir j) P := fun j => (integrable_const (1 : ℝ)).indicator (hE j)
  have hind : ∀ s, MeasurableSet s → Integrable (s.indicator (1 : Ω → ℝ)) P :=
    fun s hs => (integrable_const (1 : ℝ)).indicator hs
  have hcompm : ∀ M : Ω → ℕ, Measurable M → Measurable (fun ω => f (M ω)) :=
    fun M hM => (Measurable.of_discrete (f := f)).comp hM
  have hcomp : ∀ M : Ω → ℕ, Measurable M → Integrable (fun ω => f (M ω)) P := by
    intro M hM
    refine Integrable.of_bound (hcompm M hM).aestronglyMeasurable 1 ?_
    exact Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hf (M ω)
  have hW1 : Measurable (fun ω => W ω + 1) := hWm.add_const 1
  have hV1 : ∀ i, Measurable (fun ω => 1 + V i ω) := fun i => (hVm i).const_add 1
  have hprod : ∀ i j, (fun ω => Ir i ω * Ir j ω) = (E i ∩ E j).indicator (1 : Ω → ℝ) := by
    intro i j
    rw [inter_indicator_one]
    rfl
  -- the three pieces
  set C : ι → Ω → ℝ := fun i ω => (Ir i ω - q i) * f (1 + V i ω) with hCdef
  set D : Ω → ℝ := fun ω => ∑ i, (q i * (f (W ω + 1) - f (1 + V i ω)) -
    Ir i ω * (f (W ω) - f (1 + V i ω))) with hDdef
  set R : Ω → ℝ := fun ω => ∑ i, (2 * q i * ∑ j ∈ B i, Ir j ω +
    2 * ∑ j ∈ B i \ {i}, Ir i ω * Ir j ω) with hRdef
  have hCint : ∀ i, Integrable (C i) P := by
    intro i
    refine Integrable.mul_bdd ((hIrint i).sub (integrable_const _))
      (hcompm _ (hV1 i)).aestronglyMeasurable (c := 1) ?_
    exact Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hf _
  have hDint : Integrable D P := by
    refine integrable_finsetSum _ (fun i _ => ?_)
    refine Integrable.sub (((hcomp _ hW1).sub (hcomp _ (hV1 i))).const_mul (q i)) ?_
    refine Integrable.mul_bdd (hIrint i)
      ((hcompm _ hWm).sub (hcompm _ (hV1 i))).aestronglyMeasurable (c := 2) ?_
    refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs]
    calc |f (W ω) - f (1 + V i ω)| ≤ |f (W ω)| + |f (1 + V i ω)| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add (hf _) (hf _)
      _ = 2 := by norm_num
  have hRint : Integrable R P := by
    refine integrable_finsetSum _ (fun i _ => ?_)
    refine Integrable.add ?_ ?_
    · exact (integrable_finsetSum _ (fun j _ => hIrint j)).const_mul _
    · refine Integrable.const_mul (integrable_finsetSum _ (fun j _ => ?_)) _
      rw [hprod]
      exact (integrable_const (1 : ℝ)).indicator ((hE i).inter (hE j))
  -- Step 1: the discrepancy is the expectation of the Stein operator
  have hstep1 : (P.map W).real A - (poissonMeasure r).real A =
      ∫ ω, ((r : ℝ) * f (W ω + 1) - W ω * f (W ω)) ∂P := by
    have hpt : ∀ ω, (r : ℝ) * f (W ω + 1) - W ω * f (W ω) =
        (W ⁻¹' A).indicator (1 : Ω → ℝ) ω - (poissonMeasure r).real A := by
      intro ω
      rw [hfdef, steinSolution_equation hr A (W ω)]
      by_cases h : W ω ∈ A <;> simp [h]
    simp_rw [hpt]
    rw [integral_sub (hind _ (hWm MeasurableSet.of_discrete)) (integrable_const _),
      integral_indicator_one (hWm MeasurableSet.of_discrete), integral_const, probReal_univ,
      one_smul, map_measureReal_apply hWm MeasurableSet.of_discrete]
  -- Step 2: the neighbourhood decomposition
  have hstep2 : ∀ ω, (r : ℝ) * f (W ω + 1) - W ω * f (W ω) = D ω - ∑ i, C i ω := by
    intro ω
    have hWcast : (W ω : ℝ) = ∑ i, Ir i ω := by
      simp only [hWdef, Nat.cast_sum, hNcast]
    rw [hWcast, hrE, hDdef, hCdef]
    rw [← Finset.sum_sub_distrib, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  -- Step 3: the pointwise bound `|D| ≤ R`
  have hstep3 : ∀ ω, ‖D ω‖ ≤ R ω := by
    intro ω
    rw [Real.norm_eq_abs, hDdef, hRdef]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    have h := abs_pointwise_le hf (hq0 i) (hNle i ω) (u := U i ω) (v := V i ω)
    rw [← hWdec i ω, hNcast] at h
    rw [hSdec i ω, ← hIU i ω]
    linarith
  -- Step 4: the expectation of `R`
  have hstep4 : ∫ ω, R ω ∂P = 2 * ∑ i, ∑ j ∈ B i, P.real (E i) * P.real (E j) +
      2 * ∑ i, ∑ j ∈ B i \ {i}, P.real (E i ∩ E j) := by
    have hIrE : ∀ j, ∫ ω, Ir j ω ∂P = q j := fun j => integral_indicator_one (hE j)
    have hprodE : ∀ i j, ∫ ω, Ir i ω * Ir j ω ∂P = P.real (E i ∩ E j) := by
      intro i j
      rw [hprod]
      exact integral_indicator_one ((hE i).inter (hE j))
    rw [hRdef, integral_finsetSum _ (fun i _ => ?_)]
    · rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [integral_add, integral_const_mul, integral_const_mul,
        integral_finsetSum _ (fun j _ => hIrint j),
        integral_finsetSum _ (fun j _ => by rw [hprod]; exact
          (integrable_const (1 : ℝ)).indicator ((hE i).inter (hE j)))]
      · simp only [hIrE, hprodE, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl (fun j _ => ?_)
        simp only [hqdef]
        ring
      · exact (integrable_finsetSum _ (fun j _ => hIrint j)).const_mul _
      · refine Integrable.const_mul (integrable_finsetSum _ (fun j _ => ?_)) _
        rw [hprod]
        exact (integrable_const (1 : ℝ)).indicator ((hE i).inter (hE j))
    · refine Integrable.add ?_ ?_
      · exact (integrable_finsetSum _ (fun j _ => hIrint j)).const_mul _
      · refine Integrable.const_mul (integrable_finsetSum _ (fun j _ => ?_)) _
        rw [hprod]
        exact (integrable_const (1 : ℝ)).indicator ((hE i).inter (hE j))
  -- Conclusion
  have key : |(P.map W).real A - (poissonMeasure r).real A| ≤
      2 * ∑ i, ∑ j ∈ B i, P.real (E i) * P.real (E j) +
        2 * ∑ i, ∑ j ∈ B i \ {i}, P.real (E i ∩ E j) + ∑ i, |∫ ω, C i ω ∂P| := by
    rw [hstep1]
    simp_rw [hstep2]
    rw [integral_sub hDint (integrable_finsetSum _ (fun i _ => hCint i)),
      integral_finsetSum _ (fun i _ => hCint i)]
    have hD := norm_integral_le_of_norm_le hRint (Filter.Eventually.of_forall hstep3)
    rw [Real.norm_eq_abs, hstep4] at hD
    calc _ ≤ |∫ ω, D ω ∂P| + |∑ i, ∫ ω, C i ω ∂P| := abs_sub _ _
      _ ≤ |∫ ω, D ω ∂P| + ∑ i, |∫ ω, C i ω ∂P| :=
          add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _)
      _ ≤ _ := add_le_add hD le_rfl
  exact key

/-- **Chen–Stein bound, sharper constants.** With the indicators `I_i = 1_{E_i}`,
`q_i = P(E_i)`, `λ = ∑ q_i` and neighbourhoods `B_i ∋ i`, some `f` with `|f| ≤ 1` gives
`d_TV(W, Po(λ)) ≤ 2 b_1 + 2 b_2 + b_3(f)`. The rate is passed as `lam : ℝ≥0` with its defining
equation; the degenerate case `λ = 0` is included. -/
theorem exists_paperTVDist_le_two_mul_add (P : Measure Ω) [IsProbabilityMeasure P]
    (E : ι → Set Ω) (hE : ∀ i, MeasurableSet (E i)) (B : ι → Finset ι) (hB : ∀ i, i ∈ B i)
    (lam : ℝ≥0) (hlam : (lam : ℝ) = ∑ i, P.real (E i)) :
    ∃ f : ℕ → ℝ, (∀ k, |f k| ≤ 1) ∧
      paperTVDist (P.map (fun ω => ∑ i, (E i).indicator (1 : Ω → ℕ) ω))
          (poissonMeasure lam) ≤
        2 * ∑ i, ∑ j ∈ B i, P.real (E i) * P.real (E j) +
          2 * ∑ i, ∑ j ∈ B i \ {i}, P.real (E i ∩ E j) +
          ∑ i, |∫ ω, ((E i).indicator (1 : Ω → ℝ) ω - P.real (E i)) *
            f (1 + ∑ j ∈ Finset.univ \ B i, (E j).indicator (1 : Ω → ℕ) ω) ∂P| := by
  rcases eq_zero_or_pos lam with rfl | hpos
  · -- Degenerate case: all `E i` are null, so `W = 0` almost surely and `Po(0) = δ_0`.
    refine ⟨fun _ => 0, fun _ => by simp, ?_⟩
    have hq : ∀ i, P.real (E i) = 0 := by
      have h0 : ∑ i, P.real (E i) = 0 := by rw [← hlam]; simp
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => measureReal_nonneg)).mp h0 i
        (Finset.mem_univ i)
    have hae : (fun ω => ∑ i, (E i).indicator (1 : Ω → ℕ) ω) =ᵐ[P] fun _ => 0 := by
      have h : ∀ i, ∀ᵐ ω ∂P, ω ∉ E i := fun i =>
        measure_eq_zero_iff_ae_notMem.mp ((measureReal_eq_zero_iff).mp (hq i))
      filter_upwards [ae_all_iff.mpr h] with ω hω
      simp [hω]
    rw [Measure.map_congr hae, Measure.map_const, measure_univ, one_smul, poissonMeasure_zero,
      paperTVDist_self]
    have h1 : 0 ≤ ∑ i, ∑ j ∈ B i, P.real (E i) * P.real (E j) :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        mul_nonneg measureReal_nonneg measureReal_nonneg
    have h2 : 0 ≤ ∑ i, ∑ j ∈ B i \ {i}, P.real (E i ∩ E j) :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => measureReal_nonneg
    have h3 := Finset.sum_nonneg (s := Finset.univ) fun i (_ : i ∈ Finset.univ) =>
      abs_nonneg (∫ ω, ((E i).indicator (1 : Ω → ℝ) ω - P.real (E i)) *
        (fun _ : ℕ => (0 : ℝ)) (1 + ∑ j ∈ Finset.univ \ B i, (E j).indicator (1 : Ω → ℕ) ω) ∂P)
    linarith
  · have hWm : Measurable (fun ω => ∑ i, (E i).indicator (1 : Ω → ℕ) ω) :=
      Finset.measurable_sum _ (fun j _ => measurable_one.indicator (hE j))
    obtain ⟨A, -, hA⟩ := exists_measurableSet_abs_sub_measureReal_eq_paperTVDist
      (P.map (fun ω => ∑ i, (E i).indicator (1 : Ω → ℕ) ω)) (poissonMeasure lam)
    refine ⟨steinSolution lam A, abs_steinSolution_le_one lam A, ?_⟩
    rw [← hA]
    exact abs_map_sub_poissonMeasure_le P E hE B hB hpos hlam A

/-- **Proposition `prop:AGG`** (Arratia–Goldstein–Gordon), for an arbitrary finite index type and
a rate `lam` given with its defining equation `lam = ∑ i, P(E i)`: there is one `f` with
`‖f‖_∞ ≤ 1` such that `d_TV(W, Po(λ)) ≤ 2 (b_1 + b_2 + b_3)`. -/
theorem exists_paperTVDist_le_AGG (P : Measure Ω) [IsProbabilityMeasure P]
    (E : ι → Set Ω) (hE : ∀ i, MeasurableSet (E i)) (B : ι → Finset ι) (hB : ∀ i, i ∈ B i)
    (lam : ℝ≥0) (hlam : (lam : ℝ) = ∑ i, P.real (E i)) :
    ∃ f : ℕ → ℝ, (∀ k, |f k| ≤ 1) ∧
      paperTVDist (P.map (fun ω => ∑ i, (E i).indicator (1 : Ω → ℕ) ω))
          (poissonMeasure lam) ≤
        2 * (∑ i, ∑ j ∈ B i, P.real (E i) * P.real (E j) +
          ∑ i, ∑ j ∈ B i \ {i}, P.real (E i ∩ E j) +
          ∑ i, |∫ ω, ((E i).indicator (1 : Ω → ℝ) ω - P.real (E i)) *
            f (1 + ∑ j ∈ Finset.univ \ B i, (E j).indicator (1 : Ω → ℕ) ω) ∂P|) := by
  obtain ⟨f, hf, h⟩ := exists_paperTVDist_le_two_mul_add P E hE B hB lam hlam
  refine ⟨f, hf, h.trans ?_⟩
  have h3 := Finset.sum_nonneg (s := Finset.univ) fun i (_ : i ∈ Finset.univ) =>
    abs_nonneg (∫ ω, ((E i).indicator (1 : Ω → ℝ) ω - P.real (E i)) *
      f (1 + ∑ j ∈ Finset.univ \ B i, (E j).indicator (1 : Ω → ℕ) ω) ∂P)
  linarith

/-- **Proposition `prop:AGG`** in the source's notation (lines 1600–1614): indicators
`I^n_i = 1_{E i}` indexed by `[n] = Fin n` on a probability space, `q^n_i = P(E i)`,
`λ^n = ∑ q^n_i`, `W^n = ∑ I^n_i`, and `B^n_i ⊆ [n]` with `i ∈ B^n_i`. There exists `f_n` with
`‖f_n‖_∞ ≤ 1` such that `d_TV(W^n, Po(λ^n)) ≤ 2 (b^n_1 + b^n_2 + b^n_3)`, where `d_TV` is the
`[0, 1]`-valued `paperTVDist`. -/
theorem prop_AGG {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (E : Fin n → Set Ω) (hE : ∀ i, MeasurableSet (E i)) (B : Fin n → Finset (Fin n))
    (hB : ∀ i, i ∈ B i) :
    ∃ f : ℕ → ℝ, (∀ k, |f k| ≤ 1) ∧
      paperTVDist (P.map (fun ω => ∑ i, (E i).indicator (1 : Ω → ℕ) ω))
          (poissonMeasure (∑ i, P.real (E i)).toNNReal) ≤
        2 * (∑ i, ∑ j ∈ B i, P.real (E i) * P.real (E j) +
          ∑ i, ∑ j ∈ B i \ {i}, P.real (E i ∩ E j) +
          ∑ i, |∫ ω, ((E i).indicator (1 : Ω → ℝ) ω - P.real (E i)) *
            f (1 + ∑ j ∈ Finset.univ \ B i, (E j).indicator (1 : Ω → ℕ) ω) ∂P|) :=
  exists_paperTVDist_le_AGG P E hE B hB _
    (Real.coe_toNNReal _ (Finset.sum_nonneg fun _ _ => measureReal_nonneg))

end PoissonDeclumping.ChenStein
