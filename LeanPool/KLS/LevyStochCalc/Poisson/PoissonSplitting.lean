/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# Poisson splitting

A Poisson number `K` of independent marks `X₀, X₁, …` with common law `ρ`, independent of `K`,
scattered over pairwise disjoint measurable sets `B₁, …, Bₙ`: the counts
`Nᵢ = ∑_{j < K} 1_{Bᵢ}(Xⱼ)` are independent, and `Nᵢ` is Poisson with mean `r ρ(Bᵢ)`.

The joint characteristic function is computed by conditioning on `K`: given `K = m`, the
marks are independent, so `𝔼 exp(i ∑ᵢ tᵢ Nᵢ) = ∑ₘ P(K = m) cₘ` with
`c = ∑ᵢ ρ(Bᵢ) e^{i tᵢ} + (1 − ∑ᵢ ρ(Bᵢ))`, and the exponential series gives
`exp(r (c − 1)) = ∏ᵢ exp(r ρ(Bᵢ) (e^{i tᵢ} − 1))`, the characteristic function of the product of
the Poisson laws.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Complex Function
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {ρ : Measure 𝓧} [IsProbabilityMeasure ρ]
  {K : Ω → ℕ} {X : ℕ → Ω → 𝓧} {r : ℝ≥0}

/-- The number of the first `K` marks that fall in `B`. -/
noncomputable def markCount (K : Ω → ℕ) (X : ℕ → Ω → 𝓧) (B : Set 𝓧) (ω : Ω) : ℕ :=
  ∑ j ∈ Finset.range (K ω), B.indicator (1 : 𝓧 → ℕ) (X j ω)

lemma markCount_measurable (mK : Measurable K) (mX : ∀ j, Measurable (X j)) {B : Set 𝓧}
    (hB : MeasurableSet B) : Measurable (markCount K X B) := by
  have h : Measurable
      (fun p : Ω × ℕ => ∑ j ∈ Finset.range p.2, B.indicator (1 : 𝓧 → ℕ) (X j p.1)) := by
    refine measurable_from_prod_countable_left fun m => ?_
    change Measurable fun ω : Ω => ∑ j ∈ Finset.range m, B.indicator (1 : 𝓧 → ℕ) (X j ω)
    exact Finset.measurable_sum _ fun j _ => (measurable_one.indicator hB).comp (mX j)
  exact h.comp (measurable_id.prodMk mK)

lemma markCount_cast_real (B : Set 𝓧) (ω : Ω) :
    (markCount K X B ω : ℝ) = ∑ j ∈ Finset.range (K ω), B.indicator (1 : 𝓧 → ℝ) (X j ω) := by
  unfold markCount
  rw [Nat.cast_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : X j ω ∈ B <;> simp [h]

lemma markCount_measurable_real (mK : Measurable K) (mX : ∀ j, Measurable (X j)) {B : Set 𝓧}
    (hB : MeasurableSet B) : Measurable (fun ω => (markCount K X B ω : ℝ)) :=
  (Measurable.of_discrete (f := (Nat.cast : ℕ → ℝ))).comp (markCount_measurable mK mX hB)

section CharFun

variable {n : ℕ} (B : Fin n → Set 𝓧) (t : Fin n → ℝ)

/-- The factor contributed by one mark to the joint characteristic function of the counts. -/
noncomputable def markPhase (x : 𝓧) : ℂ :=
  exp ((∑ i, t i * (B i).indicator (1 : 𝓧 → ℝ) x : ℝ) * I)

lemma markPhase_measurable (hB : ∀ i, MeasurableSet (B i)) : Measurable (markPhase B t) := by
  unfold markPhase
  refine Complex.measurable_exp.comp (Measurable.mul_const ?_ I)
  refine Complex.measurable_ofReal.comp (Finset.measurable_sum _ fun i _ => ?_)
  exact measurable_const.mul (measurable_const.indicator (hB i))

lemma norm_markPhase (x : 𝓧) : ‖markPhase B t x‖ = 1 := by
  unfold markPhase
  rw [Complex.norm_exp_ofReal_mul_I]

/-- The exponential of the joint phase of the counts is the product of the mark phases. -/
lemma exp_sum_markCount (ω : Ω) :
    exp ((∑ i, (markCount K X (B i) ω : ℝ) * t i : ℝ) * I)
      = ∏ j ∈ Finset.range (K ω), markPhase B t (X j ω) := by
  have hreal : (∑ i, (markCount K X (B i) ω : ℝ) * t i)
      = ∑ j ∈ Finset.range (K ω), ∑ i, t i * (B i).indicator (1 : 𝓧 → ℝ) (X j ω) := by
    simp_rw [markCount_cast_real, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => mul_comm _ _
  unfold markPhase
  rw [← Complex.exp_sum]
  congr 1
  rw [hreal]
  push_cast
  rw [Finset.sum_mul]

/-- The integral of the mark phase against the law of a mark, for pairwise disjoint sets. -/
lemma integral_markPhase (hB : ∀ i, MeasurableSet (B i)) (hdisj : Pairwise (Disjoint on B)) :
    ∫ x, markPhase B t x ∂ρ
      = ∑ i, (ρ.real (B i) : ℂ) * exp (t i * I) + (1 - ∑ i, (ρ.real (B i) : ℂ)) := by
  classical
  have hU : MeasurableSet (⋃ i, B i) := MeasurableSet.iUnion hB
  -- pointwise decomposition of the phase
  have hpt : ∀ x, markPhase B t x
      = ∑ i, (B i).indicator (fun _ => exp (t i * I)) x
        + (⋃ i, B i)ᶜ.indicator (fun _ => (1 : ℂ)) x := by
    intro x
    unfold markPhase
    by_cases hx : x ∈ ⋃ i, B i
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
      have hsum : (∑ k, t k * (B k).indicator 1 x : ℝ) = t i := by
        rw [Finset.sum_eq_single i]
        · simp [Set.indicator_of_mem hi]
        · intro k _ hk
          rw [Set.indicator_of_notMem (fun hxk => hk ?_), mul_zero]
          by_contra hne
          exact Set.disjoint_left.1 (hdisj hne) hxk hi
        · simp
      rw [hsum, Finset.sum_eq_single i]
      · rw [Set.indicator_of_mem hi,
          Set.indicator_of_notMem (fun h : x ∈ (⋃ i, B i)ᶜ => h hx), add_zero]
      · intro k _ hk
        refine Set.indicator_of_notMem (fun hxk => hk ?_) _
        by_contra hne
        exact Set.disjoint_left.1 (hdisj hne) hxk hi
      · simp
    · have hsum : (∑ k, t k * (B k).indicator 1 x : ℝ) = 0 := by
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [Set.indicator_of_notMem (fun hxk => hx (Set.mem_iUnion.2 ⟨k, hxk⟩)), mul_zero]
      rw [hsum]
      simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero]
      rw [Finset.sum_eq_zero fun k _ =>
        Set.indicator_of_notMem (fun hxk => hx (Set.mem_iUnion.2 ⟨k, hxk⟩)) _, zero_add,
        Set.indicator_of_mem (Set.mem_compl hx)]
  simp_rw [hpt]
  have hint1 : ∀ i, Integrable ((B i).indicator (fun _ : 𝓧 => exp (t i * I))) ρ := fun i =>
    (integrable_const _).indicator (hB i)
  have hint2 : Integrable ((⋃ i, B i)ᶜ.indicator (fun _ => (1 : ℂ))) ρ :=
    (integrable_const _).indicator hU.compl
  rw [integral_add (integrable_finsetSum _ fun i _ => hint1 i) hint2, integral_finsetSum]
  · congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_indicator_const _ (hB i), Complex.real_smul]
    · rw [integral_indicator_const _ hU.compl, Complex.real_smul, mul_one, measureReal_compl hU,
        probReal_univ]
      have hU' : ρ.real (⋃ i, B i) = ∑ i, ρ.real (B i) := by
        rw [measureReal_def, measure_iUnion hdisj hB, tsum_fintype,
          ENNReal.toReal_sum (fun i _ => measure_ne_top _ _)]
        rfl
      rw [hU']
      push_cast
      ring
  · exact fun i _ => hint1 i

variable {B t}

omit [IsProbabilityMeasure P] [IsProbabilityMeasure ρ] in
/-- For independent marks with common law `ρ`, the expectation of the product of the first `m`
mark phases is the `m`-th power of the integral of the phase. -/
lemma integral_prod_markPhase (hB : ∀ i, MeasurableSet (B i)) (hX : ∀ j, HasLaw (X j) ρ P)
    (mX : ∀ j, Measurable (X j)) (hXi : iIndepFun X P) (m : ℕ) :
    ∫ ω, ∏ j ∈ Finset.range m, markPhase B t (X j ω) ∂P = (∫ x, markPhase B t x ∂ρ) ^ m := by
  have hg := markPhase_measurable B t hB
  have hind : iIndepFun (fun j : Fin m => fun ω => markPhase B t (X j ω)) P :=
    (hXi.comp (fun _ => markPhase B t) (fun _ => hg)).precomp Fin.val_injective
  have h := hind.integral_fun_prod_eq_prod_integral
    (fun j => (hg.comp (mX j)).aestronglyMeasurable)
  have hone : ∀ j : Fin m, ∫ ω, markPhase B t (X j ω) ∂P = ∫ x, markPhase B t x ∂ρ := by
    intro j
    rw [← (hX j).map_eq, integral_map (mX j).aemeasurable hg.aestronglyMeasurable]
  calc ∫ ω, ∏ j ∈ Finset.range m, markPhase B t (X j ω) ∂P
      = ∫ ω, ∏ j : Fin m, markPhase B t (X j ω) ∂P := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
        exact (Fin.prod_univ_eq_prod_range (fun j => markPhase B t (X j ω)) m).symm
    _ = ∏ j : Fin m, ∫ ω, markPhase B t (X j ω) ∂P := h
    _ = (∫ x, markPhase B t x ∂ρ) ^ m := by
        rw [Finset.prod_congr rfl fun j _ => hone j, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin]

omit [IsProbabilityMeasure ρ] in
/-- Conditioning on the number of marks: the expectation of the product of the mark phases of
the first `K` marks, for `K` independent of the marks. -/
lemma integral_prod_range_markPhase (hB : ∀ i, MeasurableSet (B i)) (mK : Measurable K)
    (hX : ∀ j, HasLaw (X j) ρ P) (mX : ∀ j, Measurable (X j)) (hXi : iIndepFun X P)
    (hKX : IndepFun K (fun ω j => X j ω) P) :
    ∫ ω, ∏ j ∈ Finset.range (K ω), markPhase B t (X j ω) ∂P
      = ∑' m, (P.real (K ⁻¹' {m}) : ℂ) * (∫ x, markPhase B t x ∂ρ) ^ m := by
  have hg := markPhase_measurable B t hB
  set F : ℕ → Ω → ℂ := fun m ω => ∏ j ∈ Finset.range m, markPhase B t (X j ω) with hF
  have hF_meas : ∀ m, Measurable (F m) := fun m =>
    Finset.measurable_prod _ fun j _ => hg.comp (mX j)
  have hF_norm : ∀ m ω, ‖F m ω‖ = 1 := by
    intro m ω
    simp only [hF, norm_prod, norm_markPhase, Finset.prod_const_one]
  set G : ℕ → Ω → ℂ := fun m ω => ({m} : Set ℕ).indicator (fun _ => (1 : ℂ)) (K ω) * F m ω
    with hG
  have hpt : ∀ ω, (∏ j ∈ Finset.range (K ω), markPhase B t (X j ω)) = ∑' m, G m ω := by
    intro ω
    rw [tsum_eq_single (K ω)]
    · simp [hG, hF]
    · intro m hm
      simp only [hG]
      rw [Set.indicator_of_notMem (fun h => hm (Set.mem_singleton_iff.1 h).symm), zero_mul]
  have hG_meas : ∀ m, Measurable (G m) := fun m =>
    ((measurable_const.indicator (measurableSet_singleton m)).comp mK).mul (hF_meas m)
  have hG_norm : ∀ m ω, ‖G m ω‖ₑ = (K ⁻¹' {m}).indicator (fun _ => (1 : ℝ≥0∞)) ω := by
    intro m ω
    simp only [hG]
    by_cases h : K ω = m
    · have h1 : ω ∈ K ⁻¹' {m} := h
      rw [Set.indicator_of_mem (Set.mem_singleton_iff.2 h), Set.indicator_of_mem h1, one_mul,
        ← ofReal_norm, hF_norm, ENNReal.ofReal_one]
    · have h1 : ω ∉ K ⁻¹' {m} := h
      rw [Set.indicator_of_notMem (fun h' => h (Set.mem_singleton_iff.1 h')),
        Set.indicator_of_notMem h1, zero_mul, eNorm_zero]
  simp_rw [hpt]
  rw [integral_tsum (fun m => (hG_meas m).aestronglyMeasurable)]
  · refine tsum_congr fun m => ?_
    have hf : AEStronglyMeasurable (fun k : ℕ => ({m} : Set ℕ).indicator (fun _ => (1 : ℂ)) k)
        (P.map K) := Measurable.aestronglyMeasurable (Measurable.of_discrete)
    have hgm : AEStronglyMeasurable
        (fun v : ℕ → 𝓧 => ∏ j ∈ Finset.range m, markPhase B t (v j))
        (P.map (fun ω j => X j ω)) :=
      (Finset.measurable_prod _ fun j _ => hg.comp (measurable_pi_apply j)).aestronglyMeasurable
    have h1 := hKX.integral_fun_comp_mul_comp mK.aemeasurable
      (Measurable.of_eval mX).aemeasurable hf hgm
    simp only [hG, hF]
    rw [h1, integral_prod_markPhase hB hX mX hXi m]
    congr 1
    have hind : (fun ω => ({m} : Set ℕ).indicator (fun _ => (1 : ℂ)) (K ω))
        = (K ⁻¹' {m}).indicator (fun _ => (1 : ℂ)) := by
      funext ω
      by_cases h : K ω = m
      · rw [Set.indicator_of_mem (Set.mem_singleton_iff.2 h),
          Set.indicator_of_mem (show ω ∈ K ⁻¹' {m} from h)]
      · rw [Set.indicator_of_notMem (fun h' => h (Set.mem_singleton_iff.1 h')),
          Set.indicator_of_notMem (show ω ∉ K ⁻¹' {m} from h)]
    rw [hind, integral_indicator_const _ (mK (measurableSet_singleton m)), Complex.real_smul,
      mul_one]
  · have hle : ∀ m, ∫⁻ ω, ‖G m ω‖ₑ ∂P = P (K ⁻¹' {m}) := by
      intro m
      rw [lintegral_congr (hG_norm m),
        lintegral_indicator_const (mK (measurableSet_singleton m)), one_mul]
    simp_rw [hle]
    rw [← measure_iUnion (f := fun m => K ⁻¹' {m})
      (fun i j hij => Set.disjoint_left.2 fun ω (h1 : K ω = i) (h2 : K ω = j) =>
        hij (h1.symm.trans h2))
      (fun m => mK (measurableSet_singleton m))]
    exact measure_ne_top _ _

/-- The exponential series weighted by the Poisson probabilities. -/
lemma tsum_poisson_pow (r : ℝ≥0) (c : ℂ) :
    ∑' m : ℕ, ((Real.exp (-r) * r ^ m / m.factorial : ℝ) : ℂ) * c ^ m = exp (r * (c - 1)) := by
  have h := NormedSpace.expSeries_div_hasSum_exp ((r : ℂ) * c)
  rw [← Complex.exp_eq_exp_ℂ] at h
  have h2 := (h.mul_left (exp (-(r : ℂ)))).tsum_eq
  rw [← Complex.exp_add] at h2
  rw [show (r : ℂ) * (c - 1) = -(r : ℂ) + r * c by ring, ← h2]
  refine tsum_congr fun m => ?_
  push_cast
  ring

end CharFun

section Law

variable {n : ℕ} {B : Fin n → Set 𝓧}

/-- The joint characteristic function of the counts of a Poisson number of independent marks
on pairwise disjoint sets. -/
theorem charFun_map_markCount (hK : HasLaw K Po(r) P) (mK : Measurable K)
    (hX : ∀ j, HasLaw (X j) ρ P) (mX : ∀ j, Measurable (X j)) (hXi : iIndepFun X P)
    (hKX : IndepFun K (fun ω j => X j ω) P) (hB : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise (Disjoint on B)) (t : PiLp 2 (fun _ : Fin n => ℝ)) :
    charFun (P.map (fun ω => WithLp.toLp 2 (fun i => (markCount K X (B i) ω : ℝ)))) t
      = ∏ i, charFun Po(ℝ, r * (ρ (B i)).toNNReal) (t.ofLp i) := by
  have hV : Measurable (fun ω => WithLp.toLp 2 (fun i => (markCount K X (B i) ω : ℝ))) :=
    (MeasurableEquiv.toLp 2 _).measurable.comp
      (Measurable.of_eval fun i => markCount_measurable_real mK mX (hB i))
  rw [charFun_apply, integral_map hV.aemeasurable (by fun_prop)]
  have hinner : ∀ ω, (inner ℝ (WithLp.toLp 2 (fun i => (markCount K X (B i) ω : ℝ))) t : ℝ)
      = ∑ i, (markCount K X (B i) ω : ℝ) * t.ofLp i := by
    intro ω
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Real.inner_apply _ _
  simp_rw [hinner, exp_sum_markCount B t.ofLp]
  rw [integral_prod_range_markPhase hB mK hX mX hXi hKX, integral_markPhase B t.ofLp hB hdisj]
  have hpmf : ∀ m, P.real (K ⁻¹' {m}) = Real.exp (-r) * r ^ m / m.factorial := by
    intro m
    rw [measureReal_def, ← Measure.map_apply mK (measurableSet_singleton m), hK.map_eq,
      ← measureReal_def]
    exact poissonMeasure_real_singleton r m
  simp_rw [hpmf]
  rw [tsum_poisson_pow]
  simp_rw [charFun_map_cast_poissonMeasure]
  rw [← Complex.exp_sum]
  congr 1
  have hp : ∀ i, (((r * (ρ (B i)).toNNReal : ℝ≥0) : ℝ) : ℂ) = (r : ℂ) * (ρ.real (B i) : ℂ) := by
    intro i
    push_cast
    rfl
  simp_rw [hp]
  have h3 : ∀ i, (r : ℂ) * (ρ.real (B i) : ℂ) * (exp (t.ofLp i * I) - 1)
      = (r : ℂ) * ((ρ.real (B i) : ℂ) * exp (t.ofLp i * I)) - (r : ℂ) * (ρ.real (B i) : ℂ) :=
    fun i => by ring
  simp_rw [h3, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- The joint law of the counts of a Poisson number of independent marks on pairwise disjoint
sets is the product of Poisson laws, as a law on `EuclideanSpace ℝ (Fin n)`. -/
theorem map_markCount_toLp_eq (hK : HasLaw K Po(r) P) (mK : Measurable K)
    (hX : ∀ j, HasLaw (X j) ρ P) (mX : ∀ j, Measurable (X j)) (hXi : iIndepFun X P)
    (hKX : IndepFun K (fun ω j => X j ω) P) (hB : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise (Disjoint on B)) :
    P.map (fun ω => WithLp.toLp 2 (fun i => (markCount K X (B i) ω : ℝ)))
      = (Measure.pi (fun i => Po(ℝ, r * (ρ (B i)).toNNReal))).map (WithLp.toLp 2) := by
  have hV : Measurable (fun ω => WithLp.toLp 2 (fun i => (markCount K X (B i) ω : ℝ))) :=
    (MeasurableEquiv.toLp 2 _).measurable.comp
      (Measurable.of_eval fun i => markCount_measurable_real mK mX (hB i))
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [charFun_map_markCount hK mK hX mX hXi hKX hB hdisj, charFun_pi]

/-- The joint law of the counts, as a law on `Fin n → ℝ`. -/
theorem map_markCount_eq_pi (hK : HasLaw K Po(r) P) (mK : Measurable K)
    (hX : ∀ j, HasLaw (X j) ρ P) (mX : ∀ j, Measurable (X j)) (hXi : iIndepFun X P)
    (hKX : IndepFun K (fun ω j => X j ω) P) (hB : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise (Disjoint on B)) :
    P.map (fun ω i => (markCount K X (B i) ω : ℝ))
      = Measure.pi (fun i => Po(ℝ, r * (ρ (B i)).toNNReal)) := by
  have h := congrArg (Measure.map (WithLp.ofLp : PiLp 2 (fun _ : Fin n => ℝ) → Fin n → ℝ))
    (map_markCount_toLp_eq hK mK hX mX hXi hKX hB hdisj)
  have hofLp : Measurable (WithLp.ofLp : PiLp 2 (fun _ : Fin n => ℝ) → Fin n → ℝ) :=
    (MeasurableEquiv.toLp 2 _).symm.measurable
  have hN : Measurable (fun ω i => (markCount K X (B i) ω : ℝ)) :=
    Measurable.of_eval fun i => markCount_measurable_real mK mX (hB i)
  have hT : Measurable (WithLp.toLp 2 : (Fin n → ℝ) → PiLp 2 (fun _ : Fin n => ℝ)) :=
    (MeasurableEquiv.toLp 2 _).measurable
  have hV : Measurable (fun ω => WithLp.toLp 2 (fun i => (markCount K X (B i) ω : ℝ))) :=
    hT.comp hN
  rw [Measure.map_map hofLp hV, Measure.map_map hofLp hT] at h
  have e1 : (WithLp.ofLp ∘ fun ω => WithLp.toLp 2 (fun i => (markCount K X (B i) ω : ℝ)))
      = fun ω i => (markCount K X (B i) ω : ℝ) := by
    funext ω
    simp
  have e2 : (WithLp.ofLp ∘ (WithLp.toLp 2 : (Fin n → ℝ) → PiLp 2 (fun _ : Fin n => ℝ))) = id := by
    funext v
    simp
  rw [e1, e2, Measure.map_id] at h
  exact h

/-- Each count is Poisson with mean `r ρ(Bᵢ)`, as a real random variable. -/
theorem hasLaw_markCount_real (hK : HasLaw K Po(r) P) (mK : Measurable K)
    (hX : ∀ j, HasLaw (X j) ρ P) (mX : ∀ j, Measurable (X j)) (hXi : iIndepFun X P)
    (hKX : IndepFun K (fun ω j => X j ω) P) (hB : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise (Disjoint on B)) (i : Fin n) :
    HasLaw (fun ω => (markCount K X (B i) ω : ℝ)) Po(ℝ, r * (ρ (B i)).toNNReal) P := by
  refine ⟨(markCount_measurable_real mK mX (hB i)).aemeasurable, ?_⟩
  have hN : Measurable (fun ω i => (markCount K X (B i) ω : ℝ)) :=
    Measurable.of_eval fun i => markCount_measurable_real mK mX (hB i)
  calc P.map (fun ω => (markCount K X (B i) ω : ℝ))
      = (P.map (fun ω i => (markCount K X (B i) ω : ℝ))).map (fun v => v i) :=
        (Measure.map_map (measurable_pi_apply i) hN).symm
    _ = Po(ℝ, r * (ρ (B i)).toNNReal) := by
        rw [map_markCount_eq_pi hK mK hX mX hXi hKX hB hdisj, ← Measure.infinitePi_eq_pi,
          Measure.infinitePi_map_eval]

/-- The counts on pairwise disjoint sets are independent, as real random variables. -/
theorem iIndepFun_markCount_real (hK : HasLaw K Po(r) P) (mK : Measurable K)
    (hX : ∀ j, HasLaw (X j) ρ P) (mX : ∀ j, Measurable (X j)) (hXi : iIndepFun X P)
    (hKX : IndepFun K (fun ω j => X j ω) P) (hB : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise (Disjoint on B)) :
    iIndepFun (fun i ω => (markCount K X (B i) ω : ℝ)) P := by
  rw [iIndepFun_iff_map_fun_eq_pi_map
    (fun i => (markCount_measurable_real mK mX (hB i)).aemeasurable),
    map_markCount_eq_pi hK mK hX mX hXi hKX hB hdisj]
  congr 1
  funext i
  exact (hasLaw_markCount_real hK mK hX mX hXi hKX hB hdisj i).map_eq.symm

/-- Each count is Poisson with mean `r ρ(Bᵢ)`, as an `ℝ≥0∞`-valued random variable. -/
theorem map_markCount_ennreal (hK : HasLaw K Po(r) P) (mK : Measurable K)
    (hX : ∀ j, HasLaw (X j) ρ P) (mX : ∀ j, Measurable (X j)) (hXi : iIndepFun X P)
    (hKX : IndepFun K (fun ω j => X j ω) P) (hB : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise (Disjoint on B)) (i : Fin n) :
    P.map (fun ω => (markCount K X (B i) ω : ℝ≥0∞))
      = Po(r * (ρ (B i)).toNNReal).map (fun k : ℕ => (k : ℝ≥0∞)) := by
  have h1 : (fun ω => (markCount K X (B i) ω : ℝ≥0∞))
      = ENNReal.ofReal ∘ (fun ω => (markCount K X (B i) ω : ℝ)) := by
    funext ω
    simp [ENNReal.ofReal_natCast]
  rw [h1, ← Measure.map_map ENNReal.measurable_ofReal (markCount_measurable_real mK mX (hB i)),
    (hasLaw_markCount_real hK mK hX mX hXi hKX hB hdisj i).map_eq,
    Measure.map_map ENNReal.measurable_ofReal Measurable.of_discrete]
  congr 1
  funext k
  simp [ENNReal.ofReal_natCast]

/-- The counts on pairwise disjoint sets are independent, as `ℝ≥0∞`-valued random variables. -/
theorem iIndepFun_markCount_ennreal (hK : HasLaw K Po(r) P) (mK : Measurable K)
    (hX : ∀ j, HasLaw (X j) ρ P) (mX : ∀ j, Measurable (X j)) (hXi : iIndepFun X P)
    (hKX : IndepFun K (fun ω j => X j ω) P) (hB : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise (Disjoint on B)) :
    iIndepFun (fun i ω => (markCount K X (B i) ω : ℝ≥0∞)) P := by
  have h := (iIndepFun_markCount_real hK mK hX mX hXi hKX hB hdisj).comp
    (fun _ => ENNReal.ofReal) (fun _ => ENNReal.measurable_ofReal)
  have e : (fun i ω => (markCount K X (B i) ω : ℝ≥0∞))
      = fun i => ENNReal.ofReal ∘ (fun ω => (markCount K X (B i) ω : ℝ)) := by
    funext i ω
    simp [ENNReal.ofReal_natCast]
  rw [e]
  exact h

/-- The counts on a pairwise disjoint family of sets indexed by an arbitrary type are
independent, as `ℝ≥0∞`-valued random variables. -/
theorem iIndepFun_markCount_ennreal' {ι : Type*} {B : ι → Set 𝓧} (hK : HasLaw K Po(r) P)
    (mK : Measurable K) (hX : ∀ j, HasLaw (X j) ρ P) (mX : ∀ j, Measurable (X j))
    (hXi : iIndepFun X P) (hKX : IndepFun K (fun ω j => X j ω) P)
    (hB : ∀ i, MeasurableSet (B i)) (hdisj : Pairwise (Disjoint on B)) :
    iIndepFun (fun i ω => (markCount K X (B i) ω : ℝ≥0∞)) P := by
  rw [iIndepFun_iff_finset]
  intro s
  have h := iIndepFun_markCount_ennreal hK mK hX mX hXi hKX
    (B := fun k : Fin s.card => B (s.equivFin.symm k)) (fun k => hB _)
    (fun k l hkl => hdisj fun h => hkl (s.equivFin.symm.injective (Subtype.ext h)))
  have h' := h.precomp s.equivFin.injective
  simp only [Equiv.symm_apply_apply] at h'
  exact h'

end Law

end LevyStochCalc.Poisson
