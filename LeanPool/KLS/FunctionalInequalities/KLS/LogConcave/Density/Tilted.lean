/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Density.FromBorell
public import Mathlib.MeasureTheory.Measure.Tilted
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Density.BorellRepresentation.Construction
public import LeanPool.KLS.FunctionalInequalities.Probability.LogConcave
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Density.BorellRepresentation.Basic

/-!
# Tilted laws of Haar measure

For a potential `W` on a finite-dimensional real inner product space and a Haar measure `m`,
the tilted law `m.tilted (-W)` has density `e^{-W} / ∫ e^{-W} dm` with respect to `m`. When it is
a probability law, `e^{-W}` is `m`-integrable; the law then has full support, and it is
log-concave when `W` is continuous and convex (its density is a log-concave Borell density for
Lebesgue measure `volume`).
-/

@[expose] public section

section

open MeasureTheory Set

namespace FunctionalInequalities.KLS.LogConcave

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {ν : ProbabilityMeasure V}

section TiltedDensityIntegrability

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V]
/-- A tilted law of total mass one has an integrable density: `e^{-W} ∈ L¹(m)`. -/
theorem integrable_exp_neg_of_eq_tilted {m : Measure V} {W : V → ℝ}
    (hνW : (ν : Measure V) = m.tilted (-W)) :
    Integrable (fun x => Real.exp (-W x)) m := by
  by_contra h
  have h' : ¬ Integrable (fun x => Real.exp ((-W) x)) m := by
    intro hI
    apply h
    simpa using hI
  have hzero : m.tilted (-W) = 0 :=
    tilted_of_not_integrable h'
  have hνzero : (ν : Measure V) = 0 := by
    rw [hνW, hzero]
  have huniv : (ν : Measure V) Set.univ = 1 := by
    simp
  rw [hνzero] at huniv
  norm_num at huniv

/-- A tilted law of total mass one has a positive normalizing constant `∫ e^{-W} dm`. -/
theorem integral_exp_neg_pos_of_eq_tilted {m : Measure V} {W : V → ℝ}
    (hνW : (ν : Measure V) = m.tilted (-W)) :
    0 < ∫ x, Real.exp (-W x) ∂m := by
  have hint : Integrable (fun x => Real.exp (-W x)) m :=
    integrable_exp_neg_of_eq_tilted hνW
  have hm : m ≠ 0 := by
    intro hmzero
    have hzero : m.tilted (-W) = 0 := by
      simp [hmzero, Measure.tilted]
    have hνzero : (ν : Measure V) = 0 := hνW.trans hzero
    have huniv : (ν : Measure V) Set.univ = 1 := by
      simp
    rw [hνzero] at huniv
    norm_num at huniv
  have hmuniv : 0 < m Set.univ := by
    rw [pos_iff_ne_zero]
    intro hzero
    exact hm (Measure.measure_univ_eq_zero.mp hzero)
  have hsupp :
      Function.support (fun x => Real.exp (-W x)) = (Set.univ : Set V) := by
    ext x
    simp [Function.support]
  rw [integral_pos_iff_support_of_nonneg (fun x => (Real.exp_pos _).le) hint, hsupp]
  exact hmuniv

end TiltedDensityIntegrability

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- For `W` convex on a set `s` and `Z > 0`, the normalized weight `e^{-W} / Z` satisfies
`ρ(x)^t ρ(y)^{1-t} ≤ ρ(t x + (1 - t) y)` for `x, y ∈ s` and `0 < t < 1`. -/
theorem rpow_mul_rpow_le_of_convexOn_of_mem {s : Set V} {W : V → ℝ} (hconv : ConvexOn ℝ s W)
    {Z : ℝ} (hZ : 0 < Z) {x y : V} (hx : x ∈ s) (hy : y ∈ s) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t < 1) :
    (Real.exp (-W x) / Z) ^ t * (Real.exp (-W y) / Z) ^ (1 - t) ≤
      Real.exp (-W (t • x + (1 - t) • y)) / Z := by
  have hAx : 0 < Real.exp (-W x) / Z :=
    div_pos (Real.exp_pos _) hZ
  have hAy : 0 < Real.exp (-W y) / Z :=
    div_pos (Real.exp_pos _) hZ
  have hlogx :
      Real.log (Real.exp (-W x) / Z) = -W x - Real.log Z := by
    rw [Real.log_div (ne_of_gt (Real.exp_pos _)) (ne_of_gt hZ), Real.log_exp]
  have hlogy :
      Real.log (Real.exp (-W y) / Z) = -W y - Real.log Z := by
    rw [Real.log_div (ne_of_gt (Real.exp_pos _)) (ne_of_gt hZ), Real.log_exp]
  have hleft :
      (Real.exp (-W x) / Z) ^ t * (Real.exp (-W y) / Z) ^ (1 - t) =
        Real.exp ((-W x - Real.log Z) * t +
          (-W y - Real.log Z) * (1 - t)) := by
    rw [Real.rpow_def_of_pos hAx, Real.rpow_def_of_pos hAy, hlogx, hlogy,
      ← Real.exp_add]
  have hright :
      Real.exp (-W (t • x + (1 - t) • y)) / Z =
        Real.exp (-W (t • x + (1 - t) • y) - Real.log Z) := by
    calc
      Real.exp (-W (t • x + (1 - t) • y)) / Z =
          Real.exp (-W (t • x + (1 - t) • y)) / Real.exp (Real.log Z) := by
            rw [Real.exp_log hZ]
      _ = Real.exp (-W (t • x + (1 - t) • y) - Real.log Z) := by
        rw [Real.exp_sub]
  rw [hleft, hright]
  apply Real.exp_le_exp.mpr
  have hW0 :=
    hconv.2 hx hy ht0.le (by linarith : 0 ≤ 1 - t) (by ring : t + (1 - t) = 1)
  have hW :
      W (t • x + (1 - t) • y) ≤ t * W x + (1 - t) * W y := by
    simpa [smul_eq_mul] using hW0
  calc
    (-W x - Real.log Z) * t + (-W y - Real.log Z) * (1 - t) =
        -(t * W x + (1 - t) * W y) - Real.log Z := by ring
    _ ≤ -W (t • x + (1 - t) • y) - Real.log Z := by linarith

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- For convex `W` and `Z > 0`, the normalized weight `e^{-W} / Z` is log-concave:
`ρ(x)^t ρ(y)^{1-t} ≤ ρ(t x + (1 - t) y)` for `0 < t < 1`. -/
theorem rpow_mul_rpow_le_of_convexOn {W : V → ℝ} (hconv : ConvexOn ℝ Set.univ W) {Z : ℝ}
    (hZ : 0 < Z) (x y : V) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (Real.exp (-W x) / Z) ^ t * (Real.exp (-W y) / Z) ^ (1 - t) ≤
      Real.exp (-W (t • x + (1 - t) • y)) / Z :=
  rpow_mul_rpow_le_of_convexOn_of_mem hconv hZ (Set.mem_univ x) (Set.mem_univ y) ht0 ht1

omit [FiniteDimensional ℝ V] in
/-- For continuous convex `W`, the density `e^{-W} / ∫ e^{-W} dm` of `ν = m.tilted (-W)` is a
log-concave Borell density with respect to `m`. -/
theorem isBorellDensity_of_eq_tilted {m : Measure V} {W : V → ℝ}
    (hνW : (ν : Measure V) = m.tilted (-W)) (hW : Continuous W)
    (hconv : ConvexOn ℝ Set.univ W) :
    IsBorellDensity (ν : Measure V) m (fun x => Real.exp (-W x) / ∫ y, Real.exp (-W y) ∂m) := by
  have hZ : 0 < ∫ y, Real.exp (-W y) ∂m :=
    integral_exp_neg_pos_of_eq_tilted hνW
  have hcont :
      Continuous (fun x => Real.exp (-W x) / ∫ y, Real.exp (-W y) ∂m) :=
    (Real.continuous_exp.comp hW.neg).div_const _
  refine
    { measurable := hcont.measurable
      nonneg := fun x => div_nonneg (Real.exp_pos _).le hZ.le
      upperSemicontinuous := hcont.upperSemicontinuous
      logConcave := fun x y t ht0 ht1 =>
        rpow_mul_rpow_le_of_convexOn hconv hZ x y ht0 ht1
      withDensity_eq := ?_ }
  rw [hνW]
  rfl

/-- A law `ν = volume.tilted (-W)` with continuous convex `W` is log-concave: its density
`e^{-W} / ∫ e^{-W}` is a log-concave Borell density (`IsBorellDensity.compactLogConcave`). -/
theorem logConcave_of_eq_tilted {W : V → ℝ}
    (hνW : (ν : Measure V) = (volume : Measure V).tilted (-W)) (hW : Continuous W)
    (hconv : ConvexOn ℝ Set.univ W) : LogConcave ν := by
  exact
    IsBorellDensity.compactLogConcave
      (isBorellDensity_of_eq_tilted hνW hW hconv)

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] in
/-- A tilted Haar law has full support, so its support has nonempty interior. -/
theorem interior_support_nonempty_of_eq_tilted (m : Measure V) [m.IsAddHaarMeasure] {W : V → ℝ}
    (hνW : (ν : Measure V) = m.tilted (-W)) :
    (interior (ν : Measure V).support).Nonempty := by
  have hint : Integrable (fun x => Real.exp (-W x)) m :=
    integrable_exp_neg_of_eq_tilted hνW
  have hac : m ≪ (ν : Measure V) := by
    rw [hνW]
    exact absolutelyContinuous_tilted (by simpa using hint)
  have hsupp : (ν : Measure V).support = (Set.univ : Set V) := by
    apply Set.eq_univ_of_forall
    intro x
    apply (Measure.mem_support_iff_forall x).2
    intro U hU
    have hmU : 0 < m U := Measure.measure_pos_of_mem_nhds m hU
    exact pos_iff_ne_zero.2 fun h0 =>
      (pos_iff_ne_zero.1 hmU) (hac h0)
  rw [hsupp, interior_univ]
  exact Set.univ_nonempty

/-! ### Convexity of the potential of a log-concave tilted law -/

section Convexity

variable [SecondCountableTopology V] (m : Measure V) [m.IsAddHaarMeasure] {U : V → ℝ}

/-- A log-concave law `ν = m.tilted (-U)` with a continuous potential has a convex potential: the
continuous density `e^{-U} / Z` agrees with the log-concave Borell representative of `ν`, which is
continuous because `ν` has full support. Converse of `isBorellDensity_of_eq_tilted`. -/
theorem convexOn_of_eq_tilted (hν : LogConcave ν) (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : Continuous U) : ConvexOn ℝ Set.univ U := by
  have hint : Integrable (fun x => Real.exp (-U x)) m := integrable_exp_neg_of_eq_tilted hνU
  have hZ : 0 < ∫ y, Real.exp (-U y) ∂m := integral_exp_neg_pos_of_eq_tilted hνU
  set Z := ∫ y, Real.exp (-U y) ∂m with hZdef
  set q : V → ℝ := fun x => Real.exp (-U x) / Z with hqdef
  have hqpos : ∀ x, 0 < q x := fun x => div_pos (Real.exp_pos _) hZ
  have hqc : Continuous q := (Real.continuous_exp.comp hU.neg).div_const _
  have hmν : m ≪ (ν : Measure V) := by
    rw [hνU]; exact absolutelyContinuous_tilted (by simpa using hint)
  have hνm : (ν : Measure V) ≪ m := by rw [hνU]; exact tilted_absolutelyContinuous m (-U)
  have hsupp : (ν : Measure V).support = Set.univ := by
    refine Set.eq_univ_of_forall fun x => (Measure.mem_support_iff_forall x).2 fun s hs => ?_
    exact pos_iff_ne_zero.2 fun h0 =>
      (pos_iff_ne_zero.1 (Measure.measure_pos_of_mem_nhds m hs)) (hmν h0)
  obtain ⟨ρ, hρ⟩ := hν.exists_isBorellDensity_of_interior_support_nonempty m
    (interior_support_nonempty_of_eq_tilted m hνU) hνm
  have hρc : Continuous ρ := by
    have h := hρ.continuousOn_interior_support
    rw [hsupp, interior_univ] at h
    exact continuousOn_univ.mp h
  have hqd : m.withDensity (fun x => ENNReal.ofReal (q x)) = ν := by rw [hνU]; rfl
  have hae : (fun x => ENNReal.ofReal (ρ x)) =ᵐ[m] fun x => ENNReal.ofReal (q x) :=
    (withDensity_eq_iff_of_sigmaFinite hρc.measurable.ennreal_ofReal.aemeasurable
      hqc.measurable.ennreal_ofReal.aemeasurable).mp (hρ.withDensity_eq.trans hqd.symm)
  have hae' : ρ =ᵐ[m] q := by
    filter_upwards [hae] with x hx
    exact (ENNReal.ofReal_eq_ofReal_iff (hρ.nonneg x) (hqpos x).le).mp hx
  have heq : ρ = q := (hρc.ae_eq_iff_eq m hqc).mp hae'
  have hlog : ∀ x, Real.log (q x) = -U x - Real.log Z := fun x => by
    rw [hqdef, Real.log_div (Real.exp_pos _).ne' hZ.ne', Real.log_exp]
  rw [convexOn_iff_forall_pos]
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  obtain rfl : b = 1 - a := by linarith
  have h := hρ.logConcave x y a ha (by linarith)
  rw [heq] at h
  have hx' := Real.rpow_pos_of_pos (hqpos x) a
  have hy' := Real.rpow_pos_of_pos (hqpos y) (1 - a)
  have h' := Real.log_le_log (mul_pos hx' hy') h
  rw [Real.log_mul hx'.ne' hy'.ne', Real.log_rpow (hqpos x), Real.log_rpow (hqpos y), hlog, hlog,
    hlog] at h'
  simp only [smul_eq_mul]
  nlinarith

end Convexity

end FunctionalInequalities.KLS.LogConcave

/-! ### Restricted exponential densities

For closed convex `K` and `W` continuous and convex on `K`, `1_K e^{-W}` is a Borell density of `μ =
(1_K e^{-W}) dx`, so `μ` is log-concave; in particular every regular-class law (`W - κ/2 ‖·‖²`
convex) is log-concave. For a
convex `K` that need not be closed (Letwin's bounded open convex bodies), continuity on `closure K`
and convexity on `K`
suffice (`logConcave_of_eq_restricted_exp_on_closure`). -/

section
open MeasureTheory Set
open scoped Topology

namespace FunctionalInequalities.KLS.LogConcave

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/--
For closed convex `K` and `W` continuous and convex on `K`, `1_K e^{-W}` is a log-concave Borell
density of `μ = (1_K e^{-W}) dx`. Only the values of `W` on `K` enter. -/
theorem isBorellDensity_of_eq_restricted_exp_on (μ : ProbabilityMeasure E) {K : Set E}
    (hK : IsClosed K) (hKc : Convex ℝ K) {W : E → ℝ} (hW : ContinuousOn W K)
    (hWc : ConvexOn ℝ K W)
    (hμ :
      (μ : Measure E) =
        (volume : Measure E).withDensity
          (K.indicator fun x => ENNReal.ofReal (Real.exp (-W x)))) :
    IsBorellDensity (μ : Measure E) volume (K.indicator fun x => Real.exp (-W x)) := by
  classical
  let f : E → ℝ := fun x => Real.exp (-W x)
  have hf : ContinuousOn f K := hW.neg.rexp
  have hnonneg : ∀ x, 0 ≤ K.indicator f x := fun x =>
    Set.indicator_nonneg (fun y _ => (Real.exp_pos (-W y)).le) x
  refine
    { measurable := ?_
      nonneg := hnonneg
      upperSemicontinuous := ?_
      logConcave := ?_
      withDensity_eq := ?_ }
  · rw [← Set.piecewise_eq_indicator]
    exact hf.measurable_piecewise continuousOn_const hK.measurableSet
  · intro x a hxa
    by_cases hx : x ∈ K
    · have hfa : f x < a := by simpa only [Set.indicator_of_mem hx] using hxa
      have ha : 0 < a := (Real.exp_pos (-W x)).trans hfa
      filter_upwards [eventually_nhdsWithin_iff.mp
          ((hf x hx).eventually (gt_mem_nhds hfa))] with
        y hy
      by_cases hyK : y ∈ K
      · simpa only [Set.indicator_of_mem hyK] using hy hyK
      · simpa only [Set.indicator_of_notMem hyK] using ha
    · have ha : 0 < a := by simpa only [Set.indicator_of_notMem hx] using hxa
      filter_upwards [hK.isOpen_compl.mem_nhds hx] with y hy
      simpa only [Set.indicator_of_notMem hy] using ha
  · intro x y t ht ht1
    by_cases hx : x ∈ K
    · by_cases hy : y ∈ K
      · have hz : t • x + (1 - t) • y ∈ K := hKc hx hy ht.le (by linarith) (by ring)
        simp only [Set.indicator_of_mem hx, Set.indicator_of_mem hy, Set.indicator_of_mem hz]
        simpa only [div_one] using
          rpow_mul_rpow_le_of_convexOn_of_mem hWc (by norm_num : (0 : ℝ) < 1) hx hy ht ht1
      · rw [Set.indicator_of_notMem hy, Real.zero_rpow (by linarith : 1 - t ≠ 0), mul_zero]
        exact hnonneg _
    · rw [Set.indicator_of_notMem hx, Real.zero_rpow ht.ne', zero_mul]
      exact hnonneg _
  · rw [hμ]
    congr 1
    funext x
    by_cases hx : x ∈ K <;> simp [hx]

theorem isBorellDensity_of_eq_restricted_exp
    (μ : ProbabilityMeasure E) {K : Set E} (hK : IsClosed K) (hKc : Convex ℝ K)
    {W : E → ℝ} (hW : Continuous W) (hWc : ConvexOn ℝ univ W)
    (hμ : (μ : Measure E) = (volume : Measure E).withDensity
      (K.indicator fun x => ENNReal.ofReal (Real.exp (-W x)))) :
    IsBorellDensity (μ : Measure E) volume (K.indicator fun x => Real.exp (-W x)) :=
  isBorellDensity_of_eq_restricted_exp_on μ hK hKc hW.continuousOn
    (hWc.subset (subset_univ K) hKc) hμ

/-- **Log-concavity of restricted exponential laws.** For closed convex `K` and `W` continuous and
convex on `K` (no condition off `K`), the law `μ = (1_K e^{-W}) dx` is log-concave. -/
theorem logConcave_of_eq_restricted_exp_on
    (μ : ProbabilityMeasure E) {K : Set E} (hK : IsClosed K) (hKc : Convex ℝ K)
    {W : E → ℝ} (hW : ContinuousOn W K) (hWc : ConvexOn ℝ K W)
    (hμ : (μ : Measure E) = (volume : Measure E).withDensity
      (K.indicator fun x => ENNReal.ofReal (Real.exp (-W x)))) :
    FunctionalInequalities.KLS.LogConcave μ :=
  IsBorellDensity.compactLogConcave (isBorellDensity_of_eq_restricted_exp_on μ hK hKc hW hWc hμ)

theorem logConcave_of_eq_restricted_exp
    (μ : ProbabilityMeasure E) {K : Set E} (hK : IsClosed K) (hKc : Convex ℝ K)
    {W : E → ℝ} (hW : Continuous W) (hWc : ConvexOn ℝ univ W)
    (hμ : (μ : Measure E) = (volume : Measure E).withDensity
      (K.indicator fun x => ENNReal.ofReal (Real.exp (-W x)))) :
    FunctionalInequalities.KLS.LogConcave μ :=
  logConcave_of_eq_restricted_exp_on μ hK hKc hW.continuousOn (hWc.subset (subset_univ K) hKc) hμ

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A function continuous on the closure of a convex set and convex on the set is convex on the
closure. -/
private theorem convexOn_closure_of_continuousOn {K : Set E} (hKc : Convex ℝ K) {W : E → ℝ}
    (hW : ContinuousOn W (closure K)) (hWc : ConvexOn ℝ K W) : ConvexOn ℝ (closure K) W := by
  refine ⟨hKc.closure, fun x hx y hy a b ha hb hab => ?_⟩
  let g : E × E → ℝ := fun p => a • W p.1 + b • W p.2 - W (a • p.1 + b • p.2)
  have hg : ContinuousOn g (closure K ×ˢ closure K) := by
    have h1 : ContinuousOn (fun p : E × E => W p.1) (closure K ×ˢ closure K) :=
      hW.comp continuousOn_fst fun p hp => hp.1
    have h2 : ContinuousOn (fun p : E × E => W p.2) (closure K ×ˢ closure K) :=
      hW.comp continuousOn_snd fun p hp => hp.2
    have h3 : ContinuousOn (fun p : E × E => W (a • p.1 + b • p.2)) (closure K ×ˢ closure K) :=
      hW.comp (by fun_prop) fun p hp => hKc.closure hp.1 hp.2 ha hb hab
    exact ((h1.const_smul a).add (h2.const_smul b)).sub h3
  have hxy : (x, y) ∈ closure (K ×ˢ K) := by rw [closure_prod_eq]; exact ⟨hx, hy⟩
  have hmem : g (x, y) ∈ closure (Ici (0 : ℝ)) :=
    ((hg (x, y) ⟨hx, hy⟩).mono (prod_mono subset_closure subset_closure)).mem_closure hxy
      fun p hp => sub_nonneg.mpr (hWc.2 hp.1 hp.2 ha hb hab)
  rw [closure_Ici] at hmem
  exact sub_nonneg.mp hmem

/--
**Log-concavity of `1_K e^{-W} dx` on a convex set.** For convex `K` (for instance a bounded open
convex body) and `W` continuous on `closure K` and convex on `K`, the law `μ = (1_K e^{-W}) dx` is
log-concave: the frontier of `K` is Lebesgue-null, so `μ = (1_{closure K} e^{-W}) dx`, and `W` is
convex on `closure K` by continuity. -/
theorem logConcave_of_eq_restricted_exp_on_closure (μ : ProbabilityMeasure E) {K : Set E}
    (hKc : Convex ℝ K) {W : E → ℝ} (hW : ContinuousOn W (closure K)) (hWc : ConvexOn ℝ K W)
    (hμ :
      (μ : Measure E) =
        (volume : Measure E).withDensity
          (K.indicator fun x => ENNReal.ofReal (Real.exp (-W x)))) :
    FunctionalInequalities.KLS.LogConcave μ := by
  refine
    logConcave_of_eq_restricted_exp_on μ isClosed_closure hKc.closure hW
      (convexOn_closure_of_continuousOn hKc hW hWc) ?_
  rw [hμ]
  exact
    withDensity_congr_ae
      (indicator_ae_eq_of_ae_eq_set
        (closure_ae_eq_of_null_frontier (hKc.addHaar_frontier volume)).symm)

theorem logConcave_of_eq_regularClass (μ : ProbabilityMeasure E) {K : Set E} (hK : IsClosed K)
    (hKc : Convex ℝ K) {W : E → ℝ} (hW : Continuous W) {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
    (hμ :
      (μ : Measure E) =
        (volume : Measure E).withDensity
          (K.indicator fun x => ENNReal.ofReal (Real.exp (-W x)))) :
    FunctionalInequalities.KLS.LogConcave μ := by
  have hWc : ConvexOn ℝ univ W := by
    have hn' : ConvexOn ℝ univ (fun y : E => ‖y‖ ^ 2) :=
      convexOn_univ_norm.pow (fun _ _ => norm_nonneg _) 2
    have hq := hn'.smul (show 0 ≤ κ / 2 by positivity)
    have he : (fun y => W y - κ / 2 * ‖y‖ ^ 2) + (fun y => (κ / 2) • ‖y‖ ^ 2) = W := by
      funext y
      simp only [Pi.add_apply, smul_eq_mul, sub_add_cancel]
    rw [← he]
    exact hstrong.add hq
  exact logConcave_of_eq_restricted_exp μ hK hKc hW hWc hμ

end FunctionalInequalities.KLS.LogConcave

end
