/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.CompactReduction
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.BallConditioning
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.IsotropicReduction
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.RegularApproximation
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Density.BorellRepresentation.Moments
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Density.Tilted
public import LeanPool.KLS.FunctionalInequalities.Probability.Conditioning
public import LeanPool.KLS.FunctionalInequalities.Probability.Moments
public import Mathlib.Analysis.Convex.Measure

/-!
# Letwin's regular approximation (Lemma A.1)

Letwin arXiv:2607.24164v1, Lemma A.1 (PDF p. 16): every isotropic log-concave law `μ` is
approximated by isotropic laws
`e^{-V} 1_K dx`, `K` bounded open convex and `V` smooth convex on a neighbourhood of `closure K`,
with convergent
expectations of polynomials of degree at most four.

* `exists_regularClass_seq_tendsto_of_compact`: compactly supported isotropic log-concave laws are
  weak and
  degree-`≤ 4` moment limits of isotropic laws `1_K e^{-W} dx` (`K` compact convex with nonempty
  interior inside one
  fixed ball, `W` smooth and uniformly convex), by Gaussian smoothing, fixed-ball conditioning and
  whitening;
  `exists_regularClass_seq_of_compact` keeps the moment statement.
* `exists_regular_approximation`: Lemma A.1 in sequential form for every isotropic log-concave law.
  It composes the
  compact approximation `Suspension.exists_compact_moment_approximation` with the compact regular
  approximation by a
  diagonal choice over the finitely many coordinate monomials of degree `≤ 4`, and passes from the
  compact body to its
  interior (null frontier).
* `exists_regular_approximation_eps`: the `ε`-form for all coordinate monomials of degree `≤ 4`.

Convergence is stated for mixed linear moments `∫ ∏ᵢ ⟪vᵢ, x⟫`, which span the polynomials of degree
`≤ 4`; finite sums
of them are polynomial observables. No multivariate-polynomial (`MvPolynomial`) interface is stated.
Every approximant
is isotropic and log-concave with the exact density `volume.withDensity (K.indicator (exp ∘ -V))`.
This module does not
import the Letwin endpoints; `Suspension.letwinCompactBound_of_regularClass` consumes it.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set Filter Topology
open scoped RealInnerProductSpace ENNReal

namespace FunctionalInequalities.KLS.LogConcave
open MeasureTheory ProbabilityTheory Filter Topology Metric
open FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff

/-- Diagonal selection for finitely many real sequences of sequences. -/
private theorem exists_diagonal {ι : Type*} [Finite ι] (a : ℕ → ℕ → ι → ℝ) (b : ℕ → ι → ℝ)
    (c : ι → ℝ) (ha : ∀ k i, Tendsto (fun j => a k j i) atTop (𝓝 (b k i)))
    (hb : ∀ i, Tendsto (fun k => b k i) atTop (𝓝 (c i))) :
    ∃ J : ℕ → ℕ, ∀ i, Tendsto (fun k => a k (J k) i) atTop (𝓝 (c i)) := by
  have hev (k : ℕ) : ∀ᶠ j in atTop, ∀ i, |a k j i - b k i| < 1 / ((k : ℝ) + 1) := by
    refine eventually_all.2 fun i => ?_
    have h := (ha k i).sub_const (b k i)
    rw [sub_self] at h
    have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    have h0 : |(0 : ℝ)| < 1 / ((k : ℝ) + 1) := by rw [abs_zero]; exact hpos
    exact (h.abs).eventually (gt_mem_nhds h0)
  choose J hJ using fun k => (hev k).exists
  refine ⟨J, fun i => ?_⟩
  have hd : Tendsto (fun k => a k (J k) i - b k i) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun k => (hJ k i).le) ?_
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  simpa using hd.add (hb i)

/--
A convex body and its interior carry the same `withDensity` measure for an additive Haar measure:
the indicators differ only on the frontier, which is null. -/
private theorem withDensity_indicator_interior {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {K : Set E} (hK : Convex ℝ K) (g : E → ℝ≥0∞) :
    μ.withDensity ((interior K).indicator g) = μ.withDensity (K.indicator g) := by
  refine withDensity_congr_ae ?_
  have hnull : ∀ᵐ x ∂μ, x ∉ frontier K :=
    measure_eq_zero_iff_ae_notMem.1 (hK.addHaar_frontier μ)
  filter_upwards [hnull] with x hx
  by_cases hi : x ∈ interior K
  · simp [hi, interior_subset hi]
  · have hc : x ∉ closure K := fun hc => hx ⟨hc, hi⟩
    have hk : x ∉ K := fun hk => hc (subset_closure hk)
    simp [hi, hk]

/--
Coordinate monomials are integrable for every log-concave law (positive exponential moment). -/
private theorem integrable_coord_of_logConcave {n : ℕ}
    (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))) (hLC : KLS.LogConcave ν) {d : ℕ}
    (c : Fin d → Fin n) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) => ∏ i, x (c i))
      (ν : Measure (EuclideanSpace ℝ (Fin n))) := by
  obtain ⟨r, hr, hexp⟩ := ((KLS.LogConcave.borel_iff ν).1 hLC).exists_integrable_exp_norm
  have h :=
    FunctionalInequalities.Probability.integrable_prod_inner_of_exp
      (ν : Measure (EuclideanSpace ℝ (Fin n))) hr hexp d
      (fun i => EuclideanSpace.single (c i) (1 : ℝ))
  refine h.congr (ae_of_all _ fun x => ?_)
  simp [EuclideanSpace.inner_single_right]

/--
**Compact regular approximation with weak convergence and uniform support.** A compactly supported
isotropic
log-concave law `μ` is the weak limit of isotropic laws `ζ j = 1_{K j} e^{-W j} dx`, with `K j`
compact convex with
nonempty interior and `W j` smooth and uniformly convex, such that all mixed linear moments of
degree `≤ 4` converge
and the bodies `K j` lie in one fixed ball. The terms are whitened Gaussian-smoothed conditionings
on a fixed ball,
taken beyond the index where whitening is exact; `K j` is the affine image of that ball under maps
converging to the
identity, which gives the uniform bound. -/
theorem exists_regularClass_seq_tendsto_of_compact {n : ℕ}
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))) (hLC : KLS.LogConcave μ)
    (hiso : KLS.Isotropic μ)
    (hcompact : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support) :
    ∃ (ζ : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin n))) (K :
      ℕ → Set (EuclideanSpace ℝ (Fin n))) (W : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (κ : ℕ → ℝ),
      (∀ j,
          KLS.Isotropic (ζ j) ∧
            0 < κ j ∧
              IsCompact (K j) ∧
                Convex ℝ (K j) ∧
                  (interior (K j)).Nonempty ∧
                    ContDiff ℝ ∞ (W j) ∧
                      ConvexOn ℝ univ (fun y => W j y - (κ j / 2) * ‖y‖ ^ 2) ∧
                        (ζ j : Measure (EuclideanSpace ℝ (Fin n))) =
                          (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
                            ((K j).indicator fun p => ENNReal.ofReal (Real.exp (-W j p)))) ∧
        (∀ d ≤ 4,
            ∀ v : Fin d → EuclideanSpace ℝ (Fin n),
              Tendsto (fun j => ∫ x, ∏ i, ⟪v i, x⟫ ∂(ζ j : Measure (EuclideanSpace ℝ (Fin n))))
                atTop (𝓝 (∫ x, ∏ i, ⟪v i, x⟫ ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))))) ∧
          Tendsto ζ atTop (𝓝 μ) ∧ ∃ R : ℝ, ∀ j, ∀ y ∈ K j, ‖y‖ ≤ R := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  obtain ⟨r, hr⟩ := Bornology.IsBounded.subset_closedBall hcompact.isBounded (0 : E)
  let r₀ : ℝ := max r 0
  let R : ℝ := r₀ + 1
  have hr₀ : (μ : Measure E) (closedBall (0 : E) r₀)ᶜ = 0 := by
    have hsub : (μ : Measure E).support ⊆ closedBall (0 : E) r₀ :=
      hr.trans (closedBall_subset_closedBall (le_max_left r 0))
    exact measure_mono_null (compl_subset_compl.mpr hsub) Measure.measure_compl_support
  have hR : 0 < R := by
    have : 0 ≤ r₀ := le_max_right r 0
    dsimp [R]
    linarith
  have hrR : r₀ < R := by
    dsimp [R]
    linarith
  have hμR : (μ : Measure E) (closedBall (0 : E) R)ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.mpr (closedBall_subset_closedBall hrR.le)) hr₀
  obtain ⟨ρ, hρ⟩ := KLS.LogConcave.exists_isBorellDensity_of_isotropic hLC hiso
  obtain ⟨k, _hk, _hkpos, _hkδ, hkV, _hkupper, hweak, _hmean, _hsecond, _hcov⟩ :=
    KLS.LogConcave.GaussianSmoothing.exists_regularSeq_limits hρ hiso.memLp_two
  let ν : ℕ → ProbabilityMeasure E := fun j =>
    KLS.LogConcave.GaussianSmoothing.regularSeq hρ j (k j)
  have hνV (j : ℕ) :
    KLS.RegularPotential
      (KLS.LogConcave.GaussianSmoothing.quadraticPotential ρ ((j : ℝ) + 1)
        (KLS.LogConcave.GaussianSmoothing.tiltRate (k j)))
      (KLS.LogConcave.GaussianSmoothing.tiltRate (k j))
      (2 * ((j : ℝ) + 1) + KLS.LogConcave.GaussianSmoothing.tiltRate (k j)) :=
    hkV j
  have hνeq (j : ℕ) : ν j = (hνV j).law := rfl
  have hweak' : Tendsto ν atTop (𝓝 μ) := hweak
  have hνball (j : ℕ) : 0 < (ν j : Measure E) (closedBall (0 : E) R) := by
    rw [hνeq j]
    have hv : 0 < (volume : Measure E) (closedBall (0 : E) R) :=
      Measure.measure_pos_of_mem_nhds volume (closedBall_mem_nhds (0 : E) hR)
    have hac : (volume : Measure E) ≪ ((hνV j).law : Measure E) :=
      MeasureTheory.absolutelyContinuous_tilted (hνV j).integrable_exp_neg
    by_contra hz
    have hz' : ((hνV j).law : Measure E) (closedBall (0 : E) R) = 0 :=
      nonpos_iff_eq_zero.mp (le_of_not_gt hz)
    exact (ne_of_gt hv) (hac hz')
  let lam : ℕ → ProbabilityMeasure E := fun j =>
    ⟨ProbabilityTheory.cond (ν j : Measure E) (closedBall (0 : E) R),
      ProbabilityTheory.cond_isProbabilityMeasure (ne_of_gt (hνball j))⟩
  have hlam (j : ℕ) :
    (lam j : Measure E) = ProbabilityTheory.cond (ν j : Measure E) (closedBall (0 : E) R) := rfl
  have hlam_supp (j : ℕ) : (lam j : Measure E) (closedBall (0 : E) R)ᶜ = 0 := by
    rw [hlam j, ProbabilityTheory.cond_apply measurableSet_closedBall]
    simp
  have hlam_mom :
    ∀ d ≤ 4,
      ∀ v : Fin d → E,
        Tendsto (fun j => ∫ x, ∏ i, ⟪v i, x⟫ ∂(lam j : Measure E)) atTop
          (𝓝 (∫ x, ∏ i, ⟪v i, x⟫ ∂(μ : Measure E))) := by
    intro d _hd v
    exact
      FunctionalInequalities.KLS.tendsto_integral_cond_closedBall hweak' hrR hr₀ (by fun_prop)
  obtain ⟨L, c, hL, hc, hwhite, hwhmom⟩ :=
    FunctionalInequalities.KLS.exists_whitening_tendsto_one_tendsto_moments hiso hlam_supp hμR
      hlam_mom
  let η : ℕ → ProbabilityMeasure E := fun j =>
    MeasureTheory.ProbabilityMeasure.map (lam j) (fun x : E => L j (x - c j))
  have hηsupp (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ (η j : Measure E) (closedBall (0 : E) C)ᶜ = 0 := by
    let f : E → E := fun x => L j (x - c j)
    have hf : Continuous f := by fun_prop
    obtain ⟨C₀, hC₀⟩ :=
      (isCompact_closedBall (0 : E) R).exists_bound_of_continuousOn hf.continuousOn
    let C : ℝ := max C₀ 0
    refine ⟨C, le_max_right _ _, ?_⟩
    change (Measure.map f (lam j : Measure E)) (closedBall (0 : E) C)ᶜ = 0
    rw [Measure.map_apply hf.measurable measurableSet_closedBall.compl]
    refine measure_mono_null (t := (closedBall (0 : E) R)ᶜ) ?_ (hlam_supp j)
    intro x hx hxR
    apply hx
    rw [mem_closedBall, dist_zero_right]
    exact (hC₀ x hxR).trans (le_max_left _ _)
  have hηmem2 (j : ℕ) : MemLp id 2 (η j : Measure E) := by
    obtain ⟨C, _hC, hs⟩ := hηsupp j
    refine MemLp.of_bound continuous_id.aestronglyMeasurable C ?_
    filter_upwards [ae_iff.mpr hs] with x hx
    simpa only [id_eq, dist_zero_right] using mem_closedBall.mp hx
  have hηintegral {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (j : ℕ) {f : E → F}
    (hf : Continuous f) :
    ∫ y, f y ∂(η j : Measure E) = ∫ x, f (L j (x - c j)) ∂(lam j : Measure E) := by
    let g : E → E := fun x => L j (x - c j)
    have hg : Continuous g := by fun_prop
    change (∫ y, f y ∂Measure.map g (lam j : Measure E)) = ∫ x, f (g x) ∂(lam j : Measure E)
    exact MeasureTheory.integral_map hg.aemeasurable hf.aestronglyMeasurable
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.1 hwhite
  have hηiso (j : ℕ) (hj : j₀ ≤ j) : KLS.Isotropic (η j) := by
    have hwj := hj₀ j hj
    apply KLS.isotropic_of_moments (η j) (hηmem2 j)
    · exact (hηintegral j (f := fun x : E => x) continuous_id).trans hwj.1
    · intro u v
      exact (hηintegral j (f := fun x : E => ⟪u, x⟫ * ⟪v, x⟫) (by fun_prop)).trans (hwj.2 u v)
  have hηmom :
    ∀ d ≤ 4,
      ∀ v : Fin d → E,
        Tendsto (fun j => ∫ x, ∏ i, ⟪v i, x⟫ ∂(η j : Measure E)) atTop
          (𝓝 (∫ x, ∏ i, ⟪v i, x⟫ ∂(μ : Measure E))) := by
    intro d hd v
    apply (hwhmom d hd v).congr'
    filter_upwards [] with j
    exact (hηintegral j (f := fun x : E => ∏ i, ⟪v i, x⟫) (by fun_prop)).symm
  have hηweak : Tendsto η atTop (𝓝 μ) := by
    refine MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2 fun f => ?_
    have hp :=
      FunctionalInequalities.KLS.tendsto_integral_comp_affine_sub hlam_supp hL hc f.continuous
    have hr :=
      FunctionalInequalities.KLS.tendsto_integral_cond_closedBall hweak' hrR hr₀ f.continuous
    have hs := hp.add hr
    rw [zero_add] at hs
    refine hs.congr fun j => ?_
    rw [hηintegral j f.continuous]
    exact sub_add_cancel _ _
  have hreg (j : ℕ) :=
    FunctionalInequalities.KLS.exists_regularClass_eq_image_of_cond_closedBall_map
      (hνV (j + j₀)) hR (L (j + j₀)) (c (j + j₀))
  choose K W κ hKeq hκ hK hKconv hKint hW hWconv hmap using hreg
  obtain ⟨B, hB⟩ :=
    ((hL.norm.mul (tendsto_const_nhds.add hc.norm)).comp
        (tendsto_add_atTop_nat j₀)).bddAbove_range
  refine
    ⟨fun j => η (j + j₀), K, W, κ, fun j =>
      ⟨hηiso (j + j₀) (by omega), hκ j, hK j, hKconv j, hKint j, hW j, hWconv j, ?_⟩,
      fun d hd v => (hηmom d hd v).comp (tendsto_add_atTop_nat j₀),
      hηweak.comp (tendsto_add_atTop_nat j₀), B, fun j y hy => ?_⟩
  · change
      Measure.map (fun x : E => L (j + j₀) (x - c (j + j₀)))
          (ProbabilityTheory.cond (ν (j + j₀) : Measure E) (closedBall (0 : E) R)) =
        (volume : Measure E).withDensity
          ((K j).indicator fun p => ENNReal.ofReal (Real.exp (-W j p)))
    rw [hνeq (j + j₀)]
    exact hmap j
  · rw [hKeq j] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [mem_closedBall, dist_zero_right] at hx
    calc
      ‖L (j + j₀) (x - c (j + j₀))‖ ≤ ‖(L (j + j₀) : E →L[ℝ] E)‖ * ‖x - c (j + j₀)‖ :=
        (L (j + j₀) : E →L[ℝ] E).le_opNorm _
      _ ≤ ‖(L (j + j₀) : E →L[ℝ] E)‖ * (R + ‖c (j + j₀)‖) :=
        mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (by linarith)) (norm_nonneg _)
      _ ≤ B := hB ⟨j, rfl⟩

/--
**Compact regular approximation.** A compactly supported isotropic log-concave law is the limit, in
all mixed
linear moments of degree `≤ 4`, of isotropic laws `1_K e^{-W} dx` with `K` compact convex with
nonempty interior and `W`
smooth and uniformly convex. Every term is isotropic: the whitened Gaussian-smoothed ball
conditionings are taken beyond
the index where whitening is exact. Log-concavity of each term follows from its density
(`logConcave_of_eq_regularClass`).
Weak convergence and a uniform bound on the bodies are added in
`exists_regularClass_seq_tendsto_of_compact`. -/
theorem exists_regularClass_seq_of_compact {n : ℕ}
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))) (hLC : KLS.LogConcave μ)
    (hiso : KLS.Isotropic μ)
    (hcompact : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support) :
    ∃ ζ : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin n)),
      (∀ j,
          KLS.Isotropic (ζ j) ∧
            ∃ (K : Set (EuclideanSpace ℝ (Fin n))) (W : EuclideanSpace ℝ (Fin n) → ℝ) (κ : ℝ),
              0 < κ ∧
                IsCompact K ∧
                  Convex ℝ K ∧
                    (interior K).Nonempty ∧
                      ContDiff ℝ ∞ W ∧
                        ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2) ∧
                          (ζ j : Measure (EuclideanSpace ℝ (Fin n))) =
                            (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
                              (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p)))) ∧
        ∀ d ≤ 4,
          ∀ v : Fin d → EuclideanSpace ℝ (Fin n),
            Tendsto (fun j => ∫ x, ∏ i, ⟪v i, x⟫ ∂(ζ j : Measure (EuclideanSpace ℝ (Fin n))))
              atTop (𝓝 (∫ x, ∏ i, ⟪v i, x⟫ ∂(μ : Measure (EuclideanSpace ℝ (Fin n))))) := by
  obtain ⟨ζ, K, W, κ, hζ, hmom, -, -⟩ :=
    exists_regularClass_seq_tendsto_of_compact μ hLC hiso hcompact
  exact ⟨ζ, fun j => ⟨(hζ j).1, K j, W j, κ j, (hζ j).2⟩, hmom⟩

/--
**Letwin arXiv:2607.24164v1, Lemma A.1 (regular approximation), sequential form.** Every isotropic
log-concave
probability law `μ` on `ℝⁿ` is the limit, in every mixed linear moment `∫ ∏_{i<d} ⟪v i, x⟫` of
degree `d ≤ 4` (hence in
every finite sum of such moments, i.e. every polynomial observable of degree `≤ 4` written in this
form), of isotropic
log-concave laws `η j = e^{-V j} 1_{K j} dx` with the exact density normalization, `K j` bounded
open convex nonempty and
`V j` smooth and convex on an open neighbourhood of `closure (K j)`. Moreover `V j` is smooth and
uniformly convex on the
whole space. The source states `n > 0`; the proof does not use it. -/
theorem exists_regular_approximation {n : ℕ} (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hLC : KLS.LogConcave μ) (hiso : KLS.Isotropic μ) :
    ∃ (η : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin n))) (K :
      ℕ → Set (EuclideanSpace ℝ (Fin n))) (V : ℕ → EuclideanSpace ℝ (Fin n) → ℝ),
      (∀ j,
          KLS.LogConcave (η j) ∧
            KLS.Isotropic (η j) ∧
              IsOpen (K j) ∧
                Bornology.IsBounded (K j) ∧
                  Convex ℝ (K j) ∧
                    (K j).Nonempty ∧
                      (∃ U : Set (EuclideanSpace ℝ (Fin n)),
                          IsOpen U ∧
                            closure (K j) ⊆ U ∧ ContDiffOn ℝ ∞ (V j) U ∧ ConvexOn ℝ U (V j)) ∧
                        (∃ κ : ℝ,
                            0 < κ ∧
                              ContDiff ℝ ∞ (V j) ∧
                                ConvexOn ℝ univ (fun y => V j y - (κ / 2) * ‖y‖ ^ 2)) ∧
                          (η j : Measure (EuclideanSpace ℝ (Fin n))) =
                            (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
                              ((K j).indicator fun x => ENNReal.ofReal (Real.exp (-V j x)))) ∧
        ∀ d ≤ 4,
          ∀ v : Fin d → EuclideanSpace ℝ (Fin n),
            Tendsto (fun j => ∫ x, ∏ i, ⟪v i, x⟫ ∂(η j : Measure (EuclideanSpace ℝ (Fin n))))
              atTop (𝓝 (∫ x, ∏ i, ⟪v i, x⟫ ∂(μ : Measure (EuclideanSpace ℝ (Fin n))))) := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  obtain ⟨ξ, hξ, hξmom⟩ := Suspension.exists_compact_moment_approximation hLC hiso
  have hreg (k : ℕ) := exists_regularClass_seq_of_compact (ξ k) (hξ k).1 (hξ k).2.1 (hξ k).2.2
  choose ζ hζ hζmom using hreg
  choose hζiso K W κ hκ hK hKc hKint hW hWc hζeq using hζ
  have hζLC (k j : ℕ) : KLS.LogConcave (ζ k j) :=
    logConcave_of_eq_regularClass (ζ k j) (hK k j).isClosed (hKc k j) (hW k j).continuous
      (hκ k j) (hWc k j)
      (hζeq k j)
  -- finite family of coordinate monomials of degree `≤ 4`

  let mom : (Σ d : Fin 5, Fin d → Fin n) → Measure E → ℝ := fun m ρ => ∫ x, ∏ i, x (m.2 i) ∂ρ
  have hcoord_of (ρ : ℕ → Measure E) (σ : Measure E)
    (h :
      ∀ d ≤ 4,
        ∀ v : Fin d → E,
          Tendsto (fun j => ∫ x, ∏ i, ⟪v i, x⟫ ∂(ρ j)) atTop (𝓝 (∫ x, ∏ i, ⟪v i, x⟫ ∂σ)))
    (m : Σ d : Fin 5, Fin d → Fin n) : Tendsto (fun j => mom m (ρ j)) atTop (𝓝 (mom m σ)) := by
    have := h m.1 (Nat.lt_succ_iff.1 m.1.2) (fun i => EuclideanSpace.single (m.2 i) (1 : ℝ))
    simpa only [mom, ← Probability.prod_coord_eq_prod_inner_single] using this
  obtain ⟨J, hJ⟩ :=
    exists_diagonal (fun k j m => mom m (ζ k j : Measure E))
      (fun k m => mom m (ξ k : Measure E)) (fun m => mom m (μ : Measure E))
      (fun k m => hcoord_of _ _ (hζmom k) m) (fun m => hcoord_of _ _ hξmom m)
  refine
    ⟨fun k => ζ k (J k), fun k => interior (K k (J k)), fun k => W k (J k), fun k => ?_, ?_⟩
  · have hWconv : ConvexOn ℝ univ (W k (J k)) := by
      have hq : ConvexOn ℝ univ (fun y : E => (κ k (J k) / 2) * ‖y‖ ^ 2) :=
        (convexOn_univ_norm.pow (fun _ _ => norm_nonneg _) 2).smul
          (show 0 ≤ κ k (J k) / 2 from (div_pos (hκ k (J k)) two_pos).le)
      have he :
        (fun y => W k (J k) y - (κ k (J k) / 2) * ‖y‖ ^ 2) +
            (fun y : E => (κ k (J k) / 2) * ‖y‖ ^ 2) =
          W k (J k) := by
        funext y; simp
      rw [← he]
      exact (hWc k (J k)).add hq
    refine
      ⟨hζLC k (J k), hζiso k (J k), isOpen_interior,
        (hK k (J k)).isBounded.subset interior_subset, (hKc k (J k)).interior, hKint k (J k),
        ⟨univ, isOpen_univ, subset_univ _, (hW k (J k)).contDiffOn, hWconv⟩,
        ⟨κ k (J k), hκ k (J k), hW k (J k), hWc k (J k)⟩, ?_⟩
    rw [withDensity_indicator_interior volume (hKc k (J k))]
    exact hζeq k (J k)
  · intro d hd v
    refine
      Probability.tendsto_integral_prod_inner_of_coord _ _
        (fun k c => integrable_coord_of_logConcave _ (hζLC k (J k)) c)
        (fun c => integrable_coord_of_logConcave _ hLC c) (fun c => ?_) v
    exact hJ ⟨⟨d, Nat.lt_succ_iff.2 hd⟩, c⟩

/--
**Lemma A.1, ε-form** (the paper's formulation, for the finite family of coordinate monomials of
degree `≤ 4`,
which spans the polynomials of degree `≤ 4`): for every `ε > 0` one regular law has all these
moments within `ε`. -/
theorem exists_regular_approximation_eps {n : ℕ}
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))) (hLC : KLS.LogConcave μ)
    (hiso : KLS.Isotropic μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (η : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))) (K : Set (EuclideanSpace ℝ (Fin n)))
      (V : EuclideanSpace ℝ (Fin n) → ℝ),
      KLS.LogConcave η ∧
        KLS.Isotropic η ∧
          IsOpen K ∧
            Bornology.IsBounded K ∧
              Convex ℝ K ∧
                K.Nonempty ∧
                  (∃ U : Set (EuclideanSpace ℝ (Fin n)),
                      IsOpen U ∧ closure K ⊆ U ∧ ContDiffOn ℝ ∞ V U ∧ ConvexOn ℝ U V) ∧
                    (η : Measure (EuclideanSpace ℝ (Fin n))) =
                        (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
                          (K.indicator fun x => ENNReal.ofReal (Real.exp (-V x))) ∧
                      ∀ d ≤ 4,
                        ∀ c : Fin d → Fin n,
                          |∫ x, ∏ i, x (c i) ∂(η : Measure (EuclideanSpace ℝ (Fin n))) -
                                ∫ x, ∏ i, x (c i) ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))| <
                            ε := by
  obtain ⟨η, K, V, hη, hmom⟩ := exists_regular_approximation μ hLC hiso
  have hev :
    ∀ᶠ j in atTop,
      ∀ m : (Σ d : Fin 5, Fin d → Fin n),
        |∫ x, ∏ i, x (m.2 i) ∂(η j : Measure (EuclideanSpace ℝ (Fin n))) -
              ∫ x, ∏ i, x (m.2 i) ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))| <
          ε := by
    refine eventually_all.2 fun m => ?_
    have h :=
      hmom m.1 (Nat.lt_succ_iff.1 m.1.2) (fun i => EuclideanSpace.single (m.2 i) (1 : ℝ))
    simp only [← Probability.prod_coord_eq_prod_inner_single] at h
    have h0 := (h.sub_const (∫ x, ∏ i, x (m.2 i) ∂(μ : Measure (EuclideanSpace ℝ (Fin n))))).abs
    rw [sub_self, abs_zero] at h0
    exact h0.eventually (gt_mem_nhds hε)
  obtain ⟨j, hj⟩ := hev.exists
  obtain ⟨hLCj, hisoj, hopen, hbdd, hconv, hne, hU, -, heq⟩ := hη j
  exact
    ⟨η j, K j, V j, hLCj, hisoj, hopen, hbdd, hconv, hne, hU, heq, fun d hd c =>
      hj ⟨⟨d, Nat.lt_succ_iff.2 hd⟩, c⟩⟩

end FunctionalInequalities.KLS.LogConcave
