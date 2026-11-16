/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Probability.Support.Convex
public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.PointwiseCompactness
public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.RadialExtension
public import LeanPool.KLS.FunctionalInequalities.Probability.MomentMeasure.ConjugateMass
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Compactness of convex potentials (CEK Lemma 17)

Cordero-Erausquin–Klartag, *Moment measures* (arXiv:1304.0630v1), Lemma 17, for a finite Borel
measure `μ` (not
normalized) on a finite-dimensional real inner product space whose support hull has `0` in its
interior, and nonnegative
extended-real potentials `φ ℓ` with convex real epigraphs, `φ ℓ 0 = 0`, a.e.-measurable `toENNReal`
and uniformly bounded
integrals. Dimension zero is included.

* (56a), `Probability.exists_subseq_lintegral_le_liminf_of_convex_epigraph`: a subsequence and a
  nonnegative convex limit,
  finite and attained pointwise on the interior of the support hull, radially closed, `⊤` off its
  closure and Borel,
  whose integral is at most the liminf of the integrals. Pointwise bounds come from Lemma 16
  (`Probability/Support/Convex.lean`), the subsequence from
  `Analysis/Convex/PointwiseCompactness.lean`, the limit from
  `Analysis/Convex/RadialExtension.lean`; Fatou is applied to the scaled potentials and then along
  the radial limit.
* Full (56), `MomentMeasure.exists_subseq_integral_bounds_of_convex_epigraph`: the same subsequence
  and limit also satisfy
  (56b) for every additive Haar `dx`, `limsup ∫ exp(-(φ (s j))*) dx ≤ ∫ exp(-ψ*) dx`, with `ψ`
  integrable against `μ` and
  finite conjugate mass derived (`MomentMeasure/ConjugateMass.lean`), not assumed. Zero conjugate
  mass is allowed.

Not provided: attainment in Proposition 12, essential continuity, the Euler–Lagrange identification,
existence or
uniqueness of moment potentials (Theorem 2).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace FunctionalInequalities.Probability

private theorem aemeasurable_toENNReal_comp_of_continuousOn_toReal {X E : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [TopologicalSpace E]
    {μ : Measure X} {K : Set E} (hK : IsOpen K) {g : X → E} (hg : Continuous g) {φ : E → EReal}
    (hnn : ∀ y ∈ K, 0 ≤ φ y) (hfin : ∀ y ∈ K, φ y ≠ ⊤)
    (hcont : ContinuousOn (fun y => (φ y).toReal) K) (hae : ∀ᵐ x ∂μ, g x ∈ K) :
    AEMeasurable (fun x => (φ (g x)).toENNReal) μ := by
  let S : Set X := g ⁻¹' K
  have hS : IsOpen S := hK.preimage hg
  have hcore : ContinuousOn (fun x => ENNReal.ofReal ((φ (g x)).toReal)) S :=
    ENNReal.continuous_ofReal.comp_continuousOn
      (hcont.comp hg.continuousOn (by intro x hx; exact hx))
  have heq :
    Set.EqOn (fun x => (φ (g x)).toENNReal) (fun x => ENNReal.ofReal ((φ (g x)).toReal)) S := by
    intro x hx
    change (φ (g x)).toENNReal = ENNReal.ofReal ((φ (g x)).toReal)
    have hc : ((φ (g x)).toReal : EReal) = φ (g x) :=
      EReal.coe_toReal (hfin _ hx) (ne_of_gt (EReal.bot_lt_zero.trans_le (hnn _ hx)))
    rw [← hc, EReal.real_coe_toENNReal, EReal.toReal_coe]
  have hcontinuous : ContinuousOn (fun x => (φ (g x)).toENNReal) S := hcore.congr heq
  have hm : AEMeasurable (fun x => (φ (g x)).toENNReal) (μ.restrict S) :=
    hcontinuous.aemeasurable hS.measurableSet
  have hrestrict : μ.restrict S = μ := Measure.restrict_eq_self_of_ae_mem hae
  rwa [hrestrict] at hm

private theorem le_of_smul_of_convex_epigraph {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {φ : E → EReal} (hnn : ∀ x, 0 ≤ φ x) (hφ0 : φ 0 = 0)
    (hconv : Convex ℝ {p : E × ℝ | φ p.1 ≤ (p.2 : EReal)}) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (x : E) : φ (t • x) ≤ φ x := by
  by_cases htop : φ x = ⊤
  · rw [htop]
    exact le_top
  have hbot : φ x ≠ ⊥ := ne_of_gt (EReal.bot_lt_zero.trans_le (hnn x))
  lift φ x to ℝ using ⟨htop, hbot⟩ with q hq
  have hq0 : 0 ≤ q := by
    apply EReal.coe_le_coe_iff.mp
    simpa only [hq, EReal.coe_zero] using hnn x
  have hx : (x, q) ∈ {p : E × ℝ | φ p.1 ≤ (p.2 : EReal)} := by
    change φ x ≤ (q : EReal)
    rw [hq]
  have hz : ((0 : E), (0 : ℝ)) ∈ {p : E × ℝ | φ p.1 ≤ (p.2 : EReal)} := by
    change φ 0 ≤ (0 : EReal)
    rw [hφ0]
  have hepi := hconv hx hz ht0 (sub_nonneg.mpr ht1) (by ring : t + (1 - t) = 1)
  have hle : φ (t • x) ≤ (t * q : ℝ) := by
    change φ (t • x + (1 - t) • 0) ≤ (t * q + (1 - t) * 0 : ℝ) at hepi
    simpa only [smul_zero, mul_zero, add_zero] using hepi
  exact
    hle.trans
      (EReal.coe_le_coe_iff.mpr
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right ht1 hq0))

private theorem ae_mem_closure_and_smul_mem_interior_convexHull_support {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (μ : Measure E) (h0 : (0 : E) ∈ interior (convexHull ℝ μ.support)) :
    (∀ᵐ x ∂μ, x ∈ closure (interior (convexHull ℝ μ.support))) ∧
      ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ᵐ x ∂μ, t • x ∈ interior (convexHull ℝ μ.support) := by
  let C := convexHull ℝ μ.support
  have hc : Convex ℝ C := convex_convexHull ℝ μ.support
  have hclosed : closure (interior C) = closure C :=
    hc.closure_interior_eq_closure_of_nonempty_interior ⟨0, h0⟩
  have hae : ∀ᵐ x ∂μ, x ∈ closure (interior C) := by
    filter_upwards [μ.support_mem_ae] with x hx
    rw [hclosed]
    exact subset_closure (subset_convexHull ℝ μ.support hx)
  refine ⟨hae, ?_⟩
  intro t ht0 ht1
  filter_upwards [hae] with x hx
  have hxC : x ∈ closure C := by simpa only [hclosed] using hx
  have hh :=
    hc.combo_interior_closure_mem_interior h0 hxC (sub_pos.mpr ht1) ht0
      (by ring : (1 - t) + t = 1)
  simpa only [smul_zero, zero_add] using hh

/--
**CEK Lemma 17, first half (56a).** For a finite measure whose support hull contains `0` in its
interior, nonnegative
convex extended-real functions vanishing at `0` with uniformly bounded lintegrals have a subsequence
and a nonnegative convex
limit (finite and attained pointwise on the interior of the support hull, radially closed, `⊤` off
its closure, Borel) whose
lintegral is at most the liminf of the lintegrals. -/
theorem exists_subseq_lintegral_le_liminf_of_convex_epigraph {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] (h0 : (0 : E) ∈ interior (convexHull ℝ μ.support))
    (φ : ℕ → E → EReal) (hnn : ∀ ℓ x, 0 ≤ φ ℓ x) (hφ0 : ∀ ℓ, φ ℓ 0 = 0)
    (hconv : ∀ ℓ, Convex ℝ {p : E × ℝ | φ ℓ p.1 ≤ (p.2 : EReal)})
    (hmeas : ∀ ℓ, AEMeasurable (fun x => (φ ℓ x).toENNReal) μ)
    (hbdd : (⨆ ℓ, ∫⁻ x, (φ ℓ x).toENNReal ∂μ) ≠ ⊤) :
    ∃ (s : ℕ → ℕ) (ψ : E → EReal),
      StrictMono s ∧
        (∀ x, 0 ≤ ψ x) ∧
          ψ 0 = 0 ∧
            Convex ℝ {p : E × ℝ | ψ p.1 ≤ (p.2 : EReal)} ∧
              Measurable (fun x => (ψ x).toENNReal) ∧
                (∀ x ∈ interior (convexHull ℝ μ.support),
                    ψ x ≠ ⊤ ∧ Filter.Tendsto (fun j => φ (s j) x) Filter.atTop (nhds (ψ x))) ∧
                  (∀ x,
                      Filter.Tendsto (fun t : ℝ => ψ (t • x)) (nhdsWithin 1 (Set.Iio 1))
                        (nhds (ψ x))) ∧
                    (∀ x ∉ closure (interior (convexHull ℝ μ.support)), ψ x = ⊤) ∧
                      ∫⁻ x, (ψ x).toENNReal ∂μ ≤
                        Filter.liminf (fun j => ∫⁻ x, (φ (s j) x).toENNReal ∂μ) Filter.atTop := by
  let K : Set E := interior (convexHull ℝ μ.support)
  have hK : IsOpen K := isOpen_interior
  have hKconv : Convex ℝ K := (convex_convexHull ℝ μ.support).interior
  have h0K : (0 : E) ∈ K := h0
  let B : ℝ≥0∞ := ⨆ ℓ, ∫⁻ x, (φ ℓ x).toENNReal ∂μ
  have hB : B ≠ ⊤ := hbdd
  have hint (ℓ : ℕ) : (∫⁻ x, (φ ℓ x).toENNReal ∂μ) ≠ ⊤ :=
    ne_of_lt ((le_iSup (fun j => ∫⁻ x, (φ j x).toENNReal ∂μ) ℓ).trans_lt (Ne.lt_top hB))
  have hbounds : ∀ x ∈ K, ∃ M : ℝ, ∀ ℓ, φ ℓ x ≤ (M : EReal) := by
    intro x hx
    obtain ⟨C, hC, hbound⟩ := exists_pos_le_mul_lintegral_toReal_of_convex_epigraph μ x hx
    refine ⟨C * B.toReal, ?_⟩
    intro ℓ
    have ht := hbound (φ ℓ) (hnn ℓ) (hconv ℓ) (hmeas ℓ) (hint ℓ)
    have hib : (∫⁻ y, (φ ℓ y).toENNReal ∂μ).toReal ≤ B.toReal :=
      ENNReal.toReal_mono hB (le_iSup (fun j => ∫⁻ y, (φ j y).toENNReal ∂μ) ℓ)
    exact ht.trans (EReal.coe_le_coe_iff.mpr (mul_le_mul_of_nonneg_left hib hC.le))
  have hfin : ∀ ℓ, ∀ x ∈ K, φ ℓ x ≠ ⊤ := by
    intro ℓ x hx
    obtain ⟨M, hM⟩ := hbounds x hx
    exact ne_of_lt ((hM ℓ).trans_lt (EReal.coe_lt_top M))
  have hcoe : ∀ ℓ, ∀ x ∈ K, ((φ ℓ x).toReal : EReal) = φ ℓ x := by
    intro ℓ x hx
    exact EReal.coe_toReal (hfin ℓ x hx) (ne_of_gt (EReal.bot_lt_zero.trans_le (hnn ℓ x)))
  have hrealconv : ∀ ℓ, ConvexOn ℝ K (fun x => (φ ℓ x).toReal) := by
    intro ℓ
    exact
      (real_convexOn_effective_domain (hnn ℓ) (hconv ℓ)).subset (fun x hx => hfin ℓ x hx) hKconv
  have hrealbdd : ∀ x ∈ K, BddAbove (Set.range fun ℓ => (φ ℓ x).toReal) := by
    intro x hx
    obtain ⟨M, hM⟩ := hbounds x hx
    refine ⟨M, ?_⟩
    rintro r ⟨ℓ, rfl⟩
    apply EReal.coe_le_coe_iff.mp
    rw [hcoe ℓ x hx]
    exact hM ℓ
  obtain ⟨s, g, hs, hgconv, hglim⟩ :=
    FunctionalInequalities.Analysis.exists_subseq_tendsto_of_convexOn_of_bddAbove hK
      (fun ℓ x => (φ ℓ x).toReal) hrealconv (fun ℓ x hx => EReal.toReal_nonneg (hnn ℓ x))
      hrealbdd
  have hgnn : ∀ x ∈ K, 0 ≤ g x := by
    intro x hx
    exact
      ge_of_tendsto (hglim x hx)
        (Filter.Eventually.of_forall fun j => EReal.toReal_nonneg (hnn (s j) x))
  have hg0 : g 0 = 0 := by
    have hz : Filter.Tendsto (fun j => (φ (s j) 0).toReal) Filter.atTop (nhds (0 : ℝ)) := by
      simpa only [hφ0, EReal.toReal_zero] using
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds 0))
    exact tendsto_nhds_unique (hglim 0 h0K) hz
  obtain ⟨ψ, hψnn, hψ0, hψconv, hψmeas, hψeq, hψoff, hψrad⟩ :=
    FunctionalInequalities.Analysis.exists_radial_extension_of_convexOn hK h0K hgconv hgnn hg0
  have hlim : ∀ x ∈ K, Filter.Tendsto (fun j => φ (s j) x) Filter.atTop (nhds (ψ x)) := by
    intro x hx
    rw [hψeq x hx]
    have ht := (continuous_coe_real_ereal.tendsto (g x)).comp (hglim x hx)
    convert ht using 1
    funext j
    exact (hcoe (s j) x hx).symm
  refine ⟨s, ψ, hs, hψnn, hψ0, hψconv, hψmeas, ?_, hψrad, hψoff, ?_⟩
  · intro x hx
    refine ⟨?_, hlim x hx⟩
    rw [hψeq x hx]
    exact EReal.coe_ne_top _
  · have hscale := (ae_mem_closure_and_smul_mem_interior_convexHull_support μ h0).2
    let L : ℝ≥0∞ := Filter.liminf (fun j => ∫⁻ x, (φ (s j) x).toENNReal ∂μ) Filter.atTop
    have hcontract : ∀ t : ℝ, 0 ≤ t → t < 1 → ∫⁻ x, (ψ (t • x)).toENNReal ∂μ ≤ L := by
      intro t ht0 ht1
      have himage : ∀ᵐ x ∂μ, t • x ∈ K := hscale t ht0 ht1
      have hscaledmeas : ∀ j, AEMeasurable (fun x => (φ (s j) (t • x)).toENNReal) μ := by
        intro j
        exact
          aemeasurable_toENNReal_comp_of_continuousOn_toReal hK
            (continuous_const.smul continuous_id) (fun y hy => hnn (s j) y) (hfin (s j))
            ((hrealconv (s j)).continuousOn hK) himage
      have hscaledlim :
        ∀ᵐ x ∂μ,
          Filter.Tendsto (fun j => (φ (s j) (t • x)).toENNReal) Filter.atTop
            (nhds ((ψ (t • x)).toENNReal)) := by
        filter_upwards [himage] with x hx
        exact (EReal.continuous_toENNReal.tendsto (ψ (t • x))).comp (hlim _ hx)
      calc
        ∫⁻ x, (ψ (t • x)).toENNReal ∂μ =
            ∫⁻ x, Filter.liminf (fun j => (φ (s j) (t • x)).toENNReal) Filter.atTop ∂μ :=
          lintegral_congr_ae (hscaledlim.mono fun x hx => hx.liminf_eq.symm)
        _ ≤ Filter.liminf (fun j => ∫⁻ x, (φ (s j) (t • x)).toENNReal ∂μ) Filter.atTop :=
          lintegral_liminf_le' hscaledmeas
        _ ≤ L :=
          Filter.liminf_le_liminf
            (Filter.Eventually.of_forall fun j =>
              lintegral_mono fun x =>
                EReal.toENNReal_le_toENNReal
                  (le_of_smul_of_convex_epigraph (hnn (s j)) (hφ0 (s j)) (hconv (s j)) ht0
                    ht1.le x))
    have hradial :
      ∀ x,
        Filter.Tendsto (fun t : ℝ => (ψ (t • x)).toENNReal) (nhdsWithin 1 (Set.Iio 1))
          (nhds ((ψ x).toENNReal)) := by
      intro x
      exact (EReal.continuous_toENNReal.tendsto (ψ x)).comp (hψrad x)
    have hev : ∀ᶠ t : ℝ in nhdsWithin 1 (Set.Iio 1), ∫⁻ x, (ψ (t • x)).toENNReal ∂μ ≤ L := by
      have hpos : ∀ᶠ t : ℝ in nhdsWithin 1 (Set.Iio 1), 0 < t :=
        nhdsWithin_le_nhds (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
      filter_upwards [hpos, self_mem_nhdsWithin] with t ht0 ht1
      exact hcontract t ht0.le ht1
    calc
      ∫⁻ x, (ψ x).toENNReal ∂μ =
          ∫⁻ x,
            Filter.liminf (fun t : ℝ => (ψ (t • x)).toENNReal) (nhdsWithin 1 (Set.Iio 1)) ∂μ :=
        lintegral_congr_ae (Filter.Eventually.of_forall fun x => (hradial x).liminf_eq.symm)
      _ ≤
          Filter.liminf (fun t : ℝ => ∫⁻ x, (ψ (t • x)).toENNReal ∂μ)
            (nhdsWithin 1 (Set.Iio 1)) :=
        lintegral_liminf_le
          (fun t => hψmeas.comp (continuous_const.smul continuous_id).measurable)
      _ ≤ L := Filter.liminf_le_of_frequently_le' hev.frequently

end FunctionalInequalities.Probability

section
open Filter
open scoped Topology

namespace FunctionalInequalities.Probability.MomentMeasure

open FunctionalInequalities.Analysis

/-- **CEK Lemma 17 (56).** The original uniformly integrable nonnegative convex
sequence has one subsequence and one genuine integrable convex limit satisfying
both semicontinuity inequalities. The original interior, radial and off-closure
outputs are retained. Finite dual mass is a derived output; zero mass is allowed.
Source mass need not be one, and zero dimension is included. -/
theorem exists_subseq_integral_bounds_of_convex_epigraph
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (dx μ : Measure E) [dx.IsAddHaarMeasure] [IsFiniteMeasure μ]
    (h0 : (0 : E) ∈ interior (convexHull ℝ μ.support))
    (φ : ℕ → E → EReal) (hnn : ∀ ℓ x, 0 ≤ φ ℓ x) (hφ0 : ∀ ℓ, φ ℓ 0 = 0)
    (hconv : ∀ ℓ, Convex ℝ {p : E × ℝ | φ ℓ p.1 ≤ (p.2 : EReal)})
    (hmeas : ∀ ℓ, AEMeasurable (fun x => (φ ℓ x).toENNReal) μ)
    (hbdd : (⨆ ℓ, ∫⁻ x, (φ ℓ x).toENNReal ∂μ) ≠ ⊤) :
    ∃ (s : ℕ → ℕ) (ψ : E → EReal), StrictMono s ∧ (∀ x, 0 ≤ ψ x) ∧ ψ 0 = 0 ∧
      Convex ℝ {p : E × ℝ | ψ p.1 ≤ (p.2 : EReal)} ∧
      Measurable (fun x => (ψ x).toENNReal) ∧
      (∀ x ∈ interior (convexHull ℝ μ.support),
        ψ x ≠ ⊤ ∧ Tendsto (fun j => φ (s j) x) atTop (𝓝 (ψ x))) ∧
      (∀ x, Tendsto (fun t : ℝ => ψ (t • x)) (𝓝[<] 1) (𝓝 (ψ x))) ∧
      (∀ x ∉ closure (interior (convexHull ℝ μ.support)), ψ x = ⊤) ∧
      PotentialIntegrable ψ μ ∧ mass dx (legendre ψ) ≠ ⊤ ∧
      (∫⁻ x, (ψ x).toENNReal ∂μ ≤
        liminf (fun j => ∫⁻ x, (φ (s j) x).toENNReal ∂μ) atTop) ∧
      limsup (fun j => mass dx (legendre (φ (s j)))) atTop ≤ mass dx (legendre ψ) := by
  obtain ⟨s, ψ, hs, hψnn, hψ0, hψconv, hψmeas, hlim, hrad, hoff, hfirst⟩ :=
    FunctionalInequalities.Probability.exists_subseq_lintegral_le_liminf_of_convex_epigraph
      μ h0 φ hnn hφ0 hconv hmeas hbdd
  have hbot : ∀ x, ψ x ≠ ⊥ := fun x => ne_of_gt (EReal.bot_lt_zero.trans_le (hψnn x))
  have hψfinite : (∫⁻ x, (ψ x).toENNReal ∂μ) ≠ ⊤ := by
    apply ne_top_of_le_ne_top hbdd
    apply hfirst.trans
    exact liminf_le_of_frequently_le' (Eventually.of_forall fun j =>
      le_iSup (fun ℓ => ∫⁻ x, (φ ℓ x).toENNReal ∂μ) (s j)).frequently
  have hpot : PotentialIntegrable ψ μ := by
    refine ⟨hbot, ?_, ?_⟩
    · filter_upwards [ae_lt_top hψmeas hψfinite] with x hx
      intro ht
      simp only [ht, EReal.toENNReal_top, lt_self_iff_false] at hx
    · have hi := integrable_toReal_of_lintegral_ne_top hψmeas.aemeasurable hψfinite
      simpa only [EReal.toReal_toENNReal (hψnn _)] using hi
  obtain ⟨hdualfinite, hsecond⟩ := limsup_mass_legendre_le dx
    (fun j => φ (s j)) ψ isOpen_interior (convex_convexHull ℝ μ.support).interior h0
    (fun x hx => ⟨(hlim x hx).1, hbot x⟩) (fun x hx => (hlim x hx).2) hrad hoff
  exact ⟨s, ψ, hs, hψnn, hψ0, hψconv, hψmeas, hlim, hrad, hoff,
    hpot, hdualfinite, hfirst, hsecond⟩

end FunctionalInequalities.Probability.MomentMeasure
