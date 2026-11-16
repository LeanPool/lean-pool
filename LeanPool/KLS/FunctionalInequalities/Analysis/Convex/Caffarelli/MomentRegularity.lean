/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Probability.Transport
public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Caffarelli.Sublevel
public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.TruncatedConjugate

/-! # MomentRegularity in convex Monge--Ampere analysis

Caffarelli contact geometry supporting Letwin arXiv:2607.24164v1
Lemma 2.2 through BB arXiv:1207.6128v1 Theorem 2.24(ii).
The declarations retain their given-source hypotheses; domain contact
rigidity and moment-source regularity have separate consumers.
-/

@[expose] public section

section

section MomentStrictConvexity

open MeasureTheory Set Metric
open scoped RealInnerProductSpace ENNReal

/-! **Caffarelli's strict convexity** for moment-map potentials: a convex potential whose gradient
pushes a measure with bounded density forward to one with density bounded above and below on a
convex body is strictly convex. -/

namespace FunctionalInequalities.Analysis

/-- **The moment potential is strictly convex**: a convex Lipschitz `u` with `∫ e^{-u} = 1` whose
gradient pushes `e^{-u} dx` forward
to `1_K e^{-V} dx` (`K` compact convex nonempty, `V` continuous) is strictly convex. -/
theorem strictConvexOn_of_map_gradient {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    {u : E → ℝ} {L : NNReal} (hu : LipschitzWith L u) (hconv : ConvexOn ℝ univ u)
    (hnorm : ∫ x, Real.exp (-u x) ∂(volume : Measure E) = 1)
    {K : Set E} (hK : IsCompact K) (hKc : Convex ℝ K) (hKne : K.Nonempty)
    {V : E → ℝ} (hV : Continuous V)
    (hmap : ((volume : Measure E).tilted (-u)).map (gradient u) =
      (volume : Measure E).withDensity (K.indicator fun p => ENNReal.ofReal (Real.exp (-V p)))) :
    StrictConvexOn ℝ univ u := by
  classical
  have hgrad : Measurable (gradient u) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.measurable.comp
      (measurable_fderiv ℝ u)
  have hint : Integrable (fun x => Real.exp (-u x)) (volume : Measure E) :=
    Integrable.of_integral_ne_zero (by rw [hnorm]; exact one_ne_zero)
  have hae : ∀ᵐ x ∂(volume : Measure E), gradient u x ∈ K :=
    Probability.ae_mem_of_map_tilted_eq_withDensity_indicator volume volume hint
      hgrad.aemeasurable hK.measurableSet
      (by fun_prop) hmap
  have hsub : ∀ R : ℝ, IsCompact {x | u x ≤ R} :=
    (exists_forall_le_and_isCompact_sublevel_of_convexOn_integrable_exp_neg
      volume hconv hint).2
  obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn hV.continuousOn
  obtain ⟨q, hq⟩ := hKne
  have hDnonneg : 0 ≤ D := (norm_nonneg (V q)).trans (hD q hq)
  apply strictConvexOn_of_contact_eq hconv
  intro x p hp y hy
  let R : ℝ := max (u x) (u y) + 1
  have hyR : u y < R := by
    dsimp only [R]
    linarith [le_max_right (u x) (u y)]
  refine eq_of_contact_of_sublevel_bounds hconv hp (hsub R) ?_ hyR hy
  intro Q hQ _
  obtain ⟨C, hC⟩ := hQ.exists_bound_of_continuousOn hu.continuous.continuousOn
  refine ⟨Real.exp (-C - D), Real.exp (C + D), Real.exp_pos _, ?_⟩
  intro G hG hGQ
  have hbounds :
      ∀ᵐ z ∂(volume : Measure E).restrict G,
        ENNReal.ofReal (Real.exp (-C - D)) ≤
            ENNReal.ofReal (Real.exp (-u z + V (gradient u z))) ∧
          ENNReal.ofReal (Real.exp (-u z + V (gradient u z))) ≤
            ENNReal.ofReal (Real.exp (C + D)) := by
    filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem hG.measurableSet]
      with z hzK hzG
    have hzQ : z ∈ Q := hGQ (subset_closure hzG)
    have huz : -C ≤ u z ∧ u z ≤ C := by
      apply abs_le.mp
      simpa only [Real.norm_eq_abs] using hC z hzQ
    have hvz : -D ≤ V (gradient u z) ∧ V (gradient u z) ≤ D := by
      apply abs_le.mp
      simpa only [Real.norm_eq_abs] using hD (gradient u z) hzK
    constructor
    · apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      linarith [huz.2, hvz.1]
    · apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      linarith [huz.1, hvz.2, hDnonneg]
  rw [volume_subgradientImage_eq_lintegral_of_isOpen
    hu hconv hnorm hK.isClosed hKc hV.measurable hmap hG]
  constructor
  · calc
      ENNReal.ofReal (Real.exp (-C - D)) * (volume : Measure E) G =
          ∫⁻ z in G, ENNReal.ofReal (Real.exp (-C - D)) ∂(volume : Measure E) :=
        (setLIntegral_const G _).symm
      _ ≤ ∫⁻ z in G, ENNReal.ofReal (Real.exp (-u z + V (gradient u z)))
          ∂(volume : Measure E) :=
        lintegral_mono_ae (hbounds.mono fun _ hz => hz.1)
  · calc
      (∫⁻ z in G, ENNReal.ofReal (Real.exp (-u z + V (gradient u z)))
          ∂(volume : Measure E)) ≤
          ∫⁻ z in G, ENNReal.ofReal (Real.exp (C + D)) ∂(volume : Measure E) :=
        lintegral_mono_ae (hbounds.mono fun _ hz => hz.2)
      _ = ENNReal.ofReal (Real.exp (C + D)) * (volume : Measure E) G :=
        setLIntegral_const G _

end FunctionalInequalities.Analysis

end MomentStrictConvexity

section MomentC1

open MeasureTheory Set Metric
open scoped RealInnerProductSpace ENNReal

/-! **The moment-map potential is C¹**: strict convexity of the conjugate gives differentiability of
the potential. -/

namespace FunctionalInequalities.Analysis

private lemma exists_pos_sublevel_subset_of_zero_locus_subset {X : Type*} [TopologicalSpace X]
    {f : X → ℝ} (hf : Continuous f) (hnonneg : ∀ x, 0 ≤ f x)
    (hcompact : IsCompact {x | f x ≤ 1})
    {A : Set X} (hA : IsOpen A) (hzero : ∀ x, f x = 0 → x ∈ A) :
    ∃ R : ℝ, 0 < R ∧ {x | f x ≤ R} ⊆ A := by
  classical
  by_cases hne : ({x | f x ≤ 1} \ A).Nonempty
  · obtain ⟨z, hz, hmin⟩ :=
      (hcompact.diff hA).exists_isMinOn hne hf.continuousOn
    have hzpos : 0 < f z := by
      have hznot : f z ≠ 0 := fun h => hz.2 (hzero z h)
      exact lt_of_le_of_ne (hnonneg z) (Ne.symm hznot)
    refine ⟨min 1 (f z / 2), lt_min zero_lt_one (by linarith), ?_⟩
    intro x hx
    change f x ≤ min 1 (f z / 2) at hx
    by_contra hxA
    have hxB : x ∈ {x | f x ≤ 1} \ A :=
      ⟨hx.trans (min_le_left _ _), hxA⟩
    have hzx : f z ≤ f x := hmin hxB
    have hhalf : f x ≤ f z / 2 := hx.trans (min_le_right _ _)
    linarith
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x hx
    by_contra hxA
    exact hne ⟨x, hx, hxA⟩

section InnerProduct

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The moment potential is `C¹`**: a convex Lipschitz `u` with `∫ e^{-u} = 1` whose gradient
pushes
`e^{-u} dx` forward to `1_K e^{-V} dx` (`K` compact convex with nonempty interior, `V` continuous)
has exactly
one subgradient at every point, hence is continuously differentiable. -/
theorem contDiff_one_of_map_gradient [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E]
    [BorelSpace E] {u : E → ℝ} {L : NNReal} (hu : LipschitzWith L u) (hconv : ConvexOn ℝ univ u)
    (hnorm : ∫ x, Real.exp (-u x) ∂(volume : Measure E) = 1) {K : Set E} (hK : IsCompact K)
    (hKc : Convex ℝ K) (hKint : (interior K).Nonempty) {V : E → ℝ} (hV : Continuous V)
    (hmap :
      ((volume : Measure E).tilted (-u)).map (gradient u) =
        (volume : Measure E).withDensity
          (K.indicator fun p => ENNReal.ofReal (Real.exp (-V p)))) :
    ContDiff ℝ 1 u := by
  classical
  have hstrict : StrictConvexOn ℝ univ u :=
    strictConvexOn_of_map_gradient hu hconv hnorm hK hKc (hKint.mono interior_subset) hV hmap
  let ρ : E → ℝ≥0∞ := K.indicator fun p => ENNReal.ofReal (Real.exp (-V p))
  let w : E → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (-u x))
  have hρ : Measurable ρ := hV.measurable.neg.exp.ennreal_ofReal.indicator hK.measurableSet
  have hw : Measurable w := hu.continuous.measurable.neg.exp.ennreal_ofReal
  have hgrad : Measurable (gradient u) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.measurable.comp (measurable_fderiv ℝ u)
  have htilt : (volume : Measure E).tilted (-u) = volume.withDensity w := by
    change
      (volume : Measure E).withDensity
          (fun x =>
            ENNReal.ofReal (Real.exp (-u x) / ∫ y, Real.exp (-u y) ∂(volume : Measure E))) =
        volume.withDensity w
    simp only [hnorm, div_one, w]
  have hmap' : ((volume : Measure E).withDensity w).map (gradient u) = volume.withDensity ρ := by
    rw [← htilt]
    exact hmap
  have hμK : ∀ᵐ p ∂(volume : Measure E).withDensity ρ, p ∈ K := by
    apply (ae_withDensity_iff hρ).2
    exact
      Filter.Eventually.of_forall fun p hp => by
        by_contra h
        exact hp (Set.indicator_of_notMem h _)
  have hνK : ∀ᵐ x ∂(volume : Measure E).withDensity w, gradient u x ∈ K := by
    apply ae_of_ae_map hgrad.aemeasurable
    rw [hmap']
    exact hμK
  have hae : ∀ᵐ x ∂(volume : Measure E), gradient u x ∈ K := by
    have h := (ae_withDensity_iff hw).1 hνK
    filter_upwards [h] with x hx
    exact hx (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos (-u x))))
  have hsubK : ∀ x p, (∀ y, u x + ⟪p, y - x⟫ ≤ u y) → p ∈ K := by
    intro x p hp
    exact subgradient_mem_of_ae_gradient_mem hu hconv hK.isClosed hKc hae hp
  have hsubint : ∀ x p, (∀ y, u x + ⟪p, y - x⟫ ≤ u y) → p ∈ interior K := by
    intro x p hp
    exact subgradient_mem_interior_of_strictConvexOn hstrict hKc hKint hsubK hp
  obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn hV.continuousOn
  have hρK :
    ∀ p ∈ K, ENNReal.ofReal (Real.exp (-D)) ≤ ρ p ∧ ρ p ≤ ENNReal.ofReal (Real.exp D) := by
    intro p hp
    have hbound : -D ≤ V p ∧ V p ≤ D :=
      abs_le.mp (by simpa only [Real.norm_eq_abs] using hD p hp)
    dsimp only [ρ]
    rw [Set.indicator_of_mem hp]
    constructor
    · exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith [hbound.2]))
    · exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith [hbound.1]))
  apply contDiff_one_of_convexOn_of_unique_subgradient hconv
  intro xc
  obtain ⟨p₀, hp₀, _⟩ := exists_subgradient_slope_le_inner_add hconv xc (0 : E)
  let M : ℝ := ‖xc‖ + 1
  have hxc : ‖xc‖ < M := by dsimp only [M]; linarith
  have hM : 0 ≤ M := (norm_nonneg xc).trans hxc.le
  let f : E → ℝ := fun p => truncatedConjugate u M p - ⟪p, xc⟫ + u xc
  have hspec := truncatedConjugate_centered_spec hconv hxc
  have hfnonneg : ∀ p, 0 ≤ f p := hspec.1
  have hfzero : ∀ p, f p = 0 ↔ ∀ y, u xc + ⟪p, y - xc⟫ ≤ u y := hspec.2.1
  have hfcompact : ∀ R : ℝ, IsCompact {p | f p ≤ R} := hspec.2.2
  have hfeq : f = fun p => truncatedConjugate u M p - (⟪xc, p⟫ + (-u xc)) := by
    funext p
    dsimp only [f]
    rw [real_inner_comm p xc]
    ring
  have hfconv : ConvexOn ℝ univ f := by
    rw [hfeq]
    exact
      (convexOn_truncatedConjugate hu.continuous hM).sub
        (((innerₗ E xc).concaveOn convex_univ).add_const (-u xc))
  have hfcont : Continuous f := continuousOn_univ.mp (ConvexOn.continuousOn isOpen_univ hfconv)
  let A : Set E :=
    interior K ∩
      {p | ∀ x ∈ closedBall (0 : E) M, truncatedConjugate u M p = ⟪p, x⟫ - u x → ‖x‖ < M}
  have hAopen : IsOpen A :=
    isOpen_interior.inter (isOpen_setOf_truncatedConjugate_maximizer_lt hu.continuous hM)
  have hzeroA : ∀ p, f p = 0 → p ∈ A := by
    intro p hp
    have hpsub := (hfzero p).mp hp
    refine ⟨hsubint xc p hpsub, ?_⟩
    intro x hx heq
    have hxxc := eq_of_truncatedConjugate_eq_of_subgradient hstrict hxc hpsub hx heq
    rw [hxxc]
    exact hxc
  obtain ⟨R, hR, hRA⟩ :=
    exists_pos_sublevel_subset_of_zero_locus_subset hfcont hfnonneg (hfcompact 1) hAopen hzeroA
  obtain ⟨a, b, ha, hab⟩ :=
    exists_inverse_subgradient_volume_bounds hu hconv hnorm hmap hρ rfl hK.isClosed hKc
      (Real.exp_pos (-D)) hρK M
  have hB :
    ∀ Q : Set E,
      IsCompact Q →
        Q ⊆ {p | f p < R} →
          ∃ a b,
            0 < a ∧
              ∀ G : Set E,
                IsOpen G →
                  closure G ⊆ Q →
                    ENNReal.ofReal a * volume G ≤ volume (subgradientImage f G) ∧
                      volume (subgradientImage f G) ≤ ENNReal.ofReal b * volume G := by
    intro Q _ hQR
    refine ⟨a, b, ha, ?_⟩
    intro G hG hGQ
    have hGA : G ⊆ A := by
      intro p hp
      have hpR : f p < R := hQR (hGQ (subset_closure hp))
      exact hRA (show f p ≤ R from hpR.le)
    have hGK : G ⊆ K := fun p hp => interior_subset (hGA hp).1
    have hmax :
      ∀ p ∈ G, ∀ x ∈ closedBall (0 : E) M, truncatedConjugate u M p = ⟪p, x⟫ - u x → ‖x‖ < M := by
      intro p hp
      exact (hGA hp).2
    have hinv : {x | ∃ p ∈ G, ∀ y, u x + ⟪p, y - x⟫ ≤ u y} ⊆ closedBall (0 : E) M := by
      rintro x ⟨p, hpG, hpx⟩
      obtain ⟨z, hz, heq⟩ := (exists_truncatedConjugate_eq hu.continuous hM p).1
      have hzlt : ‖z‖ < M := hmax p hpG z hz heq
      have hpz : ∀ y, u z + ⟪p, y - z⟫ ≤ u y := by
        apply ((truncatedConjugate_centered_spec hconv hzlt).2.1 p).mp
        linarith [heq]
      have hxz : x = z := eq_of_strictConvexOn_of_support hstrict hpx hpz
      exact hxz.symm ▸ hz
    have hvol :
      volume (subgradientImage f G) = volume {x | ∃ p ∈ G, ∀ y, u x + ⟪p, y - x⟫ ≤ u y} := by
      rw [hfeq, volume_subgradientImage_sub_inner_add_const]
      rw [subgradientImage_truncatedConjugate_eq hu.continuous hstrict hM hmax]
    rw [hvol]
    exact hab G hG hGK hinv
  have hp₀zero : f p₀ = 0 := (hfzero p₀).mpr hp₀
  have hp₀f : ∀ q, f p₀ + ⟪(0 : E), q - p₀⟫ ≤ f q := by
    intro q
    simpa only [hp₀zero, inner_zero_left, add_zero] using hfnonneg q
  refine ⟨p₀, hp₀, ?_⟩
  intro p hp
  have hpzero : f p = 0 := (hfzero p).mpr hp
  apply eq_of_contact_of_sublevel_bounds hfconv hp₀f (hfcompact R) hB
  · simpa only [hpzero] using hR
  · simp only [hpzero, hp₀zero, inner_zero_left, add_zero]

end InnerProduct

end FunctionalInequalities.Analysis

end MomentC1
