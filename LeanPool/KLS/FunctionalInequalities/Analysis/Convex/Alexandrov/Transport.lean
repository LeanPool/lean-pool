/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Subgradient.Basic
public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Subgradient.Measure
public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Calculus.Deriv.AffineMap
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.LinearAlgebra.AffineSpace.Slope
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Tilted
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! # Alexandrov identities from gradient transport

The global supporting-image pushforward identity and local two-sided
supporting-image volume bounds for a given convex Lipschitz source and
actual source/target densities. The hypotheses are retained separately
from the cone geometry and domain measure construction.
-/

@[expose] public section

section
open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal

namespace FunctionalInequalities.Analysis



section InnerProduct

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private lemma alexandrov_gradient_support [CompleteSpace E]
    {u : E → ℝ} (hc : ConvexOn ℝ univ u)
    {x : E} (hx : DifferentiableAt ℝ u x) (y : E) :
    u x + ⟪gradient u x, y - x⟫ ≤ u y := by
  have hd :
      HasFDerivAt u ((InnerProductSpace.toDual ℝ E) (gradient u x))
        ((AffineMap.lineMap (k := ℝ) x y) (0 : ℝ)) := by
    simpa only [AffineMap.lineMap_apply_zero] using hx.hasGradientAt.hasFDerivAt
  have hl :
      HasDerivAt (u ∘ ⇑(AffineMap.lineMap (k := ℝ) x y))
        ⟪gradient u x, y - x⟫ (0 : ℝ) := by
    simpa only [InnerProductSpace.toDual_apply_apply] using
      hd.comp_hasDerivAt 0
        (AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := (0 : ℝ)))
  have hcl :
      ConvexOn ℝ univ (u ∘ ⇑(AffineMap.lineMap (k := ℝ) x y)) := by
    simpa only [preimage_univ] using
      ConvexOn.comp_affineMap (AffineMap.lineMap (k := ℝ) x y) hc
  have hle : ⟪gradient u x, y - x⟫ ≤ u y - u x := by
    simpa only [slope_def_field, Function.comp_apply,
      AffineMap.lineMap_apply_one, AffineMap.lineMap_apply_zero, sub_zero, div_one] using
      hcl.le_slope_of_hasDerivAt (mem_univ 0) (mem_univ 1)
        (zero_lt_one : (0 : ℝ) < 1) hl
  linarith

/-- **Alexandrov identity in push-forward form**: for a convex Lipschitz
`u` with `ν ≪ volume`, `ν.map (gradient u) = μ ≪ volume`, integrals of nonnegative functions over
the subgradient
image `∂u(S)` of a compact `S` against `μ` equal integrals over `S` of the composition with `∇u`
against `ν`. -/
theorem lintegral_subgradientImage_eq_of_map_gradient [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {u : E → ℝ} {L : NNReal} (hu : LipschitzWith L u)
    (hconv : ConvexOn ℝ univ u) {ν μ : Measure E} (hν : ν ≪ (volume : Measure E))
    (hmap : ν.map (gradient u) = μ) (hac : μ ≪ (volume : Measure E)) {S : Set E}
    (hS : IsCompact S) (g : E → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ p in subgradientImage u S, g p ∂μ = ∫⁻ x in S, g (gradient u x) ∂ν := by
  classical
  have hgrad : Measurable (gradient u) := by
    exact (InnerProductSpace.toDual ℝ E).symm.continuous.measurable.comp (measurable_fderiv ℝ u)
  have hT : MeasurableSet (subgradientImage u S) :=
    (isClosed_subgradientImage_of_isCompact hu.continuous hS).measurableSet
  let D : Set E :=
    {p | ∃ x y : E, x ≠ y ∧ (∀ z, u x + ⟪p, z - x⟫ ≤ u z) ∧ (∀ z, u y + ⟪p, z - y⟫ ≤ u z)}
  have hD : μ D = 0 := hac (volume_subgradient_two_points_eq_zero hu hconv)
  have hpre : ν (gradient u ⁻¹' D) = 0 := by
    apply le_antisymm
    · calc
        ν (gradient u ⁻¹' D) ≤ (ν.map (gradient u)) D :=
          Measure.le_map_apply hgrad.aemeasurable D
        _ = μ D := congrArg (fun m : Measure E => m D) hmap
        _ = 0 := hD
    · exact bot_le
  have havoid : ∀ᵐ x ∂ν, gradient u x ∉ D := by
    apply ae_iff.mpr
    apply measure_mono_null (t := gradient u ⁻¹' D) _ hpre
    intro x hx
    exact Classical.not_not.mp hx
  have hdiff : ∀ᵐ x ∂ν, DifferentiableAt ℝ u x := by
    exact ae_iff.mpr (hν (ae_iff.mp (hu.ae_differentiableAt (μ := (volume : Measure E)))))
  have hsets : (gradient u ⁻¹' subgradientImage u S) =ᵐ[ν] S := by
    filter_upwards [hdiff, havoid] with x hx hxD
    change (gradient u x ∈ subgradientImage u S) = (x ∈ S)
    apply propext
    constructor
    · rintro ⟨y, hyS, hy⟩
      by_contra hxS
      have hxy : x ≠ y := by
        intro h
        exact hxS (h.symm ▸ hyS)
      exact hxD ⟨x, y, hxy, alexandrov_gradient_support hconv hx, hy⟩
    · intro hxS
      exact ⟨x, hxS, alexandrov_gradient_support hconv hx⟩
  calc
    ∫⁻ p in subgradientImage u S, g p ∂μ =
        ∫⁻ p in subgradientImage u S, g p ∂(ν.map (gradient u)) := by
      rw [hmap]
    _ = ∫⁻ x in gradient u ⁻¹' subgradientImage u S, g (gradient u x) ∂ν :=
      setLIntegral_map hT hg hgrad
    _ = ∫⁻ x in S, g (gradient u x) ∂ν := setLIntegral_congr hsets

end InnerProduct

end FunctionalInequalities.Analysis

section LocalAlexandrovBounds

open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal

/-! Local two-sided Alexandrov bounds. -/

namespace FunctionalInequalities.Analysis

section FiniteDimensional

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]

omit [MeasurableSpace E] in
private lemma isCompact_subgradientImage_local
    {u : E → ℝ} {L : NNReal} (hu : LipschitzWith L u) {S : Set E}
    (hS : IsCompact S) :
    IsCompact (subgradientImage u S) := by
  let T : Set (E × E) :=
    (S ×ˢ Metric.closedBall (0 : E) (L : ℝ)) ∩
      ⋂ y : E, {z : E × E | u z.1 + ⟪z.2, y - z.1⟫ ≤ u y}
  have hclosed : IsClosed
      (⋂ y : E, {z : E × E | u z.1 + ⟪z.2, y - z.1⟫ ≤ u y}) := by
    apply isClosed_iInter
    intro y
    have hcont :
        Continuous (fun z : E × E => u z.1 + ⟪z.2, y - z.1⟫) :=
      (hu.continuous.comp continuous_fst).add
        (continuous_snd.inner (continuous_const.sub continuous_fst))
    exact isClosed_Iic.preimage hcont
  have hcompact : IsCompact T := by
    dsimp [T]
    exact (hS.prod (isCompact_closedBall (0 : E) (L : ℝ))).inter_right hclosed
  have hTimage : IsCompact (Prod.snd '' T) :=
    hcompact.image continuous_snd
  have hEq : Prod.snd '' T = subgradientImage u S := by
    ext p
    constructor
    · rintro ⟨⟨x, q⟩, hz, rfl⟩
      rcases hz with ⟨hzprod, hzall⟩
      refine ⟨x, hzprod.1, ?_⟩
      intro y
      exact Set.mem_iInter.mp hzall y
    · rintro ⟨x, hxS, hp⟩
      have hpbound : ‖p‖ ≤ (L : ℝ) := by
        have hnorm := hu.norm_sub_le (x + p) x
        have habs : |u (x + p) - u x| ≤ (L : ℝ) * ‖p‖ := by
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hnorm
        have hup : u (x + p) - u x ≤ (L : ℝ) * ‖p‖ :=
          (le_abs_self _).trans habs
        have hsub : u x + ⟪p, p⟫ ≤ u (x + p) := by
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hp (x + p)
        have hinner : ⟪p, p⟫ = ‖p‖ ^ 2 :=
          real_inner_self_eq_norm_sq p
        rw [hinner] at hsub
        nlinarith [norm_nonneg p, (show (0 : ℝ) ≤ (L : ℝ) by positivity)]
      have hpball : p ∈ Metric.closedBall (0 : E) (L : ℝ) := by
        change dist p 0 ≤ (L : ℝ)
        simpa [dist_eq_norm] using hpbound
      refine ⟨(x, p), ?_, rfl⟩
      refine ⟨⟨hxS, hpball⟩, ?_⟩
      apply Set.mem_iInter.mpr
      intro y
      exact hp y
  rw [← hEq]
  exact hTimage

/-- **Local two-sided Alexandrov bounds** (input of the Caffarelli
argument): if `u` is convex and Lipschitz, `ν = e^{-u} dx` (normalized), `ν.map ∇u = μ` has a
density `ρ` bounded above and below on a closed convex `K` containing `∇u` a.e., then on every
compact
`Q` the volume of the subgradient image is comparable to the volume of the set:
`a · vol S ≤ vol (∂u(S)) ≤ b · vol S` for all compact `S ⊆ Q`, with `0 < a`. -/
theorem exists_local_subgradientImage_volume_bounds [BorelSpace E] {u : E → ℝ} {L : NNReal}
    (hu : LipschitzWith L u) (hconv : ConvexOn ℝ univ u)
    (hnorm : ∫ x, Real.exp (-u x) ∂(volume : Measure E) = 1) {μ : Measure E}
    (hmap : ((volume : Measure E).tilted (-u)).map (gradient u) = μ) {ρ : E → ℝ≥0∞}
    (hρ : Measurable ρ) (hμ : μ = (volume : Measure E).withDensity ρ) {K : Set E}
    (hK : IsClosed K) (hKc : Convex ℝ K) (hae : ∀ᵐ x ∂(volume : Measure E), gradient u x ∈ K)
    {c C : ℝ} (hc : 0 < c) (hρK : ∀ p ∈ K, ENNReal.ofReal c ≤ ρ p ∧ ρ p ≤ ENNReal.ofReal C)
    {Q : Set E} (hQ : IsCompact Q) :
    ∃ a b : ℝ,
      0 < a ∧
        ∀ S : Set E,
          IsCompact S →
            S ⊆ Q →
              ENNReal.ofReal a * (volume : Measure E) S ≤
                  (volume : Measure E) (subgradientImage u S) ∧
                (volume : Measure E) (subgradientImage u S) ≤
                  ENNReal.ofReal b * (volume : Measure E) S := by
  have _hρ : Measurable ρ := hρ
  let ν : Measure E := (volume : Measure E).tilted (-u)
  have hν : ν ≪ (volume : Measure E) := by
    dsimp [ν, Measure.tilted]
    exact MeasureTheory.withDensity_absolutelyContinuous _ _
  have hμac : μ ≪ (volume : Measure E) := by
    rw [hμ]
    exact MeasureTheory.withDensity_absolutelyContinuous _ _
  have hν_eq :
    ν = (volume : Measure E).withDensity (fun x => ENNReal.ofReal (Real.exp (-u x))) := by
    dsimp [ν, Measure.tilted]
    rw [hnorm]
    simp
  by_cases hQne : Q.Nonempty
  · obtain ⟨xm, hxmQ, hxm⟩ := hQ.exists_isMaxOn hQne hu.continuous.continuousOn
    obtain ⟨xn, hxnQ, hxn⟩ := hQ.exists_isMinOn hQne hu.continuous.continuousOn
    let m : ℝ := u xm
    let n : ℝ := u xn
    let C' : ℝ := max C 1
    let a : ℝ := Real.exp (-m) / C'
    let b : ℝ := Real.exp (-n) / c
    have hC'pos : 0 < C' := by
      dsimp [C']
      exact lt_of_lt_of_le zero_lt_one (le_max_right C 1)
    have ha : 0 < a := by
      dsimp [a]
      positivity
    refine ⟨a, b, ha, ?_⟩
    intro S hS hSQ
    have hSmeas : MeasurableSet S := hS.measurableSet
    have hIcompact : IsCompact (subgradientImage u S) := isCompact_subgradientImage_local hu hS
    have hImeas : MeasurableSet (subgradientImage u S) := hIcompact.measurableSet
    have hνS : ν S = ∫⁻ x in S, ENNReal.ofReal (Real.exp (-u x)) := by
      rw [hν_eq]
      exact MeasureTheory.withDensity_apply _ hSmeas
    have hident : ∫⁻ p in subgradientImage u S, (1 : ℝ≥0∞) ∂μ = ∫⁻ x in S, (1 : ℝ≥0∞) ∂ν :=
      lintegral_subgradientImage_eq_of_map_gradient hu hconv hν (by simpa [ν] using hmap) hμac
        hS 1 measurable_const
    have hμS : μ (subgradientImage u S) = ν S := by
      simpa [MeasureTheory.lintegral_one, MeasureTheory.Measure.restrict_apply_univ] using
        hident
    have hsubK : subgradientImage u S ⊆ K := by
      intro p hp
      rcases hp with ⟨x, hxS, hp⟩
      exact subgradient_mem_of_ae_gradient_mem hu hconv hK hKc hae hp
    have hlowerν : ENNReal.ofReal (Real.exp (-m)) * (volume : Measure E) S ≤ ν S := by
      rw [hνS]
      calc
        ENNReal.ofReal (Real.exp (-m)) * (volume : Measure E) S =
            ∫⁻ x in S, ENNReal.ofReal (Real.exp (-m)) :=
          (MeasureTheory.setLIntegral_const S _).symm
        _ ≤ ∫⁻ x in S, ENNReal.ofReal (Real.exp (-u x)) := by
          apply MeasureTheory.setLIntegral_mono' hSmeas
          intro x hx
          have hxu : u x ≤ m := hxm (hSQ hx)
          exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg hxu))
    have hupperν : ν S ≤ ENNReal.ofReal (Real.exp (-n)) * (volume : Measure E) S := by
      rw [hνS]
      calc
        ∫⁻ x in S, ENNReal.ofReal (Real.exp (-u x)) ≤
            ∫⁻ x in S, ENNReal.ofReal (Real.exp (-n)) := by
          apply MeasureTheory.setLIntegral_mono' hSmeas
          intro x hx
          have hxu : n ≤ u x := hxn (hSQ hx)
          exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg hxu))
        _ = ENNReal.ofReal (Real.exp (-n)) * (volume : Measure E) S :=
          MeasureTheory.setLIntegral_const S _
    have hμlower :
      ENNReal.ofReal c * (volume : Measure E) (subgradientImage u S) ≤
        μ (subgradientImage u S) := by
      rw [hμ, MeasureTheory.withDensity_apply ρ hImeas]
      calc
        ENNReal.ofReal c * (volume : Measure E) (subgradientImage u S) =
            ∫⁻ p in subgradientImage u S, ENNReal.ofReal c :=
          (MeasureTheory.setLIntegral_const _ _).symm
        _ ≤ ∫⁻ p in subgradientImage u S, ρ p := by
          apply MeasureTheory.setLIntegral_mono' hImeas
          intro p hp
          exact (hρK p (hsubK hp)).1
    have hμupper :
      μ (subgradientImage u S) ≤
        ENNReal.ofReal C' * (volume : Measure E) (subgradientImage u S) := by
      rw [hμ, MeasureTheory.withDensity_apply ρ hImeas]
      calc
        ∫⁻ p in subgradientImage u S, ρ p ≤ ∫⁻ p in subgradientImage u S, ENNReal.ofReal C' := by
          apply MeasureTheory.setLIntegral_mono' hImeas
          intro p hp
          exact le_trans (hρK p (hsubK hp)).2 (ENNReal.ofReal_mono (le_max_left C 1))
        _ = ENNReal.ofReal C' * (volume : Measure E) (subgradientImage u S) :=
          MeasureTheory.setLIntegral_const _ _
    constructor
    · have hmul :
        ENNReal.ofReal (Real.exp (-m)) * (volume : Measure E) S ≤
          ENNReal.ofReal C' * (volume : Measure E) (subgradientImage u S) := by
        calc
          ENNReal.ofReal (Real.exp (-m)) * (volume : Measure E) S ≤ ν S := hlowerν
          _ = μ (subgradientImage u S) := hμS.symm
          _ ≤ _ := hμupper
      have hC0 : ENNReal.ofReal C' ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hC'pos)
      have hCne : ENNReal.ofReal C' ≠ ∞ := ENNReal.ofReal_ne_top
      have hdiv :
        (ENNReal.ofReal (Real.exp (-m)) * (volume : Measure E) S) / ENNReal.ofReal C' ≤
          (volume : Measure E) (subgradientImage u S) := by
        apply (ENNReal.div_le_iff hC0 hCne).mpr
        simpa [mul_comm] using hmul
      have hdiv' :
        ENNReal.ofReal (Real.exp (-m) / C') * (volume : Measure E) S ≤
          (volume : Measure E) (subgradientImage u S) := by
        simpa [ENNReal.ofReal_div_of_pos hC'pos, ENNReal.div_eq_inv_mul, mul_assoc,
          mul_left_comm, mul_comm] using hdiv
      simpa [a] using hdiv'
    · have hmul :
        ENNReal.ofReal c * (volume : Measure E) (subgradientImage u S) ≤
          ENNReal.ofReal (Real.exp (-n)) * (volume : Measure E) S := by
        calc
          ENNReal.ofReal c * (volume : Measure E) (subgradientImage u S) ≤
              μ (subgradientImage u S) :=
            hμlower
          _ = ν S := hμS
          _ ≤ _ := hupperν
      have hc0 : ENNReal.ofReal c ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hc)
      have hcne : ENNReal.ofReal c ≠ ∞ := ENNReal.ofReal_ne_top
      have hdiv :
        (volume : Measure E) (subgradientImage u S) ≤
          (ENNReal.ofReal (Real.exp (-n)) * (volume : Measure E) S) / ENNReal.ofReal c := by
        apply (ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl hcne)).mpr
        simpa [mul_comm] using hmul
      have hdiv' :
        (volume : Measure E) (subgradientImage u S) ≤
          ENNReal.ofReal (Real.exp (-n) / c) * (volume : Measure E) S := by
        simpa [ENNReal.ofReal_div_of_pos hc, ENNReal.div_eq_inv_mul, mul_assoc, mul_left_comm,
          mul_comm] using hdiv
      simpa [b] using hdiv'
  · have hQempty : Q = ∅ := Set.not_nonempty_iff_eq_empty.mp hQne
    refine ⟨1, 1, by norm_num, ?_⟩
    intro S hS hSQ
    have hSsub : S ⊆ (∅ : Set E) := by
      intro x hx
      rw [hQempty] at hSQ
      exact hSQ hx
    have hSempty : S = ∅ := Set.Subset.antisymm hSsub (Set.empty_subset S)
    rw [hSempty]
    simp [subgradientImage]

end FiniteDimensional

end FunctionalInequalities.Analysis

end LocalAlexandrovBounds
