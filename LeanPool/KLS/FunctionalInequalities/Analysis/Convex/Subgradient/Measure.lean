/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Subgradient.Basic
public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Legendre.Variation.Attainment
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Convex.Measure

/-!
# Almost-everywhere differentiability and supporting-slope uniqueness

Supporting convex infrastructure for Letwin arXiv:2607.24164v1
Theorem 1.2 and Lemma 2.2. Mathematical scopes and source attributions
are retained in the individual declarations.
-/

@[expose] public section

section
open MeasureTheory Set
open scoped RealInnerProductSpace

namespace FunctionalInequalities.Analysis

section ConvexAeDifferentiable

open MeasureTheory Set

/-! Convex functions on open sets are differentiable almost everywhere. -/

/-- **A convex function on an open set is differentiable almost everywhere on it** (Rademacher for
convex functions; support for the a.e. injectivity of the subgradient map). -/
theorem ConvexOn.ae_differentiableAt_of_isOpen {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {U : Set E} (hU : IsOpen U) {f : E → ℝ} (hf : ConvexOn ℝ U f) :
    ∀ᵐ x ∂μ, x ∈ U → DifferentiableAt ℝ f x := by
  let I := {x : E // x ∈ U}
  have hball : ∀ x : I, ∃ q : ℝ × NNReal,
      0 < q.1 ∧ LipschitzOnWith q.2 f (Metric.ball (x : E) q.1) ∧
        Metric.ball (x : E) q.1 ⊆ U := by
    intro x
    rcases hf.locallyLipschitzOn hU x.property with ⟨K, t, ht, hK⟩
    have hU_nhds : U ∈ nhds (x : E) := hU.mem_nhds x.property
    have hnhds : nhdsWithin (x : E) U = nhds (x : E) :=
      nhdsWithin_eq_nhds.mpr hU_nhds
    have htx : t ∈ nhds (x : E) := by
      rw [← hnhds]
      exact ht
    rcases Metric.mem_nhds_iff.mp
        (Filter.inter_mem htx (hU.mem_nhds x.property)) with ⟨r, hr, hrt⟩
    exact ⟨(r, K), hr, hK.mono (hrt.trans inter_subset_left),
      hrt.trans inter_subset_right⟩
  let q : I → ℝ × NNReal := fun x => Classical.choose (hball x)
  let B : I → Set E := fun x => Metric.ball (x : E) (q x).1
  have hq : ∀ x : I, 0 < (q x).1 ∧ LipschitzOnWith (q x).2 f (B x) ∧ B x ⊆ U := by
    intro x
    exact Classical.choose_spec (hball x)
  have hAE : ∀ x : I, ∀ᵐ y ∂μ, y ∈ B x → DifferentiableAt ℝ f y := by
    intro x
    filter_upwards [(hq x).2.1.ae_differentiableWithinAt_of_mem] with y hy
    intro hyB
    exact (hy hyB).differentiableAt (Metric.isOpen_ball.mem_nhds hyB)
  obtain ⟨T, hT, hTU⟩ :=
    TopologicalSpace.isOpen_iUnion_countable B (fun x => Metric.isOpen_ball)
  have hTcount : Countable T := hT.to_subtype
  have hBU : (⋃ x, B x) = U := by
    apply Subset.antisymm
    · exact iUnion_subset fun x => (hq x).2.2
    · intro y hy
      let x : I := ⟨y, hy⟩
      exact mem_iUnion.2 ⟨x, Metric.mem_ball_self (hq x).1⟩
  have hAEall : ∀ᵐ y ∂μ, ∀ x : T, y ∈ B (x : I) →
      DifferentiableAt ℝ f y := by
    exact ae_all_iff.2 (fun x => hAE (x : I))
  filter_upwards [hAEall] with y hy
  intro hyU
  have hyT : y ∈ ⋃ x ∈ T, B x := by
    rw [hTU, hBU]
    exact hyU
  rcases mem_iUnion₂.mp hyT with ⟨x, hxT, hyx⟩
  exact hy ⟨x, hxT⟩ hyx

end ConvexAeDifferentiable

end FunctionalInequalities.Analysis
namespace FunctionalInequalities.Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Subgradients of a convex Lipschitz function lie in the closed convex range of its a.e.
gradient** (`∂u(x) ⊆ Kbar` for the weak moment map, whose gradient lies
a.e. in the target `K`): if `u` is convex and Lipschitz on a finite-dimensional inner product space,
`K` is closed and convex and `∇u(x) ∈ K` for a.e. `x`, then every subgradient `p` of `u` at every
point `x` (`u(x) + ⟪p, y − x⟫ ≤ u(y)` for all `y`) lies in `K`. -/
theorem subgradient_mem_of_ae_gradient_mem [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] {u : E → ℝ} {L : NNReal} (hu : LipschitzWith L u) (hconv : ConvexOn ℝ univ u)
    {K : Set E} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hae : ∀ᵐ x ∂(volume : Measure E), gradient u x ∈ K) {x p : E}
    (hp : ∀ y, u x + ⟪p, y - x⟫ ≤ u y) : p ∈ K := by
  by_contra hpn
  obtain ⟨f, s, hps, hsep⟩ := geometric_hahn_banach_point_closed hKc hK hpn
  let θ : E := (InnerProductSpace.toDual ℝ E).symm f
  have hθ : ∀ q : E, ⟪q, θ⟫ = f q := by
    intro q
    rw [real_inner_comm]
    exact
      InnerProductSpace.toDual_symm_apply
  -- The differentiability points with gradient in K form a dense set.
  have hdense : Dense {z | DifferentiableAt ℝ u z ∧ gradient u z ∈ K} :=
    MeasureTheory.Measure.dense_of_ae
      ((hu.ae_differentiableAt (μ := (volume : Measure E))).and hae)
  -- Convexity gives the bound on the dense set; continuity extends it everywhere.
  have hbound : ∀ z ∈ {z | DifferentiableAt ℝ u z ∧ gradient u z ∈ K}, s ≤ u (z + θ) - u z := by
    intro z hz
    exact (hsep _ hz.2).le.trans ((hθ (gradient u z)) ▸ gradient_le_increment hconv z θ hz.1)
  have hb : ∀ z : E, s ≤ u (z + θ) - u z := by
    intro z
    exact
      hdense.induction hbound
        (isClosed_le continuous_const
          ((hu.continuous.comp (continuous_id.add_const θ)).sub hu.continuous))
        z
  have hb' : s ≤ u x - u (x - θ) := by simpa only [sub_add_cancel] using hb (x - θ)
  have hp' := hp (x - θ)
  simp only [sub_sub_cancel_left, inner_neg_right, hθ] at hp'
  linarith


end FunctionalInequalities.Analysis
section SubgradientAeInjective

open MeasureTheory Set
open scoped RealInnerProductSpace

/-! Almost-everywhere injectivity of the subgradient map. -/

namespace FunctionalInequalities.Analysis

section InnerProduct

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem legendre_eq_of_subgradient (u : E → ℝ) (x p : E)
    (hsub : ∀ z, u x + ⟪p, z - x⟫ ≤ u z) :
    (⟪x, p⟫ : EReal) - (u x : EReal) =
      legendre (fun z => (u z : EReal)) p := by
  apply le_antisymm
  · change (⟪x, p⟫ : EReal) - (u x : EReal) ≤
      ⨆ z : E, (⟪z, p⟫ : EReal) - (u z : EReal)
    exact le_iSup (fun z : E => (⟪z, p⟫ : EReal) - (u z : EReal)) x
  · change (⨆ z : E, (⟪z, p⟫ : EReal) - (u z : EReal)) ≤
      (⟪x, p⟫ : EReal) - (u x : EReal)
    apply iSup_le
    intro z
    have hz := hsub z
    rw [inner_sub_right] at hz
    rw [← real_inner_comm p z, ← real_inner_comm p x] at hz
    have hz' : ⟪z, p⟫ - u z ≤ ⟪x, p⟫ - u x := by
      linarith
    simpa only [EReal.coe_sub] using
      (EReal.coe_le_coe_iff.mpr hz')

/-- **Almost every subgradient belongs to a single point** (the
Alexandrov identity): for a convex Lipschitz `u` on a finite-dimensional inner product space, the
set of `p` that are subgradients of `u` at two distinct points is Lebesgue-null (such `p` are
non-differentiability points of the conjugate `u*`, or frontier points of its domain). -/
theorem volume_subgradient_two_points_eq_zero [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] {u : E → ℝ} {L : NNReal} (hu : LipschitzWith L u)
    (hconv : ConvexOn ℝ univ u) :
    (volume : Measure E)
        {p : E |
          ∃ x y : E, x ≠ y ∧ (∀ z, u x + ⟪p, z - x⟫ ≤ u z) ∧ (∀ z, u y + ⟪p, z - y⟫ ≤ u z)} =
      0 := by
  have _ := hu
  have _ := hconv
  classical
  let φ : E → EReal := fun x => (u x : EReal)
  let Dom : Set E := {q | legendre φ q ≠ ⊤}
  let g : E → ℝ := fun q => (legendre φ q).toReal
  let S : Set E :=
    {p : E | ∃ x y : E, x ≠ y ∧ (∀ z, u x + ⟪p, z - x⟫ ≤ u z) ∧ (∀ z, u y + ⟪p, z - y⟫ ≤ u z)}
  change (volume : Measure E) S = 0
  have hφ : ProperPotential φ := by
    refine ⟨?_, ⟨0, ?_⟩⟩
    · intro x
      exact EReal.coe_ne_bot _
    · exact EReal.coe_ne_top _
  have hconvφ : ConvexPotential (legendre φ) := convexPotential_legendre φ hφ.2
  have hDom : Convex ℝ Dom := hconvφ.convex_domain
  have hconvG : ConvexOn ℝ (interior Dom) g :=
    hconvφ.convexOn_toReal.subset interior_subset hDom.interior
  have hae : ∀ᵐ q : E ∂(volume : Measure E), q ∈ interior Dom → DifferentiableAt ℝ g q :=
    FunctionalInequalities.Analysis.ConvexOn.ae_differentiableAt_of_isOpen (volume : Measure E)
      isOpen_interior hconvG
  let B : Set E := {q | q ∈ interior Dom ∧ ¬DifferentiableAt ℝ g q}
  have hB : (volume : Measure E) B = 0 := by
    have hnot : ∀ᵐ q : E ∂(volume : Measure E), q ∉ B := by
      filter_upwards [hae] with q hq
      intro hqB
      change q ∈ interior Dom ∧ ¬DifferentiableAt ℝ g q at hqB
      exact hqB.2 (hq hqB.1)
    have hz := ae_iff.mp hnot
    have hset : {q : E | ¬q ∉ B} = B := by
      ext q
      simp
    rw [hset] at hz
    exact hz
  have hfrontier : (volume : Measure E) (frontier Dom) = 0 :=
    Convex.addHaar_frontier (volume : Measure E) hDom
  have hsubset : S ⊆ frontier Dom ∪ B := by
    intro p hp
    rcases hp with ⟨x, y, hxy, hx, hy⟩
    have hxEq : (⟪x, p⟫ : EReal) - φ x = legendre φ p := by
      simpa only [φ] using legendre_eq_of_subgradient u x p hx
    have hyEq : (⟪y, p⟫ : EReal) - φ y = legendre φ p := by
      simpa only [φ] using legendre_eq_of_subgradient u y p hy
    have hterm : (⟪x, p⟫ : EReal) - φ x ≠ ⊤ := by
      intro ht
      have ht' : ((⟪x, p⟫ - u x : ℝ) : EReal) = ⊤ := by simpa only [φ, EReal.coe_sub] using ht
      exact EReal.coe_ne_top _ ht'
    have hpD : p ∈ Dom := by
      intro htop
      exact hterm (hxEq.trans htop)
    have hpcl : p ∈ closure Dom := subset_closure hpD
    rw [closure_eq_interior_union_frontier] at hpcl
    rcases hpcl with hpI | hpF
    · right
      change p ∈ interior Dom ∧ ¬DifferentiableAt ℝ g p
      refine ⟨hpI, ?_⟩
      intro hd
      have hd' : DifferentiableAt ℝ (fun q => (legendre φ q).toReal) p := by
        simpa only [g] using hd
      have hxg := conjugate_maximizer_eq_gradient φ hφ hpI hd' x hxEq
      have hyg := conjugate_maximizer_eq_gradient φ hφ hpI hd' y hyEq
      exact hxy (hxg.trans hyg.symm)
    · left
      exact hpF
  exact measure_mono_null hsubset (measure_union_null hfrontier hB)

end InnerProduct

end FunctionalInequalities.Analysis

end SubgradientAeInjective
section AffineLineSubgradient

open MeasureTheory Set
open scoped RealInnerProductSpace

/-! Subgradients along a segment where the function is affine form a null set (Caffarelli block). -/

namespace FunctionalInequalities.Analysis

section InnerProduct

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **A function affine along a full line pins every subgradient** (Caffarelli's argument): if
`u (x₀ + t θ) = u x₀ + t c` for all real `t`, then every subgradient `p` of `u` at
any point satisfies `⟪p, θ⟫ = c`. -/
theorem inner_subgradient_eq_of_affine_on_line {u : E → ℝ} {x₀ θ : E} {c : ℝ}
    (hline : ∀ t : ℝ, u (x₀ + t • θ) = u x₀ + t * c) {x p : E}
    (hp : ∀ y, u x + ⟪p, y - x⟫ ≤ u y) : ⟪p, θ⟫ = c := by
  have hineq (t : ℝ) :
      u x + ⟪p, (x₀ + t • θ) - x⟫ ≤ u x₀ + t * c := by
    calc
      u x + ⟪p, (x₀ + t • θ) - x⟫ ≤ u (x₀ + t • θ) :=
        hp (x₀ + t • θ)
      _ = u x₀ + t * c := hline t
  have hzero : ⟪p, θ⟫ - c = 0 := by
    by_contra hne
    let K : ℝ := u x₀ - u x - ⟪p, x₀ - x⟫
    let t : ℝ := (K + 1) / (⟪p, θ⟫ - c)
    have ht := hineq t
    have harg : (x₀ + t • θ) - x = (x₀ - x) + t • θ := by
      abel
    rw [harg, inner_add_right, inner_smul_right] at ht
    have ht' : t * (⟪p, θ⟫ - c) ≤ K := by
      dsimp [K]
      nlinarith [ht]
    have hprod : t * (⟪p, θ⟫ - c) = K + 1 := by
      dsimp [t]
      exact div_mul_cancel₀ (K + 1) hne
    nlinarith [ht', hprod]
  linarith

/-- The set of subgradients of a function affine along a line in a nonzero direction is
Lebesgue-null (it lies in an affine hyperplane). -/
theorem volume_setOf_subgradient_eq_zero_of_affine_on_line [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {u : E → ℝ} {x₀ θ : E} (hθ : θ ≠ 0) {c : ℝ}
    (hline : ∀ t : ℝ, u (x₀ + t • θ) = u x₀ + t * c) :
    (volume : Measure E) {p | ∃ x, ∀ y, u x + ⟪p, y - x⟫ ≤ u y} = 0 := by
  let L : E →ₗ[ℝ] ℝ :=
    { toFun := fun p => ⟪p, θ⟫
      map_add' := by
        intro p q
        exact inner_add_left p q θ
      map_smul' := by
        intro a p
        change ⟪a • p, θ⟫ = a * ⟪p, θ⟫
        exact real_inner_smul_left p θ a }
  let p₀ : E := (c / ⟪θ, θ⟫) • θ
  have hθθ : ⟪θ, θ⟫ ≠ 0 := (inner_self_ne_zero).2 hθ
  have hp₀ : L p₀ = c := by
    dsimp [L, p₀]
    rw [real_inner_smul_left]
    exact div_mul_cancel₀ c hθθ
  let H : AffineSubspace ℝ E := AffineSubspace.mk' p₀ L.ker
  have hq : p₀ + θ ∉ H := by
    intro hmem
    change p₀ + θ ∈ AffineSubspace.mk' p₀ L.ker at hmem
    have hv : (p₀ + θ) -ᵥ p₀ ∈ L.ker := (AffineSubspace.mem_mk').mp hmem
    have hz : L ((p₀ + θ) -ᵥ p₀) = 0 := (LinearMap.mem_ker).mp hv
    have hz' : ⟪θ, θ⟫ = 0 := by simpa [L] using hz
    exact hθθ hz'
  have hHtop : H ≠ (⊤ : AffineSubspace ℝ E) := by
    intro htop
    apply hq
    rw [htop]
    exact AffineSubspace.mem_top ℝ E (p₀ + θ)
  apply measure_mono_null ?_ (Measure.addHaar_affineSubspace volume H hHtop)
  intro p hp
  rcases hp with ⟨x, hx⟩
  have hpc : ⟪p, θ⟫ = c := inner_subgradient_eq_of_affine_on_line hline hx
  have hpL : L p = c := by simpa [L] using hpc
  change p ∈ AffineSubspace.mk' p₀ L.ker
  apply (AffineSubspace.mem_mk').2
  apply (LinearMap.mem_ker).2
  change L (p - p₀) = 0
  calc
    L (p - p₀) = L p - L p₀ := L.map_sub p p₀
    _ = c - c := by rw [hpL, hp₀]
    _ = 0 := sub_self c

end InnerProduct

end FunctionalInequalities.Analysis

end AffineLineSubgradient
