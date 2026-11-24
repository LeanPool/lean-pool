/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.GermParametrizationData
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.HolomorphicCoefficientPolynomials
public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The parametrizing sets of an irreducible germ

Blueprint `lag:parametrization-sets`, `lag:parametrization-regular` (Demailly, *Complex
analytic and differential geometry*, II.4.19).

From the pointwise identities `ParametrizationData A` we build `SetsData`: on a small
polydisc the fibre coordinates of `A` are small over small base points (the roots of the
Weierstrass polynomials `Q_k(z', ·)` tend to `0`), the fibre over a point off the
discriminant locus consists of the `q` points `(x, B(x, t) / δ(x))`, `W(x, t) = 0`, and
near such a point `A` is the graph of `x ↦ B(x, ω(x)) / δ(x)`, where `ω` is the holomorphic
simple root of `W(x, ·)` given by the implicit function theorem.
-/

@[expose] public section

open Set Filter Metric
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.GermParametrizationData

open FirstPass RegularLocusDense AnalyticGermDecomposition

noncomputable section

variable {n : ℕ} {A : Set (ComplexModel n)}

/-! ### Norms and polydiscs -/

theorem norm_le_sum_norm (z : ComplexModel n) : ‖z‖ ≤ ∑ i, ‖z i‖ := by
  rw [EuclideanSpace.norm_eq]
  calc √(∑ i, ‖z i‖ ^ 2) ≤ √((∑ i, ‖z i‖) ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_sq_le_sq_sum_of_nonneg fun _ _ => norm_nonneg _)
    _ = ∑ i, ‖z i‖ := Real.sqrt_sq (Finset.sum_nonneg fun _ _ => norm_nonneg _)

theorem norm_apply_le_norm_coordinateProjection {d : ℕ} (z : ComplexModel n) (i : Fin n)
    (hi : i.1 < d) : ‖z i‖ ≤ ‖coordinateProjection n d z‖ := by
  have := PiLp.norm_apply_le (coordinateProjection n d z) ⟨i.1, hi⟩
  simpa [coordinateProjection_apply, i.2] using this

theorem polydisc_subset_ball {d : ℕ} {r : ℝ} (hr : 0 < r) :
    polydisc n d r r ⊆ ball 0 ((n + 1) * r) := by
  intro z hz
  rw [mem_ball_zero_iff]
  have hle : ∀ i ∈ (Finset.univ : Finset (Fin n)), ‖z i‖ ≤ r := fun i _ => by
    by_cases hi : i.1 < d
    · exact ((norm_apply_le_norm_coordinateProjection z i hi).trans_lt hz.1).le
    · exact (hz.2 i (not_lt.mp hi)).le
  calc ‖z‖ ≤ ∑ i, ‖z i‖ := norm_le_sum_norm z
    _ ≤ n * r := by simpa using Finset.sum_le_card_nsmul _ _ _ hle
    _ < (n + 1) * r := by nlinarith

/-! ### Roots of monic polynomials with function coefficients -/

/-- A monic polynomial of degree `q` over `ℂ` whose roots are simple has exactly `q` roots. -/
theorem ncard_setOf_monicEval_eq_zero {E : Type*} (q : ℕ) (a : ℕ → E → ℂ) (x : E)
    (hsimple : ∀ t, monicEval q a x t = 0 → deriv (monicEval q a x) t ≠ 0) :
    {t | monicEval q a x t = 0}.Finite ∧ {t | monicEval q a x t = 0}.ncard = q := by
  classical
  open Polynomial in
  set p : ℂ[X] := X ^ q + ∑ j : Fin q, C (a j x) * X ^ (j : ℕ) with hp
  have hmonic : p.Monic := Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt _)
  have hp0 : p ≠ 0 := hmonic.ne_zero
  have heval : monicEval q a x = fun t => p.eval t := by
    funext t
    simp [p, monicEval, Polynomial.eval_finsetSum, Finset.sum_range]
  have hdeg : p.natDegree = q := by
    have := Polynomial.natDegree_add_eq_left_of_degree_lt
      (p := (Polynomial.X : ℂ[X]) ^ q) (q := ∑ j : Fin q, Polynomial.C (a j x) * Polynomial.X ^ (j
        : ℕ))
      (by simpa using Polynomial.degree_sum_fin_lt (fun j : Fin q => a j x))
    simpa [p] using this
  have hnodup : p.roots.Nodup := by
    rw [Multiset.nodup_iff_count_le_one]
    intro t
    rw [Polynomial.count_roots]
    by_contra h
    push Not at h
    obtain ⟨h1, h2⟩ := (Polynomial.one_lt_rootMultiplicity_iff_isRoot hp0).1 h
    have ht : monicEval q a x t = 0 := by rw [heval]; exact h1
    apply hsimple t ht
    rw [heval, Polynomial.deriv]
    exact h2
  have hset : {t | monicEval q a x t = 0} = (p.roots.toFinset : Set ℂ) := by
    ext t
    simp [heval, Polynomial.mem_roots hp0]
  rw [hset]
  refine ⟨Finset.finite_toSet _, ?_⟩
  rw [ncard_coe_finset, Multiset.toFinset_card_of_nodup hnodup,
    IsAlgClosed.card_roots_eq_natDegree, hdeg]

namespace ParametrizationData

variable (P : ParametrizationData A)

/-- Roots of the `Q_k(x, ·)` are small for small `x`. -/
theorem exists_root_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ x : ComplexModel P.dim, ‖x‖ < η → ∀ k : Fin n, ∀ t : ℂ,
      monicEval (P.s k) (P.e k) x t = 0 → ‖t‖ < ε := by
  set ε' := min ε 1 with hε'
  have hε'0 : 0 < ε' := lt_min hε one_pos
  have hev : ∀ᶠ x in 𝓝 (0 : ComplexModel P.dim), ∀ k : Fin n, ∀ j : Fin (P.s k),
      ‖P.e k j x‖ * P.s k < ε' ^ P.s k := by
    refine Filter.eventually_all.2 fun k => Filter.eventually_all.2 fun j => ?_
    have hc : ContinuousAt (P.e k j) 0 :=
      ((P.differentiableOn_e k j).differentiableAt
        (isOpen_ball.mem_nhds (mem_ball_self P.rad_pos))).continuousAt
    refine (hc.norm.mul continuousAt_const).eventually_lt continuousAt_const ?_
    simp [P.e_zero k j j.2, pow_pos hε'0]
  obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨η, hη, fun x hx k t ht => ?_⟩
  have hx' := hball (by simpa using hx)
  refine lt_of_lt_of_le ?_ (min_le_left ε 1)
  exact HolomorphicCoefficientPolynomials.norm_lt_of_weierstrass_root hε'0 (min_le_right _ _)
    (fun j hj => hx' k ⟨j, hj⟩) ht

/-- Radii for which the polydisc lies in the ball and the roots of the `Q_k(x, ·)` over the
base disc lie in the fibre disc. -/
structure GoodRadii (r₁ r₂ : ℝ) : Prop where
  r₁_pos : 0 < r₁
  r₂_pos : 0 < r₂
  r₁_le : r₁ ≤ P.rad
  polydisc_subset : polydisc n P.dim r₁ r₂ ⊆ ball 0 P.rad
  root_lt : ∀ x : ComplexModel P.dim, ‖x‖ < r₁ → ∀ k : Fin n, ∀ t : ℂ,
    monicEval (P.s k) (P.e k) x t = 0 → ‖t‖ < r₂

theorem exists_goodRadii : ∃ r₁ r₂, P.GoodRadii r₁ r₂ := by
  set r₂ := P.rad / (n + 1) with hr₂
  have hr₂0 : 0 < r₂ := div_pos P.rad_pos (by positivity)
  obtain ⟨η, hη, hroot⟩ := P.exists_root_bound hr₂0
  have hr₂le : r₂ ≤ P.rad := div_le_self P.rad_pos.le (by linarith [(n.cast_nonneg : (0:ℝ) ≤ n)])
  refine ⟨min η r₂, r₂, ⟨lt_min hη hr₂0, hr₂0, (min_le_right _ _).trans hr₂le, ?_,
    fun x hx => hroot x (hx.trans_le (min_le_left _ _))⟩⟩
  refine (polydisc_mono (min_le_right _ _)).trans ((polydisc_subset_ball hr₂0).trans ?_)
  refine ball_subset_ball (le_of_eq ?_)
  rw [hr₂]
  field_simp

/-! ### The points over a root -/

/-- The point `(x, B(x, t) / δ(x))`. -/
def graphPoint (x : ComplexModel P.dim) (t : ℂ) : ComplexModel n :=
  WithLp.toLp 2 fun i =>
    if h : i.1 < P.dim then x ⟨i.1, h⟩ else lowEval P.deg (P.b i) x t / P.disc x

theorem graphPoint_apply_of_le (x : ComplexModel P.dim) (t : ℂ) {k : Fin n}
    (hk : P.dim ≤ k.1) : P.graphPoint x t k = lowEval P.deg (P.b k) x t / P.disc x := by
  simp [graphPoint, not_lt.mpr hk]

theorem coordinateProjection_graphPoint (x : ComplexModel P.dim) (t : ℂ) :
    coordinateProjection n P.dim (P.graphPoint x t) = x := by
  ext a
  have ha : a.1 < n := lt_of_lt_of_le a.2 P.dim_le
  simp [coordinateProjection_apply, graphPoint, ha]

theorem fibreForm_graphPoint {x : ComplexModel P.dim} (hx : x ∈ ball 0 P.rad)
    (hδ : P.disc x ≠ 0) {t : ℂ} (ht : monicEval P.deg P.w x t = 0) :
    fibreForm P.dim P.coef (P.graphPoint x t) = t := by
  have h := P.recover x hx t ht
  unfold fibreForm
  rw [coordinateProjection_graphPoint]
  have : ∀ k : Fin n, (if P.dim ≤ k.1 then P.coef k x * P.graphPoint x t k else 0) =
      (if P.dim ≤ k.1 then P.coef k x * lowEval P.deg (P.b k) x t else 0) / P.disc x := by
    intro k
    split_ifs with hk
    · rw [graphPoint_apply_of_le P x t hk, mul_div_assoc]
    · simp
  rw [Finset.sum_congr rfl fun k _ => this k, ← Finset.sum_div, h, mul_div_cancel_left₀ t hδ]

theorem eq_graphPoint {z : ComplexModel n} (hzA : z ∈ A) (hz : z ∈ ball 0 P.rad)
    (hδ : P.disc (coordinateProjection n P.dim z) ≠ 0) :
    z = P.graphPoint (coordinateProjection n P.dim z) (fibreForm P.dim P.coef z) := by
  ext i
  by_cases hi : i.1 < P.dim
  · simp [graphPoint, hi, coordinateProjection_apply]
  · rw [graphPoint_apply_of_le P _ _ (not_lt.mp hi),
      ← P.disc_mul_eq z hzA hz i (not_lt.mp hi), mul_div_cancel_left₀ _ hδ]

variable {P}

theorem GoodRadii.graphPoint_mem {r₁ r₂ : ℝ} (hR : P.GoodRadii r₁ r₂)
    {x : ComplexModel P.dim} (hx : ‖x‖ < r₁) (hδ : P.disc x ≠ 0) {t : ℂ}
    (ht : monicEval P.deg P.w x t = 0) :
    P.graphPoint x t ∈ A ∩ polydisc n P.dim r₁ r₂ := by
  have hxb : x ∈ ball (0 : ComplexModel P.dim) P.rad :=
    mem_ball_zero_iff.2 (hx.trans_le hR.r₁_le)
  have hpoly : P.graphPoint x t ∈ polydisc n P.dim r₁ r₂ := by
    refine ⟨by rwa [coordinateProjection_graphPoint], fun k hk => ?_⟩
    rw [graphPoint_apply_of_le P x t hk]
    exact hR.root_lt x hx k _ (P.subst x hxb hδ t ht k hk)
  refine ⟨P.complete _ (hR.polydisc_subset hpoly) ?_ ?_ ?_, hpoly⟩
  · rwa [coordinateProjection_graphPoint]
  · rwa [coordinateProjection_graphPoint, fibreForm_graphPoint P hxb hδ ht]
  · intro k hk
    rw [coordinateProjection_graphPoint, fibreForm_graphPoint P hxb hδ ht,
      graphPoint_apply_of_le P x t hk, mul_div_cancel₀ _ hδ]

/-- The fibre of `A ∩ Δ` over a point off the discriminant locus is the image of the roots
of `W(x, ·)`. -/
theorem GoodRadii.fibre_eq {r₁ r₂ : ℝ} (hR : P.GoodRadii r₁ r₂)
    {x : ComplexModel P.dim} (hx : ‖x‖ < r₁) (hδ : P.disc x ≠ 0) :
    A ∩ polydisc n P.dim r₁ r₂ ∩ coordinateProjection n P.dim ⁻¹' {x} =
      P.graphPoint x '' {t | monicEval P.deg P.w x t = 0} := by
  have hxb : x ∈ ball (0 : ComplexModel P.dim) P.rad :=
    mem_ball_zero_iff.2 (hx.trans_le hR.r₁_le)
  ext z
  constructor
  · rintro ⟨⟨hzA, hzΔ⟩, hzx⟩
    rw [mem_preimage, mem_singleton_iff] at hzx
    have hzb := hR.polydisc_subset hzΔ
    refine ⟨fibreForm P.dim P.coef z, ?_, ?_⟩
    · have := P.w_eq_zero z hzA hzb
      rwa [hzx] at this
    · have := P.eq_graphPoint hzA hzb (by rwa [hzx])
      rw [hzx] at this
      exact this.symm
  · rintro ⟨t, ht, rfl⟩
    exact ⟨hR.graphPoint_mem hx hδ ht, by simp [coordinateProjection_graphPoint]⟩

theorem GoodRadii.injOn_graphPoint {r₁ r₂ : ℝ} (hR : P.GoodRadii r₁ r₂)
    {x : ComplexModel P.dim} (hx : ‖x‖ < r₁) (hδ : P.disc x ≠ 0) :
    InjOn (P.graphPoint x) {t | monicEval P.deg P.w x t = 0} := by
  have hxb : x ∈ ball (0 : ComplexModel P.dim) P.rad :=
    mem_ball_zero_iff.2 (hx.trans_le hR.r₁_le)
  intro t ht t' ht' h
  rw [← fibreForm_graphPoint P hxb hδ ht, h, fibreForm_graphPoint P hxb hδ ht']

theorem GoodRadii.finite_fibre {r₁ r₂ : ℝ} (hR : P.GoodRadii r₁ r₂)
    {x : ComplexModel P.dim} (hx : ‖x‖ < r₁) (hδ : P.disc x ≠ 0) :
    (A ∩ polydisc n P.dim r₁ r₂ ∩ coordinateProjection n P.dim ⁻¹' {x}).Finite ∧
      (A ∩ polydisc n P.dim r₁ r₂ ∩ coordinateProjection n P.dim ⁻¹' {x}).ncard = P.deg := by
  have hxb : x ∈ ball (0 : ComplexModel P.dim) P.rad :=
    mem_ball_zero_iff.2 (hx.trans_le hR.r₁_le)
  obtain ⟨hfin, hcard⟩ := ncard_setOf_monicEval_eq_zero P.deg P.w x (P.simple x hxb hδ)
  rw [hR.fibre_eq hx hδ]
  exact ⟨hfin.image _, by rw [(hR.injOn_graphPoint hx hδ).ncard_image, hcard]⟩

theorem continuousOn_fibreForm (P : ParametrizationData A) :
    ContinuousOn (fibreForm P.dim P.coef) (coordinateProjection n P.dim ⁻¹' ball 0 P.rad) := by
  unfold fibreForm
  refine continuousOn_finsetSum _ fun k _ => ?_
  by_cases hk : P.dim ≤ k.1
  · simp only [hk, ite_true]
    exact ((P.differentiableOn_coef k).continuousOn.comp
      (coordinateProjection n P.dim).continuous.continuousOn fun z hz => hz).mul
      (EuclideanSpace.proj (𝕜 := ℂ) k).continuous.continuousOn
  · simp only [hk, ite_false]
    exact continuousOn_const

/-- **Local graph.**  Near a point of `A ∩ Δ` off the discriminant locus, `A` is the graph of
`x ↦ (x, B(x, ω(x)) / δ(x))`, `ω` the holomorphic simple root of `W(x, ·)` given by the
implicit function theorem. -/
theorem GoodRadii.localGraph {r₁ r₂ : ℝ} (hR : P.GoodRadii r₁ r₂) {y : ComplexModel n}
    (hy : y ∈ A ∩ polydisc n P.dim r₁ r₂) (hδ : P.disc (coordinateProjection n P.dim y) ≠ 0) :
    ∃ (U : Set (ComplexModel P.dim)) (V : Set (ComplexModel n))
      (g : ComplexModel P.dim → ComplexModel n),
      IsOpen U ∧ IsOpen V ∧ coordinateProjection n P.dim y ∈ U ∧ y ∈ V ∧
      V ⊆ polydisc n P.dim r₁ r₂ ∧ U ⊆ {x | ‖x‖ < r₁ ∧ P.disc x ≠ 0} ∧
      DifferentiableOn ℂ g U ∧ (∀ x ∈ U, coordinateProjection n P.dim (g x) = x) ∧
      (∀ x ∈ U, g x ∈ A ∩ polydisc n P.dim r₁ r₂) ∧
      ∀ z ∈ V, z ∈ A →
        coordinateProjection n P.dim z ∈ U ∧ g (coordinateProjection n P.dim z) = z := by
  set x₀ := coordinateProjection n P.dim y with hx₀
  set t₀ := fibreForm P.dim P.coef y with ht₀
  have hyb := hR.polydisc_subset hy.2
  have hx₀b : x₀ ∈ ball (0 : ComplexModel P.dim) P.rad :=
    mem_ball_zero_iff.2 (hy.2.1.trans_le hR.r₁_le)
  have hW0 : monicEval P.deg P.w x₀ t₀ = 0 := P.w_eq_zero y hy.1 hyb
  set f : ComplexModel P.dim × ℂ → ℂ := fun p => monicEval P.deg P.w p.1 p.2 with hf
  have hopen : IsOpen (ball (0 : ComplexModel P.dim) P.rad ×ˢ (univ : Set ℂ)) :=
    isOpen_ball.prod isOpen_univ
  have hfd : DifferentiableOn ℂ f (ball 0 P.rad ×ˢ univ) := by
    have h1 : DifferentiableOn ℂ (fun p : ComplexModel P.dim × ℂ => p.2 ^ P.deg)
        (ball 0 P.rad ×ˢ univ) := (differentiable_snd.pow _).differentiableOn
    have h2 : ∀ j ∈ Finset.range P.deg,
        DifferentiableOn ℂ (fun p : ComplexModel P.dim × ℂ => P.w j p.1 * p.2 ^ j)
          (ball 0 P.rad ×ˢ univ) := fun j _ =>
      ((P.differentiableOn_w j).comp (s := ball 0 P.rad ×ˢ univ)
        differentiableOn_fst fun p hp => hp.1).mul
        (differentiable_snd.pow _).differentiableOn
    exact h1.add (DifferentiableOn.fun_sum h2)
  have hu : ((x₀, t₀) : ComplexModel P.dim × ℂ) ∈ ball 0 P.rad ×ˢ univ := ⟨hx₀b, mem_univ _⟩
  have hcd : ContDiffAt ℂ 1 f (x₀, t₀) :=
    (contDiffAt_of_differentiableOn_complex hfd hopen hu).of_le (by exact_mod_cast le_top)
  have hfda : DifferentiableAt ℂ f (x₀, t₀) := hfd.differentiableAt (hopen.mem_nhds hu)
  set L := (fderiv ℂ f (x₀, t₀)).comp (ContinuousLinearMap.inr ℂ (ComplexModel P.dim) ℂ)
    with hL
  have hcomp : HasFDerivAt (fun t => f (x₀, t)) L t₀ :=
    hfda.hasFDerivAt.comp t₀ (hasFDerivAt_prodMk_right x₀ t₀)
  have hL1 : L 1 ≠ 0 := by
    have h := hcomp.hasDerivAt.deriv
    have hne : deriv (monicEval P.deg P.w x₀) t₀ ≠ 0 := P.simple x₀ hx₀b hδ t₀ hW0
    rw [← h]
    exact hne
  have hinv : L.IsInvertible := by
    refine ContinuousLinearMap.IsInvertible.of_inverse
      (g := (L 1)⁻¹ • ContinuousLinearMap.id ℂ ℂ) ?_ ?_
    · ext
      simp [hL1]
    · ext
      simp [hL1]
  have pn : (1 : WithTop ℕ∞) ≠ 0 := one_ne_zero
  set ψ := hcd.implicitFunction pn hinv with hψ
  have hψ0 : ψ x₀ = t₀ := hcd.implicitFunction_apply_self pn hinv
  have hiff := hcd.eventually_apply_eq_iff_implicitFunction pn hinv
  obtain ⟨U₁, D, hU₁, hx₀U₁, hD, ht₀D, hsub⟩ := mem_nhds_prod_iff'.1 hiff
  have hψcd := hcd.contDiffAt_implicitFunction pn hinv
  have hS : {x | x ∈ U₁ ∧ (‖x‖ < r₁ ∧ P.disc x ≠ 0) ∧ ψ x ∈ D ∧ DifferentiableAt ℂ ψ x}
      ∈ 𝓝 x₀ := by
    filter_upwards [hU₁.mem_nhds hx₀U₁,
      (isOpen_lt continuous_norm continuous_const).mem_nhds hy.2.1,
      (P.differentiableOn_disc.differentiableAt
        (isOpen_ball.mem_nhds hx₀b)).continuousAt.eventually_ne hδ,
      hψcd.continuousAt.preimage_mem_nhds (hD.mem_nhds (show ψ x₀ ∈ D by rw [hψ0]; exact ht₀D)),
      hψcd.eventually (by simp)] with x h1 h2 h3 h4 h5
    exact ⟨h1, ⟨h2, h3⟩, h4, h5.differentiableAt one_ne_zero⟩
  set S := {x | x ∈ U₁ ∧ (‖x‖ < r₁ ∧ P.disc x ≠ 0) ∧ ψ x ∈ D ∧ DifferentiableAt ℂ ψ x}
    with hSdef
  have hSball : ∀ x ∈ S, x ∈ ball (0 : ComplexModel P.dim) P.rad := fun x hx =>
    mem_ball_zero_iff.2 (hx.2.1.1.trans_le hR.r₁_le)
  have hSroot : ∀ x ∈ S, monicEval P.deg P.w x (ψ x) = 0 := by
    intro x hx
    have := (hsub (show (x, ψ x) ∈ U₁ ×ˢ D from ⟨hx.1, hx.2.2.1⟩)).2 rfl
    exact this.trans hW0
  set g : ComplexModel P.dim → ComplexModel n := fun x => P.graphPoint x (ψ x) with hg
  have hgd : ∀ x ∈ S, DifferentiableAt ℂ g x := by
    intro x hx
    have hbn : ball (0 : ComplexModel P.dim) P.rad ∈ 𝓝 x := isOpen_ball.mem_nhds (hSball x hx)
    have hc : DifferentiableAt ℂ (fun x (i : Fin n) =>
        if h : i.1 < P.dim then x ⟨i.1, h⟩ else lowEval P.deg (P.b i) x (ψ x) / P.disc x) x := by
      refine differentiableAt_pi.2 fun i => ?_
      by_cases hi : i.1 < P.dim
      · simp only [hi, dite_eq_left]
        exact (EuclideanSpace.proj (𝕜 := ℂ) (⟨i.1, hi⟩ : Fin P.dim)).differentiableAt
      · simp only [hi, dite_eq_right, not_false_eq_true]
        simp only [div_eq_mul_inv]
        refine DifferentiableAt.mul ?_
          ((P.differentiableOn_disc.differentiableAt hbn).inv hx.2.1.2)
        unfold lowEval
        exact DifferentiableAt.fun_sum fun j _ =>
          ((P.differentiableOn_b i j).differentiableAt hbn).mul (hx.2.2.2.pow j)
    exact (EuclideanSpace.equiv (Fin n) ℂ).symm.differentiable.differentiableAt.comp x hc
  set U := interior S with hU
  have hUS : U ⊆ S := interior_subset
  set V := polydisc n P.dim r₁ r₂ ∩ coordinateProjection n P.dim ⁻¹' U ∩
    fibreForm P.dim P.coef ⁻¹' D with hV
  refine ⟨U, V, g, isOpen_interior, ?_, mem_interior_iff_mem_nhds.2 hS, ?_,
    fun z hz => hz.1.1, fun x hx => (hUS hx).2.1, ?_, ?_, ?_, ?_⟩
  · refine (P.continuousOn_fibreForm.mono fun z hz => ?_).isOpen_inter_preimage
      ((isOpen_polydisc n P.dim r₁ r₂).inter
        (isOpen_interior.preimage (coordinateProjection n P.dim).continuous)) hD
    exact mem_ball_zero_iff.2 (hz.1.1.trans_le hR.r₁_le)
  · exact ⟨⟨hy.2, mem_interior_iff_mem_nhds.2 hS⟩, ht₀D⟩
  · exact fun x hx => (hgd x (hUS hx)).differentiableWithinAt
  · exact fun x _ => P.coordinateProjection_graphPoint x (ψ x)
  · exact fun x hx => hR.graphPoint_mem (hUS hx).2.1.1 (hUS hx).2.1.2 (hSroot x (hUS hx))
  · intro z hz hzA
    have hzU : coordinateProjection n P.dim z ∈ U := hz.1.2
    have hzS := hUS hzU
    have hzb := hR.polydisc_subset hz.1.1
    refine ⟨hzU, ?_⟩
    have hWz : monicEval P.deg P.w (coordinateProjection n P.dim z) (fibreForm P.dim P.coef z)
      = 0 :=
      P.w_eq_zero z hzA hzb
    have hψz : ψ (coordinateProjection n P.dim z) = fibreForm P.dim P.coef z :=
      (hsub (show (coordinateProjection n P.dim z, fibreForm P.dim P.coef z) ∈ U₁ ×ˢ D
        from ⟨hzS.1, hz.2⟩)).1 (hWz.trans hW0.symm)
    change P.graphPoint _ (ψ _) = z
    rw [hψz]
    exact (P.eq_graphPoint hzA hzb hzS.2.1.2).symm

end ParametrizationData

/-! ### Regularity and openness from local graphs -/

/-- A set which near `y` is the graph of a holomorphic map over the first `d` coordinates is
regular of dimension `d` at `y`. -/
theorem regularAtDim_of_isLocalGraph {S : Set (ComplexModel n)} {d : ℕ} (hd : d ≤ n)
    {y : ComplexModel n} (hyS : y ∈ S) {U : Set (ComplexModel d)} {V : Set (ComplexModel n)}
    {g : ComplexModel d → ComplexModel n} (hU : IsOpen U) (hV : IsOpen V)
    (hyV : y ∈ V) (hg : DifferentiableOn ℂ g U)
    (hπg : ∀ x ∈ U, coordinateProjection n d (g x) = x) (hgS : ∀ x ∈ U, g x ∈ S)
    (hSV : ∀ z ∈ V, z ∈ S →
      coordinateProjection n d z ∈ U ∧ g (coordinateProjection n d z) = z) :
    RegularAtDim (n := n) (M := ComplexModel n) S y d := by
  have hπι : ∀ x, coordinateProjection n d (coordinateInclusion n d x) = x :=
    coordinateProjection_coordinateInclusion hd
  let h : ComplexModel d → ComplexModel n := fun x => g x - coordinateInclusion n d x
  have hπh : ∀ x ∈ U, coordinateProjection n d (h x) = 0 := fun x hx => by
    simp [h, map_sub, hπg x hx, hπι]
  have hhd : DifferentiableOn ℂ h U :=
    hg.sub (coordinateInclusion n d).differentiable.differentiableOn
  obtain ⟨hyU, hgy⟩ := hSV y hyV hyS
  let c : ComplexModel n := coordinateInclusion n d (coordinateProjection n d y)
  let F : ComplexModel n → ComplexModel n := fun z => z - h (coordinateProjection n d z) - c
  let G : ComplexModel n → ComplexModel n := fun w =>
    w + h (coordinateProjection n d w + coordinateProjection n d y) + c
  have hπF : ∀ z, coordinateProjection n d z ∈ U →
      coordinateProjection n d (F z) + coordinateProjection n d y = coordinateProjection n d z :=
    fun z hz => by simp [F, map_sub, hπh _ hz, c, hπι]
  have hπG : ∀ w, coordinateProjection n d w + coordinateProjection n d y ∈ U →
      coordinateProjection n d (G w) = coordinateProjection n d w + coordinateProjection n d y :=
    fun w hw => by simp [G, map_add, hπh _ hw, c, hπι]
  have hGF : ∀ z, coordinateProjection n d z ∈ U → G (F z) = z := fun z hz => by
    simp only [G, hπF z hz]
    simp only [F]
    abel
  have hFG : ∀ w, coordinateProjection n d w + coordinateProjection n d y ∈ U → F (G w) = w :=
    fun w hw => by
      simp only [F, hπG w hw]
      simp only [G]
      abel
  have hpre : IsOpen {w : ComplexModel n |
      coordinateProjection n d w + coordinateProjection n d y ∈ U} :=
    hU.preimage ((coordinateProjection n d).continuous.add continuous_const)
  have hGd : DifferentiableOn ℂ G {w | coordinateProjection n d w + coordinateProjection n d y ∈
    U} :=
    (differentiableOn_id.add (hhd.comp
      ((coordinateProjection n d).differentiable.add_const _).differentiableOn
      fun w hw => hw)).add_const c
  let Φ : LocalHolomorphicEquivAt (n := n) y :=
    { source := V ∩ coordinateProjection n d ⁻¹' U
      target := {w | coordinateProjection n d w + coordinateProjection n d y ∈ U} ∩ G ⁻¹' V
      isOpen_source := hV.inter (hU.preimage (coordinateProjection n d).continuous)
      isOpen_target := hGd.continuousOn.isOpen_inter_preimage hpre hV
      center_mem_source := ⟨hyV, hyU⟩
      toFun := F
      invFun := G
      toFun_holomorphic := (differentiableOn_id.sub
        (hhd.comp (s := V ∩ coordinateProjection n d ⁻¹' U)
          (coordinateProjection n d).differentiable.differentiableOn fun z hz => hz.2)).sub_const c
      invFun_holomorphic := hGd.mono inter_subset_left
      mapsTo_toFun := fun z hz => ⟨by
          change _ ∈ U
          rw [hπF z hz.2]
          exact hz.2, by
          change G (F z) ∈ V
          rw [hGF z hz.2]
          exact hz.1⟩
      mapsTo_invFun := fun w hw => ⟨hw.2, by
          change coordinateProjection n d (G w) ∈ U
          rw [hπG w hw.1]
          exact hw.1⟩
      left_inv := fun z hz => hGF z hz.2
      right_inv := fun w hw => hFG w hw.1 }
  refine ⟨hd, hyS, Φ, subset_univ _, ?_, ?_⟩
  · change y - h (coordinateProjection n d y) - c = 0
    simp only [h, c, hgy]
    abel
  · intro z _ hz
    change z ∈ V ∩ coordinateProjection n d ⁻¹' U at hz
    change z ∈ S ↔ F z ∈ complexCoordinatePlane n d
    constructor
    · intro hzS i hi
      obtain ⟨-, hgz⟩ := hSV z hz.1 hzS
      simp [F, h, c, hgz, coordinateInclusion_apply, not_lt.mpr hi]
    · intro hF
      have hgz : g (coordinateProjection n d z) = z := by
        ext i
        by_cases hi : i.1 < d
        · have := congrArg (fun w => w ⟨i.1, hi⟩) (hπg _ hz.2)
          simpa [coordinateProjection_apply, i.2] using this
        · have hz : z i - g (coordinateProjection n d z) i = 0 := by
            simpa [F, h, c, coordinateInclusion_apply, hi] using hF i (not_lt.mp hi)
          exact (sub_eq_zero.mp hz).symm
      rw [← hgz]
      exact hgS _ hz.2

theorem nonempty_setsData (P : ParametrizationData A) : Nonempty (SetsData P) := by
  obtain ⟨r₁, r₂, hR⟩ := P.exists_goodRadii
  refine ⟨{
    r₁ := r₁
    r₂ := r₂
    r₁_pos := hR.r₁_pos
    r₂_pos := hR.r₂_pos
    polydisc_subset := hR.polydisc_subset
    small := ?_
    finite_fibre := fun x hx hδ => (hR.finite_fibre hx hδ).1
    ncard_fibre := fun x hx hδ => (hR.finite_fibre hx hδ).2
    local_graph := fun y hy hδ => hR.localGraph hy hδ
    regular := ?_
    isOpen_image := ?_ }⟩
  · intro ε hε
    obtain ⟨η, hη, h⟩ := P.exists_root_bound hε
    exact ⟨η, hη, fun z hz hzη k hk =>
      h _ hzη k _ (P.e_eq_zero z hz.1 (hR.polydisc_subset hz.2) k hk)⟩
  · intro y hy hδ
    obtain ⟨U, V, g, hU, hV, -, hyV, -, -, hg, hπg, hgA, hVA⟩ := hR.localGraph hy hδ
    exact regularAtDim_of_isLocalGraph P.dim_le hy hU hV hyV hg hπg hgA
      fun z hz hzS => hVA z hz hzS.1
  · intro O hO
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨y, ⟨hyO, hy, hδ⟩, rfl⟩
    obtain ⟨U, V, g, hU, hV, hyU, hyV, -, hUsub, hg, hπg, hgA, hVA⟩ := hR.localGraph hy hδ
    have hgy : g (coordinateProjection n P.dim y) = y := (hVA y hyV hy.1).2
    refine Filter.mem_of_superset ((hg.continuousOn.isOpen_inter_preimage hU
      (hO.inter hV)).mem_nhds ⟨hyU, by rw [mem_preimage, hgy]; exact ⟨hyO, hyV⟩⟩) ?_
    rintro x ⟨hxU, hxO, -⟩
    exact ⟨g x, ⟨hxO, hgA x hxU, by
      simpa [mem_preimage, hπg x hxU] using (hUsub hxU).2⟩, hπg x hxU⟩

end

end SGPT.Foundations.Analysis.Pending.GermParametrizationData
