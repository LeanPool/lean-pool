/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Probability.Transport
public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Subgradient.Image
public import LeanPool.KLS.FunctionalInequalities.Analysis.MetricCover
public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Extension
public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Quadratic
public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Alexandrov.Transport
public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Alexandrov.MaximumPrinciple

/-! # Affine subgradient-image volumes, Alexandrov identities and domain boundary bounds

Supports the domain Monge--Ampere infrastructure for Letwin
arXiv:2607.24164v1 Lemma 2.2 through BB arXiv:1207.6128v1
Theorem 2.24(ii).
-/

@[expose] public section

section
open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal

section QuadraticSubgradientImage

open MeasureTheory Set Matrix
open scoped RealInnerProductSpace ENNReal

/-! Subgradient images of quadratic functions. -/

namespace FunctionalInequalities.Analysis

private lemma quadraticAt_inner_symm {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (x y : EuclideanSpace ℝ (Fin n)) :
    ⟪x, Matrix.toEuclideanLin A y⟫ = ⟪Matrix.toEuclideanLin A x, y⟫ := by
  let T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    Matrix.toEuclideanLin A
  have hT : LinearMap.adjoint T = T := by
    calc
      LinearMap.adjoint T = Matrix.toEuclideanLin Aᴴ := by
        symm
        exact Matrix.toEuclideanLin_conjTranspose_eq_adjoint A
      _ = T := by
        rw [hA.eq]
  change ⟪x, T y⟫ = ⟪T x, y⟫
  simpa [hT] using LinearMap.adjoint_inner_right T x y

private lemma quadraticAt_nonneg {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (x : EuclideanSpace ℝ (Fin n)) :
    0 ≤ ⟪x, Matrix.toEuclideanLin A x⟫ := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change 0 ≤ (A *ᵥ x.ofLp) ⬝ᵥ star x.ofLp
  simpa [dotProduct_comm] using
    (posSemidef_iff_dotProduct_mulVec.mp hA).2 x.ofLp

private lemma quadraticAt_quadratic_expand {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (x₀ b : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (x v : EuclideanSpace ℝ (Fin n)) :
    quadraticAt A x₀ b c (x + v) =
      quadraticAt A x₀ b c x +
        ⟪b + Matrix.toEuclideanLin A (x - x₀), v⟫ +
          (1 / 2) * ⟪v, Matrix.toEuclideanLin A v⟫ := by
  let T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    Matrix.toEuclideanLin A
  have hq (z w : EuclideanSpace ℝ (Fin n)) :
      ⟪z + w, T (z + w)⟫ =
        ⟪z, T z⟫ + 2 * ⟪T z, w⟫ + ⟪w, T w⟫ := by
    simp only [map_add, inner_add_left, inner_add_right]
    rw [quadraticAt_inner_symm hA z w, real_inner_comm w (T z)]
    ring
  have harg : x + v - x₀ = (x - x₀) + v := by
    abel
  dsimp [quadraticAt]
  dsimp [T] at hq ⊢
  rw [harg, hq]
  have hlin :
      ⟪b + Matrix.toEuclideanLin A (x - x₀), v⟫ =
        ⟪b, v⟫ + ⟪Matrix.toEuclideanLin A (x - x₀), v⟫ := by
    rw [inner_add_left]
  rw [hlin, inner_add_right]
  ring

private lemma quadraticAt_subgradient_iff {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (x₀ b : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (x p : EuclideanSpace ℝ (Fin n)) :
    (∀ y, quadraticAt A x₀ b c x + ⟪p, y - x⟫ ≤ quadraticAt A x₀ b c y) ↔
      p = b + Matrix.toEuclideanLin A (x - x₀) := by
  let T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    Matrix.toEuclideanLin A
  let g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun z => b + T (z - x₀)
  constructor
  · intro hp
    have hineq (w : EuclideanSpace ℝ (Fin n)) :
        ⟪p - g x, w⟫ ≤ (1 / 2) * ⟪w, T w⟫ := by
      have h₁ := hp (x + w)
      have h₂ := quadraticAt_quadratic_expand hA.1 x₀ b c x w
      have h₁' :
          quadraticAt A x₀ b c x + ⟪p, w⟫ ≤ quadraticAt A x₀ b c (x + w) := by
        simpa only [add_sub_cancel_left] using h₁
      have h₃ : ⟪p, w⟫ = ⟪g x, w⟫ + ⟪p - g x, w⟫ := by
        rw [← inner_add_left]
        congr 1
        abel
      rw [h₂, h₃] at h₁'
      linarith
    have hv : p - g x = 0 := by
      by_contra hv
      let r : ℝ := ⟪p - g x, p - g x⟫
      let q : ℝ := ⟪p - g x, T (p - g x)⟫
      have hr : 0 < r := by
        dsimp [r]
        rw [real_inner_self_eq_norm_sq]
        exact sq_pos_of_pos (norm_pos_iff.mpr hv)
      have hq : 0 ≤ q := by
        dsimp [q]
        exact quadraticAt_nonneg hA _
      let t : ℝ := r / (q + 1)
      have ht : 0 < t := by
        dsimp [t]
        positivity
      have hs : ⟪p - g x, t • (p - g x)⟫ = t * r := by
        calc
          ⟪p - g x, t • (p - g x)⟫ =
              t * ⟪p - g x, p - g x⟫ := by
                rw [real_inner_smul_right]
          _ = t * r := by rfl
      have hsmul (z : EuclideanSpace ℝ (Fin n)) (s : ℝ) :
          ⟪s • z, T (s • z)⟫ = s ^ 2 * ⟪z, T z⟫ := by
        rw [map_smul]
        simp only [real_inner_smul_left, real_inner_smul_right]
        ring
      have hqs :
          ⟪t • (p - g x), T (t • (p - g x))⟫ =
            t ^ 2 * q := by
        rw [hsmul]
      have hi := hineq (t • (p - g x))
      rw [hs, hqs] at hi
      have htq : t * (q + 1) = r := by
        dsimp [t]
        exact div_mul_cancel₀ r (by positivity)
      nlinarith [sq_pos_of_pos ht, hr, hq, htq]
    exact sub_eq_zero.mp hv
  · intro hp y
    have hinc := quadraticAt_quadratic_expand hA.1 x₀ b c x (y - x)
    have harg : x + (y - x) = y := by
      abel
    rw [harg] at hinc
    rw [hp]
    nlinarith [quadraticAt_nonneg hA (y - x)]

private lemma quadraticAt_mix_identity {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (x₀ b : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) (a r : ℝ) (har : a + r = 1) :
    quadraticAt A x₀ b c (a • x + r • y) =
      a * quadraticAt A x₀ b c x + r * quadraticAt A x₀ b c y -
        (1 / 2) * (a * r) *
          ⟪x - y, Matrix.toEuclideanLin A (x - y)⟫ := by
  let T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    Matrix.toEuclideanLin A
  have hr : r = 1 - a := by
    linarith
  have hcross (u v : EuclideanSpace ℝ (Fin n)) :
      ⟪v, T u⟫ = ⟪u, T v⟫ := by
    calc
      ⟪v, T u⟫ = ⟪T u, v⟫ := real_inner_comm _ _
      _ = ⟪u, T v⟫ := (quadraticAt_inner_symm hA.1 u v).symm
  have hquad (u v : EuclideanSpace ℝ (Fin n)) :
      ⟪a • u + r • v, T (a • u + r • v)⟫ =
        a * ⟪u, T u⟫ + r * ⟪v, T v⟫ -
          a * r * ⟪u - v, T (u - v)⟫ := by
    rw [hr]
    simp only [map_add, map_smul, map_sub, inner_add_left, inner_add_right,
      inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
    rw [hcross u v]
    ring
  have harg :
      a • x + r • y - x₀ = a • (x - x₀) + r • (y - x₀) := by
    calc
      a • x + r • y - x₀ =
          a • x + r • y - (a + r) • x₀ := by
            rw [har, one_smul]
      _ = a • (x - x₀) + r • (y - x₀) := by
        module
  have hdiff : (x - x₀) - (y - x₀) = x - y := by
    abel
  dsimp [quadraticAt]
  dsimp [T] at hquad ⊢
  rw [harg, hquad, hdiff]
  have hlin :
      ⟪b, a • (x - x₀) + r • (y - x₀)⟫ =
        a * ⟪b, x - x₀⟫ + r * ⟪b, y - x₀⟫ := by
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  rw [hlin, hr]
  ring

/-- A quadratic with positive semidefinite Hessian is convex. -/
theorem convexOn_quadraticAt {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef)
    (x₀ b : EuclideanSpace ℝ (Fin n)) (c : ℝ) : ConvexOn ℝ univ (quadraticAt A x₀ b c) := by
  refine ⟨convex_univ, ?_⟩
  intro x _hx y _hy a r ha hr har
  change quadraticAt A x₀ b c (a • x + r • y) ≤
    a * quadraticAt A x₀ b c x + r * quadraticAt A x₀ b c y
  rw [quadraticAt_mix_identity hA x₀ b c x y a r har]
  have hcoeff : 0 ≤ (1 / 2 : ℝ) * (a * r) := by
    positivity
  have hq :
      0 ≤ ⟪x - y, Matrix.toEuclideanLin A (x - y)⟫ :=
    quadraticAt_nonneg hA (x - y)
  have hprod :
      0 ≤ (1 / 2 : ℝ) * (a * r) *
        ⟪x - y, Matrix.toEuclideanLin A (x - y)⟫ :=
    mul_nonneg hcoeff hq
  nlinarith

/-- A quadratic with positive definite Hessian is strictly convex, including
zero-dimensional spaces. -/
theorem strictConvexOn_quadraticAt {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) (x₀ b : EuclideanSpace ℝ (Fin n)) (c : ℝ) :
    StrictConvexOn ℝ univ (quadraticAt A x₀ b c) := by
  refine ⟨convex_univ, ?_⟩
  intro x _hx y _hy hxy a r ha hr har
  change quadraticAt A x₀ b c (a • x + r • y) <
    a * quadraticAt A x₀ b c x + r * quadraticAt A x₀ b c y
  rw [quadraticAt_mix_identity hA.posSemidef x₀ b c x y a r har]
  have hne : (x - y).ofLp ≠ 0 := by
    intro he
    apply hxy
    have hzero : x - y = 0 := by
      apply PiLp.ext
      intro i
      exact congrFun he i
    exact sub_eq_zero.mp hzero
  have hq : 0 < ⟪x - y, Matrix.toEuclideanLin A (x - y)⟫ := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    change 0 < (A *ᵥ (x - y).ofLp) ⬝ᵥ star (x - y).ofLp
    simpa [dotProduct_comm] using hA.dotProduct_mulVec_pos hne
  have hprod : 0 < (1 / 2 : ℝ) * (a * r) *
      ⟪x - y, Matrix.toEuclideanLin A (x - y)⟫ := by positivity
  linarith

private lemma volume_subgradientImage_quadraticAt_aux
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (x₀ b : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    {G : Set (EuclideanSpace ℝ (Fin n))} :
    (volume : Measure (EuclideanSpace ℝ (Fin n)))
        (subgradientImage (quadraticAt A x₀ b c) G) =
      ENNReal.ofReal A.det *
        (volume : Measure (EuclideanSpace ℝ (Fin n))) G := by
  let E := EuclideanSpace ℝ (Fin n)
  let T : E →ₗ[ℝ] E := Matrix.toEuclideanLin A
  let g : E → E := fun x => b + T (x - x₀)
  have himage :
      subgradientImage (quadraticAt A x₀ b c) G = g '' G := by
    ext p
    constructor
    · rintro ⟨x, hx, hp⟩
      refine ⟨x, hx, ?_⟩
      have heq :=
        (quadraticAt_subgradient_iff hA.posSemidef x₀ b c x p).mp hp
      simpa [g] using heq.symm
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x, hx, ?_⟩
      apply (quadraticAt_subgradient_iff hA.posSemidef x₀ b c x (g x)).mpr
      rfl
  let d : E := b - T x₀
  have hg (x : E) : g x = d + T x := by
    dsimp [g, d]
    rw [map_sub]
    abel
  have haffine :
      g '' G = (fun z : E => d + z) '' (T '' G) := by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨T x, ⟨x, hx, rfl⟩, ?_⟩
      exact (hg x).symm
    · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, hg x⟩
  have htrans :
      (volume : Measure E) ((fun z : E => d + z) '' (T '' G)) =
        (volume : Measure E) (T '' G) := by
    rw [image_add_left]
    exact measure_preimage_add volume (-d) (T '' G)
  have hdet : LinearMap.det T = A.det := by
    change LinearMap.det (Matrix.toLpLin 2 2 A) = A.det
    rw [Matrix.toLpLin_eq_toLin]
    exact LinearMap.det_toLin (PiLp.basisFun 2 ℝ (Fin n)) A
  have hdetpos : 0 < A.det := Matrix.PosDef.det_pos hA
  calc
    (volume : Measure E) (subgradientImage (quadraticAt A x₀ b c) G) =
        (volume : Measure E) (g '' G) := by rw [himage]
    _ = (volume : Measure E) ((fun z : E => d + z) '' (T '' G)) := by
      rw [haffine]
    _ = (volume : Measure E) (T '' G) := htrans
    _ = ENNReal.ofReal |LinearMap.det T| * (volume : Measure E) G :=
      Measure.addHaar_image_linearMap volume T G
    _ = ENNReal.ofReal A.det * (volume : Measure E) G := by
      rw [hdet, abs_of_pos hdetpos]

/-- **Subgradient images of a positive definite quadratic are exact affine images, with volume
`det A · vol G`**. -/
theorem volume_subgradientImage_quadraticAt {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (x₀ b : EuclideanSpace ℝ (Fin n)) (c : ℝ) {G : Set (EuclideanSpace ℝ (Fin n))}
    (hG : MeasurableSet G) :
    (volume : Measure (EuclideanSpace ℝ (Fin n))) (subgradientImage (quadraticAt A x₀ b c) G) =
      ENNReal.ofReal A.det * (volume : Measure (EuclideanSpace ℝ (Fin n))) G := by
  have _hG : MeasurableSet G := hG
  exact volume_subgradientImage_quadraticAt_aux hA x₀ b c

/-- The actual DOMAIN support image of a positive definite quadratic has its
exact determinant mass on EVERY subset of an open domain. No measurability,
finite-volume, domain-convexity or source image-agreement premise is needed. -/
theorem volume_subgradientImageOn_quadraticAt {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) (x₀ b : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    {Ω G : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω) (hGΩ : G ⊆ Ω) :
    (volume : Measure (EuclideanSpace ℝ (Fin n)))
        (subgradientImageOn (quadraticAt A x₀ b c) Ω G) =
      ENNReal.ofReal A.det * (volume : Measure (EuclideanSpace ℝ (Fin n))) G := by
  rw [subgradientImageOn_eq_subgradientImage_of_isOpen
      (convexOn_quadraticAt hA.posSemidef _ _ _) hΩ hGΩ]
  exact volume_subgradientImage_quadraticAt_aux hA x₀ b c

end FunctionalInequalities.Analysis

end QuadraticSubgradientImage

section InfdistLeWidth

open Set Metric
open scoped RealInnerProductSpace

/-! Distance to the frontier is bounded by the directional width (Caffarelli's argument). -/

namespace FunctionalInequalities.Analysis

/-- **Distance to the frontier is at most the width in any direction** (Caffarelli's argument): for
a bounded open `S`, a point `x ∈ S` and a unit vector `θ`, if
`⟪y − x, θ⟫ ≤ t` for all `y ∈ S`, then `infDist x (frontier S) ≤ t`. -/
theorem infDist_frontier_le_of_forall_inner_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {S : Set E} (hS : IsOpen S) (hb : Bornology.IsBounded S)
    {x : E} (hx : x ∈ S) {θ : E} (hθ : ‖θ‖ = 1) {t : ℝ} (ht : ∀ y ∈ S, ⟪y - x, θ⟫ ≤ t) :
    infDist x (frontier S) ≤ t := by
  have _ := hb
  have ht0 : 0 ≤ t := by
    simpa using ht x hx
  apply le_of_forall_pos_le_add
  intro η hη
  have ha0 : 0 ≤ t + η := add_nonneg ht0 (le_of_lt hη)
  have hz : x + (t + η) • θ ∉ S := by
    intro hzS
    have hle := ht (x + (t + η) • θ) hzS
    have heq : ⟪(x + (t + η) • θ) - x, θ⟫ = t + η := by
      simp only [add_sub_cancel_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
        hθ, one_pow, mul_one]
    rw [heq] at hle
    linarith
  let f : ℝ → E := fun r => x + r • θ
  let T : Set E := f '' Icc 0 (t + η)
  have hf : Continuous f := by
    dsimp [f]
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hTpc : IsPreconnected T := by
    exact isPreconnected_Icc.image f hf.continuousOn
  have hxT : (T ∩ S).Nonempty := by
    refine ⟨x, ?_, hx⟩
    refine ⟨0, ⟨le_rfl, ha0⟩, ?_⟩
    simp [f]
  have hzT : x + (t + η) • θ ∈ T := by
    refine ⟨t + η, ⟨ha0, le_rfl⟩, ?_⟩
    rfl
  have hfront : (frontier S ∩ T).Nonempty := by
    by_contra hne
    have hclosure : closure S ∩ T ⊆ S := by
      intro y hy
      by_contra hys
      have hyf : y ∈ frontier S := by
        rw [hS.frontier_eq]
        exact ⟨hy.1, hys⟩
      exact hne ⟨y, hyf, hy.2⟩
    have hsub : T ⊆ S :=
      hTpc.subset_of_closure_inter_subset hS hxT hclosure
    exact hz (hsub hzT)
  rcases hfront with ⟨y, hyfront, hyT⟩
  rcases hyT with ⟨r, hr, rfl⟩
  change x + r • θ ∈ frontier S at hyfront
  calc
    infDist x (frontier S) ≤ dist x (x + r • θ) :=
      Metric.infDist_le_dist_of_mem hyfront
    _ = r := by
      rw [dist_self_add_right, norm_smul, Real.norm_eq_abs, hθ, mul_one,
        abs_of_nonneg hr.1]
    _ ≤ t + η := hr.2

end FunctionalInequalities.Analysis

end InfdistLeWidth

section AffineTransportSubgradientImage

open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal

/-! Subgradient images under affine changes of variables and their volume. -/

namespace FunctionalInequalities.Analysis

section StructuredSpace

variable {E : Type*}
  [NormedAddCommGroup E]

/-- The absolute determinant of the inverse affine linear part. -/
theorem abs_det_linear_symm [InnerProductSpace ℝ E] (e : E ≃ᵃ[ℝ] E) :
    |LinearMap.det (e.symm.linear : E →ₗ[ℝ] E)| =
      |LinearMap.det (e.linear : E →ₗ[ℝ] E)|⁻¹ := by
  rw [AffineEquiv.linear_symm, LinearEquiv.det_coe_symm, abs_inv]

section FiniteDimensional

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The volume of an affine image is `|det| · vol`. -/
theorem volume_image_affineEquiv [MeasurableSpace E] [BorelSpace E] (e : E ≃ᵃ[ℝ] E) (G : Set E) :
    (volume : Measure E) (e '' G) =
      ENNReal.ofReal |LinearMap.det (e.linear : E →ₗ[ℝ] E)| * volume G := by
  have he (x : E) : e x = e.linear x + e 0 := by
    simpa only [vadd_eq_add, add_zero] using e.map_vadd (0 : E) x
  have himage : e '' G = (fun x => x + e 0) '' ((e.linear : E →ₗ[ℝ] E) '' G) := by
    rw [Set.image_image]
    congr 1
    funext x
    exact he x
  rw [himage, Set.image_add_right, measure_preimage_add_right, Measure.addHaar_image_linearMap]

/-- Actual DOMAIN supporting-image volume under an invertible affine change.
This is an outer-measure identity, including zero dimension and infinite volume. -/
theorem volume_subgradientImageOn_comp_affineEquiv_symm
    [MeasurableSpace E] [BorelSpace E]
    (u : E → ℝ) (e : E ≃ᵃ[ℝ] E) (D G : Set E) :
    (volume : Measure E)
        (subgradientImageOn (u ∘ e.symm) (e '' D) (e '' G)) =
      ENNReal.ofReal
          |LinearMap.det (e.linear : E →ₗ[ℝ] E)|⁻¹ *
        (volume : Measure E)
          (subgradientImageOn u D G) := by
  rw [subgradientImageOn_comp_affineEquiv_symm, Measure.addHaar_image_linearMap]
  let b := stdOrthonormalBasis ℝ E
  have hdetadj :
      LinearMap.det (LinearMap.adjoint (e.linear.symm : E →ₗ[ℝ] E)) =
        LinearMap.det (e.linear.symm : E →ₗ[ℝ] E) := by
    calc
      LinearMap.det (LinearMap.adjoint (e.linear.symm : E →ₗ[ℝ] E)) =
          (LinearMap.toMatrix b.toBasis b.toBasis
            (LinearMap.adjoint (e.linear.symm : E →ₗ[ℝ] E))).det :=
        (LinearMap.det_toMatrix b.toBasis
          (LinearMap.adjoint (e.linear.symm : E →ₗ[ℝ] E))).symm
      _ = (LinearMap.toMatrix b.toBasis b.toBasis
            (e.linear.symm : E →ₗ[ℝ] E)).conjTranspose.det := by
        rw [LinearMap.toMatrix_adjoint b b]
      _ = (LinearMap.toMatrix b.toBasis b.toBasis
            (e.linear.symm : E →ₗ[ℝ] E)).det := by
        rw [Matrix.det_conjTranspose]
        simp
      _ = LinearMap.det (e.linear.symm : E →ₗ[ℝ] E) :=
        LinearMap.det_toMatrix b.toBasis (e.linear.symm : E →ₗ[ℝ] E)
  rw [hdetadj, LinearEquiv.det_coe_symm, abs_inv]

/-- Affine transport of the GLOBAL supporting image, obtained from genuine DOMAIN transport. -/
theorem subgradientImage_comp_affineEquiv_symm (u : E → ℝ) (e : E ≃ᵃ[ℝ] E) (G : Set E) :
    subgradientImage (u ∘ e.symm) (e '' G) =
      (LinearMap.adjoint (e.linear.symm : E →ₗ[ℝ] E)) '' subgradientImage u G := by
  simpa only [Set.image_univ_of_surjective e.surjective, subgradientImageOn_univ] using
    subgradientImageOn_comp_affineEquiv_symm u e Set.univ G

/-- The volume of the transported subgradient image is `vol (∂u(G)) / |det T|`. -/
theorem volume_subgradientImage_comp_affineEquiv_symm [MeasurableSpace E] [BorelSpace E]
    (u : E → ℝ) (e : E ≃ᵃ[ℝ] E) (G : Set E) :
    (volume : Measure E) (subgradientImage (u ∘ e.symm) (e '' G)) =
      ENNReal.ofReal |LinearMap.det (e.linear : E →ₗ[ℝ] E)|⁻¹ *
        (volume : Measure E) (subgradientImage u G) := by
  simpa only [Set.image_univ_of_surjective e.surjective, subgradientImageOn_univ] using
    volume_subgradientImageOn_comp_affineEquiv_symm u e Set.univ G

end FiniteDimensional

end StructuredSpace

end FunctionalInequalities.Analysis

end AffineTransportSubgradientImage

section NormalizedMinEstimate

open MeasureTheory Set Metric
open scoped RealInnerProductSpace ENNReal

/-! Minimum estimate for a normalized convex function from a lower Alexandrov bound. -/

namespace FunctionalInequalities.Analysis

/-- **Minimum estimate on a normalised section by quadratic comparison** (Caffarelli's argument;
Gutiérrez Lemma via the comparison with `½κ(‖x‖² − 1)`): if `v` is convex, `≤ 0` on
the frontier of a bounded open `S ⊇ closedBall 0 1`, and `a · vol G ≤ vol ∂v(G)` for open `G ⊆ S`,
then
`v 0 ≤ −½ (a/2)^{1/n}`. -/
theorem le_neg_of_lower_alexandrov_bound {n : ℕ} (hn : 0 < n) {v : EuclideanSpace ℝ (Fin n) → ℝ}
    (hconv : ConvexOn ℝ univ v) {S : Set (EuclideanSpace ℝ (Fin n))} (hS : IsOpen S)
    (hb : Bornology.IsBounded S) (hball : closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ S)
    (hfr : ∀ x ∈ frontier S, v x ≤ 0) {a : ℝ} (ha : 0 < a)
    (hA :
      ∀ G : Set (EuclideanSpace ℝ (Fin n)),
        IsOpen G →
          G ⊆ S →
            ENNReal.ofReal a * (volume : Measure (EuclideanSpace ℝ (Fin n))) G ≤
              (volume : Measure (EuclideanSpace ℝ (Fin n))) (subgradientImage v G)) :
    v 0 ≤ -(1 / 2) * (a / 2) ^ (1 / (n : ℝ)) := by
  let E := EuclideanSpace ℝ (Fin n)
  let κ : ℝ := (a / 2) ^ (1 / (n : ℝ))
  let M : Matrix (Fin n) (Fin n) ℝ := κ • (1 : Matrix (Fin n) (Fin n) ℝ)
  let w : E → ℝ := quadraticAt M 0 0 (-κ / 2)
  have hκ : 0 < κ := by
    dsimp [κ]
    exact Real.rpow_pos_of_pos (by positivity) _
  have hκpow : κ ^ n = a / 2 := by
    dsimp [κ]
    simpa only [one_div] using
      (Real.rpow_inv_natCast_pow (show 0 ≤ a / 2 by positivity) (Nat.ne_of_gt hn))
  have hMpos : M.PosDef := by
    dsimp [M]
    exact Matrix.PosDef.one.smul hκ
  have hMdet : M.det = κ ^ n := by
    dsimp [M]
    rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one]
  have hMaction (x : E) : Matrix.toEuclideanLin M x = κ • x := by
    change Matrix.toLpLin 2 2 (κ • (1 : Matrix (Fin n) (Fin n) ℝ)) x = κ • x
    rw [map_smul, Matrix.toLpLin_one]
    simp
  have hwformula (x : E) : w x = (κ / 2) * (‖x‖ ^ 2 - 1) := by
    dsimp [w, quadraticAt]
    rw [hMaction]
    simp only [sub_zero, inner_zero_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
    ring
  have hvc : Continuous v := by
    apply continuousOn_univ.mp
    exact hconv.continuousOn isOpen_univ
  have hwconv : ConvexOn ℝ univ w := by
    dsimp [w]
    exact convexOn_quadraticAt hMpos.posSemidef 0 0 (-κ / 2)
  have hwc : Continuous w := by
    apply continuousOn_univ.mp
    exact hwconv.continuousOn isOpen_univ
  have hwfront : ∀ x ∈ frontier S, 0 < w x := by
    intro x hx
    have hxnotS : x ∉ S := by
      rw [hS.frontier_eq] at hx
      exact fun hxs => hx.2 hxs
    have hnorm : 1 < ‖x‖ := by
      apply lt_of_not_ge
      intro hle
      apply hxnotS
      apply hball
      simpa [mem_closedBall, dist_zero_right] using hle
    have hsq : 0 < ‖x‖ ^ 2 - 1 := by nlinarith [norm_nonneg x]
    rw [hwformula]
    exact mul_pos (half_pos hκ) hsq
  let G : Set E := S ∩ {x | w x < v x}
  have hGopen : IsOpen G := by
    dsimp [G]
    exact hS.inter (isOpen_lt hwc hvc)
  have hGsub : G ⊆ S := by
    intro x hx
    exact hx.1
  have hGb : Bornology.IsBounded G := hb.subset hGsub
  have hGeq : ∀ x ∈ frontier G, w x = v x := by
    intro x hx
    have hxclG : x ∈ closure G := frontier_subset_closure hx
    have hxclS : x ∈ closure S := closure_mono hGsub hxclG
    have hle : w x ≤ v x := by
      apply closure_minimal (s := G) (t := {y | w y ≤ v y}) ?_ (isClosed_le hwc hvc) hxclG
      intro y hy
      change w y ≤ v y
      exact le_of_lt (show w y < v y from hy.2)
    by_cases hxs : x ∈ S
    · have hxnotG : x ∉ G := by
        have hx' := hx
        rw [hGopen.frontier_eq] at hx'
        exact fun hxg => hx'.2 hxg
      apply le_antisymm hle
      exact le_of_not_gt (fun hlt => hxnotG ⟨hxs, hlt⟩)
    · have hxf : x ∈ frontier S := by
        rw [hS.frontier_eq]
        exact ⟨hxclS, hxs⟩
      exfalso
      linarith [hfr x hxf, hwfront x hxf]
  have hGempty : G = ∅ := by
    by_contra hGne
    have hGnonempty : G.Nonempty := nonempty_iff_ne_empty.mpr hGne
    have hGpos : 0 < (volume : Measure E) G := IsOpen.measure_pos volume hGopen hGnonempty
    have hGtop : (volume : Measure E) G < ∞ := hGb.measure_lt_top
    have hcomp : subgradientImage v G ⊆ subgradientImage w G :=
      subgradientImage_subset_of_le hwconv hconv hGopen hGb (fun x hx => le_of_lt hx.2) hGeq
    have hmul :
      ENNReal.ofReal a * (volume : Measure E) G ≤
        ENNReal.ofReal M.det * (volume : Measure E) G := by
      calc
        ENNReal.ofReal a * (volume : Measure E) G ≤
            (volume : Measure E) (subgradientImage v G) :=
          hA G hGopen hGsub
        _ ≤ (volume : Measure E) (subgradientImage w G) := measure_mono hcomp
        _ = ENNReal.ofReal M.det * (volume : Measure E) G :=
          volume_subgradientImage_quadraticAt hMpos 0 0 (-κ / 2) hGopen.measurableSet
    have hcoef : ENNReal.ofReal a ≤ ENNReal.ofReal M.det := by
      exact
        (ENNReal.mul_le_mul_iff_right (a := (volume : Measure E) G) (ne_of_gt hGpos)
              (ne_of_lt hGtop)).mp
          (by simpa [mul_comm] using hmul)
    have hreal : a ≤ M.det := (ENNReal.ofReal_le_ofReal_iff hMpos.det_pos.le).mp hcoef
    rw [hMdet, hκpow] at hreal
    linarith
  have hvw : ∀ x ∈ S, v x ≤ w x := by
    intro x hxs
    by_contra hnot
    have hlt : w x < v x := lt_of_not_ge hnot
    have hxg : x ∈ G := ⟨hxs, hlt⟩
    rw [hGempty] at hxg
    exact hxg
  have hzeroS : (0 : E) ∈ S := by
    apply hball
    simp [mem_closedBall]
  calc
    v 0 ≤ w 0 := hvw 0 hzeroS
    _ = -(1 / 2) * (a / 2) ^ (1 / (n : ℝ)) := by
      rw [hwformula]
      dsimp [κ]
      simp
      ring

end FunctionalInequalities.Analysis

end NormalizedMinEstimate

section SubgradientImageSubAffine

open MeasureTheory Set
open scoped RealInnerProductSpace

/-! Subgradient images after subtracting an affine function, and their volume. -/

namespace FunctionalInequalities.Analysis

section InnerProduct

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Subtracting an affine function translates subgradient images** (Caffarelli's argument,
bookkeeping): `∂(u − ⟪p, ·⟫ − c)(G) = ∂u(G) − p`, hence the volumes agree. -/
theorem subgradientImage_sub_inner_add_const (u : E → ℝ) (p : E) (c : ℝ) (G : Set E) :
    subgradientImage (fun x => u x - (⟪p, x⟫ + c)) G =
      (fun q => q - p) '' subgradientImage u G := by
  ext q
  constructor
  · rintro ⟨x, hx, hq⟩
    refine ⟨q + p, ?_, add_sub_cancel_right q p⟩
    refine ⟨x, hx, ?_⟩
    intro y
    have h := hq y
    simp only [inner_sub_right] at h
    simp only [inner_add_left, inner_sub_right]
    linarith
  · rintro ⟨r, ⟨x, hx, hr⟩, rfl⟩
    refine ⟨x, hx, ?_⟩
    intro y
    have h := hr y
    simp only [inner_sub_right] at h
    simp only [inner_sub_left, inner_sub_right]
    linarith

theorem volume_subgradientImage_sub_inner_add_const [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (u : E → ℝ) (p : E) (c : ℝ) (G : Set E) :
    (volume : Measure E) (subgradientImage (fun x => u x - (⟪p, x⟫ + c)) G) =
      (volume : Measure E) (subgradientImage u G) := by
  rw [subgradientImage_sub_inner_add_const]
  simp only [sub_eq_add_neg, Set.image_add_right, neg_neg]
  exact measure_preimage_add_right (volume : Measure E) p (subgradientImage u G)

end InnerProduct

end FunctionalInequalities.Analysis

end SubgradientImageSubAffine

section AlexandrovIdentityOpen

open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal

/-! The Alexandrov identity on open sets: the volume of the subgradient image equals the integral of
the Monge–Ampère density. -/

namespace FunctionalInequalities.Analysis

section InnerProduct

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- One actual compact-to-open producer shared by the moment-open identity
and actual local-map-to-open source. The compact exhaustion, canonical pure
image union and monotone measure continuity are implemented only here. No C0/convex/Lip/image
measurability or
finite measure premise. Compact equality is intermediate generated data. -/
theorem subgradientImage_open_measure_of_compact_eq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {u : E → ℝ} {μ : Measure E} {D G : Set E} (hG : IsOpen G) (hGD : G ⊆ D)
    (hc : ∀ S : Set E, IsCompact S → S ⊆ D → volume (subgradientImage u S) = μ S) :
    volume (subgradientImage u G) = μ G := by
  let : LocallyCompactSpace G := hG.locallyCompactSpace
  let S : ℕ → Set E := fun n => Subtype.val '' compactCovering G n
  have hScompact (n : ℕ) : IsCompact (S n) :=
    (isCompact_compactCovering G n).image continuous_subtype_val
  have hSmono : Monotone S := fun _ _ hij => Set.image_mono (compactCovering_subset G hij)
  have hSunion : (⋃ n, S n) = G := by
    change (⋃ n, Subtype.val '' compactCovering G n) = G
    rw [← image_iUnion, iUnion_compactCovering, image_univ, Subtype.range_coe]
  have hSsub (n : ℕ) : S n ⊆ D := by
    rintro _ ⟨y, _hy, rfl⟩
    exact hGD y.property
  have hTmono : Monotone (fun n => subgradientImage u (S n)) := by
    intro i j hij
    simpa only [subgradientImageOn_univ] using subgradientImageOn_mono u univ (hSmono hij)
  have hTunion : subgradientImage u G = ⋃ n, subgradientImage u (S n) := by
    rw [← hSunion]
    simpa only [subgradientImageOn_univ] using subgradientImageOn_iUnion u univ S
  calc
    volume (subgradientImage u G) = volume (⋃ n, subgradientImage u (S n)) :=
      congrArg volume hTunion
    _ = ⨆ n, volume (subgradientImage u (S n)) := hTmono.measure_iUnion
    _ = ⨆ n, μ (S n) := iSup_congr fun n => hc (S n) (hScompact n) (hSsub n)
    _ = μ (⋃ n, S n) := hSmono.measure_iUnion.symm
    _ = μ G := congrArg μ hSunion


/-- **Alexandrov identity on open sets for the moment potential**:
if `u` is convex, Lipschitz, `ν = e^{-u} dx` is normalised and `ν.map ∇u = μ = 1_K e^{-V} dx` for a
closed convex
`K` and a measurable `V`, then the subgradient image of every open `G` has volume `∫_G e^{-u +
V(∇u)}`. -/
theorem volume_subgradientImage_eq_lintegral_of_isOpen [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {u : E → ℝ} {L : NNReal} (hu : LipschitzWith L u)
    (hconv : ConvexOn ℝ univ u) (hnorm : ∫ x, Real.exp (-u x) ∂(volume : Measure E) = 1)
    {K : Set E} (hK : IsClosed K) (hKc : Convex ℝ K) {V : E → ℝ} (hV : Measurable V)
    (hmap :
      ((volume : Measure E).tilted (-u)).map (gradient u) =
        (volume : Measure E).withDensity
          (K.indicator fun p => ENNReal.ofReal (Real.exp (-V p))))
    {G : Set E} (hG : IsOpen G) :
    (volume : Measure E) (subgradientImage u G) =
      ∫⁻ x in G, ENNReal.ofReal (Real.exp (-u x + V (gradient u x))) ∂(volume : Measure E) := by
  classical
  let ρ : E → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (-u x))
  let f : E → ℝ≥0∞ := K.indicator fun p => ENNReal.ofReal (Real.exp (-V p))
  let g : E → ℝ≥0∞ := K.indicator fun p => ENNReal.ofReal (Real.exp (V p))
  let F : E → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (-u x + V (gradient u x)))
  have hρ : Measurable ρ := hu.continuous.measurable.neg.exp.ennreal_ofReal
  have hf : Measurable f := hV.neg.exp.ennreal_ofReal.indicator hK.measurableSet
  have hg : Measurable g := hV.exp.ennreal_ofReal.indicator hK.measurableSet
  have hgrad : Measurable (gradient u) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.measurable.comp (measurable_fderiv ℝ u)
  have htilt : (volume : Measure E).tilted (-u) = volume.withDensity ρ := by
    change
      (volume : Measure E).withDensity
          (fun x =>
            ENNReal.ofReal (Real.exp (-u x) / ∫ y, Real.exp (-u y) ∂(volume : Measure E))) =
        volume.withDensity ρ
    simp only [hnorm, div_one, ρ]
  have hmap' : ((volume : Measure E).withDensity ρ).map (gradient u) = volume.withDensity f := by
    rw [← htilt]
    exact hmap
  have hint : Integrable (fun x => Real.exp (-u x)) (volume : Measure E) :=
    Integrable.of_integral_ne_zero (by rw [hnorm]; exact one_ne_zero)
  have hae : ∀ᵐ x ∂(volume : Measure E), gradient u x ∈ K :=
    Probability.ae_mem_of_map_tilted_eq_withDensity_indicator volume volume hint
      hgrad.aemeasurable hK.measurableSet (by fun_prop) hmap
  have hsub (S : Set E) : subgradientImage u S ⊆ K := by
    rintro p ⟨x, _, hp⟩
    exact subgradient_mem_of_ae_gradient_mem hu hconv hK hKc hae hp
  have hcancel (p : E) (hp : p ∈ K) : (f * g) p = 1 := by
    change
      (K.indicator (fun q => ENNReal.ofReal (Real.exp (-V q))) p) *
          (K.indicator (fun q => ENNReal.ofReal (Real.exp (V q))) p) =
        1
    rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp, ←
      ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add, neg_add_cancel, Real.exp_zero,
      ENNReal.ofReal_one]
  have hprod : (fun x => (ρ * (g ∘ gradient u)) x) =ᵐ[volume] F := by
    filter_upwards [hae] with x hx
    change
      ENNReal.ofReal (Real.exp (-u x)) *
          (K.indicator (fun p => ENNReal.ofReal (Real.exp (V p))) (gradient u x)) =
        ENNReal.ofReal (Real.exp (-u x + V (gradient u x)))
    rw [Set.indicator_of_mem hx, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
  have hcompact {S : Set E} (hS : IsCompact S) :
    (volume : Measure E) (subgradientImage u S) = ((volume : Measure E).withDensity F) S := by
    have hT : MeasurableSet (subgradientImage u S) :=
      (isClosed_subgradientImage_of_isCompact hu.continuous hS).measurableSet
    have hleft :
      ∫⁻ p in subgradientImage u S, g p ∂(volume : Measure E).withDensity f =
        (volume : Measure E) (subgradientImage u S) := by
      calc
        ∫⁻ p in subgradientImage u S, g p ∂(volume : Measure E).withDensity f =
            ∫⁻ p in subgradientImage u S, (f * g) p ∂(volume : Measure E) :=
          setLIntegral_withDensity_eq_setLIntegral_mul volume hf hg hT
        _ = ∫⁻ p in subgradientImage u S, 1 ∂(volume : Measure E) :=
          setLIntegral_congr_fun hT fun p hp => hcancel p (hsub S hp)
        _ = (volume : Measure E) (subgradientImage u S) := by
          rw [lintegral_one, Measure.restrict_apply_univ]
    calc
      (volume : Measure E) (subgradientImage u S) =
          ∫⁻ p in subgradientImage u S, g p ∂(volume : Measure E).withDensity f :=
        hleft.symm
      _ = ∫⁻ x in S, g (gradient u x) ∂(volume : Measure E).withDensity ρ :=
        lintegral_subgradientImage_eq_of_map_gradient hu hconv
          (withDensity_absolutelyContinuous volume ρ) hmap'
          (withDensity_absolutelyContinuous volume f) hS g hg
      _ = ∫⁻ x in S, (ρ * (g ∘ gradient u)) x ∂(volume : Measure E) :=
        setLIntegral_withDensity_eq_setLIntegral_mul volume hρ (hg.comp hgrad) hS.measurableSet
      _ = ∫⁻ x in S, F x ∂(volume : Measure E) := lintegral_congr_ae (ae_restrict_of_ae hprod)
      _ = ((volume : Measure E).withDensity F) S := (withDensity_apply F hS.measurableSet).symm
  have hmass :
    (volume : Measure E) (subgradientImage u G) = ((volume : Measure E).withDensity F) G :=
    subgradientImage_open_measure_of_compact_eq hG (subset_univ _) (fun _ hS _ => hcompact hS)
  exact hmass.trans (withDensity_apply F hG.measurableSet)

end InnerProduct

end FunctionalInequalities.Analysis

end AlexandrovIdentityOpen

section ReciprocalAlexandrovBounds

open MeasureTheory Set Metric
open scoped RealInnerProductSpace ENNReal

/-! Two-sided Alexandrov bounds for the inverse subgradient map. -/

namespace FunctionalInequalities.Analysis

section InnerProduct

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]



private lemma inverse_subgradient_isClosed {u : E → ℝ} (hu : Continuous u)
    {S : Set E} (hS : IsCompact S) :
    IsClosed {x | ∃ p ∈ S, ∀ y, u x + ⟪p, y - x⟫ ≤ u y} := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let A : Set (S × E) :=
    ⋂ y : E, {q | u q.2 + ⟪q.1.1, y - q.2⟫ ≤ u y}
  have hA : IsClosed A := by
    refine isClosed_iInter fun y => ?_
    exact isClosed_le
      ((hu.comp continuous_snd).add
        ((continuous_subtype_val.comp continuous_fst).inner
          (continuous_const.sub continuous_snd)))
      continuous_const
  have himage :
      Prod.snd '' A = {x | ∃ p ∈ S, ∀ y, u x + ⟪p, y - x⟫ ≤ u y} := by
    ext x
    constructor
    · rintro ⟨⟨p, z⟩, hz, rfl⟩
      exact ⟨p.1, p.2, mem_iInter.mp hz⟩
    · rintro ⟨p, hp, hx⟩
      exact ⟨(⟨p, hp⟩, x), mem_iInter.mpr hx, rfl⟩
  rw [← himage]
  exact isClosedMap_snd_of_compactSpace A hA

section FiniteDimensional

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

private lemma inverse_subgradient_measurableSet
    {u : E → ℝ} (hu : Continuous u) {G : Set E} (hG : IsOpen G) :
    MeasurableSet {x | ∃ p ∈ G, ∀ y, u x + ⟪p, y - x⟫ ≤ u y} := by
  let : LocallyCompactSpace G := hG.locallyCompactSpace
  let S : ℕ → Set E := fun n => Subtype.val '' compactCovering G n
  have hScompact (n : ℕ) : IsCompact (S n) :=
    (isCompact_compactCovering G n).image continuous_subtype_val
  have hSunion : (⋃ n, S n) = G := by
    change (⋃ n, Subtype.val '' compactCovering G n) = G
    rw [← image_iUnion, iUnion_compactCovering, image_univ, Subtype.range_coe]
  have hTunion :
      {x | ∃ p ∈ G, ∀ y, u x + ⟪p, y - x⟫ ≤ u y} =
        ⋃ n, {x | ∃ p ∈ S n, ∀ y, u x + ⟪p, y - x⟫ ≤ u y} := by
    rw [← hSunion]
    ext x
    constructor
    · rintro ⟨p, hp, hx⟩
      obtain ⟨n, hn⟩ := mem_iUnion.mp hp
      exact mem_iUnion.mpr ⟨n, p, hn, hx⟩
    · intro hx
      obtain ⟨n, p, hp, hx⟩ := mem_iUnion.mp hx
      exact ⟨p, mem_iUnion.mpr ⟨n, hp⟩, hx⟩
  rw [hTunion]
  exact MeasurableSet.iUnion fun n =>
    (inverse_subgradient_isClosed hu (hScompact n)).measurableSet

/-- **Reciprocal Alexandrov bounds**: for the moment potential `u` (convex, Lipschitz,
`ν = e^{-u} dx` normalised, `ν.map ∇u = μ = ρ dx` with `c ≤ ρ ≤ C` on a closed convex `K`) and a
radius `M`,
the set `(∂u)⁻¹(G) = {x | ∃ p ∈ G, p ∈ ∂u(x)}` of an open `G ⊆ K` that lies in `closedBall 0 M` has
volume
comparable to `vol G`. -/
theorem exists_inverse_subgradient_volume_bounds {u : E → ℝ} {L : NNReal}
    (hu : LipschitzWith L u) (hconv : ConvexOn ℝ univ u)
    (hnorm : ∫ x, Real.exp (-u x) ∂(volume : Measure E) = 1) {μ : Measure E}
    (hmap : ((volume : Measure E).tilted (-u)).map (gradient u) = μ) {ρ : E → ℝ≥0∞}
    (hρ : Measurable ρ) (hμ : μ = (volume : Measure E).withDensity ρ) {K : Set E}
    (hK : IsClosed K) (hKc : Convex ℝ K) {c C : ℝ} (hc : 0 < c)
    (hρK : ∀ p ∈ K, ENNReal.ofReal c ≤ ρ p ∧ ρ p ≤ ENNReal.ofReal C) (M : ℝ) :
    ∃ a b : ℝ,
      0 < a ∧
        ∀ G : Set E,
          IsOpen G →
            G ⊆ K →
              {x | ∃ p ∈ G, ∀ y, u x + ⟪p, y - x⟫ ≤ u y} ⊆ closedBall (0 : E) M →
                ENNReal.ofReal a * (volume : Measure E) G ≤
                    (volume : Measure E) {x | ∃ p ∈ G, ∀ y, u x + ⟪p, y - x⟫ ≤ u y} ∧
                  (volume : Measure E) {x | ∃ p ∈ G, ∀ y, u x + ⟪p, y - x⟫ ≤ u y} ≤
                    ENNReal.ofReal b * (volume : Measure E) G := by
  have _hρ : Measurable ρ := hρ
  have _hK : IsClosed K := hK
  have _hKc : Convex ℝ K := hKc
  let ν : Measure E := (volume : Measure E).tilted (-u)
  have hν : ν ≪ (volume : Measure E) := by
    dsimp [ν, Measure.tilted]
    exact withDensity_absolutelyContinuous _ _
  have hν_eq :
    ν = (volume : Measure E).withDensity (fun x => ENNReal.ofReal (Real.exp (-u x))) := by
    dsimp [ν, Measure.tilted]
    rw [hnorm]
    simp
  have hgrad : Measurable (gradient u) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.measurable.comp (measurable_fderiv ℝ u)
  have hdiff : ∀ᵐ x ∂ν, DifferentiableAt ℝ u x :=
    ae_iff.mpr (hν (ae_iff.mp (hu.ae_differentiableAt (μ := (volume : Measure E)))))
  let Q : Set E := closedBall (0 : E) (max M 0)
  have hQ : IsCompact Q := isCompact_closedBall _ _
  have hQne : Q.Nonempty := nonempty_closedBall.mpr (le_max_right M 0)
  obtain ⟨xm, _, hxm⟩ := hQ.exists_isMaxOn hQne hu.continuous.continuousOn
  obtain ⟨xn, _, hxn⟩ := hQ.exists_isMinOn hQne hu.continuous.continuousOn
  let m : ℝ := u xm
  let n : ℝ := u xn
  let a : ℝ := c / Real.exp (-n)
  let b : ℝ := C / Real.exp (-m)
  have ha : 0 < a := div_pos hc (Real.exp_pos (-n))
  refine ⟨a, b, ha, ?_⟩
  intro G hG hGK hTG
  let T : Set E := {x | ∃ p ∈ G, ∀ y, u x + ⟪p, y - x⟫ ≤ u y}
  have hT : MeasurableSet T := inverse_subgradient_measurableSet hu.continuous hG
  have hTQ : T ⊆ Q := hTG.trans (closedBall_subset_closedBall (le_max_left M 0))
  have hsets : T =ᵐ[ν] (gradient u ⁻¹' G) := by
    filter_upwards [hdiff] with x hx
    change (∃ p ∈ G, ∀ y, u x + ⟪p, y - x⟫ ≤ u y) ↔ gradient u x ∈ G
    constructor
    · rintro ⟨p, hpG, hp⟩
      exact (subgradient_eq_gradient hx hp) ▸ hpG
    · intro hxG
      refine ⟨gradient u x, hxG, ?_⟩
      intro y
      have ht := gradient_le_increment hconv x (y - x) hx
      rw [add_sub_cancel] at ht
      linarith
  have hident : ν T = μ G := by
    calc
      ν T = ν (gradient u ⁻¹' G) := measure_congr hsets
      _ = (ν.map (gradient u)) G := (Measure.map_apply hgrad hG.measurableSet).symm
      _ = μ G := congrArg (fun η : Measure E => η G) hmap
  have hνT : ν T = ∫⁻ x in T, ENNReal.ofReal (Real.exp (-u x)) := by
    rw [hν_eq]
    exact withDensity_apply _ hT
  have hlowerν : ENNReal.ofReal (Real.exp (-m)) * (volume : Measure E) T ≤ ν T := by
    rw [hνT]
    calc
      ENNReal.ofReal (Real.exp (-m)) * (volume : Measure E) T =
          ∫⁻ x in T, ENNReal.ofReal (Real.exp (-m)) :=
        (setLIntegral_const T _).symm
      _ ≤ ∫⁻ x in T, ENNReal.ofReal (Real.exp (-u x)) := by
        apply setLIntegral_mono' hT
        intro x hx
        have hxu : u x ≤ m := hxm (hTQ hx)
        exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg hxu))
  have hupperν : ν T ≤ ENNReal.ofReal (Real.exp (-n)) * (volume : Measure E) T := by
    rw [hνT]
    calc
      ∫⁻ x in T, ENNReal.ofReal (Real.exp (-u x)) ≤ ∫⁻ x in T, ENNReal.ofReal (Real.exp (-n)) := by
        apply setLIntegral_mono' hT
        intro x hx
        have hxu : n ≤ u x := hxn (hTQ hx)
        exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg hxu))
      _ = ENNReal.ofReal (Real.exp (-n)) * (volume : Measure E) T := setLIntegral_const T _
  have hμlower : ENNReal.ofReal c * (volume : Measure E) G ≤ μ G := by
    rw [hμ, withDensity_apply ρ hG.measurableSet]
    calc
      ENNReal.ofReal c * (volume : Measure E) G = ∫⁻ p in G, ENNReal.ofReal c :=
        (setLIntegral_const G _).symm
      _ ≤ ∫⁻ p in G, ρ p := setLIntegral_mono' hG.measurableSet fun p hp => (hρK p (hGK hp)).1
  have hμupper : μ G ≤ ENNReal.ofReal C * (volume : Measure E) G := by
    rw [hμ, withDensity_apply ρ hG.measurableSet]
    calc
      ∫⁻ p in G, ρ p ≤ ∫⁻ p in G, ENNReal.ofReal C :=
        setLIntegral_mono' hG.measurableSet fun p hp => (hρK p (hGK hp)).2
      _ = ENNReal.ofReal C * (volume : Measure E) G := setLIntegral_const G _
  constructor
  · have hmul :
      ENNReal.ofReal c * (volume : Measure E) G ≤
        ENNReal.ofReal (Real.exp (-n)) * (volume : Measure E) T := by
      calc
        ENNReal.ofReal c * (volume : Measure E) G ≤ μ G := hμlower
        _ = ν T := hident.symm
        _ ≤ _ := hupperν
    have hn0 : ENNReal.ofReal (Real.exp (-n)) ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos (-n)))
    have hdiv :
      (ENNReal.ofReal c * (volume : Measure E) G) / ENNReal.ofReal (Real.exp (-n)) ≤
        (volume : Measure E) T := by
      apply (ENNReal.div_le_iff hn0 ENNReal.ofReal_ne_top).mpr
      simpa only [mul_comm] using hmul
    change ENNReal.ofReal (c / Real.exp (-n)) * (volume : Measure E) G ≤ (volume : Measure E) T
    rw [ENNReal.ofReal_div_of_pos (Real.exp_pos (-n))]
    exact (ENNReal.mul_div_right_comm ▸ hdiv)
  · have hmul :
      ENNReal.ofReal (Real.exp (-m)) * (volume : Measure E) T ≤
        ENNReal.ofReal C * (volume : Measure E) G := by
      calc
        ENNReal.ofReal (Real.exp (-m)) * (volume : Measure E) T ≤ ν T := hlowerν
        _ = μ G := hident
        _ ≤ _ := hμupper
    have hm0 : ENNReal.ofReal (Real.exp (-m)) ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos (-m)))
    have hdiv :
      (volume : Measure E) T ≤
        (ENNReal.ofReal C * (volume : Measure E) G) / ENNReal.ofReal (Real.exp (-m)) := by
      apply (ENNReal.le_div_iff_mul_le (Or.inl hm0) (Or.inl ENNReal.ofReal_ne_top)).mpr
      simpa only [mul_comm] using hmul
    change (volume : Measure E) T ≤ ENNReal.ofReal (C / Real.exp (-m)) * (volume : Measure E) G
    rw [ENNReal.ofReal_div_of_pos (Real.exp_pos (-m))]
    exact (ENNReal.mul_div_right_comm ▸ hdiv)

end FiniteDimensional

end InnerProduct

end FunctionalInequalities.Analysis

end ReciprocalAlexandrovBounds

namespace FunctionalInequalities.Analysis

section DomainBoundaryBounds

open MeasureTheory Set Metric
open scoped RealInnerProductSpace ENNReal

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]

/-- Finite TOTAL domain MA mass, with no density upper bound, controls the
negative-part boundary power. The positive constant precedes every source. -/
theorem exists_pos_boundary_power_bound_of_domain_mass :
    ∃ C : ℝ,
      0 < C ∧
        ∀ (Ω : Set E) (u : E → ℝ) (M : ℝ),
          IsOpen Ω →
            Convex ℝ Ω →
              Bornology.IsBounded Ω →
                ConvexOn ℝ (closure Ω) u →
                  ContinuousOn u (closure Ω) →
                    (∀ x ∈ frontier Ω, 0 ≤ u x) →
                      0 ≤ M →
                        (volume : Measure E) (subgradientImageOn u Ω Ω) ≤ ENNReal.ofReal M →
                          ∀ x ∈ Ω,
                            (max 0 (-u x)) ^ Module.finrank ℝ E ≤
                              C * M * diam Ω ^ (Module.finrank ℝ E - 1) *
                                infDist x (frontier Ω) := by
  obtain ⟨c, hc, hmaximum⟩ := exists_pos_alexandrov_maximum_principle_domain (E := E)
  refine ⟨c⁻¹, inv_pos.mpr hc, ?_⟩
  intro Ω u M hΩ hΩconv hb hu huc hfr hM hmass x hx
  have hD : 0 ≤ diam Ω := Metric.diam_nonneg
  have hd : 0 ≤ infDist x (frontier Ω) := Metric.infDist_nonneg
  by_cases hneg : u x < 0
  · have hmax := hmaximum u Ω hu huc hΩ hΩconv hb hfr x hx hneg
    have hcoef : 0 ≤ diam Ω ^ (Module.finrank ℝ E - 1) * infDist x (frontier Ω) := by positivity
    have hENN :
      ENNReal.ofReal (c * (-u x) ^ Module.finrank ℝ E) ≤
        ENNReal.ofReal (M * (diam Ω ^ (Module.finrank ℝ E - 1) * infDist x (frontier Ω))) := by
      calc
        _ ≤
            volume (subgradientImageOn u Ω Ω) *
              ENNReal.ofReal (diam Ω ^ (Module.finrank ℝ E - 1) * infDist x (frontier Ω)) :=
          hmax
        _ ≤
            ENNReal.ofReal M *
              ENNReal.ofReal (diam Ω ^ (Module.finrank ℝ E - 1) * infDist x (frontier Ω)) :=
          mul_le_mul' hmass (le_refl _)
        _ = _ := (ENNReal.ofReal_mul hM).symm
    have hreal := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hM hcoef)).mp hENN
    have hscaled := mul_le_mul_of_nonneg_left hreal (inv_pos.mpr hc).le
    rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] at hscaled
    rw [max_eq_right (by linarith : 0 ≤ -u x)]
    nlinarith only [hscaled]
  · rw [max_eq_left (by linarith : -u x ≤ 0),
      zero_pow (Module.finrank_pos (R := ℝ) (M := E)).ne']
    positivity

omit [Nontrivial E] in
/-- A true open-set density bound yields a finite total supporting-image mass
bound; boundedness supplies finite volume. -/
theorem volume_subgradientImageOn_le_of_density_le
    {Ω : Set E} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {u : E → ℝ} {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hMA : ∀ H : Set E, IsOpen H → H ⊆ Ω →
      (volume : Measure E) (subgradientImageOn u Ω H) ≤
        ENNReal.ofReal Λ * (volume : Measure E) H) :
    (volume : Measure E) (subgradientImageOn u Ω Ω) ≤
      ENNReal.ofReal (Λ * ((volume : Measure E) Ω).toReal) := by
  calc
    _ ≤ ENNReal.ofReal Λ * (volume : Measure E) Ω := hMA Ω hΩ Subset.rfl
    _ = _ := by
      rw [ENNReal.ofReal_mul hΛ, ENNReal.ofReal_toReal (ne_of_lt hb.measure_lt_top)]

/-- A real negative-part boundary power estimate obtained from the actual
DOMAIN Alexandrov maximum principle.

The constant is chosen before the domain, function, and density bound.
Boundedness, rather than a separate finite-volume premise, supplies the
finite volume needed for the real/ENNReal conversion. -/
theorem exists_pos_boundary_power_bound_domain :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Ω : Set E) (u : E → ℝ) (Λ : ℝ),
        IsOpen Ω →
        Convex ℝ Ω →
        Bornology.IsBounded Ω →
        ConvexOn ℝ (closure Ω) u →
        ContinuousOn u (closure Ω) →
        (∀ x ∈ frontier Ω, 0 ≤ u x) →
        0 ≤ Λ →
        (∀ H : Set E, IsOpen H → H ⊆ Ω →
          (volume : Measure E) (subgradientImageOn u Ω H) ≤
            ENNReal.ofReal Λ * (volume : Measure E) H) →
        ∀ x ∈ Ω,
          (max 0 (-u x)) ^ Module.finrank ℝ E ≤
            C * Λ * ((volume : Measure E) Ω).toReal *
              diam Ω ^ (Module.finrank ℝ E - 1) *
                infDist x (frontier Ω) := by
  obtain ⟨C, hC, hbound⟩ := exists_pos_boundary_power_bound_of_domain_mass (E := E)
  refine ⟨C, hC, ?_⟩
  intro Ω u Λ hΩ hΩconv hb hu huc hfr hΛ hMA x hx
  have hmass := volume_subgradientImageOn_le_of_density_le hΩ hb hΛ hMA
  have h := hbound Ω u (Λ * ((volume : Measure E) Ω).toReal)
    hΩ hΩconv hb hu huc hfr (mul_nonneg hΛ ENNReal.toReal_nonneg) hmass x hx
  simpa only [mul_assoc] using h

/-- The elementary numerical implication used for the common lower modulus.
Only natural-number powers occur. Positive dimension is explicit. -/
private lemma lower_bound_of_boundary_power
    {n : ℕ} (hn : 0 < n)
    {a K d ε : ℝ}
    (hK : 0 ≤ K) (hd0 : 0 ≤ d) (hε : 0 < ε)
    (hpower : (max 0 (-a)) ^ n ≤ K * d)
    (hsmall : d < ε ^ n / (K + 1)) :
    -ε ≤ a := by
  have hden : 0 < K + 1 := by linarith
  have hsmall' : d * (K + 1) < ε ^ n :=
    (lt_div_iff₀ hden).mp hsmall
  have hKd : K * d < ε ^ n := by
    nlinarith only [hd0, hsmall']
  by_contra ha
  have hεm : ε < max 0 (-a) :=
    (show ε < -a by linarith).trans_le (le_max_right 0 (-a))
  have hpow :
      ε ^ n < (max 0 (-a)) ^ n :=
    pow_lt_pow_left₀ hεm hε.le (Nat.ne_of_gt hn)
  linarith only [hpower, hKd, hpow]

/-- The radius precedes every closure-convex/C0 source with a fixed finite
TOTAL domain MA mass bound. Atomic measures are not excluded by a density premise. -/
theorem exists_common_lower_boundary_modulus_of_domain_mass {Ω : Set E} (hΩ : IsOpen Ω)
    (hΩconv : Convex ℝ Ω) (hb : Bornology.IsBounded Ω) {M : ℝ} (hM : 0 ≤ M) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ ρ : ℝ,
      0 < ρ ∧
        ∀ u : E → ℝ,
          ConvexOn ℝ (closure Ω) u →
            ContinuousOn u (closure Ω) →
              (∀ x ∈ frontier Ω, 0 ≤ u x) →
                (volume : Measure E) (subgradientImageOn u Ω Ω) ≤ ENNReal.ofReal M →
                  ∀ x ∈ Ω, infDist x (frontier Ω) < ρ → -ε ≤ u x := by
  obtain ⟨C, hC, hbound⟩ := exists_pos_boundary_power_bound_of_domain_mass (E := E)
  let K : ℝ := C * M * diam Ω ^ (Module.finrank ℝ E - 1)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨ε ^ Module.finrank ℝ E / (K + 1), div_pos (pow_pos hε _) (by linarith), ?_⟩
  intro u hu huc hfr hmass x hx hdist
  exact
    lower_bound_of_boundary_power (Module.finrank_pos (R := ℝ) (M := E)) hK
      Metric.infDist_nonneg hε
      (by simpa only [K] using hbound Ω u M hΩ hΩconv hb hu huc hfr hM hmass x hx) hdist
/-- A genuine common lower boundary modulus for the entire source class.

For a fixed bounded open convex domain, nonnegative density upper bound, and
positive epsilon, the radius is chosen before every unknown source function.
Its proof reuses `exists_pos_boundary_power_bound_domain`. -/
theorem exists_common_lower_boundary_modulus_domain
    {Ω : Set E}
    (hΩ : IsOpen Ω)
    (hΩconv : Convex ℝ Ω)
    (hb : Bornology.IsBounded Ω)
    {Λ : ℝ} (hΛ : 0 ≤ Λ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ u : E → ℝ,
        ConvexOn ℝ (closure Ω) u →
        ContinuousOn u (closure Ω) →
        (∀ x ∈ frontier Ω, 0 ≤ u x) →
        (∀ H : Set E, IsOpen H → H ⊆ Ω →
          (volume : Measure E) (subgradientImageOn u Ω H) ≤
            ENNReal.ofReal Λ * (volume : Measure E) H) →
        ∀ x ∈ Ω,
          infDist x (frontier Ω) < ρ →
            -ε ≤ u x := by
  obtain ⟨ρ, hρ, hlower⟩ := exists_common_lower_boundary_modulus_of_domain_mass
    hΩ hΩconv hb (mul_nonneg hΛ ENNReal.toReal_nonneg) hε
  refine ⟨ρ, hρ, ?_⟩
  intro u hu huc hfr hMA
  exact hlower u hu huc hfr (volume_subgradientImageOn_le_of_density_le hΩ hb hΛ hMA)

/-- A true common absolute modulus from finite TOTAL domain MA mass and zero
frontier, with no positive density lower bound and no differentiability input. -/
theorem exists_common_boundary_modulus_of_domain_mass {Ω : Set E} (hΩ : IsOpen Ω)
    (hΩconv : Convex ℝ Ω) (hb : Bornology.IsBounded Ω) {M : ℝ} (hM : 0 ≤ M) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ ρ : ℝ,
      0 < ρ ∧
        ∀ u : E → ℝ,
          ConvexOn ℝ (closure Ω) u →
            ContinuousOn u (closure Ω) →
              (∀ x ∈ frontier Ω, u x = 0) →
                (volume : Measure E) (subgradientImageOn u Ω Ω) ≤ ENNReal.ofReal M →
                  ∀ x ∈ Ω, infDist x (frontier Ω) < ρ → |u x| ≤ ε := by
  obtain ⟨ρ, hρ, hlower⟩ :=
    exists_common_lower_boundary_modulus_of_domain_mass hΩ hΩconv hb hM hε
  refine ⟨ρ, hρ, ?_⟩
  intro u hu huc hfr hmass x hx hdist
  have hupp :=
    le_on_closure_of_le_frontier_of_convexOn hΩ hΩconv hb hu huc (fun y hy => (hfr y hy).le) x
      (subset_closure hx)
  have hlow := hlower u hu huc (fun y hy => (hfr y hy).ge) hmass x hx hdist
  rw [abs_of_nonpos hupp]
  linarith

end DomainBoundaryBounds


end FunctionalInequalities.Analysis
