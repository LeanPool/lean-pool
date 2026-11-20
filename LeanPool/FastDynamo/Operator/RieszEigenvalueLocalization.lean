/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Global.CorrectedRieszProjectionEigenmode
public import LeanPool.FastDynamo.Operator.RieszProjectionCalculus
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Eigenvalue localization by a Riesz contour

This file records the elementary part of the Riesz spectral-mapping argument
for a bundled-domain operator.  On a domain eigenvector, the chosen resolvent
is the scalar Cauchy kernel.  Cauchy--Goursat then shows that the Riesz contour
operator annihilates that eigenvector when its eigenvalue is outside the
closed disk.  Since an eigenvalue cannot itself be a resolvent point, a
nonzero eigenvector fixed by the Riesz operator must lie strictly inside the
circle.

The final theorem applies this localization to the finite invariant Riesz
range constructed in `CorrectedRieszProjectionEigenmode`.  It proves the
spectral location of that range from the inverse identities,
idempotence, and nonnegative radius alone.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Complex Metric Set

namespace DomainOperator

universe u v

variable {X : Type u} {D : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup D] [NormedSpace ℂ D]
  {A : DomainOperator X D}

/-- On a domain eigenvector, the operator pencil is scalar multiplication by
`z - eigenvalue`. -/
theorem pencil_apply_of_isEigenpair
    {eigenvalue z : ℂ} {b : D} (hb : A.IsEigenpair eigenvalue b) :
    A.pencil z b = (z - eigenvalue) • A.embedding b := by
  simp only [pencil, sub_apply, smul_apply, hb.2]
  rw [sub_smul]

end DomainOperator

namespace HasResolventOn

universe u v

variable {X : Type u} {D : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup D] [NormedSpace ℂ D]
  {A : DomainOperator X D} {S : Set ℂ}
variable {b : D}

omit [CompleteSpace X] in
/-- A domain eigenvalue cannot belong to a set on which the pencil
has a chosen two-sided inverse. -/
theorem eigenvalue_not_mem_of_isEigenpair
    (h : HasResolventOn A S) {eigenvalue : ℂ} {b : D}
    (hb : A.IsEigenpair eigenvalue b) :
    eigenvalue ∉ S := by
  intro heigenvalue
  have hpencil : A.pencil eigenvalue b = 0 := by
    simpa using A.pencil_apply_of_isEigenpair hb (z := eigenvalue)
  have hleft := congrArg (fun T : D →L[ℂ] D ↦ T b)
    (h.left_inv eigenvalue heigenvalue)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    hpencil, map_zero] at hleft
  apply hb.1
  rw [← hleft]
  exact A.embedding.map_zero

omit [CompleteSpace X] in
/-- The domain-valued resolvent acts on an eigenvector by the scalar Cauchy
kernel. -/
theorem inv_apply_of_isEigenpair
    (h : HasResolventOn A S) {eigenvalue z : ℂ} {b : D}
    (hz : z ∈ S) (hb : A.IsEigenpair eigenvalue b) :
    h.inv z (A.embedding b) = (z - eigenvalue)⁻¹ • b := by
  have hze : z ≠ eigenvalue := by
    intro hze
    subst z
    exact h.eigenvalue_not_mem_of_isEigenpair hb hz
  have hpencil := A.pencil_apply_of_isEigenpair hb (z := z)
  have hleft := congrArg (fun T : D →L[ℂ] D ↦ T b) (h.left_inv z hz)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    hpencil, map_smul] at hleft
  calc
    h.inv z (A.embedding b) = 1 • h.inv z (A.embedding b) :=
      (one_smul ℂ _).symm
    _ = ((z - eigenvalue)⁻¹ * (z - eigenvalue)) •
        h.inv z (A.embedding b) := by
      rw [inv_mul_cancel₀ (sub_ne_zero.mpr hze)]
    _ = (z - eigenvalue)⁻¹ •
        ((z - eigenvalue) • h.inv z (A.embedding b)) := by
      rw [smul_smul]
    _ = (z - eigenvalue)⁻¹ • b := by rw [hleft]

omit [CompleteSpace X] in
/-- Ambient form of `inv_apply_of_isEigenpair`. -/
theorem stateResolvent_apply_of_isEigenpair
    (h : HasResolventOn A S) {eigenvalue z : ℂ} {b : D}
    (hz : z ∈ S) (hb : A.IsEigenpair eigenvalue b) :
    h.stateResolvent z (A.embedding b) =
      (z - eigenvalue)⁻¹ • A.embedding b := by
  simp only [stateResolvent, ContinuousLinearMap.comp_apply,
    h.inv_apply_of_isEigenpair hz hb, map_smul]

/-- The Riesz operator acts on an eigenvector by the winding-number scalar
given by the normalized Cauchy-kernel integral. -/
theorem rieszProjection_apply_of_isEigenpair
    {c eigenvalue : ℂ} {R : ℝ}
    (h : HasResolventOn A (sphere c R)) (hR : 0 ≤ R)
    (hb : A.IsEigenpair eigenvalue b) :
    h.rieszProjection (A.embedding b) =
      ((2 * Real.pi * I : ℂ)⁻¹ *
        (∮ z in C(c, R), (z - eigenvalue)⁻¹)) • A.embedding b := by
  have hcircle := h.circleIntegrable_stateResolvent hR
  rw [rieszProjection, smul_apply]
  have hmap :
      (∮ z in C(c, R), h.stateResolvent z (A.embedding b)) =
        (circleIntegral h.stateResolvent c R) (A.embedding b) := by
    simpa only [ContinuousLinearMap.apply_apply] using
      (circleIntegral.map
        (ContinuousLinearMap.apply ℂ X (A.embedding b)) hcircle)
  rw [← hmap]
  have hintegral :
      (∮ z in C(c, R), h.stateResolvent z (A.embedding b)) =
        ∮ z in C(c, R), (z - eigenvalue)⁻¹ • A.embedding b := by
    apply circleIntegral.integral_congr hR
    intro z hz
    exact h.stateResolvent_apply_of_isEigenpair hz hb
  rw [hintegral, circleIntegral.integral_smul_const, smul_smul]

/-- An eigenvalue inside the circle has winding number one, so the Riesz
operator fixes its ambient eigenvector. -/
theorem rieszProjection_apply_of_isEigenpair_mem_ball
    {c eigenvalue : ℂ} {R : ℝ}
    (h : HasResolventOn A (sphere c R))
    (hb : A.IsEigenpair eigenvalue b)
    (heigenvalue : eigenvalue ∈ ball c R) :
    h.rieszProjection (A.embedding b) = A.embedding b := by
  have hR : 0 ≤ R :=
    (dist_nonneg.trans_lt (mem_ball.mp heigenvalue)).le
  rw [h.rieszProjection_apply_of_isEigenpair hR hb,
    circleIntegral.integral_sub_inv_of_mem_ball heigenvalue]
  have htwo : (2 * Real.pi * I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  rw [inv_mul_cancel₀ htwo, one_smul]

end HasResolventOn

namespace circleIntegral

/-- The scalar Cauchy kernel integrates to zero when its pole is outside the
closed disk. -/
theorem integral_sub_inv_of_not_mem_closedBall
    {c eigenvalue : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (heigenvalue : eigenvalue ∉ closedBall c R) :
    (∮ z in C(c, R), (z - eigenvalue)⁻¹) = 0 := by
  apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
    hR Set.countable_empty
  · intro z hz
    exact (((differentiableAt_id (𝕜 := ℂ)).sub_const eigenvalue).inv
      (sub_ne_zero.mpr (ne_of_mem_of_not_mem hz heigenvalue))).continuousAt.continuousWithinAt
  · intro z hz
    exact ((differentiableAt_id (𝕜 := ℂ)).sub_const eigenvalue).inv
      (sub_ne_zero.mpr (ne_of_mem_of_not_mem
        (mem_closedBall.mpr (mem_ball.mp hz.1).le) heigenvalue))

end circleIntegral

namespace HasResolventOn

universe u v

variable {X : Type u} {D : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup D] [NormedSpace ℂ D]
  {A : DomainOperator X D}
variable {b : D}

/-- Outside the closed disk the winding number is zero, so the Riesz operator
annihilates an ambient eigenvector. -/
theorem rieszProjection_apply_of_isEigenpair_not_mem_closedBall
    {c eigenvalue : ℂ} {R : ℝ}
    (h : HasResolventOn A (sphere c R)) (hR : 0 ≤ R)
    (hb : A.IsEigenpair eigenvalue b)
    (heigenvalue : eigenvalue ∉ closedBall c R) :
    h.rieszProjection (A.embedding b) = 0 := by
  rw [h.rieszProjection_apply_of_isEigenpair hR hb,
    circleIntegral.integral_sub_inv_of_not_mem_closedBall hR heigenvalue,
    mul_zero, zero_smul]

/-- A nonzero domain eigenvector fixed by the Riesz operator has eigenvalue
strictly inside the isolating circle.  Resolvent invertibility excludes the
boundary, while Cauchy--Goursat excludes the exterior. -/
theorem eigenvalue_mem_ball_of_rieszProjection_fixes_eigenvector
    {c eigenvalue : ℂ} {R : ℝ}
    (h : HasResolventOn A (sphere c R)) (hR : 0 ≤ R)
    (hb : A.IsEigenpair eigenvalue b)
    (hfixed : h.rieszProjection (A.embedding b) = A.embedding b) :
    eigenvalue ∈ ball c R := by
  by_contra hnotBall
  have hnotSphere : eigenvalue ∉ sphere c R :=
    h.eigenvalue_not_mem_of_isEigenpair hb
  have hdist_ge : R ≤ dist eigenvalue c := by
    exact not_lt.mp (by simpa only [mem_ball] using hnotBall)
  have hdist_ne : dist eigenvalue c ≠ R := by
    intro hdist
    exact hnotSphere (mem_sphere.mpr hdist)
  have hdist_gt : R < dist eigenvalue c :=
    lt_of_le_of_ne hdist_ge hdist_ne.symm
  have houtside : eigenvalue ∉ closedBall c R := by
    intro hclosed
    exact (not_le_of_gt hdist_gt) (mem_closedBall.mp hclosed)
  have hzero :=
    h.rieszProjection_apply_of_isEigenpair_not_mem_closedBall
      hR hb houtside
  rw [hzero] at hfixed
  exact hb.1 hfixed.symm

end HasResolventOn

namespace CorrectedRieszProjectionEigenmode

universe u v

variable {X : Type u} {D : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup D] [NormedSpace ℂ D] [CompleteSpace D]
  {A : DomainOperator X D} {center : ℂ} {radius : ℝ}

/-- The restricted first moment's eigenvalues lie inside the Riesz circle.
Thus `RieszRangeSpectrumInsideCircle` follows from the concrete inverse
identities and the idempotence already present in `FiniteInvariantRieszData`;
it is not an additional spectral-mapping assumption. -/
theorem rieszRangeSpectrumInsideCircle_of_nonnegative_radius
    (h : HasResolventOn A (sphere center radius))
    (data : FiniteInvariantRieszData h) (hRadius : 0 ≤ radius) :
    RieszRangeSpectrumInsideCircle h data := by
  intro eigenvalue heigenvalue
  obtain ⟨x, hx⟩ := heigenvalue.exists_hasEigenvector
  have hPx : h.rieszProjection (x : X) = x := by
    exact (LinearMap.IsIdempotentElem.mem_range_iff
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap data.idempotent)).mp
      x.property
  have hpair :
      A.IsEigenpair eigenvalue (h.domainRieszProjection (x : X)) :=
    data.isEigenpair_domainRieszProjection_of_hasEigenvector hRadius hx
  have hembedding :
      A.embedding (h.domainRieszProjection (x : X)) = x := by
    rw [h.embedding_domainRieszProjection_apply hRadius, hPx]
  have hfixed :
      h.rieszProjection
          (A.embedding (h.domainRieszProjection (x : X))) =
        A.embedding (h.domainRieszProjection (x : X)) := by
    rw [hembedding, hPx]
  exact h.eigenvalue_mem_ball_of_rieszProjection_fixes_eigenvector
    hRadius hpair hfixed

end CorrectedRieszProjectionEigenmode

end

end FastDynamo
