/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Operator.Domain

/-!
# The real resolvent ray of a Hille–Yosida generator

This module opens the abstract Hille–Yosida development.  It contributes two
independent layers.

* **The algebra of a two-sided domain-valued resolvent.**  A
  `HasResolventOn A S` certificate (`FastDynamo/Operator/Domain.lean`) bundles
  only the two inverse equations for the pencil `z - A`, yet every identity the
  generation theorem needs is already a consequence of them:
  `op_comp_inv` (`A R(z) = z R(z) - I` on the ambient space), `inv_comp_pencil`,
  the two forms `resolvent_identity` and `stateResolvent_identity` of the
  resolvent identity, `op_inv_embedding` (`A R(z) ι = R(z) A` on the domain) and
  `HasResolventOn.commute_stateResolvent`.  None of them assumes a closed graph,
  a complete domain, or continuity of `z ↦ R(z)`; they are stated on a plain
  `HasResolventOn` so that the half-plane resolvent construction can reuse them.

* **The hypothesis of the generation theorem.**  `HilleYosidaRay A M` records
  that the pencil is invertible at every real `r > M` with
  `‖R(r)‖ ≤ (r - M)⁻¹`, which is the only analytic input the Yosida
  approximation scheme consumes.  `HilleYosidaRay.ofHalfPlane` builds one from a
  resolvent on the half-plane `{Re z > M}`.  The two quantitative consequences
  used downstream are `HilleYosidaRay.norm_smul_stateResolvent_le`
  (`‖r R(r)‖ ≤ r / (r - M)`, a uniform bound for large `r`) and
  `HilleYosidaRay.norm_smul_stateResolvent_sub_le`
  (`‖r R(r) ι d - ι d‖ ≤ (r - M)⁻¹ ‖A d‖`, convergence on the domain);
  together with density of the domain they give the strong convergence
  `r R(r) x → x` of `HilleYosidaRay.tendsto_smul_stateResolvent`.

Nothing here uses the exponential function; the Yosida approximants themselves
are built in the companion modules of `FastDynamo/Dynamics/HilleYosida/`.

The sign convention is the one of `DomainOperator.pencil`: `pencil A z = z ι - A`
as a map `D → X`, so `R(z) = ι ∘ (pencil A z)⁻¹` is the usual resolvent
`(z - A)⁻¹` and the Hille–Yosida bound reads `‖R(r)‖ ≤ (r - M)⁻¹`.
-/

@[expose] public section

namespace FastDynamo

universe u v

variable {X : Type u} {D : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup D] [NormedSpace ℂ D]
  {A : DomainOperator X D} {S : Set ℂ}

/-!
## Identities derived from the two inverse equations
-/

/-- `A R(z) = z R(z) - I` as operators on the ambient space: applying the
operator to the domain-valued resolvent recovers the state resolvent up to the
identity.  This is the right inverse equation rewritten through
`DomainOperator.pencil`. -/
theorem op_comp_inv (h : HasResolventOn A S) {z : ℂ} (hz : z ∈ S) :
    A.op.comp (h.inv z) = z • h.stateResolvent z - ContinuousLinearMap.id ℂ X := by
  have hr := h.right_inv z hz
  have hsplit : (A.pencil z).comp (h.inv z)
      = z • (A.embedding.comp (h.inv z)) - A.op.comp (h.inv z) := by
    ext x; simp [DomainOperator.pencil]
  rw [hsplit] at hr
  rw [HasResolventOn.stateResolvent, ← hr]
  abel

/-- The resolvent at `z` applied to the pencil at another parameter `w`: the
deviation from the identity of the domain is the domain-valued resolvent
composed with the embedding. -/
theorem inv_comp_pencil (h : HasResolventOn A S) {z w : ℂ} (hz : z ∈ S) :
    (h.inv z).comp (A.pencil w)
      = ContinuousLinearMap.id ℂ D + (w - z) • (h.inv z).comp A.embedding := by
  have hpw : A.pencil w = A.pencil z + (w - z) • A.embedding := by
    ext d
    simp [DomainOperator.pencil, sub_smul]
  rw [hpw, ContinuousLinearMap.comp_add, h.left_inv z hz]
  congr 1
  ext d; simp

/-- The resolvent identity in its domain-valued form,
`R(z) - R(w) = (w - z) R(z) R(w)`, with the right-hand resolvent read as a state
resolvent. -/
theorem resolvent_identity (h : HasResolventOn A S) {z w : ℂ} (hz : z ∈ S) (hw : w ∈ S) :
    h.inv z - h.inv w = (w - z) • (h.inv z).comp (h.stateResolvent w) := by
  calc h.inv z - h.inv w
      = ((h.inv z).comp (A.pencil w)).comp (h.inv w) - h.inv w := by
        rw [ContinuousLinearMap.comp_assoc, h.right_inv w hw,
          ContinuousLinearMap.comp_id]
    _ = (ContinuousLinearMap.id ℂ D
          + (w - z) • (h.inv z).comp A.embedding).comp (h.inv w) - h.inv w := by
        rw [inv_comp_pencil h hz]
    _ = (w - z) • (h.inv z).comp (h.stateResolvent w) := by
        ext x; simp [HasResolventOn.stateResolvent]

/-- The resolvent identity on the ambient space:
`R(z) - R(w) = (w - z) R(z) R(w)` for the state resolvents. -/
theorem stateResolvent_identity (h : HasResolventOn A S) {z w : ℂ} (hz : z ∈ S) (hw : w ∈ S) :
    h.stateResolvent z - h.stateResolvent w
      = (w - z) • (h.stateResolvent z).comp (h.stateResolvent w) := by
  have := congrArg (fun T : X →L[ℂ] D ↦ A.embedding.comp T) (resolvent_identity h hz hw)
  simpa [HasResolventOn.stateResolvent, ContinuousLinearMap.comp_sub,
    ContinuousLinearMap.comp_smul, ← ContinuousLinearMap.comp_assoc] using this

/-- `A R(z) ι d = R(z) A d`: the resolvent commutes with the operator on the
domain. -/
theorem op_inv_embedding (h : HasResolventOn A S) {z : ℂ} (hz : z ∈ S) (d : D) :
    A.op (h.inv z (A.embedding d)) = h.stateResolvent z (A.op d) := by
  have hleft := DFunLike.congr_fun (h.left_inv z hz) d
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    DomainOperator.pencil, sub_apply,
    smul_apply, map_sub, map_smul] at hleft
  have hright := DFunLike.congr_fun (op_comp_inv h hz) (A.embedding d)
  simp only [ContinuousLinearMap.comp_apply, sub_apply,
    smul_apply, ContinuousLinearMap.id_apply] at hright
  have hemb := congrArg A.embedding hleft
  simp only [map_sub, map_smul] at hemb
  rw [hright]
  have hkey := sub_eq_iff_eq_add.mp hemb
  rw [HasResolventOn.stateResolvent] at hright ⊢
  simp only [ContinuousLinearMap.comp_apply] at hright ⊢
  rw [hkey]; abel

/-- Two state resolvents of the same certificate commute.  For distinct
parameters this is the resolvent identity read in both orders; for equal
parameters it is reflexivity. -/
theorem HasResolventOn.commute_stateResolvent (h : HasResolventOn A S) {z w : ℂ}
    (hz : z ∈ S) (hw : w ∈ S) :
    Commute (h.stateResolvent z) (h.stateResolvent w) := by
  rcases eq_or_ne z w with rfl | hne
  · exact Commute.refl _
  · have hzw : w - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have key : (w - z) • (h.stateResolvent z).comp (h.stateResolvent w)
        = (w - z) • (h.stateResolvent w).comp (h.stateResolvent z) := by
      rw [← stateResolvent_identity h hz hw,
        show w - z = -(z - w) by ring, neg_smul, ← stateResolvent_identity h hw hz, neg_sub]
    have hcancel := congrArg (fun T : X →L[ℂ] X ↦ (w - z)⁻¹ • T) key
    change h.stateResolvent z * h.stateResolvent w = h.stateResolvent w * h.stateResolvent z
    rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def]
    simpa [smul_smul, inv_mul_cancel₀ hzw] using hcancel

/-!
## The Hille–Yosida ray hypothesis
-/

/--
The hypothesis of the abstract Hille–Yosida generation theorem: the operator `A`
has a two-sided domain-valued resolvent at every real parameter `r > M`, with
the sharp bound `‖R(r)‖ ≤ (r - M)⁻¹` on the induced state resolvent.

The certificate is *wrapped* rather than consumed: a resolvent on a half-plane
is more than is needed here (see `HilleYosidaRay.ofHalfPlane`), and the
generation theorem uses neither the continuity of `z ↦ R(z)` nor any closed
graph or completeness property of the domain.
-/
structure HilleYosidaRay (A : DomainOperator X D) (M : ℝ) where
  /-- The set of parameters on which the resolvent certificate is given. -/
  spectralSet : Set ℂ
  /-- The two-sided domain-valued resolvent certificate. -/
  resolvent : HasResolventOn A spectralSet
  /-- Every real parameter to the right of `M` carries the resolvent. -/
  mem_ofReal : ∀ r : ℝ, M < r → (r : ℂ) ∈ spectralSet
  /-- The Hille–Yosida bound on the real ray. -/
  norm_stateResolvent_le : ∀ r : ℝ, M < r →
    ‖resolvent.stateResolvent (r : ℂ)‖ ≤ (r - M)⁻¹

/-- A resolvent on the half-plane `{Re z > M}` obeying the Hille–Yosida bound
there restricts to a `HilleYosidaRay`: a real `r > M` has `Re r = r`. -/
def HilleYosidaRay.ofHalfPlane {A : DomainOperator X D} {M : ℝ}
    (h : HasResolventOn A {z : ℂ | M < z.re})
    (hb : ∀ z : ℂ, M < z.re → ‖h.stateResolvent z‖ ≤ (z.re - M)⁻¹) :
    HilleYosidaRay A M where
  spectralSet := {z : ℂ | M < z.re}
  resolvent := h
  mem_ofReal := fun r hr ↦ by simpa using hr
  norm_stateResolvent_le := fun r hr ↦ by simpa using hb (r : ℂ) (by simpa using hr)

/-- The uniform bound on the ray: `‖r R(r)‖ ≤ r / (r - M)` for `0 ≤ r` with
`M < r`.  Once `max (2 |M|) 1 + 1 ≤ r` the right-hand side is at most `2`, which
is the form in which the bound enters the density argument of
`HilleYosidaRay.tendsto_smul_stateResolvent`. -/
theorem HilleYosidaRay.norm_smul_stateResolvent_le {M : ℝ} (hy : HilleYosidaRay A M) {r : ℝ}
    (hr : M < r) (h0 : 0 ≤ r) :
    ‖(r : ℝ) • hy.resolvent.stateResolvent (r : ℂ)‖ ≤ r / (r - M) := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg h0, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left (hy.norm_stateResolvent_le r hr) h0

/-- Convergence of `r R(r)` to the identity on the domain, quantitatively:
`r R(r) ι d - ι d = R(r) A d`, whose norm is at most `(r - M)⁻¹ ‖A d‖`. -/
theorem HilleYosidaRay.norm_smul_stateResolvent_sub_le {M : ℝ} (hy : HilleYosidaRay A M)
    {r : ℝ} (hr : M < r) (d : D) :
    ‖(r : ℝ) • hy.resolvent.stateResolvent (r : ℂ) (A.embedding d) - A.embedding d‖
      ≤ (r - M)⁻¹ * ‖A.op d‖ := by
  have hmem := hy.mem_ofReal r hr
  have hright := DFunLike.congr_fun (op_comp_inv hy.resolvent hmem) (A.embedding d)
  simp only [ContinuousLinearMap.comp_apply, sub_apply,
    smul_apply, ContinuousLinearMap.id_apply] at hright
  have hkey : (r : ℝ) • hy.resolvent.stateResolvent (r : ℂ) (A.embedding d) - A.embedding d
      = hy.resolvent.stateResolvent (r : ℂ) (A.op d) := by
    rw [← Complex.coe_smul, ← hright, op_inv_embedding hy.resolvent hmem d]
  rw [hkey]
  exact le_trans (ContinuousLinearMap.le_opNorm _ _)
    (mul_le_mul_of_nonneg_right (hy.norm_stateResolvent_le r hr) (norm_nonneg _))

/-- Strong convergence `r R(r) x → x` as `r → ∞`, for every ambient state `x`,
when the domain is dense.  On the range of the embedding this is
`HilleYosidaRay.norm_smul_stateResolvent_sub_le`; the general case follows by an
`ε/3` argument from the uniform bound `‖r R(r)‖ ≤ r / (r - M) ≤ 2`, valid once
`max (2 |M|) 1 + 1 ≤ r`. -/
theorem HilleYosidaRay.tendsto_smul_stateResolvent {M : ℝ} (hy : HilleYosidaRay A M)
    (hdense : DenseRange A.embedding) (x : X) :
    Filter.Tendsto (fun r : ℝ ↦ (r : ℝ) • hy.resolvent.stateResolvent (r : ℂ) x)
      Filter.atTop (nhds x) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨d, hd⟩ : ∃ d : D, ‖A.embedding d - x‖ < ε / 6 := by
    obtain ⟨d, hdd⟩ := Metric.denseRange_iff.mp hdense x (ε / 6) (by linarith)
    exact ⟨d, by rwa [← dist_eq_norm, dist_comm]⟩
  refine ⟨max (max (2 * |M|) 1 + 1) (M + 2 * ‖A.op d‖ / ε + 1), fun r hrN ↦ ?_⟩
  have hr₁ : max (2 * |M|) 1 + 1 ≤ r := le_trans (le_max_left _ _) hrN
  have hr₂ : M + 2 * ‖A.op d‖ / ε + 1 ≤ r := le_trans (le_max_right _ _) hrN
  have habs : 2 * |M| ≤ max (2 * |M|) 1 := le_max_left _ _
  have hone : (1 : ℝ) ≤ max (2 * |M|) 1 := le_max_right _ _
  have hMabs : M ≤ |M| := le_abs_self M
  have hlt : M < r := by linarith
  have hrM : 0 < r - M := by linarith
  have h0 : 0 ≤ r := by linarith
  -- the uniform bound `‖r R(r)‖ ≤ 2`
  have hunif : ‖(r : ℝ) • hy.resolvent.stateResolvent (r : ℂ)‖ ≤ 2 := by
    refine le_trans (hy.norm_smul_stateResolvent_le hlt h0) ?_
    rw [div_le_iff₀ hrM]
    linarith
  -- the domain estimate
  have hdom : ‖(r : ℝ) • hy.resolvent.stateResolvent (r : ℂ) (A.embedding d)
      - A.embedding d‖ < ε / 2 := by
    refine lt_of_le_of_lt (hy.norm_smul_stateResolvent_sub_le hlt d) ?_
    rw [inv_mul_eq_div, div_lt_iff₀ hrM]
    have hge : 2 * ‖A.op d‖ / ε + 1 ≤ r - M := by linarith
    have hmul : ε / 2 * (2 * ‖A.op d‖ / ε + 1) ≤ ε / 2 * (r - M) :=
      mul_le_mul_of_nonneg_left hge (by linarith)
    have heq : ε / 2 * (2 * ‖A.op d‖ / ε + 1) = ‖A.op d‖ + ε / 2 := by
      field_simp
    linarith
  -- the three-term decomposition
  have hdecomp : (r : ℝ) • hy.resolvent.stateResolvent (r : ℂ) x - x
      = ((r : ℝ) • hy.resolvent.stateResolvent (r : ℂ)) (x - A.embedding d)
        + ((r : ℝ) • hy.resolvent.stateResolvent (r : ℂ) (A.embedding d) - A.embedding d)
        + (A.embedding d - x) := by
    simp only [smul_apply, map_sub]
    abel
  have hsplit : ‖((r : ℝ) • hy.resolvent.stateResolvent (r : ℂ)) (x - A.embedding d)‖
      ≤ 2 * ‖A.embedding d - x‖ := by
    refine le_trans (ContinuousLinearMap.le_opNorm _ _) ?_
    rw [norm_sub_rev]
    exact mul_le_mul_of_nonneg_right hunif (norm_nonneg _)
  rw [dist_eq_norm, hdecomp]
  refine lt_of_le_of_lt norm_add₃_le ?_
  linarith [hsplit, hdom, hd]

/-- The domain-valued resolvent inverts the pencil on the ray: `R(r) (r - A) d = d`
for every `d` in the domain and every real `r > M`. -/
theorem HilleYosidaRay.inv_pencil {M : ℝ} (hy : HilleYosidaRay A M) {r : ℝ} (hr : M < r)
    (d : D) : hy.resolvent.inv (r : ℂ) (A.pencil (r : ℂ) d) = d := by
  simpa using DFunLike.congr_fun (hy.resolvent.left_inv (r : ℂ) (hy.mem_ofReal r hr)) d

end FastDynamo
