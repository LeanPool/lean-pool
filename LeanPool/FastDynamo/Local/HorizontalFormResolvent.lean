/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Local.HorizontalModeIsolation
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The resolvent of the horizontal form operator

The analytic Fredholm paragraph of §2.3 of the paper reads

> Where it is invertible, its inverse restricted to `L² ⊂ V*` equals `(z - A_w)^{-1}`.

This module performs that restriction.  The repository's resolvent interface is
`HasResolventOn` of `FastDynamo/Operator/Domain.lean`: a *domain-valued* inverse
`L²(ℝ²;ℂ²) → D(A_w)`, two-sided on the given parameter set and continuous there.  Since the
graph domain `D(A_w)` carries the product norm of `H¹ × L²`, this is exactly the paper's
`L² → H¹` resolvent bound together with the stored weak identity.

Near an eigenvalue the pencil form is not coercive, only invertible, so Lax-Milgram does not
apply: the generic first section takes an arbitrary solution map of the weak pencil equation
and rebuilds the graph pair `f ↦ (u, f - z j u)` from it.

The second section instantiates this at the horizontal pencil, using the Fredholm
factorisation `𝔸_w(z) = F_z(1 - K(z))` of `FastDynamo/Local/HorizontalFormCompactness.lean`
to write the solution map as `(1 - K(z))⁻¹G_z⁻¹F_1⁻¹`, which is manifestly holomorphic in `z`
wherever it exists.  The same factorisation shows that the state resolvent differs from the
free one by a compact operator; that is what turns the Riesz projection on an isolating
contour into a finite-rank projection in `FastDynamo/Local/HorizontalModeContour.lean`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

/-! ## Generic: a resolvent from an invertible pencil form -/

section FormPencilResolvent

universe u v

variable {V : Type u} {X : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup X] [InnerProductSpace ℂ X]

/-- The graph pair `f ↦ (R f, f - z • j (R f))` attached to a solution map `R : X → V` of the
weak pencil equation at `z`. -/
def formPencilGraphPair (j : V →L[ℂ] X) (z : ℂ) (R : X →L[ℂ] V) : X →L[ℂ] V × X :=
  (ContinuousLinearMap.inl ℂ V X).comp R +
    (ContinuousLinearMap.inr ℂ V X).comp
      (ContinuousLinearMap.id ℂ X - z • j.comp R)

omit [CompleteSpace V] in
/-- Evaluation of the graph pair. -/
@[simp] theorem formPencilGraphPair_apply (j : V →L[ℂ] X) (z : ℂ) (R : X →L[ℂ] V) (f : X) :
    formPencilGraphPair j z R f = (R f, f - z • j (R f)) := by
  refine Prod.ext ?_ ?_ <;>
    simp [formPencilGraphPair]

omit [CompleteSpace V] in
/-- The graph pair lies in the maximal graph domain of `a` exactly because `R f` solves the
weak pencil equation at `z`. -/
theorem formPencilGraphPair_mem (j : V →L[ℂ] X) (a : ComplexForm V) (z : ℂ) (R : X →L[ℂ] V)
    (hR : ∀ (f : X) (phi : V),
      a (R f) phi + z * inner ℂ (j phi) (j (R f)) = inner ℂ (j phi) f)
    (f : X) : formPencilGraphPair j z R f ∈ AssociatedFormProdDomain j a := by
  rw [mem_associatedFormProdDomain_iff_forall]
  intro phi
  have hfst : (formPencilGraphPair j z R f).1 = R f := by
    rw [formPencilGraphPair_apply]
  have hsnd : (formPencilGraphPair j z R f).2 = f - z • j (R f) := by
    rw [formPencilGraphPair_apply]
  rw [hfst, hsnd, inner_sub_right, inner_smul_right]
  linear_combination hR f phi

/-- The domain-valued solution map built from a solution map of the weak pencil equation. -/
def formPencilDomainInverse (j : V →L[ℂ] X) (a : ComplexForm V) (z : ℂ) (R : X →L[ℂ] V)
    (hR : ∀ (f : X) (phi : V),
      a (R f) phi + z * inner ℂ (j phi) (j (R f)) = inner ℂ (j phi) f) :
    X →L[ℂ] AssociatedFormProdDomain j a :=
  (formPencilGraphPair j z R).codRestrict (AssociatedFormProdDomain j a)
    (formPencilGraphPair_mem j a z R hR)

omit [CompleteSpace V] in
/-- The underlying pair of the domain-valued solution map. -/
@[simp] theorem formPencilDomainInverse_val (j : V →L[ℂ] X) (a : ComplexForm V) (z : ℂ)
    (R : X →L[ℂ] V)
    (hR : ∀ (f : X) (phi : V),
      a (R f) phi + z * inner ℂ (j phi) (j (R f)) = inner ℂ (j phi) f) (f : X) :
    (formPencilDomainInverse j a z R hR f).1 = formPencilGraphPair j z R f :=
  rfl

omit [CompleteSpace V] in
/-- The domain-valued solution map is a right inverse of the operator pencil. -/
theorem formPencilDomainInverse_right_apply (j : V →L[ℂ] X) (hj : Function.Injective j)
    (hdense : DenseRange j) (a : ComplexForm V) (z : ℂ) (R : X →L[ℂ] V)
    (hR : ∀ (f : X) (phi : V),
      a (R f) phi + z * inner ℂ (j phi) (j (R f)) = inner ℂ (j phi) f) (f : X) :
    (associatedFormProdOperator j hj hdense a).pencil z
        (formPencilDomainInverse j a z R hR f) = f := by
  have hfst : (formPencilDomainInverse j a z R hR f).1.1 = R f := by
    rw [formPencilDomainInverse_val, formPencilGraphPair_apply]
  have hsnd : (formPencilDomainInverse j a z R hR f).1.2 = f - z • j (R f) := by
    rw [formPencilDomainInverse_val, formPencilGraphPair_apply]
  have hpencil : (associatedFormProdOperator j hj hdense a).pencil z
      (formPencilDomainInverse j a z R hR f) =
      z • j (formPencilDomainInverse j a z R hR f).1.1 +
        (formPencilDomainInverse j a z R hR f).1.2 := by
    simp only [DomainOperator.pencil, sub_apply, smul_apply,
      associatedFormProdOperator_embedding_apply, associatedFormProdOperator_op_apply]
    module
  rw [hpencil, hfst, hsnd]
  module

omit [CompleteSpace V] in
/-- Injectivity of the pencil form identifies the first graph coordinate of any graph element
with the solution attached to its pencil image. -/
theorem formPencilDomainInverse_fst_of_injective (j : V →L[ℂ] X) (hj : Function.Injective j)
    (hdense : DenseRange j) (a : ComplexForm V) (z : ℂ) (R : X →L[ℂ] V)
    (hR : ∀ (f : X) (phi : V),
      a (R f) phi + z * inner ℂ (j phi) (j (R f)) = inner ℂ (j phi) f)
    (hinj : ∀ e : V, (∀ phi : V, a e phi + z * inner ℂ (j phi) (j e) = 0) → e = 0)
    (d : AssociatedFormProdDomain j a) :
    R ((associatedFormProdOperator j hj hdense a).pencil z d) = d.1.1 := by
  set f : X := (associatedFormProdOperator j hj hdense a).pencil z d with hf
  have hfval : f = z • j d.1.1 + d.1.2 := by
    rw [hf]
    simp only [DomainOperator.pencil, sub_apply, smul_apply,
      associatedFormProdOperator_embedding_apply, associatedFormProdOperator_op_apply]
    module
  have hdiff : R f - d.1.1 = 0 := by
    apply hinj
    intro phi
    have h1 := hR f phi
    have h2 := associatedFormProdDomain_relation_apply j a d phi
    have h3 : inner ℂ (j phi) f =
        z * inner ℂ (j phi) (j d.1.1) + inner ℂ (j phi) d.1.2 := by
      rw [hfval, inner_add_right, inner_smul_right]
    have h4 : a (R f - d.1.1) phi = a (R f) phi - a d.1.1 phi := by
      rw [map_sub]
      rfl
    have h5 : inner ℂ (j phi) (j (R f - d.1.1)) =
        inner ℂ (j phi) (j (R f)) - inner ℂ (j phi) (j d.1.1) := by
      rw [map_sub, inner_sub_right]
    rw [h4, h5]
    linear_combination h1 + h3 - h2
  exact sub_eq_zero.mp hdiff

omit [CompleteSpace V] in
/-- The domain-valued solution map is a left inverse of the operator pencil. -/
theorem formPencilDomainInverse_left_apply (j : V →L[ℂ] X) (hj : Function.Injective j)
    (hdense : DenseRange j) (a : ComplexForm V) (z : ℂ) (R : X →L[ℂ] V)
    (hR : ∀ (f : X) (phi : V),
      a (R f) phi + z * inner ℂ (j phi) (j (R f)) = inner ℂ (j phi) f)
    (hinj : ∀ e : V, (∀ phi : V, a e phi + z * inner ℂ (j phi) (j e) = 0) → e = 0)
    (d : AssociatedFormProdDomain j a) :
    formPencilDomainInverse j a z R hR
        ((associatedFormProdOperator j hj hdense a).pencil z d) = d := by
  set f : X := (associatedFormProdOperator j hj hdense a).pencil z d with hf
  have hfval : f = z • j d.1.1 + d.1.2 := by
    rw [hf]
    simp only [DomainOperator.pencil, sub_apply, smul_apply,
      associatedFormProdOperator_embedding_apply, associatedFormProdOperator_op_apply]
    module
  have hRf : R f = d.1.1 :=
    formPencilDomainInverse_fst_of_injective j hj hdense a z R hR hinj d
  apply Subtype.ext
  rw [formPencilDomainInverse_val, formPencilGraphPair_apply, hRf]
  refine Prod.ext rfl ?_
  change f - z • j d.1.1 = d.1.2
  rw [hfval]
  module

/-- The chosen domain-valued inverse family, junk outside the parameter set. -/
def formPencilInvFamily (j : V →L[ℂ] X) (a : ComplexForm V) {S : Set ℂ}
    (R : ℂ → X →L[ℂ] V)
    (hR : ∀ z ∈ S, ∀ (f : X) (phi : V),
      a (R z f) phi + z * inner ℂ (j phi) (j (R z f)) = inner ℂ (j phi) f)
    (z : ℂ) : X →L[ℂ] AssociatedFormProdDomain j a :=
  @dite _ (z ∈ S) (Classical.propDecidable (z ∈ S))
    (fun hzS => formPencilDomainInverse j a z (R z) (hR z hzS)) (fun _ => 0)

omit [CompleteSpace V] in
/-- On the parameter set the chosen family is the domain-valued solution map. -/
theorem formPencilInvFamily_of_mem (j : V →L[ℂ] X) (a : ComplexForm V) {S : Set ℂ}
    (R : ℂ → X →L[ℂ] V)
    (hR : ∀ z ∈ S, ∀ (f : X) (phi : V),
      a (R z f) phi + z * inner ℂ (j phi) (j (R z f)) = inner ℂ (j phi) f)
    {z : ℂ} (hz : z ∈ S) :
    formPencilInvFamily j a R hR z = formPencilDomainInverse j a z (R z) (hR z hz) :=
  dite_eq_left hz

/-- Post-composition with the inclusion of a submodule preserves the operator norm. -/
theorem norm_subtypeL_comp {M E : Type*} [NormedAddCommGroup M] [NormedSpace ℂ M]
    [NormedAddCommGroup E] [NormedSpace ℂ E] (p : Submodule ℂ E) (g : M →L[ℂ] p) :
    ‖p.subtypeL.comp g‖ = ‖g‖ := by
  refine le_antisymm ?_ ?_
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg g) fun x => ?_
    have h : ‖(p.subtypeL.comp g) x‖ = ‖g x‖ := Submodule.norm_coe (g x)
    rw [h]
    exact g.le_opNorm x
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    have h : ‖g x‖ = ‖(p.subtypeL.comp g) x‖ := (Submodule.norm_coe (g x)).symm
    rw [h]
    exact (p.subtypeL.comp g).le_opNorm x

/-- Post-composition with the inclusion of a submodule is an isometry of operator spaces. -/
theorem isometry_subtypeL_comp {M E : Type*} [NormedAddCommGroup M] [NormedSpace ℂ M]
    [NormedAddCommGroup E] [NormedSpace ℂ E] (p : Submodule ℂ E) :
    Isometry (fun g : M →L[ℂ] p => p.subtypeL.comp g) := by
  rw [isometry_iff_dist_eq]
  intro g h
  rw [dist_eq_norm, dist_eq_norm, ← ContinuousLinearMap.comp_sub, norm_subtypeL_comp]

/-- **The resolvent of the maximal associated operator from an invertible pencil form.**  On
a parameter set where the weak pencil equation has a bounded solution map depending
continuously on `z`, and where the pencil form is injective, the operator `A_a` has a
domain-valued resolvent. -/
def formPencilHasResolventOn (j : V →L[ℂ] X) (hj : Function.Injective j)
    (hdense : DenseRange j) (a : ComplexForm V) {S : Set ℂ} (R : ℂ → X →L[ℂ] V)
    (hR : ∀ z ∈ S, ∀ (f : X) (phi : V),
      a (R z f) phi + z * inner ℂ (j phi) (j (R z f)) = inner ℂ (j phi) f)
    (hinj : ∀ z ∈ S, ∀ e : V, (∀ phi : V, a e phi + z * inner ℂ (j phi) (j e) = 0) → e = 0)
    (hcont : ContinuousOn R S) :
    HasResolventOn (associatedFormProdOperator j hj hdense a) S where
  inv := formPencilInvFamily j a R hR
  left_inv := by
    intro z hz
    rw [formPencilInvFamily_of_mem j a R hR hz]
    refine ContinuousLinearMap.ext fun d => ?_
    exact formPencilDomainInverse_left_apply j hj hdense a z (R z) (hR z hz) (hinj z hz) d
  right_inv := by
    intro z hz
    rw [formPencilInvFamily_of_mem j a R hR hz]
    refine ContinuousLinearMap.ext fun f => ?_
    exact formPencilDomainInverse_right_apply j hj hdense a z (R z) (hR z hz) f
  continuousOn := by
    rw [← (isometry_subtypeL_comp (M := X) (AssociatedFormProdDomain j a)).comp_continuousOn_iff]
    have hpair : ContinuousOn (fun z : ℂ => formPencilGraphPair j z (R z)) S := by
      have h1 : ContinuousOn (fun z : ℂ => j.comp (R z)) S :=
        ((ContinuousLinearMap.compL ℂ X V X j).continuous).comp_continuousOn hcont
      have h2 : ContinuousOn (fun z : ℂ => z • j.comp (R z)) S :=
        continuousOn_id.smul h1
      have h3 : ContinuousOn
          (fun z : ℂ => ContinuousLinearMap.id ℂ X - z • j.comp (R z)) S :=
        continuousOn_const.sub h2
      have h4 : ContinuousOn
          (fun z : ℂ => (ContinuousLinearMap.inl ℂ V X).comp (R z)) S :=
        ((ContinuousLinearMap.compL ℂ X V (V × X))
          (ContinuousLinearMap.inl ℂ V X)).continuous.comp_continuousOn hcont
      have h5 : ContinuousOn
          (fun z : ℂ => (ContinuousLinearMap.inr ℂ V X).comp
            (ContinuousLinearMap.id ℂ X - z • j.comp (R z))) S :=
        ((ContinuousLinearMap.compL ℂ X X (V × X))
          (ContinuousLinearMap.inr ℂ V X)).continuous.comp_continuousOn h3
      exact h4.add h5
    refine hpair.congr fun z hz => ?_
    change (AssociatedFormProdDomain j a).subtypeL.comp (formPencilInvFamily j a R hR z) =
      formPencilGraphPair j z (R z)
    rw [formPencilInvFamily_of_mem j a R hR hz]
    rfl

omit [CompleteSpace V] in
/-- The chosen inverse of the constructed resolvent, on the parameter set. -/
theorem formPencilHasResolventOn_inv (j : V →L[ℂ] X) (hj : Function.Injective j)
    (hdense : DenseRange j) (a : ComplexForm V) {S : Set ℂ} (R : ℂ → X →L[ℂ] V)
    (hR : ∀ z ∈ S, ∀ (f : X) (phi : V),
      a (R z f) phi + z * inner ℂ (j phi) (j (R z f)) = inner ℂ (j phi) f)
    (hinj : ∀ z ∈ S, ∀ e : V, (∀ phi : V, a e phi + z * inner ℂ (j phi) (j e) = 0) → e = 0)
    (hcont : ContinuousOn R S) {z : ℂ} (hz : z ∈ S) :
    (formPencilHasResolventOn j hj hdense a R hR hinj hcont).inv z =
      formPencilDomainInverse j a z (R z) (hR z hz) :=
  formPencilInvFamily_of_mem j a R hR hz

omit [CompleteSpace V] in
/-- The state resolvent of the constructed resolvent is `j ∘ R`. -/
theorem formPencilHasResolventOn_stateResolvent (j : V →L[ℂ] X) (hj : Function.Injective j)
    (hdense : DenseRange j) (a : ComplexForm V) {S : Set ℂ} (R : ℂ → X →L[ℂ] V)
    (hR : ∀ z ∈ S, ∀ (f : X) (phi : V),
      a (R z f) phi + z * inner ℂ (j phi) (j (R z f)) = inner ℂ (j phi) f)
    (hinj : ∀ z ∈ S, ∀ e : V, (∀ phi : V, a e phi + z * inner ℂ (j phi) (j e) = 0) → e = 0)
    (hcont : ContinuousOn R S) {z : ℂ} (hz : z ∈ S) :
    (formPencilHasResolventOn j hj hdense a R hR hinj hcont).stateResolvent z =
      j.comp (R z) := by
  refine ContinuousLinearMap.ext fun f => ?_
  change (associatedFormProdOperator j hj hdense a).embedding
      ((formPencilHasResolventOn j hj hdense a R hR hinj hcont).inv z f) = j (R z f)
  rw [formPencilHasResolventOn_inv j hj hdense a R hR hinj hcont hz]
  change j (formPencilDomainInverse j a z (R z) (hR z hz) f).1.1 = j (R z f)
  rw [formPencilDomainInverse_val, formPencilGraphPair_apply]

end FormPencilResolvent

namespace HorizontalWeakForm

/-! ## The inverse of the horizontal pencil form -/

/-- The free part `F_z⁻¹ = G_z⁻¹F_1⁻¹ : V* → V` of the inverse. -/
def horizontalFreeFormInverse (N : ℝ) (z : ℂ) :
    ComplexAntiDual WholePlaneC2H1 →L[ℂ] WholePlaneC2H1 :=
  (freeHorizontalNormalizer N z).inverse.comp (freeHorizontalBaseInverse N)

/-- The inverse `𝔸_w(z)⁻¹ : V* → V` of the shifted form operator, written through the
Fredholm factorisation `𝔸_w(z) = F_z(1 - K(z))` as `(1 - K(z))⁻¹F_z⁻¹`. -/
def horizontalPencilFormInverse (N : ℝ) (w : WholePlaneC3LInf) (z : ℂ) :
    ComplexAntiDual WholePlaneC2H1 →L[ℂ] WholePlaneC2H1 :=
  (AnalyticFredholm.compactPencil (horizontalFredholmKernel N w) z).inverse.comp
    (horizontalFreeFormInverse N z)

/-- `F_z` undoes `F_z⁻¹` on the open right half plane. -/
theorem freeHorizontalForm_freeFormInverse (N : ℝ) {z : ℂ} (hz : 0 < z.re)
    (g : ComplexAntiDual WholePlaneC2H1) :
    freeHorizontalForm N z (horizontalFreeFormInverse N z g) = g :=
  freeHorizontalForm_normalizerInverse N hz g

/-- `F_z⁻¹` undoes `F_z` on the open right half plane. -/
theorem horizontalFreeFormInverse_freeHorizontalForm (N : ℝ) {z : ℂ} (hz : 0 < z.re)
    (b : WholePlaneC2H1) :
    horizontalFreeFormInverse N z (freeHorizontalForm N z b) = b :=
  (freeHorizontalNormalizer_isInvertible N hz).inverse_apply_self b

/-- The Fredholm factorisation `𝔸_w(z) = F_z(1 - K(z))`, evaluated at a vector. -/
theorem horizontalPencilForm_apply_eq_free (N : ℝ) (w : WholePlaneC3LInf) {z : ℂ}
    (hz : 0 < z.re) (b : WholePlaneC2H1) :
    horizontalPencilForm N w z b =
      freeHorizontalForm N z
        (AnalyticFredholm.compactPencil (horizontalFredholmKernel N w) z b) :=
  (congrArg (fun T : WholePlaneC2H1 →L[ℂ] ComplexAntiDual WholePlaneC2H1 => T b)
    (freeHorizontalForm_comp_compactPencil N w hz)).symm

/-- The pencil inverse is a right inverse of `𝔸_w(z)`. -/
theorem horizontalPencilForm_pencilFormInverse (N : ℝ) (w : WholePlaneC3LInf) {z : ℂ}
    (hz : 0 < z.re) (hinv : (horizontalPencilForm N w z).IsInvertible)
    (g : ComplexAntiDual WholePlaneC2H1) :
    horizontalPencilForm N w z (horizontalPencilFormInverse N w z g) = g := by
  have hG := (horizontalPencilForm_isInvertible_iff N w hz).mp hinv
  have hself : AnalyticFredholm.compactPencil (horizontalFredholmKernel N w) z
      (horizontalPencilFormInverse N w z g) = horizontalFreeFormInverse N z g :=
    hG.self_apply_inverse (horizontalFreeFormInverse N z g)
  calc horizontalPencilForm N w z (horizontalPencilFormInverse N w z g)
      = freeHorizontalForm N z
          (AnalyticFredholm.compactPencil (horizontalFredholmKernel N w) z
            (horizontalPencilFormInverse N w z g)) :=
        horizontalPencilForm_apply_eq_free N w hz _
    _ = freeHorizontalForm N z (horizontalFreeFormInverse N z g) :=
        congrArg (fun y : WholePlaneC2H1 => freeHorizontalForm N z y) hself
    _ = g := freeHorizontalForm_freeFormInverse N hz g

/-- The pencil inverse is a left inverse of `𝔸_w(z)`. -/
theorem horizontalPencilFormInverse_pencilForm (N : ℝ) (w : WholePlaneC3LInf) {z : ℂ}
    (hz : 0 < z.re) (hinv : (horizontalPencilForm N w z).IsInvertible)
    (b : WholePlaneC2H1) :
    horizontalPencilFormInverse N w z (horizontalPencilForm N w z b) = b := by
  have hG := (horizontalPencilForm_isInvertible_iff N w hz).mp hinv
  have hfac := horizontalPencilForm_apply_eq_free N w hz b
  have hnorm := horizontalFreeFormInverse_freeHorizontalForm N hz
    (AnalyticFredholm.compactPencil (horizontalFredholmKernel N w) z b)
  have hstep : horizontalFreeFormInverse N z (horizontalPencilForm N w z b) =
      AnalyticFredholm.compactPencil (horizontalFredholmKernel N w) z b :=
    (congrArg (fun g : ComplexAntiDual WholePlaneC2H1 => horizontalFreeFormInverse N z g)
      hfac).trans hnorm
  calc horizontalPencilFormInverse N w z (horizontalPencilForm N w z b)
      = (AnalyticFredholm.compactPencil (horizontalFredholmKernel N w) z).inverse
          (horizontalFreeFormInverse N z (horizontalPencilForm N w z b)) := rfl
    _ = (AnalyticFredholm.compactPencil (horizontalFredholmKernel N w) z).inverse
          (AnalyticFredholm.compactPencil (horizontalFredholmKernel N w) z b) :=
        congrArg
          (fun y : WholePlaneC2H1 =>
            (AnalyticFredholm.compactPencil (horizontalFredholmKernel N w) z).inverse y) hstep
    _ = b := hG.inverse_apply_self b

/-! ## The solution map and its analyticity -/

/-- The base solution map `F_1⁻¹` composed with the `L² → V*` pivot. -/
def horizontalBaseSolution (N : ℝ) : WholePlaneC2L2 →L[ℂ] WholePlaneC2H1 :=
  (freeHorizontalBaseInverse N).comp (associatedFormPivot (wholePlaneH1Embedding C2))

/-- The free solution map `F_z⁻¹` composed with the pivot, as a map `L² → H¹`. -/
def horizontalFreeSolution (N : ℝ) (z : ℂ) : WholePlaneC2L2 →L[ℂ] WholePlaneC2H1 :=
  (freeHorizontalNormalizer N z).inverse.comp (horizontalBaseSolution N)

/-- The solution map `L²(ℝ²;ℂ²) → H¹(ℝ²;ℂ²)` of the pencil equation at `z`. -/
def horizontalFormSolution (N : ℝ) (w : WholePlaneC3LInf) (z : ℂ) :
    WholePlaneC2L2 →L[ℂ] WholePlaneC2H1 :=
  (AnalyticFredholm.compactPencil (horizontalFredholmKernel N w) z).inverse.comp
    (horizontalFreeSolution N z)

/-- The weak pencil equation solved by the solution map. -/
theorem horizontalFormSolution_weak (N : ℝ) (w : WholePlaneC3LInf) {z : ℂ}
    (hz : 0 < z.re) (hinv : (horizontalPencilForm N w z).IsInvertible)
    (f : WholePlaneC2L2) (phi : WholePlaneC2H1) :
    horizontalWeakForm N w (horizontalFormSolution N w z f) phi +
        z * inner ℂ (wholePlaneH1Embedding C2 phi)
          (wholePlaneH1Embedding C2 (horizontalFormSolution N w z f)) =
      inner ℂ (wholePlaneH1Embedding C2 phi) f := by
  have hsol : horizontalPencilForm N w z (horizontalFormSolution N w z f) =
      associatedFormPivot (wholePlaneH1Embedding C2) f :=
    horizontalPencilForm_pencilFormInverse N w hz hinv
      (associatedFormPivot (wholePlaneH1Embedding C2) f)
  have happ := congrArg (fun g : ComplexAntiDual WholePlaneC2H1 => g phi) hsol
  have hleft := horizontalPencilForm_apply N w z (horizontalFormSolution N w z f) phi
  have hright : associatedFormPivot (wholePlaneH1Embedding C2) f phi =
      inner ℂ (wholePlaneH1Embedding C2 phi) f :=
    associatedFormPivot_apply (wholePlaneH1Embedding C2) f phi
  rw [← hleft, ← hright]
  exact happ

/-- Injectivity of the pencil form in the weak formulation. -/
theorem horizontalPencilForm_injective_weak (N : ℝ) (w : WholePlaneC3LInf) {z : ℂ}
    (hz : 0 < z.re) (hinv : (horizontalPencilForm N w z).IsInvertible)
    (e : WholePlaneC2H1)
    (he : ∀ phi : WholePlaneC2H1,
      horizontalWeakForm N w e phi +
        z * inner ℂ (wholePlaneH1Embedding C2 phi) (wholePlaneH1Embedding C2 e) = 0) :
    e = 0 := by
  have hzero : horizontalPencilForm N w z e = 0 := by
    refine ContinuousLinearMap.ext fun phi => ?_
    rw [horizontalPencilForm_apply]
    exact he phi
  have h := horizontalPencilFormInverse_pencilForm N w hz hinv e
  rw [hzero, map_zero] at h
  exact h.symm

/-- The free solution map is holomorphic on the open right half plane. -/
theorem analyticAt_horizontalFreeSolution (N : ℝ) {z : ℂ} (hz : 0 < z.re) :
    AnalyticAt ℂ (horizontalFreeSolution N) z :=
  FiniteDimensionalSchur.analyticAt_clm_comp
    (AnalyticFredholm.analyticAt_inverse (analyticAt_freeHorizontalNormalizer N z)
      (freeHorizontalNormalizer_isInvertible N hz))
    analyticAt_const

/-- The solution map is holomorphic wherever the pencil form is invertible. -/
theorem analyticAt_horizontalFormSolution (N : ℝ) (w : WholePlaneC3LInf) {z : ℂ}
    (hz : 0 < z.re) (hinv : (horizontalPencilForm N w z).IsInvertible) :
    AnalyticAt ℂ (horizontalFormSolution N w) z :=
  FiniteDimensionalSchur.analyticAt_clm_comp
    (AnalyticFredholm.analyticAt_inverse
      (AnalyticFredholm.analyticAt_compactPencil
        (analyticAt_horizontalFredholmKernel N w hz))
      ((horizontalPencilForm_isInvertible_iff N w hz).mp hinv))
    (analyticAt_horizontalFreeSolution N hz)

/-! ## The resolvent -/

/-- **The resolvent of `A_w`.**  On any parameter set inside the open right half plane on
which the shifted form operator `𝔸_w(z)` is an isomorphism `V → V*`, the operator `A_w` has a
domain-valued resolvent `L²(ℝ²;ℂ²) → D(A_w) ⊂ H¹(ℝ²;ℂ²) × L²(ℝ²;ℂ²)`, continuous in
the spectral parameter.  This is the restriction step of the analytic Fredholm paragraph of
§2.3. -/
def horizontalHasResolventOn (N : ℝ) (w : WholePlaneC3LInf) (S : Set ℂ)
    (hS : ∀ z ∈ S, 0 < z.re)
    (hSinv : ∀ z ∈ S, (horizontalPencilForm N w z).IsInvertible) :
    HasResolventOn (horizontalFormOperator N w) S :=
  formPencilHasResolventOn (wholePlaneH1Embedding C2) wholePlaneC2H1Embedding_injective
    denseRange_wholePlaneC2H1Embedding (horizontalWeakForm N w)
    (horizontalFormSolution N w)
    (fun z hz f phi => horizontalFormSolution_weak N w (hS z hz) (hSinv z hz) f phi)
    (fun z hz e he => horizontalPencilForm_injective_weak N w (hS z hz) (hSinv z hz) e he)
    (fun z hz =>
      ((analyticAt_horizontalFormSolution N w (hS z hz)
        (hSinv z hz)).continuousAt).continuousWithinAt)

/-- The state resolvent of `A_w` is `j ∘ 𝔸_w(z)⁻¹ ∘ pivot`. -/
theorem horizontalHasResolventOn_stateResolvent (N : ℝ) (w : WholePlaneC3LInf) (S : Set ℂ)
    (hS : ∀ z ∈ S, 0 < z.re)
    (hSinv : ∀ z ∈ S, (horizontalPencilForm N w z).IsInvertible) {z : ℂ} (hz : z ∈ S) :
    (horizontalHasResolventOn N w S hS hSinv).stateResolvent z =
      (wholePlaneH1Embedding C2).comp (horizontalFormSolution N w z) :=
  formPencilHasResolventOn_stateResolvent _ _ _ _ _ _ _ _ hz

/-! ## The free reference resolvent and the compact difference -/

/-- The free state resolvent `j F_z⁻¹ (pivot j) : L² → L²`, the resolvent of `Δ_⊥ - N²`.  It
is holomorphic on the whole open right half plane and is the reference family in the
finite-rank argument for the Riesz projection. -/
def horizontalFreeStateResolvent (N : ℝ) (z : ℂ) : WholePlaneC2L2 →L[ℂ] WholePlaneC2L2 :=
  (wholePlaneH1Embedding C2).comp (horizontalFreeSolution N z)

/-- The inverse of a compact pencil differs from the identity by a compact operator. -/
theorem inverse_compactPencil_sub_id {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (K : ℂ → (H →L[ℂ] H)) {z : ℂ}
    (hinv : (AnalyticFredholm.compactPencil K z).IsInvertible) (x : H) :
    (AnalyticFredholm.compactPencil K z).inverse x - x =
      (AnalyticFredholm.compactPencil K z).inverse (K z x) := by
  have h1 : (AnalyticFredholm.compactPencil K z).inverse x -
      (AnalyticFredholm.compactPencil K z).inverse (K z x) = x := by
    rw [← map_sub]
    exact hinv.inverse_apply_self x
  linear_combination (norm := module) h1

/-- The state resolvent of `A_w` differs from the free one by the compact family
`j (1 - K(z))⁻¹K(z)F_z⁻¹(pivot j)`. -/
theorem horizontalStateResolvent_sub_free (N : ℝ) (w : WholePlaneC3LInf) {z : ℂ}
    (hz : 0 < z.re) (hinv : (horizontalPencilForm N w z).IsInvertible) :
    (wholePlaneH1Embedding C2).comp (horizontalFormSolution N w z) -
        horizontalFreeStateResolvent N z =
      (wholePlaneH1Embedding C2).comp
        ((AnalyticFredholm.compactPencil (horizontalFredholmKernel N w) z).inverse.comp
          ((horizontalFredholmKernel N w z).comp (horizontalFreeSolution N z))) := by
  have hG := (horizontalPencilForm_isInvertible_iff N w hz).mp hinv
  refine ContinuousLinearMap.ext fun f => ?_
  have hval := inverse_compactPencil_sub_id (horizontalFredholmKernel N w) hG
    (horizontalFreeSolution N z f)
  change wholePlaneH1Embedding C2
      ((AnalyticFredholm.compactPencil (horizontalFredholmKernel N w) z).inverse
        (horizontalFreeSolution N z f)) -
      wholePlaneH1Embedding C2 (horizontalFreeSolution N z f) =
    wholePlaneH1Embedding C2
      ((AnalyticFredholm.compactPencil (horizontalFredholmKernel N w) z).inverse
        (horizontalFredholmKernel N w z (horizontalFreeSolution N z f)))
  rw [← map_sub]
  exact congrArg (wholePlaneH1Embedding C2) hval

/-- **Compactness of the resolvent difference.**  For a velocity supported in a set of finite
measure the state resolvent of `A_w` differs from the free state resolvent by a compact
operator on `L²(ℝ²;ℂ²)`. -/
theorem isCompactOperator_horizontalStateResolvent_sub_free
    (s : Set WholePlane) (hs : MeasurableSet s) (hsm : volume s ≠ (∞ : ℝ≥0∞))
    (N : ℝ) (w : WholePlaneC3LInf)
    (hw3 : ∀ᵐ x ∂volume, x ∉ s → wholePlaneCoordLInf 2 w x = 0)
    (hw : ∀ j : Fin 2, ∀ᵐ x ∂volume, x ∉ s → wholePlaneCoordLInf j.castSucc w x = 0)
    {z : ℂ} (hz : 0 < z.re) (hinv : (horizontalPencilForm N w z).IsInvertible) :
    IsCompactOperator ((wholePlaneH1Embedding C2).comp (horizontalFormSolution N w z) -
      horizontalFreeStateResolvent N z) := by
  have hK := isCompactOperator_horizontalFredholmKernel_of_ae_zero_off s hs hsm N w hw3 hw z
  have h1 : IsCompactOperator
      ((horizontalFredholmKernel N w z).comp (horizontalFreeSolution N z)) :=
    hK.comp_clm _
  have h2 : IsCompactOperator
      ((AnalyticFredholm.compactPencil (horizontalFredholmKernel N w) z).inverse.comp
        ((horizontalFredholmKernel N w z).comp (horizontalFreeSolution N z))) :=
    h1.clm_comp _
  have h3 : IsCompactOperator
      ((wholePlaneH1Embedding C2).comp
        ((AnalyticFredholm.compactPencil (horizontalFredholmKernel N w) z).inverse.comp
          ((horizontalFredholmKernel N w z).comp (horizontalFreeSolution N z)))) :=
    h2.clm_comp (wholePlaneH1Embedding C2)
  rw [horizontalStateResolvent_sub_free N w hz hinv]
  exact h3

/-- The free state resolvent is holomorphic on the open right half plane. -/
theorem analyticAt_horizontalFreeStateResolvent (N : ℝ) {z : ℂ} (hz : 0 < z.re) :
    AnalyticAt ℂ (horizontalFreeStateResolvent N) z :=
  FiniteDimensionalSchur.analyticAt_clm_comp analyticAt_const
    (analyticAt_horizontalFreeSolution N hz)

/-- **The free reference has no contour residue.**  On a closed disc inside the open right
half plane the free state resolvent is holomorphic, so its circle integral vanishes. -/
theorem circleIntegral_horizontalFreeStateResolvent_eq_zero (N : ℝ) {c : ℂ} {r : ℝ}
    (hr : 0 ≤ r) (hdisc : Metric.closedBall c r ⊆ {z : ℂ | 0 < z.re}) :
    (∮ z in C(c, r), horizontalFreeStateResolvent N z) = 0 := by
  refine Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr
    Set.countable_empty ?_ ?_
  · intro z hz
    exact ((analyticAt_horizontalFreeStateResolvent N
      (hdisc hz)).continuousAt).continuousWithinAt
  · intro z hz
    have hzball : z ∈ Metric.closedBall c r := Metric.ball_subset_closedBall hz.1
    exact (analyticAt_horizontalFreeStateResolvent N (hdisc hzball)).differentiableAt

end HorizontalWeakForm

end

end FastDynamo
