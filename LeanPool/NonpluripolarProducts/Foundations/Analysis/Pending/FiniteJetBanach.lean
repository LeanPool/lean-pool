/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.DistributionSeminorms
public import Mathlib.Analysis.Convex.Cone.Extension
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Normed.Module.TransferInstance

/-!
# Finite jets as a Banach space

A distribution restricted to one compact support is controlled by finitely
many derivative seminorms.  The corresponding finite jet embeds the
fixed-support test-function space into a Banach space.  Since the zeroth jet
is included, this embedding is injective, so Hahn--Banach extends the
restricted distribution without first passing to a separated quotient or an
abstract completion.
-/

@[expose] public section

noncomputable section

open Set TopologicalSpace
open scoped ContDiff Distributions NNReal

namespace SGPT.Foundations.Analysis.Pending

/-- The Banach space containing all bounded derivative jets through order
`m`, with the supremum norm over the finitely many derivative orders.  It is a
type synonym carrying only the normed structure of the product, so that its
additive and module structures have a single instance path. -/
def FiniteJetSpace
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (m : ℕ) :=
  (i : ↑(Finset.Iic m)) → BoundedContinuousFunction E (E [×(i : ℕ)]→L[ℝ] ℝ)

noncomputable instance finiteJetSpaceNormedAddCommGroup
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (m : ℕ) :
    NormedAddCommGroup (FiniteJetSpace E m) :=
  Pi.normedAddCommGroup

noncomputable instance finiteJetSpaceNormedSpace
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (m : ℕ) :
    NormedSpace ℝ (FiniteJetSpace E m) :=
  Pi.normedSpace

instance finiteJetSpaceCompleteSpace
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (m : ℕ) :
    CompleteSpace (FiniteJetSpace E m) :=
  Pi.complete _

@[ext]
theorem finiteJetSpace_ext
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ} {J H : FiniteJetSpace E m}
    (h : ∀ i, J i = H i) : J = H :=
  funext h

@[simp]
theorem finiteJetSpace_add_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ} (J H : FiniteJetSpace E m) (i : ↑(Finset.Iic m)) :
    (J + H) i = J i + H i :=
  rfl

@[simp]
theorem finiteJetSpace_smul_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ} (c : ℝ) (J : FiniteJetSpace E m) (i : ↑(Finset.Iic m)) :
    (c • J) i = c • J i :=
  rfl

theorem norm_finiteJetSpace_apply_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ} (J : FiniteJetSpace E m) (i : ↑(Finset.Iic m)) :
    ‖J i‖ ≤ ‖J‖ :=
  norm_le_pi_norm (J : (i : ↑(Finset.Iic m)) →
    BoundedContinuousFunction E (E [×(i : ℕ)]→L[ℝ] ℝ)) i

theorem norm_finiteJetSpace_le_iff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ} (J : FiniteJetSpace E m) {r : ℝ} (hr : 0 ≤ r) :
    ‖J‖ ≤ r ↔ ∀ i, ‖J i‖ ≤ r :=
  pi_norm_le_iff_of_nonneg (x := (J : (i : ↑(Finset.Iic m)) →
    BoundedContinuousFunction E (E [×(i : ℕ)]→L[ℝ] ℝ))) hr

/-- Projection to one derivative coordinate of the finite jet. -/
noncomputable def finiteJetProj
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m : ℕ) (i : ↑(Finset.Iic m)) :
    FiniteJetSpace E m →L[ℝ]
      BoundedContinuousFunction E (E [×(i : ℕ)]→L[ℝ] ℝ) :=
  ContinuousLinearMap.proj (R := ℝ) (φ := fun i : ↑(Finset.Iic m) ↦
    BoundedContinuousFunction E (E [×(i : ℕ)]→L[ℝ] ℝ)) i

@[simp]
theorem finiteJetProj_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m : ℕ) (i : ↑(Finset.Iic m)) (J : FiniteJetSpace E m) :
    finiteJetProj m i J = J i :=
  rfl

/-- Evaluation of one derivative coordinate of a finite jet at a point and
on a tuple of directions. -/
noncomputable def finiteJetEvalCLM
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m : ℕ) (i : ↑(Finset.Iic m)) (y : E) (v : Fin (i : ℕ) → E) :
    FiniteJetSpace E m →L[ℝ] ℝ :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin (i : ℕ) ↦ E) ℝ v).comp
    ((BoundedContinuousFunction.evalCLM ℝ y).comp (finiteJetProj (E := E) m i))

@[simp]
theorem finiteJetEvalCLM_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m : ℕ) (i : ↑(Finset.Iic m)) (y : E) (v : Fin (i : ℕ) → E)
    (J : FiniteJetSpace E m) :
    finiteJetEvalCLM m i y v J = J i y v :=
  rfl

/-- The derivatives through order `m` of a fixed-support smooth function,
viewed as one element of `FiniteJetSpace`. -/
noncomputable def finiteJetCLM
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Compacts E) (m : ℕ) :
    ContDiffMapSupportedIn E ℝ ⊤ K →L[ℝ] FiniteJetSpace E m :=
  ContDiffMapSupportedIn.mkCLMtoNormedSpace ℝ
    (fun f ↦ (fun i : ↑(Finset.Iic m) ↦
      ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ (i : ℕ) f : FiniteJetSpace E m))
    (fun f g ↦ finiteJetSpace_ext fun i ↦
      map_add (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ (i : ℕ)) f g)
    (fun c f ↦ finiteJetSpace_ext fun i ↦
      map_smul (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ (i : ℕ)) c f)
    ⟨Finset.Iic m, 1, zero_le_one, fun f ↦ by
      rw [one_mul]
      refine (norm_finiteJetSpace_le_iff _ (apply_nonneg _ _)).2 fun i ↦ ?_
      simpa [ContDiffMapSupportedIn.seminorm_apply] using
        (Seminorm.le_finset_sup_apply
          (p := ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K)
          (x := f) i.property)⟩

@[simp]
theorem finiteJetCLM_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Compacts E) (m : ℕ)
    (f : ContDiffMapSupportedIn E ℝ ⊤ K) (i : ↑(Finset.Iic m)) :
    finiteJetCLM K m f i =
      ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ (i : ℕ) f :=
  rfl

/-- The finite jet map is injective because its zeroth component remembers
the original function. -/
theorem finiteJetCLM_injective
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Compacts E) (m : ℕ) :
    Function.Injective (finiteJetCLM K m) := by
  intro f g hfg
  apply ContDiffMapSupportedIn.structureMapCLM_zero_injective ℝ
  exact congrArg (fun J : FiniteJetSpace E m ↦
    J ⟨0, Finset.mem_Iic.mpr (Nat.zero_le m)⟩) hfg

/-- The initial-order sup-seminorm is bounded by the norm of the finite jet.
This is the direction needed to transport the distribution estimate to the
jet image. -/
theorem finiteOrderSeminorm_le_norm_finiteJetCLM
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Compacts E) (m : ℕ)
    (f : ContDiffMapSupportedIn E ℝ ⊤ K) :
    ((Finset.Iic m).sup
        (ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K)) f ≤
      ‖finiteJetCLM K m f‖ := by
  apply Seminorm.finset_sup_apply_le
    (x := f) (norm_nonneg (finiteJetCLM K m f))
  intro i hi
  rw [ContDiffMapSupportedIn.seminorm_apply]
  let j : ↑(Finset.Iic m) := ⟨i, hi⟩
  simpa [j] using
    (norm_finiteJetSpace_apply_le (finiteJetCLM K m f) j)

/-- The finite jet norm is exactly the standard maximum of all derivative
seminorms through order `m`. -/
theorem norm_finiteJetCLM_eq_finiteOrderSeminorm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Compacts E) (m : ℕ)
    (f : ContDiffMapSupportedIn E ℝ ⊤ K) :
    ‖finiteJetCLM K m f‖ =
      ((Finset.Iic m).sup
        (ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K)) f := by
  apply le_antisymm
  · refine (norm_finiteJetSpace_le_iff _ (apply_nonneg _ _)).2 fun i ↦ ?_
    have hi : (i : ℕ) ∈ Finset.Iic m :=
      i.property
    simpa [ContDiffMapSupportedIn.seminorm_apply] using
      (Seminorm.le_finset_sup_apply
        (p := ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K)
        (x := f) hi)
  · exact finiteOrderSeminorm_le_norm_finiteJetCLM K m f

/-- A linear functional controlled by the initial derivative seminorm extends
to a continuous functional on the ambient finite-jet Banach space. -/
theorem exists_finiteJet_extension
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Compacts E) (m : ℕ)
    (L : ContDiffMapSupportedIn E ℝ ⊤ K →ₗ[ℝ] ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (hL : ∀ f : ContDiffMapSupportedIn E ℝ ⊤ K,
      |L f| ≤ C *
        ((Finset.Iic m).sup
          (ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K)) f) :
    ∃ G : FiniteJetSpace E m →L[ℝ] ℝ,
      ∀ f : ContDiffMapSupportedIn E ℝ ⊤ K,
        G (finiteJetCLM K m f) = L f := by
  let J := finiteJetCLM K m
  have hJ : Function.Injective J := finiteJetCLM_injective K m
  let e : ContDiffMapSupportedIn E ℝ ⊤ K ≃ₗ[ℝ]
      LinearMap.range J.toLinearMap :=
    LinearEquiv.ofInjective J.toLinearMap hJ
  let F : FiniteJetSpace E m →ₗ.[ℝ] ℝ :=
    { domain := LinearMap.range J.toLinearMap
      toFun := L.comp e.symm.toLinearMap }
  have hF : ∀ x : F.domain, F x ≤ C * ‖(x : FiniteJetSpace E m)‖ := by
    intro x
    have hxval : J (e.symm x) = (x : FiniteJetSpace E m) :=
      LinearEquiv.ofInjective_symm_apply J.toLinearMap x
    calc
      F x = L (e.symm x) := rfl
      _ ≤ |L (e.symm x)| := le_abs_self _
      _ ≤ C *
          ((Finset.Iic m).sup
            (ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K)) (e.symm x) :=
        hL (e.symm x)
      _ ≤ C * ‖J (e.symm x)‖ :=
        mul_le_mul_of_nonneg_left
          (finiteOrderSeminorm_le_norm_finiteJetCLM K m (e.symm x)) hC
      _ = C * ‖(x : FiniteJetSpace E m)‖ := by
        rw [hxval]
  obtain ⟨g, hgF, hgN⟩ := exists_extension_of_le_sublinear F
    (fun x ↦ C * ‖x‖)
    (fun c hc x ↦ by
      simp only [norm_smul, Real.norm_of_nonneg hc.le]
      ring)
    (fun x y ↦ by
      nlinarith [norm_add_le x y])
    hF
  have hg : ∀ x, ‖g x‖ ≤ C * ‖x‖ := by
    intro x
    rw [Real.norm_eq_abs, abs_le]
    refine ⟨?_, hgN x⟩
    have h := hgN (-x)
    simp only [map_neg, norm_neg] at h
    linarith
  refine ⟨g.mkContinuous C hg, fun f ↦ ?_⟩
  have h := hgF (e f)
  simpa [F, e, J] using h

/-- A distribution restricted to one compact support extends, after choosing
the finite order supplied by continuity, to a continuous functional on the
corresponding finite-jet Banach space. -/
theorem exists_finiteJet_distribution_extension
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (T : Distribution Ω ℝ ⊤) (K : Compacts E)
    (hKΩ : (K : Set E) ⊆ Ω) :
    ∃ (m : ℕ) (G : FiniteJetSpace E m →L[ℝ] ℝ),
      ∀ f : ContDiffMapSupportedIn E ℝ ⊤ K,
        G (finiteJetCLM K m f) =
          T (TestFunction.ofSupportedIn hKΩ f) := by
  obtain ⟨m, C, _hC, hbound⟩ :=
    exists_finite_order_seminorm_bound_on_compact T K hKΩ
  obtain ⟨G, hG⟩ := exists_finiteJet_extension K m
    (T.comp (TestFunction.ofSupportedInCLM ℝ hKΩ)).toLinearMap
    (C : ℝ) C.coe_nonneg (fun f ↦ by
      change |T (TestFunction.ofSupportedIn hKΩ f)| ≤
        (C : ℝ) *
          ((Finset.Iic m).sup
            (ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K)) f
      exact hbound f)
  exact ⟨m, G, fun f ↦ by
    exact hG f⟩

end SGPT.Foundations.Analysis.Pending
