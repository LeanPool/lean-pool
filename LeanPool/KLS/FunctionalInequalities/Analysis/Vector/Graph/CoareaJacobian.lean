/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Vector.Graph.Basic
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! # The fibre Jacobian of a codimension-`m` level family

The regular case of the codimension-`m` coarea formula compares two densities: the ambient one,
`coareaJacobian (fderiv ℝ u x)`, which the scalar theory records as `‖gradient u x‖`, and the
graph area density `normDet (graphMapLinear ι κ (Dγ y))` produced by the normalized area formula
(`hausdorffNormalized_image_vectorGraphMap`).  This module proves that the two match, exactly as
`abs_deriv_mul_norm_gradient` does in codimension one.

Two identities are proved.  The **linear** one says that if `V` splits orthogonally as
`ι '' H ⊕ κ '' K`, the codimension `finrank K` equals `finrank W`, and the slope `A` makes the
graph `y ↦ ι y + κ (A y)` land in the kernel of `L` — the equation `(L ∘ κ) ∘ A = -(L ∘ ι)` — then

`coareaJacobian L = normDet (L ∘ κ) * normDet (graphMapLinear ι κ A)`.

The **`C¹`** one applies it along a level family `u (ι y + κ (ψ (y, t))) = t`, where implicit
differentiation supplies both the slope equation and the inverse relation `(L ∘ κ) ∘ Dₜψ = 1`:

`normDet (Dₜψ) * coareaJacobian (fderiv ℝ u x) = normDet (graphMapLinear ι κ (D_yψ))`.

The codimension hypothesis `finrank K = finrank W` is **not** removable.  With `V = ℝ²`, `W = ℝ`,
`H = 0`, `K = ℝ²`, `u (x, y) = x` and `ψ t = (t, t)` the level identity holds, the left-hand side is
`√2` and the right-hand side is `1`.

The one genuinely new piece of linear algebra is the **Weinstein–Aronszajn identity in linear-map
form**, `det (1 + X ∘ Y) = det (1 + Y ∘ X)` for maps between two different spaces; Mathlib has it
for matrices only.  It converts the Gram determinant on the target into the Gram determinant on the
parameter space, which is exactly the passage from a coarea Jacobian to an area Jacobian.

**No coarea formula is proved here.**
-/

@[expose] public section

noncomputable section

open Module
open scoped RealInnerProductSpace

namespace FunctionalInequalities.Analysis

/-! ### Weinstein–Aronszajn for linear maps -/

section Sylvester

variable {H W : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

/-- **Weinstein–Aronszajn in linear-map form.**  The two identities are on different spaces: the
left-hand `id` is on `W`, the right-hand one on `H`.  Mathlib proves the matrix statement only. -/
theorem det_id_add_comp_comm (X : H →ₗ[ℝ] W) (Y : W →ₗ[ℝ] H) :
    LinearMap.det (LinearMap.id + X ∘ₗ Y) = LinearMap.det (LinearMap.id + Y ∘ₗ X) := by
  classical
  let bH : Basis (Fin (finrank ℝ H)) ℝ H := Module.finBasis ℝ H
  let bW : Basis (Fin (finrank ℝ W)) ℝ W := Module.finBasis ℝ W
  rw [← LinearMap.det_toMatrix bW, ← LinearMap.det_toMatrix bH, map_add, map_add,
    LinearMap.toMatrix_id, LinearMap.toMatrix_id,
    LinearMap.toMatrix_comp bW bH bW, LinearMap.toMatrix_comp bH bW bH]
  exact Matrix.det_one_add_mul_comm _ _

end Sylvester

/-! ### The adjoint carries the same volume factor in equal dimensions -/

section Adjoint

variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- Between spaces of the same dimension a map and its adjoint have the same volume factor.  The
degenerate case is genuine: a non-injective map and its adjoint both give `0`. -/
theorem normDet_adjoint (f : U →ₗ[ℝ] V) (h : finrank ℝ U = finrank ℝ V) :
    LinearMap.normDet (LinearMap.adjoint f) = LinearMap.normDet f := by
  have hcomp : LinearMap.normDet (LinearMap.adjoint f ∘ₗ f)
      = LinearMap.normDet (LinearMap.adjoint f) * LinearMap.normDet f :=
    LinearMap.normDet_comp_of_finrank_eq f (LinearMap.adjoint f) h
  have hsq : LinearMap.normDet (LinearMap.adjoint f ∘ₗ f) = LinearMap.normDet f ^ 2 := by
    have hd : LinearMap.det (LinearMap.adjoint f ∘ₗ f) = LinearMap.normDet f ^ 2 := by
      have hn := LinearMap.normDet_sq f
      exact_mod_cast hn.symm
    rw [LinearMap.normDet_eq_abs_det, hd, abs_of_nonneg (by positivity)]
  by_cases hf : LinearMap.normDet f = 0
  · rw [hf, LinearMap.normDet_eq_zero_iff_rank_range_ne, LinearMap.finrank_range_adjoint, ← h]
    rw [LinearMap.normDet_eq_zero_iff_rank_range_ne] at hf
    exact hf
  · refine mul_right_cancel₀ hf ?_
    rw [← hcomp, hsq]
    ring

/-- **In equal dimensions the coarea Jacobian is the area Jacobian.**  This is the bookkeeping that
makes the codimension of a regular level the dimension of the target. -/
theorem coareaJacobian_eq_normDet (L : U →L[ℝ] V) (h : finrank ℝ U = finrank ℝ V) :
    coareaJacobian L = LinearMap.normDet ((L : U →ₗ[ℝ] V)) :=
  normDet_adjoint (L : U →ₗ[ℝ] V) h

end Adjoint

/-! ### Orthogonal splittings with a vector-valued normal factor -/

section Splitting

variable {H K V W : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

/-- The codimension-`m` analogue of `IsGraphSplitting`: two isometric embeddings with orthogonal
ranges which together span the ambient space.  The normal factor is a whole space `K`, not a single
unit vector. -/
structure IsVectorGraphSplitting (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V) : Prop where
  /-- The two ranges are orthogonal. -/
  perp : ∀ (y : H) (z : K), ⟪ι y, κ z⟫ = (0 : ℝ)
  /-- The two ranges together span `V`. -/
  split : ∀ x : V, ι (graphProj ι x) + κ (graphProj κ x) = x

/-- The parameter retraction of an adjoint is the adjoint of the restriction. -/
theorem graphProj_adjoint (ι : H →ₗᵢ[ℝ] V) (L : V →L[ℝ] W) (w : W) :
    graphProj ι (LinearMap.adjoint (L : V →ₗ[ℝ] W) w)
      = LinearMap.adjoint ((L ∘L ι.toContinuousLinearMap : H →L[ℝ] W) : H →ₗ[ℝ] W) w := by
  refine ext_inner_right ℝ fun y => ?_
  rw [graphProj, ContinuousLinearMap.adjoint_inner_left, LinearMap.adjoint_inner_left,
    LinearMap.adjoint_inner_left]
  rfl

namespace IsVectorGraphSplitting

variable {ι : H →ₗᵢ[ℝ] V} {κ : K →ₗᵢ[ℝ] V}

theorem perp' (hs : IsVectorGraphSplitting ι κ) (z : K) (y : H) : ⟪κ z, ι y⟫ = (0 : ℝ) := by
  rw [real_inner_comm]; exact hs.perp y z

/-- The parameter component of a split vector. -/
theorem proj_left (hs : IsVectorGraphSplitting ι κ) (y : H) (z : K) :
    graphProj ι (ι y + κ z) = y := by
  rw [map_add, graphProj_ι, graphProj_apply_of_perp ι κ hs.perp, add_zero]

/-- The normal component of a split vector. -/
theorem proj_right (hs : IsVectorGraphSplitting ι κ) (y : H) (z : K) :
    graphProj κ (ι y + κ z) = z := by
  rw [map_add, graphProj_apply_of_perp κ ι hs.perp', graphProj_ι, zero_add]

/-- Pythagoras in a vector-valued splitting. -/
theorem norm_add_sq (hs : IsVectorGraphSplitting ι κ) (y : H) (z : K) :
    ‖ι y + κ z‖ ^ 2 = ‖y‖ ^ 2 + ‖z‖ ^ 2 := by
  rw [← @real_inner_self_eq_norm_sq V]
  simp only [inner_add_left, inner_add_right, ι.inner_map_map, κ.inner_map_map,
    hs.perp, hs.perp']
  rw [← @real_inner_self_eq_norm_sq H, ← @real_inner_self_eq_norm_sq K]
  ring

/-- **The Gram operator of `L` splits.**  Writing `P = L ∘ ι` and `Q = L ∘ κ`, the target Gram
operator `L ∘ Lᵀ` is `P ∘ Pᵀ + Q ∘ Qᵀ`.  This is where the spanning hypothesis is used. -/
theorem comp_adjoint (hs : IsVectorGraphSplitting ι κ) (L : V →L[ℝ] W) :
    (L : V →ₗ[ℝ] W) ∘ₗ LinearMap.adjoint (L : V →ₗ[ℝ] W)
      = ((L ∘L ι.toContinuousLinearMap : H →L[ℝ] W) : H →ₗ[ℝ] W)
            ∘ₗ LinearMap.adjoint ((L ∘L ι.toContinuousLinearMap : H →L[ℝ] W) : H →ₗ[ℝ] W)
        + ((L ∘L κ.toContinuousLinearMap : K →L[ℝ] W) : K →ₗ[ℝ] W)
            ∘ₗ LinearMap.adjoint ((L ∘L κ.toContinuousLinearMap : K →L[ℝ] W) : K →ₗ[ℝ] W) := by
  ext w
  have hsplit := hs.split (LinearMap.adjoint (L : V →ₗ[ℝ] W) w)
  rw [graphProj_adjoint ι L w, graphProj_adjoint κ L w] at hsplit
  simp only [LinearMap.add_apply, LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
  rw [← hsplit]
  simp

end IsVectorGraphSplitting

/-- Every orthogonal complement gives a splitting.  At a regular point of `u` the relevant one has
`H` the kernel of the differential. -/
theorem isVectorGraphSplitting_orthogonal (P : Submodule ℝ V) :
    IsVectorGraphSplitting P.subtypeₗᵢ (Pᗮ).subtypeₗᵢ where
  perp := by
    intro y z
    exact (Submodule.mem_orthogonal P (z : V)).1 z.2 (y : V) y.2
  split := by
    intro x
    have h1 : (P.subtypeₗᵢ (graphProj P.subtypeₗᵢ x) : V) = P.starProjection x := by
      rw [graphProj, show (P.subtypeₗᵢ.toContinuousLinearMap) = P.subtypeL from rfl,
        Submodule.adjoint_subtypeL]
      rfl
    have h2 : ((Pᗮ).subtypeₗᵢ (graphProj (Pᗮ).subtypeₗᵢ x) : V) = (Pᗮ).starProjection x := by
      rw [graphProj, show ((Pᗮ).subtypeₗᵢ.toContinuousLinearMap) = (Pᗮ).subtypeL from rfl,
        Submodule.adjoint_subtypeL]
      rfl
    rw [h1, h2, Submodule.starProjection_orthogonal_val]
    abel

omit [FiniteDimensional ℝ W] in
/-- At a regular point the normal factor has exactly the dimension of the target: the codimension
hypothesis of the fibre Jacobian identity is automatic. -/
theorem finrank_orthogonal_ker_eq (L : V →L[ℝ] W)
    (hL : Function.Surjective (L : V →ₗ[ℝ] W)) :
    finrank ℝ ((LinearMap.ker (L : V →ₗ[ℝ] W))ᗮ : Submodule ℝ V) = finrank ℝ W := by
  have hrange : LinearMap.range (L : V →ₗ[ℝ] W) = ⊤ := LinearMap.range_eq_top.2 hL
  have h1 := Submodule.finrank_add_finrank_orthogonal (𝕜 := ℝ) (E := V)
    (LinearMap.ker (L : V →ₗ[ℝ] W))
  have h2 := LinearMap.finrank_range_add_finrank_ker (L : V →ₗ[ℝ] W)
  rw [hrange] at h2
  simp only [finrank_top] at h2
  omega

/-! ### The splitting is measure preserving -/

/-- The linear isometry equivalence `WithLp 2 (H × K) ≃ₗᵢ[ℝ] V` attached to a vector-valued
splitting; the codimension-one case is `splitIsometry`. -/
def splitVectorIsometry {ι : H →ₗᵢ[ℝ] V} {κ : K →ₗᵢ[ℝ] V} (hs : IsVectorGraphSplitting ι κ) :
    WithLp 2 (H × K) ≃ₗᵢ[ℝ] V :=
  LinearIsometryEquiv.ofSurjective
    { toFun := fun p => ι (WithLp.ofLp p).1 + κ (WithLp.ofLp p).2
      map_add' := by intro p q; simp; abel
      map_smul' := by intro c p; simp [smul_add]
      norm_map' := by
        intro p
        change ‖ι (WithLp.ofLp p).1 + κ (WithLp.ofLp p).2‖ = ‖p‖
        have h1 := hs.norm_add_sq (WithLp.ofLp p).1 (WithLp.ofLp p).2
        have h2 : ‖p‖ ^ 2 = ‖(WithLp.ofLp p).1‖ ^ 2 + ‖(WithLp.ofLp p).2‖ ^ 2 :=
          WithLp.prod_norm_sq_eq_of_L2 p
        nlinarith [norm_nonneg (ι (WithLp.ofLp p).1 + κ (WithLp.ofLp p).2), norm_nonneg p] }
    (fun x => ⟨WithLp.toLp 2 (graphProj ι x, graphProj κ x), hs.split x⟩)

theorem splitVectorIsometry_apply {ι : H →ₗᵢ[ℝ] V} {κ : K →ₗᵢ[ℝ] V}
    (hs : IsVectorGraphSplitting ι κ) (p : WithLp 2 (H × K)) :
    splitVectorIsometry hs p = ι (WithLp.ofLp p).1 + κ (WithLp.ofLp p).2 := rfl

/-- **The splitting chart preserves Lebesgue measure.**  This is the Fubini backbone of the
codimension-`m` regular case: integrating over `V` is integrating over parameter times normal
factor, with no constant left over. -/
theorem measurePreserving_split [MeasurableSpace H] [BorelSpace H] [MeasurableSpace K]
    [BorelSpace K] [MeasurableSpace V] [BorelSpace V] {ι : H →ₗᵢ[ℝ] V} {κ : K →ₗᵢ[ℝ] V}
    (hs : IsVectorGraphSplitting ι κ) :
    MeasureTheory.MeasurePreserving (fun p : H × K => ι p.1 + κ p.2)
      (MeasureTheory.volume : MeasureTheory.Measure (H × K))
      (MeasureTheory.volume : MeasureTheory.Measure V) := by
  have h1 : MeasureTheory.MeasurePreserving (WithLp.toLp 2 : H × K → WithLp 2 (H × K))
      (MeasureTheory.volume : MeasureTheory.Measure (H × K))
      (MeasureTheory.volume : MeasureTheory.Measure (WithLp 2 (H × K))) :=
    WithLp.volume_preserving_toLp H K
  have h2 := ((splitVectorIsometry hs).measurePreserving).comp h1
  have heq : ⇑(splitVectorIsometry hs) ∘ (WithLp.toLp 2 : H × K → WithLp 2 (H × K))
      = fun p : H × K => ι p.1 + κ p.2 := by
    funext p
    simp [splitVectorIsometry_apply]
  rwa [heq] at h2

end Splitting

/-! ### The fibre Jacobian identity -/

section FibreJacobian

variable {H K V W : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

/-- **The linear fibre Jacobian identity.**  With `Q = L ∘ κ` and a slope `A` whose graph lies in
the kernel of `L`, the coarea Jacobian of `L` factors as the normal volume factor times the area
Jacobian of the graph.  For `K = W = ℝ` this is `‖∇u‖ = |∂u/∂z| · √(1 + |slope|²)`. -/
theorem coareaJacobian_eq_normDet_mul_normDet_graphMapLinear
    {ι : H →ₗᵢ[ℝ] V} {κ : K →ₗᵢ[ℝ] V} (hs : IsVectorGraphSplitting ι κ)
    (hdim : finrank ℝ K = finrank ℝ W) (L : V →L[ℝ] W) {A : H →L[ℝ] K}
    (hA : (L ∘L κ.toContinuousLinearMap) ∘L A = -(L ∘L ι.toContinuousLinearMap)) :
    coareaJacobian L
      = LinearMap.normDet ((L ∘L κ.toContinuousLinearMap : K →L[ℝ] W) : K →ₗ[ℝ] W)
        * LinearMap.normDet ((graphMapLinear ι κ A : H →ₗ[ℝ] V)) := by
  set a : H →ₗ[ℝ] K := (A : H →ₗ[ℝ] K) with ha
  set q : K →ₗ[ℝ] W := ((L ∘L κ.toContinuousLinearMap : K →L[ℝ] W) : K →ₗ[ℝ] W) with hq
  set p : H →ₗ[ℝ] W := ((L ∘L ι.toContinuousLinearMap : H →L[ℝ] W) : H →ₗ[ℝ] W) with hp
  set S : K →ₗ[ℝ] K := LinearMap.id + a ∘ₗ LinearMap.adjoint a with hS
  set G : ℝ := LinearMap.normDet ((graphMapLinear ι κ A : H →ₗ[ℝ] V)) with hG
  have hpq : p = -(q ∘ₗ a) := by
    rw [hp, hq, ha]
    refine LinearMap.ext fun y => ?_
    have h := congrArg (fun T : H →L[ℝ] W => T y) hA
    simp only [ContinuousLinearMap.comp_apply, neg_apply,
      LinearIsometry.coe_toContinuousLinearMap] at h
    simp only [LinearMap.neg_apply, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap]
    rw [h, neg_neg]
  -- the Gram operator of `L` is conjugated from the Gram operator of the graph
  have hLL : (L : V →ₗ[ℝ] W) ∘ₗ LinearMap.adjoint (L : V →ₗ[ℝ] W)
      = (q ∘ₗ S) ∘ₗ LinearMap.adjoint q := by
    rw [hs.comp_adjoint L, ← hp, ← hq, hpq, map_neg, LinearMap.adjoint_comp]
    refine LinearMap.ext fun w => ?_
    simp only [hS, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.neg_apply,
      LinearMap.id_apply, map_add, map_neg, neg_neg]
    abel
  -- the three volume factors multiply
  have h1 : LinearMap.normDet ((q ∘ₗ S) ∘ₗ LinearMap.adjoint q)
      = LinearMap.normDet (q ∘ₗ S) * LinearMap.normDet (LinearMap.adjoint q) :=
    LinearMap.normDet_comp_of_finrank_eq _ _ hdim.symm
  have h2 : LinearMap.normDet (q ∘ₗ S) = LinearMap.normDet q * LinearMap.normDet S :=
    LinearMap.normDet_comp_of_finrank_eq _ _ rfl
  have h3 : LinearMap.normDet (LinearMap.adjoint q) = LinearMap.normDet q :=
    normDet_adjoint q hdim
  have h4 : LinearMap.normDet S = G ^ 2 := by
    have hdet : LinearMap.det S = G ^ 2 := by
      rw [hS, det_id_add_comp_comm a (LinearMap.adjoint a), hG,
        normDet_graphMapLinear_sq ι κ hs.perp A]
    rw [LinearMap.normDet_eq_abs_det, hdet, abs_of_nonneg (by positivity)]
  have hsq : coareaJacobian L ^ 2 = (LinearMap.normDet q * G) ^ 2 := by
    have hdetL : LinearMap.det ((L : V →ₗ[ℝ] W) ∘ₗ LinearMap.adjoint (L : V →ₗ[ℝ] W))
        = coareaJacobian L ^ 2 := (coareaJacobian_sq L).symm
    have habs : LinearMap.normDet ((L : V →ₗ[ℝ] W) ∘ₗ LinearMap.adjoint (L : V →ₗ[ℝ] W))
        = coareaJacobian L ^ 2 := by
      rw [LinearMap.normDet_eq_abs_det, hdetL, abs_of_nonneg (by positivity)]
    rw [← habs, hLL, h1, h2, h3, h4]
    ring
  have hnn : 0 ≤ LinearMap.normDet q * G :=
    mul_nonneg (LinearMap.normDet_nonneg _) (LinearMap.normDet_nonneg _)
  nlinarith [coareaJacobian_nonneg L, hsq, hnn]

/-- **The `C¹` fibre Jacobian identity**, the codimension-`m` analogue of
`abs_deriv_mul_norm_gradient`.  Along a `C¹` family of levels `u (ι y + κ (ψ (y, t))) = t` the
normal volume factor of `Dₜψ` times the ambient coarea density is the graph area density that the
normalized area formula `hausdorffNormalized_image_vectorGraphMap` integrates.  No division, no
finiteness and no regular-value hypothesis occur; only differentiability at the point is used for
`u`. -/
theorem normDet_fderiv_mul_coareaJacobian
    {ι : H →ₗᵢ[ℝ] V} {κ : K →ₗᵢ[ℝ] V} (hs : IsVectorGraphSplitting ι κ)
    (hdim : finrank ℝ K = finrank ℝ W)
    {ψ : H × W → K} {Ω : Set (H × W)} (hΩ : IsOpen Ω) (hψ : ContDiffOn ℝ 1 ψ Ω)
    {u : V → W} (hlevel : ∀ p ∈ Ω, u (ι p.1 + κ (ψ p)) = p.2)
    {y₀ : H} {t₀ : W} (hp : (y₀, t₀) ∈ Ω)
    (hu : DifferentiableAt ℝ u (ι y₀ + κ (ψ (y₀, t₀)))) :
    LinearMap.normDet ((fderiv ℝ (fun t => ψ (y₀, t)) t₀ : W →ₗ[ℝ] K))
        * coareaJacobian (fderiv ℝ u (ι y₀ + κ (ψ (y₀, t₀))))
      = LinearMap.normDet
          ((graphMapLinear ι κ (fderiv ℝ (fun y => ψ (y, t₀)) y₀) : H →ₗ[ℝ] V)) := by
  set L : V →L[ℝ] W := fderiv ℝ u (ι y₀ + κ (ψ (y₀, t₀))) with hLdef
  set A : H →L[ℝ] K := fderiv ℝ (fun y => ψ (y, t₀)) y₀ with hAdef
  set B : W →L[ℝ] K := fderiv ℝ (fun t => ψ (y₀, t)) t₀ with hBdef
  have hψp : DifferentiableAt ℝ ψ (y₀, t₀) :=
    (hψ.contDiffAt (hΩ.mem_nhds hp)).differentiableAt one_ne_zero
  have hyd : DifferentiableAt ℝ (fun y => ψ (y, t₀)) y₀ :=
    hψp.comp y₀ (differentiableAt_id.prodMk (differentiableAt_const _))
  have htd : DifferentiableAt ℝ (fun t => ψ (y₀, t)) t₀ :=
    hψp.comp t₀ ((differentiableAt_const _).prodMk differentiableAt_id)
  -- differentiating along the fibre: the graph slope lands in the kernel
  have hΓ : HasFDerivAt (vectorGraphMap ι κ fun y => ψ (y, t₀)) (graphMapLinear ι κ A) y₀ :=
    hasFDerivAt_vectorGraphMap ι κ hyd
  have hlevelY : (u ∘ vectorGraphMap ι κ fun y => ψ (y, t₀)) =ᶠ[nhds y₀] fun _ => t₀ := by
    have hn := (continuousAt_id.prodMk continuousAt_const).preimage_mem_nhds (hΩ.mem_nhds hp)
    filter_upwards [hn] with y hy using hlevel (y, t₀) hy
  have hcompY : HasFDerivAt (u ∘ vectorGraphMap ι κ fun y => ψ (y, t₀))
      (L ∘L graphMapLinear ι κ A) y₀ := hu.hasFDerivAt.comp y₀ hΓ
  have hzeroY : HasFDerivAt (u ∘ vectorGraphMap ι κ fun y => ψ (y, t₀)) (0 : H →L[ℝ] W) y₀ :=
    (hasFDerivAt_const t₀ y₀).congr_of_eventuallyEq hlevelY
  have hkernel : (L ∘L κ.toContinuousLinearMap) ∘L A = -(L ∘L ι.toContinuousLinearMap) := by
    have hzero : L ∘L graphMapLinear ι κ A = 0 := hcompY.unique hzeroY
    refine ContinuousLinearMap.ext fun y => ?_
    have h := congrArg (fun T : H →L[ℝ] W => T y) hzero
    simp only [ContinuousLinearMap.comp_apply, graphMapLinear_apply, map_add,
      zero_apply] at h
    simp only [ContinuousLinearMap.comp_apply, neg_apply,
      LinearIsometry.coe_toContinuousLinearMap]
    exact eq_neg_of_add_eq_zero_right h
  -- differentiating across the levels: the normal derivative inverts `L ∘ κ`
  have hΛ : HasFDerivAt (fun t => ι y₀ + κ (ψ (y₀, t))) (κ.toContinuousLinearMap ∘L B) t₀ :=
    (κ.toContinuousLinearMap.hasFDerivAt.comp t₀ htd.hasFDerivAt).const_add (ι y₀)
  have hlevelT : (fun t => u (ι y₀ + κ (ψ (y₀, t)))) =ᶠ[nhds t₀] id := by
    have hn := (continuousAt_const.prodMk continuousAt_id).preimage_mem_nhds (hΩ.mem_nhds hp)
    filter_upwards [hn] with t ht using hlevel (y₀, t) ht
  have hcompT : HasFDerivAt (fun t => u (ι y₀ + κ (ψ (y₀, t))))
      (L ∘L κ.toContinuousLinearMap ∘L B) t₀ := hu.hasFDerivAt.comp t₀ hΛ
  have hidT : HasFDerivAt (fun t => u (ι y₀ + κ (ψ (y₀, t)))) (ContinuousLinearMap.id ℝ W) t₀ :=
    (hasFDerivAt_id t₀).congr_of_eventuallyEq hlevelT
  have hinv : ((L ∘L κ.toContinuousLinearMap : K →L[ℝ] W) : K →ₗ[ℝ] W) ∘ₗ (B : W →ₗ[ℝ] K)
      = LinearMap.id := by
    have h := hcompT.unique hidT
    refine LinearMap.ext fun w => ?_
    have hw := congrArg (fun T : W →L[ℝ] W => T w) h
    simpa using hw
  have hone : LinearMap.normDet ((B : W →ₗ[ℝ] K))
      * LinearMap.normDet ((L ∘L κ.toContinuousLinearMap : K →L[ℝ] W) : K →ₗ[ℝ] W) = 1 := by
    have h := LinearMap.normDet_comp_of_finrank_eq ((B : W →ₗ[ℝ] K))
      (((L ∘L κ.toContinuousLinearMap : K →L[ℝ] W)) : K →ₗ[ℝ] W) hdim.symm
    rw [hinv, LinearMap.normDet_id] at h
    linarith [h]
  rw [coareaJacobian_eq_normDet_mul_normDet_graphMapLinear hs hdim L hkernel, ← mul_assoc, hone,
    one_mul]

end FibreJacobian

/-! ### The codimension-one case is the proved scalar identity -/

section Codimension

variable {H V : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

omit [MeasurableSpace H] [BorelSpace H] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] in
/-- A one-dimensional normal factor makes the graph model the repository's codimension-one
`graphLinear`, with the Riesz representative of the slope as its parameter. -/
theorem graphMapLinear_eq_graphLinear (ι : H →ₗᵢ[ℝ] V) (κ : ℝ →ₗᵢ[ℝ] V) (A : H →L[ℝ] ℝ) :
    graphMapLinear ι κ A = graphLinear ι (κ 1) ((InnerProductSpace.toDual ℝ H).symm A) := by
  refine ContinuousLinearMap.ext fun y => ?_
  rw [graphMapLinear_apply, graphLinear_apply, InnerProductSpace.toDual_symm_apply,
    show κ (A y) = A y • κ 1 by rw [← map_smul]; norm_num]

omit [FiniteDimensional ℝ V] in
/-- **The codimension-one volume factor.**  In codimension one the new graph Jacobian is the
already proved `graphJacobian`. -/
theorem normDet_graphMapLinear_eq_graphJacobian (ι : H →ₗᵢ[ℝ] V) (κ : ℝ →ₗᵢ[ℝ] V)
    (hperp : ∀ (y : H) (z : ℝ), ⟪ι y, κ z⟫ = (0 : ℝ)) (A : H →L[ℝ] ℝ) :
    LinearMap.normDet ((graphMapLinear ι κ A : H →ₗ[ℝ] V))
      = graphJacobian ((InnerProductSpace.toDual ℝ H).symm A) := by
  have he : ‖κ 1‖ = 1 := by rw [κ.norm_map]; norm_num
  rw [graphMapLinear_eq_graphLinear ι κ A]
  exact normDet_graphLinear ι he (fun v => hperp v 1) _

/-- **`m = 1` recovers the scalar identity.**  With a one-dimensional target the `C¹` fibre
Jacobian identity is literally `abs_deriv_mul_norm_gradient`: the normal factor is the absolute
derivative in the level direction and the ambient density is the gradient norm. -/
theorem abs_deriv_mul_norm_gradient_of_vectorGraphSplitting {ι : H →ₗᵢ[ℝ] V} {κ : ℝ →ₗᵢ[ℝ] V}
    (hs : IsVectorGraphSplitting ι κ) {ψ : H × ℝ → ℝ} {Ω : Set (H × ℝ)} (hΩ : IsOpen Ω)
    (hψ : ContDiffOn ℝ 1 ψ Ω) {u : V → ℝ} (hlevel : ∀ p ∈ Ω, u (ι p.1 + κ (ψ p)) = p.2)
    {y₀ : H} {t₀ : ℝ} (hp : (y₀, t₀) ∈ Ω)
    (hu : DifferentiableAt ℝ u (ι y₀ + κ (ψ (y₀, t₀)))) :
    |deriv (fun t => ψ (y₀, t)) t₀| * ‖gradient u (ι y₀ + κ (ψ (y₀, t₀)))‖
      = graphJacobian (gradient (fun y => ψ (y, t₀)) y₀) := by
  have hmain := normDet_fderiv_mul_coareaJacobian hs rfl hΩ hψ hlevel hp hu
  rw [normDet_graphMapLinear_eq_graphJacobian ι κ hs.perp] at hmain
  rw [coareaJacobian_fderiv] at hmain
  rw [show gradient (fun y => ψ (y, t₀)) y₀
      = (InnerProductSpace.toDual ℝ H).symm (fderiv ℝ (fun y => ψ (y, t₀)) y₀) from rfl,
    ← hmain]
  congr 1
  rw [LinearMap.normDet_eq_abs_det, LinearMap.det_ring]
  rfl

end Codimension

end FunctionalInequalities.Analysis
