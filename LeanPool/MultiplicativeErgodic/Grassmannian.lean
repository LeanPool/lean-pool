/-
Copyright (c) 2026 George Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Lee
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.MetricSpace.Closeds
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.MeasureTheory.Constructions.Pi
public import LeanPool.MultiplicativeErgodic.Auerbach

/-!
# The Grassmannian of a Banach space

Corresponds to Section 2 ("The Grassmannian") of `proof_met.tex`.
-/

@[expose] public section

namespace MultiplicativeErgodic

open _root_.Submodule MultiplicativeErgodic.Submodule TopologicalSpace

variable (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- `𝒢X`: closed subspaces of `X` admitting a bounded (i.e. continuous) projection.
Definition in Section 2, first display. We reuse Mathlib's `Submodule.ClosedComplemented`,
which is already exactly "there is a continuous linear projection onto `V`". -/
def Grassmannian : Type _ :=
  {V : Submodule ℝ X // V.ClosedComplemented}

/-- `𝒢_kX`: the Grassmannian of `k`-dimensional subspaces. Finite-dimensional subspaces of a
real Banach space are automatically closed and complemented, so this is a genuine sub-type of
`Grassmannian X`; see `GrassmannianFin.toGrassmannian` below. -/
def GrassmannianFin (k : ℕ) : Type _ :=
  {V : Submodule ℝ X // FiniteDimensional ℝ V ∧ Module.finrank ℝ V = k}

/-- `𝒢^kX`: the Grassmannian of subspaces of finite codimension `k`, as a subtype of `𝒢X`
(the paper defines it this way: `𝒢^kX ⊆ 𝒢X`). -/
def GrassmannianCofin (k : ℕ) : Type _ :=
  {V : Grassmannian X // FiniteDimensional ℝ (X ⧸ (V.1 : Submodule ℝ X)) ∧
    Module.finrank ℝ (X ⧸ (V.1 : Submodule ℝ X)) = k}

variable {X}

/-- Every finite-dimensional subspace is closed-complemented, giving the inclusion
`𝒢_kX ↪ 𝒢X` used implicitly throughout the paper. -/
theorem GrassmannianFin.closedComplemented (k : ℕ) (V : GrassmannianFin X k) :
    (V.1 : Submodule ℝ X).ClosedComplemented := by
  have : FiniteDimensional ℝ (V.1 : Submodule ℝ X) := V.2.1
  exact Submodule.closedComplemented_of_finiteDimensional _

/-- The inclusion `𝒢_kX → 𝒢X`. -/
def GrassmannianFin.toGrassmannian {k : ℕ} (V : GrassmannianFin X k) : Grassmannian X :=
  ⟨V.1, GrassmannianFin.closedComplemented k V⟩

/-! ### The distance on `𝒢X`

`𝒢X` carries the Hausdorff distance between unit spheres. It is an extended distance: the unit
sphere of `0` is empty, at infinite distance from every nonempty set. -/

/-- Every subspace is spanned by its unit sphere. -/
theorem span_sphere_inter (V : Submodule ℝ X) :
    Submodule.span ℝ (Metric.sphere (0 : X) 1 ∩ (V : Set X)) = V := by
  apply le_antisymm
  · exact Submodule.span_le.2 Set.inter_subset_right
  · intro x hx
    rcases eq_or_ne x 0 with rfl | hx0
    · exact Submodule.zero_mem _
    · have hxeq : x = ‖x‖ • (‖x‖⁻¹ • x) := by
        rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hx0), one_smul]
      rw [hxeq]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨?_, V.smul_mem _ hx⟩)
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.2 hx0)]

/-- The unit sphere `𝕊_V = 𝕊_X ∩ V` of `V ∈ 𝒢X`. -/
def Grassmannian.sphere (V : Grassmannian X) : Set X :=
  Metric.sphere (0 : X) 1 ∩ (V.1 : Set X)

theorem Grassmannian.isClosed_sphere (V : Grassmannian X) : IsClosed V.sphere :=
  Metric.isClosed_sphere.inter V.2.isClosed

/-- `V ↦ 𝕊_V`, as a closed subset of `X`. -/
def Grassmannian.toCloseds (V : Grassmannian X) : Closeds X :=
  ⟨V.sphere, V.isClosed_sphere⟩

theorem Grassmannian.toCloseds_injective :
    Function.Injective (Grassmannian.toCloseds (X := X)) := by
  intro V W h
  apply Subtype.ext
  rw [← span_sphere_inter V.1, ← span_sphere_inter W.1]
  exact congrArg (fun s : Closeds X => Submodule.span ℝ (s : Set X)) h

/-- `𝒢X` with the Hausdorff extended distance between unit spheres. -/
noncomputable instance instEMetricSpaceGrassmannian : EMetricSpace (Grassmannian X) :=
  EMetricSpace.induced Grassmannian.toCloseds Grassmannian.toCloseds_injective inferInstance

/-- The Borel `σ`-algebra of that extended metric. -/
noncomputable instance instMeasurableSpaceGrassmannian : MeasurableSpace (Grassmannian X) :=
  borel (Grassmannian X)

instance instBorelSpaceGrassmannian : BorelSpace (Grassmannian X) := ⟨rfl⟩

theorem Grassmannian.edist_eq (V W : Grassmannian X) :
    edist V W = Metric.hausdorffEDist V.sphere W.sphere :=
  rfl

/-- Given a direct sum decomposition `X = U ⊕ V`, the projection `Π_{U∥V} : X → U`
parallel to `V`, from the Definition opening Section 2.

**Hypotheses corrected.** This used to take `hb : U.ClosedComplemented`, which is not enough:
`ClosedComplemented` says *some* continuous projection onto `U` exists, not that the one along
`V` is continuous, and it says nothing at all about `V`. The projection along `V` is continuous
exactly when both summands are closed and `X` is complete (closed graph theorem, via Mathlib's
`Submodule.projectionOntoL`), so those are the hypotheses now. Both are available at the one
intended call site, where `U` is finite-dimensional and `V` is a closed slow space. -/
noncomputable def parallelProj [CompleteSpace X] {U V : Submodule ℝ X} (h : IsCompl U V)
    (hU : IsClosed (U : Set X)) (hV : IsClosed (V : Set X)) : X →L[ℝ] X :=
  U.subtypeL.comp (U.projectionOntoL V (Submodule.IsCompl.isTopCompl_of_isClosed h hU hV))

theorem parallelProj_mem [CompleteSpace X] {U V : Submodule ℝ X} (h : IsCompl U V)
    (hU : IsClosed (U : Set X)) (hV : IsClosed (V : Set X)) (x : X) :
    parallelProj h hU hV x ∈ U :=
  (U.projectionOntoL V (Submodule.IsCompl.isTopCompl_of_isClosed h hU hV) x).2

theorem parallelProj_of_mem_left [CompleteSpace X] {U V : Submodule ℝ X} (h : IsCompl U V)
    (hU : IsClosed (U : Set X)) (hV : IsClosed (V : Set X)) {x : X} (hx : x ∈ U) :
    parallelProj h hU hV x = x := by
  change ((U.projectionOntoL V (Submodule.IsCompl.isTopCompl_of_isClosed h hU hV)) x : X) = x
  rw [Submodule.coe_projectionOntoL]
  rw [Submodule.projectionOnto_apply_of_mem_left h hx]

theorem parallelProj_of_mem_right [CompleteSpace X] {U V : Submodule ℝ X} (h : IsCompl U V)
    (hU : IsClosed (U : Set X)) (hV : IsClosed (V : Set X)) {x : X} (hx : x ∈ V) :
    parallelProj h hU hV x = 0 := by
  change ((U.projectionOntoL V (Submodule.IsCompl.isTopCompl_of_isClosed h hU hV)) x : X) = 0
  rw [Submodule.coe_projectionOntoL, Submodule.projectionOnto_apply_of_mem_right h hx]
  rfl

theorem parallelProj_idem [CompleteSpace X] {U V : Submodule ℝ X} (h : IsCompl U V)
    (hU : IsClosed (U : Set X)) (hV : IsClosed (V : Set X)) :
    (parallelProj h hU hV).comp (parallelProj h hU hV) = parallelProj h hU hV := by
  ext x
  exact parallelProj_of_mem_left h hU hV (parallelProj_mem h hU hV x)

theorem parallelProj_sub_mem [CompleteSpace X] {U V : Submodule ℝ X} (h : IsCompl U V)
    (hU : IsClosed (U : Set X)) (hV : IsClosed (V : Set X)) (x : X) :
    x - parallelProj h hU hV x ∈ V := by
  have hx : x ∈ (⊤ : Submodule ℝ X) := Submodule.mem_top
  rw [← h.sup_eq_top] at hx
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hx
  have h1 : parallelProj h hU hV (u + v) = u := by
    rw [map_add, parallelProj_of_mem_left h hU hV hu, parallelProj_of_mem_right h hU hV hv,
      add_zero]
  rw [h1]
  simpa using hv

/-- The unit sphere of `V`: `𝕊_V = 𝕊_X ∩ V`, as a subset of `X`. -/
def GrassmannianFin.sphere {k : ℕ} (V : GrassmannianFin X k) : Set X :=
  Metric.sphere (0 : X) 1 ∩ (V.1 : Set X)

/-- Every `V ∈ 𝒢_kX` is spanned by its own unit sphere (any nonzero `x ∈ V` is a scalar
multiple of the unit vector `x / ‖x‖ ∈ 𝕊_V`). Holds even for `k = 0`, where both sides are `⊥`. -/
theorem GrassmannianFin.span_sphere {k : ℕ} (V : GrassmannianFin X k) :
    Submodule.span ℝ V.sphere = (V.1 : Submodule ℝ X) :=
  span_sphere_inter V.1

/-- `V ↦ 𝕊_V` is injective: it recovers `V` as the span of its image. -/
theorem GrassmannianFin.sphere_injective (k : ℕ) :
    Function.Injective (GrassmannianFin.sphere (X := X) (k := k)) := by
  intro V W h
  apply Subtype.ext
  rw [← V.span_sphere, ← W.span_sphere, h]

/-- `𝕊_V` is compact: `V` is finite-dimensional, hence a proper space, so its closed unit
sphere is compact, and this transfers to `X` along the (continuous) inclusion `V ↪ X`. -/
theorem GrassmannianFin.isCompact_sphere {k : ℕ} (V : GrassmannianFin X k) :
    IsCompact V.sphere := by
  have : FiniteDimensional ℝ (V.1 : Submodule ℝ X) := V.2.1
  have himg : V.sphere =
      (Subtype.val : (V.1 : Submodule ℝ X) → X) '' Metric.sphere (0 : (V.1 : Submodule ℝ X)) 1 := by
    ext x
    simp only [GrassmannianFin.sphere, Set.mem_inter_iff, Set.mem_image]
    constructor
    · rintro ⟨hx1, hxV⟩
      refine ⟨⟨x, hxV⟩, ?_, rfl⟩
      rw [mem_sphere_zero_iff_norm] at hx1 ⊢
      exact hx1
    · rintro ⟨v, hv, rfl⟩
      rw [mem_sphere_zero_iff_norm] at hv
      exact ⟨by rwa [mem_sphere_zero_iff_norm], v.2⟩
  rw [himg]
  exact (_root_.isCompact_sphere (0 : (V.1 : Submodule ℝ X)) 1).image continuous_subtype_val

/-- `𝕊_V` is nonempty as long as `k ≠ 0` (for `k = 0`, `V = ⊥` and `𝕊_V = ∅`). -/
theorem GrassmannianFin.nonempty_sphere {k : ℕ} [NeZero k] (V : GrassmannianFin X k) :
    V.sphere.Nonempty := by
  have hne : (V.1 : Submodule ℝ X) ≠ ⊥ := by
    intro h
    apply NeZero.ne k
    have hfr := V.2.2
    rw [h, finrank_bot] at hfr
    exact hfr.symm
  obtain ⟨x, hxV, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨‖x‖⁻¹ • x, ?_, V.1.smul_mem _ hxV⟩
  rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.2 hx0)]

/-- `V ↦ 𝕊_V`, bundled as a nonempty compact subset of `X`: this is what carries the
Grassmannian's metric structure (Hausdorff distance between unit spheres, as remarked after
the Definition), via `MetricSpace.induced` along this injective map. -/
noncomputable def GrassmannianFin.toNonemptyCompacts {k : ℕ} [NeZero k]
    (V : GrassmannianFin X k) : TopologicalSpace.NonemptyCompacts X where
  carrier := V.sphere
  isCompact' := V.isCompact_sphere
  nonempty' := V.nonempty_sphere

theorem GrassmannianFin.toNonemptyCompacts_injective (k : ℕ) [NeZero k] :
    Function.Injective (GrassmannianFin.toNonemptyCompacts (X := X) (k := k)) := by
  intro V W h
  apply GrassmannianFin.sphere_injective
  exact congrArg (fun s : TopologicalSpace.NonemptyCompacts X => (s : Set X)) h

/-- `𝒢_kX`'s metric (Hausdorff distance between unit spheres), pulled back along the injection
into `NonemptyCompacts X` -- for `k ≠ 0` (see `GrassmannianFin.nonempty_sphere`). -/
noncomputable instance instMetricSpaceGrassmannianFin (k : ℕ) [NeZero k] :
    MetricSpace (GrassmannianFin X k) :=
  MetricSpace.induced GrassmannianFin.toNonemptyCompacts
    (GrassmannianFin.toNonemptyCompacts_injective k) inferInstance

/-- `dist` on `𝒢_kX` unfolds to the Hausdorff distance between unit spheres: this is the bridge
used to extract "nearby point" facts for the continuity of `g`. -/
theorem GrassmannianFin.dist_eq_hausdorffDist {k : ℕ} [NeZero k] (V W : GrassmannianFin X k) :
    dist V W = Metric.hausdorffDist V.sphere W.sphere :=
  rfl

/-- The Borel σ-algebra of `𝒢_kX`'s metric topology. -/
noncomputable instance instMeasurableSpaceGrassmannianFin (k : ℕ) [NeZero k] :
    MeasurableSpace (GrassmannianFin X k) :=
  borel (GrassmannianFin X k)

instance instBorelSpaceGrassmannianFin (k : ℕ) [NeZero k] :
    BorelSpace (GrassmannianFin X k) := ⟨rfl⟩

/-- **Lemma \ref{GXsep}, part 1a (separability).** If `X` is separable then `𝒢_kX` is
separable. -/
theorem grassmannianFin_separable [SeparableSpace X] (k : ℕ) [NeZero k] :
    SeparableSpace (GrassmannianFin X k) := by
  -- A separable metric space is second countable; second countability passes to
  -- `NonemptyCompacts X` (Vietoris = Hausdorff-metric topology, so Mathlib's instance applies).
  have : SecondCountableTopology X := UniformSpace.secondCountable_of_separable X
  -- `V ↦ 𝕊_V` is an isometric embedding into `NonemptyCompacts X` (the metric on `𝒢_kX` is,
  -- by construction, the pullback of the Hausdorff-distance metric), hence `𝒢_kX` embeds into a
  -- second-countable space and is therefore separable.
  have hiso : Isometry (GrassmannianFin.toNonemptyCompacts (X := X) (k := k)) :=
    Isometry.of_dist_eq fun _ _ => rfl
  exact hiso.isEmbedding.separableSpace

/-! ### Completeness

`𝒢_kX` is complete when `X` is (Kato IV.2.1). The proof below is self-contained. Its shape is
dictated by one obstruction: the obvious argument — take a unit frame of the first term of a
Cauchy sequence, transport it along the sequence, and pass to the limit — is *circular*. The
transport step needs the steps to be small compared with `1/K`, where `K` is the conditioning
constant of the frame one starts from; but which term of the sequence one starts from is itself
determined by how small the steps have to be. A frame at an early index cannot be carried to a
deep one, and the conditioning at a deep index is not known before the index is chosen.

The way out is to take the frame in the *limit* object instead. `S_{V_j}` is Cauchy in
`NonemptyCompacts X`, which is complete, so it converges to a compact `K ⊆ 𝕊_X`; a frame chosen
inside `K` has a conditioning constant that is simply a fixed number, and every `V_j` then
carries a perturbation of it. That `K` supports `k` independent vectors at all — that the
dimension does not drop in the limit — is `hmeq` below, and is where Riesz's lemma enters. -/

section Complete

open Filter
open scoped Topology

/-- **Conditioning of a frame.** A linearly independent finite family controls the coefficient
vector by the norm of the combination: `‖a‖ ≤ K ‖∑ aᵢ vᵢ‖`. This is `K = 1/c(v)` for the usual
modulus `c(v) = inf {‖∑ aᵢ vᵢ‖ : ‖a‖ = 1}`, obtained from Mathlib's antilipschitz bound for an
injective map out of a finite-dimensional space. -/
theorem LinearIndependent.exists_norm_coeff_le {k : ℕ} {v : Fin k → X}
    (hv : LinearIndependent ℝ v) :
    ∃ K : ℝ, 0 < K ∧ ∀ a : Fin k → ℝ, ‖a‖ ≤ K * ‖∑ i, a i • v i‖ := by
  classical
  set L : (Fin k → ℝ) →ₗ[ℝ] X :=
    LinearMap.lsum ℝ (fun _ : Fin k => ℝ) ℕ fun i => LinearMap.id.smulRight (v i) with hL
  have hker : LinearMap.ker L = ⊥ := Fintype.linearIndependent_iff'.mp hv
  obtain ⟨K, hK0, hK⟩ := L.exists_antilipschitzWith hker
  have hKR : (0:ℝ) < K := by exact_mod_cast hK0
  refine ⟨K, hKR, fun a => ?_⟩
  have h := hK.le_mul_dist a 0
  have hLa : L a = ∑ i, a i • v i := by simp [hL]
  simpa [hLa, dist_zero_right, map_zero] using h

/-- **Conditioning is stable under small perturbations**, at the cost of a factor `2`. This is
what lets a frame of the limit object be transported into every nearby subspace at once: the
constant `2K` does not depend on which subspace. -/
theorem norm_coeff_le_of_perturb {k : ℕ} {v w : Fin k → X} {K η : ℝ} (hK0 : 0 ≤ K)
    (hv : ∀ a : Fin k → ℝ, ‖a‖ ≤ K * ‖∑ i, a i • v i‖)
    (hη : ∀ i, ‖w i - v i‖ ≤ η) (hsmall : K * k * η ≤ 1/2) :
    ∀ a : Fin k → ℝ, ‖a‖ ≤ 2 * K * ‖∑ i, a i • w i‖ := by
  intro a
  have hdiff : ‖(∑ i, a i • v i) - ∑ i, a i • w i‖ ≤ k * ‖a‖ * η := by
    have hs : (∑ i, a i • v i) - ∑ i, a i • w i = ∑ i, a i • (v i - w i) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [smul_sub]
    rw [hs]
    calc ‖∑ i, a i • (v i - w i)‖ ≤ ∑ i, ‖a i • (v i - w i)‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin k, ‖a‖ * η := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [norm_smul, Real.norm_eq_abs]
          have h1 : |a i| ≤ ‖a‖ := by
            simpa [Real.norm_eq_abs] using norm_le_pi_norm a i
          have h2 : ‖v i - w i‖ ≤ η := by rw [norm_sub_rev]; exact hη i
          exact mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg a)
      _ = k * (‖a‖ * η) := by simp [Finset.sum_const, mul_comm]
      _ = k * ‖a‖ * η := by ring
  have hstep : ‖a‖ ≤ K * ‖∑ i, a i • w i‖ + K * (k * ‖a‖ * η) := by
    calc ‖a‖ ≤ K * ‖∑ i, a i • v i‖ := hv a
      _ ≤ K * (‖∑ i, a i • w i‖ + k * ‖a‖ * η) := by
          refine mul_le_mul_of_nonneg_left ?_ hK0
          calc ‖∑ i, a i • v i‖ = ‖(∑ i, a i • w i) + ((∑ i, a i • v i) - ∑ i, a i • w i)‖ := by
                congr 1; abel
            _ ≤ ‖∑ i, a i • w i‖ + ‖(∑ i, a i • v i) - ∑ i, a i • w i‖ := norm_add_le _ _
            _ ≤ ‖∑ i, a i • w i‖ + k * ‖a‖ * η := by linarith
      _ = K * ‖∑ i, a i • w i‖ + K * (k * ‖a‖ * η) := by ring
  have hhalf : K * (k * ‖a‖ * η) ≤ ‖a‖ / 2 := by
    have hre : K * (k * ‖a‖ * η) = (K * k * η) * ‖a‖ := by ring
    rw [hre]
    nlinarith [norm_nonneg a]
  linarith

/-- Normalising moves a unit vector by at most twice the distance: `‖x - y/‖y‖‖ ≤ 2‖x - y‖`. -/
theorem dist_normalize_le {x y : X} (hx : ‖x‖ = 1) (hy : y ≠ 0) :
    ‖x - ‖y‖⁻¹ • y‖ ≤ 2 * ‖x - y‖ := by
  have hy0 : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have key : ‖y - ‖y‖⁻¹ • y‖ = |‖y‖ - 1| := by
    have hs : y - ‖y‖⁻¹ • y = (1 - ‖y‖⁻¹) • y := by rw [sub_smul, one_smul]
    rw [hs, norm_smul, Real.norm_eq_abs]
    have h1 : |1 - ‖y‖⁻¹| * ‖y‖ = |(1 - ‖y‖⁻¹) * ‖y‖| := by
      rw [abs_mul, abs_of_pos hy0]
    rw [h1]
    congr 1
    field_simp
  have h2 : |‖y‖ - 1| ≤ ‖x - y‖ := by
    rw [← hx, norm_sub_rev x y]
    exact abs_norm_sub_norm_le y x
  calc ‖x - ‖y‖⁻¹ • y‖ ≤ ‖x - y‖ + ‖y - ‖y‖⁻¹ • y‖ := by
        simpa using norm_sub_le_norm_sub_add_norm_sub x y (‖y‖⁻¹ • y)
    _ = ‖x - y‖ + |‖y‖ - 1| := by rw [key]
    _ ≤ 2 * ‖x - y‖ := by linarith

/-- `k` independent vectors lying inside a `k`-dimensional subspace span it. -/
theorem GrassmannianFin.span_eq_of_frame {k : ℕ} {V : GrassmannianFin X k} {v : Fin k → X}
    (hmem : ∀ i, v i ∈ (V.1 : Set X)) (hind : LinearIndependent ℝ v) :
    (V.1 : Submodule ℝ X) = Submodule.span ℝ (Set.range v) := by
  have hle : Submodule.span ℝ (Set.range v) ≤ (V.1 : Submodule ℝ X) := by
    rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    exact hmem i
  have : FiniteDimensional ℝ (V.1 : Submodule ℝ X) := V.2.1
  have hr : Module.finrank ℝ (Submodule.span ℝ (Set.range v)) = k := by
    rw [finrank_span_eq_card hind]
    simp
  exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [hr, V.2.2])).symm

/-- One direction of the Hausdorff estimate: each unit vector of `W` is within `2kCD` of `𝕊_V`,
when `V` and `W` carry frames that are `D`-close and `C`-conditioned. Expand the vector in the
frame of `W`, replace that frame by the frame of `V` coefficient by coefficient, and normalise. -/
theorem GrassmannianFin.exists_close_sphere_point {k : ℕ} {V W : GrassmannianFin X k}
    {v w : Fin k → X} {C D : ℝ}
    (hvV : ∀ i, v i ∈ (V.1 : Set X))
    (hwspan : (W.1 : Submodule ℝ X) ≤ Submodule.span ℝ (Set.range w))
    (hcond : ∀ a : Fin k → ℝ, ‖a‖ ≤ C * ‖∑ i, a i • w i‖)
    (hclose : ∀ i, ‖v i - w i‖ ≤ D) (hC : 0 ≤ C)
    (hsmall : (k : ℝ) * C * D < 1) :
    ∀ x ∈ W.sphere, ∃ y ∈ V.sphere, dist x y ≤ 2 * k * C * D := by
  intro x hx
  obtain ⟨hx1, hxW⟩ := hx
  rw [mem_sphere_zero_iff_norm] at hx1
  obtain ⟨a, ha⟩ := Submodule.mem_span_range_iff_exists_fun ℝ |>.mp (hwspan hxW)
  have hanorm : ‖a‖ ≤ C := by
    have hc := hcond a
    rw [ha, hx1, mul_one] at hc
    exact hc
  set z : X := ∑ i, a i • v i with hz
  have hzV : z ∈ (V.1 : Submodule ℝ X) :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hvV i)
  have hxz : ‖x - z‖ ≤ (k : ℝ) * C * D := by
    have hsub : x - z = ∑ i, a i • (w i - v i) := by
      rw [← ha, hz, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [smul_sub]
    rw [hsub]
    calc ‖∑ i, a i • (w i - v i)‖ ≤ ∑ i, ‖a i • (w i - v i)‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin k, C * D := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [norm_smul, Real.norm_eq_abs]
          have h1 : |a i| ≤ C := le_trans (by simpa [Real.norm_eq_abs] using norm_le_pi_norm a i)
            hanorm
          have h2 : ‖w i - v i‖ ≤ D := by rw [norm_sub_rev]; exact hclose i
          exact mul_le_mul h1 h2 (norm_nonneg _) hC
      _ = (k : ℝ) * C * D := by simp [Finset.sum_const]; ring
  have hzne : z ≠ 0 := by
    intro h0
    rw [h0, sub_zero, hx1] at hxz
    linarith
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hzne
  refine ⟨‖z‖⁻¹ • z, ⟨?_, ?_⟩, ?_⟩
  · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm]
    field_simp
  · exact Submodule.smul_mem _ _ hzV
  · rw [dist_eq_norm]
    calc ‖x - ‖z‖⁻¹ • z‖ ≤ 2 * ‖x - z‖ := dist_normalize_le hx1 hzne
      _ ≤ 2 * ((k : ℝ) * C * D) := by linarith
      _ = 2 * k * C * D := by ring

/-- **Two `D`-close, `C`-conditioned frames span subspaces at Grassmannian distance `≤ 2kCD`.** -/
theorem GrassmannianFin.dist_le_of_frames {k : ℕ} [NeZero k] {V W : GrassmannianFin X k}
    {v w : Fin k → X} {C D : ℝ}
    (hvV : ∀ i, v i ∈ (V.1 : Set X)) (hwW : ∀ i, w i ∈ (W.1 : Set X))
    (hcv : ∀ a : Fin k → ℝ, ‖a‖ ≤ C * ‖∑ i, a i • v i‖)
    (hcw : ∀ a : Fin k → ℝ, ‖a‖ ≤ C * ‖∑ i, a i • w i‖)
    (hclose : ∀ i, ‖v i - w i‖ ≤ D) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hsmall : (k : ℝ) * C * D < 1) :
    dist V W ≤ 2 * k * C * D := by
  have hvspan : (V.1 : Submodule ℝ X) = Submodule.span ℝ (Set.range v) :=
    GrassmannianFin.span_eq_of_frame hvV (linearIndependent_of_norm_coeff_le hcv)
  have hwspan : (W.1 : Submodule ℝ X) = Submodule.span ℝ (Set.range w) :=
    GrassmannianFin.span_eq_of_frame hwW (linearIndependent_of_norm_coeff_le hcw)
  have hclose' : ∀ i, ‖w i - v i‖ ≤ D := fun i => by rw [norm_sub_rev]; exact hclose i
  rw [GrassmannianFin.dist_eq_hausdorffDist]
  refine Metric.hausdorffDist_le_of_mem_dist (by positivity) ?_ ?_
  · exact GrassmannianFin.exists_close_sphere_point hwW hvspan.le hcv hclose' hC hsmall
  · intro y hy
    obtain ⟨x, hx, hd⟩ :=
      GrassmannianFin.exists_close_sphere_point hvV hwspan.le hcw hclose hC hsmall y hy
    exact ⟨x, hx, hd⟩

/-- **Riesz's lemma, uniformly.** A proper subspace `U < V` of a `k`-dimensional `V` is missed by
some unit vector of `V` by a margin of `1/2` — and crucially the margin does not depend on `U`
or `V`. This is what rules out a drop in dimension along a Cauchy sequence. -/
theorem GrassmannianFin.exists_far_from_proper {k : ℕ} (V : GrassmannianFin X k)
    (U : Submodule ℝ X) (hUV : U ≤ (V.1 : Submodule ℝ X)) (hlt : Module.finrank ℝ U < k) :
    ∃ x ∈ V.sphere, ∀ y ∈ U, (1/2 : ℝ) ≤ ‖x - y‖ := by
  have : FiniteDimensional ℝ ((V.1 : Submodule ℝ X)) := V.2.1
  set F : Submodule ℝ ((V.1 : Submodule ℝ X)) := U.comap (V.1 : Submodule ℝ X).subtype with hFdef
  have hFc : IsClosed (F : Set ((V.1 : Submodule ℝ X))) := Submodule.closed_of_finiteDimensional F
  have hFne : ∃ z : ((V.1 : Submodule ℝ X)), z ∉ F := by
    by_contra hcon
    rw [not_exists] at hcon
    have hVU : (V.1 : Submodule ℝ X) ≤ U := by
      intro x hx
      have h1 := hcon ⟨x, hx⟩
      rw [not_not] at h1
      simpa [hFdef, Submodule.mem_comap] using h1
    have heq : U = (V.1 : Submodule ℝ X) := le_antisymm hUV hVU
    rw [heq, V.2.2] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨z, hzF, hz⟩ := riesz_lemma hFc hFne (r := 1/2) (by norm_num)
  have hz0 : (z : X) ≠ 0 := by
    intro h
    apply hzF
    have hz0' : z = 0 := Subtype.ext h
    rw [hz0']
    exact F.zero_mem
  have hznpos : 0 < ‖(z : X)‖ := norm_pos_iff.mpr hz0
  refine ⟨‖(z:X)‖⁻¹ • (z:X), ⟨?_, ?_⟩, ?_⟩
  · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (ne_of_gt hznpos)]
  · exact (V.1 : Submodule ℝ X).smul_mem _ z.2
  · intro y hy
    have hyV : y ∈ (V.1 : Submodule ℝ X) := hUV hy
    have hmem : (‖(z:X)‖ • (⟨y, hyV⟩ : ((V.1 : Submodule ℝ X)))) ∈ F := by
      rw [hFdef, Submodule.mem_comap]
      exact U.smul_mem _ hy
    have hriesz := hz _ hmem
    have hcoe : ((z - ‖(z:X)‖ • (⟨y, hyV⟩ : ((V.1 : Submodule ℝ X)))  : (V.1 : Submodule ℝ X)) : X)
        = (z:X) - ‖(z:X)‖ • y := by simp
    have hnormeq : ‖z - ‖(z:X)‖ • (⟨y, hyV⟩ : ((V.1 : Submodule ℝ X)))‖
        = ‖(z:X) - ‖(z:X)‖ • y‖ := by
      rw [← hcoe]; rfl
    rw [hnormeq] at hriesz
    have hsub : (z:X) - ‖(z:X)‖ • y = ‖(z:X)‖ • (‖(z:X)‖⁻¹ • (z:X) - y) := by
      rw [smul_sub, smul_smul, mul_inv_cancel₀ (ne_of_gt hznpos), one_smul]
    rw [hsub, norm_smul, norm_norm] at hriesz
    have hzn : ‖z‖ = ‖(z:X)‖ := rfl
    rw [hzn] at hriesz
    nlinarith [norm_nonneg (‖(z:X)‖⁻¹ • (z:X) - y)]

open MeasureTheory Metric in
/-- **Lemma \ref{GXcomplete}.** `𝒢_kX` is complete when `X` is a Banach space
(`kato2013perturbation`, chapter IV, section 2.1). Separability is *not* needed.

**`[CompleteSpace X]` is not optional — without it the statement is false.** The file's section
variables give `X` only `NormedAddCommGroup` and `NormedSpace ℝ`, but `\ref{GXcomplete}` says
"let `X` be a Banach space". Counterexample over an incomplete `X`: take `X = c₀₀` with the sup
norm and `k = 1`. Let `vₙ = (1, 1/2, …, 1/n, 0, …)` normalised, so `vₙ → v = (1, 1/2, …) ∈ c₀`,
which is not in `c₀₀`. The unit sphere of `span vₙ` is `{±vₙ}`, so the Hausdorff distance between
the spheres of `span vₙ` and `span vₘ` is `min ‖vₙ - vₘ‖ ‖vₙ + vₘ‖ → 0` and the sequence is
Cauchy in `𝒢₁X`; but a limit `span w` with `w ∈ c₀₀` would force `vₙ → ±w` in `c₀₀`, whence
`w = ±v ∉ c₀₀`. So `𝒢₁(c₀₀)` is not complete. -/
theorem grassmannianFin_complete [CompleteSpace X] (k : ℕ) [NeZero k] :
    CompleteSpace (GrassmannianFin X k) := by
  classical
  refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
  have hiso : Isometry (GrassmannianFin.toNonemptyCompacts (X := X) (k := k)) :=
    Isometry.of_dist_eq fun _ _ => rfl
  -- The unit spheres form a Cauchy sequence of nonempty compacta, which converges.
  have hSC : CauchySeq (fun j => (u j).toNonemptyCompacts) :=
    hiso.uniformContinuous.comp_cauchySeq hu
  obtain ⟨Kc, hKc⟩ := cauchySeq_tendsto_of_complete hSC
  set Kset : Set X := (Kc : Set X) with hKsetdef
  set D : ℕ → ℝ := fun j => Metric.hausdorffDist (u j).sphere Kset with hDdef
  have hD0 : Tendsto D atTop (𝓝 0) := tendsto_iff_dist_tendsto_zero.mp hKc
  have hKne : Kset.Nonempty := Kc.nonempty
  have hedist : ∀ j, Metric.hausdorffEDist (u j).sphere Kset ≠ ⊤ := fun j =>
    Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded (u j).nonempty_sphere hKne
      (u j).isCompact_sphere.isBounded Kc.isCompact.isBounded
  have hedist' : ∀ j, Metric.hausdorffEDist Kset (u j).sphere ≠ ⊤ := fun j => by
    rw [Metric.hausdorffEDist_comm]; exact hedist j
  have hDcomm : ∀ j, Metric.hausdorffDist Kset (u j).sphere = D j := fun j =>
    Metric.hausdorffDist_comm
  -- Every point of the limit compact set is a unit vector.
  have hKnorm : ∀ x ∈ Kset, ‖x‖ = 1 := by
    intro x hx
    have key : ∀ ε > 0, |‖x‖ - 1| < ε := by
      intro ε hε
      obtain ⟨j, hj⟩ := (hD0.eventually (gt_mem_nhds hε)).exists
      obtain ⟨y, hy, hxy⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt hx
        (by rw [hDcomm j]; exact hj) (hedist' j)
      have hy1 : ‖y‖ = 1 := mem_sphere_zero_iff_norm.mp hy.1
      calc |‖x‖ - 1| = |‖x‖ - ‖y‖| := by rw [hy1]
        _ ≤ ‖x - y‖ := abs_norm_sub_norm_le x y
        _ = dist x y := (dist_eq_norm x y).symm
        _ < ε := hxy
    have h0 : |‖x‖ - 1| = 0 := by
      by_contra hne
      exact lt_irrefl _ (key _ (lt_of_le_of_ne (abs_nonneg _) (Ne.symm hne)))
    linarith [abs_eq_zero.mp h0]
  -- The largest independent family the limit set supports.
  set P : ℕ → Prop := fun m => ∃ f : Fin m → X, (∀ i, f i ∈ Kset) ∧ LinearIndependent ℝ f
    with hPdef
  have hP0 : P 0 := ⟨Fin.elim0, fun i => i.elim0, linearIndependent_empty_type⟩
  set m := Nat.findGreatest P k with hmdef
  have hPm : P m := Nat.findGreatest_spec (Nat.zero_le k) hP0
  have hmk : m ≤ k := Nat.findGreatest_le k
  -- The maximum is `k`: the dimension cannot drop in the limit.  If it did, the limit set would
  -- lie in the span of `m < k` of its own points; transporting that span back into `u j` gives a
  -- proper subspace of `u j` that every unit vector of `u j` is within `(1 + mC)r` of, which
  -- Riesz's lemma forbids once `r` is small.
  have hmeq : m = k := by
    by_contra hne
    have hmlt : m < k := lt_of_le_of_ne hmk hne
    obtain ⟨f, hfK, hfind⟩ := hPm
    obtain ⟨C, hC0, hC⟩ := LinearIndependent.exists_norm_coeff_le hfind
    have hspan : ∀ x ∈ Kset, x ∈ Submodule.span ℝ (Set.range f) := by
      intro x hx
      by_contra hnot
      have hPsucc : P (m + 1) :=
        ⟨Fin.cons x f, fun i => Fin.cases hx hfK i,
          linearIndependent_finCons.mpr ⟨hfind, hnot⟩⟩
      exact @Nat.findGreatest_is_greatest (m + 1) P _ k (by omega) (by omega) hPsucc
    set r : ℝ := 1 / (4 * (1 + m * C)) with hrdef
    have hden : (0:ℝ) < 1 + (m:ℝ) * C := by
      have : (0:ℝ) ≤ (m:ℝ) * C := mul_nonneg (Nat.cast_nonneg m) hC0.le
      linarith
    have hrpos : 0 < r := by rw [hrdef]; exact div_pos one_pos (by linarith)
    obtain ⟨j, hj⟩ := (hD0.eventually (gt_mem_nhds hrpos)).exists
    have hstep : ∀ i, ∃ y ∈ (u j).sphere, dist (f i) y < r := fun i =>
      Metric.exists_dist_lt_of_hausdorffDist_lt (hfK i) (by rw [hDcomm j]; exact hj) (hedist' j)
    choose e hemem hedst using hstep
    set U : Submodule ℝ X := Submodule.span ℝ (Set.range e) with hUdef
    have hUle : U ≤ ((u j).1 : Submodule ℝ X) := by
      rw [hUdef, Submodule.span_le]
      rintro x ⟨i, rfl⟩
      exact (hemem i).2
    have hUrank : Module.finrank ℝ U < k := by
      have h1 : Module.finrank ℝ (Submodule.span ℝ (Set.range e)) ≤ m := by
        simpa [Set.finrank, Fintype.card_fin] using finrank_range_le_card (R := ℝ) e
      exact lt_of_le_of_lt h1 hmlt
    obtain ⟨x, hxs, hxfar⟩ := GrassmannianFin.exists_far_from_proper (u j) U hUle hUrank
    obtain ⟨y, hyK, hxy⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt hxs hj (hedist j)
    obtain ⟨a, ha⟩ := Submodule.mem_span_range_iff_exists_fun ℝ |>.mp (hspan y hyK)
    have hanorm : ‖a‖ ≤ C := by
      have h := hC a
      rw [ha, hKnorm y hyK, mul_one] at h
      exact h
    have hyz : ‖y - ∑ i, a i • e i‖ ≤ (m : ℝ) * C * r := by
      have hsub : y - ∑ i, a i • e i = ∑ i, a i • (f i - e i) := by
        rw [← ha, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by rw [smul_sub]
      rw [hsub]
      calc ‖∑ i, a i • (f i - e i)‖ ≤ ∑ i, ‖a i • (f i - e i)‖ := norm_sum_le _ _
        _ ≤ ∑ _i : Fin m, C * r := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [norm_smul, Real.norm_eq_abs]
            have h1 : |a i| ≤ C :=
              le_trans (by simpa [Real.norm_eq_abs] using norm_le_pi_norm a i) hanorm
            have h2 : ‖f i - e i‖ ≤ r := le_of_lt (by rw [← dist_eq_norm]; exact hedst i)
            exact mul_le_mul h1 h2 (norm_nonneg _) hC0.le
        _ = (m : ℝ) * C * r := by simp [Finset.sum_const]; ring
    have hzU : (∑ i, a i • e i) ∈ U := by
      refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
      exact Submodule.subset_span ⟨i, rfl⟩
    have hfar := hxfar _ hzU
    have hxyn : ‖x - y‖ < r := by rw [← dist_eq_norm]; exact hxy
    have htri : ‖x - ∑ i, a i • e i‖ ≤ ‖x - y‖ + ‖y - ∑ i, a i • e i‖ := by
      simpa using norm_sub_le_norm_sub_add_norm_sub x y (∑ i, a i • e i)
    have hrid : (1 + (m:ℝ) * C) * r = 1/4 := by
      rw [hrdef]; field_simp
    nlinarith [hfar, htri, hxyn, hyz, hrid]
  -- The limit subspace: the span of a maximal independent family inside the limit compact set.
  rw [hmeq] at hPm
  obtain ⟨f, hfK, hfind⟩ := hPm
  obtain ⟨C, hC0, hC⟩ := LinearIndependent.exists_norm_coeff_le hfind
  have : FiniteDimensional ℝ (Submodule.span ℝ (Set.range f)) :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_range f)
  set W : GrassmannianFin X k :=
    ⟨Submodule.span ℝ (Set.range f), ⟨inferInstance, by rw [finrank_span_eq_card hfind]; simp⟩⟩
    with hWdef
  refine ⟨W, ?_⟩
  rw [tendsto_iff_dist_tendsto_zero]
  set ρ : ℕ → ℝ := fun j => D j + (1/2:ℝ) ^ j with hρdef
  have hρpos : ∀ j, 0 < ρ j := fun j => by
    have h1 : (0:ℝ) < (1/2:ℝ) ^ j := by positivity
    have h2 := Metric.hausdorffDist_nonneg (s := (u j).sphere) (t := Kset)
    simp only [hρdef]
    linarith
  have hρ0 : Tendsto ρ atTop (𝓝 0) := by
    have h2 : Tendsto (fun j : ℕ => (1/2:ℝ) ^ j) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have h3 := hD0.add h2
    rw [add_zero] at h3
    exact h3
  -- A frame of `W` transported into each `u j`, with error `ρ j → 0`.
  have hstep : ∀ j, ∀ i, ∃ y ∈ (u j).sphere, dist (f i) y < ρ j := by
    intro j i
    refine Metric.exists_dist_lt_of_hausdorffDist_lt (hfK i) ?_ (hedist' j)
    rw [hDcomm j, hρdef]
    have h1 : (0:ℝ) < (1/2:ℝ) ^ j := by positivity
    exact lt_add_of_pos_right _ h1
  choose e hemem hedst using hstep
  have hkpos : (0:ℝ) < k := by
    have := Nat.pos_of_ne_zero (NeZero.ne k); exact_mod_cast this
  have hbound : ∀ᶠ j in atTop, dist (u j) W ≤ 4 * k * C * ρ j := by
    have hposC : (0:ℝ) < 4 * C * (k:ℝ) := by nlinarith
    have hsmall : ∀ᶠ j in atTop, ρ j < 1 / (4 * C * (k:ℝ)) :=
      hρ0.eventually (gt_mem_nhds (div_pos one_pos hposC))
    filter_upwards [hsmall] with j hj
    rw [lt_div_iff₀ hposC] at hj
    have hρj := (hρpos j).le
    have hclose : ∀ i, ‖e j i - f i‖ ≤ ρ j := by
      intro i
      have h := hedst j i
      rw [dist_eq_norm, ← norm_neg] at h
      simp only [neg_sub] at h
      exact h.le
    have hcond : ∀ a : Fin k → ℝ, ‖a‖ ≤ 2 * C * ‖∑ i, a i • e j i‖ :=
      norm_coeff_le_of_perturb (η := ρ j) hC0.le hC hclose (by nlinarith)
    have hCf : ∀ a : Fin k → ℝ, ‖a‖ ≤ 2 * C * ‖∑ i, a i • f i‖ := by
      intro a
      have h := hC a
      nlinarith [norm_nonneg (∑ i, a i • f i)]
    have hlt1 : (k:ℝ) * (2 * C) * ρ j < 1 := by nlinarith
    have hmain := GrassmannianFin.dist_le_of_frames (V := u j) (W := W) (v := e j) (w := f)
      (fun i => (hemem j i).2) (fun i => Submodule.subset_span ⟨i, rfl⟩)
      hcond hCf hclose (by linarith) hρj hlt1
    calc dist (u j) W ≤ 2 * k * (2 * C) * ρ j := hmain
      _ = 4 * k * C * ρ j := by ring
  refine squeeze_zero' (Eventually.of_forall fun j => dist_nonneg) hbound ?_
  have hfin : Tendsto (fun j => 4 * (k:ℝ) * C * ρ j) atTop (𝓝 (4 * k * C * 0)) :=
    hρ0.const_mul _
  simpa using hfin

end Complete

section InfDistSubspace

open MeasureTheory Metric

theorem infDist_le_of_mem_aux (k : ℕ) [NeZero k] (x : X) (V W : GrassmannianFin X k)
    {v : X} (hv : v ∈ (V.1 : Submodule ℝ X)) :
    infDist x ((W.1 : Submodule ℝ X) : Set X) ≤ ‖x - v‖ + ‖v‖ * dist V W := by
  have hWne : ((W.1 : Submodule ℝ X) : Set X).Nonempty := ⟨0, (W.1 : Submodule ℝ X).zero_mem⟩
  rcases eq_or_ne v 0 with rfl | hv0
  · have h0 := infDist_le_dist_of_mem (x := x) (y := (0 : X)) (W.1 : Submodule ℝ X).zero_mem
    rw [dist_eq_norm] at h0
    simpa using h0
  · have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv0
    set u : X := ‖v‖⁻¹ • v with hu
    have hunorm : ‖u‖ = 1 := by
      rw [hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (ne_of_gt hvpos)]
    have huS : u ∈ V.sphere :=
      ⟨mem_sphere_zero_iff_norm.2 hunorm, (V.1 : Submodule ℝ X).smul_mem _ hv⟩
    have hfin : Metric.hausdorffEDist V.sphere W.sphere ≠ ⊤ :=
      Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded V.nonempty_sphere W.nonempty_sphere
        V.isCompact_sphere.isBounded W.isCompact_sphere.isBounded
    have hle : infDist u W.sphere ≤ dist V W := by
      rw [GrassmannianFin.dist_eq_hausdorffDist]
      exact Metric.infDist_le_hausdorffDist_of_mem huS hfin
    obtain ⟨w, hwS, hw⟩ :=
      W.isCompact_sphere.exists_infDist_eq_dist W.nonempty_sphere u
    have hwW : (‖v‖ • w) ∈ (W.1 : Submodule ℝ X) :=
      (W.1 : Submodule ℝ X).smul_mem _ hwS.2
    have hvu : v = ‖v‖ • u := by
      rw [hu, smul_smul, mul_inv_cancel₀ (ne_of_gt hvpos), one_smul]
    have hstep : ‖v - ‖v‖ • w‖ = ‖v‖ * dist u w := by
      have h1 : v - ‖v‖ • w = ‖v‖ • (u - w) := by rw [smul_sub, ← hvu]
      rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos hvpos, dist_eq_norm]
    have hfinal := infDist_le_dist_of_mem (x := x) hwW
    rw [dist_eq_norm] at hfinal
    have htri : ‖x - ‖v‖ • w‖ ≤ ‖x - v‖ + ‖v - ‖v‖ • w‖ := by
      have : x - ‖v‖ • w = (x - v) + (v - ‖v‖ • w) := by abel
      rw [this]
      exact norm_add_le _ _
    have hdle : dist u w ≤ dist V W := by rw [← hw]; exact hle
    calc infDist x ((W.1 : Submodule ℝ X) : Set X) ≤ ‖x - ‖v‖ • w‖ := hfinal
      _ ≤ ‖x - v‖ + ‖v - ‖v‖ • w‖ := htri
      _ = ‖x - v‖ + ‖v‖ * dist u w := by rw [hstep]
      _ ≤ ‖x - v‖ + ‖v‖ * dist V W := by nlinarith [hvpos.le, dist_nonneg (x := u) (y := w)]

/-- **Distance to a subspace is `2‖x‖`-Lipschitz in the subspace.** -/
theorem infDist_subspace_le (k : ℕ) [NeZero k] (x : X) (V W : GrassmannianFin X k) :
    infDist x ((W.1 : Submodule ℝ X) : Set X)
      ≤ infDist x ((V.1 : Submodule ℝ X) : Set X) + 2 * ‖x‖ * dist V W := by
  have hVne : ((V.1 : Submodule ℝ X) : Set X).Nonempty := ⟨0, (V.1 : Submodule ℝ X).zero_mem⟩
  have hVx : infDist x ((V.1 : Submodule ℝ X) : Set X) ≤ ‖x‖ := by
    have := infDist_le_dist_of_mem (x := x) (y := (0 : X)) (V.1 : Submodule ℝ X).zero_mem
    rw [dist_eq_norm] at this
    simpa using this
  have hdnn : (0 : ℝ) ≤ dist V W := dist_nonneg
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set η : ℝ := ε / (1 + dist V W) with hη
  have hηpos : 0 < η := by rw [hη]; positivity
  obtain ⟨v, hvV, hvlt⟩ := (infDist_lt_iff hVne).1
    (lt_add_of_pos_right (infDist x ((V.1 : Submodule ℝ X) : Set X)) hηpos)
  rw [dist_eq_norm] at hvlt
  have hvnorm : ‖v‖ ≤ 2 * ‖x‖ + η := by
    have h1 : ‖v‖ ≤ ‖x‖ + ‖x - v‖ := by
      have : v = x - (x - v) := by abel
      rw [this]
      exact le_trans (norm_sub_le _ _) (by simp)
    linarith
  have haux := infDist_le_of_mem_aux k x V W hvV
  have hηε : η * (1 + dist V W) = ε := by
    rw [hη]; field_simp
  nlinarith [haux, hvlt, hvnorm, hdnn, norm_nonneg x, hηpos.le]

theorem continuous_infDist_subspace (k : ℕ) [NeZero k] (x : X) :
    Continuous fun V : GrassmannianFin X k => infDist x ((V.1 : Submodule ℝ X) : Set X) := by
  have hK : (0 : ℝ) ≤ 2 * ‖x‖ := by positivity
  refine LipschitzWith.continuous (K := ⟨2 * ‖x‖, hK⟩) ?_
  refine LipschitzWith.of_dist_le_mul fun V W => ?_
  have h1 := infDist_subspace_le k x V W
  have h2 := infDist_subspace_le k x W V
  rw [dist_comm W V] at h2
  change dist (infDist x ((V.1 : Submodule ℝ X) : Set X))
      (infDist x ((W.1 : Submodule ℝ X) : Set X)) ≤ 2 * ‖x‖ * dist V W
  rw [Real.dist_eq, abs_sub_le_iff]
  exact ⟨by linarith, by linarith⟩

/-- **Measurability into `𝒢_kX` is testable on distances to subspaces.**

The maps `V ↦ d(x, V)` are continuous (`continuous_infDist_subspace`) and separate points, so on
the Polish space `𝒢_kX` they assemble into a continuous injection into `ℝ^ℕ`, which is a
measurable embedding by Lusin--Souslin. Unlike `measurable_of_measurable_dist`, the test
functions here involve the *subspace*, not its unit sphere — which is what removes the
normalisation `y ↦ Ay/‖Ay‖` from the pushforward argument. -/
theorem measurable_of_measurable_infDist [SeparableSpace X] [CompleteSpace X] (k : ℕ) [NeZero k]
    {Ω : Type*} [MeasurableSpace Ω] {F : Ω → GrassmannianFin X k}
    (h : ∀ x : X, Measurable fun ω => infDist x ((F ω).1 : Set X)) :
    Measurable F := by
  have := grassmannianFin_separable (X := X) k
  have := grassmannianFin_complete (X := X) k
  have : SecondCountableTopology (GrassmannianFin X k) :=
    UniformSpace.secondCountable_of_separable _
  obtain ⟨D, hDcount, hDdense⟩ := TopologicalSpace.exists_countable_dense X
  have : Countable D := hDcount.to_subtype
  set Ψ : GrassmannianFin X k → (D → ℝ) :=
    fun V d => infDist ((d : X)) ((V.1 : Submodule ℝ X) : Set X) with hΨ
  have hΨcont : Continuous Ψ := continuous_pi fun d => continuous_infDist_subspace k (d : X)
  have hΨinj : Function.Injective Ψ := by
    intro V W hVW
    by_contra hne
    have hVfd : FiniteDimensional ℝ (V.1 : Submodule ℝ X) := V.2.1
    have hWfd : FiniteDimensional ℝ (W.1 : Submodule ℝ X) := W.2.1
    -- `V ≰ W`, else equal by dimension
    have hnle : ¬ ((V.1 : Submodule ℝ X) ≤ (W.1 : Submodule ℝ X)) := by
      intro hle
      exact hne (Subtype.ext (Submodule.eq_of_le_of_finrank_eq hle (by rw [V.2.2, W.2.2])))
    obtain ⟨v, hvV, hvW⟩ := Set.not_subset.1 hnle
    have hWclosed : IsClosed ((W.1 : Submodule ℝ X) : Set X) :=
      Submodule.closed_of_finiteDimensional _
    have hWne : ((W.1 : Submodule ℝ X) : Set X).Nonempty := ⟨0, (W.1 : Submodule ℝ X).zero_mem⟩
    have hr : 0 < infDist v ((W.1 : Submodule ℝ X) : Set X) := by
      refine (Metric.infDist_pos_iff_notMem_closure hWne).1 ?_
      rwa [hWclosed.closure_eq]
    set r : ℝ := infDist v ((W.1 : Submodule ℝ X) : Set X) with hrdef
    obtain ⟨d, hdD, hd⟩ := Metric.mem_closure_iff.1 (hDdense v) (r / 2) (by linarith)
    have h1 : infDist ((⟨d, hdD⟩ : D) : X) ((V.1 : Submodule ℝ X) : Set X) < r / 2 := by
      refine lt_of_le_of_lt (infDist_le_dist_of_mem hvV) ?_
      rwa [dist_comm] at hd
    have h2 : r / 2 < infDist ((⟨d, hdD⟩ : D) : X) ((W.1 : Submodule ℝ X) : Set X) := by
      have hlip := Metric.infDist_le_infDist_add_dist
        (x := v) (y := (d : X)) (s := ((W.1 : Submodule ℝ X) : Set X))
      have : dist v d < r / 2 := hd
      simp only [← hrdef] at hlip
      linarith
    have := congrFun hVW (⟨d, hdD⟩ : D)
    simp only [hΨ] at this
    linarith [h1, h2, this.le, this.ge]
  have hemb : MeasurableEmbedding Ψ := hΨcont.measurableEmbedding hΨinj
  rw [← hemb.measurable_comp_iff]
  exact measurable_pi_iff.mpr fun d => h ((d : D) : X)

/-- **The moving-subspace infimum.** For a measurable family `E` of subspaces and a strongly
measurable family `A` of operators, `ω ↦ d(x, A(ω)E(ω))` is measurable.

The approximants only ever evaluate `A ω` at *fixed* points of a countable dense set, so strong
measurability of `A` suffices: no joint measurability in `(ω, y)` is needed. -/
theorem measurable_infDist_map [SeparableSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (k : ℕ) [NeZero k] {Ω : Type*}
    [MeasurableSpace Ω] {E : Ω → GrassmannianFin X k} (hE : Measurable E)
    {A : Ω → X →L[ℝ] X} (hA : ∀ y : X, Measurable fun ω => A ω y) (x : X) :
    Measurable fun ω => infDist x ((A ω) '' (((E ω).1 : Submodule ℝ X) : Set X)) := by
  classical
  have : SecondCountableTopology X := UniformSpace.secondCountable_of_separable X
  obtain ⟨D, hDcount, hDdense⟩ := TopologicalSpace.exists_countable_dense X
  have : Countable D := hDcount.to_subtype
  have : Nonempty D := by
    obtain ⟨d, hd, -⟩ := hDdense.exists_mem_open isOpen_univ Set.univ_nonempty
    exact ⟨⟨d, hd⟩⟩
  set T : Ω → ℝ := fun ω => infDist x ((A ω) '' (((E ω).1 : Submodule ℝ X) : Set X)) with hTdef
  set f : ℕ → D → Ω → ℝ := fun m d ω =>
    if infDist ((d : X)) (((E ω).1 : Submodule ℝ X) : Set X) < 1 / (m + 1) then
      ‖x - A ω (d : X)‖ else ‖x‖ + 1 with hfdef
  set M : ℕ → Ω → ℝ := fun m ω => ⨅ d : D, f m d ω with hMdef
  -- basic facts, pointwise in ω
  have hEne : ∀ ω, ((((E ω).1 : Submodule ℝ X)) : Set X).Nonempty :=
    fun ω => ⟨0, ((E ω).1 : Submodule ℝ X).zero_mem⟩
  have hImne : ∀ ω, ((A ω) '' (((E ω).1 : Submodule ℝ X) : Set X)).Nonempty :=
    fun ω => ⟨A ω 0, ⟨0, ((E ω).1 : Submodule ℝ X).zero_mem, rfl⟩⟩
  have hTnn : ∀ ω, 0 ≤ T ω := fun ω => infDist_nonneg
  have hTx : ∀ ω, T ω ≤ ‖x‖ := by
    intro ω
    have h0 : A ω 0 ∈ (A ω) '' (((E ω).1 : Submodule ℝ X) : Set X) :=
      ⟨0, ((E ω).1 : Submodule ℝ X).zero_mem, rfl⟩
    have := infDist_le_dist_of_mem (x := x) h0
    simpa [dist_eq_norm] using this
  have hbddM : ∀ m ω, BddBelow (Set.range fun d : D => f m d ω) := by
    intro m ω
    refine ⟨0, ?_⟩
    rintro _ ⟨d, rfl⟩
    rw [hfdef]
    dsimp only
    split_ifs with h
    · exact norm_nonneg _
    · positivity
  -- (A) each approximant is below the true value
  have hMle : ∀ m ω, M m ω ≤ T ω := by
    intro m ω
    rw [hMdef, hTdef]
    refine (le_infDist (hImne ω)).2 ?_
    rintro _ ⟨y, hyE, rfl⟩
    refine le_of_forall_pos_le_add fun ε hε => ?_
    set η : ℝ := min (ε / (‖A ω‖ + 1)) (1 / (m + 1)) with hη
    have hηpos : 0 < η := by
      refine lt_min (by positivity) (by positivity)
    obtain ⟨d, hdD, hd⟩ := Metric.mem_closure_iff.1 (hDdense y) η hηpos
    have hdlt : infDist ((⟨d, hdD⟩ : D) : X) (((E ω).1 : Submodule ℝ X) : Set X) < 1 / (m + 1) := by
      refine lt_of_le_of_lt (infDist_le_dist_of_mem hyE) ?_
      have hd' : dist ((⟨d, hdD⟩ : D) : X) y < η := by rw [dist_comm]; exact hd
      exact lt_of_lt_of_le hd' (min_le_right _ _)
    have hfval : f m ⟨d, hdD⟩ ω = ‖x - A ω d‖ := by
      rw [hfdef]; dsimp only; rw [ite_eq_left hdlt]
    have hiInf : (⨅ d' : D, f m d' ω) ≤ ‖x - A ω d‖ := by
      rw [← hfval]
      exact ciInf_le (hbddM m ω) ⟨d, hdD⟩
    have hstep : ‖x - A ω d‖ ≤ dist x (A ω y) + ε := by
      have h1 : ‖x - A ω d‖ ≤ ‖x - A ω y‖ + ‖A ω y - A ω d‖ := by
        have : x - A ω d = (x - A ω y) + (A ω y - A ω d) := by abel
        rw [this]; exact norm_add_le _ _
      have h2 : ‖A ω y - A ω d‖ ≤ ‖A ω‖ * η := by
        rw [← map_sub]
        refine le_trans ((A ω).le_opNorm _) ?_
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        rw [← dist_eq_norm]
        exact hd.le
      have h3 : ‖A ω‖ * η ≤ ε := by
        have hle : η ≤ ε / (‖A ω‖ + 1) := min_le_left _ _
        have hpos : (0 : ℝ) < ‖A ω‖ + 1 := by positivity
        rw [le_div_iff₀ hpos] at hle
        nlinarith [norm_nonneg (A ω), hηpos.le]
      rw [dist_eq_norm]
      linarith
    linarith [hiInf, hstep]
  -- (B) the approximants close the gap
  have hMge : ∀ m ω, T ω - ‖A ω‖ / (m + 1) ≤ M m ω := by
    intro m ω
    rw [hMdef]
    refine le_ciInf fun d => ?_
    rw [hfdef]
    dsimp only
    split_ifs with hcond
    · obtain ⟨y, hyE, hy⟩ := (infDist_lt_iff (hEne ω)).1 hcond
      have hTy : T ω ≤ dist x (A ω y) :=
        infDist_le_dist_of_mem ⟨y, hyE, rfl⟩
      have h1 : dist x (A ω y) ≤ ‖x - A ω (d : X)‖ + ‖A ω‖ / (m + 1) := by
        have hsplit : x - A ω y = (x - A ω (d : X)) + (A ω (d : X) - A ω y) := by abel
        have h2 : ‖A ω (d : X) - A ω y‖ ≤ ‖A ω‖ / (m + 1) := by
          rw [← map_sub]
          refine le_trans ((A ω).le_opNorm _) ?_
          have hd2 : ‖(d : X) - y‖ ≤ 1 / (m + 1) := by
            rw [← dist_eq_norm]; exact hy.le
          have hmul := mul_le_mul_of_nonneg_left hd2 (norm_nonneg (A ω))
          calc ‖A ω‖ * ‖(d : X) - y‖ ≤ ‖A ω‖ * (1 / (m + 1)) := hmul
            _ = ‖A ω‖ / (m + 1) := by ring
        rw [dist_eq_norm, hsplit]
        exact le_trans (norm_add_le _ _) (by linarith)
      linarith
    · have : T ω ≤ ‖x‖ := hTx ω
      have hnn : (0 : ℝ) ≤ ‖A ω‖ / (m + 1) := by positivity
      linarith
  -- (C) the true value is the supremum of the approximants
  have hTeq : ∀ ω, T ω = ⨆ m : ℕ, M m ω := by
    intro ω
    have hbdd : BddAbove (Set.range fun m : ℕ => M m ω) := ⟨T ω, by
      rintro _ ⟨m, rfl⟩; exact hMle m ω⟩
    refine le_antisymm ?_ (ciSup_le fun m => hMle m ω)
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨m, hm⟩ := exists_nat_gt (‖A ω‖ / ε)
    have hmpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hlt : ‖A ω‖ / ((m : ℝ) + 1) < ε := by
      rw [div_lt_iff₀ hmpos]
      rw [div_lt_iff₀ hε] at hm
      nlinarith [hε.le]
    have := hMge m ω
    have hle : M m ω ≤ ⨆ m' : ℕ, M m' ω := le_ciSup hbdd m
    linarith
  have hMmeas : ∀ m, Measurable (M m) := by
    intro m
    refine Measurable.iInf fun d => ?_
    rw [hfdef]
    dsimp only
    have hval : Measurable fun ω => ‖x - A ω (d : X)‖ := by
      have h := (measurable_const (a := x)).dist (hA (d : X))
      simpa [dist_eq_norm] using h
    refine Measurable.ite ?_ hval measurable_const
    exact measurableSet_lt
      (((continuous_infDist_subspace k ((d : X))).measurable).comp hE) measurable_const
  have hfun : T = fun ω => ⨆ m : ℕ, M m ω := funext hTeq
  rw [hfun]
  exact Measurable.iSup hMmeas

end InfDistSubspace

/-- **A map into a separable metric space is measurable as soon as every distance function
`ω ↦ dist (F ω) y` is.** Balls around a countable dense set form a basis, so every open set is a
countable union of sets of the form `{ω | dist (F ω) d < r}`.

This is step 1 of the route recorded on `measurable_pushforward`: it reduces measurability of a
`𝒢_kX`-valued map to measurability of its Hausdorff distances to fixed subspaces. -/
theorem measurable_of_measurable_dist {Y Ω : Type*} [MetricSpace Y] [SeparableSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] [MeasurableSpace Ω] {F : Ω → Y}
    (h : ∀ y : Y, Measurable fun ω => dist (F ω) y) : Measurable F := by
  classical
  obtain ⟨D, hDcount, hDdense⟩ := TopologicalSpace.exists_countable_dense Y
  have : Countable D := hDcount.to_subtype
  refine measurable_of_isOpen fun s hs => ?_
  have hEq : F ⁻¹' s =
      ⋃ (p : D × ℚ) (_ : Metric.ball ((p.1 : Y)) ((p.2 : ℝ)) ⊆ s),
        {ω | dist (F ω) (p.1 : Y) < (p.2 : ℝ)} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · intro hω
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hs (F ω) hω
      obtain ⟨q, hq0, hqε⟩ := exists_rat_btwn (show (0 : ℝ) < ε / 3 by linarith)
      obtain ⟨d, hdD, hd⟩ :=
        Metric.mem_closure_iff.1 (hDdense (F ω)) (q : ℝ) (by exact_mod_cast hq0)
      refine ⟨(⟨d, hdD⟩, 2 * q), ?_, ?_⟩
      · intro z hz
        have hzd : dist z d < 2 * (q : ℝ) := by
          have := Metric.mem_ball.1 hz
          push_cast at this ⊢
          linarith
        refine hball ?_
        have hdF : dist d (F ω) < (q : ℝ) := by rwa [dist_comm] at hd
        have : dist z (F ω) < 3 * (q : ℝ) := by
          have := dist_triangle z d (F ω)
          linarith
        rw [Metric.mem_ball]
        linarith
      · have : dist (F ω) d < (q : ℝ) := hd
        push_cast
        have hq0' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
        linarith
    · rintro ⟨p, hsub, hlt⟩
      exact hsub (Metric.mem_ball.2 hlt)
  rw [hEq]
  refine MeasurableSet.iUnion fun p => ?_
  by_cases hp : Metric.ball ((p.1 : Y)) ((p.2 : ℝ)) ⊆ s
  · simp only [hp, Set.iUnion_true]
    exact measurableSet_lt (h (p.1 : Y)) measurable_const
  · simp [hp]

/-- A measurable operator family sends measurable subspaces to measurable images,
with arbitrary positive source and target dimensions. -/
theorem measurable_pushforward' {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [OpensMeasurableSpace X] [SeparableSpace X] [CompleteSpace X] (k l : ℕ)
    [NeZero k] [NeZero l] (E : Ω → GrassmannianFin X k) (hE : Measurable E)
    (A : Ω → X →L[ℝ] X) (hA : ∀ x : X, Measurable fun ω => A ω x)
    (F : Ω → GrassmannianFin X l)
    (hF : ∀ ω, (F ω).1 = Submodule.map ((A ω : X →ₗ[ℝ] X)) (E ω).1) :
    Measurable F := by
  refine measurable_of_measurable_infDist l fun x => ?_
  have himg : ∀ ω, (((F ω).1 : Submodule ℝ X) : Set X)
      = (A ω) '' (((E ω).1 : Submodule ℝ X) : Set X) := by
    intro ω
    rw [hF ω]
    ext z
    simp []
  simp_rw [himg]
  exact measurable_infDist_map k hE hA x

/-- **Lemma \ref{GXpush}.** The pointwise pushforward of a measurable family of subspaces along a
strongly measurable family of operators is measurable.

**Hypotheses corrected.** `[SeparableSpace X]`, `[CompleteSpace X]` and `[OpensMeasurableSpace X]`
were missing. The blueprint node says "a separable Banach space" and the paper's citation
(González-Tokman--Quas Cor. B.13) is under that standing assumption; without separability `𝒢_kX`
need not be separable and the appendix's `measdisaster` is the warning of what goes wrong.
Completeness is what makes `𝒢_kX` Polish, and `OpensMeasurableSpace` is what lets the *given*
σ-algebra on `X` see the norm, without which `hA` says nothing numerical.

`F` is taken as given, with `hF` identifying it: that `A(ω)E(ω)` is again `k`-dimensional is a
hypothesis, not something to prove, and it is what `A(ω)` being injective on `E(ω)` amounts to.

**No selection theorem is involved.** An earlier version of this comment claimed the statement
needs Kuratowski--Ryll-Nardzewski for Banach-space-valued multifunctions. It does not. The proof
is two steps.

1. `measurable_of_measurable_infDist` reduces measurability of `F` to measurability of
   `ω ↦ d(x, F ω)` for each fixed `x`: the maps `V ↦ d(x, V)` are `2‖x‖`-Lipschitz
   (`continuous_infDist_subspace`) and separate points, so they assemble into a continuous
   injection `𝒢_kX → ℝ^ℕ`, a measurable embedding by Lusin--Souslin since `𝒢_kX` is Polish.

   Testing against the *subspace* rather than its unit sphere is the whole trick. The sphere of
   `A(ω)E(ω)` is the image of `𝕊_{E ω}` under `y ↦ A(ω)y/‖A(ω)y‖`, whose normalisation
   degenerates as soon as one approximates `𝕊_{E ω}` from outside; distances to the subspace
   involve no normalisation at all.

2. `measurable_infDist_map` then computes `d(x, A(ω)E(ω)) = ⨅_{y ∈ E ω} ‖x - A(ω)y‖` as the
   *supremum* over `m` of the countable infima
   `⨅ {‖x - A(ω)xₙ‖ : d(xₙ, E ω) < 1/(m+1)}` along a dense `{xₙ}`. Those approximants are
   monotone in `m` and sandwich the true value within `‖A(ω)‖/(m+1)`, so the supremum is exact —
   no limit argument is needed. Each approximant evaluates `A ω` only at *fixed* points, so
   strong measurability of `A` suffices and no joint measurability in `(ω, y)` arises. -/
theorem measurable_pushforward {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [OpensMeasurableSpace X] [SeparableSpace X] [CompleteSpace X] (k : ℕ)
    [NeZero k] (E : Ω → GrassmannianFin X k) (hE : Measurable E)
    (A : Ω → X →L[ℝ] X) (hA : ∀ x : X, Measurable fun ω => A ω x)
    (F : Ω → GrassmannianFin X k)
    (hF : ∀ ω, (F ω).1 = Submodule.map ((A ω : X →ₗ[ℝ] X)) (E ω).1) :
    Measurable F :=
  measurable_pushforward' k k E hE A hA F hF

end MultiplicativeErgodic
