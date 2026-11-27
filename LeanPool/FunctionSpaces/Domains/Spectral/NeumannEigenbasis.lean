/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Spectral.DirichletEigenbasis
public import LeanPool.FunctionSpaces.Domains.Sobolev.LipschitzDomainW1p

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The Neumann Laplacian on bounded Lipschitz domains

Let `V` be a finite-dimensional real inner product space of dimension `n`, such as `ℝ^n`, with
Lebesgue measure and the orthonormal basis `b_k = Rd.gridBasis V k`, and `O ⊆ V` open. Inner
products are conjugate-linear in the first argument, as in Mathlib.

* **The Neumann space** `Rd.neumannSpace O` is `W^1_2(O)` as the graph of the weak gradient: the
  pairs `(f, g)` in `L_2(O) × L_2(O)^n` (`Rd.ValueGradientL2`) with `g_k = ∂_{b_k} f` weakly on
  `O`. It is closed (`Rd.isClosed_neumannSpace`), carries the inner product
  `⟨f, f'⟩_2 + ∑_k ⟨g_k, g'_k⟩_2` of the plain gradient (`Rd.inner_neumannSpace`), and its norm is
  equivalent to the norm of the jets of `W^1_2(O)` (`Rd.neumannSpace.toJet`,
  `Rd.neumannSpace.norm_toJet_le`, `Rd.neumannSpace.norm_le_norm_toJet`).
* **The Neumann embedding** `Rd.neumannEmbedding O : (f, g) ↦ f` is injective, has norm at most
  `1`, and has dense range, since its range contains that of the Dirichlet embedding
  (`Rd.range_dirichletEmbedding_le_range_neumannEmbedding`, through `Rd.restrictNeumann`).
* **Rellich's theorem**: on a bounded Lipschitz domain `Ω` in dimension `n ≥ 1`, every `(f, g)` in
  the Neumann space has `f = u|_Ω` for some `u ∈ H^1(Ω)` with `‖u‖ ≤ C ‖(f, g)‖`
  (`Rd.BoundedLipschitzDomain.exists_restrictionSpace_of_neumannSpace`), so the Neumann embedding
  is compact (`Rd.BoundedLipschitzDomain.isCompactOperator_neumannEmbedding`).
* **The Neumann eigenbasis**: `Rd.BoundedLipschitzDomain.neumannScheme` is the spectral scheme of
  this compact dense embedding, a Hilbert basis `(e_i)` of `L_2(Ω)` with levels `⌊√(1 + λ_i)⌋₊`,
  where `λ_i = σ_i⁻² - 1 ≥ 0` is the Neumann eigenvalue. The eigenfunction `φ_i` with value `e_i`
  satisfies `∑_k ⟨∂_k φ_i, g_k⟩_2 = λ_i ⟨φ_i, f⟩_2` for every `(f, g)` in the Neumann space
  (`Rd.BoundedLipschitzDomain.neumannEigenfunction_weak`), the weak form of `-Δ φ_i = λ_i φ_i` with
  `∂_ν φ_i = 0` on `∂Ω`; the constants give the eigenvalue `0`
  (`Rd.BoundedLipschitzDomain.exists_neumannEigenvalue_eq_zero`).
* **`W^1_2(Ω)` as a spectral Sobolev space**: `f ∈ L_2(Ω)` lies in `W^1_2(Ω)` iff
  `∑_i (1 + ⌊σ_i⁻¹⌋₊)² |⟨e_i, f⟩|² < ∞`
  (`Rd.BoundedLipschitzDomain.exists_neumannEmbedding_eq_iff`), and the real interpolation spaces
  `(L_2(Ω), W^1_2(Ω))_{θ,q}` are the approximation spaces of the Neumann scheme
  (`Rd.BoundedLipschitzDomain.memKMethod_neumann_iff`,
  `Rd.BoundedLipschitzDomain.memKMethod_neumann_iff_blockNorm_lt_top`).
-/

@[expose] public section

open MeasureTheory Filter Topology TopologicalSpace Module Metric
open scoped ENNReal Real InnerProductSpace BesselPotentialSpace

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### The graph space of the weak gradient -/

/-- **Values and gradients in `L_2(O)`**: the Hilbert space `L_2(O) × L_2(O)^n`, `n = dim V`, with
the inner product `⟨(f, g), (f', g')⟩ = ⟨f, f'⟩_2 + ∑_i ⟨g_i, g'_i⟩_2`; the pairs `(u, ∇u)` of
the Neumann space lie in it. -/
abbrev ValueGradientL2 (O : Opens V) : Type _ :=
  WithLp 2 (Lp ℂ 2 (volume.restrict (O : Set V)) ×
    PiLp 2 (fun _ : Fin (finrank ℝ V) => Lp ℂ 2 (volume.restrict (O : Set V))))

/-- **The Neumann space** `W^1_2(O)` as the graph of the weak gradient: the pairs `(f, g)` in
`L_2(O) × L_2(O)^n` with `g_k = ∂_{b_k} f` weakly on `O` for the basis `b_k = Rd.gridBasis V k`
(the carrier of `Rd.weakSobolevJet 2 O`), with the inner product
`⟨f, f'⟩_2 + ∑_k ⟨g_k, g'_k⟩_2` of the plain gradient. -/
noncomputable def neumannSpace (O : Opens V) : Submodule ℂ (ValueGradientL2 O) where
  carrier := {u | ∀ i, HasWeakLineDeriv O (fun _ : Fin 1 => gridBasis V i) u.fst (u.snd i)}
  zero_mem' := fun _ =>
    hasWeakLineDeriv_zero.congr_ae (Lp.coeFn_zero ..).symm (Lp.coeFn_zero ..).symm
  add_mem' := fun hu hv i =>
    ((hu i).add (hv i)).congr_ae (Lp.coeFn_add ..).symm (Lp.coeFn_add ..).symm
  smul_mem' := fun c _ hu i =>
    ((hu i).smul c).congr_ae (Lp.coeFn_smul ..).symm (Lp.coeFn_smul ..).symm

variable {O : Opens V}

/-- Membership in the Neumann space: `g_k = ∂_{b_k} f` weakly on `O` for every `k`. -/
theorem mem_neumannSpace {u : ValueGradientL2 O} :
    u ∈ neumannSpace O ↔
      ∀ i, HasWeakLineDeriv O (fun _ : Fin 1 => gridBasis V i) u.fst (u.snd i) :=
  Iff.rfl

variable (O) in
/-- **The Neumann space is closed**: weak derivatives pass to limits in `L_2(O)`
(`Rd.HasWeakLineDeriv.of_tendsto`). -/
theorem isClosed_neumannSpace : IsClosed (neumannSpace O : Set (ValueGradientL2 O)) := by
  refine IsSeqClosed.isClosed fun {u u₀} hu hlim i => ?_
  have h1 : Tendsto (fun n => (u n).fst) atTop (𝓝 u₀.fst) :=
    ((WithLp.fstL 2 ℂ _ _).continuous.tendsto u₀).comp hlim
  have h2 : Tendsto (fun n => (u n).snd i) atTop (𝓝 (u₀.snd i)) :=
    ((PiLp.continuous_apply 2 _ i).tendsto _).comp
      (((WithLp.sndL 2 ℂ _ _).continuous.tendsto u₀).comp hlim)
  exact HasWeakLineDeriv.of_tendsto one_le_two one_le_two (fun n => hu n i) (Lp.memLp _)
    (Lp.memLp _) ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).1 h1)
    ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).1 h2)

/-- The Neumann space is a Hilbert space, as a closed subspace (`Rd.isClosed_neumannSpace`). -/
instance completeSpace_neumannSpace : CompleteSpace (neumannSpace O) :=
  (isClosed_neumannSpace O).completeSpace_coe

/-- **The inner product of the Neumann space**: `⟨u, w⟩ = ⟨f, f'⟩_2 + ∑_i ⟨g_i, g'_i⟩_2` for
`u = (f, g)` and `w = (f', g')`. -/
theorem inner_neumannSpace (u w : neumannSpace O) :
    ⟪u, w⟫_ℂ = ⟪(u : ValueGradientL2 O).fst, (w : ValueGradientL2 O).fst⟫_ℂ +
      ∑ i, ⟪(u : ValueGradientL2 O).snd i, (w : ValueGradientL2 O).snd i⟫_ℂ := by
  rw [Submodule.coe_inner, WithLp.prod_inner_apply, PiLp.inner_apply]
  rfl

/-- **The norm of `L_2(O) × L_2(O)^n`**: `‖(f, g)‖² = ‖f‖_2² + ∑_i ‖g_i‖_2²`. -/
theorem ValueGradientL2.sq_norm_eq (u : ValueGradientL2 O) :
    ‖u‖ ^ 2 = ‖u.fst‖ ^ 2 + ∑ i, ‖u.snd i‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]

/-- `‖(f, g)‖ ≤ ‖f‖_2 + ∑_i ‖g_i‖_2` in `L_2(O) × L_2(O)^n`, from
`Rd.ValueGradientL2.sq_norm_eq`. -/
theorem ValueGradientL2.norm_le_norm_fst_add_sum (u : ValueGradientL2 O) :
    ‖u‖ ≤ ‖u.fst‖ + ∑ i, ‖u.snd i‖ := by
  have hs := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
    fun i _ => norm_nonneg (u.snd i)
  have h0 : 0 ≤ ∑ i, ‖u.snd i‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [ValueGradientL2.sq_norm_eq]
  nlinarith [norm_nonneg u.fst]

/-- `‖f‖_2 + ∑_i ‖g_i‖_2 ≤ (n + 1) ‖(f, g)‖` in `L_2(O) × L_2(O)^n`, `n = dim V`, since each
coordinate has norm at most `‖(f, g)‖` (Mathlib's `WithLp.norm_fst_le`, `WithLp.norm_snd_le`,
`PiLp.norm_apply_le`). -/
theorem ValueGradientL2.norm_fst_add_sum_le (u : ValueGradientL2 O) :
    ‖u.fst‖ + ∑ i, ‖u.snd i‖ ≤ (finrank ℝ V + 1) * ‖u‖ := by
  have h : ∑ i, ‖u.snd i‖ ≤ ∑ _i : Fin (finrank ℝ V), ‖u‖ :=
    Finset.sum_le_sum fun i _ => (PiLp.norm_apply_le _ i).trans (WithLp.norm_snd_le _ u)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  linarith [WithLp.norm_fst_le _ u]

/-! ### The Neumann space and the jets of `W^1_2(O)` -/

/-- **The sup norm is at most the Hilbert norm**: `max(‖f‖_2, max_k ‖g_k‖_2) ≤ ‖(f, g)‖` for
`(f, g)` in `L_2(O) × L_2(O)^n`, since each coordinate has norm at most `‖(f, g)‖` (Mathlib's
`norm_prod_le_iff`, `pi_norm_le_iff_of_nonneg`, `WithLp.norm_fst_le`, `WithLp.norm_snd_le`,
`PiLp.norm_apply_le`). -/
theorem ValueGradientL2.norm_pair_le (u : ValueGradientL2 O) :
    ‖((u.fst, fun k => u.snd k) : Lp ℂ 2 (volume.restrict (O : Set V)) ×
      (Fin (finrank ℝ V) → Lp ℂ 2 (volume.restrict (O : Set V))))‖ ≤ ‖u‖ :=
  norm_prod_le_iff.2 ⟨WithLp.norm_fst_le _ u, (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
    fun k => (PiLp.norm_apply_le _ k).trans (WithLp.norm_snd_le _ u)⟩

variable (O) in
/-- **The Neumann space as jets**: `(f, g) ↦ (f, (g_k)_k)` from the Neumann space to the jets of
`W^1_2(O)` (`Rd.weakSobolevJet 2 O`, with the sup norm), a bounded linear operator of norm at most
`1` (`Rd.ValueGradientL2.norm_pair_le`). -/
noncomputable def neumannSpace.toJet : neumannSpace O →L[ℂ] weakSobolevJet 2 O :=
  LinearMap.mkContinuous
    { toFun := fun u => ⟨((u : ValueGradientL2 O).fst, fun k => (u : ValueGradientL2 O).snd k),
        u.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 fun u => by
      rw [one_mul]
      exact ValueGradientL2.norm_pair_le (u : ValueGradientL2 O)

/-- The value of `toJet u` is the value of `u`. -/
@[simp]
theorem neumannSpace.toJet_fst (u : neumannSpace O) :
    (neumannSpace.toJet O u).1.1 = (u : ValueGradientL2 O).fst :=
  rfl

/-- The derivatives of `toJet u` are those of `u`. -/
@[simp]
theorem neumannSpace.toJet_snd (u : neumannSpace O) (i : Fin (finrank ℝ V)) :
    (neumannSpace.toJet O u).1.2 i = (u : ValueGradientL2 O).snd i :=
  rfl

/-- **The jet norm is at most the norm of the Neumann space**: `‖toJet u‖ ≤ ‖u‖`
(`Rd.ValueGradientL2.norm_pair_le`). -/
theorem neumannSpace.norm_toJet_le (u : neumannSpace O) : ‖neumannSpace.toJet O u‖ ≤ ‖u‖ :=
  ValueGradientL2.norm_pair_le (u : ValueGradientL2 O)

/-- **The two norms are equivalent**: `‖u‖ ≤ (n + 1) ‖toJet u‖`, the converse of
`Rd.neumannSpace.norm_toJet_le` (`Rd.ValueGradientL2.norm_le_norm_fst_add_sum`,
`Rd.norm_fst_add_sum_le`). -/
theorem neumannSpace.norm_le_norm_toJet (u : neumannSpace O) :
    ‖u‖ ≤ (finrank ℝ V + 1) * ‖neumannSpace.toJet O u‖ := by
  have h := norm_fst_add_sum_le (neumannSpace.toJet O u).1
  rw [Fintype.card_fin] at h
  exact (ValueGradientL2.norm_le_norm_fst_add_sum (u : ValueGradientL2 O)).trans h

/-! ### The Neumann embedding -/

variable (O) in
/-- **The Neumann embedding** `(f, g) ↦ f` from the Neumann space to `L_2(O)`. -/
noncomputable def neumannEmbedding : neumannSpace O →L[ℂ] Lp ℂ 2 (volume.restrict (O : Set V)) :=
  WithLp.fstL 2 ℂ _ _ ∘L (neumannSpace O).subtypeL

/-- `neumannEmbedding O u` is the value `f` of `u = (f, g)`. -/
theorem neumannEmbedding_apply (u : neumannSpace O) :
    neumannEmbedding O u = (u : ValueGradientL2 O).fst :=
  rfl

/-- The Neumann embedding has norm at most `1`. -/
theorem norm_neumannEmbedding_le : ‖neumannEmbedding O‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => by
    rw [one_mul]
    exact WithLp.norm_fst_le _ (u : ValueGradientL2 O)

/-- **The Neumann embedding is injective**: the weak derivatives of `f` are determined by `f`
(`Rd.HasWeakLineDeriv.unique`). -/
theorem neumannEmbedding_injective : Function.Injective (neumannEmbedding O) := by
  intro u w h
  have hs : ∀ i, (u : ValueGradientL2 O).snd i = (w : ValueGradientL2 O).snd i := fun i => by
    have hw := w.2 i
    rw [← (show (u : ValueGradientL2 O).fst = (w : ValueGradientL2 O).fst from h)] at hw
    exact Lp.ext ((u.2 i).unique hw)
  exact Subtype.ext (WithLp.ofLp_injective 2 (Prod.ext h (WithLp.ofLp_injective 2 (funext hs))))

variable (O) in
/-- **`H^1(V)` in `L_2(O) × L_2(O)^n`**: `U ↦ (ι U|_O, ((∂_{b_k} ι U)|_O)_k)`, a bounded linear
operator. -/
noncomputable def toValueGradientL2 : H^{1}(V) →L[ℂ] ValueGradientL2 O :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).symm.toContinuousLinearMap ∘L
    ((LpToLpRestrictCLM V ℂ ℂ volume 2 (O : Set V) ∘L toL2).prod
      ((PiLp.continuousLinearEquiv 2 ℂ _).symm.toContinuousLinearMap ∘L
        ContinuousLinearMap.pi fun i =>
          LpToLpRestrictCLM V ℂ ℂ volume 2 (O : Set V) ∘L weakDerivL2 (gridBasis V i)))

/-- The pair `(ι U|_O, ((∂_{b_k} ι U)|_O)_k)` lies in the Neumann space, since weak derivatives on
`V` restrict to `O` (`Rd.HasWeakLineDeriv.mono`). -/
theorem toValueGradientL2_mem (U : H^{1}(V)) : toValueGradientL2 O U ∈ neumannSpace O := fun i =>
  ((hasWeakLineDeriv_weakDerivL2 (gridBasis V i) U).mono le_top).congr_ae
    (LpToLpRestrictCLM_coeFn ℂ (O : Set V) _).symm (LpToLpRestrictCLM_coeFn ℂ (O : Set V) _).symm

variable (O) in
/-- **`H^1(V)` in the Neumann space**: `U ↦ (ι U|_O, ((∂_{b_k} ι U)|_O)_k)`. -/
noncomputable def restrictNeumann : H^{1}(V) →L[ℂ] neumannSpace O :=
  (toValueGradientL2 O).codRestrict (neumannSpace O) toValueGradientL2_mem

/-- The value of `restrictNeumann O U` is the restriction to `O` of `ι U`. -/
theorem neumannEmbedding_restrictNeumann (U : H^{1}(V)) :
    neumannEmbedding O (restrictNeumann O U) =
      LpToLpRestrictCLM V ℂ ℂ volume 2 (O : Set V) (toL2 U) :=
  rfl

/-- **`H^1_0(O)` lies in the Neumann space**: every value `J u` of the Dirichlet embedding is a
value of the Neumann embedding, namely of `Rd.restrictNeumann O u`. -/
theorem range_dirichletEmbedding_le_range_neumannEmbedding :
    LinearMap.range (dirichletEmbedding O :
        zeroBoundarySpace 1 O →ₗ[ℂ] Lp ℂ 2 (volume.restrict (O : Set V))) ≤
      LinearMap.range (neumannEmbedding O :
        neumannSpace O →ₗ[ℂ] Lp ℂ 2 (volume.restrict (O : Set V))) := by
  rintro _ ⟨u, rfl⟩
  exact ⟨restrictNeumann O ((u : RestrictionSpace 1 O) : H^{1}(V)), rfl⟩

/-- **The range of the Neumann embedding is dense**: its orthogonal complement lies in that of the
range of the Dirichlet embedding (`Rd.range_dirichletEmbedding_le_range_neumannEmbedding`), which
is trivial (`Rd.orthogonal_range_dirichletEmbedding`). -/
theorem orthogonal_range_neumannEmbedding :
    (LinearMap.range (neumannEmbedding O :
      neumannSpace O →ₗ[ℂ] Lp ℂ 2 (volume.restrict (O : Set V))))ᗮ = ⊥ :=
  eq_bot_iff.2 ((Submodule.orthogonal_le range_dirichletEmbedding_le_range_neumannEmbedding).trans
    orthogonal_range_dirichletEmbedding.le)

/-- The Neumann embedding has dense range (`Rd.orthogonal_range_neumannEmbedding`). -/
theorem denseRange_neumannEmbedding : DenseRange (neumannEmbedding O) := by
  have h := Submodule.topologicalClosure_eq_top_iff.2
    (orthogonal_range_neumannEmbedding (O := O))
  rw [← Submodule.dense_iff_topologicalClosure_eq_top, LinearMap.coe_range] at h
  exact h

/-! ### The constant functions -/

namespace BoundedLipschitzDomain

variable (Ω : BoundedLipschitzDomain V)

/-- **The constant function `1` in the Neumann space**: the pair `(1, 0)`, since the weak
gradient of a constant vanishes (`Rd.hasWeakLineDeriv_const`); `1 ∈ L_2(Ω)` as `Ω` has finite
measure (`Rd.BoundedLipschitzDomain.isFiniteMeasure_volume_restrict`). -/
noncomputable def constNeumann : neumannSpace Ω.toOpens :=
  ⟨WithLp.toLp 2 (Lp.const 2 (volume.restrict (Ω.toOpens : Set V)) (1 : ℂ), 0), fun i =>
    (hasWeakLineDeriv_const Ω.toOpens (gridBasis V i) 1).congr_ae
      (Lp.coeFn_const ..).symm (Lp.coeFn_zero ..).symm⟩

/-- **The constant `1` has no gradient term**: `⟨(1, 0), w⟩ = ⟨1, f⟩_{L_2(Ω)}` for every
`w = (f, g)` in the Neumann space, the weak eigenvalue equation `⟨u, w⟩ = σ⁻² ⟨J u, J w⟩` with
`σ = 1`. -/
theorem inner_constNeumann (w : neumannSpace Ω.toOpens) :
    ⟪Ω.constNeumann, w⟫_ℂ =
      ⟪neumannEmbedding Ω.toOpens Ω.constNeumann, neumannEmbedding Ω.toOpens w⟫_ℂ := by
  have h0 : ∀ i, (Ω.constNeumann : ValueGradientL2 Ω.toOpens).snd i = 0 := fun _ => rfl
  rw [inner_neumannSpace]
  simp only [h0, inner_zero_left, Finset.sum_const_zero, add_zero]
  rfl

/-- **The constant `1` is a nonzero element of `L_2(Ω)`** for a nonempty bounded Lipschitz domain
`Ω`, as `Ω` has positive measure. -/
theorem neumannEmbedding_constNeumann_ne_zero (hΩ : Ω.carrier.Nonempty) :
    neumannEmbedding Ω.toOpens Ω.constNeumann ≠ 0 := by
  intro h
  have hμ : volume.restrict (Ω.toOpens : Set V) ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero]
    exact (Ω.isOpen.measure_pos volume hΩ).ne'
  have : (ae (volume.restrict (Ω.toOpens : Set V))).NeBot := ae_neBot.2 hμ
  have hc := Lp.coeFn_const 2 (volume.restrict (Ω.toOpens : Set V)) (1 : ℂ)
  have h0 : Lp.const 2 (volume.restrict (Ω.toOpens : Set V)) (1 : ℂ) = 0 := h
  rw [h0] at hc
  obtain ⟨x, hx1, hx2⟩ :=
    (hc.and (Lp.coeFn_zero ℂ 2 (volume.restrict (Ω.toOpens : Set V)))).exists
  exact one_ne_zero (hx1.symm.trans hx2)

/-! ### Rellich's theorem for the Neumann space -/

variable [Nontrivial V]

/-- **Every value of the Neumann space comes from `H^1(Ω)`**: for a bounded Lipschitz domain `Ω`
in dimension `n ≥ 1` and every `u = (f, g)` in the Neumann space, `f = u_R|_Ω` for some
`u_R ∈ H^1(Ω)`. The extension operator maps the jet of `u` to a jet `(F, G)` of `W^1_2(V)` with
`F = f` on `Ω` (`Rd.BoundedLipschitzDomain.memSobolev_sobolevExtensionL`,
`Rd.BoundedLipschitzDomain.sobolevExtensionL_fst_ae_eq`), and `u_R = F|_Ω`. -/
theorem exists_restrictL2_eq_neumannEmbedding (u : neumannSpace Ω.toOpens) :
    ∃ uR : RestrictionSpace 1 Ω.toOpens,
      restrictL2 Ω.toOpens uR = neumannEmbedding Ω.toOpens u := by
  have hF := Ω.memSobolev_sobolevExtensionL (neumannSpace.toJet Ω.toOpens u)
  have hFf := Ω.sobolevExtensionL_fst_ae_eq (neumannSpace.toJet Ω.toOpens u)
  set F := (Ω.sobolevExtensionL 2 (neumannSpace.toJet Ω.toOpens u)).1.1
  have hS := (memSobolev_one_iff F).1 hF
  have hU : toL2 hS.toBesselPotentialSpace = F :=
    toL2_eq_of_toDistr_eq _ hS.toBesselPotentialSpace_toDistr.symm
  refine ⟨restrictProj 1 Ω.toOpens hS.toBesselPotentialSpace, ?_⟩
  rw [restrictL2_restrictProj, hU]
  exact Lp.ext ((LpToLpRestrictCLM_coeFn ℂ _ _).trans hFf)

/-- **The Neumann space inside `H^1(Ω)`, with a bound**: for a bounded Lipschitz domain `Ω` in
dimension `n ≥ 1` there is a constant `C ≥ 0` such that every `u = (f, g)` in the Neumann space
has some `u_R ∈ H^1(Ω)` with `u_R|_Ω = f` and `‖u_R‖ ≤ C ‖u‖`
(`Rd.BoundedLipschitzDomain.exists_restrictL2_eq_neumannEmbedding`, and the bound of the quotient
norm of `H^1(Ω)` by the `W^1_2(Ω)` norm, `Rd.BoundedLipschitzDomain.exists_norm_le_restrictL2`).
As an element of `H^1(V)`, `u_R` is an extension of `f` to `V`. -/
theorem exists_restrictionSpace_of_neumannSpace :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : neumannSpace Ω.toOpens, ∃ uR : RestrictionSpace 1 Ω.toOpens,
      restrictL2 Ω.toOpens uR = neumannEmbedding Ω.toOpens u ∧ ‖uR‖ ≤ C * ‖u‖ := by
  obtain ⟨C, hC⟩ := Ω.exists_norm_le_restrictL2
  refine ⟨max C 0 * (finrank ℝ V + 1), by positivity, fun u => ?_⟩
  obtain ⟨uR, huR⟩ := Ω.exists_restrictL2_eq_neumannEmbedding u
  refine ⟨uR, huR, ?_⟩
  have hae : (toL2 (uR : H^{1}(V)) : V → ℂ) =ᵐ[volume.restrict (Ω.toOpens : Set V)]
      neumannEmbedding Ω.toOpens u := by
    rw [← huR, restrictL2_apply]
    exact (LpToLpRestrictCLM_coeFn ℂ _ _).symm
  have h := hC uR (fun i => (u : ValueGradientL2 Ω.toOpens).snd i)
    fun i => (u.2 i).congr_ae hae.symm EventuallyEq.rfl
  rw [huR, neumannEmbedding_apply] at h
  have h2 := ValueGradientL2.norm_fst_add_sum_le (u : ValueGradientL2 Ω.toOpens)
  have h0 : 0 ≤ ‖(u : ValueGradientL2 Ω.toOpens).fst‖ +
      ∑ i, ‖(u : ValueGradientL2 Ω.toOpens).snd i‖ := by positivity
  calc ‖uR‖ ≤ C * (‖(u : ValueGradientL2 Ω.toOpens).fst‖ +
        ∑ i, ‖(u : ValueGradientL2 Ω.toOpens).snd i‖) := h
    _ ≤ max C 0 * (‖(u : ValueGradientL2 Ω.toOpens).fst‖ +
        ∑ i, ‖(u : ValueGradientL2 Ω.toOpens).snd i‖) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) h0
    _ ≤ max C 0 * ((finrank ℝ V + 1) * ‖u‖) := mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
    _ = max C 0 * (finrank ℝ V + 1) * ‖u‖ := by ring

/-- **Rellich's theorem for the Neumann space**: for a bounded Lipschitz domain `Ω` in dimension
`n ≥ 1`, the Neumann embedding `W^1_2(Ω) → L_2(Ω)` is compact. The image of the unit ball lies in
the image of a ball of `H^1(Ω)` under `u ↦ u|_Ω`
(`Rd.BoundedLipschitzDomain.exists_restrictionSpace_of_neumannSpace`), which has compact closure
(`Rd.isCompactOperator_restrictL2`). -/
theorem isCompactOperator_neumannEmbedding : IsCompactOperator (neumannEmbedding Ω.toOpens) := by
  obtain ⟨C, hC, h⟩ := Ω.exists_restrictionSpace_of_neumannSpace
  refine (isCompactOperator_iff_isCompact_closure_image_closedBall
    (neumannEmbedding Ω.toOpens).toLinearMap zero_lt_one).2 ?_
  refine ((isCompactOperator_restrictL2 Ω.isBounded).isCompact_closure_image_closedBall
    C).of_isClosed_subset isClosed_closure (closure_mono ?_)
  rintro _ ⟨u, hu, rfl⟩
  obtain ⟨uR, h1, h2⟩ := h u
  refine ⟨uR, mem_closedBall_zero_iff.2 (h2.trans ?_), h1⟩
  exact mul_le_of_le_one_right hC (mem_closedBall_zero_iff.1 hu)

/-! ### The Neumann eigenbasis -/

/-- **`W^1_2(Ω) ↪ L_2(Ω)` as a compact dense embedding**, for every bounded Lipschitz domain `Ω` in
dimension `n ≥ 1` (`Rd.BoundedLipschitzDomain.isCompactOperator_neumannEmbedding`,
`Rd.neumannEmbedding_injective`, `Rd.denseRange_neumannEmbedding`). -/
noncomputable def neumannCompactEmbedding :
    @CompactDenseEmbedding (neumannSpace Ω.toOpens)
      (Lp ℂ 2 (volume.restrict (Ω.toOpens : Set V)))
      (Submodule.normedAddCommGroup (neumannSpace Ω.toOpens))
      (Submodule.innerProductSpace (neumannSpace Ω.toOpens)) inferInstance inferInstance where
  toCLM := neumannEmbedding Ω.toOpens
  isCompact := Ω.isCompactOperator_neumannEmbedding
  injective := neumannEmbedding_injective
  denseRange := denseRange_neumannEmbedding

/-- The embedding of `Rd.BoundedLipschitzDomain.neumannCompactEmbedding` is the Neumann
embedding. -/
@[simp]
theorem neumannCompactEmbedding_toCLM :
    Ω.neumannCompactEmbedding.toCLM = neumannEmbedding Ω.toOpens :=
  rfl

/-- **The Neumann eigenbasis as a spectral scheme**: for a bounded Lipschitz domain `Ω` in
dimension `n ≥ 1`, the Hilbert basis `(e_i)` of `L_2(Ω)` of eigenvectors of `J J†`, `J` the Neumann
embedding, with the levels `⌊σ_i⁻¹⌋₊` of the singular values
(`CompactDenseEmbedding.spectralScheme`). With the plain gradient in the inner product of the
Neumann space, `σ_i⁻² = 1 + λ_i` for the Neumann eigenvalue `λ_i`
(`Rd.BoundedLipschitzDomain.one_add_neumannEigenvalue`), so the level is `⌊√(1 + λ_i)⌋₊`
(`Rd.BoundedLipschitzDomain.neumannScheme_level`). -/
noncomputable def neumannScheme :
    SpectralScheme Ω.neumannCompactEmbedding.index
      (Lp ℂ 2 (volume.restrict (Ω.toOpens : Set V))) :=
  Ω.neumannCompactEmbedding.spectralScheme

/-- The singular values of the Neumann embedding are at most `1`
(`Rd.norm_neumannEmbedding_le`). -/
theorem singularValue_neumannCompactEmbedding_le_one (i : Ω.neumannCompactEmbedding.index) :
    Ω.neumannCompactEmbedding.singularValue i ≤ 1 :=
  (Ω.neumannCompactEmbedding.singularValue_le_norm i).trans norm_neumannEmbedding_le

/-- **The Neumann eigenvalue** `λ_i = σ_i⁻² - 1` of the index `i`, `σ_i` the singular value of the
Neumann embedding; `-Δ φ_i = λ_i φ_i` weakly with the natural boundary condition
(`Rd.BoundedLipschitzDomain.neumannEigenfunction_weak`). -/
noncomputable def neumannEigenvalue (i : Ω.neumannCompactEmbedding.index) : ℝ :=
  (Ω.neumannCompactEmbedding.singularValue i)⁻¹ ^ 2 - 1

/-- The Neumann eigenvalues are nonnegative, since `σ_i ≤ 1`
(`Rd.BoundedLipschitzDomain.singularValue_neumannCompactEmbedding_le_one`). -/
theorem neumannEigenvalue_nonneg (i : Ω.neumannCompactEmbedding.index) :
    0 ≤ Ω.neumannEigenvalue i := by
  have h1 : 1 ≤ (Ω.neumannCompactEmbedding.singularValue i)⁻¹ :=
    one_le_inv_iff₀.2 ⟨Ω.neumannCompactEmbedding.singularValue_pos i,
      Ω.singularValue_neumannCompactEmbedding_le_one i⟩
  have h2 : 1 ≤ (Ω.neumannCompactEmbedding.singularValue i)⁻¹ ^ 2 := one_le_pow₀ h1
  unfold neumannEigenvalue
  linarith

/-- `1 + λ_i = σ_i⁻²`. -/
theorem one_add_neumannEigenvalue (i : Ω.neumannCompactEmbedding.index) :
    1 + Ω.neumannEigenvalue i = (Ω.neumannCompactEmbedding.singularValue i)⁻¹ ^ 2 := by
  unfold neumannEigenvalue
  ring

/-- **The level of a Neumann eigenfunction** is `⌊√(1 + λ_i)⌋₊`. -/
theorem neumannScheme_level (i : Ω.neumannCompactEmbedding.index) :
    Ω.neumannScheme.level i = ⌊Real.sqrt (1 + Ω.neumannEigenvalue i)⌋₊ := by
  rw [one_add_neumannEigenvalue, Real.sqrt_sq
    (inv_nonneg.2 (Ω.neumannCompactEmbedding.singularValue_pos i).le)]
  rfl

/-- **The Neumann eigenfunction** `φ_i = σ_i⁻¹ v_i` in the Neumann space, `v_i` the singular basis
of the Neumann embedding; its value is the basis vector `e_i` of `L_2(Ω)`
(`Rd.BoundedLipschitzDomain.neumannEmbedding_neumannEigenfunction`). -/
noncomputable def neumannEigenfunction (i : Ω.neumannCompactEmbedding.index) :
    neumannSpace Ω.toOpens :=
  (((Ω.neumannCompactEmbedding.singularValue i)⁻¹ : ℝ) : ℂ) •
    Ω.neumannCompactEmbedding.singularBasis i

/-- **`φ_i = e_i` on `Ω`**: the Neumann embedding maps the eigenfunction `φ_i` to the basis vector
`e_i` of the Neumann scheme, since `J v_i = σ_i e_i` (`CompactDenseEmbedding.apply_singularBasis`).
-/
theorem neumannEmbedding_neumannEigenfunction (i : Ω.neumannCompactEmbedding.index) :
    neumannEmbedding Ω.toOpens (Ω.neumannEigenfunction i) = Ω.neumannScheme.basis i := by
  have h := Ω.neumannCompactEmbedding.apply_singularBasis i
  rw [neumannCompactEmbedding_toCLM] at h
  rw [neumannEigenfunction, map_smul, h, smul_smul, ← Complex.ofReal_mul,
    inv_mul_cancel₀ (Ω.neumannCompactEmbedding.singularValue_pos i).ne', Complex.ofReal_one,
    one_smul]
  rfl

/-! ### The weak Neumann eigenvalue equation -/

/-- **The weak Neumann eigenvalue equation**: for a bounded Lipschitz domain `Ω` in dimension
`n ≥ 1`, every index `i` and every `w = (f, g)` in the Neumann space, the eigenfunction
`φ_i = (φ_i, ∇φ_i)` satisfies `∑_k ⟨∂_k φ_i, g_k⟩_{L_2(Ω)} = λ_i ⟨φ_i, f⟩_{L_2(Ω)}`, the weak
form of `-Δ φ_i = λ_i φ_i` in `Ω` with `∂_ν φ_i = 0` on `∂Ω`. It is the weak eigenvalue equation
`⟨v_i, w⟩ = σ_i⁻² ⟨J v_i, J w⟩` of the singular basis
(`CompactDenseEmbedding.inner_singularBasis`) with the inner product of the Neumann space
(`Rd.inner_neumannSpace`). -/
theorem neumannEigenfunction_weak (i : Ω.neumannCompactEmbedding.index)
    (w : neumannSpace Ω.toOpens) :
    ∑ k, ⟪(Ω.neumannEigenfunction i : ValueGradientL2 Ω.toOpens).snd k,
        (w : ValueGradientL2 Ω.toOpens).snd k⟫_ℂ =
      (Ω.neumannEigenvalue i : ℂ) *
        ⟪(Ω.neumannEigenfunction i : ValueGradientL2 Ω.toOpens).fst,
          (w : ValueGradientL2 Ω.toOpens).fst⟫_ℂ := by
  have hφ : ⟪Ω.neumannEigenfunction i, w⟫_ℂ =
      (((Ω.neumannCompactEmbedding.singularValue i)⁻¹ ^ 2 : ℝ) : ℂ) *
        ⟪neumannEmbedding Ω.toOpens (Ω.neumannEigenfunction i),
          neumannEmbedding Ω.toOpens w⟫_ℂ := by
    -- the scalar multiplication of the subspace matches `inner_smul_left` up to unfolding
    -- instances, so the lemma is applied by unification instead of rewriting
    refine (inner_smul_left (𝕜 := ℂ) (E := neumannSpace Ω.toOpens)
      (Ω.neumannCompactEmbedding.singularBasis i) w _).trans ?_
    rw [neumannEigenfunction, map_smul, inner_smul_left,
      Ω.neumannCompactEmbedding.inner_singularBasis i w, neumannCompactEmbedding_toCLM]
    ring
  rw [inner_neumannSpace, neumannEmbedding_apply, neumannEmbedding_apply] at hφ
  unfold neumannEigenvalue
  push_cast at hφ ⊢
  linear_combination hφ

/-! ### The eigenvalue `0` -/

/-- **`0` is a Neumann eigenvalue**: for a nonempty bounded Lipschitz domain `Ω` in dimension
`n ≥ 1`, some index `i` has `λ_i = 0`. The constant function `1` satisfies
`⟨(1, 0), w⟩ = ⟨1, J w⟩_{L_2(Ω)}` (`Rd.BoundedLipschitzDomain.inner_constNeumann`), so some
singular value is `1` (`CompactDenseEmbedding.exists_singularValue_eq_one`). -/
theorem exists_neumannEigenvalue_eq_zero (hΩ : Ω.carrier.Nonempty) :
    ∃ i, Ω.neumannEigenvalue i = 0 := by
  have hc0 : Ω.constNeumann ≠ 0 := fun h =>
    Ω.neumannEmbedding_constNeumann_ne_zero hΩ (by rw [h, map_zero])
  obtain ⟨i, hi⟩ := Ω.neumannCompactEmbedding.exists_singularValue_eq_one hc0 Ω.inner_constNeumann
  exact ⟨i, by rw [neumannEigenvalue, hi]; norm_num⟩

/-! ### The Neumann space as a spectral Sobolev space -/

/-- **The Neumann space in the Neumann eigenbasis**: `f ∈ L_2(Ω)` is the value of some `w` in the
Neumann space, that is `f ∈ W^1_2(Ω)`, iff `∑_i (1 + ⌊σ_i⁻¹⌋₊)² |⟨e_i, f⟩|² < ∞`, the Sobolev
space of order `1` of the Neumann scheme (`CompactDenseEmbedding.range_eq_range_sobolevEmbed`,
`SpectralScheme.mem_range_sobolevEmbed_iff`). -/
theorem exists_neumannEmbedding_eq_iff (f : Lp ℂ 2 (volume.restrict (Ω.toOpens : Set V))) :
    (∃ w, neumannEmbedding Ω.toOpens w = f) ↔
      Memℓp (fun i => ((1 + Ω.neumannScheme.level i : ℕ) : ℂ) *
        Ω.neumannScheme.basis.repr f i) 2 := by
  -- unfolding the scheme first keeps the definitional unfolding in the rewrites cheap
  unfold neumannScheme
  have hw : ∀ i, ((Ω.neumannCompactEmbedding.spectralScheme.weight 1 i : ℝ) : ℂ) =
      ((1 + Ω.neumannCompactEmbedding.spectralScheme.level i : ℕ) : ℂ) := fun i => by
    simp [SpectralScheme.weight]
  refine ((Set.ext_iff.1 Ω.neumannCompactEmbedding.range_eq_range_sobolevEmbed f).trans
    (Ω.neumannCompactEmbedding.spectralScheme.mem_range_sobolevEmbed_iff 1 zero_le_one f)).trans
      ?_
  simp only [hw]

/-- **The interpolation spaces between `L_2(Ω)` and `W^1_2(Ω)`**: for a bounded Lipschitz domain
`Ω` in dimension `n ≥ 1`, `0 < θ < 1` and `1 ≤ q ≤ ∞`, `(L_2(Ω), W^1_2(Ω))_{θ,q}` is the
approximation space `A^θ_q` of the Neumann scheme
(`CompactDenseEmbedding.memKMethod_iff_memApprox`). -/
theorem memKMethod_neumann_iff {θ : ℝ} {q : ℝ≥0∞} (hθ : 0 < θ) (hθ' : θ < 1) (hq : 1 ≤ q)
    {f : Lp ℂ 2 (volume.restrict (Ω.toOpens : Set V))} :
    (InterpCouple.ofMap ((neumannEmbedding Ω.toOpens).restrictScalars ℝ)).MemKMethod θ q f ↔
      Ω.neumannScheme.toScheme.MemApprox θ q f :=
  Ω.neumannCompactEmbedding.memKMethod_iff_memApprox hθ hθ' hq

/-- **The interpolation spaces between `L_2(Ω)` and `W^1_2(Ω)` by dyadic blocks**: for a bounded
Lipschitz domain `Ω` in dimension `n ≥ 1`, `0 < θ < 1` and `1 ≤ q ≤ ∞`,
`f ∈ (L_2(Ω), W^1_2(Ω))_{θ,q}` iff the dyadic blocks of the expansion of `f` in the Neumann
eigenbasis have finite `B^θ_{2,q}` norm (`Rd.BoundedLipschitzDomain.memKMethod_neumann_iff`,
`SpectralScheme.memApprox_iff_blockNorm_lt_top`). -/
theorem memKMethod_neumann_iff_blockNorm_lt_top {θ : ℝ} {q : ℝ≥0∞} (hθ : 0 < θ) (hθ' : θ < 1)
    (hq : 1 ≤ q) {f : Lp ℂ 2 (volume.restrict (Ω.toOpens : Set V))} :
    (InterpCouple.ofMap ((neumannEmbedding Ω.toOpens).restrictScalars ℝ)).MemKMethod θ q f ↔
      Ω.neumannScheme.projectionScheme.blockNorm θ q f < ∞ := by
  rw [Ω.memKMethod_neumann_iff hθ hθ' hq, Ω.neumannScheme.memApprox_iff_blockNorm_lt_top hθ hq]

end BoundedLipschitzDomain

end Rd
