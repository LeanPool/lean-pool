/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Spectrum.Spectrum
public import LeanPool.EllipticPDE.Analysis.FrechetKolmogorov
public import LeanPool.EllipticPDE.Analysis.LpExtendByZero
public import LeanPool.EllipticPDE.Analysis.EuclideanFunctionalNorm


/-!
# Discharging the Rellich-Kondrachov compact embedding

`Compactness.lean` reduces the Fredholm theory to the single analytic hypothesis
`IsCompactOperator (embL2 Ω)`, the Rellich-Kondrachov compact embedding `H₀¹(Ω) ↪ L²(Ω)`. This
file proves it for bounded measurable `Ω`, consuming the Fréchet-Kolmogorov engine built in
`EllipticPdes.Analysis.*`.

The argument sends `embL2 Ω U = U 0 ∈ L²(Ω)` to its extension by zero in `L²(ℝᵈ)`, where the
Fréchet-Kolmogorov criterion `totallyBounded_of_lipschitz_translation` applies: the family is
uniformly bounded, supported in a fixed ball (`Ω` bounded), and uniformly Lipschitz under
translation. The translation modulus comes from the gradient estimate
`integral_sq_sub_translation_le` on the smooth approximants, passed to the limit through
`transL2_sub_le_of_tendsto'`.
-/

@[expose] public section

open MeasureTheory InnerProductSpace Metric Filter
open scoped RealInnerProductSpace ENNReal Topology

noncomputable section

namespace EllipticPdes.Sobolev

variable {d : ℕ}

/-- The squared `L²` norm of any class is the integral of its square. -/
lemma norm_sq_L2_eq {α : Type*} [MeasurableSpace α] {μ : Measure α} (f : Lp ℝ 2 μ) :
    ‖f‖ ^ 2 = ∫ x, (f x) ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [RCLike.inner_apply, conj_trivial]
  simp_rw [pow_two]

/-- **Extension of a test class is the function.** The extension by zero of the `L²(Ω)` class of a
test function `φ` equals `φ` almost everywhere on `ℝᵈ`, since `φ` is supported in `Ω`. -/
lemma extCls_ae {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩm : MeasurableSet Ω)
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω φ) :
    (lpExtendByZero volume 2 Ω hΩm h.testCls : EuclideanSpace ℝ (Fin d) → ℝ) =ᵐ[volume] φ := by
  have h1 := coeFn_lpExtendByZero hΩm h.testCls
  have h3 : Ω.indicator (h.testCls : EuclideanSpace ℝ (Fin d) → ℝ) =ᵐ[volume] Ω.indicator φ := by
    have hr : ∀ᵐ x ∂volume, x ∈ Ω → (h.testCls : EuclideanSpace ℝ (Fin d) → ℝ) x = φ x :=
      (ae_restrict_iff' hΩm).mp h.mem_lp.coeFn_toLp
    filter_upwards [hr] with x hx
    by_cases hxΩ : x ∈ Ω
    · rw [Set.indicator_of_mem hxΩ, Set.indicator_of_mem hxΩ, hx hxΩ]
    · rw [Set.indicator_of_notMem hxΩ, Set.indicator_of_notMem hxΩ]
  have h4 : Ω.indicator φ = φ := by
    funext x; by_cases hxΩ : x ∈ Ω
    · rw [Set.indicator_of_mem hxΩ]
    · rw [Set.indicator_of_notMem hxΩ, image_eq_zero_of_notMem_tsupport (fun hc => hxΩ (h.2.2 hc))]
  exact (h1.trans h3).trans (Filter.EventuallyEq.of_eq h4)

/-- The squared `L²(Ω)` norm of a partial-derivative class is the integral of the squared partial
over `Ω`. -/
lemma partialCls_norm_sq_eq {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω φ) (i : Fin d) :
    ‖h.partialCls i‖ ^ 2 = ∫ x in Ω, (partialD i φ x) ^ 2 := by
  rw [norm_sq_L2_eq (h.partialCls i)]
  refine integral_congr_ae ?_
  filter_upwards [(h.memLp_partialD i).coeFn_toLp] with x hx
  rw [show (h.partialCls i : EuclideanSpace ℝ (Fin d) → ℝ) x = partialD i φ x from hx]

/-- The `L²(ℝᵈ)` gradient energy of a test function decomposes into the sum of its
partial-derivative class norms: `∫ ‖∇φ‖² = ∑ᵢ ‖[∂ᵢφ]‖²`. Combines the Riesz identity
`norm_sq_clm_eq_sum_apply_single` with the fact that each partial is supported in `Ω`. -/
lemma integral_grad_norm_sq_eq {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω φ) :
    ∫ x, ‖fderiv ℝ φ x‖ ^ 2 = ∑ i, ‖h.partialCls i‖ ^ 2 := by
  have hpt : (fun x => ‖fderiv ℝ φ x‖ ^ 2) = fun x => ∑ i, (partialD i φ x) ^ 2 := by
    funext x; rw [norm_sq_clm_eq_sum_apply_single (fderiv ℝ φ x)]; rfl
  have hint : ∀ i : Fin d, Integrable (fun x => (partialD i φ x) ^ 2) volume := fun i =>
    ((h.continuous_partialD i).fun_pow 2).integrable_of_hasCompactSupport
      (by simpa only [Function.comp_def] using
        (h.hasCompactSupport_partialD i).comp_left (g := fun y : ℝ => y ^ 2) (by norm_num))
  rw [hpt, integral_finsetSum Finset.univ (fun i _ => hint i)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [partialCls_norm_sq_eq h i]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hxts : x ∉ tsupport (partialD i φ) :=
    fun hc => hx (((tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := φ)
      (EuclideanSpace.single i 1)).trans h.2.2) hc)
  simp [image_eq_zero_of_notMem_tsupport hxts]

/-- **Per-test-function translation modulus (squared).** Through the extension by zero, the
squared `L²(ℝᵈ)` translation increment of a test class is controlled by `‖hvec‖²` times the sum of
its partial-derivative class norms. This is `integral_sq_sub_translation_le` transported to the
extended class. -/
lemma mod_sq {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩm : MeasurableSet Ω)
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω φ) (hvec : EuclideanSpace ℝ (Fin d)) :
    ‖transL2 hvec (lpExtendByZero volume 2 Ω hΩm h.testCls)
        - lpExtendByZero volume 2 Ω hΩm h.testCls‖ ^ 2
      ≤ ‖hvec‖ ^ 2 * ∑ i, ‖h.partialCls i‖ ^ 2 := by
  rw [norm_sq_transL2_sub hvec (lpExtendByZero volume 2 Ω hΩm h.testCls)]
  have hae := extCls_ae hΩm h
  have hcomp : ∀ᵐ x ∂volume,
      (lpExtendByZero volume 2 Ω hΩm h.testCls : EuclideanSpace ℝ (Fin d) → ℝ) (x + hvec)
        = φ (x + hvec) :=
    ((measurePreserving_add_right volume hvec).quasiMeasurePreserving.tendsto_ae).eventually hae
  have hcongr : (fun x =>
      ((lpExtendByZero volume 2 Ω hΩm h.testCls : EuclideanSpace ℝ (Fin d) → ℝ) (x + hvec)
        - lpExtendByZero volume 2 Ω hΩm h.testCls x) ^ 2)
      =ᵐ[volume] fun x => (φ (x + hvec) - φ x) ^ 2 := by
    filter_upwards [hcomp, hae] with x h1 h2; rw [h1, h2]
  rw [integral_congr_ae hcongr]
  calc ∫ x, (φ (x + hvec) - φ x) ^ 2
      ≤ ‖hvec‖ ^ 2 * ∫ x, ‖fderiv ℝ φ x‖ ^ 2 :=
        integral_sq_sub_translation_le (h.1.of_le (by exact_mod_cast le_top)) h.2.1 hvec
    _ = ‖hvec‖ ^ 2 * ∑ i, ‖h.partialCls i‖ ^ 2 := by rw [integral_grad_norm_sq_eq h]

/-- **Translation modulus of an `H₀¹` element.** For `U ∈ H₀¹(Ω)`, the extension by zero of
`embL2 Ω U = U 0` is Lipschitz under translation with modulus `‖U‖`. The bound comes from the smooth
approximants of `U` (density of test graphs) through `transL2_sub_le_of_tendsto'`. -/
lemma trans_mod {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩm : MeasurableSet Ω) (U : H01 Ω)
    (hvec : EuclideanSpace ℝ (Fin d)) :
    ‖transL2 hvec (lpExtendByZero volume 2 Ω hΩm (embL2 Ω U))
        - lpExtendByZero volume 2 Ω hΩm (embL2 Ω U)‖ ≤ ‖U‖ * ‖hvec‖ := by
  set P0 : H1amb Ω →L[ℝ] L2D Ω := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (d + 1) => L2D Ω) 0 with hP0
  -- density: a sequence of test graphs converging to `↑U`
  obtain ⟨uk, huk_mem, huk⟩ := mem_closure_iff_seq_limit.mp
    (show (↑U : H1amb Ω) ∈ closure (↑(Submodule.span ℝ (testGraphSet Ω)) : Set (H1amb Ω)) by
      rw [← Submodule.topologicalClosure_coe]; exact SetLike.mem_coe.mpr U.2)
  have hmem' : ∀ k, ∃ (φ : EuclideanSpace ℝ (Fin d) → ℝ) (h : IsTestFn Ω φ),
      uk k = h.testGraph := by
    intro k
    have hk := huk_mem k
    rw [span_testGraphSet] at hk
    exact hk
  choose φk hk huk_eq using hmem'
  -- the approximating L²(ℝᵈ) sequence and its moduli
  set gk : ℕ → EucL2 d := fun k => lpExtendByZero volume 2 Ω hΩm (hk k).testCls with hgk
  set Λk : ℕ → ℝ := fun k => Real.sqrt (∑ i, ‖(hk k).partialCls i‖ ^ 2) with hΛk
  -- gk → e (embL2 Ω U)
  have htend : Tendsto gk atTop (𝓝 (lpExtendByZero volume 2 Ω hΩm (embL2 Ω U))) := by
    have hcomp : Continuous (fun v : H1amb Ω => lpExtendByZero volume 2 Ω hΩm (P0 v)) :=
      (lpExtendByZero volume 2 Ω hΩm).continuous.comp P0.continuous
    have hgk_eq : (fun k => lpExtendByZero volume 2 Ω hΩm (P0 (uk k))) = gk := by
      funext k; simp only [hgk, hP0, huk_eq k, PiLp.proj_apply, IsTestFn.testGraph_zero]
    have hlim_eq : lpExtendByZero volume 2 Ω hΩm (P0 (↑U : H1amb Ω))
        = lpExtendByZero volume 2 Ω hΩm (embL2 Ω U) := by
      rw [hP0, PiLp.proj_apply, embL2_apply]
    have ht0 := (hcomp.tendsto (↑U : H1amb Ω)).comp huk
    simp only [Function.comp_def, hgk_eq, hlim_eq] at ht0
    exact ht0
  -- Λk → Λ := sqrt (∑ ‖U i.succ‖²)
  have hΛtend : Tendsto Λk atTop (𝓝 (Real.sqrt (∑ (i : Fin d), ‖(↑U : H1amb Ω) i.succ‖ ^ 2))) := by
    have hcoord : Continuous (fun v : H1amb Ω => Real.sqrt (∑ (i : Fin d), ‖v i.succ‖ ^ 2)) := by
      apply Real.continuous_sqrt.comp
      exact continuous_finsetSum Finset.univ (fun (i : Fin d) _ =>
        (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (d + 1) => L2D Ω) i.succ).continuous).norm).pow 2)
    have hΛeq : (fun k => Real.sqrt (∑ (i : Fin d), ‖(uk k) i.succ‖ ^ 2)) = Λk := by
      funext k
      simp only [hΛk]
      congr 1
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [huk_eq k, IsTestFn.testGraph_succ]
    have ht := (hcoord.tendsto (↑U : H1amb Ω)).comp huk
    simp only [Function.comp_def, hΛeq] at ht
    exact ht
  -- per-k modulus
  have hmod : ∀ k, ∀ hv, ‖transL2 hv (gk k) - gk k‖ ≤ Λk k * ‖hv‖ := by
    intro k hv
    have hb := mod_sq hΩm (hk k) hv
    rw [show ‖transL2 hv (gk k) - gk k‖ = Real.sqrt (‖transL2 hv (gk k) - gk k‖ ^ 2)
          from (Real.sqrt_sq (norm_nonneg _)).symm]
    calc Real.sqrt (‖transL2 hv (gk k) - gk k‖ ^ 2)
        ≤ Real.sqrt (‖hv‖ ^ 2 * ∑ i, ‖(hk k).partialCls i‖ ^ 2) := Real.sqrt_le_sqrt hb
      _ = Λk k * ‖hv‖ := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _), hΛk, mul_comm]
  -- assemble and bound Λ ≤ ‖U‖
  have key := transL2_sub_le_of_tendsto' htend hΛtend hmod hvec
  refine key.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  rw [show ‖U‖ = Real.sqrt (‖U‖ ^ 2) from (Real.sqrt_sq (norm_nonneg _)).symm]
  apply Real.sqrt_le_sqrt
  have hnorm : ‖U‖ ^ 2 = ∑ j, ‖(↑U : H1amb Ω) j‖ ^ 2 := by
    rw [show ‖U‖ = ‖(↑U : H1amb Ω)‖ from rfl,
      PiLp.norm_sq_eq_of_L2 (fun _ : Fin (d + 1) => L2D Ω) (↑U)]
  rw [hnorm, Fin.sum_univ_succ]
  linarith [sq_nonneg ‖(↑U : H1amb Ω) 0‖]

/-- The embedding `embL2 Ω` is a contraction: `‖U 0‖ ≤ ‖U‖`. -/
lemma embL2_norm_le {Ω : Set (EuclideanSpace ℝ (Fin d))} (U : H01 Ω) : ‖embL2 Ω U‖ ≤ ‖U‖ := by
  rw [embL2_apply, show ‖U‖ = ‖(↑U : H1amb Ω)‖ from rfl,
    ← Real.sqrt_sq (norm_nonneg ((↑U : H1amb Ω) 0)), ← Real.sqrt_sq (norm_nonneg (↑U : H1amb Ω))]
  apply Real.sqrt_le_sqrt
  rw [PiLp.norm_sq_eq_of_L2 (fun _ : Fin (d + 1) => L2D Ω) (↑U)]
  exact Finset.single_le_sum (f := fun i : Fin (d + 1) => ‖(↑U : H1amb Ω) i‖ ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ (0 : Fin (d + 1)))

/-- **Rellich-Kondrachov compact embedding.** For bounded measurable `Ω`, the embedding
`embL2 Ω : H₀¹(Ω) →L[ℝ] L²(Ω)` is a compact operator. This discharges the single analytic
hypothesis of the Fredholm theory in `Compactness.lean` and `Spectrum.lean`. -/
theorem embL2_isCompact {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩm : MeasurableSet Ω)
    (hΩb : Bornology.IsBounded Ω) : IsCompactOperator (embL2 Ω) := by
  obtain ⟨R, hR⟩ := hΩb.subset_closedBall (0 : EuclideanSpace ℝ (Fin d))
  set S : Set (EucL2 d) :=
    (fun U : H01 Ω => lpExtendByZero volume 2 Ω hΩm (embL2 Ω U)) '' Metric.closedBall 0 1 with hS
  have hSTB : TotallyBounded S := by
    refine totallyBounded_of_lipschitz_translation S (R := R) (M := 1) (Λ := 1) ?_ ?_ ?_
    · rintro g ⟨U, hU, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right] at hU
      rw [(lpExtendByZero volume 2 Ω hΩm).norm_map]
      exact (embL2_norm_le U).trans hU
    · rintro g ⟨U, hU, rfl⟩
      filter_upwards [lpExtendByZero_ae_eq_zero hΩm (embL2 Ω U)] with x hx hxR
      exact hx (fun hxΩ => hxR (hR hxΩ))
    · rintro g ⟨U, hU, rfl⟩ hvec
      rw [Metric.mem_closedBall, dist_zero_right] at hU
      exact (trans_mod hΩm U hvec).trans (mul_le_mul_of_nonneg_right hU (norm_nonneg _))
  have hpre : (lpExtendByZero volume 2 Ω hΩm) ⁻¹' S = embL2 Ω '' Metric.closedBall 0 1 := by
    rw [hS, ← Set.image_image (lpExtendByZero volume 2 Ω hΩm) (embL2 Ω),
      Set.preimage_image_eq _ (lpExtendByZero volume 2 Ω hΩm).injective]
  have hTB : TotallyBounded (embL2 Ω '' Metric.closedBall (0 : H01 Ω) 1) := by
    rw [← hpre]
    exact totallyBounded_preimage
      (lpExtendByZero volume 2 Ω hΩm).isometry.isUniformInducing hSTB
  exact (isCompactOperator_iff_isCompact_closure_image_closedBall (embL2 Ω).toLinearMap
    one_pos).mpr (hTB.closure.isCompact_of_isClosed isClosed_closure)

/-! ### Fredholm and spectral theorems with the Rellich hypothesis discharged

With `embL2_isCompact` proved, the analytic hypothesis `IsCompactOperator (embL2 Ω)` threaded
through `Compactness.lean` and `Spectrum.lean` is no longer assumed: every headline theorem holds
for a bounded measurable domain outright.
-/

/-- The Fredholm alternative for a bounded measurable domain, with no compactness hypothesis. -/
theorem FullEllipticOp.fredholm_alternative_of_bounded (Op : FullEllipticOp d)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) (hΩm : MeasurableSet Ω)
    (hΩb : Bornology.IsBounded Ω) :
    (∃ u : H01 Ω, u ≠ 0 ∧ ∀ v : H01 Ω, Op.fullBilin Ω u v = 0)
      ∨ (∀ f : H01 Ω →L[ℝ] ℝ, ∃! u : H01 Ω, ∀ v : H01 Ω, Op.fullBilin Ω u v = f v) :=
  Op.fredholm_alternative_rellich Ω (embL2_isCompact hΩm hΩb)

/-- The Fredholm uniqueness-implies-existence corollary for a bounded measurable domain.

Terminal result of the library, the companion of `fredholm_alternative_of_bounded`.
Nothing else consumes it. -/
theorem FullEllipticOp.fredholm_unique_imp_exists_of_bounded (Op : FullEllipticOp d)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) (hΩm : MeasurableSet Ω)
    (hΩb : Bornology.IsBounded Ω)
    (huniq : ∀ u : H01 Ω, (∀ v : H01 Ω, Op.fullBilin Ω u v = 0) → u = 0)
    (f : H01 Ω →L[ℝ] ℝ) :
    ∃! u : H01 Ω, ∀ v : H01 Ω, Op.fullBilin Ω u v = f v :=
  Op.fredholm_unique_imp_exists_rellich Ω (embL2_isCompact hΩm hΩb) huniq f

/-- **Spectral theorem for the Dirichlet Laplacian on a bounded measurable domain**, with the
Rellich compact embedding discharged. -/
theorem dirichlet_spectral_of_bounded (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (hΩm : MeasurableSet Ω) (hΩb : Bornology.IsBounded Ω) (CP : ℝ) (hCP : 0 ≤ CP)
    (hbase : ∀ {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω φ),
      ‖(h.testGraph 0 : L2D Ω)‖ ^ 2 ≤ CP * ∑ i : Fin d, ‖h.testGraph i.succ‖ ^ 2) :
    (⨆ μ : ℝ, Module.End.eigenspace
        (solOp (laplaceBilin Ω) (laplaceBilin_coercive Ω CP hCP hbase)
          : Module.End ℝ (L2D Ω)) μ)ᗮ = ⊥ :=
  dirichlet_spectral Ω CP hCP hbase (embL2_isCompact hΩm hΩb)

/-- **Spectral theorem for the general symmetric divergence-form operator on a bounded measurable
domain**, with the Rellich compact embedding discharged.

Terminal result of the library. Nothing else consumes it. -/
theorem symmetric_fullElliptic_spectral_of_bounded (Op : FullEllipticOp d)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) (hΩm : MeasurableSet Ω) (hΩb : Bornology.IsBounded Ω)
    (hb : ∀ i, ∀ᵐ x ∂(volume.restrict Ω), Op.b x i = 0)
    (hc : ∀ᵐ x ∂(volume.restrict Ω), 0 ≤ Op.c x)
    (hAsymm : ∀ᵐ x ∂(volume.restrict Ω), ∀ i j, Op.a x i j = Op.a x j i)
    (CP : ℝ) (hCP : 0 ≤ CP)
    (hbase : ∀ {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω φ),
      ‖(h.testGraph 0 : L2D Ω)‖ ^ 2 ≤ CP * ∑ i : Fin d, ‖h.testGraph i.succ‖ ^ 2) :
    (⨆ μ : ℝ, Module.End.eigenspace
        (solOp (Op.fullBilin Ω) (Op.fullBilin_coercive_of_nonneg_zeroth Ω hb hc CP hCP hbase)
          : Module.End ℝ (L2D Ω)) μ)ᗮ = ⊥ :=
  symmetric_fullElliptic_spectral Op Ω hb hc hAsymm CP hCP hbase (embL2_isCompact hΩm hΩb)

end EllipticPdes.Sobolev
