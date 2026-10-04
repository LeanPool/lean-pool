/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Sobolev.H01Lattice
public import LeanPool.EllipticPDE.Regularity.Localise.Datum
public import LeanPool.EllipticPDE.Extension.GraphOperator


/-!
# Weak solutions with no boundary condition

Evans, *Partial Differential Equations* (2nd ed.), §6.3.1 poses interior regularity for
`u ∈ H¹(U)` solving `L u = f` weakly, with nothing asked of `u` on `∂U`. The interior chain of
this development (`interior_H2_estimate`, `higher_interior_regularity`, `interior_smooth`) is
stated for `u ∈ H₀¹(Ω)`, tested against every `w ∈ H₀¹(Ω)`. This file states Evans's notion on
the ambient graph space and supplies the two facts that reduce it to the `H₀¹` chain.

* `IsLocalWeakSolution Op Ω U f`: `U ∈ W12 Ω` and `B[U, φ] = ∫ f φ` for every test function
  `φ` of `Ω`. `IsLocalWeakSolution.weakForm` extends the identity to every `w ∈ H₀¹(Ω)` by
  density, which is the form Evans writes.
* `cutoffMul_mem_H01_of_mem_W12`: for a test function `η` of `Ω` and `U ∈ W12 Ω`, the product
  `η U` lies in `H₀¹(Ω)`. No closure argument is available, since `U` is not itself a limit of
  test graphs; the whole-space weak gradient of `η U` is read off the `W12` constraint against
  `η φ`, and `mem_H01_of_hasCompactSupport` does the rest.

The connection to the plain-representative predicate `LocalWeakSol` of `Localise/Datum.lean`
is an equivalence once the representatives are identified almost everywhere
(`isLocalWeakSolution_iff_localWeakSol`), and `isLocalWeakSolution_of_localWeakSol` builds the
ambient element from square-integrable representatives with a weak gradient.

## Main declarations

* `pairL`: the functional `B[U, ·]` on the ambient space.
* `IsLocalWeakSolution`, `IsLocalWeakSolution.weakForm`, `isLocalWeakSolution_of_H01`.
* `cutoffMul_mem_H01_of_mem_W12`.
* `isLocalWeakSolution_iff_localWeakSol`, `isLocalWeakSolution_of_localWeakSol`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev EllipticPdes.Embedding EllipticPdes.Extension

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-- The gradient coordinates of an element of `W12 Ω` are weak derivatives of its function
coordinate on `Ω`, in the `L²`-class form `HasWeakDerivOn` states. -/
theorem hasWeakDerivOn_of_mem_W12 {U : H1amb Ω} (hU : U ∈ W12 Ω) (k : Fin d) :
    HasWeakDerivOn Ω k (U 0) (U k.succ) := by
  intro φ hφc hφcs hφΩ
  exact hasWeakGradOn_of_mem_W12 hU φ hφc hφcs hφΩ k

/-- An `L²(Ω)` class times a continuous compactly supported function is integrable on `Ω`. -/
theorem integrable_L2D_mul {g : L2D Ω} {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hc : Continuous ψ) (hcs : HasCompactSupport ψ) :
    Integrable (fun x => (g x : ℝ) * ψ x) (volume.restrict Ω) :=
  (Lp.memLp g).integrable_mul (memLp_two_restrict_of_continuous_hasCompactSupport hc hcs)

/-- A bounded continuous weight times a whole-space `L²` class is in `L²`. -/
theorem memLp_weight_mul {g : EucL2 d} {η : EuclideanSpace ℝ (Fin d) → ℝ}
    (hc : Continuous η) {M : ℝ} (hM : ∀ x, |η x| ≤ M) :
    MemLp (fun x => η x * (g x : ℝ)) 2 volume := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  refine ((Lp.memLp g).const_mul M).of_le
    (hc.aestronglyMeasurable.mul (Lp.aestronglyMeasurable g)) ?_
  refine Eventually.of_forall fun x => ?_
  simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hM0]
  exact mul_le_mul_of_nonneg_right (hM x) (abs_nonneg _)

/-- An integrand vanishing off `Ω`, with `g` replaced by its extension by zero, integrates to
the same value over the whole space as over `Ω`. -/
theorem integral_extendL2_mul_eq {g : L2D Ω} (hΩm : MeasurableSet Ω)
    {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : ∀ x, x ∉ Ω → ψ x = 0) :
    ∫ x, (extendL2 hΩm g x : ℝ) * ψ x = ∫ x in Ω, (g x : ℝ) * ψ x := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ω)
    (fun x hx => by rw [hψ x hx, mul_zero])]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae (coeFn_extendL2 hΩm g), ae_restrict_mem hΩm] with x h1 h2
  rw [h1, Set.indicator_of_mem h2]

/-- **Cutoff of an element of `W12 Ω` lies in `H₀¹(Ω)`.** For a test function `η` of an open
`Ω`, the product `η U` of the cutoff-multiplication operator is in `H₀¹(Ω)` whenever `U` is in
`W12 Ω`, with no boundary condition on `U`.

The closure argument of `cutoffMul_mem_H01` needs `U` to be a limit of test graphs. Here the
whole-space weak gradient of `η U₀` is `η U_{k+1} + ∂_k η U₀`, read off
the `W12` constraint against the test function `η φ`, and the mollification density
`mem_H01_of_hasCompactSupport` places a compactly supported element with a whole-space weak
gradient in `H₀¹(Ω)`. -/
theorem cutoffMul_mem_H01_of_mem_W12 (hΩo : IsOpen Ω) {η : EuclideanSpace ℝ (Fin d) → ℝ}
    (hη : IsTestFn Ω η) {U : H1amb Ω} (hU : U ∈ W12 Ω) :
    cutoffMul hη U ∈ H01 Ω := by
  classical
  have hΩm : MeasurableSet Ω := hΩo.measurableSet
  obtain ⟨M, hM⟩ := exists_abs_bound hη
  set g0 : EucL2 d := extendL2 hΩm (U 0) with hg0
  set gk : Fin d → EucL2 d := fun k => extendL2 hΩm (U k.succ) with hgk
  set w : EuclideanSpace ℝ (Fin d) → ℝ := fun x => η x * (g0 x : ℝ) with hw
  set h : Fin d → EuclideanSpace ℝ (Fin d) → ℝ :=
    fun k x => η x * (gk k x : ℝ) + partialD k η x * (g0 x : ℝ) with hh
  have hwL : MemLp w 2 volume := memLp_weight_mul hη.continuous hM
  have hhL : ∀ k, MemLp (h k) 2 volume := fun k => by
    obtain ⟨Mk, hMk⟩ := exists_abs_bound_partialD hη k
    exact (memLp_weight_mul hη.continuous hM).add
      (memLp_weight_mul (hη.continuous_partialD k) hMk)
  have hηoff : ∀ x, x ∉ Ω → η x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun hc => hx (hη.2.2 hc))
  have hdηoff : ∀ k x, x ∉ Ω → partialD k η x = 0 := fun k x hx =>
    image_eq_zero_of_notMem_tsupport (fun hc => hx (hη.2.2 (tsupport_partialD_subset k η hc)))
  -- The whole-space weak gradient.
  have hwg : HasWeakGradOn Set.univ w h := by
    intro φ hφc hφcs _ k
    simp only [Measure.restrict_univ]
    have hηφ : IsTestFn Ω (fun x => η x * φ x) :=
      ⟨hη.1.mul hφc, hφcs.mul_left, tsupport_mul_subset_left.trans hη.2.2⟩
    have key := hasWeakDerivOn_of_mem_W12 hU k _ hηφ.1 hηφ.2.1 hηφ.2.2
    rw [partialD_mul (hη.1.differentiable (by simp)) (hφc.differentiable (by simp)) k] at key
    have hdφc : Continuous (partialD k φ) :=
      (hφc.continuous_fderiv (by simp)).clm_apply continuous_const
    have hdφcs : HasCompactSupport (partialD k φ) := hφcs.fderiv_apply (𝕜 := ℝ) _
    have i1 : Integrable (fun x => ((U 0 : L2D Ω) x : ℝ) * (η x * partialD k φ x))
        (volume.restrict Ω) :=
      integrable_L2D_mul (hη.continuous.mul hdφc) hdφcs.mul_left
    have i2 : Integrable (fun x => ((U 0 : L2D Ω) x : ℝ) * (partialD k η x * φ x))
        (volume.restrict Ω) :=
      integrable_L2D_mul ((hη.continuous_partialD k).mul hφc.continuous) hφcs.mul_left
    have hsplit : ∫ x in Ω, ((U 0 : L2D Ω) x : ℝ)
          * (η x * partialD k φ x + partialD k η x * φ x)
        = (∫ x in Ω, ((U 0 : L2D Ω) x : ℝ) * (η x * partialD k φ x))
          + ∫ x in Ω, ((U 0 : L2D Ω) x : ℝ) * (partialD k η x * φ x) := by
      rw [← integral_add i1 i2]; congr 1; funext x; ring
    have hL : ∫ x, w x * partialD k φ x
        = ∫ x in Ω, ((U 0 : L2D Ω) x : ℝ) * (η x * partialD k φ x) := by
      rw [← integral_extendL2_mul_eq hΩm (fun x hx => by
        simp only [hηoff x hx, zero_mul])]
      congr 1; funext x; simp only [hw]; ring
    have hR : ∫ x, h k x * φ x
        = (∫ x in Ω, ((U k.succ : L2D Ω) x : ℝ) * (η x * φ x))
          + ∫ x in Ω, ((U 0 : L2D Ω) x : ℝ) * (partialD k η x * φ x) := by
      have e1 : ∫ x, (extendL2 hΩm (U k.succ) x : ℝ) * (η x * φ x)
          = ∫ x in Ω, ((U k.succ : L2D Ω) x : ℝ) * (η x * φ x) :=
        integral_extendL2_mul_eq hΩm (fun x hx => by simp only [hηoff x hx, zero_mul])
      have e2 : ∫ x, (extendL2 hΩm (U 0) x : ℝ) * (partialD k η x * φ x)
          = ∫ x in Ω, ((U 0 : L2D Ω) x : ℝ) * (partialD k η x * φ x) :=
        integral_extendL2_mul_eq hΩm (fun x hx => by simp only [hdηoff k x hx, zero_mul])
      have m1 : MemLp (fun x => η x * φ x) 2 volume :=
        (hη.continuous.mul hφc.continuous).memLp_of_hasCompactSupport hφcs.mul_left
      have m2 : MemLp (fun x => partialD k η x * φ x) 2 volume :=
        ((hη.continuous_partialD k).mul hφc.continuous).memLp_of_hasCompactSupport
          hφcs.mul_left
      have I1 : Integrable (fun x => (extendL2 hΩm (U k.succ) x : ℝ) * (η x * φ x)) volume :=
        (Lp.memLp (extendL2 hΩm (U k.succ))).integrable_mul m1
      have I2 : Integrable (fun x => (extendL2 hΩm (U 0) x : ℝ) * (partialD k η x * φ x))
          volume :=
        (Lp.memLp (extendL2 hΩm (U 0))).integrable_mul m2
      rw [← e1, ← e2, ← integral_add I1 I2]
      congr 1; funext x; simp only [hh, hgk, hg0]; ring
    rw [hL, hR]
    linarith [key, hsplit]
  have hmem := mem_H01_of_hasCompactSupport hΩo hwg hwL hhL hη.2.1.mul_right
    (tsupport_mul_subset_left.trans hη.2.2)
  convert hmem using 1
  apply PiLp.ext
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · rw [cutoffMul_apply_zero]
    simp only [Fin.cons_zero]
    apply Lp.ext
    filter_upwards [mulTest_coeFn hη (U 0),
      MemLp.coeFn_toLp (hwL.mono_measure Measure.restrict_le_self),
      ae_restrict_of_ae (coeFn_extendL2 hΩm (U 0)), ae_restrict_mem hΩm] with x h1 h2 h3 h4
    rw [h1, h2]
    simp only [hw, hg0]
    rw [h3, Set.indicator_of_mem h4]
  · rw [cutoffMul_apply_succ]
    simp only [Fin.cons_succ]
    apply Lp.ext
    filter_upwards [Lp.coeFn_add (mulTest hη (U i.succ)) (mulTestPartial hη i (U 0)),
      mulTest_coeFn hη (U i.succ), mulTestPartial_coeFn hη i (U 0),
      MemLp.coeFn_toLp ((hhL i).mono_measure Measure.restrict_le_self),
      ae_restrict_of_ae (coeFn_extendL2 hΩm (U 0)),
      ae_restrict_of_ae (coeFn_extendL2 hΩm (U i.succ)), ae_restrict_mem hΩm]
      with x h0 h1 h2 h3 h4 h5 h6
    rw [h0, Pi.add_apply, h1, h2, h3, hh]
    simp only [hgk, hg0]
    rw [h4, h5, Set.indicator_of_mem h6, Set.indicator_of_mem h6]

/-! ### Ambient pairing and the local weak formulation -/

/-- The bilinear form `B[U, ·]` for a fixed ambient `U`, as a continuous functional on the
ambient space. On `H₀¹(Ω) × H₀¹(Ω)` it is `FullEllipticOp.fullBilin` (`fullBilin_eq_pairL`). -/
def pairL (Op : FullEllipticOp d) (Ω : Set (EuclideanSpace ℝ (Fin d))) (U : H1amb Ω) :
    H1amb Ω →L[ℝ] ℝ :=
  (∑ i : Fin d, ∑ j : Fin d, (innerSL ℝ (Op.toEllipticCoeff.actL i j (U i.succ))).comp
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (d + 1) => L2D Ω) j.succ))
    + (∑ i : Fin d, (innerSL ℝ (Op.bAct i (U i.succ))).comp
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (d + 1) => L2D Ω) 0))
    + (innerSL ℝ (Op.cAct (U 0))).comp (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (d + 1) => L2D Ω) 0)

theorem pairL_apply (Op : FullEllipticOp d) (U W : H1amb Ω) :
    pairL Op Ω U W
      = (∑ i : Fin d, ∑ j : Fin d, ⟪Op.toEllipticCoeff.actL i j (U i.succ), W j.succ⟫)
        + (∑ i : Fin d, ⟪Op.bAct i (U i.succ), W 0⟫) + ⟪Op.cAct (U 0), W 0⟫ := by
  simp [pairL, _root_.sum_apply]

/-- `fullBilin` is the ambient pairing on `H₀¹ × H₀¹`. -/
theorem fullBilin_eq_pairL (Op : FullEllipticOp d) (u w : H01 Ω) :
    Op.fullBilin Ω u w = pairL Op Ω (u : H1amb Ω) (w : H1amb Ω) := by
  rw [pairL_apply, FullEllipticOp.fullBilin_apply, EllipticCoeff.bilin_apply,
    FullEllipticOp.lowerBilin_apply]
  ring

/-- The ambient pairing against a test graph, as integrals of representatives. -/
theorem pairL_testGraph_eq (Op : FullEllipticOp d) (U : H1amb Ω)
    {v : EuclideanSpace ℝ (Fin d) → ℝ} (hv : IsTestFn Ω v) :
    pairL Op Ω U hv.testGraph
      = (∑ i : Fin d, ∑ j : Fin d, ∫ x in Ω, Op.a x i j * (U i.succ x : ℝ) * partialD j v x)
        + (∑ i : Fin d, ∫ x in Ω, Op.b x i * (U i.succ x : ℝ) * v x)
        + ∫ x in Ω, Op.c x * (U 0 x : ℝ) * v x := by
  have hgrad : ∀ j : Fin d, (hv.testGraph j.succ : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume.restrict Ω] partialD j v := by
    intro j; rw [IsTestFn.testGraph_succ]; exact (hv.memLp_partialD j).coeFn_toLp
  have hfun : (hv.testGraph 0 : EuclideanSpace ℝ (Fin d) → ℝ) =ᵐ[volume.restrict Ω] v := by
    rw [IsTestFn.testGraph_zero]; exact hv.mem_lp.coeFn_toLp
  rw [pairL_apply]
  congr 1
  · congr 1
    · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [Op.toEllipticCoeff.inner_actL_eq]
      refine integral_congr_ae ?_
      filter_upwards [hgrad j] with x hx; rw [hx]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [FullEllipticOp.bAct, inner_mulCoeffL_eq]
      refine integral_congr_ae ?_
      filter_upwards [hfun] with x hx; rw [hx]
  · rw [FullEllipticOp.cAct, inner_mulCoeffL_eq]
    refine integral_congr_ae ?_
    filter_upwards [hfun] with x hx; rw [hx]

/-- **Local weak solution with no boundary condition.** `U ∈ W12 Ω`, the ambient encoding of
Evans's `u ∈ H¹(U)`, and `B[U, φ] = ∫_Ω f φ` for every test function `φ` of `Ω`. Nothing is
asked of `U` at `∂Ω`. `IsLocalWeakSolution.weakForm` gives the identity against every
`w ∈ H₀¹(Ω)`, which is the formulation of Evans, *Partial Differential Equations* (2nd ed.),
§6.3.1. -/
def IsLocalWeakSolution (Op : FullEllipticOp d) (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (U : H1amb Ω) (f : L2D Ω) : Prop :=
  U ∈ W12 Ω ∧ ∀ (φ : EuclideanSpace ℝ (Fin d) → ℝ) (hφ : IsTestFn Ω φ),
    pairL Op Ω U hφ.testGraph = ∫ x in Ω, (f x : ℝ) * φ x

/-- A weak solution in `H₀¹(Ω)`, in the formulation of the interior chain, is a local weak
solution. -/
theorem isLocalWeakSolution_of_H01 (Op : FullEllipticOp d) (u : H01 Ω) (f : L2D Ω)
    (hweak : ∀ w : H01 Ω, Op.fullBilin Ω u w
      = ∫ x in Ω, (f x : ℝ) * ((w : H1amb Ω) 0 x : ℝ)) :
    IsLocalWeakSolution Op Ω (u : H1amb Ω) f := by
  refine ⟨H01_le_W12 Ω u.2, fun φ hφ => ?_⟩
  have h := hweak ⟨hφ.testGraph, testGraph_mem_H01 hφ⟩
  rw [fullBilin_eq_pairL] at h
  rw [h]
  refine integral_congr_ae ?_
  change (fun x => (f x : ℝ) * (hφ.testGraph 0 x : ℝ)) =ᵐ[_] _
  rw [IsTestFn.testGraph_zero]
  filter_upwards [hφ.mem_lp.coeFn_toLp] with x hx
  rw [IsTestFn.testCls, hx]

/-- **Density.** A local weak solution satisfies the identity against every `w ∈ H₀¹(Ω)`, with
the pairing in the ambient space: Evans's formulation, `u ∈ H¹(U)` tested against
`v ∈ H₀¹(U)`. -/
theorem IsLocalWeakSolution.weakForm {Op : FullEllipticOp d} {U : H1amb Ω} {f : L2D Ω}
    (hsol : IsLocalWeakSolution Op Ω U f) {W : H1amb Ω} (hW : W ∈ H01 Ω) :
    pairL Op Ω U W = ∫ x in Ω, (f x : ℝ) * (W 0 x : ℝ) := by
  set D : H1amb Ω →L[ℝ] ℝ := innerSL ℝ (PiLp.single 2 (0 : Fin (d + 1)) f) with hD
  have hDapp : ∀ V : H1amb Ω, D V = ∫ x in Ω, (f x : ℝ) * (V 0 x : ℝ) := by
    intro V
    change ⟪PiLp.single 2 (0 : Fin (d + 1)) f, V⟫ = _
    rw [inner_single_left, L2.inner_def]
    exact integral_congr_ae (Eventually.of_forall fun a => Real.inner_apply _ _)
  have hclosed : IsClosed {V : H1amb Ω | pairL Op Ω U V = D V} :=
    isClosed_eq (pairL Op Ω U).continuous D.continuous
  have hspan : ((Submodule.span ℝ (testGraphSet Ω) : Submodule ℝ (H1amb Ω)) : Set (H1amb Ω))
      ⊆ {V | pairL Op Ω U V = D V} := by
    rw [span_testGraphSet]
    rintro _ ⟨φ, hφ, rfl⟩
    simp only [Set.mem_ofPred_eq]
    rw [hsol.2 φ hφ, hDapp]
    refine integral_congr_ae ?_
    rw [IsTestFn.testGraph_zero]
    filter_upwards [hφ.mem_lp.coeFn_toLp] with x hx
    rw [IsTestFn.testCls, hx]
  have hsub : (H01 Ω : Set (H1amb Ω)) ⊆ {V | pairL Op Ω U V = D V} := by
    rw [H01, Submodule.topologicalClosure_coe]
    exact closure_minimal hspan hclosed
  have := hsub hW
  simp only [Set.mem_ofPred_eq] at this
  rw [this, hDapp]

/-! ### Plain representatives -/

/-- **`IsLocalWeakSolution` is `LocalWeakSol` on representatives.** For `U ∈ W12 Ω` whose
coordinates agree almost everywhere on `Ω` with plain functions `u` and `G`, and a datum class
agreeing with `f`, the ambient local weak formulation is the plain-integral one of
`Localise/Datum.lean`. -/
theorem isLocalWeakSolution_iff_localWeakSol (Op : FullEllipticOp d) {U : H1amb Ω}
    (hU : U ∈ W12 Ω) {F : L2D Ω} {u f : EuclideanSpace ℝ (Fin d) → ℝ}
    {G : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : (U 0 : EuclideanSpace ℝ (Fin d) → ℝ) =ᵐ[volume.restrict Ω] u)
    (hG : ∀ i, (U i.succ : EuclideanSpace ℝ (Fin d) → ℝ) =ᵐ[volume.restrict Ω] G i)
    (hF : (F : EuclideanSpace ℝ (Fin d) → ℝ) =ᵐ[volume.restrict Ω] f) :
    IsLocalWeakSolution Op Ω U F ↔ LocalWeakSol Ω Op.a Op.b Op.c f u G := by
  have hrw : ∀ (φ : EuclideanSpace ℝ (Fin d) → ℝ) (hφ : IsTestFn Ω φ),
      (pairL Op Ω U hφ.testGraph = ∫ x in Ω, (F x : ℝ) * φ x) ↔
        ((∑ i, ∑ j, ∫ x in Ω, Op.a x i j * G i x * partialD j φ x)
          + (∑ i, ∫ x in Ω, Op.b x i * G i x * φ x) + (∫ x in Ω, Op.c x * u x * φ x)
          = ∫ x in Ω, f x * φ x) := by
    intro φ hφ
    have e1 : ∀ i j, ∫ x in Ω, Op.a x i j * (U i.succ x : ℝ) * partialD j φ x
        = ∫ x in Ω, Op.a x i j * G i x * partialD j φ x := fun i j =>
      integral_congr_ae (by filter_upwards [hG i] with x hx; rw [hx])
    have e2 : ∀ i, ∫ x in Ω, Op.b x i * (U i.succ x : ℝ) * φ x
        = ∫ x in Ω, Op.b x i * G i x * φ x := fun i =>
      integral_congr_ae (by filter_upwards [hG i] with x hx; rw [hx])
    have e3 : ∫ x in Ω, Op.c x * (U 0 x : ℝ) * φ x = ∫ x in Ω, Op.c x * u x * φ x :=
      integral_congr_ae (by filter_upwards [hu] with x hx; rw [hx])
    have e4 : ∫ x in Ω, (F x : ℝ) * φ x = ∫ x in Ω, f x * φ x :=
      integral_congr_ae (by filter_upwards [hF] with x hx; rw [hx])
    rw [pairL_testGraph_eq, e4, e3, Finset.sum_congr rfl fun i _ => e2 i,
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => e1 i j]
  constructor
  · rintro ⟨-, h⟩ φ hφc hφcs hφΩ
    exact (hrw φ ⟨hφc, hφcs, hφΩ⟩).1 (h φ ⟨hφc, hφcs, hφΩ⟩)
  · intro h
    exact ⟨hU, fun φ hφ => (hrw φ hφ).2 (h φ hφ.1 hφ.2.1 hφ.2.2)⟩

/-- **Ambient local weak solution from representatives.** Square-integrable `u` and `G` on `Ω`,
with `G` the weak gradient of `u` and the plain local weak formulation, give the ambient element
`(u, G)` of `W12 Ω` as a local weak solution. -/
theorem isLocalWeakSolution_of_localWeakSol (Op : FullEllipticOp d)
    {u f : EuclideanSpace ℝ (Fin d) → ℝ} {G : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : MemLp u 2 (volume.restrict Ω)) (hG : ∀ k, MemLp (G k) 2 (volume.restrict Ω))
    (hf : MemLp f 2 (volume.restrict Ω)) (hwg : HasWeakGradOn Ω u G)
    (hsol : LocalWeakSol Ω Op.a Op.b Op.c f u G) :
    IsLocalWeakSolution Op Ω
      (WithLp.toLp 2 (Fin.cons (hu.toLp u) fun k => (hG k).toLp (G k)) : H1amb Ω)
      (hf.toLp f) := by
  have hmem := mem_W12_of_hasWeakGradOn hu hG hwg
  refine (isLocalWeakSolution_iff_localWeakSol Op hmem ?_ (fun i => ?_) hf.coeFn_toLp).2 hsol
  · change ((Fin.cons (hu.toLp u) fun k => (hG k).toLp (G k) : Fin (d + 1) → L2D Ω) 0
      : EuclideanSpace ℝ (Fin d) → ℝ) =ᵐ[_] _
    rw [Fin.cons_zero]; exact hu.coeFn_toLp
  · change ((Fin.cons (hu.toLp u) fun k => (hG k).toLp (G k) : Fin (d + 1) → L2D Ω) i.succ
      : EuclideanSpace ℝ (Fin d) → ℝ) =ᵐ[_] _
    rw [Fin.cons_succ]; exact (hG i).coeFn_toLp

end EllipticPdes.Regularity
