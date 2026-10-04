/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Existence.Garding
public import LeanPool.EllipticPDE.Regularity.DiffQuotientBound


/-!
# Caccioppoli (interior energy) estimate

The first-derivative interior estimate: for a weak solution of `L u = f`, the energy
`∫_V |∇u|²` is bounded by the data on a slightly larger set `W`. Obtained by testing
the weak formulation with `ζ² u`, using uniform ellipticity from below and Young's
inequality to absorb the gradient term. See Gilbarg-Trudinger, *Elliptic PDE of
Second Order*, Theorem 8.8, and Evans, *Partial Differential Equations* (2nd ed.),
§6.3.1.

## Cutoff-multiplication keystone

The test function `ζ² u` for `u ∈ H₀¹(Ω)` is not directly available from the graph
encoding of `Sobolev/Basic.lean`. We build it here. For a smooth compactly supported
cutoff `η` (an [`IsTestFn`]) we assemble the **cutoff-multiplication operator** on the
ambient graph space,

  `(cutoffMul η U)₀ = η · U₀`,   `(cutoffMul η U)_{i+1} = η · U_{i+1} + (∂ᵢη) · U₀`,

which is exactly the Leibniz rule `∇(η u) = η ∇u + (∇η) u`. It is a bounded operator, it
sends the graph of a test function `φ` to the graph of the product `η φ`, hence by
closure it maps `H₀¹(Ω)` into itself: [`cutoffMul_mem_H01`].
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ}

/-! ### Global sup bounds for a test function and its partials -/

/-- A smooth compactly supported function is globally bounded in absolute value. -/
lemma exists_abs_bound {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω φ) : ∃ M : ℝ, ∀ x, |φ x| ≤ M := by
  obtain ⟨C, hC⟩ := h.continuous.bounded_above_of_compact_support h.2.1
  exact ⟨C, fun x => by have := hC x; rwa [Real.norm_eq_abs] at this⟩

/-- Each partial derivative of a test function is globally bounded in absolute value. -/
lemma exists_abs_bound_partialD {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω φ) (i : Fin d) :
    ∃ M : ℝ, ∀ x, |partialD i φ x| ≤ M := by
  obtain ⟨C, hC⟩ := (h.continuous_partialD i).bounded_above_of_compact_support
    (h.hasCompactSupport_partialD i)
  exact ⟨C, fun x => by have := hC x; rwa [Real.norm_eq_abs] at this⟩

/-! ### Multiplier actions of a cutoff on `L²(Ω)` -/

/-- Multiplication by the cutoff `η` on `L²(Ω)`, as a continuous linear map. -/
def mulTest {Ω : Set (EuclideanSpace ℝ (Fin d))} {η : EuclideanSpace ℝ (Fin d) → ℝ}
    (h : IsTestFn Ω η) : L2D Ω →L[ℝ] L2D Ω :=
  mulCoeffL h.continuous.measurable
    (ae_of_all (volume.restrict Ω) (exists_abs_bound h).choose_spec)

/-- Multiplication by the partial `∂ᵢη` of the cutoff on `L²(Ω)`, continuous linear map. -/
def mulTestPartial {Ω : Set (EuclideanSpace ℝ (Fin d))} {η : EuclideanSpace ℝ (Fin d) → ℝ}
    (h : IsTestFn Ω η) (i : Fin d) : L2D Ω →L[ℝ] L2D Ω :=
  mulCoeffL (h.continuous_partialD i).measurable
    (ae_of_all (volume.restrict Ω) (exists_abs_bound_partialD h i).choose_spec)

/-- The a.e. representative of `mulTest`: `mulTest h g =ᵐ x ↦ η x · g x`. -/
lemma mulTest_coeFn {Ω : Set (EuclideanSpace ℝ (Fin d))} {η : EuclideanSpace ℝ (Fin d) → ℝ}
    (h : IsTestFn Ω η) (g : L2D Ω) :
    mulTest h g =ᵐ[volume.restrict Ω] fun x => η x * (g x : ℝ) :=
  mulCoeffL_coeFn _ _ g

/-- The a.e. representative of `mulTestPartial`: `mulTestPartial h i g =ᵐ x ↦ ∂ᵢη x · g x`. -/
lemma mulTestPartial_coeFn {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {η : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω η) (i : Fin d) (g : L2D Ω) :
    mulTestPartial h i g =ᵐ[volume.restrict Ω] fun x => partialD i η x * (g x : ℝ) :=
  mulCoeffL_coeFn _ _ g

/-! ### Cutoff-multiplication operator on the graph space -/

/-- The **cutoff-multiplication operator** `cutoffMul η : H1amb Ω →L H1amb Ω`, encoding the
Leibniz rule `∇(η u) = η ∇u + (∇η) u`: coordinate `0` multiplies by `η`, coordinate `i+1`
sends `U` to `η · U_{i+1} + (∂ᵢη) · U₀`. -/
def cutoffMul {Ω : Set (EuclideanSpace ℝ (Fin d))} {η : EuclideanSpace ℝ (Fin d) → ℝ}
    (h : IsTestFn Ω η) : H1amb Ω →L[ℝ] H1amb Ω :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (d + 1) => L2D Ω)).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.pi
        (Fin.cons ((mulTest h).comp (ContinuousLinearMap.proj 0))
          (fun i => (mulTest h).comp (ContinuousLinearMap.proj i.succ)
            + (mulTestPartial h i).comp (ContinuousLinearMap.proj 0)))).comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (d + 1) => L2D Ω)).toContinuousLinearMap)

/-- Coordinate `0` of `cutoffMul`: `(cutoffMul η U)₀ = η · U₀`. -/
lemma cutoffMul_apply_zero {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {η : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω η) (U : H1amb Ω) :
    (cutoffMul h U) 0 = mulTest h (U 0) := by
  simp only [cutoffMul, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, PiLp.coe_symm_continuousLinearEquiv,
    PiLp.coe_continuousLinearEquiv, PiLp.toLp_apply, ContinuousLinearMap.pi_apply,
    Fin.cons_zero, ContinuousLinearMap.proj_apply]

/-- Coordinate `i+1` of `cutoffMul`: `(cutoffMul η U)_{i+1} = η · U_{i+1} + (∂ᵢη) · U₀`. -/
lemma cutoffMul_apply_succ {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {η : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω η) (U : H1amb Ω) (i : Fin d) :
    (cutoffMul h U) i.succ = mulTest h (U i.succ) + mulTestPartial h i (U 0) := by
  simp only [cutoffMul, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, PiLp.coe_symm_continuousLinearEquiv,
    PiLp.coe_continuousLinearEquiv, PiLp.toLp_apply, ContinuousLinearMap.pi_apply,
    Fin.cons_succ, _root_.add_apply, ContinuousLinearMap.proj_apply]

/-! ### Leibniz product rule and stability of test functions under products -/

/-- The classical Leibniz rule for the `i`-th partial of a product:
`∂ᵢ(η φ) = η ∂ᵢφ + (∂ᵢη) φ`. -/
lemma partialD_mul {η φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hη : Differentiable ℝ η) (hφ : Differentiable ℝ φ) (i : Fin d) :
    partialD i (fun x => η x * φ x)
      = fun x => η x * partialD i φ x + partialD i η x * φ x := by
  funext x
  simp only [partialD]
  rw [fderiv_fun_mul (hη x) (hφ x)]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  ring

/-- The pointwise product of two test functions is a test function: smoothness is
`ContDiff.mul`, the support of the product sits inside `tsupport φ ⊆ Ω`, and compact
support is inherited from `φ`. -/
lemma isTestFn_mul {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {η φ : EuclideanSpace ℝ (Fin d) → ℝ} (hη : IsTestFn Ω η) (hφ : IsTestFn Ω φ) :
    IsTestFn Ω (fun x => η x * φ x) := by
  refine ⟨hη.1.mul hφ.1, ?_, ?_⟩
  · exact HasCompactSupport.mul_left (f' := φ) (f := η) hφ.2.1
  · exact (closure_mono (Function.support_mul_subset_right η φ)).trans hφ.2.2

/-! ### Cutoff multiplication sending a graph to the product graph -/

/-- **Keystone (graphs).** The cutoff-multiplication operator sends the graph of a test
function `φ` to the graph of the product `η φ`: `cutoffMul η (graph φ) = graph (η φ)`. This
is the Leibniz rule realised at the level of `L²` classes, and it is what lets `cutoffMul`
extend from test functions to `H₀¹(Ω)` by closure. -/
lemma cutoffMul_testGraph {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {η φ : EuclideanSpace ℝ (Fin d) → ℝ} (hη : IsTestFn Ω η) (hφ : IsTestFn Ω φ) :
    cutoffMul hη hφ.testGraph = (isTestFn_mul hη hφ).testGraph := by
  apply PiLp.ext
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · -- coordinate 0: `η · [φ] = [η φ]`
    rw [cutoffMul_apply_zero, IsTestFn.testGraph_zero, IsTestFn.testGraph_zero]
    apply Lp.ext
    filter_upwards [mulTest_coeFn hη hφ.testCls, hφ.mem_lp.coeFn_toLp,
      (isTestFn_mul hη hφ).mem_lp.coeFn_toLp] with x hx hφx hprod
    rw [hx, show (hφ.testCls x : ℝ) = φ x from hφx]
    exact hprod.symm
  · -- coordinate `i+1`: `η · [∂ᵢφ] + (∂ᵢη) · [φ] = [∂ᵢ(η φ)]`
    rw [cutoffMul_apply_succ, IsTestFn.testGraph_succ, IsTestFn.testGraph_zero,
      IsTestFn.testGraph_succ]
    apply Lp.ext
    filter_upwards [Lp.coeFn_add (mulTest hη (hφ.partialCls i))
        (mulTestPartial hη i hφ.testCls),
      mulTest_coeFn hη (hφ.partialCls i), mulTestPartial_coeFn hη i hφ.testCls,
      (hφ.memLp_partialD i).coeFn_toLp, hφ.mem_lp.coeFn_toLp,
      ((isTestFn_mul hη hφ).memLp_partialD i).coeFn_toLp] with
      x hadd hmt hmtp hpφ hφx hprodp
    rw [hadd, Pi.add_apply, hmt, hmtp]
    change η x * (hφ.partialCls i x : ℝ) + partialD i η x * (hφ.testCls x : ℝ)
      = ((isTestFn_mul hη hφ).partialCls i) x
    rw [show (hφ.partialCls i x : ℝ) = partialD i φ x from hpφ,
      show (hφ.testCls x : ℝ) = φ x from hφx,
      show ((isTestFn_mul hη hφ).partialCls i) x = partialD i (fun y => η y * φ y) x from hprodp,
      congrFun (partialD_mul (hη.1.differentiable (by simp))
        (hφ.1.differentiable (by simp)) i) x]

/-! ### Preservation of `H₀¹(Ω)` under cutoff multiplication -/

/-- **Keystone (membership).** The cutoff-multiplication operator maps `H₀¹(Ω)` into
itself. Since `cutoffMul η` is continuous and sends every test-function graph into
`H₀¹(Ω)` (by [`cutoffMul_testGraph`]), it maps the closure `H₀¹(Ω)` into the closed set
`H₀¹(Ω)`. -/
lemma cutoffMul_mem_H01 {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {η : EuclideanSpace ℝ (Fin d) → ℝ} (hη : IsTestFn Ω η) {U : H1amb Ω}
    (hU : U ∈ H01 Ω) : cutoffMul hη U ∈ H01 Ω := by
  have hle : (Submodule.span ℝ (testGraphSet Ω)).topologicalClosure
      ≤ Submodule.comap (cutoffMul hη).toLinearMap (H01 Ω) := by
    apply Submodule.topologicalClosure_minimal
    · rw [Submodule.span_le]
      rintro _ ⟨φ, hφ, rfl⟩
      change cutoffMul hη hφ.testGraph ∈ H01 Ω
      rw [cutoffMul_testGraph hη hφ]
      exact (Submodule.le_topologicalClosure _)
        (Submodule.subset_span ⟨_, isTestFn_mul hη hφ, rfl⟩)
    · exact IsClosed.preimage (cutoffMul hη).continuous
        (Submodule.isClosed_topologicalClosure _)
  exact Submodule.mem_comap.mp (hle hU)

/-! ### Weighted energy lower bound from ellipticity -/

/-- **Ellipticity energy bound for an arbitrary `L²` gradient family.** The lower bound of
[`EllipticCoeff.bilin_self_ge`] uses only the `L²` classes, not the weak-gradient
relation, so it holds for any family `g : Fin d → L²(Ω)`:
`λ ∑ᵢ ‖gᵢ‖² ≤ ∑ᵢⱼ ⟪aᵢⱼ gᵢ, gⱼ⟫`. Applied to `gᵢ = ζ · ∂ᵢu` this is the cutoff-weighted
energy lower bound `λ ∫_Ω ζ² |∇u|² ≤ ∫_Ω ζ² ∑ᵢⱼ aᵢⱼ ∂ᵢu ∂ⱼu` driving the Caccioppoli
estimate (Evans, *PDE* 2nd ed., §6.3.1). -/
lemma energy_ge (A : EllipticCoeff d) {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (g : Fin d → L2D Ω) :
    A.lam * ∑ i : Fin d, ‖g i‖ ^ 2
      ≤ ∑ i : Fin d, ∑ j : Fin d, ⟪A.actL i j (g i), g j⟫ := by
  have hPint : Integrable (fun x => A.lam * ∑ i : Fin d, (g i x : ℝ) ^ 2)
      (volume.restrict Ω) :=
    (integrable_finsetSum _ (fun i _ => integrable_sq (g i))).const_mul A.lam
  have hpoint : (fun x => A.lam * ∑ i : Fin d, (g i x : ℝ) ^ 2)
      ≤ᵐ[volume.restrict Ω] fun x => ∑ i : Fin d, ∑ j : Fin d,
        A.a x i j * (g i x : ℝ) * (g j x : ℝ) :=
    (ae_restrict_of_ae A.elliptic).mono (fun x hx => hx (fun i => g i x))
  have hlamS : ∫ x in Ω, A.lam * ∑ i : Fin d, (g i x : ℝ) ^ 2
      = A.lam * ∑ i : Fin d, ‖g i‖ ^ 2 := by
    rw [integral_const_mul, integral_finsetSum _ (fun i _ => integrable_sq (g i))]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => sq_integral_eq_norm_sq (g i))
  have hRHS : ∑ i : Fin d, ∑ j : Fin d, ⟪A.actL i j (g i), g j⟫
      = ∫ x in Ω, ∑ i : Fin d, ∑ j : Fin d,
        A.a x i j * (g i x : ℝ) * (g j x : ℝ) := by
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
      (fun j _ => A.integrable_triple i j _ _))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [integral_finsetSum _ (fun j _ => A.integrable_triple i j _ _)]
    exact Finset.sum_congr rfl (fun j _ => A.inner_actL_eq i j _ _)
  calc A.lam * ∑ i : Fin d, ‖g i‖ ^ 2
      = ∫ x in Ω, A.lam * ∑ i : Fin d, (g i x : ℝ) ^ 2 := hlamS.symm
    _ ≤ ∫ x in Ω, ∑ i : Fin d, ∑ j : Fin d,
          A.a x i j * (g i x : ℝ) * (g j x : ℝ) :=
        integral_mono_ae hPint (integrable_finsetSum _ (fun i _ =>
          integrable_finsetSum _ (fun j _ => A.integrable_triple i j _ _))) hpoint
    _ = ∑ i : Fin d, ∑ j : Fin d, ⟪A.actL i j (g i), g j⟫ := hRHS.symm

/-! ### Operator-norm bounds and regrouping identities for the cutoff -/

/-- Operator-norm bound for the cutoff multiplier: `‖η · g‖ ≤ ‖η‖∞ · ‖g‖`. -/
lemma norm_mulTest_le {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {η : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω η) (g : L2D Ω) :
    ‖mulTest h g‖ ≤ (exists_abs_bound h).choose * ‖g‖ :=
  norm_mulCoeffL_le _ _ g

/-- Operator-norm bound for the partial-cutoff multiplier: `‖∂ᵢη · g‖ ≤ ‖∂ᵢη‖∞ · ‖g‖`. -/
lemma norm_mulTestPartial_le {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {η : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω η) (i : Fin d) (g : L2D Ω) :
    ‖mulTestPartial h i g‖ ≤ (exists_abs_bound_partialD h i).choose * ‖g‖ :=
  norm_mulCoeffL_le _ _ g

/-- Regrouping one `ζ` factor across the coefficient action, principal part:
`⟪aᵢⱼ (ζ p), ζ q⟫ = ⟪aᵢⱼ p, ζ² q⟫`. -/
lemma actL_mulTest_regroup (A : EllipticCoeff d)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} {ζ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hζ : IsTestFn Ω ζ) (i j : Fin d) (p q : L2D Ω) :
    ⟪A.actL i j (mulTest hζ p), mulTest hζ q⟫
      = ⟪A.actL i j p, mulTest (isTestFn_mul hζ hζ) q⟫ := by
  rw [A.inner_actL_eq, A.inner_actL_eq]
  refine integral_congr_ae ?_
  filter_upwards [mulTest_coeFn hζ p, mulTest_coeFn hζ q,
    mulTest_coeFn (isTestFn_mul hζ hζ) q] with x hp hq hpq
  rw [hp, hq, hpq]
  ring

/-- Regrouping the cross term: moving one `ζ` off `∂ⱼ(ζ²) = 2 ζ ∂ⱼζ` onto `p`,
`⟪aᵢⱼ p, ∂ⱼ(ζ²) q⟫ = 2 ⟪aᵢⱼ (ζ p), ∂ⱼζ q⟫`. -/
lemma actL_cross_regroup (A : EllipticCoeff d)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} {ζ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hζ : IsTestFn Ω ζ) (i j : Fin d) (p q : L2D Ω) :
    ⟪A.actL i j p, mulTestPartial (isTestFn_mul hζ hζ) j q⟫
      = 2 * ⟪A.actL i j (mulTest hζ p), mulTestPartial hζ j q⟫ := by
  rw [A.inner_actL_eq, A.inner_actL_eq, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [mulTestPartial_coeFn (isTestFn_mul hζ hζ) j q,
    mulTest_coeFn hζ p, mulTestPartial_coeFn hζ j q] with x hpart hp hq
  rw [hpart, hp, hq,
    congrFun (partialD_mul (hζ.1.differentiable (by simp))
      (hζ.1.differentiable (by simp)) j) x]
  ring

/-- Regrouping the transport term: `⟪bᵢ p, ζ² q⟫ = ⟪bᵢ (ζ p), ζ q⟫`. -/
private lemma bAct_transport_regroup (Op : FullEllipticOp d)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} {ζ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hζ : IsTestFn Ω ζ) (i : Fin d) (p q : L2D Ω) :
    ⟪Op.bAct i p, mulTest (isTestFn_mul hζ hζ) q⟫
      = ⟪Op.bAct i (mulTest hζ p), mulTest hζ q⟫ := by
  simp only [FullEllipticOp.bAct]
  rw [inner_mulCoeffL_eq, inner_mulCoeffL_eq]
  refine integral_congr_ae ?_
  filter_upwards [mulTest_coeFn (isTestFn_mul hζ hζ) q, mulTest_coeFn hζ p,
    mulTest_coeFn hζ q] with x hq2 hp hq
  rw [hq2, hp, hq]
  ring

/-! ### Interior energy (Caccioppoli) estimate -/

/-- Per-coordinate absorption of the principal cross term and transport term. -/
lemma caccioppoli_cross_transport_bound : ∀ {d : ℕ} (Op : FullEllipticOp d) {Ω : Set
  (EuclideanSpace ℝ (Fin d))}
  {ζ : EuclideanSpace ℝ (Fin d) → ℝ} (hζ : IsTestFn Ω ζ),
  let A := Op.toEllipticCoeff;
  let Z := (exists_abs_bound hζ).choose;
  let SW := ∑ j, (exists_abs_bound_partialD hζ j).choose;
  ∀ (_ : SW = ∑ j, (exists_abs_bound_partialD hζ j).choose),
    let β := 2 * A.Λ * SW + Op.Bsup * Z;
    ∀ (_ : β = 2 * A.Λ * SW + Op.Bsup * Z) (U : H1amb Ω) (i : Fin d),
      0 ≤
        A.lam / 2 * ‖(mulTest hζ) (U.ofLp i.succ)‖ ^ 2 + β ^ 2 / (2 * A.lam) * ‖U.ofLp 0‖ ^ 2 +
          (∑ j, ⟪(A.actL i j) (U.ofLp i.succ), (mulTestPartial (isTestFn_mul hζ hζ) j) (U.ofLp 0)⟫ +
            ⟪(Op.bAct i) (U.ofLp i.succ), (mulTest (isTestFn_mul hζ hζ)) (U.ofLp 0)⟫) := by
  classical
  intro d Op Ω ζ hζ A Z SW hSW β hβ U i
  have hcross_ij : ∀ j : Fin d,
      |⟪A.actL i j (U i.succ),
          mulTestPartial (isTestFn_mul hζ hζ) j (U 0)⟫|
      ≤ 2 * A.Λ * ‖mulTest hζ (U i.succ)‖
          * (exists_abs_bound_partialD hζ j).choose * ‖U 0‖ := by
    intro j
    rw [actL_cross_regroup A hζ i j (U i.succ) (U 0),
      abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hcs : |⟪A.actL i j (mulTest hζ (U i.succ)),
          mulTestPartial hζ j (U 0)⟫|
        ≤ A.Λ * ‖mulTest hζ (U i.succ)‖
            * ((exists_abs_bound_partialD hζ j).choose * ‖U 0‖) :=
      calc |⟪A.actL i j (mulTest hζ (U i.succ)),
            mulTestPartial hζ j (U 0)⟫|
          ≤ ‖A.actL i j (mulTest hζ (U i.succ))‖
              * ‖mulTestPartial hζ j (U 0)‖ := abs_real_inner_le_norm _ _
        _ ≤ (A.Λ * ‖mulTest hζ (U i.succ)‖)
              * ((exists_abs_bound_partialD hζ j).choose * ‖U 0‖) :=
            mul_le_mul (A.norm_actL_le i j _) (norm_mulTestPartial_le hζ j _)
              (norm_nonneg _) (mul_nonneg A.Λ_nonneg (norm_nonneg _))
        _ = A.Λ * ‖mulTest hζ (U i.succ)‖
              * ((exists_abs_bound_partialD hζ j).choose * ‖U 0‖) := by ring
    calc 2 * |⟪A.actL i j (mulTest hζ (U i.succ)),
          mulTestPartial hζ j (U 0)⟫|
        ≤ 2 * (A.Λ * ‖mulTest hζ (U i.succ)‖
            * ((exists_abs_bound_partialD hζ j).choose * ‖U 0‖)) := by
          linarith [hcs]
      _ = 2 * A.Λ * ‖mulTest hζ (U i.succ)‖
            * (exists_abs_bound_partialD hζ j).choose * ‖U 0‖ := by ring
  have hcross : |∑ j : Fin d,
        ⟪A.actL i j (U i.succ),
          mulTestPartial (isTestFn_mul hζ hζ) j (U 0)⟫|
      ≤ 2 * A.Λ * SW * ‖mulTest hζ (U i.succ)‖ * ‖U 0‖ := by
    calc |∑ j : Fin d, ⟪A.actL i j (U i.succ),
          mulTestPartial (isTestFn_mul hζ hζ) j (U 0)⟫|
        ≤ ∑ j : Fin d, |⟪A.actL i j (U i.succ),
            mulTestPartial (isTestFn_mul hζ hζ) j (U 0)⟫| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin d, 2 * A.Λ * ‖mulTest hζ (U i.succ)‖
            * (exists_abs_bound_partialD hζ j).choose * ‖U 0‖ :=
          Finset.sum_le_sum (fun j _ => hcross_ij j)
      _ = 2 * A.Λ * ‖mulTest hζ (U i.succ)‖ * ‖U 0‖
            * ∑ j : Fin d, (exists_abs_bound_partialD hζ j).choose := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
      _ = 2 * A.Λ * SW * ‖mulTest hζ (U i.succ)‖ * ‖U 0‖ := by
          rw [hSW]; ring
  have htrans : |⟪Op.bAct i (U i.succ),
        mulTest (isTestFn_mul hζ hζ) (U 0)⟫|
      ≤ Op.Bsup * Z * ‖mulTest hζ (U i.succ)‖ * ‖U 0‖ := by
    rw [bAct_transport_regroup Op hζ i (U i.succ) (U 0)]
    calc |⟪Op.bAct i (mulTest hζ (U i.succ)),
          mulTest hζ (U 0)⟫|
        ≤ ‖Op.bAct i (mulTest hζ (U i.succ))‖
            * ‖mulTest hζ (U 0)‖ := abs_real_inner_le_norm _ _
      _ ≤ (Op.Bsup * ‖mulTest hζ (U i.succ)‖) * (Z * ‖U 0‖) :=
          mul_le_mul (Op.norm_bAct_le i _) (norm_mulTest_le hζ _) (norm_nonneg _)
            (mul_nonneg Op.Bsup_nonneg (norm_nonneg _))
      _ = Op.Bsup * Z * ‖mulTest hζ (U i.succ)‖ * ‖U 0‖ := by ring
  have hbridge : β * ‖mulTest hζ (U i.succ)‖ * ‖U 0‖
      = 2 * A.Λ * SW * ‖mulTest hζ (U i.succ)‖ * ‖U 0‖
        + Op.Bsup * Z * ‖mulTest hζ (U i.succ)‖ * ‖U 0‖ := by
    rw [hβ]; ring
  have hyoung := young_peterPaul (lam := A.lam) (B := β)
    (x := ‖mulTest hζ (U i.succ)‖) (y := ‖U 0‖) A.lam_pos
  linarith [hcross, htrans, hbridge, hyoung,
    neg_le_abs ((∑ j : Fin d, ⟪A.actL i j (U i.succ),
        mulTestPartial (isTestFn_mul hζ hζ) j (U 0)⟫)
      + ⟪Op.bAct i (U i.succ),
          mulTest (isTestFn_mul hζ hζ) (U 0)⟫),
    abs_add_le (∑ j : Fin d, ⟪A.actL i j (U i.succ),
        mulTestPartial (isTestFn_mul hζ hζ) j (U 0)⟫)
      (⟪Op.bAct i (U i.succ),
          mulTest (isTestFn_mul hζ hζ) (U 0)⟫)]

/-- **Interior energy (Caccioppoli) estimate.** For a weak solution `u ∈ H₀¹(Ω)` of
`L u = f` and a cutoff `ζ` (a test function), the cutoff-weighted gradient energy
`(λ/2) ∫_Ω ζ² |∇u|²` is bounded by `C · (‖f‖²_{L²} + ‖u₀‖²_{L²})`. The constant is quantified
before the solution and the datum, so it depends only on `λ`, `Λ`, `‖b‖∞`, `‖c‖∞`, `‖ζ‖∞`,
and `‖∇ζ‖∞`. Testing the weak formulation with
`ζ² u` (admissible by [`cutoffMul_mem_H01`]), the ellipticity lower bound [`energy_ge`]
controls the principal part from below, and Cauchy-Schwarz together with the Peter-Paul
(Young) inequality absorbs the cross, transport, zeroth-order, and right-hand terms into a
`(λ/2) ∫_Ω ζ² |∇u|²` share. Since `ζ ≡ 1` on an interior set `V`, this gives
`‖∇u‖_{L²(V)} ≤ C' (‖f‖ + ‖u₀‖)`. See Gilbarg-Trudinger, *Elliptic PDE of Second Order*,
Theorem 8.8, and Evans, *Partial Differential Equations* (2nd ed.), §6.3.1.

Guo, *Partial Differential Equations* (JHU AS.110.631-632), Lemma X.3.5 also has the name
Caccioppoli, and is a different statement: it takes a non-negative subsolution `Lv ≥ 0` of the
principal part alone and bounds `∫ |∇(φv)|²` by `‖∇φ‖²_∞ ∫ v²`, with no datum on the right. This
statement takes a solution of `Lu = f` for the full operator, has `f` on the right, and imposes
no sign condition, so neither implies the other. Gilbarg and Trudinger Theorem 8.8 remains the
match, cited here rather than transcribed. -/
theorem caccioppoli (Op : FullEllipticOp d) {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {ζ : EuclideanSpace ℝ (Fin d) → ℝ} (hζ : IsTestFn Ω ζ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : H01 Ω) (f : L2D Ω),
      (∀ v : H01 Ω, Op.fullBilin Ω u v
        = ∫ x in Ω, (f x : ℝ) * ((v : H1amb Ω) 0 x : ℝ)) →
      Op.lam / 2 * ∑ i : Fin d, ‖mulTest hζ ((u : H1amb Ω) i.succ)‖ ^ 2
        ≤ C * (‖f‖ ^ 2 + ‖(u : H1amb Ω) 0‖ ^ 2) := by
  classical
  set A := Op.toEllipticCoeff with hA
  set Z : ℝ := (exists_abs_bound hζ).choose with hZ
  set Z2 : ℝ := (exists_abs_bound (isTestFn_mul hζ hζ)).choose with hZ2
  set SW : ℝ := ∑ j : Fin d, (exists_abs_bound_partialD hζ j).choose with hSW
  set β : ℝ := 2 * A.Λ * SW + Op.Bsup * Z with hβ
  have hZ2n : (0 : ℝ) ≤ Z2 :=
    le_trans (abs_nonneg _) ((exists_abs_bound (isTestFn_mul hζ hζ)).choose_spec 0)
  -- The constant, fixed before the solution and the datum.
  have hβn : (0 : ℝ) ≤ (d : ℝ) * β ^ 2 / (2 * A.lam) :=
    div_nonneg (by positivity) (by have := A.lam_pos; linarith)
  have hCu : (0 : ℝ) ≤ Z2 ^ 2 / 2 + (d : ℝ) * β ^ 2 / (2 * A.lam) + Op.Csup * Z2 :=
    by linarith [hβn, mul_nonneg Op.Csup_nonneg hZ2n, sq_nonneg Z2]
  refine ⟨1 / 2 + Z2 ^ 2 / 2 + (d : ℝ) * β ^ 2 / (2 * A.lam) + Op.Csup * Z2,
    by linarith, ?_⟩
  intro u f hu
  set v : H01 Ω := ⟨cutoffMul (isTestFn_mul hζ hζ) (u : H1amb Ω),
    cutoffMul_mem_H01 (isTestFn_mul hζ hζ) u.2⟩ with hvdef
  set E : ℝ := ∑ i : Fin d, ‖mulTest hζ ((u : H1amb Ω) i.succ)‖ ^ 2 with hE
  -- Coordinate values of the test element `ζ² u`.
  have hv0 : (v : H1amb Ω) 0 = mulTest (isTestFn_mul hζ hζ) ((u : H1amb Ω) 0) := by
    change cutoffMul (isTestFn_mul hζ hζ) (u : H1amb Ω) 0 = _
    rw [cutoffMul_apply_zero]
  have hv0succ : ∀ j : Fin d, (v : H1amb Ω) j.succ
      = mulTest (isTestFn_mul hζ hζ) ((u : H1amb Ω) j.succ)
        + mulTestPartial (isTestFn_mul hζ hζ) j ((u : H1amb Ω) 0) := by
    intro j
    change cutoffMul (isTestFn_mul hζ hζ) (u : H1amb Ω) j.succ = _
    rw [cutoffMul_apply_succ]
  -- Principal expansion of the bilinear form on `ζ² u`.
  have hbil : A.bilin Ω u v
      = (∑ i : Fin d, ∑ j : Fin d,
          ⟪A.actL i j ((u : H1amb Ω) i.succ),
            mulTest (isTestFn_mul hζ hζ) ((u : H1amb Ω) j.succ)⟫)
        + ∑ i : Fin d, ∑ j : Fin d,
          ⟪A.actL i j ((u : H1amb Ω) i.succ),
            mulTestPartial (isTestFn_mul hζ hζ) j ((u : H1amb Ω) 0)⟫ := by
    rw [EllipticCoeff.bilin_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hv0succ j, inner_add_right]
  -- Ellipticity lower bound for the principal part after regrouping one `ζ`.
  have hen : A.lam * E
      ≤ ∑ i : Fin d, ∑ j : Fin d,
          ⟪A.actL i j ((u : H1amb Ω) i.succ),
            mulTest (isTestFn_mul hζ hζ) ((u : H1amb Ω) j.succ)⟫ := by
    calc A.lam * E
        = A.lam * ∑ i : Fin d, ‖mulTest hζ ((u : H1amb Ω) i.succ)‖ ^ 2 := by rw [hE]
      _ ≤ ∑ i : Fin d, ∑ j : Fin d,
            ⟪A.actL i j (mulTest hζ ((u : H1amb Ω) i.succ)),
              mulTest hζ ((u : H1amb Ω) j.succ)⟫ := by
          have h := energy_ge A (fun i => mulTest hζ ((u : H1amb Ω) i.succ))
          simpa using h
      _ = ∑ i : Fin d, ∑ j : Fin d,
            ⟪A.actL i j ((u : H1amb Ω) i.succ),
              mulTest (isTestFn_mul hζ hζ) ((u : H1amb Ω) j.succ)⟫ :=
          Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl
            (fun j _ => actL_mulTest_regroup A hζ i j _ _))
  -- Weak equation: the principal part equals data minus the lower-order form.
  have hweak : A.bilin Ω u v
      = (∫ x in Ω, (f x : ℝ) * ((v : H1amb Ω) 0 x : ℝ))
        - ((∑ i : Fin d, ⟪Op.bAct i ((u : H1amb Ω) i.succ),
              mulTest (isTestFn_mul hζ hζ) ((u : H1amb Ω) 0)⟫)
          + ⟪Op.cAct ((u : H1amb Ω) 0),
              mulTest (isTestFn_mul hζ hζ) ((u : H1amb Ω) 0)⟫) := by
    have hfb := Op.fullBilin_apply Ω u v
    rw [hu v] at hfb
    have hlow : Op.lowerBilin Ω u v
        = (∑ i : Fin d, ⟪Op.bAct i ((u : H1amb Ω) i.succ),
              mulTest (isTestFn_mul hζ hζ) ((u : H1amb Ω) 0)⟫)
          + ⟪Op.cAct ((u : H1amb Ω) 0),
              mulTest (isTestFn_mul hζ hζ) ((u : H1amb Ω) 0)⟫ := by
      rw [Op.lowerBilin_apply]
      simp only [hv0]
    linarith [hfb, hlow]
  -- Right-hand side as an inner product, bounded by Cauchy-Schwarz and Young.
  have hRHSeq : (∫ x in Ω, (f x : ℝ) * ((v : H1amb Ω) 0 x : ℝ))
      = ⟪f, mulTest (isTestFn_mul hζ hζ) ((u : H1amb Ω) 0)⟫ := by
    rw [hv0, L2.inner_def]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [Real.inner_apply]
  have hRHSf : (∫ x in Ω, (f x : ℝ) * ((v : H1amb Ω) 0 x : ℝ))
      ≤ 1 / 2 * ‖f‖ ^ 2 + Z2 ^ 2 / 2 * ‖(u : H1amb Ω) 0‖ ^ 2 := by
    rw [hRHSeq]
    calc ⟪f, mulTest (isTestFn_mul hζ hζ) ((u : H1amb Ω) 0)⟫
        ≤ ‖f‖ * ‖mulTest (isTestFn_mul hζ hζ) ((u : H1amb Ω) 0)‖ := real_inner_le_norm _ _
      _ ≤ ‖f‖ * (Z2 * ‖(u : H1amb Ω) 0‖) :=
          mul_le_mul_of_nonneg_left (norm_mulTest_le (isTestFn_mul hζ hζ) _) (norm_nonneg _)
      _ = Z2 * ‖f‖ * ‖(u : H1amb Ω) 0‖ := by ring
      _ ≤ 1 / 2 * ‖f‖ ^ 2 + Z2 ^ 2 / 2 * ‖(u : H1amb Ω) 0‖ ^ 2 := by
          have hy := young_peterPaul (lam := 1) (B := Z2) (x := ‖f‖)
            (y := ‖(u : H1amb Ω) 0‖) one_pos
          have h2l : (2 : ℝ) * 1 = 2 := by norm_num
          rw [h2l] at hy
          linarith [hy]
  -- Zeroth-order term bounded (no absorption needed).
  have hZthbound :
      -(⟪Op.cAct ((u : H1amb Ω) 0),
          mulTest (isTestFn_mul hζ hζ) ((u : H1amb Ω) 0)⟫)
        ≤ Op.Csup * Z2 * ‖(u : H1amb Ω) 0‖ ^ 2 :=
    calc -(⟪Op.cAct ((u : H1amb Ω) 0),
            mulTest (isTestFn_mul hζ hζ) ((u : H1amb Ω) 0)⟫)
        ≤ |⟪Op.cAct ((u : H1amb Ω) 0),
            mulTest (isTestFn_mul hζ hζ) ((u : H1amb Ω) 0)⟫| := neg_le_abs _
      _ ≤ ‖Op.cAct ((u : H1amb Ω) 0)‖
            * ‖mulTest (isTestFn_mul hζ hζ) ((u : H1amb Ω) 0)‖ := abs_real_inner_le_norm _ _
      _ ≤ (Op.Csup * ‖(u : H1amb Ω) 0‖) * (Z2 * ‖(u : H1amb Ω) 0‖) :=
          mul_le_mul (Op.norm_cAct_le _) (norm_mulTest_le (isTestFn_mul hζ hζ) _)
            (norm_nonneg _) (mul_nonneg Op.Csup_nonneg (norm_nonneg _))
      _ = Op.Csup * Z2 * ‖(u : H1amb Ω) 0‖ ^ 2 := by ring
  -- Per-index absorption bound for the cross and transport terms.
  have hbnd : ∀ i : Fin d, (0 : ℝ) ≤
      (A.lam / 2 * ‖mulTest hζ ((u : H1amb Ω) i.succ)‖ ^ 2
        + β ^ 2 / (2 * A.lam) * ‖(u : H1amb Ω) 0‖ ^ 2)
      + ((∑ j : Fin d,
          ⟪A.actL i j ((u : H1amb Ω) i.succ),
            mulTestPartial (isTestFn_mul hζ hζ) j ((u : H1amb Ω) 0)⟫)
        + ⟪Op.bAct i ((u : H1amb Ω) i.succ),
            mulTest (isTestFn_mul hζ hζ) ((u : H1amb Ω) 0)⟫) := by
    exact caccioppoli_cross_transport_bound Op hζ hSW hβ (u : H1amb Ω)
  -- Sum the per-index bound to absorb the cross and transport totals.
  have hTsum : (0 : ℝ)
      ≤ (A.lam / 2 * E + (d : ℝ) * β ^ 2 / (2 * A.lam) * ‖(u : H1amb Ω) 0‖ ^ 2)
        + ((∑ i : Fin d, ∑ j : Fin d,
            ⟪A.actL i j ((u : H1amb Ω) i.succ),
              mulTestPartial (isTestFn_mul hζ hζ) j ((u : H1amb Ω) 0)⟫)
          + ∑ i : Fin d, ⟪Op.bAct i ((u : H1amb Ω) i.succ),
              mulTest (isTestFn_mul hζ hζ) ((u : H1amb Ω) 0)⟫) := by
    have hsum := Finset.sum_le_sum
      (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) => hbnd i)
    rw [Finset.sum_const_zero] at hsum
    calc (0 : ℝ)
        ≤ ∑ i : Fin d, ((A.lam / 2 * ‖mulTest hζ ((u : H1amb Ω) i.succ)‖ ^ 2
            + β ^ 2 / (2 * A.lam) * ‖(u : H1amb Ω) 0‖ ^ 2)
          + ((∑ j : Fin d,
              ⟪A.actL i j ((u : H1amb Ω) i.succ),
                mulTestPartial (isTestFn_mul hζ hζ) j ((u : H1amb Ω) 0)⟫)
            + ⟪Op.bAct i ((u : H1amb Ω) i.succ),
                mulTest (isTestFn_mul hζ hζ) ((u : H1amb Ω) 0)⟫)) := hsum
      _ = (A.lam / 2 * E + (d : ℝ) * β ^ 2 / (2 * A.lam) * ‖(u : H1amb Ω) 0‖ ^ 2)
          + ((∑ i : Fin d, ∑ j : Fin d,
              ⟪A.actL i j ((u : H1amb Ω) i.succ),
                mulTestPartial (isTestFn_mul hζ hζ) j ((u : H1amb Ω) 0)⟫)
            + ∑ i : Fin d, ⟪Op.bAct i ((u : H1amb Ω) i.succ),
                mulTest (isTestFn_mul hζ hζ) ((u : H1amb Ω) 0)⟫) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
            ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, ← hE]
          ring
  -- Assemble: the absorbed energy leaves the desired estimate.
  have hrel : A.lam * E = 2 * (A.lam / 2 * E) := by ring
  have hfin : A.lam / 2 * E
      ≤ 1 / 2 * ‖f‖ ^ 2 + Z2 ^ 2 / 2 * ‖(u : H1amb Ω) 0‖ ^ 2
        + (d : ℝ) * β ^ 2 / (2 * A.lam) * ‖(u : H1amb Ω) 0‖ ^ 2
        + Op.Csup * Z2 * ‖(u : H1amb Ω) 0‖ ^ 2 := by
    linarith [hen, hbil, hweak, hRHSf, hTsum, hZthbound, hrel]
  nlinarith [hfin, sq_nonneg ‖(u : H1amb Ω) 0‖, sq_nonneg ‖f‖,
    mul_nonneg hCu (sq_nonneg ‖f‖)]

end EllipticPdes.Regularity
