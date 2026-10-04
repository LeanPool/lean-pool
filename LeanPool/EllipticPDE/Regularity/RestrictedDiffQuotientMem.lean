/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Regularity.RestrictedDiffQuotient


/-!
# Admissibility of the cutoff of an interior difference quotient

The interior second-derivative estimate (Evans, *Partial Differential Equations* (2nd ed.),
§6.3.1; Gilbarg-Trudinger, *Elliptic PDE of Second Order*, Theorem 8.8) tests the weak
formulation with `v_h = -Dₖ^{-h}(ζ²·Dₖ^h u)`. For this test element to be a legal test
vector we must know that the cutoff of the interior difference quotient of an `H₀¹` element
is again in `H₀¹`.

The composite `cutoffMul ζ ∘ diffQuotG k h` is a **continuous** linear map and `H₀¹(Ω)` is
**closed**, so membership need only be checked on the spanning set `testGraphSet Ω`. On a
test graph `testGraph φ` (`φ ∈ C_c^∞(Ω)`) the diagram collapses: `diffQuotG k h` acts
coordinatewise as `diffQuotD k h` on `φ`'s function/gradient classes; because `φ` is a
smooth function that vanishes off its support in `Ω`, its extension by zero *is*
`φ`, so the interior difference quotient equals the whole-space one, and multiplying
by `ζ` returns the graph of `ζ · Dₖ^h φ`, where `Dₖ^h φ (x) = (φ(x + h eₖ) - φ(x))/h`.
Since `ζ` localises the support, `ζ · Dₖ^h φ` is a test function **for every** `φ`, so its
graph lies in the span, hence in `H₀¹(Ω)`. This mirrors `cutoffMul_mem_H01` exactly.

## Main results

* `mulTest_diffQuotD_eq_of_small`: multiplying by the cutoff makes the interior
  difference quotient agree with the whole-space difference quotient.
* `cutoffMul_diffQuotG_mem_H01`: the cutoff of the interior difference quotient of an
  `H₀¹` element is again in `H₀¹` (the crux admissibility).
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
  {ζ φ : EuclideanSpace ℝ (Fin d) → ℝ}

/-! ### Chop-invisibility on the cutoff -/

/-- **Chop-invisibility.** Multiplying by the cutoff `ζ` kills the difference between the
interior difference quotient `diffQuotD` and the whole-space difference quotient
`diffQuot` of the extension: the two differ only through `restrictL2`'s replacement of the
extension's value by the class value on `Ω`, and on `Ω` these agree a.e. (Evans, *Partial
Differential Equations* (2nd ed.), §6.3.1). -/
theorem mulTest_diffQuotD_eq_of_small (hζ : IsTestFn Ω ζ) (k : Fin d) {h : ℝ}
    (hΩm : MeasurableSet Ω)
    (_hsmall : h ≠ 0 ∧ ∀ x ∈ tsupport ζ, x + hshift k h ∈ Ω) (g : L2D Ω) :
    mulTest hζ (diffQuotD k h hΩm g)
      = mulTest hζ (restrictL2 (diffQuot k h (extendL2 hΩm g))) := by
  apply Lp.ext
  filter_upwards [mulTest_coeFn hζ (diffQuotD k h hΩm g),
      mulTest_coeFn hζ (restrictL2 (diffQuot k h (extendL2 hΩm g))),
      coeFn_diffQuotD k h hΩm g,
      coeFn_restrictL2 (diffQuot k h (extendL2 hΩm g)),
      ae_restrict_of_ae (coeFn_diffQuot k h (extendL2 hΩm g)),
      ae_restrict_of_ae (coeFn_extendL2 hΩm g), ae_restrict_mem hΩm]
    with x hlhs hrhs hdqd hrestr hdq hext hmem
  rw [hlhs, hrhs, hdqd, hrestr, hdq, hext, Set.indicator_of_mem hmem]

/-! ### Smoothness and support of `ζ · Dₖ^h φ` -/

/-- The pointwise difference quotient `Dₖ^h φ (x) = (φ(x + h eₖ) - φ(x))/h` of a smooth
function is smooth: a translation, a subtraction, and a division by a constant. -/
private lemma contDiff_diffQuotFn (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (k : Fin d) (h : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => (φ (x + hshift k h) - φ x) / h) :=
  ((hφ.comp (contDiff_id.add contDiff_const)).sub hφ).div_const h

/-- **Cutoff of a difference quotient as a test function.** For a cutoff `ζ` (a test
function) and a smooth `φ` (a test function), `ζ · Dₖ^h φ` is smooth (`ContDiff.mul`),
compactly supported (inherited from `ζ`), and supported inside `tsupport ζ ⊆ Ω`; the cutoff
`ζ` localises the support of the difference quotient uniformly in `φ`. -/
private lemma isTestFn_cutoff_diffQuotFn (hζ : IsTestFn Ω ζ) (hφ : IsTestFn Ω φ)
    (k : Fin d) (h : ℝ) :
    IsTestFn Ω (fun x => ζ x * ((φ (x + hshift k h) - φ x) / h)) := by
  refine ⟨hζ.1.mul (contDiff_diffQuotFn hφ.1 k h), ?_, ?_⟩
  · exact HasCompactSupport.mul_right hζ.2.1
  · exact (closure_mono (Function.support_mul_subset_left _ _)).trans hζ.2.2

/-- **Commutation of the difference quotient with the partial derivative.**
`∂ᵢ(Dₖ^h φ) = Dₖ^h(∂ᵢφ)`: the shift map has derivative the identity, so the shift and the
derivative commute, and dividing by `h` scales the derivative. -/
private lemma partialD_diffQuotFn (hφ : Differentiable ℝ φ) (i k : Fin d) (h : ℝ) :
    partialD i (fun x => (φ (x + hshift k h) - φ x) / h)
      = fun x => (partialD i φ (x + hshift k h) - partialD i φ x) / h := by
  funext x
  have hc : HasFDerivAt (fun y => φ (y + hshift k h)) (fderiv ℝ φ (x + hshift k h)) x := by
    simpa [Function.comp_def, id_eq, ContinuousLinearMap.comp_id] using
      (hφ (x + hshift k h)).hasFDerivAt.comp x ((hasFDerivAt_id x).add_const (hshift k h))
  have hsub := hc.sub (hφ x).hasFDerivAt
  have hval : HasFDerivAt (fun x => (φ (x + hshift k h) - φ x) / h)
      ((h⁻¹ : ℝ) • (fderiv ℝ φ (x + hshift k h) - fderiv ℝ φ x)) x := by
    have heq : (fun x => (φ (x + hshift k h) - φ x) / h)
        = fun y => h⁻¹ * (φ (y + hshift k h) - φ y) := by funext y; rw [div_eq_inv_mul]
    rw [heq]; exact hsub.const_mul (h⁻¹ : ℝ)
  simp only [partialD]
  rw [hval.fderiv]
  simp only [_root_.smul_apply, _root_.sub_apply, smul_eq_mul]
  ring

/-! ### Extension by zero of a test-function class is the test function -/

/-- Extension by zero of the `L²(Ω)` class of a function supported inside `Ω` recovers the
function itself a.e. on the whole space: off `Ω` the function already vanishes (its
`tsupport` is inside `Ω`), and on `Ω` extension agrees with the class. -/
private lemma extendL2_toLp_ae_eq (hΩm : MeasurableSet Ω)
    {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hmem : MemLp ψ 2 (volume.restrict Ω))
    (hsupp : tsupport ψ ⊆ Ω) :
    (extendL2 hΩm (hmem.toLp ψ) : EuclideanSpace ℝ (Fin d) → ℝ) =ᵐ[volume] ψ := by
  filter_upwards [coeFn_extendL2 hΩm (hmem.toLp ψ),
      ae_imp_of_ae_restrict hmem.coeFn_toLp] with x hx himp
  rw [hx]
  by_cases hxΩ : x ∈ Ω
  · rw [Set.indicator_of_mem hxΩ, himp hxΩ]
  · rw [Set.indicator_of_notMem hxΩ,
      image_eq_zero_of_notMem_tsupport (fun hc => hxΩ (hsupp hc))]

/-! ### Discrete graph identity -/

/-- **Discrete graph identity.** On a test-function graph, the cutoff of the interior
difference quotient is the graph of the product `ζ · Dₖ^h φ`:
`cutoffMul ζ (diffQuotG k h (testGraph φ)) = testGraph (ζ · Dₖ^h φ)`. This is the discrete
analogue of `cutoffMul_testGraph`; coordinatewise the interior difference quotient of `φ`'s
classes equals the difference quotient of `φ` (its extension by zero being `φ`
itself), and the Leibniz rule `∂ᵢ(ζ · Dₖ^h φ) = ζ · ∂ᵢ(Dₖ^h φ) + (∂ᵢζ) · Dₖ^h φ` together
with `partialD_diffQuotFn` matches the successor coordinates. -/
private lemma cutoffMul_diffQuotG_testGraph (hζ : IsTestFn Ω ζ) (hφ : IsTestFn Ω φ)
    (hΩm : MeasurableSet Ω) (k : Fin d) (h : ℝ) :
    cutoffMul hζ (diffQuotG k h hΩm hφ.testGraph)
      = (isTestFn_cutoff_diffQuotFn hζ hφ k h).testGraph := by
  have hsh_test : ∀ᵐ x ∂volume,
      (⇑(extendL2 hΩm hφ.testCls) : EuclideanSpace ℝ (Fin d) → ℝ) (x + hshift k h)
        = φ (x + hshift k h) :=
    (measurePreserving_add_right volume
        (hshift k h)).quasiMeasurePreserving.tendsto_ae.eventually
      (extendL2_toLp_ae_eq hΩm hφ.mem_lp hφ.2.2)
  apply PiLp.ext
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · -- coordinate `0`: `ζ · Dₖ^h φ`
    rw [cutoffMul_apply_zero]
    simp only [diffQuotG_apply, IsTestFn.testGraph_zero]
    apply Lp.ext
    filter_upwards [mulTest_coeFn hζ (diffQuotD k h hΩm hφ.testCls),
        coeFn_diffQuotD k h hΩm hφ.testCls, ae_restrict_of_ae hsh_test,
        (show (⇑hφ.testCls : EuclideanSpace ℝ (Fin d) → ℝ)
          =ᵐ[volume.restrict Ω] φ from hφ.mem_lp.coeFn_toLp),
        (show (⇑(isTestFn_cutoff_diffQuotFn hζ hφ k h).testCls
            : EuclideanSpace ℝ (Fin d) → ℝ)
          =ᵐ[volume.restrict Ω] fun x => ζ x * ((φ (x + hshift k h) - φ x) / h) from
          (isTestFn_cutoff_diffQuotFn hζ hφ k h).mem_lp.coeFn_toLp)]
      with x hmt hdq hsh htc hpsi
    rw [hmt, hdq, hsh, htc, hpsi]
  · -- coordinate `i+1`: Leibniz `∂ᵢ(ζ · Dₖ^h φ)`
    have hsh_part : ∀ᵐ x ∂volume,
        (⇑(extendL2 hΩm (hφ.partialCls i)) : EuclideanSpace ℝ (Fin d) → ℝ) (x + hshift k h)
          = partialD i φ (x + hshift k h) :=
      (measurePreserving_add_right volume
          (hshift k h)).quasiMeasurePreserving.tendsto_ae.eventually
        (extendL2_toLp_ae_eq hΩm (hφ.memLp_partialD i)
          ((tsupport_partialD_subset i φ).trans hφ.2.2))
    have hpsi_eq : partialD i (fun x => ζ x * ((φ (x + hshift k h) - φ x) / h))
        = fun x => ζ x * ((partialD i φ (x + hshift k h) - partialD i φ x) / h)
          + partialD i ζ x * ((φ (x + hshift k h) - φ x) / h) := by
      rw [partialD_mul (hζ.1.differentiable (by simp))
          ((contDiff_diffQuotFn hφ.1 k h).differentiable (by simp)) i,
        partialD_diffQuotFn (hφ.1.differentiable (by simp)) i k h]
    rw [cutoffMul_apply_succ]
    simp only [diffQuotG_apply, IsTestFn.testGraph_zero, IsTestFn.testGraph_succ]
    apply Lp.ext
    filter_upwards [Lp.coeFn_add (mulTest hζ (diffQuotD k h hΩm (hφ.partialCls i)))
          (mulTestPartial hζ i (diffQuotD k h hΩm hφ.testCls)),
        mulTest_coeFn hζ (diffQuotD k h hΩm (hφ.partialCls i)),
        mulTestPartial_coeFn hζ i (diffQuotD k h hΩm hφ.testCls),
        coeFn_diffQuotD k h hΩm (hφ.partialCls i),
        coeFn_diffQuotD k h hΩm hφ.testCls,
        ae_restrict_of_ae hsh_part, ae_restrict_of_ae hsh_test,
        (show (⇑(hφ.partialCls i) : EuclideanSpace ℝ (Fin d) → ℝ)
          =ᵐ[volume.restrict Ω] partialD i φ from (hφ.memLp_partialD i).coeFn_toLp),
        (show (⇑hφ.testCls : EuclideanSpace ℝ (Fin d) → ℝ)
          =ᵐ[volume.restrict Ω] φ from hφ.mem_lp.coeFn_toLp),
        (show (⇑((isTestFn_cutoff_diffQuotFn hζ hφ k h).partialCls i)
            : EuclideanSpace ℝ (Fin d) → ℝ)
          =ᵐ[volume.restrict Ω]
            partialD i (fun x => ζ x * ((φ (x + hshift k h) - φ x) / h)) from
          ((isTestFn_cutoff_diffQuotFn hζ hφ k h).memLp_partialD i).coeFn_toLp)]
      with x hadd hmt hmtp hdqp hdqt hshp hsht htcp htct hpsi
    rw [hadd, Pi.add_apply, hmt, hmtp, hdqp, hdqt, hshp, hsht, htcp, htct, hpsi,
      congrFun hpsi_eq x]

/-! ### Crux admissibility -/

/-- **Crux admissibility.** For `U ∈ H₀¹(Ω)`, the cutoff of its interior difference quotient
is again in `H₀¹(Ω)`. Since `cutoffMul ζ ∘ diffQuotG k h` is continuous and sends every
test-function graph into `H₀¹(Ω)` (by `cutoffMul_diffQuotG_testGraph`, as `ζ · Dₖ^h φ` is a
test function for every `φ`), it maps the closure `H₀¹(Ω)` into the closed set `H₀¹(Ω)`.
This is what makes `v_h = -Dₖ^{-h}(ζ²·Dₖ^h u)` a legal test element (Evans, *Partial
Differential Equations* (2nd ed.), §6.3.1). -/
theorem cutoffMul_diffQuotG_mem_H01 (hζ : IsTestFn Ω ζ) (k : Fin d) {h : ℝ}
    (hΩm : MeasurableSet Ω)
    (_hsmall : ∀ x ∈ tsupport ζ, x + hshift k h ∈ Ω) {U : H1amb Ω} (hU : U ∈ H01 Ω) :
    cutoffMul hζ (diffQuotG k h hΩm U) ∈ H01 Ω := by
  have hle : (Submodule.span ℝ (testGraphSet Ω)).topologicalClosure
      ≤ Submodule.comap ((cutoffMul hζ).comp (diffQuotG k h hΩm)).toLinearMap (H01 Ω) := by
    apply Submodule.topologicalClosure_minimal
    · rw [Submodule.span_le]
      rintro _ ⟨φ, hφ, rfl⟩
      change cutoffMul hζ (diffQuotG k h hΩm hφ.testGraph) ∈ H01 Ω
      rw [cutoffMul_diffQuotG_testGraph hζ hφ hΩm k]
      exact (Submodule.le_topologicalClosure _)
        (Submodule.subset_span ⟨_, isTestFn_cutoff_diffQuotFn hζ hφ k h, rfl⟩)
    · exact IsClosed.preimage ((cutoffMul hζ).comp (diffQuotG k h hΩm)).continuous
        (Submodule.isClosed_topologicalClosure _)
  exact Submodule.mem_comap.mp (hle hU)

end EllipticPdes.Regularity
