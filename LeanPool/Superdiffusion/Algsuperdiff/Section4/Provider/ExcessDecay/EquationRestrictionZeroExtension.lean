/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.HighContrastHomogenization.Support.Sobolev.Truncation.WeakGradientLimit
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.EuclideanL2CZ

/-!
# EquationRestrictionZeroExtension

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Zero extension of an `H¹₀` test function to a superset

The Support-grade primitive needed to restrict a divergence-form weak equation
from a set `W` to a subset `V`: every `H¹₀(V)` test function is, after
extension by zero, an `H¹₀(W)` test function with gradient the zero extension of
the original gradient.

CoarseGraining proves exactly this (`H10Function.extendByZeroToOpenSuperset` in
`Homogenization/Sobolev/W1p/ZeroExtensionGraph.lean`) but through the
finite-exponent graph closure of
`Homogenization/Sobolev/W1p/WeakGradientClosure`, neither of which is available
in this repository's pinned upstream build tree (no `.olean`; recompiling
upstream is forbidden).  The construction is therefore re-derived here at the
single exponent `p = 2` that the §4.3 leg needs, on the built `L²` closure
`HasWeakGradientOn.of_tendsto_eLpNorm_two`
(`Homogenization/Sobolev/Truncation/WeakGradientLimit.lean`).

## Why the extension is a theorem and not bookkeeping

The zero extension of an `H¹(V)` function need *not* have a weak gradient across
`∂V`; it does exactly because an `H¹₀(V)` function carries an approximating
sequence of smooth functions with compact support **inside** `V`.  Each
approximant is a legitimate global test function, its classical integration by
parts is valid on all of `W`, and both sides are `L²`-continuous, so the
identity survives the limit.  That is the content below.

## Deviation from CoarseGraining's version (weaker hypotheses)

CoarseGraining's `extendByZeroToOpenSuperset` asks for `IsOpen W`; the version
here does not (openness of `W` is only used by CoarseGraining's route through
the whole-space graph and its subsequent restriction).  `MeasurableSet V` and
`V ⊆ W` suffice.

## References

* CoarseGraining, `Homogenization/Sobolev/W1p/ZeroExtensionGraph.lean` (the
  unavailable finite-`p` original; the four indicator identities below are its
  private helpers at `p = 2`),
  `Homogenization/Sobolev/Truncation/WeakGradientLimit.lean`
  (`HasWeakGradientOn.of_tendsto_eLpNorm_two`),
  `Homogenization/Sobolev/H1/BasicLemmas.lean`
  (`HasWeakGradientOn.of_contDiff`).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open MeasureTheory Filter
open HCPolySupport
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The zero extensions -/

/-- The literal zero extension of the value of an `H¹₀` function. -/
def h10ZeroExtension {V : Set (Vec d)} (phi : H10Function V) : Vec d → ℝ :=
  Set.indicator V phi.toH1Function.toFun

/-- The literal zero extension of the gradient of an `H¹₀` function. -/
def h10ZeroExtensionGrad {V : Set (Vec d)} (phi : H10Function V) : Vec d → Vec d :=
  Set.indicator V phi.toH1Function.grad

theorem h10ZeroExtension_of_mem {V : Set (Vec d)} (phi : H10Function V) {x : Vec d}
    (hx : x ∈ V) : h10ZeroExtension phi x = phi.toH1Function.toFun x := by
  simp only [h10ZeroExtension, Set.indicator_of_mem hx]

theorem h10ZeroExtension_of_not_mem {V : Set (Vec d)} (phi : H10Function V) {x : Vec d}
    (hx : x ∉ V) : h10ZeroExtension phi x = 0 := by
  simp only [h10ZeroExtension, Set.indicator_of_notMem hx]

theorem h10ZeroExtensionGrad_of_mem {V : Set (Vec d)} (phi : H10Function V) {x : Vec d}
    (hx : x ∈ V) : h10ZeroExtensionGrad phi x = phi.toH1Function.grad x := by
  simp only [h10ZeroExtensionGrad, Set.indicator_of_mem hx]

theorem h10ZeroExtensionGrad_of_not_mem {V : Set (Vec d)} (phi : H10Function V)
    {x : Vec d} (hx : x ∉ V) : h10ZeroExtensionGrad phi x = 0 := by
  simp only [h10ZeroExtensionGrad, Set.indicator_of_notMem hx]

private theorem h10ZeroExtensionGrad_coord {V : Set (Vec d)} (phi : H10Function V)
    (i : Fin d) :
    (fun x => h10ZeroExtensionGrad phi x i) =
      Set.indicator V (fun x => phi.toH1Function.grad x i) := by
  funext x
  by_cases hx : x ∈ V
  · simp only [h10ZeroExtensionGrad_of_mem phi hx, Set.indicator_of_mem hx]
  · simp only [h10ZeroExtensionGrad_of_not_mem phi hx, Set.indicator_of_notMem hx,
      Pi.zero_apply]

/-! ## 2. The four indicator identities of the approximating sequence -/

private theorem h10_approx_eq_zero_of_not_mem {V : Set (Vec d)} (phi : H10Function V)
    (n : ℕ) {x : Vec d} (hx : x ∉ V) : phi.approx n x = 0 := by
  refine image_eq_zero_of_notMem_tsupport ?_
  intro hxs
  exact hx (phi.approx_support_subset n hxs)

private theorem h10_fderiv_approx_eq_zero_of_not_mem {V : Set (Vec d)}
    (phi : H10Function V) (n : ℕ) (i : Fin d) {x : Vec d} (hx : x ∉ V) :
    (fderiv ℝ (phi.approx n) x) (basisVec i) = 0 := by
  have hxs : x ∉ tsupport (phi.approx n) := fun hxs =>
    hx (phi.approx_support_subset n hxs)
  have hzero : phi.approx n =ᶠ[nhds x] 0 :=
    (isClosed_tsupport (f := phi.approx n)).isOpen_compl.eventually_mem hxs |>.mono
      (fun y hy => image_eq_zero_of_notMem_tsupport hy)
  rw [hzero.fderiv_eq]
  simp only [fderiv_zero, Pi.zero_apply, zero_apply]

theorem h10_approx_sub_zeroExtension {V : Set (Vec d)} (phi : H10Function V)
    (n : ℕ) :
    (fun x => phi.approx n x - h10ZeroExtension phi x) =
      Set.indicator V (fun x => phi.approx n x - phi.toH1Function.toFun x) := by
  funext x
  by_cases hx : x ∈ V
  · simp only [Set.indicator_of_mem hx, h10ZeroExtension_of_mem phi hx]
  · rw [Set.indicator_of_notMem hx, h10ZeroExtension_of_not_mem phi hx, sub_zero,
      h10_approx_eq_zero_of_not_mem phi n hx]

theorem h10_fderiv_approx_sub_zeroExtensionGrad {V : Set (Vec d)}
    (phi : H10Function V) (n : ℕ) (i : Fin d) :
    (fun x => (fderiv ℝ (phi.approx n) x) (basisVec i) -
        h10ZeroExtensionGrad phi x i) =
      Set.indicator V (fun x => (fderiv ℝ (phi.approx n) x) (basisVec i) -
        phi.toH1Function.grad x i) := by
  funext x
  by_cases hx : x ∈ V
  · simp only [Set.indicator_of_mem hx, h10ZeroExtensionGrad_of_mem phi hx]
  · rw [Set.indicator_of_notMem hx, h10ZeroExtensionGrad_of_not_mem phi hx,
      Pi.zero_apply, sub_zero, h10_fderiv_approx_eq_zero_of_not_mem phi n i hx]

/-! ## 3. `L²` control of the extensions -/

theorem memL2On_h10ZeroExtension {V W : Set (Vec d)} (phi : H10Function V)
    (hV : MeasurableSet V) : MemL2On W (h10ZeroExtension phi) := by
  have hglob : MemLp (h10ZeroExtension phi) 2 volume :=
    (MeasureTheory.memLp_indicator_iff_restrict hV).2 phi.toH1Function.memL2
  exact hglob.restrict W

theorem gradMemL2On_h10ZeroExtensionGrad {V W : Set (Vec d)}
    (phi : H10Function V) (hV : MeasurableSet V) :
    GradMemL2On W (h10ZeroExtensionGrad phi) := by
  intro i
  have hglob : MemLp (fun x => h10ZeroExtensionGrad phi x i) 2 volume := by
    rw [h10ZeroExtensionGrad_coord phi i]
    exact (MeasureTheory.memLp_indicator_iff_restrict hV).2
      (phi.toH1Function.gradMemL2 i)
  exact hglob.restrict W

/-! ## 4. The weak gradient of the zero extension -/

/-- **The zero extension of an `H¹₀` pair is a weak-gradient pair on any
superset.**  The `L²`-limit closure applied to the `H¹₀` approximants, each of
which is smooth with compact support inside `V ⊆ W`. -/
theorem hasWeakGradientOn_h10ZeroExtension {V W : Set (Vec d)} (phi : H10Function V)
    (hV : MeasurableSet V) (hVW : V ⊆ W) :
    HasWeakGradientOn W (h10ZeroExtension phi) (h10ZeroExtensionGrad phi) := by
  refine HasWeakGradientOn.of_tendsto_eLpNorm_two
    (u_n := fun n => phi.approx n)
    (Du_n := fun n => euclideanGradient (phi.approx n))
    (memL2On_h10ZeroExtension phi hV) (gradMemL2On_h10ZeroExtensionGrad phi hV)
    (fun n => ?_) (fun n i => ?_) (fun n => HasWeakGradientOn.of_contDiff
      ((phi.approx_smooth n).of_le (by norm_num))) ?_ (fun i => ?_)
  · exact ((phi.approx_smooth n).continuous.memLp_of_hasCompactSupport
      (p := (2 : ℝ≥0∞)) (phi.approx_hasCompactSupport n)).restrict W
  · exact memScalarL2_coord_of_memVectorL2
      (memVectorL2_euclideanGradient_of_contDiff_hasCompactSupport
        (phi.approx_smooth n) (phi.approx_hasCompactSupport n)) i
  · refine phi.tendsto_approx.congr fun n => ?_
    rw [h10_approx_sub_zeroExtension phi n,
      MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict hV,
      Measure.restrict_restrict_of_subset hVW]
  · refine (phi.tendsto_approx_grad i).congr fun n => ?_
    rw [show (fun x => euclideanGradient (phi.approx n) x i -
          h10ZeroExtensionGrad phi x i) =
        fun x => (fderiv ℝ (phi.approx n) x) (basisVec i) -
          h10ZeroExtensionGrad phi x i from rfl,
      h10_fderiv_approx_sub_zeroExtensionGrad phi n i,
      MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict hV,
      Measure.restrict_restrict_of_subset hVW]

/-! ## 5. The extension as an `H¹₀` function of the superset -/

/-- **Every `H¹₀(V)` function is an `H¹₀(W)` function for `V ⊆ W`**, by literal
zero extension of both value and gradient.  Re-derivation at `p = 2` of
CoarseGraining's `H10Function.extendByZeroToOpenSuperset`, without the `IsOpen
W` hypothesis. -/
def h10ExtendToSuperset {V W : Set (Vec d)} (phi : H10Function V)
    (hV : MeasurableSet V) (hVW : V ⊆ W) : H10Function W where
  toFun := h10ZeroExtension phi
  grad := h10ZeroExtensionGrad phi
  memL2 := memL2On_h10ZeroExtension phi hV
  gradMemL2 := gradMemL2On_h10ZeroExtensionGrad phi hV
  hasWeakGradient := hasWeakGradientOn_h10ZeroExtension phi hV hVW
  approx := phi.approx
  approx_smooth := phi.approx_smooth
  approx_hasCompactSupport := phi.approx_hasCompactSupport
  approx_support_subset := fun n => (phi.approx_support_subset n).trans hVW
  tendsto_approx := by
    refine phi.tendsto_approx.congr fun n => ?_
    show eLpNorm (fun x => phi.approx n x - phi.toH1Function.toFun x) 2
          (volume.restrict V) =
        eLpNorm (fun x => phi.approx n x - h10ZeroExtension phi x) 2
          (volume.restrict W)
    rw [h10_approx_sub_zeroExtension phi n,
      MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict hV,
      Measure.restrict_restrict_of_subset hVW]
  tendsto_approx_grad := fun i => by
    refine (phi.tendsto_approx_grad i).congr fun n => ?_
    show eLpNorm (fun x => (fderiv ℝ (phi.approx n) x) (basisVec i) -
            phi.toH1Function.grad x i) 2 (volume.restrict V) =
        eLpNorm (fun x => (fderiv ℝ (phi.approx n) x) (basisVec i) -
            h10ZeroExtensionGrad phi x i) 2 (volume.restrict W)
    rw [h10_fderiv_approx_sub_zeroExtensionGrad phi n i,
      MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict hV,
      Measure.restrict_restrict_of_subset hVW]

@[simp] theorem h10ExtendToSuperset_toFun {V W : Set (Vec d)} (phi : H10Function V)
    (hV : MeasurableSet V) (hVW : V ⊆ W) :
    (h10ExtendToSuperset phi hV hVW).toH1Function.toFun = h10ZeroExtension phi :=
  rfl

@[simp] theorem h10ExtendToSuperset_grad {V W : Set (Vec d)} (phi : H10Function V)
    (hV : MeasurableSet V) (hVW : V ⊆ W) :
    (h10ExtendToSuperset phi hV hVW).toH1Function.grad = h10ZeroExtensionGrad phi :=
  rfl

end

end Algsuperdiff.Section4.Provider.ExcessDecay
