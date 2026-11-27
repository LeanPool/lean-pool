/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Sobolev.SobolevRestrictionSpaces
public import Mathlib.Analysis.InnerProductSpace.Dual

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Duality of Sobolev spaces on open sets

Let `V` be a finite-dimensional real inner product space, such as `ℝ^d`, with Lebesgue measure,
`Ω ⊆ V` open and `s` real. The Hilbert spaces `HTilde^s(Ω)` and `H^{-s}(Ω)` of
`FunctionSpaces/Domains/Sobolev/SobolevRestrictionSpaces.lean` are dual to each other, as in
Chandler-Wilde, Hewett and Moiola (Theorem 3.3), for every open set and every real `s`.

* **The Bessel potential on Schwartz functions**: `J_t u = 𝓕⁻(⟨ξ⟩^t 𝓕u)` (`Rd.besselSchwartz`, in
  `FunctionSpaces.Rd.Sobolev.SobolevTwoLittlewoodPaley`) is real for real `u`
  (`Rd.conj_besselSchwartz_apply`); for `g ∈ L_2(V)`, `(J_t g)(u) = ∫ J_t u · g`
  (`Rd.besselPotential_toLp_apply`).
* **`J_{2s}` as an isometry**: `Rd.besselShift s : H^s(V) ≃ₗᵢ[ℂ] H^{-s}(V)` keeps the `L_2`
  function `J_s U` and acts on distributions as `J_{2s}` (`Rd.toDistr_besselShift`).
* **The pairing** `[W, U] = ⟪J_{-s} W, J_s U⟫_{L_2}` of `W ∈ H^{-s}(V)` and `U ∈ H^s(V)`
  (`Rd.pairing`, bundled in `U` as `Rd.pairingCLM`) has `|[W, U]| ≤ ‖W‖ ‖U‖` and extends `U(φ)`
  and `conj (W(φ))` for test functions `φ` (`Rd.pairing_ofTest_left`, `Rd.pairing_ofTest_right`);
  at `s = 1` and for Schwartz `W` it is the `L_2` inner product (`Rd.pairing_one_toLp`).
* **Orthogonal complements**: `⟪U, φ⟫_{H^s} = conj ((J_{2s} U)(φ))` for test functions `φ`
  (`Rd.inner_ofTest_eq`), so `U ⊥ HTilde^s(Ω)` iff `J_{2s} U` vanishes on `Ω`
  (`Rd.mem_orthogonal_tildeSpace_iff`), and `J_{2s}` maps `HTilde^s(Ω)` onto `H^{-s}(Ω)`
  (`Rd.tildeEquivRestriction`) and `H^s(Ω)` onto `HTilde^{-s}(Ω)` (`Rd.restrictionEquivTilde`).
  Elements vanishing on `Ω` pair to zero with `HTilde^s(Ω)`
  (`Rd.pairing_eq_zero_of_mem_vanishOn_left`,
  `Rd.pairing_eq_zero_of_mem_vanishOn_right`).
* **Duality**: `(HTilde^s(Ω))^* ≅ H^{-s}(Ω)` (`Rd.dualEquiv`), `(H^s(Ω))^* ≅ HTilde^{-s}(Ω)`
  (`Rd.dualRestrictionEquiv`) and `(H^1_0(Ω))^* ≅ H^{-1}(Ω)` (`Rd.dualZeroBoundaryEquiv`), each
  through the pairing, conjugate-linear and isometric; the pairing may use every extension of the
  representing element (`Rd.dualEquiv_apply_of_restrictProj_eq`,
  `Rd.dualRestrictionEquiv_apply_restrictProj`).
-/

@[expose] public section

open MeasureTheory Filter TopologicalSpace ComplexConjugate
open scoped ENNReal SchwartzMap Real BesselPotentialSpace FourierTransform InnerProductSpace
  Distributions
open TemperedDistribution (besselPotential)

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### The Bessel potential on Schwartz functions -/

/-- **`J_t` keeps real functions real**: for a Schwartz function `u` with real values,
`conj (J_t u(x)) = J_t u(x)` (`Rd.conj_fourierInv_apply`, `Rd.conj_fourier_apply`,
`Rd.besselSchwartz_apply_eq_fourier`). -/
theorem conj_besselSchwartz_apply (t : ℝ) {u : 𝓢(V, ℂ)} (hu : ∀ x, conj (u x) = u x) (x : V) :
    conj (besselSchwartz t u x) = besselSchwartz t u x := by
  conv_rhs => rw [besselSchwartz_apply_eq_fourier]
  rw [besselSchwartz_apply, conj_fourierInv_apply]
  refine congrFun (congrArg _ (funext fun ξ => ?_)) x
  rw [map_mul, Complex.conj_ofReal, conj_fourier_apply]
  simp only [hu]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **A test function is real**: `conj (φ(x)) = φ(x)` for the Schwartz function of a real test
function `φ`. -/
theorem conj_testSchwartz {Ω : Opens V} (φ : 𝓓(Ω, ℝ)) (x : V) :
    conj (testSchwartz φ x) = testSchwartz φ x := by
  simp

/-- **The Bessel potential of an `L_2` function at a Schwartz function**: for `g ∈ L_2(V)` and a
Schwartz function `u`, `(J_t g)(u) = ∫ J_t u · g`, since Mathlib's `J_t` acts by the transpose
(`Rd.besselPotential_apply_apply`). -/
theorem besselPotential_toLp_apply (t : ℝ) (g : Lp ℂ 2 (volume : Measure V)) (u : 𝓢(V, ℂ)) :
    besselPotential V ℂ t (g : 𝓢'(V, ℂ)) u = ∫ x, besselSchwartz t u x * g x := by
  rw [besselPotential_apply_apply, Lp.toTemperedDistribution_apply]
  simp only [smul_eq_mul]

/-- **`J_t` of a real Schwartz function against `L_2`**: for a Schwartz function `u` with real
values and `g ∈ L_2(V)`, `⟪J_t u, g⟫_{L_2} = (J_t g)(u)`: the inner product is
`∫ conj (J_t u) · g`, and `J_t u` is real (`Rd.conj_besselSchwartz_apply`,
`Rd.besselPotential_toLp_apply`). -/
theorem inner_toLp_besselSchwartz (t : ℝ) {u : 𝓢(V, ℂ)} (hu : ∀ x, conj (u x) = u x)
    (g : Lp ℂ 2 (volume : Measure V)) :
    ⟪(besselSchwartz t u).toLp 2, g⟫_ℂ = besselPotential V ℂ t (g : 𝓢'(V, ℂ)) u := by
  rw [MeasureTheory.L2.inner_def, besselPotential_toLp_apply]
  refine integral_congr_ae ?_
  filter_upwards [(besselSchwartz t u).coeFn_toLp 2 volume] with x hx
  rw [hx, RCLike.inner_apply', conj_besselSchwartz_apply t hu]

/-! ### The inner product of `H^t(V)` and Schwartz functions -/

/-- **The inner product of `H^t(V)` is that of the `L_2` functions**:
`⟪U, W⟫_{H^t} = ⟪J_t U, J_t W⟫_{L_2}`, which is how Mathlib defines the inner product of
`BesselPotentialSpace`. -/
theorem inner_toLp_toLp {t : ℝ} (U W : H^{t}(V)) : ⟪U.toLp, W.toLp⟫_ℂ = ⟪U, W⟫_ℂ :=
  rfl

/-- **The `L_2` function of a Schwartz function in `H^t(V)`**: for a Schwartz function `u`, the
element `u ∈ H^t(V)` (Mathlib's `SchwartzMap.memSobolev`) has `J_t u` as its `L_2` function, since
`L_2` functions are determined by their distributions (`Rd.eq_of_toTemperedDistribution_eq`). -/
theorem toLp_schwartz (t : ℝ) (u : 𝓢(V, ℂ)) :
    (u.memSobolev (s := t) (p := 2)).toBesselPotentialSpace.toLp =
      (besselSchwartz t u).toLp 2 := by
  have h : (((u.memSobolev (s := t) (p := 2)).toBesselPotentialSpace.toLp :
      Lp ℂ 2 (volume : Measure V)) : 𝓢'(V, ℂ)) =
      (((besselSchwartz t u).toLp 2 : Lp ℂ 2 (volume : Measure V)) : 𝓢'(V, ℂ)) := by
    rw [← BesselPotentialSpace.bessel_toDistr_eq_toLp,
      TemperedDistribution.MemSobolev.toBesselPotentialSpace_toDistr, besselPotential_schwartz,
      Lp.toTemperedDistribution_toLp_eq]
  exact eq_of_toTemperedDistribution_eq h

/-- The `L_2` function of a test function `φ` in `H^t(V)` is `J_t φ` (`Rd.toLp_schwartz`). -/
theorem toLp_ofTest {Ω : Opens V} (t : ℝ) (φ : 𝓓(Ω, ℝ)) :
    (ofTest t φ).toLp = (besselSchwartz t (testSchwartz φ)).toLp 2 :=
  toLp_schwartz t (testSchwartz φ)

/-- **Test functions against `L_2`**: for a test function `φ` of `Ω`, as an element of `H^t(V)`,
and `g ∈ L_2(V)`, `⟪J_t φ, g⟫_{L_2} = (J_t g)(φ)` (`Rd.inner_toLp_besselSchwartz`). -/
theorem inner_ofTest_toLp {Ω : Opens V} (t : ℝ) (φ : 𝓓(Ω, ℝ))
    (g : Lp ℂ 2 (volume : Measure V)) :
    ⟪(ofTest t φ).toLp, g⟫_ℂ = besselPotential V ℂ t (g : 𝓢'(V, ℂ)) (testSchwartz φ) := by
  rw [toLp_ofTest]
  exact inner_toLp_besselSchwartz t (conj_testSchwartz φ) g

/-- **Inner products with a test function in the left slot**: for a test function `φ` of `Ω` and
`U ∈ H^t(V)`, `⟪φ, U⟫_{H^t} = (J_t (J_t U))(φ)`, the distribution `J_t` of the `L_2` function
`J_t U` at `φ` (`Rd.inner_ofTest_toLp`). -/
theorem inner_ofTest_left {Ω : Opens V} (t : ℝ) (φ : 𝓓(Ω, ℝ)) (U : H^{t}(V)) :
    ⟪ofTest t φ, U⟫_ℂ = besselPotential V ℂ t (U.toLp : 𝓢'(V, ℂ)) (testSchwartz φ) := by
  rw [← inner_toLp_toLp, inner_ofTest_toLp]

/-! ### `J_{2s}` as an isometry -/

variable (s : ℝ) in
/-- **`J_{2s}` as an isometry of `H^s(V)` onto `H^{-s}(V)`**: both spaces are isometric to
`L_2(V)` (Mathlib's `BesselPotentialSpace.toLpₗᵢ`), and `besselShift s U` is the element of
`H^{-s}(V)` with the same `L_2` function `J_s U` as `U`; on distributions it is `J_{2s}`
(`Rd.toDistr_besselShift`). -/
noncomputable def besselShift : H^{s}(V) ≃ₗᵢ[ℂ] H^{-s}(V) :=
  (BesselPotentialSpace.toLpₗᵢ V ℂ s 2).trans (BesselPotentialSpace.toLpₗᵢ V ℂ (-s) 2).symm

variable {s : ℝ} {Ω : Opens V}

/-- An element of `H^t(V)` built from an `L_2` function `f` by the inverse of Mathlib's isometry
`BesselPotentialSpace.toLpₗᵢ` has `f` as its `L_2` function. -/
theorem toLp_toLpLinearIsometry_symm_apply (t : ℝ) (f : Lp ℂ 2 (volume : Measure V)) :
    ((BesselPotentialSpace.toLpₗᵢ V ℂ t 2).symm f).toLp = f := by
  rw [← BesselPotentialSpace.toLpₗᵢ_apply, LinearIsometryEquiv.apply_symm_apply]

/-- `besselShift s U` has the same `L_2` function as `U`. -/
@[simp]
theorem toLp_besselShift (U : H^{s}(V)) : (besselShift s U).toLp = U.toLp := by
  rw [besselShift, LinearIsometryEquiv.trans_apply, BesselPotentialSpace.toLpₗᵢ_apply,
    toLp_toLpLinearIsometry_symm_apply]

/-- The distribution of `besselShift s U` is `J_s` of the `L_2` function `J_s U`. -/
theorem toDistr_besselShift_eq_besselPotential_toLp (U : H^{s}(V)) :
    (besselShift s U).toDistr = besselPotential V ℂ s (U.toLp : 𝓢'(V, ℂ)) := by
  rw [besselShift, LinearIsometryEquiv.trans_apply, BesselPotentialSpace.toLpₗᵢ_apply,
    BesselPotentialSpace.toLpₗᵢ_symm_apply, neg_neg]

/-- **Inner products with test functions through `besselShift`**: for `U ∈ H^s(V)` and a test
function `φ` of `Ω`, `⟪U, φ⟫_{H^s} = conj ((J_{2s} U)(φ))`, the conjugate of the distribution
`besselShift s U` at `φ` (`Rd.inner_ofTest_left`,
`Rd.toDistr_besselShift_eq_besselPotential_toLp`). -/
theorem inner_ofTest_eq (U : H^{s}(V)) (φ : 𝓓(Ω, ℝ)) :
    ⟪U, ofTest s φ⟫_ℂ = conj ((besselShift s U).toDistr (testSchwartz φ)) := by
  rw [← inner_conj_symm, inner_ofTest_left, toDistr_besselShift_eq_besselPotential_toLp]

/-- **`besselShift s` is `J_{2s}` on distributions**: the distribution of `besselShift s U` is
`J_{2s} U`, since `J_s U` is the `L_2` function of `U` and `J_s J_s = J_{2s}` (Mathlib's
`TemperedDistribution.besselPotential_besselPotential_apply`). -/
theorem toDistr_besselShift (U : H^{s}(V)) :
    (besselShift s U).toDistr = besselPotential V ℂ (2 * s) U.toDistr := by
  rw [toDistr_besselShift_eq_besselPotential_toLp, ← U.bessel_toDistr_eq_toLp,
    TemperedDistribution.besselPotential_besselPotential_apply, two_mul]

/-- **The inverse of `besselShift s`** is `besselShift (-s)`, read in `H^s(V)` through
`-(-s) = s` (Mathlib's `BesselPotentialSpace.copy`): both keep the `L_2` function. -/
theorem besselShift_symm_apply (W : H^{-s}(V)) :
    (besselShift s).symm W = (besselShift (-s) W).copy s (neg_neg s) := by
  refine BesselPotentialSpace.injective_toLp V ℂ s 2 ?_
  rw [BesselPotentialSpace.toLp_copy _ (neg_neg s), toLp_besselShift, besselShift,
    LinearIsometryEquiv.symm_trans, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.symm_symm, BesselPotentialSpace.toLpₗᵢ_apply,
    toLp_toLpLinearIsometry_symm_apply]

/-- The inverse of `besselShift s` keeps the `L_2` function. -/
@[simp]
theorem toLp_besselShift_symm (W : H^{-s}(V)) : ((besselShift s).symm W).toLp = W.toLp := by
  rw [besselShift_symm_apply, BesselPotentialSpace.toLp_copy _ (neg_neg s), toLp_besselShift]

/-- The distribution of `(besselShift s)⁻¹ W` is `J_{-s}` of the `L_2` function of `W`. -/
theorem toDistr_besselShift_symm (W : H^{-s}(V)) :
    ((besselShift s).symm W).toDistr = besselPotential V ℂ (-s) (W.toLp : 𝓢'(V, ℂ)) := by
  rw [besselShift, LinearIsometryEquiv.symm_trans, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.symm_symm, BesselPotentialSpace.toLpₗᵢ_apply,
    BesselPotentialSpace.toLpₗᵢ_symm_apply]

/-! ### The pairing of `H^{-s}(V)` and `H^s(V)` -/

variable (s) in
/-- **The pairing of `H^{-s}(V)` and `H^s(V)`**: `[W, U] = ⟪J_{-s} W, J_s U⟫_{L_2}`, the `L_2`
inner product of the `L_2` functions of `W` and `U`. It is conjugate-linear in `W`
(`Rd.pairing_add_left`, `Rd.pairing_smul_left`) and linear in `U` (`Rd.pairing_add_right`,
`Rd.pairing_smul_right`, `Rd.pairingCLM`), Mathlib's convention for inner products. For test
functions it is the distributional pairing (`Rd.pairing_ofTest_left`, `Rd.pairing_ofTest_right`). -/
noncomputable def pairing (W : H^{-s}(V)) (U : H^{s}(V)) : ℂ :=
  ⟪W.toLp, U.toLp⟫_ℂ

/-- The pairing is additive in `W`: `[W + W', U] = [W, U] + [W', U]`. -/
theorem pairing_add_left (W W' : H^{-s}(V)) (U : H^{s}(V)) :
    pairing s (W + W') U = pairing s W U + pairing s W' U := by
  simp only [pairing, BesselPotentialSpace.toLp_add, inner_add_left]

/-- The pairing respects differences in `W`: `[W - W', U] = [W, U] - [W', U]`. -/
theorem pairing_sub_left (W W' : H^{-s}(V)) (U : H^{s}(V)) :
    pairing s (W - W') U = pairing s W U - pairing s W' U := by
  simp only [pairing, BesselPotentialSpace.toLp_sub, inner_sub_left]

/-- The pairing is conjugate-homogeneous in `W`: `[c W, U] = conj c · [W, U]`. -/
theorem pairing_smul_left (c : ℂ) (W : H^{-s}(V)) (U : H^{s}(V)) :
    pairing s (c • W) U = conj c * pairing s W U := by
  simp only [pairing, BesselPotentialSpace.toLp_smul, inner_smul_left]

/-- The pairing is additive in `U`: `[W, U + U'] = [W, U] + [W, U']`. -/
theorem pairing_add_right (W : H^{-s}(V)) (U U' : H^{s}(V)) :
    pairing s W (U + U') = pairing s W U + pairing s W U' := by
  simp only [pairing, BesselPotentialSpace.toLp_add, inner_add_right]

/-- The pairing respects differences in `U`: `[W, U - U'] = [W, U] - [W, U']`. -/
theorem pairing_sub_right (W : H^{-s}(V)) (U U' : H^{s}(V)) :
    pairing s W (U - U') = pairing s W U - pairing s W U' := by
  simp only [pairing, BesselPotentialSpace.toLp_sub, inner_sub_right]

/-- The pairing is homogeneous in `U`: `[W, c U] = c · [W, U]`. -/
theorem pairing_smul_right (W : H^{-s}(V)) (c : ℂ) (U : H^{s}(V)) :
    pairing s W (c • U) = c * pairing s W U := by
  simp only [pairing, BesselPotentialSpace.toLp_smul, inner_smul_right]

variable (s) in
/-- **The pairing as a bounded functional**: for `W ∈ H^{-s}(V)`, `U ↦ [W, U]` as a continuous
linear map `H^s(V) → ℂ`, the inner product with `J_{-s} W` (Mathlib's `innerSL`) after the
isometry `U ↦ J_s U` onto `L_2(V)`. -/
noncomputable def pairingCLM (W : H^{-s}(V)) : H^{s}(V) →L[ℂ] ℂ :=
  (innerSL ℂ W.toLp).comp
    (BesselPotentialSpace.toLpₗᵢ V ℂ s 2).toContinuousLinearEquiv.toContinuousLinearMap

/-- `pairingCLM s W U = [W, U]`. -/
@[simp]
theorem pairingCLM_apply (W : H^{-s}(V)) (U : H^{s}(V)) : pairingCLM s W U = pairing s W U := by
  simp only [pairingCLM, pairing, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, BesselPotentialSpace.toLpₗᵢ_apply,
    innerSL_apply_apply]

/-- **The pairing is bounded**: `|[W, U]| ≤ ‖W‖ ‖U‖` (Cauchy–Schwarz in `L_2`). -/
theorem norm_pairing_le (W : H^{-s}(V)) (U : H^{s}(V)) : ‖pairing s W U‖ ≤ ‖W‖ * ‖U‖ := by
  rw [← BesselPotentialSpace.norm_toLp_eq W, ← BesselPotentialSpace.norm_toLp_eq U]
  exact norm_inner_le_norm _ _

/-- **The pairing through `besselShift`**: `[J_{2s} U', U] = ⟪U', U⟫_{H^s}`. -/
theorem pairing_besselShift (U' U : H^{s}(V)) : pairing s (besselShift s U') U = ⟪U', U⟫_ℂ := by
  rw [pairing, toLp_besselShift, inner_toLp_toLp]

/-- **The pairing extends the distribution in the first slot**: for a test function `φ` of `Ω`
and `U ∈ H^s(V)`, `[φ, U] = U(φ)`, since `[φ, U] = (J_{-s}(J_s U))(φ)`
(`Rd.inner_ofTest_toLp`). -/
theorem pairing_ofTest_left (φ : 𝓓(Ω, ℝ)) (U : H^{s}(V)) :
    pairing s (ofTest (-s) φ) U = U.toDistr (testSchwartz φ) := by
  rw [pairing, inner_ofTest_toLp, U.besselPotential_neg_toLp_eq]

/-- **The pairing extends the distribution in the second slot**: for `W ∈ H^{-s}(V)` and a test
function `φ` of `Ω`, `[W, φ] = conj (W(φ))`. -/
theorem pairing_ofTest_right (W : H^{-s}(V)) (φ : 𝓓(Ω, ℝ)) :
    pairing s W (ofTest s φ) = conj (W.toDistr (testSchwartz φ)) := by
  have hW := W.besselPotential_neg_toLp_eq
  rw [neg_neg] at hW
  rw [pairing, ← inner_conj_symm, inner_ofTest_toLp, hW]

/-- **The pairing at `s = 1` is the `L_2` inner product**: for a Schwartz function `ψ` as an
element of `H^{-1}(V)` and `U ∈ H^1(V)`, `[ψ, U] = ⟪ψ, U⟫_{L_2}`. By Plancherel both sides are
integrals of Fourier transforms, `∫ conj (⟨ξ⟩⁻¹ 𝓕ψ) 𝓕(J_1 U)` and `∫ conj (𝓕ψ) ⟨ξ⟩⁻¹ 𝓕(J_1 U)`
(`Rd.fourier_toL2_ae_eq`), and the weight is real. -/
theorem pairing_one_toLp (ψ : 𝓢(V, ℂ)) (U : H^{1}(V)) :
    pairing 1 (ψ.memSobolev (s := -1) (p := 2)).toBesselPotentialSpace U =
      ⟪ψ.toLp 2, toL2 U⟫_ℂ := by
  rw [pairing, toLp_schwartz, ← Lp.inner_fourier_eq]
  conv_rhs => rw [← Lp.inner_fourier_eq]
  rw [SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq, MeasureTheory.L2.inner_def,
    MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(𝓕 (besselSchwartz (-1) ψ)).coeFn_toLp 2 volume, (𝓕 ψ).coeFn_toLp 2 volume,
    fourier_toL2_ae_eq U] with ξ h1 h2 h3
  rw [h1, h2, h3, RCLike.inner_apply', RCLike.inner_apply', besselSchwartz,
    SchwartzMap.fourierMultiplierCLM_apply, FourierTransform.fourier_fourierInv_eq,
    SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_besselWeight (-1)), smul_eq_mul,
    map_mul, Complex.conj_ofReal]
  ring

/-! ### Orthogonal complements of `HTilde^t(Ω)` -/

/-- **The orthogonal complement of `HTilde^t(Ω)`**: `U ∈ H^t(V)` is orthogonal to `HTilde^t(Ω)`
iff the
distribution `J_t (J_t U)` vanishes on every test function of `Ω`. The orthogonal complement of a
closure is that of the set (Mathlib's `Submodule.orthogonal_closure`), orthogonality to a span is
orthogonality to its generators, and `⟪φ, U⟫ = (J_t (J_t U))(φ)` (`Rd.inner_ofTest_left`). -/
theorem mem_orthogonal_tildeSpace_iff_toLp {t : ℝ} (U : H^{t}(V)) :
    U ∈ (tildeSpace t Ω)ᗮ ↔
      ∀ φ : 𝓓(Ω, ℝ), besselPotential V ℂ t (U.toLp : 𝓢'(V, ℂ)) (testSchwartz φ) = 0 := by
  rw [tildeSpace, Submodule.orthogonal_closure, testSpan, Submodule.mem_orthogonal]
  constructor
  · intro h φ
    rw [← inner_ofTest_left]
    exact h _ (Submodule.subset_span ⟨φ, rfl⟩)
  · intro h u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨φ, rfl⟩ := hx
      exact (inner_ofTest_left t φ U).trans (h φ)
    | zero => exact inner_zero_left _
    | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
    | smul c x _ hx => rw [inner_smul_left, hx, mul_zero]

/-- **The orthogonal complement of `HTilde^t(Ω)` as a preimage**: for a linear isometry `e` of
`H^t(V)` onto `H^{t'}(V)` whose values are the distributions `J_t (J_t U)`, `HTilde^t(Ω)^⊥` is the
preimage under `e` of the elements of `H^{t'}(V)` vanishing on `Ω`
(`Rd.mem_orthogonal_tildeSpace_iff_toLp`). The hypothesis determines `e`, and such an `e` exists
only for `t' = -t`; the lemma is stated with `t'` free so that it applies to both
`Rd.besselShift s` and its inverse. -/
theorem orthogonal_tildeSpace_eq_comap {t t' : ℝ} (e : H^{t}(V) ≃ₗᵢ[ℂ] H^{t'}(V))
    (he : ∀ U, (e U).toDistr = besselPotential V ℂ t (U.toLp : 𝓢'(V, ℂ))) :
    (tildeSpace t Ω)ᗮ = (vanishOn t' Ω).comap (e.toLinearEquiv : H^{t}(V) →ₗ[ℂ] H^{t'}(V)) := by
  ext U
  rw [mem_orthogonal_tildeSpace_iff_toLp, Submodule.mem_comap, mem_vanishOn_iff]
  simp only [LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv, he]

/-- **The image of `HTilde^t(Ω)`**: for `e` as in `Rd.orthogonal_tildeSpace_eq_comap`,
`e(HTilde^t(Ω))`
is `H^{t'}(Ω)`, the orthogonal complement of the elements of `H^{t'}(V)` vanishing on `Ω`. Since
`HTilde^t(Ω)` is closed it is its double orthogonal complement, and `e` maps orthogonal complements
to orthogonal complements (Mathlib's `Submodule.map_orthogonal_equiv`). As there, `t'` is free
only so that the lemma applies to both `Rd.besselShift s` and its inverse. -/
theorem map_tildeSpace_eq_orthogonal {t t' : ℝ} (e : H^{t}(V) ≃ₗᵢ[ℂ] H^{t'}(V))
    (he : ∀ U, (e U).toDistr = besselPotential V ℂ t (U.toLp : 𝓢'(V, ℂ))) :
    (tildeSpace t Ω).map (e.toLinearEquiv : H^{t}(V) →ₗ[ℂ] H^{t'}(V)) = (vanishOn t' Ω)ᗮ := by
  calc (tildeSpace t Ω).map (e.toLinearEquiv : H^{t}(V) →ₗ[ℂ] H^{t'}(V))
      = ((tildeSpace t Ω)ᗮᗮ).map (e.toLinearEquiv : H^{t}(V) →ₗ[ℂ] H^{t'}(V)) := by
        rw [Submodule.orthogonal_orthogonal]
    _ = (((tildeSpace t Ω)ᗮ).map (e.toLinearEquiv : H^{t}(V) →ₗ[ℂ] H^{t'}(V)))ᗮ :=
        Submodule.map_orthogonal_equiv _ e
    _ = (vanishOn t' Ω)ᗮ := by
        rw [orthogonal_tildeSpace_eq_comap e he,
          Submodule.map_comap_eq_of_surjective e.toLinearEquiv.surjective]

/-- **The orthogonal complement of `HTilde^s(Ω)`**: `U ∈ H^s(V)` is orthogonal to `HTilde^s(Ω)` iff
`J_{2s} U ∈ H^{-s}(V)` vanishes on `Ω`. -/
theorem mem_orthogonal_tildeSpace_iff (U : H^{s}(V)) :
    U ∈ (tildeSpace s Ω)ᗮ ↔ besselShift s U ∈ vanishOn (-s) Ω := by
  rw [orthogonal_tildeSpace_eq_comap (besselShift s) toDistr_besselShift_eq_besselPotential_toLp]
  rfl

/-- **`J_{2s}` maps `HTilde^s(Ω)` onto `H^{-s}(Ω)`**: the image of `HTilde^s(Ω)` under
`besselShift s` is
the orthogonal complement of the elements of `H^{-s}(V)` vanishing on `Ω`. -/
theorem map_tildeSpace_besselShift :
    (tildeSpace s Ω).map ((besselShift (V := V) s).toLinearEquiv : H^{s}(V) →ₗ[ℂ] H^{-s}(V)) =
      (vanishOn (-s) Ω)ᗮ :=
  map_tildeSpace_eq_orthogonal (besselShift s) toDistr_besselShift_eq_besselPotential_toLp

/-- **`J_{-2s}` maps `HTilde^{-s}(Ω)` onto `H^s(Ω)`**: the image of `HTilde^{-s}(Ω)` under the
inverse of
`besselShift s` is the orthogonal complement of the elements of `H^s(V)` vanishing on `Ω`. -/
theorem map_tildeSpace_besselShift_symm :
    (tildeSpace (-s) Ω).map
        ((besselShift (V := V) s).symm.toLinearEquiv : H^{-s}(V) →ₗ[ℂ] H^{s}(V)) =
      (vanishOn s Ω)ᗮ :=
  map_tildeSpace_eq_orthogonal (besselShift s).symm toDistr_besselShift_symm

/-- **Elements vanishing on `Ω` pair to zero with `HTilde^s(Ω)`**: for `W ∈ H^{-s}(V)` vanishing on
`Ω` and `U ∈ HTilde^s(Ω)`, `[W, U] = 0`. With `U' = (besselShift s)⁻¹ W`, `[W, U] = ⟪U', U⟫_{H^s}`,
and `U'` is orthogonal to `HTilde^s(Ω)` (`Rd.mem_orthogonal_tildeSpace_iff`). -/
theorem pairing_eq_zero_of_mem_vanishOn_left {W : H^{-s}(V)} (hW : W ∈ vanishOn (-s) Ω)
    {U : H^{s}(V)} (hU : U ∈ tildeSpace s Ω) : pairing s W U = 0 := by
  have h : (besselShift s).symm W ∈ (tildeSpace s Ω)ᗮ := by
    rw [mem_orthogonal_tildeSpace_iff, LinearIsometryEquiv.apply_symm_apply]
    exact hW
  rw [pairing, ← toLp_besselShift_symm W, inner_toLp_toLp]
  exact Submodule.inner_left_of_mem_orthogonal hU h

/-- **`HTilde^{-s}(Ω)` pairs to zero with the elements vanishing on `Ω`**: for `W ∈
HTilde^{-s}(Ω)` and
`U ∈ H^s(V)` vanishing on `Ω`, `[W, U] = 0`, since `(besselShift s)⁻¹ W` lies in the orthogonal
complement of the elements vanishing on `Ω` (`Rd.map_tildeSpace_besselShift_symm`). -/
theorem pairing_eq_zero_of_mem_vanishOn_right {W : H^{-s}(V)} (hW : W ∈ tildeSpace (-s) Ω)
    {U : H^{s}(V)} (hU : U ∈ vanishOn s Ω) : pairing s W U = 0 := by
  have h : (besselShift s).symm W ∈ (vanishOn s Ω)ᗮ := by
    rw [← map_tildeSpace_besselShift_symm]
    exact Submodule.mem_map_of_mem hW
  rw [pairing, ← toLp_besselShift_symm W, inner_toLp_toLp]
  exact Submodule.inner_left_of_mem_orthogonal hU h

/-! ### `HTilde^s(Ω) ≅ H^{-s}(Ω)` -/

variable (s Ω) in
/-- **`HTilde^s(Ω) ≅ H^{-s}(Ω)` by `J_{2s}`**: for every open set `Ω` and every real `s`,
`besselShift s` restricts to an isometric isomorphism of `HTilde^s(Ω)` onto `H^{-s}(Ω)`
(`Rd.map_tildeSpace_besselShift`, Mathlib's `LinearIsometryEquiv.submoduleMap`). -/
noncomputable def tildeEquivRestriction : tildeSpace s Ω ≃ₗᵢ[ℂ] RestrictionSpace (-s) Ω :=
  ((besselShift s).submoduleMap (tildeSpace s Ω)).trans
    (LinearIsometryEquiv.ofEq _ _ map_tildeSpace_besselShift)

/-- `tildeEquivRestriction s Ω U` is `besselShift s U`. -/
theorem coe_tildeEquivRestriction_apply (U : tildeSpace s Ω) :
    (tildeEquivRestriction s Ω U : H^{-s}(V)) = besselShift s U :=
  rfl

variable (s Ω) in
/-- **`H^s(Ω) ≅ HTilde^{-s}(Ω)` by `J_{2s}`**: for every open set `Ω` and every real `s`,
`besselShift s` restricts to an isometric isomorphism of `H^s(Ω)` onto `HTilde^{-s}(Ω)`, the inverse
of the restriction of `(besselShift s)⁻¹` to `HTilde^{-s}(Ω)`
(`Rd.map_tildeSpace_besselShift_symm`). -/
noncomputable def restrictionEquivTilde : RestrictionSpace s Ω ≃ₗᵢ[ℂ] tildeSpace (-s) Ω :=
  (((besselShift s).symm.submoduleMap (tildeSpace (-s) Ω)).trans
    (LinearIsometryEquiv.ofEq _ _ map_tildeSpace_besselShift_symm)).symm

/-- `restrictionEquivTilde s Ω u` is `besselShift s u`. -/
theorem coe_restrictionEquivTilde_apply (u : RestrictionSpace s Ω) :
    (restrictionEquivTilde s Ω u : H^{-s}(V)) = besselShift s u := by
  have h : ((restrictionEquivTilde s Ω).symm (restrictionEquivTilde s Ω u) : H^{s}(V)) =
      (besselShift s).symm (restrictionEquivTilde s Ω u) :=
    rfl
  rw [LinearIsometryEquiv.symm_apply_apply] at h
  rw [h, LinearIsometryEquiv.apply_symm_apply]

/-! ### The dual of `HTilde^s(Ω)` -/

variable (s Ω) in
/-- **The dual of `HTilde^s(Ω)` is `H^{-s}(Ω)`**: for every open set `Ω` and every real `s`, every
bounded functional `ℓ` on `HTilde^s(Ω)` is `U ↦ [W, U]` for exactly one `W ∈ H^{-s}(Ω)`
(`Rd.dualEquiv_apply`, `Rd.dualEquiv_eq_iff`), with `‖W‖ = ‖ℓ‖`, and every extension of `W` to
`V` gives the same pairing (`Rd.dualEquiv_apply_of_restrictProj_eq`); this is Theorem 3.3 of
Chandler-Wilde, Hewett and Moiola with the sesquilinear pairing. The map `ℓ ↦ W` is Riesz's
representation (Mathlib's `InnerProductSpace.toDual`) followed by `Rd.tildeEquivRestriction`,
conjugate-linear and isometric. -/
noncomputable def dualEquiv : StrongDual ℂ (tildeSpace s Ω) ≃ₗᵢ⋆[ℂ] RestrictionSpace (-s) Ω :=
  (InnerProductSpace.toDual ℂ (tildeSpace s Ω)).symm.trans (tildeEquivRestriction s Ω)

/-- **`ℓ` is the pairing with `dualEquiv s Ω ℓ`**: `ℓ(U) = [W, U]` for `W = dualEquiv s Ω ℓ` and
every `U ∈ HTilde^s(Ω)` (Mathlib's `InnerProductSpace.toDual_symm_apply`,
`Rd.pairing_besselShift`). -/
theorem dualEquiv_apply (ℓ : StrongDual ℂ (tildeSpace s Ω)) (U : tildeSpace s Ω) :
    ℓ U = pairing s (dualEquiv s Ω ℓ : H^{-s}(V)) (U : H^{s}(V)) := by
  rw [← InnerProductSpace.toDual_symm_apply, Submodule.coe_inner, dualEquiv,
    LinearIsometryEquiv.trans_apply, coe_tildeEquivRestriction_apply, pairing_besselShift]

/-- The functional of `W ∈ H^{-s}(Ω)` is `U ↦ [W, U]`. -/
theorem dualEquiv_symm_apply (W : RestrictionSpace (-s) Ω) (U : tildeSpace s Ω) :
    (dualEquiv s Ω).symm W U = pairing s (W : H^{-s}(V)) (U : H^{s}(V)) := by
  rw [dualEquiv_apply, LinearIsometryEquiv.apply_symm_apply]

/-- **Uniqueness of the representing element**: `dualEquiv s Ω ℓ = W` iff `ℓ(U) = [W, U]` for
every `U ∈ HTilde^s(Ω)` (Mathlib's `LinearIsometryEquiv.eq_symm_apply`). -/
theorem dualEquiv_eq_iff (ℓ : StrongDual ℂ (tildeSpace s Ω)) (W : RestrictionSpace (-s) Ω) :
    dualEquiv s Ω ℓ = W ↔
      ∀ U : tildeSpace s Ω, ℓ U = pairing s (W : H^{-s}(V)) (U : H^{s}(V)) := by
  rw [← LinearIsometryEquiv.eq_symm_apply, ContinuousLinearMap.ext_iff]
  simp only [dualEquiv_symm_apply]

/-- `‖dualEquiv s Ω ℓ‖ = ‖ℓ‖`. -/
theorem norm_dualEquiv (ℓ : StrongDual ℂ (tildeSpace s Ω)) : ‖dualEquiv s Ω ℓ‖ = ‖ℓ‖ :=
  LinearIsometryEquiv.norm_map _ _

/-- **Every extension represents `ℓ`**: if `W ∈ H^{-s}(V)` restricts to `dualEquiv s Ω ℓ`, then
`ℓ(U) = [W, U]` for every `U ∈ HTilde^s(Ω)`. `W` and its restriction differ by an element vanishing
on `Ω` (`Rd.sub_restrictProj_mem`), which pairs to zero with `HTilde^s(Ω)`
(`Rd.pairing_eq_zero_of_mem_vanishOn_left`). -/
theorem dualEquiv_apply_of_restrictProj_eq (ℓ : StrongDual ℂ (tildeSpace s Ω))
    (U : tildeSpace s Ω) {W : H^{-s}(V)} (hW : restrictProj (-s) Ω W = dualEquiv s Ω ℓ) :
    ℓ U = pairing s W (U : H^{s}(V)) := by
  have h := pairing_eq_zero_of_mem_vanishOn_left (sub_restrictProj_mem W) U.2
  rw [pairing_sub_left, sub_eq_zero, hW] at h
  rw [dualEquiv_apply, h]

/-! ### The duals of `H^s(Ω)` and `H^1_0(Ω)` -/

variable (s Ω) in
/-- **The dual of `H^s(Ω)` is `HTilde^{-s}(Ω)`**: for every open set `Ω` and every real `s`, every
bounded functional `ℓ` on `H^s(Ω)` is `u ↦ [W, u]` for exactly one `W ∈ HTilde^{-s}(Ω)`
(`Rd.dualRestrictionEquiv_apply`, `Rd.dualRestrictionEquiv_eq_iff`), with `‖W‖ = ‖ℓ‖`, and
`ℓ(U|_Ω) = [W, U]` for every `U ∈ H^s(V)` (`Rd.dualRestrictionEquiv_apply_restrictProj`):
Riesz's representation followed by `Rd.restrictionEquivTilde`, conjugate-linear and isometric. -/
noncomputable def dualRestrictionEquiv :
    StrongDual ℂ (RestrictionSpace s Ω) ≃ₗᵢ⋆[ℂ] tildeSpace (-s) Ω :=
  (InnerProductSpace.toDual ℂ (RestrictionSpace s Ω)).symm.trans (restrictionEquivTilde s Ω)

/-- **`ℓ` is the pairing with `dualRestrictionEquiv s Ω ℓ`**: `ℓ(u) = [W, u]` for
`W = dualRestrictionEquiv s Ω ℓ` and every `u ∈ H^s(Ω)`. -/
theorem dualRestrictionEquiv_apply (ℓ : StrongDual ℂ (RestrictionSpace s Ω))
    (u : RestrictionSpace s Ω) :
    ℓ u = pairing s (dualRestrictionEquiv s Ω ℓ : H^{-s}(V)) (u : H^{s}(V)) := by
  rw [← InnerProductSpace.toDual_symm_apply, Submodule.coe_inner, dualRestrictionEquiv,
    LinearIsometryEquiv.trans_apply, coe_restrictionEquivTilde_apply, pairing_besselShift]

/-- The functional of `W ∈ HTilde^{-s}(Ω)` is `u ↦ [W, u]`. -/
theorem dualRestrictionEquiv_symm_apply (W : tildeSpace (-s) Ω) (u : RestrictionSpace s Ω) :
    (dualRestrictionEquiv s Ω).symm W u = pairing s (W : H^{-s}(V)) (u : H^{s}(V)) := by
  rw [dualRestrictionEquiv_apply, LinearIsometryEquiv.apply_symm_apply]

/-- **Uniqueness of the representing element**: `dualRestrictionEquiv s Ω ℓ = W` iff
`ℓ(u) = [W, u]` for every `u ∈ H^s(Ω)`. -/
theorem dualRestrictionEquiv_eq_iff (ℓ : StrongDual ℂ (RestrictionSpace s Ω))
    (W : tildeSpace (-s) Ω) :
    dualRestrictionEquiv s Ω ℓ = W ↔
      ∀ u : RestrictionSpace s Ω, ℓ u = pairing s (W : H^{-s}(V)) (u : H^{s}(V)) := by
  rw [← LinearIsometryEquiv.eq_symm_apply, ContinuousLinearMap.ext_iff]
  simp only [dualRestrictionEquiv_symm_apply]

/-- **The pairing with every extension**: `ℓ(U|_Ω) = [W, U]` for `W = dualRestrictionEquiv s Ω ℓ`
and every `U ∈ H^s(V)`. `U` and its restriction differ by an element vanishing on `Ω`
(`Rd.sub_restrictProj_mem`), which pairs to zero with `HTilde^{-s}(Ω)`
(`Rd.pairing_eq_zero_of_mem_vanishOn_right`). -/
theorem dualRestrictionEquiv_apply_restrictProj (ℓ : StrongDual ℂ (RestrictionSpace s Ω))
    (U : H^{s}(V)) :
    ℓ (restrictProj s Ω U) = pairing s (dualRestrictionEquiv s Ω ℓ : H^{-s}(V)) U := by
  have h := pairing_eq_zero_of_mem_vanishOn_right (dualRestrictionEquiv s Ω ℓ).2
    (sub_restrictProj_mem (Ω := Ω) U)
  rw [pairing_sub_right, sub_eq_zero] at h
  rw [dualRestrictionEquiv_apply, h]

variable (Ω) in
/-- **The dual of `H^1_0(Ω)` is `H^{-1}(Ω)`**: for every open set `Ω`, every bounded functional `ℓ`
on `H^1_0(Ω)` is `u ↦ [W, u]` for exactly one `W ∈ H^{-1}(Ω)` (`Rd.dualZeroBoundaryEquiv_apply`,
`Rd.dualZeroBoundaryEquiv_eq_iff`), with `‖W‖ = ‖ℓ‖`. Inside `H^1(V)`, `H^1_0(Ω)` is `HTilde^1(Ω)`
(`Rd.coe_tildeEquivZeroBoundary_symm_apply`), so `W` is paired with `u` itself. -/
noncomputable def dualZeroBoundaryEquiv :
    StrongDual ℂ (zeroBoundarySpace 1 Ω) ≃ₗᵢ⋆[ℂ] RestrictionSpace (-1) Ω :=
  (InnerProductSpace.toDual ℂ (zeroBoundarySpace 1 Ω)).symm.trans
    ((tildeEquivZeroBoundary Ω).symm.trans (tildeEquivRestriction 1 Ω))

/-- **`ℓ` is the pairing with `dualZeroBoundaryEquiv Ω ℓ`**: `ℓ(u) = [W, u]` for
`W = dualZeroBoundaryEquiv Ω ℓ` and every `u ∈ H^1_0(Ω)`, read as an element of `H^1(V)`. The
isometry `Rd.tildeEquivZeroBoundary` preserves inner products, and its inverse is the identity
inside `H^1(V)` (`Rd.coe_tildeEquivZeroBoundary_symm_apply`). -/
theorem dualZeroBoundaryEquiv_apply (ℓ : StrongDual ℂ (zeroBoundarySpace 1 Ω))
    (u : zeroBoundarySpace 1 Ω) :
    ℓ u = pairing 1 (dualZeroBoundaryEquiv Ω ℓ : H^{-1}(V))
      ((u : RestrictionSpace 1 Ω) : H^{1}(V)) := by
  have h := InnerProductSpace.toDual_symm_apply (𝕜 := ℂ) (E := zeroBoundarySpace 1 Ω) (x := u)
    (y := ℓ)
  rw [← h, ← LinearIsometryEquiv.inner_map_map (tildeEquivZeroBoundary Ω).symm,
    Submodule.coe_inner, dualZeroBoundaryEquiv, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.trans_apply, coe_tildeEquivRestriction_apply, pairing_besselShift,
    coe_tildeEquivZeroBoundary_symm_apply u]

/-- The functional of `W ∈ H^{-1}(Ω)` on `H^1_0(Ω)` is `u ↦ [W, u]`. -/
theorem dualZeroBoundaryEquiv_symm_apply (W : RestrictionSpace (-1) Ω)
    (u : zeroBoundarySpace 1 Ω) :
    (dualZeroBoundaryEquiv Ω).symm W u =
      pairing 1 (W : H^{-1}(V)) ((u : RestrictionSpace 1 Ω) : H^{1}(V)) := by
  rw [dualZeroBoundaryEquiv_apply, LinearIsometryEquiv.apply_symm_apply]

/-- **Uniqueness of the representing element**: `dualZeroBoundaryEquiv Ω ℓ = W` iff
`ℓ(u) = [W, u]` for every `u ∈ H^1_0(Ω)`. -/
theorem dualZeroBoundaryEquiv_eq_iff (ℓ : StrongDual ℂ (zeroBoundarySpace 1 Ω))
    (W : RestrictionSpace (-1) Ω) :
    dualZeroBoundaryEquiv Ω ℓ = W ↔ ∀ u : zeroBoundarySpace 1 Ω,
      ℓ u = pairing 1 (W : H^{-1}(V)) ((u : RestrictionSpace 1 Ω) : H^{1}(V)) := by
  rw [← LinearIsometryEquiv.eq_symm_apply, ContinuousLinearMap.ext_iff]
  simp only [dualZeroBoundaryEquiv_symm_apply]

end Rd
