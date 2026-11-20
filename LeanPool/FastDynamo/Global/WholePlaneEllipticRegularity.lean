/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Analysis.FourierMultiplierSub
public import LeanPool.FastDynamo.Global.ConstantCoefficientBackgroundResolvent
public import LeanPool.FastDynamo.Analysis.ComplexForm
public import LeanPool.FastDynamo.Operator.AssociatedForm

/-!
# Whole-plane `H²` regularity for the constant-coefficient equation

Whole-plane `L²` elliptic regularity, proved directly in the repository's weak-jet model.

* A conjugated Schwartz test function, bundled with its exact weak `H¹` jet
  (`wholePlaneSchwartzConjH1`), converts a variational identity into an identity of tempered
  distributions: testing an `L²` field against it reproduces the associated tempered
  distribution, and the gradient pairings give minus the distributional Laplacian.
* Consequently a weak `H¹` solution of `(-epsilon * Δ + mu) g = f`, in the sense of
  `IsConstantCoefficientWeakResolventSolution`, has distributional Laplacian equal to the `L²`
  datum `epsilon⁻¹ (mu g - f)` (`laplacian_toTempered_eq_of_constantCoefficientWeak`).
* If the distributional Laplacian of an `L²` field is represented by `L²` data, the field has a
  unique `H²` lift whose stored Laplacian is that datum
  (`exists_wholePlaneH2_of_laplacian_eq_l2`); the normalized Bessel identity
  `J² T = T - (2π)⁻² ΔT` constructs the lift.

`Local/HorizontalFormStrongIdentification.lean` and `Local/HorizontalSeedResolventH2.lean` use
these to identify the weak solutions of the local seed problem as strong `H²` solutions.
-/

@[expose] public section

open MeasureTheory
open scoped LineDeriv SchwartzMap
noncomputable section
namespace FastDynamo

open ConstantCoefficientBackground

/-- Complex conjugation of a scalar whole-plane Schwartz test function. -/
def wholePlaneSchwartzConj (f : SchwartzMap WholePlane ℂ) :=
  f.postcompCLM (𝕜 := ℝ) Complex.conjCLE.toContinuousLinearMap

/-- Differentiation commutes with conjugation of a Schwartz test function:
`∂_j (conj f) = conj (∂_j f)` pointwise. -/
theorem lineDeriv_wholePlaneSchwartzConj (f : SchwartzMap WholePlane ℂ)
    (j : Fin 2) (x : WholePlane) :
    (∂_{wholePlaneBasis j} (wholePlaneSchwartzConj f)) x =
      star ((∂_{wholePlaneBasis j} f) x) := by
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have h := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp x (f.hasFDerivAt x)
  have hfd := h.fderiv
  change (fderiv ℝ (Complex.conjCLE.toContinuousLinearMap ∘ (f : _ → _)) x)
      (wholePlaneBasis j) = _
  rw [hfd]
  exact Complex.conjCLE_apply _

/-- The conjugated Schwartz test bundled with its exact weak `H¹` jet. -/
def wholePlaneSchwartzConjH1 (f : SchwartzMap WholePlane ℂ) :
    WholePlaneScalarH1 :=
  wholePlaneH1OfWeakDerivatives ℂ
    ((wholePlaneSchwartzConj f).toLp 2 volume)
    (fun j => (∂_{wholePlaneBasis j} (wholePlaneSchwartzConj f)).toLp 2 volume)
    (by
      intro j
      rw [wholePlaneL2ToTempered_apply,
        Lp.toTemperedDistribution_toLp_eq,
        wholePlaneL2ToTempered_apply,
        Lp.toTemperedDistribution_toLp_eq]
      exact TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq
        (wholePlaneSchwartzConj f) (wholePlaneBasis j))

/-- The `L²` value of the bundled conjugated Schwartz test is the `L²` class of `conj f`. -/
theorem wholePlaneH1Embedding_schwartzConjH1
    (f : SchwartzMap WholePlane ℂ) :
    wholePlaneH1Embedding ℂ (wholePlaneSchwartzConjH1 f) =
      (wholePlaneSchwartzConj f).toLp 2 volume := by
  rfl

/-- The `j`-th weak derivative of the bundled conjugated Schwartz test is the `L²` class of
`∂_j (conj f)`. -/
theorem wholePlaneH1FirstDerivative_schwartzConjH1
    (f : SchwartzMap WholePlane ℂ) (j : Fin 2) :
    wholePlaneH1FirstDerivative ℂ j (wholePlaneSchwartzConjH1 f) =
      (∂_{wholePlaneBasis j} (wholePlaneSchwartzConj f)).toLp 2 volume := by
  rfl

/-- Pointwise value of the conjugated Schwartz test function. -/
@[simp] theorem wholePlaneSchwartzConj_apply
    (f : SchwartzMap WholePlane ℂ) (x : WholePlane) :
    wholePlaneSchwartzConj f x = star (f x) := by
  exact Complex.conjCLE_apply _

/-- Testing an `L²` field against the conjugated Schwartz test in the Hermitian inner product
reproduces the value of the associated tempered distribution at `f`; the conjugation cancels the
conjugate-linearity of the first slot. -/
theorem inner_schwartzConjH1_eq_tempered_apply
    (f : SchwartzMap WholePlane ℂ) (q : WholePlaneScalarL2) :
    inner ℂ (wholePlaneH1Embedding ℂ (wholePlaneSchwartzConjH1 f)) q =
      (wholePlaneL2ToTempered ℂ q) f := by
  rw [wholePlaneH1Embedding_schwartzConjH1,
    MeasureTheory.L2.inner_def, wholePlaneL2ToTempered_apply,
    MeasureTheory.Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [(wholePlaneSchwartzConj f).coeFn_toLp 2 volume]
    with x hx
  rw [hx, wholePlaneSchwartzConj_apply]
  simp [RCLike.inner_apply]
  ring

/-- Summing the gradient pairings against the conjugated Schwartz test yields minus the
distributional Laplacian of `g` evaluated at `f`; this converts the variational form into a
tempered-distribution identity. -/
theorem gradientPair_schwartzConjH1_eq_neg_laplacian_apply
    (g : WholePlaneScalarH1) (f : SchwartzMap WholePlane ℂ) :
    ∑ j : Fin 2,
        inner ℂ (wholePlaneH1FirstDerivative ℂ j
          (wholePlaneSchwartzConjH1 f))
          (wholePlaneH1FirstDerivative ℂ j g) =
      -(Laplacian.laplacian
        (wholePlaneL2ToTempered ℂ (wholePlaneH1Embedding ℂ g))) f := by
  rw [TemperedDistribution.laplacian_eq_sum wholePlaneOrthonormalBasis]
  simp only [Fin.sum_univ_two, wholePlaneOrthonormalBasis_apply]
  rw [wholePlaneH1_firstDerivative_distribution ℂ g 0,
    wholePlaneH1_firstDerivative_distribution ℂ g 1]
  simp only [add_apply, neg_apply,
    TemperedDistribution.lineDerivOp_apply_apply,
    wholePlaneL2ToTempered_apply, MeasureTheory.Lp.toTemperedDistribution_apply,
    wholePlaneH1FirstDerivative_schwartzConjH1,
    MeasureTheory.L2.inner_def]
  have hpair (j : Fin 2) :
      (∫ a : WholePlane,
        inner ℂ
          (((∂_{wholePlaneBasis j} (wholePlaneSchwartzConj f)).toLp
            2 volume) a)
          ((wholePlaneH1FirstDerivative ℂ j g) a)) =
        ∫ a : WholePlane,
          (∂_{wholePlaneBasis j} f) a •
            (wholePlaneH1FirstDerivative ℂ j g) a := by
    apply integral_congr_ae
    filter_upwards [
      (∂_{wholePlaneBasis j} (wholePlaneSchwartzConj f)).coeFn_toLp 2 volume]
      with x hx
    rw [hx, lineDeriv_wholePlaneSchwartzConj]
    simp [RCLike.inner_apply]
    ring
  rw [hpair 0, hpair 1]
  simp only [neg_smul, integral_neg]
  abel

/-- The literal L² datum represented by the Laplacian in the strong
constant-coefficient equation. -/
def constantCoefficientLaplacianDatum
    (epsilon : ℝ) (mu : ℂ) (f q : WholePlaneScalarL2) :
    WholePlaneScalarL2 :=
  ((epsilon : ℂ)⁻¹) • (mu • q - f)

/-- A weak `H¹` solution of `(-epsilon Δ + mu) g = f` has distributional Laplacian equal to the
`L²` datum `epsilon⁻¹ (mu g - f)`.  This is the elliptic-regularity input that produces the `H²`
lift. -/
theorem laplacian_toTempered_eq_of_constantCoefficientWeak
    {epsilon : ℝ} {mu : ℂ} {f : WholePlaneScalarL2}
    {g : WholePlaneScalarH1} (hepsilon : epsilon ≠ 0)
    (hweak : IsConstantCoefficientWeakResolventSolution epsilon mu f g) :
    Laplacian.laplacian
        (wholePlaneL2ToTempered ℂ (wholePlaneH1Embedding ℂ g)) =
      wholePlaneL2ToTempered ℂ
        (constantCoefficientLaplacianDatum epsilon mu f
          (wholePlaneH1Embedding ℂ g)) := by
  ext phi
  have hw := hweak (wholePlaneSchwartzConjH1 phi)
  rw [constantCoefficientWeakForm,
    gradientPair_schwartzConjH1_eq_neg_laplacian_apply,
    inner_schwartzConjH1_eq_tempered_apply,
    inner_schwartzConjH1_eq_tempered_apply] at hw
  rw [constantCoefficientLaplacianDatum, map_smul, map_sub, map_smul]
  simp only [smul_apply, sub_apply]
  have hepsilonC : (epsilon : ℂ) ≠ 0 := by exact_mod_cast hepsilon
  calc
    _ = (mu * (wholePlaneL2ToTempered ℂ
          (wholePlaneH1Embedding ℂ g)) phi -
          (wholePlaneL2ToTempered ℂ f) phi) / (epsilon : ℂ) := by
      apply (eq_div_iff hepsilonC).2
      linear_combination -hw
    _ = (epsilon : ℂ)⁻¹ *
        (mu * (wholePlaneL2ToTempered ℂ
          (wholePlaneH1Embedding ℂ g)) phi -
          (wholePlaneL2ToTempered ℂ f) phi) := by
      rw [div_eq_mul_inv]
      ring

/-- Whole-plane L² elliptic regularity in the exact weak-jet model: if the
distributional Laplacian of an L² field is represented by L² data, then the
field has a unique H² lift whose stored Laplacian is that datum. -/
theorem exists_wholePlaneH2_of_laplacian_eq_l2
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (b0 lap : WholePlaneL2 F)
    (hlap : Laplacian.laplacian (wholePlaneL2ToTempered F b0) =
      wholePlaneL2ToTempered F lap) :
    ∃ b : WholePlaneH2 F,
      wholePlaneH2Embedding F b = b0 ∧
        wholePlaneLaplacian F b = lap := by
  let T : TemperedDistribution WholePlane F := wholePlaneL2ToTempered F b0
  let alpha : ℝ := ((2 * Real.pi) ^ 2)⁻¹
  have halpha : alpha * (-(2 * Real.pi) ^ 2) = -1 := by
    dsimp [alpha]
    have hpi : (2 * Real.pi) ^ 2 ≠ 0 :=
      pow_ne_zero 2 (mul_ne_zero (by norm_num) Real.pi_ne_zero)
    field_simp
  have hbessel :
      TemperedDistribution.besselPotential WholePlane F 2 T =
        T - alpha • Laplacian.laplacian T := by
    rw [TemperedDistribution.besselPotential,
      TemperedDistribution.laplacian_eq_fourierMultiplierCLM]
    have hsymbol :
        (fun xi : WholePlane =>
          (((1 + ‖xi‖ ^ 2) ^ ((2 : ℝ) / 2) : ℝ) : ℂ)) =
          (fun _ : WholePlane => (1 : ℂ)) -
            (-1 : ℂ) •
              (fun xi : WholePlane => ((‖xi‖ ^ 2 : ℝ) : ℂ)) := by
      funext xi
      norm_num
    rw [hsymbol,
      fourierMultiplierCLM_sub (by fun_prop) (by fun_prop),
      TemperedDistribution.fourierMultiplierCLM_const,
      TemperedDistribution.fourierMultiplierCLM_smul (by fun_prop)]
    simp only [sub_apply, smul_apply, ContinuousLinearMap.id_apply]
    rw [smul_smul, halpha]
    simp
  have hbp0 : TemperedDistribution.MemSobolev 0 2
      (TemperedDistribution.besselPotential WholePlane F 2 T) := by
    rw [hbessel]
    change TemperedDistribution.MemSobolev 0 2
      (wholePlaneL2ToTempered F b0 - alpha •
        Laplacian.laplacian (wholePlaneL2ToTempered F b0))
    rw [hlap]
    have halphalap :
        alpha • wholePlaneL2ToTempered F lap =
          wholePlaneL2ToTempered F ((alpha : ℂ) • lap) := by
      change (alpha : ℂ) • wholePlaneL2ToTempered F lap = _
      exact ((wholePlaneL2ToTempered F).map_smul (alpha : ℂ) lap).symm
    rw [halphalap, ← map_sub]
    exact TemperedDistribution.memSobolev_zero_iff.mpr
      ⟨b0 - (alpha : ℂ) • lap, rfl⟩
  have hSob : TemperedDistribution.MemSobolev 2 2 T := by
    simpa only [add_zero] using
      (TemperedDistribution.memSobolev_besselPotential_iff
        (s := 0) (r := 2) (f := T)).mp hbp0
  have hfirst (j : Fin 2) : ∃ db : WholePlaneL2 F,
      ∂_{wholePlaneBasis j} T = wholePlaneL2ToTempered F db := by
    apply TemperedDistribution.memSobolev_zero_iff.mp
    have hj := hSob.lineDerivOp (m := wholePlaneBasis j)
    exact hj.mono (by norm_num)
  choose db hdb using hfirst
  have hsecond (j k : Fin 2) : ∃ ddb : WholePlaneL2 F,
      ∂_{wholePlaneBasis k} (∂_{wholePlaneBasis j} T) =
        wholePlaneL2ToTempered F ddb := by
    apply TemperedDistribution.memSobolev_zero_iff.mp
    have hj := hSob.lineDerivOp (m := wholePlaneBasis j)
    have hjk := hj.lineDerivOp (m := wholePlaneBasis k)
    rw [show (2 : ℝ) - 1 - 1 = 0 by norm_num] at hjk
    exact hjk
  choose ddb hddb using hsecond
  let b : WholePlaneH2 F := wholePlaneH2OfWeakDerivatives F b0 db ddb
    (fun j => by simpa only [T] using hdb j)
    (fun j k => by rw [← hdb j]; exact hddb j k)
  refine ⟨b, wholePlaneH2Embedding_ofWeakDerivatives F b0 db ddb _ _, ?_⟩
  apply wholePlaneL2ToTempered_injective F
  rw [wholePlaneLaplacian_toTempered]
  change Laplacian.laplacian (wholePlaneL2ToTempered F b0) =
    wholePlaneL2ToTempered F lap
  exact hlap

end FastDynamo
