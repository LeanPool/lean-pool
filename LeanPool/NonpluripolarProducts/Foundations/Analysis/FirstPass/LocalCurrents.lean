/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.RegularDistribution
public import Mathlib.Analysis.Normed.Module.Alternating.Basic
public import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Local currents and differential forms with distribution coefficients

`LocalCurrent Ω k` is the continuous dual of test forms of degree `dim ℝ E - k`.
`DistributionForm Ω k` instead stores an alternating `k`-form whose coefficients
are actual continuous scalar test functionals. The two types are not identified:
passing between them uses an oriented volume form and the complementary-degree
wedge pairing, which is not constructed here. A scalar distribution alone is
neither an arbitrary two-form nor an arbitrary current of unspecified degree.

The coefficient exterior derivative uses actual infinite-order distributional
derivatives. Our normalization is that of the revised manuscript:
`dᶜu(v) = -D_(Iv)u / (4π)` and `ddᶜ = i ∂∂bar / (2π)`.
Commutation, type `(1,1)`, and closedness are separate Pending obligations.
-/

@[expose] public section

noncomputable section

open TopologicalSpace
open scoped Distributions

namespace SGPT.Foundations.Analysis.LocalCurrents

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (Ω : Opens E)

/-- A test `q`-form on an open subset of a real vector space. -/
abbrev TestForm (q : ℕ) := 𝓓(Ω, E [⋀^Fin q]→L[ℝ] ℝ)

/-- A degree-`k` current acts on test forms of complementary degree.
The bounded index prevents truncated subtraction from admitting invalid degrees. -/
abbrev LocalCurrent (k : Fin (Module.finrank ℝ E + 1)) :=
  TestForm Ω (Module.finrank ℝ E - k.val) →L[ℝ] ℝ

/-- An alternating form with genuine distribution coefficients. In finite
dimension it has finitely many scalar distribution coefficients in every basis.
No positivity, closedness, or existence of a density is built into this type. -/
abbrev DistributionForm (k : ℕ) := E [⋀^Fin k]→ₗ[ℝ] 𝓓'(Ω, ℝ)

variable {Ω}

/-- In a finite basis the coefficient array is itself a continuous test
functional with values in a finite-dimensional real vector space. -/
def coordinateDistribution {k m : ℕ} (b : Module.Basis (Fin m) ℝ E)
    (A : DistributionForm Ω k) : 𝓓'(Ω, (Fin k → Fin m) → ℝ) where
  toFun φ I := A (fun j => b (I j)) φ
  map_add' φ ψ := by ext I; exact map_add _ φ ψ
  map_smul' c φ := by ext I; exact map_smul _ c φ
  cont := continuous_pi (fun I => (A (fun j => b (I j))).continuous)

@[simp] theorem coordinateDistribution_apply {k m : ℕ} (b : Module.Basis (Fin m) ℝ E)
    (A : DistributionForm Ω k) (φ : 𝓓(Ω, ℝ)) (I : Fin k → Fin m) :
    coordinateDistribution b A φ I = A (fun j => b (I j)) φ := rfl

/-- Pointwise products are genuine smooth compactly supported test functions. -/
def testProduct (φ ψ : 𝓓(Ω, ℝ)) : 𝓓(Ω, ℝ) where
  toFun x := φ x * ψ x
  contDiff' := φ.contDiff.mul ψ.contDiff
  hasCompactSupport' := φ.hasCompactSupport.mul_right
  tsupport_subset' := tsupport_mul_subset_left.trans φ.tsupport_subset

@[simp] theorem testProduct_apply (φ ψ : 𝓓(Ω, ℝ)) (x : E) :
    testProduct φ ψ x = φ x * ψ x := rfl

/-- Directional differentiation is linear in its direction. All distribution
orders are `⊤`, so mathlib's insufficient-order fallback cannot apply. -/
def directionalLM : E →ₗ[ℝ] (𝓓'(Ω, ℝ) →ₗ[ℝ] 𝓓'(Ω, ℝ)) where
  toFun v := (Distribution.lineDerivCLM (n := ⊤) (k := ⊤) v).toLinearMap
  map_add' v w := by
    ext T φ
    simp [Distribution.lineDerivCLM_add]
  map_smul' c v := by
    ext T φ
    simp [Distribution.lineDerivCLM_smul]

@[simp] theorem directionalLM_apply (v : E) (T : 𝓓'(Ω, ℝ)) :
    directionalLM v T = Distribution.lineDerivCLM (n := ⊤) (k := ⊤) v T := rfl

/-- Differentiate every coefficient of a distribution-valued form. -/
def coefficientDerivative {k : ℕ} (A : DistributionForm Ω k) :
    E →ₗ[ℝ] DistributionForm Ω k where
  toFun v := (directionalLM v).compAlternatingMap A
  map_add' v w := by
    ext x φ
    simp [map_add]
  map_smul' c v := by
    ext x φ
    simp [map_smul]

/-- The exterior derivative in constant vector directions, using the usual
alternating sum of distributional coefficient derivatives. -/
def exteriorDerivative {k : ℕ} (A : DistributionForm Ω k) :
    DistributionForm Ω (k + 1) :=
  AlternatingMap.alternatizeUncurryFin (coefficientDerivative A)

theorem exteriorDerivative_apply {k : ℕ} (A : DistributionForm Ω k)
    (v : Fin (k + 1) → E) :
    exteriorDerivative A v = ∑ i : Fin (k + 1), (-1 : ℤ) ^ (i : ℕ) •
      Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (v i) (A (i.removeNth v)) := by
  simp [exteriorDerivative, AlternatingMap.alternatizeUncurryFin_apply,
    coefficientDerivative]

/-- Closedness is vanishing of the actual exterior derivative. -/
def IsClosed {k : ℕ} (A : DistributionForm Ω k) : Prop :=
  exteriorDerivative A = 0

/-- Regard a linear distribution-valued covector as a one-form. -/
def oneForm (L : E →ₗ[ℝ] 𝓓'(Ω, ℝ)) : DistributionForm Ω 1 where
  toFun v := L (v 0)
  map_update_add' v i x y := by fin_cases i; simp
  map_update_smul' v i c x := by fin_cases i; simp
  map_eq_zero_of_eq' v i j _ hij := (hij (Subsingleton.elim i j)).elim

@[simp] theorem oneForm_apply (L : E →ₗ[ℝ] 𝓓'(Ω, ℝ)) (v : Fin 1 → E) :
    oneForm L v = L (v 0) := rfl

theorem exteriorDerivative_oneForm (L : E →ₗ[ℝ] 𝓓'(Ω, ℝ)) (v w : E) :
    exteriorDerivative (oneForm L) ![v, w] =
      Distribution.lineDerivCLM (n := ⊤) (k := ⊤) v (L w) -
      Distribution.lineDerivCLM (n := ⊤) (k := ⊤) w (L v) := by
  simp [exteriorDerivative_apply, Fin.sum_univ_two, Fin.removeNth,
    sub_eq_add_neg]

section Complex

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

/-- The real one-form `dᶜT`, with the manuscript's factor `1/(4π)`. -/
def dc (T : 𝓓'(Ω, ℝ)) : DistributionForm Ω 1 :=
  oneForm
    { toFun := fun v => (-1 / (4 * Real.pi) : ℝ) • directionalLM (Complex.I • v) T
      map_add' := by intros; simp [smul_add]
      map_smul' := by intros; simp [smul_comm Complex.I, smul_smul, mul_comm] }

/-- The real two-form `ddᶜT`, formed by differentiating `dᶜT`. -/
def ddC (T : 𝓓'(Ω, ℝ)) : DistributionForm Ω 2 := exteriorDerivative (dc T)

/-- The full alternating coefficient, not merely the diagonal Levi values. -/
theorem ddC_apply (T : 𝓓'(Ω, ℝ)) (v w : E) :
    ddC T ![v, w] = (-1 / (4 * Real.pi) : ℝ) •
      (Distribution.lineDerivCLM (n := ⊤) (k := ⊤) v
          (Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (Complex.I • w) T) -
        Distribution.lineDerivCLM (n := ⊤) (k := ⊤) w
          (Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (Complex.I • v) T)) := by
  rw [ddC, dc, exteriorDerivative_oneForm]
  simp [smul_sub]

/-- A real distribution-valued two-form has type `(1,1)` when it is invariant
under the complex structure in both arguments. -/
def IsOneOne (A : DistributionForm Ω 2) : Prop :=
  ∀ v w : E, A ![Complex.I • v, Complex.I • w] = A ![v, w]

/-- Positivity on every nonnegative scalar test and every constant complex line.
This definition does not assert positivity on variable test forms. -/
def ConstantDirectionPositive (A : DistributionForm Ω 2) : Prop :=
  ∀ v : E, PositiveDistribution (A ![v, Complex.I • v])

/-- Test positivity on compactly supported variable real vector squares.
This is a coefficient formulation; no identification with the full dual
current space or its complementary-degree positive cone is asserted. -/
def SquarePositive (A : DistributionForm Ω 2) : Prop :=
  ∀ (r : ℕ) (v : Fin r → E) (f : Fin r → 𝓓(Ω, ℝ)),
    0 ≤ ∑ i, ∑ j, A ![v i, Complex.I • v j] (testProduct (f i) (f j))

/-- The normalization bridge: `ddᶜT(v,Iv) = Levi_v(T)/π`. -/
theorem ddC_complexLine (T : 𝓓'(Ω, ℝ)) (v : E) :
    ddC T ![v, Complex.I • v] =
      (1 / Real.pi : ℝ) • distributionalLeviCLM v T := by
  rw [ddC_apply]
  have hJ : Complex.I • (Complex.I • v) = -v := by
    simp [smul_smul]
  rw [hJ, show -v = (-1 : ℝ) • v by simp, Distribution.lineDerivCLM_smul]
  ext φ
  simp [distributionalLeviCLM, smul_sub]
  field_simp
  ring

/-- Nonnegative distributional Levi implies positivity on constant complex lines. -/
theorem constantDirectionPositive_ddC {T : 𝓓'(Ω, ℝ)}
    (hT : HasNonnegativeDistributionalLevi T) : ConstantDirectionPositive (ddC T) := by
  intro v
  rw [ddC_complexLine]
  exact (hT v).smul (le_of_lt (one_div_pos.mpr Real.pi_pos))

end Complex

end SGPT.Foundations.Analysis.LocalCurrents
