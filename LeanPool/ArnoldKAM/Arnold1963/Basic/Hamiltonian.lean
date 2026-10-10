/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Basic.Functions
public import LeanPool.ArnoldKAM.Arnold1963.Basic.SymplecticMatrix
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
Hamiltonian vector fields and canonical pullback, using complex Frechet derivatives and
X_H = (-H_q, H_p). Derivative identities require differentiability or derive it from analyticity.
Canonical maps preserve the specified symplectic form.
-/

@[expose] public section

noncomputable section

open scoped NNReal

namespace KamProject.Arnold1963

/-- The action-coordinate derivatives of a complex Hamiltonian. -/
def pGradient {n : ℕ} (H : ComplexPhaseSpace n → ℂ) (x : ComplexPhaseSpace n) :
    ComplexSpace n := fun j => fderiv ℂ H x (pDirection j)

/-- The angle-coordinate derivatives of a complex Hamiltonian. -/
def qGradient {n : ℕ} (H : ComplexPhaseSpace n → ℂ) (x : ComplexPhaseSpace n) :
    ComplexSpace n := fun j => fderiv ℂ H x (qDirection j)

theorem pGradient_eq_of_hasFDerivAt {n : ℕ} {H : ComplexPhaseSpace n → ℂ}
    {x : ComplexPhaseSpace n} {L : ComplexPhaseSpace n →L[ℂ] ℂ}
    (hH : HasFDerivAt H L x) : pGradient H x = fun j => L (pDirection j) := by
  unfold pGradient
  rw [hH.fderiv]

theorem qGradient_eq_of_hasFDerivAt {n : ℕ} {H : ComplexPhaseSpace n → ℂ}
    {x : ComplexPhaseSpace n} {L : ComplexPhaseSpace n →L[ℂ] ℂ}
    (hH : HasFDerivAt H L x) : qGradient H x = fun j => L (qDirection j) := by
  unfold qGradient
  rw [hH.fderiv]

theorem pGradient_eq_zero_of_not_differentiableAt {n : ℕ}
    {H : ComplexPhaseSpace n → ℂ} {x : ComplexPhaseSpace n}
    (hH : ¬ DifferentiableAt ℂ H x) : pGradient H x = 0 := by
  ext j
  simp [pGradient, fderiv_zero_of_not_differentiableAt hH]

theorem qGradient_eq_zero_of_not_differentiableAt {n : ℕ}
    {H : ComplexPhaseSpace n → ℂ} {x : ComplexPhaseSpace n}
    (hH : ¬ DifferentiableAt ℂ H x) : qGradient H x = 0 := by
  ext j
  simp [qGradient, fderiv_zero_of_not_differentiableAt hH]

/-- Hamilton's vector field with action component `-∂q H` and angle component `∂p H`. -/
def hamiltonianVectorField {n : ℕ} (H : ComplexPhaseSpace n → ℂ)
    (x : ComplexPhaseSpace n) : ComplexPhaseSpace n :=
  (-qGradient H x, pGradient H x)

theorem hamiltonianVectorField_mathlibJ {n : ℕ} (H : ComplexPhaseSpace n → ℂ)
    (x : ComplexPhaseSpace n) :
    phaseCoordinate (hamiltonianVectorField H x) =
      (Matrix.J (Fin n) ℂ).mulVec (phaseCoordinate (pGradient H x, qGradient H x)) := by
  ext i
  cases i <;> simp [phaseCoordinate, hamiltonianVectorField, Matrix.J,
    Matrix.mulVec, dotProduct, Matrix.one_apply]

theorem hamiltonianVectorField_eq_sharp {n : ℕ} (H : ComplexPhaseSpace n → ℂ)
    (x : ComplexPhaseSpace n) :
    hamiltonianVectorField H x = symplecticSharp (fderiv ℂ H x).toLinearMap := rfl

theorem norm_hamiltonianVectorField_le {n : ℕ} (H : ComplexPhaseSpace n → ℂ)
    (x : ComplexPhaseSpace n) : ‖hamiltonianVectorField H x‖ ≤ ‖fderiv ℂ H x‖ := by
  rw [hamiltonianVectorField, phase_norm_eq, norm_neg, max_le_iff]
  constructor
  · apply (complex_norm_le_iff _ (norm_nonneg _)).2
    intro j
    change ‖fderiv ℂ H x (qDirection j)‖ ≤ ‖fderiv ℂ H x‖
    exact (fderiv ℂ H x).unit_le_opNorm (qDirection j) (by simp)
  · apply (complex_norm_le_iff _ (norm_nonneg _)).2
    intro j
    change ‖fderiv ℂ H x (pDirection j)‖ ≤ ‖fderiv ℂ H x‖
    exact (fderiv ℂ H x).unit_le_opNorm (pDirection j) (by simp)

theorem hamiltonianVectorField_actionOnly {n : ℕ} {h : ComplexSpace n → ℂ}
    (x : ComplexPhaseSpace n) (hh : DifferentiableAt ℂ h x.1) :
    hamiltonianVectorField (h ∘ Prod.fst) x =
      (0, fun j => fderiv ℂ h x.1 (Pi.single j 1)) := by
  have hd := hh.hasFDerivAt.comp x (hasFDerivAt_fst (𝕜 := ℂ) (p := x))
  ext j <;> simp [hamiltonianVectorField, pGradient, qGradient, hd.fderiv,
    pDirection, qDirection]

theorem hamiltonianVectorField_add {n : ℕ} {H K : ComplexPhaseSpace n → ℂ}
    {x : ComplexPhaseSpace n} (hH : DifferentiableAt ℂ H x)
    (hK : DifferentiableAt ℂ K x) :
    hamiltonianVectorField (H + K) x =
      hamiltonianVectorField H x + hamiltonianVectorField K x := by
  ext j <;> simp [hamiltonianVectorField, pGradient, qGradient,
    (hH.hasFDerivAt.add hK.hasFDerivAt).fderiv, add_comm]

theorem HasFDerivAt.symplectic_identity {n : ℕ} {H : ComplexPhaseSpace n → ℂ}
    {x : ComplexPhaseSpace n} {L : ComplexPhaseSpace n →L[ℂ] ℂ}
    (hH : HasFDerivAt H L x) (v : ComplexPhaseSpace n) :
    symplecticForm v (hamiltonianVectorField H x) = L v := by
  rw [hamiltonianVectorField_eq_sharp, hH.fderiv]
  exact symplecticForm_sharp L.toLinearMap v

theorem AnalyticPhaseFunction.hasFDerivAt {n : ℕ} {G : Set (ComplexSpace n)}
    {ρ : ℝ≥0} (H : AnalyticPhaseFunction n G ρ) {x : ComplexPhaseSpace n}
    (hx : x ∈ phaseDomain G ρ) : HasFDerivAt H.toFun (fderiv ℂ H.toFun x) x :=
  (H.analytic x hx).differentiableAt.hasFDerivAt

theorem AnalyticPhaseFunction.symplectic_identity {n : ℕ} {G : Set (ComplexSpace n)}
    {ρ : ℝ≥0} (H : AnalyticPhaseFunction n G ρ) {x : ComplexPhaseSpace n}
    (hx : x ∈ phaseDomain G ρ) (v : ComplexPhaseSpace n) :
    symplecticForm v (hamiltonianVectorField H.toFun x) = fderiv ℂ H.toFun x v :=
  HasFDerivAt.symplectic_identity (H.hasFDerivAt hx) v

/-- Differentiability and symplecticity of a transformation's derivative at one point. -/
def CanonicalAt {n : ℕ} (B : ComplexPhaseSpace n → ComplexPhaseSpace n)
    (x : ComplexPhaseSpace n) : Prop :=
  DifferentiableAt ℂ B x ∧ IsSymplecticLinear (fderiv ℂ B x).toLinearMap

/-- Pointwise canonicality of a phase transformation throughout a set. -/
def CanonicalOn {n : ℕ} (B : ComplexPhaseSpace n → ComplexPhaseSpace n)
    (S : Set (ComplexPhaseSpace n)) : Prop := ∀ x ∈ S, CanonicalAt B x

theorem canonicalAt_id {n : ℕ} (x : ComplexPhaseSpace n) : CanonicalAt id x := by
  refine ⟨differentiableAt_id, ?_⟩
  intro v w
  simp [fderiv_id]

theorem CanonicalAt.derivative_bijective {n : ℕ}
    {B : ComplexPhaseSpace n → ComplexPhaseSpace n} {x : ComplexPhaseSpace n}
    (hB : CanonicalAt B x) : Function.Bijective (fderiv ℂ B x) :=
  ⟨hB.2.injective, hB.2.surjective⟩

theorem CanonicalAt.matrix_identity {n : ℕ}
    {B : ComplexPhaseSpace n → ComplexPhaseSpace n} {x : ComplexPhaseSpace n}
    (hB : CanonicalAt B x) :
    (phaseLinearMatrix (fderiv ℂ B x).toLinearMap).transpose * symplecticMatrix n *
        phaseLinearMatrix (fderiv ℂ B x).toLinearMap = symplecticMatrix n :=
  hB.2.matrix_identity

theorem CanonicalAt.comp {n : ℕ}
    {B C : ComplexPhaseSpace n → ComplexPhaseSpace n} {x : ComplexPhaseSpace n}
    (hB : CanonicalAt B (C x)) (hC : CanonicalAt C x) : CanonicalAt (B ∘ C) x := by
  refine ⟨hB.1.comp x hC.1, ?_⟩
  rw [fderiv_comp x hB.1 hC.1]
  exact hB.2.comp hC.2

theorem CanonicalOn.comp {n : ℕ}
    {B C : ComplexPhaseSpace n → ComplexPhaseSpace n}
    {S T : Set (ComplexPhaseSpace n)} (hB : CanonicalOn B T)
    (hC : CanonicalOn C S) (hmap : Set.MapsTo C S T) : CanonicalOn (B ∘ C) S := by
  intro x hx
  exact (hB (C x) (hmap hx)).comp (hC x hx)

theorem CanonicalAt.map_hamiltonianVectorField {n : ℕ}
    {B : ComplexPhaseSpace n → ComplexPhaseSpace n} {x : ComplexPhaseSpace n}
    (hB : CanonicalAt B x) {H : ComplexPhaseSpace n → ℂ}
    (hH : DifferentiableAt ℂ H (B x)) :
    fderiv ℂ B x (hamiltonianVectorField (H ∘ B) x) =
      hamiltonianVectorField H (B x) := by
  rw [hamiltonianVectorField_eq_sharp, hamiltonianVectorField_eq_sharp,
    fderiv_comp x hH hB.1]
  exact hB.2.map_sharp_comp (fderiv ℂ H (B x)).toLinearMap

theorem AnalyticPhaseFunction.canonical_pullback {n : ℕ} {G : Set (ComplexSpace n)}
    {ρ : ℝ≥0} (H : AnalyticPhaseFunction n G ρ)
    {B : ComplexPhaseSpace n → ComplexPhaseSpace n} {S : Set (ComplexPhaseSpace n)}
    (hB : CanonicalOn B S) (hmap : Set.MapsTo B S (phaseDomain G ρ))
    {x : ComplexPhaseSpace n} (hx : x ∈ S) :
    fderiv ℂ B x (hamiltonianVectorField (H.toFun ∘ B) x) =
      hamiltonianVectorField H.toFun (B x) :=
  (hB x hx).map_hamiltonianVectorField (H.analytic (B x) (hmap hx)).differentiableAt

end KamProject.Arnold1963
