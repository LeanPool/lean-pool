/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

/-
Adapted from gpartin/LeanDiracDerivation, file `LeanDirac/Dirac030.lean`, at commit
867004142ada3eec464d5bd3088d7313fdad1613.
Upstream copyright (c) 2026 G. D. Partin, dual-licensed at the recipient's
option under the MIT License or CC0 1.0 (see the upstream `LICENSE`,
`LICENSE-CC0` and `LICENSING.md`); used here under the MIT License.
-/

module

public import LeanPool.LatticeDiracDerivation.Dirac029

/-!
# DIRAC-030: free Gordon current decomposition

This stage defines covariant gamma and sigma operators from the already
derived mass grading and C19 transport generators.  It proves the Gordon
kernel identity, derives the Dirac-adjoint on-shell equation, and separates
the free current matrix element into convection and intrinsic-spin terms.

No electromagnetic field or magnetic moment is assumed.
-/

@[expose] public section

namespace LeanDirac

noncomputable section
open Complex

/-- The gamma matrices on four-component vectors: `γ⁰ = β` and `γⁱ = β * standardCubeGamma (i - 1)`
for `i = 1, 2, 3`, where `β = standardDiracBeta`. -/
def c19Gamma (mu : Fin 4) (z : Cell4) : Cell4 :=
  if mu = 0 then standardDiracBeta z
  else if mu = 1 then standardDiracBeta (standardCubeGamma 0 z)
  else if mu = 2 then standardDiracBeta (standardCubeGamma 1 z)
  else standardDiracBeta (standardCubeGamma 2 z)

/-- The contravariant four-momentum `(energy, px, py, pz)`, indexed by `mu`. -/
def fourMomentumContravariant
    (energy px py pz : ℝ) (mu : Fin 4) : ℝ :=
  if mu = 0 then energy
  else if mu = 1 then px
  else if mu = 2 then py
  else pz

/-- The covariant four-momentum `(energy, -px, -py, -pz)`, indexed by `mu`. -/
def fourMomentumCovariant
    (energy px py pz : ℝ) (mu : Fin 4) : ℝ :=
  if mu = 0 then energy
  else if mu = 1 then -px
  else if mu = 2 then -py
  else -pz

/-- The Feynman slash `∑ μ, p_μ γ^μ` of the four-momentum, with covariant components
`fourMomentumCovariant` and gamma matrices `c19Gamma`. -/
def c19Slash
    (energy px py pz : ℝ) (z : Cell4) : Cell4 :=
  fun component =>
    ∑ mu, (fourMomentumCovariant energy px py pz mu : ℂ) *
      c19Gamma mu z component

/-- The operator `σ^{μν} = (I / 2) [γ^μ, γ^ν]` built from the gamma matrices `c19Gamma`. -/
def c19Sigma (mu nu : Fin 4) (z : Cell4) : Cell4 :=
  fun component =>
    (I / 2) *
      (c19Gamma mu (c19Gamma nu z) component -
        c19Gamma nu (c19Gamma mu z) component)

theorem c19_gordon_kernel_identity
    (mu : Fin 4)
    (q0 qx qy qz p0 px py pz : ℝ) (z : Cell4) :
    (fun component =>
      c19Slash q0 qx qy qz (c19Gamma mu z) component +
        c19Gamma mu (c19Slash p0 px py pz z) component) =
      fun component =>
        ((fourMomentumContravariant q0 qx qy qz mu +
            fourMomentumContravariant p0 px py pz mu : ℝ) : ℂ) *
            z component +
          I * ∑ nu,
            ((fourMomentumCovariant q0 qx qy qz nu -
                fourMomentumCovariant p0 px py pz nu : ℝ) : ℂ) *
              c19Sigma mu nu z component := by
  have hI3 : I ^ 3 = -I := by
    rw [show I ^ 3 = I ^ 2 * I by ring, Complex.I_sq]
    ring
  funext component
  fin_cases mu <;> fin_cases component <;>
    simp [c19Slash, c19Sigma, c19Gamma,
      fourMomentumContravariant, fourMomentumCovariant,
      Fin.sum_univ_succ, standardDiracBeta, standardCubeGamma,
      standardDiracAlphaX, standardDiracAlphaY,
      standardDiracAlphaZ] <;>
    ring_nf
  all_goals simp only [hI3, Complex.I_sq]
  all_goals ring

/-- The Dirac-adjoint bilinear form `∑ i, conj (left i) * (β right) i`, where
`β = standardDiracBeta`. -/
def diracBilinear (left right : Cell4) : ℂ :=
  ∑ component,
    starRingEnd ℂ (left component) * standardDiracBeta right component

theorem dirac_bilinear_add_right
    (left first second : Cell4) :
    diracBilinear left
        (fun component => first component + second component) =
      diracBilinear left first + diracBilinear left second := by
  simp [diracBilinear, Fin.sum_univ_succ, standardDiracBeta]
  ring

theorem dirac_bilinear_real_smul_left
    (a : ℝ) (left right : Cell4) :
    diracBilinear (fun component => (a : ℂ) * left component) right =
      (a : ℂ) * diracBilinear left right := by
  simp [diracBilinear, Fin.sum_univ_succ, standardDiracBeta]
  ring

theorem dirac_bilinear_smul_right
    (a : ℂ) (left right : Cell4) :
    diracBilinear left (fun component => a * right component) =
      a * diracBilinear left right := by
  simp [diracBilinear, Fin.sum_univ_succ, standardDiracBeta]
  ring

theorem c19_gamma_real_smul
    (mu : Fin 4) (a : ℝ) (z : Cell4) :
    c19Gamma mu (fun component => (a : ℂ) * z component) =
      fun component => (a : ℂ) * c19Gamma mu z component := by
  funext component
  fin_cases mu <;> fin_cases component <;>
    simp [c19Gamma, standardDiracBeta, standardCubeGamma,
      standardDiracAlphaX, standardDiracAlphaY,
      standardDiracAlphaZ] <;>
    ring

theorem c19_slash_dirac_adjoint_symmetric
    (energy px py pz : ℝ) (left right : Cell4) :
    diracBilinear (c19Slash energy px py pz left) right =
      diracBilinear left (c19Slash energy px py pz right) := by
  simp [diracBilinear, c19Slash, c19Gamma,
    fourMomentumCovariant, Fin.sum_univ_succ,
    standardDiracBeta, standardCubeGamma,
    standardDiracAlphaX, standardDiracAlphaY,
    standardDiracAlphaZ]
  ring

/-- The right-hand side of the Gordon decomposition: `(q^μ + p^μ)` times
`diracBilinear left right`, plus `I` times the sum over `ν` of `(q_ν - p_ν)` times
`diracBilinear left (c19Sigma mu nu right)`. -/
def gordonConvectionSpin
    (mu : Fin 4)
    (q0 qx qy qz p0 px py pz : ℝ)
    (left right : Cell4) : ℂ :=
  ((fourMomentumContravariant q0 qx qy qz mu +
      fourMomentumContravariant p0 px py pz mu : ℝ) : ℂ) *
      diracBilinear left right +
    I * ∑ nu,
      ((fourMomentumCovariant q0 qx qy qz nu -
          fourMomentumCovariant p0 px py pz nu : ℝ) : ℂ) *
        diracBilinear left (c19Sigma mu nu right)

theorem gordon_kernel_between_states
    (mu : Fin 4)
    (q0 qx qy qz p0 px py pz : ℝ)
    (left right : Cell4) :
    diracBilinear left
        (fun component =>
          c19Slash q0 qx qy qz (c19Gamma mu right) component +
            c19Gamma mu (c19Slash p0 px py pz right) component) =
      gordonConvectionSpin mu q0 qx qy qz p0 px py pz left right := by
  rw [c19_gordon_kernel_identity]
  simp [diracBilinear, gordonConvectionSpin,
    Fin.sum_univ_succ, standardDiracBeta]
  ring

theorem gordon_current_decomposition
    (mass : ℝ) (hmass : mass ≠ 0) (mu : Fin 4)
    (q0 qx qy qz p0 px py pz : ℝ)
    (left right : Cell4)
    (hleft : c19Slash q0 qx qy qz left =
      fun component => (mass : ℂ) * left component)
    (hright : c19Slash p0 px py pz right =
      fun component => (mass : ℂ) * right component) :
    diracBilinear left (c19Gamma mu right) =
      (1 / ((2 * mass : ℝ) : ℂ)) *
        gordonConvectionSpin mu q0 qx qy qz p0 px py pz left right := by
  have hfirst :
      diracBilinear left
          (c19Slash q0 qx qy qz (c19Gamma mu right)) =
        (mass : ℂ) * diracBilinear left (c19Gamma mu right) := by
    rw [← c19_slash_dirac_adjoint_symmetric]
    rw [hleft]
    exact dirac_bilinear_real_smul_left mass left (c19Gamma mu right)
  have hsecond :
      diracBilinear left
          (c19Gamma mu (c19Slash p0 px py pz right)) =
        (mass : ℂ) * diracBilinear left (c19Gamma mu right) := by
    rw [hright, c19_gamma_real_smul]
    exact dirac_bilinear_smul_right (mass : ℂ) left (c19Gamma mu right)
  have hkernel :=
    gordon_kernel_between_states mu q0 qx qy qz p0 px py pz left right
  rw [dirac_bilinear_add_right, hfirst, hsecond] at hkernel
  rw [← hkernel]
  field_simp [hmass]
  push_cast
  ring

/-- The Gordon kernel identity for `c19Slash` and `c19Gamma`, together with the decomposition of
`diracBilinear left (c19Gamma mu right)` as `gordonConvectionSpin / (2 * mass)` when `left` and
`right` satisfy the Dirac equation with nonzero `mass`. -/
structure Dirac030GordonCertificate : Prop where
  previousGate : Dirac029ChargeConjugationCertificate
  kernelIdentity : ∀ mu q0 qx qy qz p0 px py pz z,
    (fun component =>
      c19Slash q0 qx qy qz (c19Gamma mu z) component +
        c19Gamma mu (c19Slash p0 px py pz z) component) =
      fun component =>
        ((fourMomentumContravariant q0 qx qy qz mu +
            fourMomentumContravariant p0 px py pz mu : ℝ) : ℂ) *
            z component +
          I * ∑ nu,
            ((fourMomentumCovariant q0 qx qy qz nu -
                fourMomentumCovariant p0 px py pz nu : ℝ) : ℂ) *
              c19Sigma mu nu z component
  onShellCurrentSplit : ∀ (mass : ℝ), mass ≠ 0 → ∀ mu
      q0 qx qy qz p0 px py pz left right,
    c19Slash q0 qx qy qz left =
        (fun component => (mass : ℂ) * left component) →
    c19Slash p0 px py pz right =
        (fun component => (mass : ℂ) * right component) →
    diracBilinear left (c19Gamma mu right) =
      (1 / ((2 * mass : ℝ) : ℂ)) *
        gordonConvectionSpin mu q0 qx qy qz p0 px py pz left right

theorem dirac030_free_gordon_decomposition :
    Dirac030GordonCertificate where
  previousGate := dirac029_free_charge_conjugation
  kernelIdentity := c19_gordon_kernel_identity
  onShellCurrentSplit := fun mass hmass mu q0 qx qy qz
      p0 px py pz left right hleft hright =>
    gordon_current_decomposition mass hmass mu
      q0 qx qy qz p0 px py pz left right hleft hright

end
end LeanDirac
