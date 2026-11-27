/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

/-
Adapted from gpartin/LeanDiracDerivation at commit 7b2a51cf933798eeb931731609fda0ffa81123fe.
Upstream source is dual-licensed under MIT or CC0 1.0; used here under MIT.
-/

module

public import LeanPool.LatticeDiracDerivation.V33FrameworkLock

/-!
# V3.3 Stage 2: complete orthonormal spinor basis
-/

@[expose] public section

namespace LeanDirac.V2

noncomputable section

theorem v33_standard_basis_orthonormal (i j : Fin 4) :
    cubicalCell4Inner (standardCell4Basis i) (standardCell4Basis j) =
      if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [cubicalCell4Inner, standardCell4Basis]

theorem v33_standard_basis_resolves (z : CubicalCell4) :
    (fun component =>
      ∑ i : Fin 4, z i * standardCell4Basis i component) = z := by
  funext component
  fin_cases component <;>
    simp [standardCell4Basis]

/-- Certificate for the four native spinor basis states. -/
structure V33SpinorBasisCertificate : Prop where
  orthonormal : ∀ i j : Fin 4,
    cubicalCell4Inner (standardCell4Basis i) (standardCell4Basis j) =
      if i = j then 1 else 0
  resolves : ∀ z : CubicalCell4,
    (fun component =>
      ∑ i : Fin 4, z i * standardCell4Basis i component) = z

theorem v33_spinor_basis : V33SpinorBasisCertificate where
  orthonormal := v33_standard_basis_orthonormal
  resolves := v33_standard_basis_resolves

end
end LeanDirac.V2
