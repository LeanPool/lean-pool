/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.Constructor
public import LeanPool.CaffarelliKohnNirenberg.Statements.SuitableWeakSolution

/-!
# The two forms of the suitable weak-solution class

`CKN.IsSuitableWeakSolution` is the suitable weak-solution class as the CKN
manuscript states it, and it is the class the statements of this repository assume. The
CKN library proves its estimates for `CKN.IsSuitableWeakSolutionIntegrable`,
which adds an integrability condition to each identity clause. The two classes
have the same inhabitants: the extra conditions follow from the measurability
and local integrability clauses (`CKN.isSuitableWeakSolutionIntegrable_of_identities`).
This file records both directions for use at the calls into the CKN library.
-/

public section

open CKN.Foundation.Parabolic CKN


namespace CIV

variable {Ω : Set Vec3} {I : Set ℝ} {q : ℝ} {u : ParabolicPoint → Vec3}
  {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
  {f : ParabolicPoint → Vec3}

/-- A suitable weak solution in the sense of the CKN manuscript satisfies the
integrability conditions that the CKN library carries in its class. -/
theorem isSuitableWeakSolutionIntegrable_of_isSuitableWeakSolution
    (h : IsSuitableWeakSolution Ω I q u Du p f) :
    IsSuitableWeakSolutionIntegrable Ω I q u Du p f :=
  isSuitableWeakSolutionIntegrable_of_identities
    ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩
    h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2

/-- Dropping the integrability conditions of the CKN library class gives a
suitable weak solution in the sense of the CKN manuscript. -/
theorem isSuitableWeakSolution_of_integrable
    (h : IsSuitableWeakSolutionIntegrable Ω I q u Du p f) :
    IsSuitableWeakSolution Ω I q u Du p f :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    fun ψ hψ => (h.2.2.2.2.2.2.1 ψ hψ).2,
    fun φ hφ => (h.2.2.2.2.2.2.2.1 φ hφ).2,
    fun ψ hψ hnn => (h.2.2.2.2.2.2.2.2 ψ hψ hnn).2.2⟩

end CIV
