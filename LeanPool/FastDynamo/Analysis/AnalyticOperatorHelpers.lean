/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Complex.Basic

/-!
# Two analyticity helpers and the open right half plane

The analytic Fredholm argument of §2.3 of the paper (the spectral isolation before
`prop:local-seed`) needs three facts that have nothing to do with the seed:

* a scalar analytic function times a fixed vector is analytic;
* right composition with a fixed operator preserves analyticity of an operator family;
* the half plane `{re z > 0}` — the domain of the whole argument — is open.

The first two are stated for abstract normed spaces on purpose: the operator space `V →L[ℂ] V`
of the local seed carries several definitionally equal but syntactically different algebraic
instances, and unification succeeds in the generic statement while it fails at the concrete one.
They belong next to `Mathlib/Analysis/Analytic/Constructions.lean`.
-/

@[expose] public section

namespace FastDynamo

/-- A scalar analytic function times a fixed vector is analytic. -/
theorem analyticAt_smul_const {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {c : ℂ → ℂ} {z : ℂ} (hc : AnalyticAt ℂ c z) (C : F) :
    AnalyticAt ℂ (fun v => c v • C) z := by
  have hL := (ContinuousLinearMap.toSpanSingleton ℂ C).analyticAt (c z)
  exact hL.comp hc

/-- Right composition with a fixed operator preserves analyticity of an operator family. -/
theorem analyticAt_clm_comp_const {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {G : ℂ → (X →L[ℂ] X)} {z : ℂ} (hG : AnalyticAt ℂ G z) (A : X →L[ℂ] X) :
    AnalyticAt ℂ (fun v => (G v).comp A) z := by
  have hA : AnalyticAt ℂ (fun _ : ℂ => A) z := analyticAt_const
  exact hG.mul hA

/-- The open right half plane `{re z > 0}` is open. -/
theorem isOpen_rePos : IsOpen {z : ℂ | 0 < z.re} :=
  isOpen_lt continuous_const Complex.continuous_re

end FastDynamo
