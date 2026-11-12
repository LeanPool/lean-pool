/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4062T1InteriorSquare
public import LeanPool.ApollonianSuperharmonic.FordFareyParameter

-- [TABLET NODE: P4062T1RecursiveInteriors]

/-!
# P4062T1RecursiveInteriors

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a Ford parameter write $r=q_1$, $s=q_2$. Its four strict recursive
interiors, indexed $0,1,2,3$, are respectively
$A_0=D_r$, $A_1=(s,s)+D_r$, $A_2=(r,0)+D_s$, and $A_3=(0,r)+D_s$.
Here $D_d$ is the interior lattice square of denominator $d$.
-/
def P4062T1RecursiveInteriors (P : FordFareyParameter) :
    Fin 4 → Finset GaussianInt :=
-- BODY
  ![P4062T1InteriorSquare P.q₁,
    (P4062T1InteriorSquare P.q₁).image
      (fun x => x + ⟨(P.q₂ : Int), (P.q₂ : Int)⟩),
    (P4062T1InteriorSquare P.q₂).image
      (fun x => x + ⟨(P.q₁ : Int), 0⟩),
    (P4062T1InteriorSquare P.q₂).image
      (fun x => x + ⟨0, (P.q₁ : Int)⟩)]

end ApollonianSuperharmonic

end
