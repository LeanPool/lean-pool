/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.FordRecursiveVertexDomains

-- [TABLET NODE: P5130T5Prescription]

/-!
# P5130T5Prescription

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a Ford--Farey parameter $P$ and two integer lattice functions $g_1,g_2$,
define the four recursive prescriptions $F_i=F_i(P;g_1,g_2)$ by
$$
\begin{aligned}
 F_0(x)&=g_1(x),\\
 F_1(x)&=g_1(x-(q_2,q_2))+p_2x_1+p_2x_2-p_2q_2+1,\\
 F_2(x)&=g_2(x-(q_1,0))+p_1x_2,\\
 F_3(x)&=g_2(x-(0,q_1))+p_1x_1.
\end{aligned}
$$
They are total functions; their prescribed domains are, respectively,
$E_1,E_2,E_3,E_4$ of `FordRecursiveVertexDomains`.
-/
def P5130T5Prescription (P : FordFareyParameter)
    (g₁ g₂ : IntegerLatticeFunction) : Fin 4 → IntegerLatticeFunction :=
-- BODY
  ![g₁,
    fun x => g₁ (x - ⟨(P.q₂ : Int), (P.q₂ : Int)⟩) +
      P.p₂ * x.re + P.p₂ * x.im - P.p₂ * (P.q₂ : Int) + 1,
    fun x => g₂ (x - ⟨(P.q₁ : Int), 0⟩) + P.p₁ * x.im,
    fun x => g₂ (x - ⟨0, (P.q₁ : Int)⟩) + P.p₁ * x.re]

end ApollonianSuperharmonic

end
