/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Cited
public import LeanPool.GraphMinor.GM15.Cited
public import LeanPool.GraphMinor.GM16.Cited
import LeanPool.GraphMinor.GM09.Section7
import LeanPool.GraphMinor.GM09.Section8
import LeanPool.GraphMinor.GM09.Section9
import LeanPool.GraphMinor.GM09.Section10
import LeanPool.GraphMinor.GM09.Section10g
import LeanPool.GraphMinor.GM09.Section11d

/-!
# Graph Minors IX: Bridge to Cited Statements in XIV, XV, and XVI

This file proves the cited statements from *Graph Minors. IX. Disjoint crossed paths*
used in later papers:
- `GM14.GM09Theorem91Statement` ((9.1), cited in XIV)
- `GM14.GM09Theorem104Statement` ((10.4), cited in XIV)
- `GM15.GM09Theorem71Statement` ((7.1), cited in XV)
- `GM15.GM09Theorem81Statement` ((8.1), cited in XV and XVI)
- `GM15.GM09Theorem1111Statement` ((11.11), cited in XV)
- `GM16.GM09Theorem105Statement` ((10.5), cited in XVI)
-/

@[expose] public section

namespace GraphMinor.GM09

universe u v

theorem gm14_theorem_9_1 : GM14.GM09Theorem91Statement.{u, v} :=
  fun _ _ _ _ _ hrural hcomp hcr hp =>
    theorem_9_1_proof hcomp hrural hcr hp

theorem gm15_theorem_7_1 : GM15.GM09Theorem71Statement.{u, v} :=
  fun S _ _ _ _ hφ hτ₁ hτ₂ hcr hcard =>
    S.theorem_7_1_proof hφ hτ₁ hτ₂ hcr hcard

theorem gm15_theorem_8_1 : GM15.GM09Theorem81Statement.{u, v} :=
  fun S k hne hvortex =>
    GraphMinor.GM09.theorem_8_1_proof S (Or.inl hne) k hvortex

theorem gm14_theorem_10_4 : GM14.GM09Theorem104Statement.{u, v} :=
  fun _S_comp _S₀ _N _p _X _P_set hp2 hp3 _hrural hbreadth hX hcard hcomp hcr hp =>
    theorem_10_4_proof hp2 hp3 hbreadth hX hcard hcomp hcr hp

theorem gm16_theorem_10_5 : GM16.GM09Theorem105Statement.{u, v} :=
  fun _ _ _ _ _ _ hrural hbreadth hX hpX hcomp hY =>
    theorem_10_5_proof hrural hbreadth hX hpX hcomp hY

theorem gm15_theorem_11_11 : GM15.GM09Theorem1111Statement.{u, v} :=
  fun S p hp2 hp3 hno_crooked => theorem_11_11_proof S p hp2 hp3 hno_crooked

end GraphMinor.GM09
