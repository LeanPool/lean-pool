/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P3523T1InsertionConstruction
public import Mathlib.Data.Fintype.EquivFin

-- [TABLET NODE: P3523T1FaceEnumeration]

/-!
# P3523T1FaceEnumeration

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
For a finite family $\mathcal F$ of finite subsets of
$\operatorname{Fin}(n+3)$, fix the standard finite-cardinality
equivalence from $\operatorname{Fin}(|\mathcal F|)$ to the elements
of $\mathcal F$. At each index $k$, choose an injective map
$f_k:\operatorname{Fin}3\to\operatorname{Fin}(n+3)$ with range
equal to its corresponding finite face, if such a map exists.
If none exists use the constant zero map. Thus this is a total
definition; correctness must in particular prove that the fallback
is never used in the constructed family. It retains every original
fine label literally and orders only the three labels of each face.
-/
noncomputable def P3523T1FaceEnumeration {n : Nat}
    (fs : Finset (Finset (Fin (n + 3)))) : Fin fs.card → Fin 3 → Fin (n + 3) := by
-- BODY
  classical
  let e : Fin fs.card ≃ {F // F ∈ fs} := fs.equivFin.symm
  exact fun k =>
    if h : ∃ f : Fin 3 → Fin (n + 3), Function.Injective f ∧
        Set.range f = ((e k).val : Set (Fin (n + 3))) then
      Classical.choose h
    else fun _ => 0

end ApollonianSuperharmonic

end
