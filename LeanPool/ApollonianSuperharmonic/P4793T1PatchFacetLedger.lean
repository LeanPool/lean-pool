/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Tactic.Linarith

public import LeanPool.ApollonianSuperharmonic.P4793T1FacetForms
public import LeanPool.ApollonianSuperharmonic.P4783T1PatchCoordinates
public import LeanPool.ApollonianSuperharmonic.P4715T1BoundaryCycle

-- [TABLET NODE: P4793T1PatchFacetLedger]

/-!
# P4793T1PatchFacetLedger

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4793T1PatchFacetLedger :
    let v := fun j => SixSubtileFaceVertices (P4715T1PatchFaces j)
    let p := fun j => P4715T1Position ∘ v j
    (∀ (j : Fin 12) (l : Fin 6) (k : Fin 3), 0 ≤ P4793T1FacetForms l (p j k)) ∧
    (∀ (j : Fin 12) (l : Fin 6) (k : Fin 3),
      P4793T1FacetForms l (p j k) = 0 → v j k ∈ Set.range P4715T1BoundaryCycle) ∧
    ∀ j : Fin 12, ∃ l : Fin 6, ∀ k : Fin 3,
      v j k ∈ Set.range P4715T1BoundaryCycle → P4793T1FacetForms l (p j k) = 0 := by
-- BODY
  let q : Fin 12 → Fin 3 → Int × Int := ![
    ![(0,0),(-4,-8),(-6,-6)],
    ![(-12,-12),(-4,-8),(-6,-6)],
    ![(-12,0),(-16,-8),(-10,-2)],
    ![(-12,0),(-4,4),(-10,-2)],
    ![(-12,-12),(-6,-6),(-11,-7)],
    ![(-6,-6),(-10,-2),(-11,-7)],
    ![(-16,-8),(-10,-2),(-11,-7)],
    ![(-12,-12),(-16,-8),(-11,-7)],
    ![(0,0),(-6,-6),(-5,-1)],
    ![(-6,-6),(-10,-2),(-5,-1)],
    ![(-4,4),(-10,-2),(-5,-1)],
    ![(0,0),(-4,4),(-5,-1)]]
  let ev := fun (l : Fin 6) (z : Int × Int) =>
    ![-2*z.1+z.2, -z.1+2*z.2+12, z.1+z.2+24,
      2*z.1-z.2+24, z.1-2*z.2+12, -z.1-z.2] l
  let v := fun j => SixSubtileFaceVertices (P4715T1PatchFaces j)
  have cert :
      (∀ (j : Fin 12) (l : Fin 6) (k : Fin 3), 0 ≤ ev l (q j k)) ∧
      (∀ (j : Fin 12) (l : Fin 6) (k : Fin 3),
        ev l (q j k) = 0 → ∃ r, v j k = P4715T1BoundaryCycle r) ∧
      ∀ j : Fin 12, ∃ l : Fin 6, ∀ k : Fin 3,
        (∃ r, v j k = P4715T1BoundaryCycle r) → ev l (q j k) = 0 := by
    decide +kernel
  let p := fun j => P4715T1Position ∘ v j
  have coordinates (j : Fin 12) (k : Fin 3) :
      12*(p j k).1 = ((q j k).1 : Real) ∧
      12*(p j k).2 = ((q j k).2 : Real) := by
    dsimp only [p, v]
    rw [P4783T1PatchCoordinates]
    fin_cases j <;> fin_cases k <;> norm_num [q]
  have values (l : Fin 6) (j : Fin 12) (k : Fin 3) :
      12 * P4793T1FacetForms l (p j k) = (ev l (q j k) : Real) := by
    have hx := (coordinates j k).1
    have hy := (coordinates j k).2
    fin_cases l <;> norm_num [P4793T1FacetForms, ev] <;> linarith
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro j l k
    have hn : (0 : Real) ≤ (ev l (q j k) : Real) := by exact_mod_cast cert.1 j l k
    have he := values l j k
    change 0 ≤ P4793T1FacetForms l (p j k)
    linarith
  · intro j l k hk
    change P4793T1FacetForms l (p j k) = 0 at hk
    have hz : (ev l (q j k) : Real) = 0 := by linarith [values l j k]
    have hz' : ev l (q j k) = 0 := by exact_mod_cast hz
    obtain ⟨r, hr⟩ := cert.2.1 j l k hz'
    exact ⟨r, hr.symm⟩
  · intro j
    obtain ⟨l, hl⟩ := cert.2.2 j
    refine ⟨l, fun k hk => ?_⟩
    obtain ⟨r, hr⟩ := hk
    have hz := hl k ⟨r, hr.symm⟩
    have hz' : (ev l (q j k) : Real) = 0 := by exact_mod_cast hz
    change P4793T1FacetForms l (p j k) = 0
    linarith [values l j k]

end ApollonianSuperharmonic

end
