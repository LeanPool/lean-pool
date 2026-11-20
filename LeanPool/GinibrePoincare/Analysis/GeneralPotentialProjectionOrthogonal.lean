/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GeneralPotentialProjectionOrthogonal.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.NonQuadraticPiBergman

/-!
# General potential projection orthogonal

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `planarPiBergmanProjection_adjoint`.
-/

@[expose] public section

open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section

/-- A finite product of commuting selfadjoint operators is selfadjoint. -/
theorem complexSuccessiveProjections_adjoint
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Ps : List (H →L[ℂ] H)) (ha : ∀ P ∈ Ps, P.adjoint = P)
    (hc : ∀ P ∈ Ps, ∀ Q ∈ Ps, P.comp Q = Q.comp P) :
    (complexSuccessiveProjections Ps).adjoint = complexSuccessiveProjections Ps := by
  induction Ps with
  | nil => exact ContinuousLinearMap.adjoint_id
  | cons P Ps ih =>
    have ht := ih (fun Q hQ => ha Q (List.mem_cons_of_mem _ hQ))
      (fun Q hQ R hR => hc Q (List.mem_cons_of_mem _ hQ) R (List.mem_cons_of_mem _ hR))
    change (P.comp (complexSuccessiveProjections Ps)).adjoint = P.comp (complexSuccessiveProjections
        Ps)
    rw [ContinuousLinearMap.adjoint_comp, ht, ha P (List.mem_cons_self ..)]
    exact (complexSuccessiveProjections_commutes Ps P
      (fun Q hQ => hc P (List.mem_cons_self ..) Q (List.mem_cons_of_mem _ hQ))).symm

/-- The actual whole-product nonquadratic Bergman projection is selfadjoint. -/
theorem planarPiBergmanProjection_adjoint {m : ℕ} (n : ℕ) (V : ℂ → ℝ)
    (hV : ContDiff ℝ 2 V) :
    (planarPiBergmanProjection (m := m) n V hV).adjoint = planarPiBergmanProjection n V hV := by
  apply complexSuccessiveProjections_adjoint
  · intro P hP
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hP
    exact planarPiBergmanCoordinate_adjoint n V hV i
  · intro P hP Q hQ
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hP
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hQ
    exact planarPiBergmanCoordinates_commute n V hV i j

end
end GinibrePoincare
