/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NonQuadraticFiniteProjection.lean.
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

public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Non quadratic finite projection

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `complexSuccessiveProjections_error`, `complexSuccessiveProjections_commutes`,
`complexSuccessiveProjections_fixed`.
-/

@[expose] public section

open scoped InnerProductSpace
namespace GinibrePoincare
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The composition `P₁ ∘ P₂ ∘ ⋯ ∘ Pₖ` of a list of operators (the identity for the empty
list). -/
def complexSuccessiveProjections (Ps : List (H →L[ℂ] H)) : H →L[ℂ] H :=
  Ps.foldr (fun P B => P.comp B) (ContinuousLinearMap.id ℂ H)

theorem complexProjection_composition_error (P B : H →L[ℂ] H)
    (ha : P.adjoint = P) (hi : P.comp P = P) (hc : ‖P‖ ≤ 1) (x : H) :
    ‖x - P (B x)‖ ^ 2 ≤ ‖x - P x‖ ^ 2 + ‖x - B x‖ ^ 2 := by
  have hp : P (P x) = P x := DFunLike.congr_fun hi x
  have hz : P (x - P x) = 0 := by rw [map_sub, hp, sub_self]
  have ho : ⟪x - P x, P (x - B x)⟫_ℂ = 0 := by
    rw [← ha, ContinuousLinearMap.adjoint_inner_right]
    rw [ha, hz, inner_zero_left]
  have he : x - P (B x) = (x - P x) + P (x - B x) := by rw [map_sub]; abel
  have hn : ‖(x - P x) + P (x - B x)‖ ^ 2 =
      ‖x - P x‖ ^ 2 + ‖P (x - B x)‖ ^ 2 := by
    simpa only [sq] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ ho
  have hb : ‖P (x - B x)‖ ≤ ‖x - B x‖ :=
    (P.le_opNorm _).trans ((mul_le_mul_of_nonneg_right hc (norm_nonneg _)).trans_eq (one_mul _))
  rw [he, hn]
  exact add_le_add (le_refl _) ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hb)

theorem complexSuccessiveProjections_error (Ps : List (H →L[ℂ] H))
    (hp : ∀ P ∈ Ps, P.adjoint = P ∧ P.comp P = P ∧ ‖P‖ ≤ 1) (x : H) :
    ‖x - complexSuccessiveProjections Ps x‖ ^ 2 ≤ (Ps.map (fun P => ‖x - P x‖ ^ 2)).sum := by
  induction Ps with
  | nil => simp [complexSuccessiveProjections]
  | cons P Ps ih =>
    have hP := hp P (List.mem_cons_self ..)
    have ht : ∀ Q ∈ Ps, Q.adjoint = Q ∧ Q.comp Q = Q ∧ ‖Q‖ ≤ 1 :=
      fun Q hQ => hp Q (List.mem_cons_of_mem _ hQ)
    change ‖x - P (complexSuccessiveProjections Ps x)‖ ^ 2 ≤ _
    simpa only [List.map_cons, List.sum_cons] using
      (complexProjection_composition_error P _ hP.1 hP.2.1 hP.2.2 x).trans
        (add_le_add (le_refl _) (ih ht))

omit [CompleteSpace H] in
theorem complexSuccessiveProjections_commutes (Ps : List (H →L[ℂ] H))
    (Q : H →L[ℂ] H) (hc : ∀ P ∈ Ps, Q.comp P = P.comp Q) :
    Q.comp (complexSuccessiveProjections Ps) = (complexSuccessiveProjections Ps).comp Q := by
  induction Ps with
  | nil => simp [complexSuccessiveProjections]
  | cons P Ps ih =>
    have ht := ih (fun R hR => hc R (List.mem_cons_of_mem _ hR))
    change Q.comp (P.comp (complexSuccessiveProjections Ps)) = _
    rw [← ContinuousLinearMap.comp_assoc, hc P (List.mem_cons_self ..),
      ContinuousLinearMap.comp_assoc, ht, ← ContinuousLinearMap.comp_assoc]
    rfl

omit [CompleteSpace H] in
theorem complexSuccessiveProjections_fixed (Ps : List (H →L[ℂ] H))
    (hi : ∀ P ∈ Ps, P.comp P = P)
    (hc : ∀ P ∈ Ps, ∀ Q ∈ Ps, P.comp Q = Q.comp P) (x : H) :
    ∀ P ∈ Ps, P (complexSuccessiveProjections Ps x) = complexSuccessiveProjections Ps x := by
  induction Ps with
  | nil => simp
  | cons Q Ps ih =>
    intro P hP
    rcases List.mem_cons.mp hP with rfl | hP
    · change P (P (complexSuccessiveProjections Ps x)) = P (complexSuccessiveProjections Ps x)
      exact DFunLike.congr_fun (hi P (List.mem_cons_self ..)) _
    · have ht := ih (fun R hR => hi R (List.mem_cons_of_mem _ hR))
        (fun R hR S hS => hc R (List.mem_cons_of_mem _ hR) S (List.mem_cons_of_mem _ hS)) P hP
      have hq := DFunLike.congr_fun (hc P (List.mem_cons_of_mem _ hP) Q (List.mem_cons_self ..))
        (complexSuccessiveProjections Ps x)
      change P (Q (complexSuccessiveProjections Ps x)) = Q (complexSuccessiveProjections Ps x)
      simp only [ContinuousLinearMap.comp_apply] at hq
      rw [hq, ht]
end
end GinibrePoincare
