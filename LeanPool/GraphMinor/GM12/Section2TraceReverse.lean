/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2TraceComposition
import LeanPool.GraphMinor.GM12.Section2TraceParameters

/-!
# Reversing trace steps

The entry and exit rules of XII, page 243, exchange when the
parameter runs backwards. Reverse the remaining walk first, then
append the reversed pair for the first region visit. This proves
that the reversed walk traces the reversed parameter interval.
-/

public section

namespace GraphMinor.GM12

open Set Surface

private theorem append_assoc {α β : Type*} {G : Graph α β}
    {a b c d : α} (P : GraphWalk G a b) (Q : GraphWalk G b c) (R : GraphWalk G c d) :
    (P.append Q).append R = P.append (Q.append R) := by
  induction P with
  | nil _ => rfl
  | cons _ _ ih => exact congrArg (GraphWalk.cons _) (ih Q)

/-- Reversing the parameter and the walk preserves trace steps. -/
theorem traceSteps_reverse
    {S : Type*} [TopologicalSpace S] {Γ K : Drawing S} {f : ℝ → S}
    {a b : ℝ} {u v : S} (W : GraphWalk K.toGraph u v) (hW : TraceSteps Γ K f a b W) :
    TraceSteps Γ K (fun t => f (-t)) (-b) (-a) W.reverse := by
  cases hWcase : W with
  | nil hu =>
    rw [hWcase] at hW
    obtain ⟨rfl, hfa, huΓ⟩ := hW
    exact ⟨rfl, by simpa only [neg_neg] using hfa, huΓ⟩
  | cons hlink rest =>
    rw [hWcase] at hW
    cases hrestcase : rest with
    | nil hu => rw [hrestcase] at hW; exact hW.elim
    | cons hlink' tail =>
      rw [hrestcase] at hW
      obtain ⟨c, hac, hfa, hu, hfc, hwK, r, hr, hwr, hfr, hleave, henter, htail⟩ := hW
      have htail' := traceSteps_reverse tail htail
      let P := GraphWalk.cons hlink'.symm (GraphWalk.cons hlink.symm (.nil hlink.left_mem))
      have hP : TraceSteps Γ K (fun t => f (-t)) (-c) (-a) P := by
        refine ⟨-a, neg_lt_neg hac, ?_, (traceSteps_parameters tail htail).2.2.1, ?_, hwK,
          r, hr, hwr, ?_, ?_, hleave, rfl, ?_, hu⟩
        · simpa only [neg_neg] using hfc
        · simpa only [neg_neg] using hfa
        · intro t ht
          exact hfr (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
        · simpa only [LeavesLike, neg_neg] using henter
        · simpa only [neg_neg] using hfa
      change TraceSteps Γ K (fun t => f (-t)) (-b) (-a)
        ((tail.reverse.append _).append _)
      rw [append_assoc]
      exact traceSteps_append tail.reverse P htail' hP
termination_by W.length
decreasing_by
  simp_all only [GraphWalk.length, GraphWalk.edges, List.length_cons]
  omega

end GraphMinor.GM12
