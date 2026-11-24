/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73CircuitVisitCount
import LeanPool.GraphMinor.GM11.Ties
import LeanPool.GraphMinor.GM11.Section88

/-!
# Visit counts after joining two pieces

In XII (7.3), page 262, XI (9.2) supplies walks around two
pieces and a connector. Replace the connector by a shortest path
between their vertex sets. It meets either piece only at the
corresponding end. Interior vertices of the connector contribute
at most two visits and none from the pieces. At an end there is
at most one visit from the connector and one from its piece.
If the path has zero length, the two piece walks alone contribute
at most two visits.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- A closed walk never departs from a vertex outside its support. -/
theorem walkVertexCount_eq_zero_of_notMem_support
    {α β : Type*} {G : Graph α β} {a v : α} (W : GraphWalk G a a)
    (hv : v ∉ W.support) : walkVertexCount v W = 0 := by
  classical
  rw [walkVertexCount_eq_count_support_tail]
  exact List.count_eq_zero.mpr (fun h => hv (List.mem_of_mem_tail h))

/-- The forward and reverse path have the same vertex set as
the path itself. In particular their count is zero off the path. -/
theorem walkVertexCount_backtrack_eq_zero_of_notMem_support
    {α β : Type*} {G : Graph α β} {a b v : α} (Q : GraphWalk G a b)
    (hv : v ∉ Q.support) : walkVertexCount v (Q.append Q.reverse) = 0 := by
  apply walkVertexCount_eq_zero_of_notMem_support
  intro h
  rcases (GraphWalk.mem_support_append _ _).mp h with h | h
  · exact hv h
  · rw [GraphWalk.support_reverse, List.mem_reverse] at h
    exact hv h

/-- Joining two closed walks that each visit every vertex at
most once by a simple path meeting their supports only at its
ends gives at most two visits to every vertex. -/
theorem walkVertexCount_join_le_two
    {α β : Type*} {G : Graph α β} {a b : α}
    (P : GraphWalk G a a) (R : GraphWalk G b b) (Q : GraphWalk G a b)
    (hP : ∀ v, walkVertexCount v P ≤ 1) (hR : ∀ v, walkVertexCount v R ≤ 1)
    (hQ : Q.IsSimple)
    (hQP : ∀ v ∈ Q.support, v ∈ P.support → v = a)
    (hQR : ∀ v ∈ Q.support, v ∈ R.support → v = b) (v : α) :
    walkVertexCount v (P.append (Q.append (R.append Q.reverse))) ≤ 2 := by
  have hadd : walkVertexCount v (P.append (Q.append (R.append Q.reverse))) =
      walkVertexCount v P + walkVertexCount v R + walkVertexCount v (Q.append Q.reverse) := by
    simp only [walkVertexCount_append]
    omega
  rw [hadd]
  have hp := hP v
  have hr := hR v
  have hback := walkVertexCount_backtrack_bounds Q hQ v
  by_cases hvQ : v ∈ Q.support
  · by_cases hvP : v ∈ P.support
    · by_cases hvR : v ∈ R.support
      · have hva := hQP v hvQ hvP
        have hvb := hQR v hvQ hvR
        have hab : a = b := hva.symm.trans hvb
        cases hab
        cases Q with
        | nil _ => simp only [GraphWalk.append, GraphWalk.reverse, walkVertexCount]; omega
        | cons _ T => exact ((List.nodup_cons.mp hQ).1 T.end_mem_support).elim
      · have hz := walkVertexCount_eq_zero_of_notMem_support R hvR
        have hba := hback.2 (Or.inl (hQP v hvQ hvP))
        omega
    · have hzP := walkVertexCount_eq_zero_of_notMem_support P hvP
      by_cases hvR : v ∈ R.support
      · have hba := hback.2 (Or.inr (hQR v hvQ hvR))
        omega
      · have hzR := walkVertexCount_eq_zero_of_notMem_support R hvR
        omega
  · have hz := walkVertexCount_backtrack_eq_zero_of_notMem_support Q hvQ
    omega

end GraphMinor.GM12
