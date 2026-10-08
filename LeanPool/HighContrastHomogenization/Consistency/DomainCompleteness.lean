/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.ConvexDomains

/-!
# High-contrast homogenization: Consistency.DomainCompleteness

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The domain class of the Dirichlet estimate, from the other side

This module checks the shape datum `HasBallSandwich` through which the Dirichlet
estimate `e.random.dirichlet` reads the domain on which it is stated, and its
agreement with the paper's class `IsOpenBoundedConvexDomain`.
`exists_domain_with_ballSandwich` exhibits domains carrying a prescribed ball
sandwich; this module is the converse: every nonempty bounded open convex
domain admits one.  Together the two pin the class of domains the estimate
covers through its shape datum: it is exactly the class of nonempty bounded
open convex domains, no wider and no narrower.

Were that converse to fail, some nonempty bounded open convex domain would admit
no ball sandwich; the estimate's shape hypothesis would then be unsatisfiable on
that domain, so `e.random.dirichlet` — and every statement carrying the same
hypotheses — would be vacuous precisely where the paper means it to apply, and
the encoding `HasBallSandwich` would not be the domain class the paper prints.
This module is a consistency check of that definition and is not a result of the
paper.

The inner radius comes from openness at any point of the domain, the outer one
from boundedness, and the Euclidean ball of the second is obtained from the
coordinate bound by summing `d` squares.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- Every nonempty bounded open set is contained in a Euclidean ball centred at
any of its points. -/
theorem exists_outer_ball {U : Set (Vec d)} (hU : IsBoundedDomain U) (c : Vec d) :
    ∃ Rad : ℝ, 0 ≤ Rad ∧ U ⊆ euclideanBallAt c Rad := by
  obtain ⟨R, hRpos, hR⟩ := hU
  set M : ℝ := R + (∑ i : Fin d, |c i|) + 1 with hM
  have hMpos : 0 < M := by
    have : (0 : ℝ) ≤ ∑ i : Fin d, |c i| :=
      Finset.sum_nonneg fun i _ => abs_nonneg _
    rw [hM]
    linarith only [hRpos, this]
  refine ⟨Real.sqrt ((d : ℝ)) * M + M, by positivity, ?_⟩
  intro x hx
  change vecNormSq (x - c) < (Real.sqrt ((d : ℝ)) * M + M) ^ 2
  have hcoord : ∀ i : Fin d, (x - c) i ^ 2 ≤ M ^ 2 := by
    intro i
    have h1 : |x i| ≤ R := hR x hx i
    have h2 : |c i| ≤ ∑ j : Fin d, |c j| :=
      Finset.single_le_sum (f := fun j => |c j|) (fun j _ => abs_nonneg _)
        (Finset.mem_univ i)
    have h3 : |(x - c) i| ≤ M := by
      have hxc : (x - c) i = x i - c i := rfl
      rw [hxc]
      have habs : |x i - c i| ≤ |x i| + |c i| := abs_sub _ _
      rw [hM]
      linarith only [habs, h1, h2]
    have := sq_le_sq' (neg_le_of_abs_le h3) (le_of_abs_le h3)
    exact this
  have hsum : vecNormSq (x - c) ≤ (d : ℝ) * M ^ 2 := by
    rw [vecNormSq_eq_sum_sq]
    calc ∑ i : Fin d, (x - c) i ^ 2 ≤ ∑ _i : Fin d, M ^ 2 :=
          Finset.sum_le_sum fun i _ => hcoord i
      _ = (d : ℝ) * M ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hsq : (d : ℝ) * M ^ 2 = (Real.sqrt ((d : ℝ)) * M) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
  have hlt : (Real.sqrt ((d : ℝ)) * M) ^ 2
      < (Real.sqrt ((d : ℝ)) * M + M) ^ 2 := by
    have hnn : 0 ≤ Real.sqrt ((d : ℝ)) * M := by positivity
    exact pow_lt_pow_left₀ (by linarith only [hMpos]) hnn two_ne_zero
  rw [hsq] at hsum
  linarith only [hsum, hlt]

/-- Every nonempty bounded open convex domain admits a ball sandwich.  With the
witness of `exists_domain_with_ballSandwich` this pins the domain class carried
by the Dirichlet clause: the clause covers exactly the nonempty bounded convex
domains, no more and no fewer. -/
theorem exists_hasBallSandwich_of_isOpenBoundedConvexDomain {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty) :
    ∃ ρ Rad : ℝ, HasBallSandwich U ρ Rad := by
  obtain ⟨c, hc⟩ := hne
  obtain ⟨ε, hεpos, hball⟩ := Metric.isOpen_iff.1 hU.isOpen c hc
  obtain ⟨Rad, hRadnn, hRad⟩ := exists_outer_ball hU.isBoundedDomain c
  refine ⟨ε, Rad, hεpos, hRadnn, c, ?_, hRad⟩
  exact fun x hx => hball (euclideanBallAt_subset_metricBall c hεpos hx)

end

end HighContrast
end HCPolySupport
