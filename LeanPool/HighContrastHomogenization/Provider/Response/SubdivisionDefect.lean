/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Recurrence.AdaptedPartitionAverage
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.BasicVariationalIdentities
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.Existence
public import LeanPool.HighContrastHomogenization.Support.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.EnergyDensities

/-!
# High-contrast homogenization: Provider.Response.SubdivisionDefect

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The subdivision defect of the response functional

A maximizer of the response functional on a domain restricts to an admissible
competitor on every subdomain, and its response integrand is a fixed function of
the coefficient representative and the gradient.  Averaging that integrand over
a subdivision of the parent into cells that are pairwise disjoint and cover the
parent up to a null set therefore returns the parent response exactly.

Subtracting this from the second-variation identity on each cell gives the
subdivision defect identity: the weighted average of the cells' response values
exceeds the parent's response value by precisely the weighted average of the
symmetric energies of the gradient differences between the cell maximizers and
the restricted parent maximizer.  In the equal-volume case the weights are all
the reciprocal cell count, which is the form the localization argument uses.

Since the symmetric part of an elliptic coefficient is positive semidefinite,
every cell contribution is nonnegative, and so is the defect.

Everything is stated over an arbitrary Chapter 2 domain and an arbitrary finite
family of subdomains, so it reads on triadic cubes and on adapted cells alike.
-/

namespace HCPolySupport
namespace HighContrast
namespace Response

open Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## The canonical maximizer as a solution -/

/-- The canonical response maximizer of a Chapter 2 domain, read as a
solution. -/
@[expose]
def canonicalResponseSolution (U : Domain d) (a : CoeffOn U) (p r : Vec d) :
    Solution U a :=
  (canonicalMaximizer (responseExistenceTheory U a) p r).toSolution

/-- The canonical response solution maximizes the response functional. -/
theorem canonicalResponseSolution_isMaximizer (U : Domain d) (a : CoeffOn U)
    (p r : Vec d) :
    Book.Ch02.IsResponseMaximizer U a p r (canonicalResponseSolution U a p r) :=
  canonicalMaximizer_isMaximizer (responseExistenceTheory U a) p r

/-! ## The response integrand depends only on the representative and the
gradient -/

/-- Two solutions with the same gradient, on domains carrying the same
coefficient representative, have the same response integrand. -/
theorem responseIntegrand_congr {U V : Domain d} {a : CoeffOn U} {b : CoeffOn V}
    (hrep : b.toCoeffField = a.toCoeffField) {v : Solution U a}
    {z : Solution V b} (hz : z.toH1.grad = v.toH1.grad) (p r : Vec d) :
    responseIntegrand V b p r z = responseIntegrand U a p r v := by
  unfold responseIntegrand
  rw [hz, hrep]

/-! ## The parent response is the weighted average of the restricted values -/

/-- The weighted average over a subdivision of the response values of the
restricted parent maximizer is the parent response. -/
theorem sum_weight_responseValue_eq_responseJ {ι : Type*} {Z : Finset ι}
    {U : Domain d} {V : ι → Domain d} {a : CoeffOn U} {b : ∀ i, CoeffOn (V i)}
    (hrep : ∀ i ∈ Z, (b i).toCoeffField = a.toCoeffField)
    (hsub : ∀ i ∈ Z, (V i).carrier ⊆ U.carrier)
    (hdisj : (↑Z : Set ι).PairwiseDisjoint fun i => (V i).carrier)
    (hnull : volume (U.carrier \ ⋃ i ∈ (↑Z : Set ι), (V i).carrier) = 0)
    {p r : Vec d} {v : Solution U a} (hv : Book.Ch02.IsResponseMaximizer U a p r v)
    {z : ∀ i, Solution (V i) (b i)}
    (hz : ∀ i ∈ Z, (z i).toH1.grad = v.toH1.grad) :
    ∑ i ∈ Z, (volume (V i).carrier).toReal / (volume U.carrier).toReal *
        responseValue (V i) (b i) p r (z i) = responseJ U a p r := by
  have hcell0 : ∀ i ∈ Z, volume (V i).carrier ≠ 0 := fun i _ =>
    ((V i).isOpen.measure_pos volume (V i).nonempty).ne'
  have hint : IntegrableOn (responseIntegrand U a p r v) U.carrier volume :=
    Book.Ch05.Section53.JUpperBoundWeakNorms.ch02_responseIntegrand_integrableOn
      U a p r v
  have hpart := Recurrence.volumeAverage_eq_sum_weight_of_aePartition
    (fun i _hi => (V i).measurableSet) hsub hdisj hnull hint hcell0
    U.isDomain.volume_lt_top.ne
  have hcell : ∀ i ∈ Z,
      (volume (V i).carrier).toReal / (volume U.carrier).toReal *
          responseValue (V i) (b i) p r (z i) =
        (volume (V i).carrier).toReal / (volume U.carrier).toReal *
          volumeAverage (V i).carrier (responseIntegrand U a p r v) := by
    intro i hi
    congr 1
    rw [responseValue, responseIntegrand_congr (hrep i hi) (hz i hi) p r]
    rfl
  calc
    ∑ i ∈ Z, (volume (V i).carrier).toReal / (volume U.carrier).toReal *
          responseValue (V i) (b i) p r (z i) =
        ∑ i ∈ Z, (volume (V i).carrier).toReal / (volume U.carrier).toReal *
          volumeAverage (V i).carrier (responseIntegrand U a p r v) :=
      Finset.sum_congr rfl hcell
    _ = volumeAverage U.carrier (responseIntegrand U a p r v) := hpart.symm
    _ = responseJ U a p r := by
      rw [responseJ_eq_responseValue_of_isResponseMaximizer hv]
      rfl

/-! ## The subdivision defect identity -/

/-- **The subdivision defect identity.**  The weighted average of the cells'
responses exceeds the parent response by the weighted average of the symmetric
energies of the gradient differences between the cell maximizers and the
restricted parent maximizer. -/
theorem sum_weight_responseJ_sub_responseJ_eq_sum_weight_secondVariation
    {ι : Type*} {Z : Finset ι} {U : Domain d} {V : ι → Domain d}
    {a : CoeffOn U} {b : ∀ i, CoeffOn (V i)}
    (hrep : ∀ i ∈ Z, (b i).toCoeffField = a.toCoeffField)
    (hsub : ∀ i ∈ Z, (V i).carrier ⊆ U.carrier)
    (hdisj : (↑Z : Set ι).PairwiseDisjoint fun i => (V i).carrier)
    (hnull : volume (U.carrier \ ⋃ i ∈ (↑Z : Set ι), (V i).carrier) = 0)
    {p r : Vec d} {v : Solution U a} (hv : Book.Ch02.IsResponseMaximizer U a p r v)
    {z : ∀ i, Solution (V i) (b i)}
    (hz : ∀ i ∈ Z, (z i).toH1.grad = v.toH1.grad) :
    (∑ i ∈ Z, (volume (V i).carrier).toReal / (volume U.carrier).toReal *
          responseJ (V i) (b i) p r) - responseJ U a p r =
      ∑ i ∈ Z, (volume (V i).carrier).toReal / (volume U.carrier).toReal *
        secondVariationEnergyValue (V i) (b i)
          (canonicalResponseSolution (V i) (b i) p r) (z i) := by
  have hA := sum_weight_responseValue_eq_responseJ hrep hsub hdisj hnull hv hz
  have hstep : ∀ i ∈ Z,
      (volume (V i).carrier).toReal / (volume U.carrier).toReal *
          responseJ (V i) (b i) p r =
        (volume (V i).carrier).toReal / (volume U.carrier).toReal *
            responseValue (V i) (b i) p r (z i) +
          (volume (V i).carrier).toReal / (volume U.carrier).toReal *
            secondVariationEnergyValue (V i) (b i)
              (canonicalResponseSolution (V i) (b i) p r) (z i) := by
    intro i _hi
    have h := secondVariation_eq_of_isResponseMaximizer
      (canonicalResponseSolution_isMaximizer (V i) (b i) p r) (z i)
    have hsum : responseJ (V i) (b i) p r =
        responseValue (V i) (b i) p r (z i) +
          secondVariationEnergyValue (V i) (b i)
            (canonicalResponseSolution (V i) (b i) p r) (z i) := by
      linarith only [h]
    rw [hsum]
    ring
  rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, hA]
  ring

/-! ## Nonnegativity -/

end

end Response
end HighContrast
end HCPolySupport
