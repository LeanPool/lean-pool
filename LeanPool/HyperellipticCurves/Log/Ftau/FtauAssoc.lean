/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Ftau.FtauBasic

/-!
# The chart-class layer of the translated law (blueprint `thm:Ftau-assoc`)

The **chart-class layer** of the translated law, consumed by `thm:chart-mem` and the chart
identifications:

* `ChabautyColeman.chartClass`: the Jacobian class of the chart datum at a polydisk point,
  with its congruence and presentation API (`ChabautyColeman.chartClass_congr`,
  `ChabautyColeman.chartClass_eq`) and the negated `τ`-class
  `ChabautyColeman.tauClassNeg`;
* `ChabautyColeman.map_residue_eval_eq`: evaluation commutes with passing to the residue
  field at a polydisk point.

The associativity and commutativity of `F_τ` themselves are established at the fold
(`ChabautyColeman.ftauFoldFGL`, via the fold class engine of
`LeanPool.HyperellipticCurves.Log.Fold.FoldClass`).
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

section EvalChart

open IsLocalRing

variable {O : Type*} [CommRing O] [IsLocalRing O] [UniformSpace O]
  [Fact (IsAdic (IsLocalRing.maximalIdeal O))] [IsUniformAddGroup O] [CompleteSpace O]
  [T2Space O] [IsTopologicalRing O]

/-- The residues of an evaluated polynomial at a point of the maximal ideal agree with
the residues of its center. -/
theorem map_residue_eval_eq {σ : Type*} [Finite σ] {z : σ → O}
    (hz : ∀ s, z s ∈ maximalIdeal O) (P : Polynomial (MvPowerSeries σ O)) :
    (P.map (MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem hz))).map (residue O)
      = (P.map (MvPowerSeries.constantCoeff : MvPowerSeries σ O →+* O)).map
        (residue O) := by
  ext k
  simp only [Polynomial.coeff_map, MvPSeries.evalRingHom_apply]
  have hmem := MvPSeries.eval_sub_constantCoeff_mem (MvPSeries.hasEval_of_mem hz) hz
    (P.coeff k)
  have h0 : residue O (MvPSeries.eval z (P.coeff k)
      - MvPowerSeries.constantCoeff (P.coeff k)) = 0 :=
    (residue_eq_zero_iff _).mpr hmem
  rwa [map_sub, sub_eq_zero] at h0

variable [IsDomain O] {n : ℕ} {f u v w c₁ c₂ : O[X]}
  (hu : u.Monic) (hne : u.natDegree = n) (hv : v.degree < u.degree)
  (hw : v ^ 2 - f = u * w) (hbez : c₁ * u + c₂ * (2 * v) = 1)
  [NeZero (2 : FractionRing O)]
  [Fact (Odd (f.map (algebraMap O (FractionRing O))).natDegree)]
  [Fact (Squarefree (f.map (algebraMap O (FractionRing O))))]

/-- The class represented by the disk chart at a point of the polydisk: the Mumford
ideal of the evaluated chart datum, in the class group over the fraction field. -/
noncomputable def chartClass {z : Fin n → O} (hz : ∀ j, z j ∈ maximalIdeal O) :
    ClassGroup (HypRing (FractionRing O) (f.map (algebraMap O (FractionRing O)))) :=
  ClassGroup.mk0 ⟨mumfordIdeal (f.map (algebraMap O (FractionRing O)))
      ((chartU u n).map ((algebraMap O (FractionRing O)).comp
        (MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem hz))))
      ((chartV hu hne.ge hv hw hbez).map ((algebraMap O (FractionRing O)).comp
        (MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem hz)))),
    mumfordIdeal_mem_nonZeroDivisors (f.map (algebraMap O (FractionRing O)))
      (((chartU_monic hu hne.ge).map ((algebraMap O (FractionRing O)).comp
        (MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem hz)))).ne_zero)
      ((chartV hu hne.ge hv hw hbez).map ((algebraMap O (FractionRing O)).comp
        (MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem hz))))⟩

/-- The chart class in the base-change spelling: the evaluated chart datum, mapped to the
fraction field. The presentation of the two parts is supplied as arguments, so that use
sites read off the class without rewriting inside the `mk0` argument (where the
nonzero-divisor proof depends on the polynomial). -/
theorem chartClass_eq {z : Fin n → O} (hz : ∀ j, z j ∈ maximalIdeal O)
    {U V : (FractionRing O)[X]}
    (hU : ((chartU u n).map (MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem hz))).map
      (algebraMap O (FractionRing O)) = U)
    (hV : ((chartV hu hne.ge hv hw hbez).map
      (MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem hz))).map
        (algebraMap O (FractionRing O)) = V) (hUne : U ≠ 0) :
    chartClass hu hne hv hw hbez hz
      = ClassGroup.mk0 ⟨mumfordIdeal (f.map (algebraMap O (FractionRing O))) U V,
        mumfordIdeal_mem_nonZeroDivisors _ hUne V⟩ := by
  rw [chartClass]
  refine congrArg ClassGroup.mk0 (Subtype.ext ?_)
  change mumfordIdeal _ _ _ = mumfordIdeal _ _ _
  rw [← hU, ← hV, Polynomial.map_map, Polynomial.map_map]

/-- The class of the negated `τ`-datum over the fraction field. -/
noncomputable def tauClassNeg :
    ClassGroup (HypRing (FractionRing O) (f.map (algebraMap O (FractionRing O)))) :=
  ClassGroup.mk0 ⟨mumfordIdeal (f.map (algebraMap O (FractionRing O)))
      (u.map (algebraMap O (FractionRing O))) (-(v.map (algebraMap O (FractionRing O)))),
    mumfordIdeal_mem_nonZeroDivisors (f.map (algebraMap O (FractionRing O)))
      (hu.map (algebraMap O (FractionRing O))).ne_zero
      (-(v.map (algebraMap O (FractionRing O))))⟩

/-- Chart classes at equal points are equal (the membership proofs are irrelevant). -/
theorem chartClass_congr {z z' : Fin n → O} (hzz : z = z')
    (hz : ∀ j, z j ∈ maximalIdeal O) (hz' : ∀ j, z' j ∈ maximalIdeal O) :
    chartClass hu hne hv hw hbez hz = chartClass hu hne hv hw hbez hz' := by
  subst hzz
  rfl

end EvalChart

end ChabautyColeman

end
