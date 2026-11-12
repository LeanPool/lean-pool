/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Topology.Instances.Matrix
public import LeanPool.ApollonianSuperharmonic.BandDiskExteriorDensity
public import LeanPool.ApollonianSuperharmonic.CircleMatrixEnclosureCriterion

-- [TABLET NODE: TraceNonpositivePackingApproximation]

/-!
# TraceNonpositivePackingApproximation

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem TraceNonpositivePackingApproximation
    (A : Matrix (Fin 2) (Fin 2) Real) (hA : A.IsSymm)
    (htrace : Matrix.trace A ≤ 0) :
    ∃ Aseq : Nat → Matrix (Fin 2) (Fin 2) Real,
      (∀ i j, Filter.Tendsto (fun n ↦ Aseq n i j) Filter.atTop
        (nhds (A i j))) ∧
      ∃ Cseq : Nat → BandCircle, ∀ n,
        (CircleMatrix (Cseq n) - Aseq n).PosSemidef := by
-- BODY
  classical
  let x := (SymmetricMatrixCoordinates A).1
  let r := (SymmetricMatrixCoordinates A).2
  by_cases hExterior : BandPackingExterior x
  · let Cseq : Nat → BandCircle := fun n =>
      Classical.choose (BandDiskExteriorDensity x hExterior (1 / (n + 1)) (by positivity))
    let Aseq : Nat → Matrix (Fin 2) (Fin 2) Real := fun n =>
      (2 : Real)⁻¹ •
        ![![r + (BandCircleEuclideanData (Cseq n)).center.re,
            (BandCircleEuclideanData (Cseq n)).center.im],
          ![(BandCircleEuclideanData (Cseq n)).center.im,
            r - (BandCircleEuclideanData (Cseq n)).center.re]]
    refine ⟨Aseq, ?_, Cseq, ?_⟩
    · intro i j
      have hcenter : Filter.Tendsto
          (fun n => (BandCircleEuclideanData (Cseq n)).center) Filter.atTop (nhds x) := by
        have hsucc : Filter.Tendsto (fun n : Nat => n + 1) Filter.atTop Filter.atTop := by
          apply Filter.tendsto_atTop.mpr
          intro b
          filter_upwards [Filter.eventually_ge_atTop b] with n hn
          exact Nat.le_trans hn (Nat.le_succ n)
        have hden : Filter.Tendsto
            (fun n : Nat => ((n + 1 : Nat) : Real)) Filter.atTop Filter.atTop := by
          simpa [Function.comp_def] using
            (tendsto_natCast_atTop_atTop (R := Real)).comp hsucc
        apply tendsto_iff_dist_tendsto_zero.mpr
        have hlim : Filter.Tendsto
            (fun n : Nat => (1 : Real) / ((n + 1 : Nat) : Real)) Filter.atTop (nhds 0) := by
          exact tendsto_const_nhds.div_atTop (f := fun _ : Nat => (1 : Real)) hden
        refine squeeze_zero' (Filter.Eventually.of_forall (fun n => dist_nonneg)) ?_ hlim
        filter_upwards [] with n
        simpa [Cseq, dist_comm, Nat.cast_add, Nat.cast_one] using
          (Classical.choose_spec
            (BandDiskExteriorDensity x hExterior (1 / (n + 1)) (by positivity))).2.le
      have hreal : Filter.Tendsto
          (fun n => (BandCircleEuclideanData (Cseq n)).center.re) Filter.atTop (nhds x.re) := by
        have hpart : Filter.Tendsto Complex.re (nhds x) (nhds x.re) :=
          Complex.continuous_re.continuousAt
        exact hpart.comp hcenter
      have himag : Filter.Tendsto
          (fun n => (BandCircleEuclideanData (Cseq n)).center.im) Filter.atTop (nhds x.im) := by
        have hpart : Filter.Tendsto Complex.im (nhds x) (nhds x.im) :=
          Complex.continuous_im.continuousAt
        exact hpart.comp hcenter
      have htraceeq : Matrix.trace A = A 0 0 + A 1 1 := by
        simp [Matrix.trace, Fin.sum_univ_two]
      have hsymentry : A 0 1 = A 1 0 := by
        simpa [Matrix.transpose_apply] using (congrFun (congrFun hA.eq 0) 1).symm
      fin_cases i <;> fin_cases j
      · convert ((hreal.const_add r).const_mul (2 : Real)⁻¹) using 1 <;>
          simp [Aseq, x, r, SymmetricMatrixCoordinates, htraceeq]; ring
      · convert (himag.const_mul (2 : Real)⁻¹) using 1 <;>
          simp [Aseq, x, r, SymmetricMatrixCoordinates]
      · convert (himag.const_mul (2 : Real)⁻¹) using 1 <;>
          simp [Aseq, x, r, SymmetricMatrixCoordinates, hsymentry]
      · convert ((hreal.neg.const_add r).const_mul (2 : Real)⁻¹) using 1 <;>
          simp [Aseq, x, r, SymmetricMatrixCoordinates, htraceeq] <;> try ring
    · intro n
      have hsym : (Aseq n).IsSymm := by
        change Matrix.transpose (Aseq n) = Aseq n
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Aseq, Matrix.transpose]
      have hcoords : SymmetricMatrixCoordinates (Aseq n) =
          ((BandCircleEuclideanData (Cseq n)).center, r) := by
        apply Prod.ext
        · apply Complex.ext <;> simp [Aseq, SymmetricMatrixCoordinates]; ring
        · simp [Aseq, SymmetricMatrixCoordinates, Matrix.trace, Fin.sum_univ_two,
            Matrix.diag]; ring
      apply (CircleMatrixEnclosureCriterion (Aseq n) hsym (Cseq n)).1.mpr
      rw [hcoords]
      simp only [dist_self, zero_add]
      have hr : r ≤ 0 := by
        change Matrix.trace A ≤ 0
        exact htrace
      linarith [hr, (BandCircleEuclideanData (Cseq n)).radius_pos]
  · have hC : ∃ C : BandCircle,
        dist x (BandCircleEuclideanData C).center <
          (BandCircleEuclideanData C).radius := by
      change ¬ (∀ C : BandCircle,
        (BandCircleEuclideanData C).radius ≤ dist x
          (BandCircleEuclideanData C).center) at hExterior
      obtain ⟨C, hC⟩ := Classical.not_forall.mp hExterior
      exact ⟨C, lt_of_not_ge hC⟩
    obtain ⟨C, hC⟩ := hC
    refine ⟨fun _ => A, ?_, fun _ => C, ?_⟩
    · intro i j
      exact tendsto_const_nhds
    · intro n
      apply (CircleMatrixEnclosureCriterion A hA C).1.mpr
      dsimp [x, r] at hC ⊢
      have hr : (SymmetricMatrixCoordinates A).2 ≤ 0 := by
        change Matrix.trace A ≤ 0
        exact htrace
      linarith [hr, hC]

end ApollonianSuperharmonic

end
