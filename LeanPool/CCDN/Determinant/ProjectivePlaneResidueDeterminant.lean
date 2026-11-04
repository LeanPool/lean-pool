/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Determinant.ProjectiveHypersurfaceResidueDeterminant
import LeanPool.CCDN.Determinant.ResidueAggregation

/-! The residue partition and local multiplicities of a homogeneous
plane curve supply a global single-prime determinant divisor. The residue
points and their multiplicities are the case `n = 0` of the hypersurface
construction in `ProjectiveHypersurfaceResidueDeterminant`. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The residue points of a projective plane curve: the case `n = 0` of
`ProjectiveHypersurfaceResidue`. -/
abbrev ProjectivePlaneResidue (f : MvPolynomial (Fin 3) ℤ) (p : ℕ) [Fact p.Prime] :=
  ProjectiveHypersurfaceResidue (n := 0) f p

/-- The local multiplicity at a residue point of a projective plane curve. -/
abbrev projectivePlaneResidueMultiplicity {p d : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin 3) ℤ) (hf : f.IsHomogeneous d)
    (hf0 : map (Int.castRingHom (ZMod p)) f ≠ 0) (r : ProjectivePlaneResidue f p) : ℕ :=
  projectiveHypersurfaceResidueMultiplicity f hf hf0 r

/-- The multiplicity of the reduction `f mod p` of a plane curve at a residue point `r` is between
`1` and the degree `d`; in the chart of `r`, translated so that `r` is the origin, the reduced
equation lies in that power of the ideal of the origin and has a nonzero homogeneous component of
that degree. -/
theorem projectivePlaneResidueMultiplicity_spec {p d : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin 3) ℤ) (hf : f.IsHomogeneous d)
    (hf0 : map (Int.castRingHom (ZMod p)) f ≠ 0) (r : ProjectivePlaneResidue f p) :
    0 < projectivePlaneResidueMultiplicity f hf hf0 r ∧
    projectivePlaneResidueMultiplicity f hf hf0 r ≤ d ∧
    map (Int.castRingHom (ZMod p)) (originShift (projectiveResidueChartLift r.val)
      (projectivePlaneChart (projectiveResiduePivot r.val) f)) ∈
        idealOfVars (Fin 2) (ZMod p) ^ projectivePlaneResidueMultiplicity f hf hf0 r ∧
    homogeneousComponent (projectivePlaneResidueMultiplicity f hf hf0 r)
      (map (Int.castRingHom (ZMod p)) (originShift (projectiveResidueChartLift r.val)
        (projectivePlaneChart (projectiveResiduePivot r.val) f))) ≠ 0 :=
  projectiveHypersurfaceResidueMultiplicity_spec f hf hf0 r

/-- The total residue multiplicity of a projective plane curve modulo `p`. -/
abbrev projectivePlaneTotalMultiplicity {p d : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin 3) ℤ) (hf : f.IsHomogeneous d)
    (hf0 : map (Int.castRingHom (ZMod p)) f ≠ 0) : ℕ :=
  projectiveHypersurfaceTotalMultiplicity f hf hf0

private theorem projectivePlaneTotalMultiplicity_bounds {p d : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin 3) ℤ) (hf : f.IsHomogeneous d)
    (hf0 : map (Int.castRingHom (ZMod p)) f ≠ 0) :
    Fintype.card (ProjectivePlaneResidue f p) ≤ projectivePlaneTotalMultiplicity f hf hf0 ∧
    projectivePlaneTotalMultiplicity f hf hf0 ≤ Fintype.card (ProjectivePlaneResidue f p) * d :=
  projectiveHypersurfaceTotalMultiplicity_bounds f hf hf0

/-- Primitive integer zeros determine the residue partition, unit chart
coordinates and positive local multiplicities. The divisor's leading
quadratic constant uses their total multiplicity. -/
theorem projective_reduction_minorGcd {s N p d M : ℕ} [Fact p.Prime] (hs : 0 < s)
    (f : MvPolynomial (Fin 3) ℤ) (hf : f.IsHomogeneous d)
    (hf0 : map (Int.castRingHom (ZMod p)) f ≠ 0)
    (F : Fin N → MvPolynomial (Fin 3) ℤ) (hF : ∀ j, (F j).IsHomogeneous M)
    (z : Fin s → IntPoint 3) (hprim : ∀ i, Finset.univ.gcd (z i) = 1)
    (hz : ∀ i, eval (z i) f = 0) :
    0 < projectivePlaneTotalMultiplicity f hf hf0 ∧ ∃ e : ℕ,
      s ^ 2 ≤ 2 * projectivePlaneTotalMultiplicity f hf hf0 * (e + s) ∧
      (s : ℝ) ^ 2 / (2 * projectivePlaneTotalMultiplicity f hf hf0) - s ≤ e ∧
      (p : ℤ) ^ e ∣ Int.Matrix.minorGcd (Matrix.of fun i j => eval (z i) (F j)) := by
  classical
  let red : Fin s → ProjectivePlaneResidue f p := fun i =>
    ⟨primitiveProjectiveReduction (z i) (hprim i),
      primitiveProjectiveReduction_zero f hf (z i) (hprim i) (hz i)⟩
  let c := Fintype.card (ProjectivePlaneResidue f p)
  let E := Fintype.equivFin (ProjectivePlaneResidue f p)
  let label : Fin s → Fin c := fun i => E (red i)
  let k : Fin c → Fin 3 := fun i => projectiveResiduePivot (E.symm i).val
  let a : Fin c → Fin 2 → ℤ := fun i => projectiveResidueChartLift (E.symm i).val
  let μ : Fin c → ℕ := fun i => projectivePlaneResidueMultiplicity f hf hf0 (E.symm i)
  let n : Fin c → ℕ := fun i => Fintype.card {j : Fin s // label j = i}
  let e := ∑ i : Fin c, multiplicityExponent (n i) (μ i)
  have hμ (i : Fin c) := projectivePlaneResidueMultiplicity_spec f hf hf0 (E.symm i)
  have hsum : ∑ i : Fin c, μ i = projectivePlaneTotalMultiplicity f hf hf0 :=
    E.symm.sum_comp (projectivePlaneResidueMultiplicity f hf hf0)
  have hsize : ∑ i : Fin c, n i = s := sum_residue_class_sizes label
  have hc : 0 < c := Fintype.card_pos_iff.mpr ⟨red ⟨0, hs⟩⟩
  have hpos : 0 < projectivePlaneTotalMultiplicity f hf hf0 :=
    hc.trans_le (projectivePlaneTotalMultiplicity_bounds f hf hf0).1
  refine ⟨hpos, e, ?_, ?_, ?_⟩
  · simpa only [hsum, hsize] using aggregate_multiplicity_exponents Finset.univ n μ
      (fun i _ => (hμ i).1)
  · have h := aggregate_exponent_lower Finset.univ n μ
      (fun i => multiplicityExponent (n i) (μ i))
      (fun i _ => multiplicityExponent_lower_bound _ _ (hμ i).1)
      (N := (projectivePlaneTotalMultiplicity f hf hf0 : ℝ)) (by exact_mod_cast hpos)
      (by rw [hsum])
    simpa only [hsize] using h
  · apply projective_plane_residue_minorGcd f hf F hF z label k a μ
    · intro i
      exact (hμ i).2.2.1
    · intro i
      exact (hμ i).2.2.2
    · intro i
      have h := (primitiveProjectiveReduction_chart (z i) (hprim i) (red i).val rfl).1
      simpa only [k, label, E.symm_apply_apply] using h
    · intro i j
      have h := (primitiveProjectiveReduction_chart (z i) (hprim i) (red i).val rfl).2 j
      simpa only [k, a, label, E.symm_apply_apply] using h
    · exact hz

end
end CCDN
