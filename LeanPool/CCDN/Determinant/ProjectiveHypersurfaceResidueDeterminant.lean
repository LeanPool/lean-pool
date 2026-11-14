/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Determinant.BlockDeterminant
public import LeanPool.CCDN.Determinant.ProjectiveHypersurfaceReduction
public import Mathlib.LinearAlgebra.Projectivization.Cardinality
import LeanPool.CCDN.Determinant.HypersurfaceMultiplicityEstimate

/-!
Projective hypersurface residue classes give the sharp single-prime
determinant bound in every positive dimension. The residue partition, chart
units and positive local multiplicities are all constructed from the equation.

Sharp aggregation of local hypersurface exponents. Summing the exact
integer cutoff inequalities before optimizing preserves the leading constant
and gives a linear error independent of all residue multiplicities.
-/

@[expose] public section
namespace CCDN
noncomputable section

/-- A common cutoff aggregates without any loss in the leading coefficient. -/
theorem aggregate_hypersurface_exponents_cutoff {ι : Type*} [Fintype ι]
    (m : ℕ) (hm : 0 < m) (s μ : ι → ℕ) (hμ : ∀ i, 0 < μ i) (K : ℕ) :
    (∑ i, s i) * K ≤ (∑ i, hypersurfaceMultiplicityExponent m (μ i) (s i)) +
      (∑ i, μ i) * (m + K).choose (m + 1) := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    hypersurfaceMultiplicityExponent_cutoff_pos m (s i) K hm (hμ i))
  simpa only [Finset.sum_add_distrib, ← Finset.sum_mul] using h

/-- The sharp leading term depends only on the sum of local multiplicities,
with exactly the same dimension-only error as the single-residue bound. -/
private theorem aggregate_hypersurface_exponents_lower_bound {ι : Type*} [Fintype ι]
    (m : ℕ) (hm : 0 < m) (s μ : ι → ℕ) (hμ : ∀ i, 0 < μ i)
    (hμsum : 0 < ∑ i, μ i) :
    ((m.factorial : ℝ) / (∑ i, μ i : ℕ)) ^ (1 / (m : ℝ)) * m / (m + 1) *
      (∑ i, s i : ℕ) ^ (1 + 1 / (m : ℝ)) - (m + 1 : ℝ) * (∑ i, s i : ℕ) ≤
        (∑ i, hypersurfaceMultiplicityExponent m (μ i) (s i) : ℕ) :=
  local_exponent_separated_lower_bound m (∑ i, s i) _ hm hμsum
    (aggregate_hypersurface_exponents_cutoff m hm s μ hμ)

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial

/-- Every affine chart of a homogeneous integer polynomial whose reduction modulo `p` is nonzero
also has nonzero reduction modulo `p`. -/
lemma projectiveHypersurfaceChart_mod_ne_zero {n p d : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d)
    (hf0 : map (Int.castRingHom (ZMod p)) f ≠ 0) (k : Fin (n + 3)) :
    map (Int.castRingHom (ZMod p)) (projectiveHypersurfaceChart k f) ≠ 0 := by
  intro h
  have hc :
      affineChart (n + 2) (rename (Equiv.swap 0 k) (map (Int.castRingHom (ZMod p)) f)) = 0 := by
    rw [← map_rename, affineChart_map]
    exact h
  have he : rename (Equiv.swap 0 k) (map (Int.castRingHom (ZMod p)) f) = 0 :=
    affineChart_injective_on_homogeneous (hf.map _).rename_isHomogeneous
      (isHomogeneous_zero _ _ d) (by simpa only [map_zero] using hc)
  apply hf0
  exact (rename_injective (Equiv.swap 0 k) (Equiv.swap 0 k).injective)
    (he.trans (map_zero _).symm)

/-- The `𝔽_p`-points of the reduction modulo `p` of the projective hypersurface `f = 0` in `ℙⁿ⁺²`.
-/
def ProjectiveHypersurfaceResidue {n : ℕ} (f : MvPolynomial (Fin (n + 3)) ℤ) (p : ℕ)
    [Fact p.Prime] :=
  {r : ProjectiveResidueSpace (n + 2) p | eval r.rep (map (Int.castRingHom (ZMod p)) f) = 0}

instance {n : ℕ} (f : MvPolynomial (Fin (n + 3)) ℤ) (p : ℕ) [Fact p.Prime] :
    Fintype (ProjectiveHypersurfaceResidue f p) := Fintype.ofFinite _

/-- The multiplicity of the reduced hypersurface `f mod p` at the residue point `r`, computed in the
affine chart determined by the pivot of `r`. -/
def projectiveHypersurfaceResidueMultiplicity {n p d : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d)
    (hf0 : map (Int.castRingHom (ZMod p)) f ≠ 0) (r : ProjectiveHypersurfaceResidue f p) : ℕ :=
  Classical.choose (exists_hypersurface_reduction_multiplicity
    (projectiveHypersurfaceChart (hypersurfaceResiduePivot r.val) f)
    (hypersurfaceResidueChartLift r.val)
    (projectiveHypersurfaceChart_mod_ne_zero f hf hf0 _)
    (hypersurfaceResidueChartLift_zero f hf r.val r.property))

/-- The multiplicity of `f mod p` at a residue point `r` is between `1` and the degree `d`; in the
chart of `r`, translated so that `r` is the origin, the reduced equation lies in that power of the
ideal of the origin and has a nonzero homogeneous component of that degree. This is the local
multiplicity used in CCDN Corollary 2.5. -/
theorem projectiveHypersurfaceResidueMultiplicity_spec {n p d : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d)
    (hf0 : map (Int.castRingHom (ZMod p)) f ≠ 0) (r : ProjectiveHypersurfaceResidue f p) :
    0 < projectiveHypersurfaceResidueMultiplicity f hf hf0 r ∧
    projectiveHypersurfaceResidueMultiplicity f hf hf0 r ≤ d ∧
    map (Int.castRingHom (ZMod p)) (originShift (hypersurfaceResidueChartLift r.val)
      (projectiveHypersurfaceChart (hypersurfaceResiduePivot r.val) f)) ∈
        idealOfVars (Fin (n + 2)) (ZMod p) ^ projectiveHypersurfaceResidueMultiplicity f hf hf0 r ∧
    homogeneousComponent (projectiveHypersurfaceResidueMultiplicity f hf hf0 r)
      (map (Int.castRingHom (ZMod p)) (originShift (hypersurfaceResidueChartLift r.val)
        (projectiveHypersurfaceChart (hypersurfaceResiduePivot r.val) f))) ≠ 0 := by
  have h := Classical.choose_spec (exists_hypersurface_reduction_multiplicity
    (projectiveHypersurfaceChart (hypersurfaceResiduePivot r.val) f)
    (hypersurfaceResidueChartLift r.val)
    (projectiveHypersurfaceChart_mod_ne_zero f hf hf0 _)
    (hypersurfaceResidueChartLift_zero f hf r.val r.property))
  refine ⟨h.1, h.2.1.trans ?_, h.2.2⟩
  exact (affineChart_totalDegree_le _).trans hf.rename_isHomogeneous.totalDegree_le

/-- The total residue multiplicity of the projective hypersurface `f = 0` modulo `p`: the sum of the
multiplicities of `f mod p` at all of its `𝔽_p`-points. This is the quantity of CCDN Proposition
2.6. -/
def projectiveHypersurfaceTotalMultiplicity {n p d : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d)
    (hf0 : map (Int.castRingHom (ZMod p)) f ≠ 0) : ℕ :=
  ∑ r : ProjectiveHypersurfaceResidue f p, projectiveHypersurfaceResidueMultiplicity f hf hf0 r

/-- The total residue multiplicity of `f mod p` lies between the number of its `𝔽_p`-points and `d`
times that number. -/
theorem projectiveHypersurfaceTotalMultiplicity_bounds {n p d : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d)
    (hf0 : map (Int.castRingHom (ZMod p)) f ≠ 0) :
    Fintype.card (ProjectiveHypersurfaceResidue f p) ≤
      projectiveHypersurfaceTotalMultiplicity f hf hf0 ∧
    projectiveHypersurfaceTotalMultiplicity f hf hf0 ≤
      Fintype.card (ProjectiveHypersurfaceResidue f p) * d := by
  constructor
  · calc _ = ∑ _r : ProjectiveHypersurfaceResidue f p, 1 := by simp
         _ ≤ _ :=
           Finset.sum_le_sum fun r _ =>
             (projectiveHypersurfaceResidueMultiplicity_spec f hf hf0 r).1
  · calc _ ≤ ∑ _r : ProjectiveHypersurfaceResidue f p, d :=
           Finset.sum_le_sum fun r _ =>
             (projectiveHypersurfaceResidueMultiplicity_spec f hf hf0 r).2.1
         _ = _ := by simp

/-- Primitive zeros construct all local data. The resulting divisor has the
sharp leading constant in terms of the total residue multiplicity. -/
theorem projective_hypersurface_reduction_minorGcd {n s N p d M : ℕ}
    [Fact p.Prime] (hs : 0 < s)
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d)
    (hf0 : map (Int.castRingHom (ZMod p)) f ≠ 0)
    (F : Fin N → MvPolynomial (Fin (n + 3)) ℤ) (hF : ∀ j, (F j).IsHomogeneous M)
    (z : Fin s → IntPoint (n + 3)) (hprim : ∀ i, Finset.univ.gcd (z i) = 1)
    (hz : ∀ i, eval (z i) f = 0) :
    0 < projectiveHypersurfaceTotalMultiplicity f hf hf0 ∧ ∃ e : ℕ,
      (∀ K : ℕ, s * K ≤ e + projectiveHypersurfaceTotalMultiplicity f hf hf0 *
        (n + 1 + K).choose (n + 2)) ∧
      (((n + 1).factorial : ℝ) / projectiveHypersurfaceTotalMultiplicity f hf hf0) ^
        (1 / (n + 1 : ℝ)) * (n + 1 : ℝ) / (n + 2 : ℝ) *
        (s : ℝ) ^ (1 + 1 / (n + 1 : ℝ)) - (n + 2 : ℝ) * s ≤ e ∧
      (p : ℤ) ^ e ∣ Int.Matrix.minorGcd (Matrix.of fun i j => eval (z i) (F j)) := by
  classical
  let red : Fin s → ProjectiveHypersurfaceResidue f p := fun i =>
    ⟨primitiveProjectiveReduction (z i) (hprim i),
      primitiveProjectiveReduction_zero f hf (z i) (hprim i) (hz i)⟩
  let c := Fintype.card (ProjectiveHypersurfaceResidue f p)
  let E := Fintype.equivFin (ProjectiveHypersurfaceResidue f p)
  let label : Fin s → Fin c := fun i => E (red i)
  let k : Fin c → Fin (n + 3) := fun i => hypersurfaceResiduePivot (E.symm i).val
  let a : Fin c → Fin (n + 2) → ℤ := fun i => hypersurfaceResidueChartLift (E.symm i).val
  let μ : Fin c → ℕ := fun i => projectiveHypersurfaceResidueMultiplicity f hf hf0 (E.symm i)
  let sizes : Fin c → ℕ := fun i => Fintype.card {j : Fin s // label j = i}
  let e := ∑ i : Fin c, hypersurfaceMultiplicityExponent (n + 1) (μ i) (sizes i)
  have hμ (i : Fin c) := projectiveHypersurfaceResidueMultiplicity_spec f hf hf0 (E.symm i)
  have hsum : ∑ i : Fin c, μ i = projectiveHypersurfaceTotalMultiplicity f hf hf0 :=
    E.symm.sum_comp (projectiveHypersurfaceResidueMultiplicity f hf hf0)
  have hsize : ∑ i : Fin c, sizes i = s := sum_residue_class_sizes label
  have hc : 0 < c := Fintype.card_pos_iff.mpr ⟨red ⟨0, hs⟩⟩
  have hpos : 0 < projectiveHypersurfaceTotalMultiplicity f hf hf0 :=
    hc.trans_le (projectiveHypersurfaceTotalMultiplicity_bounds f hf hf0).1
  refine ⟨hpos, e, ?_, ?_, ?_⟩
  · intro K
    have h := aggregate_hypersurface_exponents_cutoff (n + 1) (by omega) sizes μ
      (fun i => (hμ i).1) K
    simpa only [hsum, hsize] using h
  · have h := aggregate_hypersurface_exponents_lower_bound (n + 1) (by omega) sizes μ
      (fun i => (hμ i).1) (by rw [hsum]; exact hpos)
    simpa only [hsum, hsize, Nat.cast_add, Nat.cast_one,
      show (n : ℝ) + 1 + 1 = n + 2 by ring] using h
  · apply projective_hypersurface_residue_minorGcd f hf F hF z label k a μ
    · intro i
      exact (hμ i).2.2.1
    · intro i
      exact (hμ i).2.2.2
    · intro i
      have h := (primitiveProjectiveReduction_hypersurface_chart
        (z i) (hprim i) (red i).val rfl).1
      simpa only [k, label, E.symm_apply_apply] using h
    · intro i j
      have h := (primitiveProjectiveReduction_hypersurface_chart
        (z i) (hprim i) (red i).val rfl).2 j
      simpa only [k, a, label, E.symm_apply_apply] using h
    · exact hz

/-- For primitive integral zeros of a homogeneous hypersurface and homogeneous columns of a
common degree, `p^e` divides the gcd of the maximal minors, where `e` is bounded below in terms
of the total residue multiplicity. The number of rows and of residue points may be zero. -/
theorem projective_hypersurface_minorGcd_bound {n s N p d M : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d)
    (hf0 : map (Int.castRingHom (ZMod p)) f ≠ 0)
    (F : Fin N → MvPolynomial (Fin (n + 3)) ℤ) (hF : ∀ j, (F j).IsHomogeneous M)
    (z : Fin s → IntPoint (n + 3)) (hprim : ∀ i, Finset.univ.gcd (z i) = 1)
    (hz : ∀ i, eval (z i) f = 0) :
    ∃ e : ℕ,
      (((n + 1).factorial : ℝ) / projectiveHypersurfaceTotalMultiplicity f hf hf0) ^
        (1 / (n + 1 : ℝ)) * (n + 1 : ℝ) / (n + 2 : ℝ) *
        (s : ℝ) ^ (1 + 1 / (n + 1 : ℝ)) - (n + 2 : ℝ) * s ≤ e ∧
      (p : ℤ) ^ e ∣ Int.Matrix.minorGcd (Matrix.of fun i j => eval (z i) (F j)) := by
  by_cases hs : 0 < s
  · obtain ⟨_, e, _, he, hd⟩ :=
      projective_hypersurface_reduction_minorGcd hs f hf hf0 F hF z hprim hz
    exact ⟨e, he, hd⟩
  · have hs0 : s = 0 := by omega
    refine ⟨0, ?_, by simp⟩
    simp only [hs0, Nat.cast_zero, Real.zero_rpow (by positivity : (1 : ℝ) + 1 / (n + 1 : ℝ) ≠ 0),
      mul_zero, sub_zero, le_refl]

end
end CCDN
