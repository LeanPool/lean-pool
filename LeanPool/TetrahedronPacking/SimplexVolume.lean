/-
Copyright (c) 2026 Mike Lady. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mike Lady
-/

-- Modified for Lean Pool.

module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Lebesgue volume of a tetrahedron from its edge determinant

The regions obtained by sorting the coordinates partition the unit cube
up to the null sets where coordinates tie. Coordinate permutations preserve
volume. The increasing region is a tetrahedron, and an affine image of it
gives any tetrahedron with the determinant scaling of Lebesgue measure.
-/

@[expose] public section

namespace TetrahedronPacking

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal Pointwise Function

private def orderedCube {n : ℕ} (σ : Equiv.Perm (Fin n)) : Set (Fin n → ℝ) :=
  Icc 0 1 ∩ {x | Monotone (x ∘ σ)}

example : (0 : Fin 3 → ℝ) ∈ orderedCube (Equiv.refl _) := by
  simp [orderedCube, Monotone]

example : (-1 : Fin 3 → ℝ) ∉ orderedCube (Equiv.refl _) := by
  intro h
  have h₀ := h.1.1 0
  norm_num at h₀

private theorem orderedCube_measurable {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    MeasurableSet (orderedCube σ) := by
  refine measurableSet_Icc.inter ?_
  simp only [Monotone, Function.comp_apply, ofPred_forall]
  exact MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun j =>
    MeasurableSet.iInter fun _ => measurableSet_le (measurable_pi_apply (σ i))
      (measurable_pi_apply (σ j))))

private theorem ae_distinct_coordinates (n : ℕ) :
    ∀ᵐ x : Fin n → ℝ ∂volume, Function.Injective x := by
  simp only [Function.Injective, ae_all_iff]
  intro i j
  by_cases hij : i = j
  · exact Filter.Eventually.of_forall fun _ _ => hij
  let f : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
    (LinearMap.proj i : (Fin n → ℝ) →ₗ[ℝ] ℝ) - LinearMap.proj j
  have hne : LinearMap.ker f ≠ ⊤ := by
    intro h
    have hk : Pi.single i (1 : ℝ) ∈ LinearMap.ker f := h.symm ▸ Submodule.mem_top
    have hk' := LinearMap.mem_ker.mp hk
    simp [f, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hij)] at hk'
  apply ae_iff.mpr
  convert addHaar_submodule volume (LinearMap.ker f) hne using 2
  ext x
  simp [f, hij, sub_eq_zero]

private theorem orderedCube_volume (n : ℕ) :
    volume (orderedCube (Equiv.refl (Fin n))) = (n.factorial : ℝ≥0∞)⁻¹ := by
  classical
  have hcover : (⋃ σ : Equiv.Perm (Fin n), orderedCube σ) = Icc 0 1 := by
    ext x
    constructor
    · rintro hx
      obtain ⟨σ, hx⟩ := mem_iUnion.mp hx
      exact hx.1
    · intro hx
      exact mem_iUnion.mpr ⟨Tuple.sort x, hx, Tuple.monotone_sort x⟩
  have hdisj : Pairwise (AEDisjoint (volume : Measure (Fin n → ℝ)) on orderedCube) := by
    intro σ τ hne
    change volume (orderedCube σ ∩ orderedCube τ) = 0
    apply measure_mono_null _ (ae_iff.mp (ae_distinct_coordinates n))
    rintro x ⟨hσ, hτ⟩ hx
    exact hne (Equiv.ext fun i => hx (congrFun (Tuple.unique_monotone hσ.2 hτ.2) i))
  have heq (σ : Equiv.Perm (Fin n)) :
      volume (orderedCube σ) = volume (orderedCube (Equiv.refl (Fin n))) := by
    let e := MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) σ.symm
    have hp : MeasurePreserving e volume volume :=
      volume_measurePreserving_piCongrLeft _ _
    have hp' := hp.measure_preimage
      (orderedCube_measurable (Equiv.refl (Fin n))).nullMeasurableSet
    rw [← hp']
    congr 1
    ext x
    change (x ∈ Icc 0 1 ∧ Monotone (x ∘ σ)) ↔
      (e x ∈ Icc 0 1 ∧ Monotone (fun i => e x i))
    have he (i) : e x i = x (σ i) := by
      simp [e, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
    simp only [mem_Icc, Pi.le_def, Pi.zero_apply, Pi.one_apply, he, Function.comp_def]
    exact ⟨fun ⟨h, hm⟩ => ⟨⟨fun i => h.1 (σ i), fun i => h.2 (σ i)⟩, hm⟩,
      fun ⟨h, hm⟩ => ⟨⟨σ.surjective.forall.mpr h.1, σ.surjective.forall.mpr h.2⟩, hm⟩⟩
  have h := measure_iUnion₀ hdisj (fun σ => (orderedCube_measurable σ).nullMeasurableSet)
  rw [hcover, Real.volume_Icc_pi, tsum_fintype] at h
  simp only [Pi.one_apply, Pi.zero_apply, sub_zero, ENNReal.ofReal_one, Finset.prod_const_one,
    heq, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul] at h
  have hn : (n.factorial : ℝ≥0∞) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hfin := ENNReal.natCast_ne_top n.factorial
  exact (ENNReal.mul_right_inj hn hfin).mp
    (h.symm.trans (ENNReal.mul_inv_cancel hn hfin).symm)

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.vecHead Matrix.vecTail

private def referenceVertex : Fin 4 → Fin 3 → ℝ :=
  ![![0, 0, 0], ![0, 0, 1], ![0, 1, 1], ![1, 1, 1]]

private theorem orderedCube_eq_hull :
    orderedCube (Equiv.refl (Fin 3)) = convexHull ℝ (range referenceVertex) := by
  apply Subset.antisymm
  · intro x hx
    have hx0 := hx.1.1 0
    have hx2 := hx.1.2 2
    have h01 := hx.2 (show (0 : Fin 3) ≤ 1 by decide)
    have h12 := hx.2 (show (1 : Fin 3) ≤ 2 by decide)
    change 0 ≤ x 0 at hx0
    change x 2 ≤ 1 at hx2
    change x 0 ≤ x 1 at h01
    change x 1 ≤ x 2 at h12
    let w : Fin 4 → ℝ := ![1 - x 2, x 2 - x 1, x 1 - x 0, x 0]
    refine mem_convexHull_of_exists_fintype (s := range referenceVertex) w referenceVertex ?_ ?_
      (fun i => ⟨i, rfl⟩) ?_
    · intro i
      fin_cases i <;> simp [w] <;> linarith
    · simp [Fin.sum_univ_four, w]
    · ext j
      fin_cases j <;> simp [Fin.sum_univ_four, referenceVertex, w]
  · apply convexHull_min
    · rintro _ ⟨i, rfl⟩
      constructor
      · constructor <;> intro j <;> fin_cases i <;> fin_cases j <;>
          norm_num [referenceVertex, Pi.one_apply]
      · intro j k hjk
        change j ≤ k at hjk
        change referenceVertex i j ≤ referenceVertex i k
        fin_cases i <;> fin_cases j <;> fin_cases k <;>
          norm_num [referenceVertex, Fin.le_def] at *
    · intro x hx y hy a b ha hb hab
      refine ⟨convex_Icc (𝕜 := ℝ) 0 1 hx.1 hy.1 ha hb hab, ?_⟩
      intro i j hij
      exact add_le_add (mul_le_mul_of_nonneg_left (hx.2 hij) ha)
        (mul_le_mul_of_nonneg_left (hy.2 hij) hb)

/-- This formula also covers degenerate tetrahedra, whose determinant and
three-dimensional volume both vanish. -/
theorem tetrahedron_volume (v : Fin 4 → Fin 3 → ℝ) :
    volume.real (convexHull ℝ (range v)) =
      |(Matrix.of (fun r (j : Fin 3) => v j.succ r - v 0 r)).det| / 6 := by
  let M : Matrix (Fin 3) (Fin 3) ℝ :=
    Matrix.of fun r => ![v 3 r - v 2 r, v 2 r - v 1 r, v 1 r - v 0 r]
  let f := Matrix.toLin' M
  have hv (i : Fin 4) : v 0 + f (referenceVertex i) = v i := by
    ext r
    fin_cases i <;> simp [f, M, Matrix.toLin'_apply, referenceVertex]
  have hvset : v 0 +ᵥ (f '' range referenceVertex) = range v := by
    change (fun x => v 0 + x) '' (f '' range referenceVertex) = _
    rw [image_image, ← range_comp']
    exact congrArg range (funext hv)
  have hvol : volume (convexHull ℝ (range referenceVertex)) = (6 : ℝ≥0∞)⁻¹ := by
    rw [← orderedCube_eq_hull, orderedCube_volume]
    norm_num [Nat.factorial]
  have hdet : M.det = -(Matrix.of (fun r (j : Fin 3) => v j.succ r - v 0 r)).det := by
    simp [M, Matrix.det_fin_three, Fin.succ]
    ring
  rw [← hvset, convexHull_vadd, ← f.image_convexHull, measureReal_def, measure_vadd,
    addHaar_image_linearMap, LinearMap.det_toLin', hvol, hdet, abs_neg,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_inv]
  norm_num [div_eq_mul_inv]

end TetrahedronPacking
