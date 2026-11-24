/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.PositivityPerturbation
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.OTChenWeights
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.LocalPotentialIndependence
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.ComplexAnalyticSubvarieties

/-!
# The distance-squared tube around a coordinate plane

Source: Copy-4, step 6 of the proof of `prop:principalization`
(`transcendental-nakamaye-copy4-20260911`), where `φ_U` contains the term
`B r_W²` and `B` is chosen so that a form positive along `T_W` becomes positive
in all directions on a tube around `W`.

In a chart flattening the submanifold (`RegularAtDim`) the submanifold is the
standard plane `complexCoordinatePlane n k` and the squared distance to it is

  `planeDistSq n k z = ∑_{i ≥ k} ‖z i‖²`.

Two facts are proved here, and they are exactly the two the manuscript uses.

* `leviForm_planeDistSq`: the Levi form of `r_W²` is `∑_{i ≥ k} ‖v i‖²` — positive
  semidefinite, with kernel EXACTLY the tangent plane
  (`leviForm_planeDistSq_eq_zero_iff`).  Note that it does not depend on the base
  point, so no smallness of the tube enters this step.
* `exists_isStrictlyPositive_add_smul_of_pos_on_null`: if a real two-form `a` is
  strictly positive on the null directions of a semipositive `b`, then `a + B b`
  is strictly positive for all LARGE `B`.  This is the mirror image of
  `PositivityPerturbation.exists_isStrictlyPositive_add_smul` (small perturbation
  of a semipositive form); the proof is the same unit-sphere compactness, with
  the roles of the two forms exchanged.

Specialised to `b = ddᶜ(r_W²)` this is
`exists_isStrictlyPositive_add_smul_ddc_planeDistSq`: a form positive along the
tangent plane is made strictly positive by adding `B ddᶜ r_W²` for `B` large.
Everything here is sorry-free, and nothing in it depends on the modification or
on any deferred input.
-/

@[expose] public section

open Set Filter Metric
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.PlaneTubePositivity

open FirstPass PositivityPerturbation

noncomputable section

variable {n k : ℕ}

/-! ### The squared distance to a coordinate plane -/

variable (n k) in
/-- The coordinates transverse to the standard complex `k`-plane. -/
def normalIndices : Finset (Fin n) := Finset.univ.filter (fun i => k ≤ i.1)

@[simp] theorem mem_normalIndices {i : Fin n} : i ∈ normalIndices n k ↔ k ≤ i.1 := by
  simp [normalIndices]

variable (n k) in
/-- The squared distance to the standard complex `k`-plane, `r_W²` in the
manuscript's notation. -/
def planeDistSq (z : ComplexModel n) : ℝ := ∑ i ∈ normalIndices n k, ‖z i‖ ^ 2

theorem planeDistSq_nonneg (z : ComplexModel n) : 0 ≤ planeDistSq n k z :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The zero locus of `r_W²` is exactly the plane. -/
theorem planeDistSq_eq_zero_iff (z : ComplexModel n) :
    planeDistSq n k z = 0 ↔ z ∈ complexCoordinatePlane n k := by
  constructor
  · intro h i hi
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp h i
      (mem_normalIndices.mpr hi)
    simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  · intro h
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [h i (mem_normalIndices.mp hi)]
    simp

theorem planeDistSq_eq_sum_coordSq :
    planeDistSq n k = fun z => ∑ i ∈ normalIndices n k, OTChen.coordSq i z := rfl

theorem contDiff_planeDistSq : ContDiff ℝ ∞ (planeDistSq n k) := by
  rw [planeDistSq_eq_sum_coordSq]
  exact ContDiff.sum fun i _ => OTChen.contDiff_coordSq i

/-- The Levi form of the single coordinate square. -/
theorem leviForm_coordSq (i : Fin n) (x v : ComplexModel n) :
    leviForm (OTChen.coordSq i) x v = ‖v i‖ ^ 2 := by
  have h := OTChen.leviForm_comp_coordSq (G := fun t : ℝ => t) (x := x) i
    (contDiff_id.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)) v
  rw [show (fun z => OTChen.coordSq i z) = OTChen.coordSq i from rfl] at h
  rw [h, deriv_id'']
  simp

/-- The Levi form of a finite sum. -/
theorem leviForm_finsetSum {ι : Type*} (s : Finset ι) {f : ι → ComplexModel n → ℝ}
    {x : ComplexModel n} (v : ComplexModel n)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) :
    leviForm (fun y => ∑ i ∈ s, f i y) x v = ∑ i ∈ s, leviForm (f i) x v := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert j s hj ih =>
      have hsum : ContDiffAt ℝ 2 (fun y => ∑ i ∈ s, f i y) x :=
        (ContDiff.sum fun i _ => hf i).contDiffAt
      have hfun : (fun y => ∑ i ∈ insert j s, f i y) =
          (f j) + (fun y => ∑ i ∈ s, f i y) := by
        funext y; simp [Finset.sum_insert hj]
      rw [hfun, leviForm_add (hf j).contDiffAt hsum, ih, Finset.sum_insert hj]

/-- **The Levi form of the squared distance to the plane.**  It is the squared
norm of the normal component of `v`, independently of the base point. -/
theorem leviForm_planeDistSq (x v : ComplexModel n) :
    leviForm (planeDistSq n k) x v = ∑ i ∈ normalIndices n k, ‖v i‖ ^ 2 := by
  rw [planeDistSq_eq_sum_coordSq,
    leviForm_finsetSum _ v
      (fun i => (OTChen.contDiff_coordSq i).of_le (WithTop.coe_le_coe.mpr le_top))]
  exact Finset.sum_congr rfl fun i _ => leviForm_coordSq i x v

theorem leviForm_planeDistSq_nonneg (x v : ComplexModel n) :
    0 ≤ leviForm (planeDistSq n k) x v := by
  rw [leviForm_planeDistSq]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **The kernel of the Levi form of `r_W²` is exactly the tangent plane.** -/
theorem leviForm_planeDistSq_eq_zero_iff (x v : ComplexModel n) :
    leviForm (planeDistSq n k) x v = 0 ↔ v ∈ complexCoordinatePlane n k := by
  rw [leviForm_planeDistSq]
  exact planeDistSq_eq_zero_iff v

/-! ### Large perturbations -/

/-- **A form strictly positive on the null directions of a semipositive form
becomes strictly positive after a LARGE multiple of it is added.**

This is the mirror image of
`PositivityPerturbation.exists_isStrictlyPositive_add_smul`, which adds a SMALL
multiple of the form that is positive on the null directions of a semipositive
one.  Same unit-sphere compactness, roles exchanged. -/
theorem exists_isStrictlyPositive_add_smul_of_pos_on_null
    {a b : ComplexModel n [⋀^Fin 2]→L[ℝ] ℝ}
    (hb : ∀ v, 0 ≤ quad b v) (ha : ∀ v, v ≠ 0 → quad b v = 0 → 0 < quad a v) :
    ∃ B₀ : ℝ, 0 < B₀ ∧ ∀ B : ℝ, B₀ ≤ B → IsStrictlyPositive (a + B • b) := by
  set S := sphere (0 : ComplexModel n) 1 with hSdef
  have hS : IsCompact S := isCompact_sphere 0 1
  have hSne : ∀ u ∈ S, u ≠ 0 := fun u hu h => by
    rw [h, mem_sphere_zero_iff_norm, norm_zero] at hu; exact zero_ne_one hu
  set K := S ∩ {v | quad a v ≤ 0} with hKdef
  have hK : IsCompact K := hS.inter_right (isClosed_le (continuous_quad a) continuous_const)
  -- `quad a` is bounded on the sphere
  obtain ⟨A, hA⟩ := hS.exists_bound_of_continuousOn (continuous_quad a).continuousOn
  -- `quad b` has a positive minimum on `K`
  obtain ⟨m, hm, hmK⟩ : ∃ m : ℝ, 0 < m ∧ ∀ u ∈ K, m ≤ quad b u := by
    by_cases hKe : K.Nonempty
    · obtain ⟨v₀, hv₀, hmin⟩ := hK.exists_isMinOn hKe (continuous_quad b).continuousOn
      refine ⟨quad b v₀, ?_, fun u hu => hmin hu⟩
      rcases (hb v₀).lt_or_eq with h | h
      · exact h
      · exact absurd (ha v₀ (hSne v₀ hv₀.1) h.symm) (not_lt.mpr hv₀.2)
    · exact ⟨1, one_pos, fun u hu => absurd ⟨u, hu⟩ hKe⟩
  refine ⟨(|A| + 1) / m, by positivity, fun B hB v hv => ?_⟩
  have hB0 : 0 < B := lt_of_lt_of_le (by positivity) hB
  set u := ‖v‖⁻¹ • v with hudef
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have huS : u ∈ S := by
    rw [hudef, mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ hvn.ne']
  have hvu : v = ‖v‖ • u := by rw [hudef, smul_inv_smul₀ hvn.ne']
  have hu : 0 < quad (a + B • b) u := by
    rw [quad_add, quad_smul_form]
    by_cases hau : quad a u ≤ 0
    · have h1 : m ≤ quad b u := hmK u ⟨huS, hau⟩
      have h2 : |quad a u| ≤ |A| := (Real.norm_eq_abs _ ▸ hA u huS).trans (le_abs_self A)
      have h3 : |A| + 1 ≤ B * m := by
        calc |A| + 1 = (|A| + 1) / m * m := (div_mul_cancel₀ _ hm.ne').symm
          _ ≤ B * m := by gcongr
      have h4 : B * m ≤ B * quad b u := by gcongr
      have h5 : -|A| ≤ quad a u := neg_le_of_abs_le h2
      linarith
    · push Not at hau
      have := hb u
      nlinarith
  change 0 < quad (a + B • b) v
  rw [hvu, quad_smul]
  positivity

/-- **The tube estimate.**  A two-form strictly positive along the tangent plane
is made strictly positive in every direction by adding a large multiple of
`ddᶜ r_W²`.  The constant depends only on the form. -/
theorem exists_isStrictlyPositive_add_smul_ddc_planeDistSq
    (a : ComplexModel n [⋀^Fin 2]→L[ℝ] ℝ) (z : ComplexModel n)
    (ha : ∀ v ∈ complexCoordinatePlane n k, v ≠ 0 → 0 < quad a v) :
    ∃ B₀ : ℝ, 0 < B₀ ∧ ∀ B : ℝ, B₀ ≤ B →
      IsStrictlyPositive (a + B • smoothDDC (planeDistSq n k) z) := by
  have hC2 : ContDiffAt ℝ 2 (planeDistSq n k) z :=
    (contDiff_planeDistSq.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
  have hquad : ∀ v : ComplexModel n,
      quad (smoothDDC (planeDistSq n k) z) v = leviForm (planeDistSq n k) z v / Real.pi :=
    fun v => smoothDDC_complexDiagonal_eq_leviForm hC2 v
  refine exists_isStrictlyPositive_add_smul_of_pos_on_null (fun v => ?_) (fun v hv hb => ?_)
  · rw [hquad]
    exact div_nonneg (leviForm_planeDistSq_nonneg z v) Real.pi_nonneg
  · refine ha v ?_ hv
    rw [hquad, div_eq_zero_iff] at hb
    rcases hb with hb | hb
    · exact (leviForm_planeDistSq_eq_zero_iff z v).mp hb
    · exact absurd hb Real.pi_ne_zero

end

end SGPT.Foundations.Analysis.Pending.PlaneTubePositivity
