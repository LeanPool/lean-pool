/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.H1EstimateSobolevBridge
public import LeanPool.EscauriazaSereginSverak.LPS.CrossEndpointProducts

/-!
# Norm comparisons at a fixed time

The supremum-norm `L²` norms of the gradient and Hessian tensors are bounded by
the square roots of the corresponding integrated sums of squares, and the
Hessian energy equals the Laplacian energy at every time slice on which the
second derivatives form a Sobolev family (`lem:lps-H1-estimate`).
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

private theorem lps_slice_norm_le_sqrt_sum {E : Type} [NormedAddCommGroup E]
    {F : Vec3 → E} (hF : MemLp F 2 volume) {S : Vec3 → ℝ}
    (hS : Integrable S volume) (hSnn : ∀ x, 0 ≤ S x) (hle : ∀ x, ‖F x‖ ^ 2 ≤ S x) :
    (eLpNorm F 2 volume).toReal ≤ Real.sqrt (∫ x : Vec3, S x) := by
  let f : Vec3 → ℝ := fun x => Real.sqrt (S x)
  have hfmeas : AEStronglyMeasurable f volume :=
    (Real.continuous_sqrt.comp_aestronglyMeasurable hS.aestronglyMeasurable)
  have hf2 : MemLp f 2 volume := by
    refine (memLp_two_iff_integrable_sq hfmeas).mpr ?_
    refine hS.congr (Eventually.of_forall fun x => ?_)
    simp [f, Real.sq_sqrt (hSnn x)]
  have hpoint : ∀ x, ‖F x‖ ≤ f x := fun x => by
    refine Real.le_sqrt_of_sq_le ?_
    exact hle x
  have h1 : eLpNorm F 2 volume ≤ eLpNorm f 2 volume :=
    eLpNorm_mono_ae_real hF.aestronglyMeasurable (Eventually.of_forall hpoint)
  have h2 : eLpNorm f 2 volume ≤ ENNReal.ofReal (Real.sqrt (∫ x : Vec3, S x)) := by
    refine lps_eLpNorm_two_le_sqrt hf2 ?_
    refine le_of_eq (integral_congr_ae (Eventually.of_forall fun x => ?_))
    simp [f, Real.sq_sqrt (hSnn x)]
  have h3 := (h1.trans h2)
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h3
  rwa [ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at this

/-- The supremum norm of a `3 × 3` tensor is bounded by the Frobenius norm. -/
theorem lps_h1_tensor_norm_sq_le (v : Fin 3 → Vec3) :
    ‖v‖ ^ 2 ≤ ∑ i : Fin 3, ∑ j : Fin 3, (v i j) ^ 2 := by
  have hrow (i : Fin 3) : ‖v i‖ ^ 2 ≤ ∑ j : Fin 3, (v i j) ^ 2 := by
    have hs : 0 ≤ ∑ j : Fin 3, (v i j) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
    have h : ‖v i‖ ≤ Real.sqrt (∑ j : Fin 3, (v i j) ^ 2) := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun j => ?_
      rw [Real.norm_eq_abs]
      refine Real.abs_le_sqrt ?_
      exact Finset.single_le_sum (f := fun j => (v i j) ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ j)
    calc ‖v i‖ ^ 2 ≤ Real.sqrt (∑ j : Fin 3, (v i j) ^ 2) ^ 2 := by gcongr
      _ = _ := Real.sq_sqrt hs
  have hs : 0 ≤ ∑ i : Fin 3, ∑ j : Fin 3, (v i j) ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have h : ‖v‖ ≤ Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3, (v i j) ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
    refine Real.le_sqrt_of_sq_le ?_
    calc ‖v i‖ ^ 2 ≤ ∑ j : Fin 3, (v i j) ^ 2 := hrow i
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, (v i j) ^ 2 :=
        Finset.single_le_sum (f := fun i => ∑ j : Fin 3, (v i j) ^ 2)
          (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _) (Finset.mem_univ i)
  calc ‖v‖ ^ 2 ≤ Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3, (v i j) ^ 2) ^ 2 := by gcongr
    _ = _ := Real.sq_sqrt hs

/-- The supremum norm of a `3 × 3 × 3` tensor is bounded by the Frobenius norm. -/
theorem lps_h1_tensor3_norm_sq_le (w : Fin 3 → Fin 3 → Vec3) :
    ‖w‖ ^ 2 ≤ ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, (w i j k) ^ 2 := by
  have hs : 0 ≤ ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, (w i j k) ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ =>
      sq_nonneg _
  have h : ‖w‖ ≤ Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, (w i j k) ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
    refine Real.le_sqrt_of_sq_le ?_
    calc ‖w i‖ ^ 2 ≤ ∑ j : Fin 3, ∑ k : Fin 3, (w i j k) ^ 2 := lps_h1_tensor_norm_sq_le (w i)
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, (w i j k) ^ 2 :=
        Finset.single_le_sum (f := fun i => ∑ j : Fin 3, ∑ k : Fin 3, (w i j k) ^ 2)
          (fun i _ => Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => sq_nonneg _)
          (Finset.mem_univ i)
  calc ‖w‖ ^ 2 ≤ Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, (w i j k) ^ 2) ^ 2 := by
        gcongr
    _ = _ := Real.sq_sqrt hs

/-- The `L²` norm of a tensor field of the first-derivative type is bounded by
the square root of the integrated sum of squares of its entries. -/
theorem lps_h1_gradient_norm_le {Du : Vec3 → Fin 3 → Vec3} (hDu2 : MemLp Du 2 volume) :
    (eLpNorm Du 2 volume).toReal ≤
      Real.sqrt (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, (Du x i j) ^ 2) := by
  have hint (i j : Fin 3) : Integrable (fun x => (Du x i j) ^ 2) volume :=
    ((memLp_two_iff_integrable_sq ((hDu2.eval i).eval j).aestronglyMeasurable).mp
      ((hDu2.eval i).eval j))
  exact lps_slice_norm_le_sqrt_sum hDu2
    (S := fun x => ∑ i : Fin 3, ∑ j : Fin 3, (Du x i j) ^ 2)
    (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j)
    (fun x => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
    (fun x => lps_h1_tensor_norm_sq_le (Du x))

/-- The integrated squared supremum norm of a gradient tensor is bounded by the
integrated sum of squares of its entries. -/
theorem lps_h1_gradient_norm_sq_integral_le {Du : Vec3 → Fin 3 → Vec3}
    (hDu2 : MemLp Du 2 volume) :
    (∫ x : Vec3, ‖Du x‖ ^ 2) ≤ ∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, (Du x i j) ^ 2 := by
  have hint (i j : Fin 3) : Integrable (fun x => (Du x i j) ^ 2) volume :=
    ((memLp_two_iff_integrable_sq ((hDu2.eval i).eval j).aestronglyMeasurable).mp
      ((hDu2.eval i).eval j))
  have hn : Integrable (fun x => ‖Du x‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm hDu2.aestronglyMeasurable).mp hDu2
  exact integral_mono hn
    (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j)
    fun x => lps_h1_tensor_norm_sq_le (Du x)

/-- The `L²` norm of a second-derivative tensor field is bounded by the square
root of the integrated sum of squares of its entries. -/
theorem lps_h1_hessian_norm_le {D2u : Vec3 → Fin 3 → Fin 3 → Vec3}
    (hD2u2 : MemLp D2u 2 volume) :
    (eLpNorm D2u 2 volume).toReal ≤
      Real.sqrt (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, (D2u x i j k) ^ 2) := by
  have hint (i j k : Fin 3) : Integrable (fun x => (D2u x i j k) ^ 2) volume :=
    ((memLp_two_iff_integrable_sq (((hD2u2.eval i).eval j).eval k).aestronglyMeasurable).mp
      (((hD2u2.eval i).eval j).eval k))
  exact lps_slice_norm_le_sqrt_sum hD2u2
    (S := fun x => ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, (D2u x i j k) ^ 2)
    (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      integrable_finsetSum _ fun k _ => hint i j k)
    (fun x => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      Finset.sum_nonneg fun k _ => sq_nonneg _)
    (fun x => lps_h1_tensor3_norm_sq_le (D2u x))

/-- At a time slice where the second derivatives form a Sobolev family, the
Hessian energy equals the Laplacian energy (`lem:lps-H1-estimate`). -/
theorem lps_h1_slice_hessian_energy_eq {t : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    (hfam : ∀ i : Fin 3, IsSobolevFamilyOn 2 (Set.univ : Set Vec3)
      (fun x : Vec3 => u (x, t) i)
      (fun α x => ESS.LPS.lpsH1SpatialFamily u Du D2u i α (x, t))) :
    (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, (D2u (x, t) i j k) ^ 2) =
      ∫ x : Vec3, ∑ i : Fin 3, (∑ j : Fin 3, D2u (x, t) i j j) ^ 2 := by
  have hD : ∀ i : Fin 3, IsSobolevFamilyOn 2 (Set.univ : Set Vec3)
      ((fun α x => ESS.LPS.lpsH1SpatialFamily u Du D2u i α (x, t)) ([] : List (Fin 3)))
      (fun α x => ESS.LPS.lpsH1SpatialFamily u Du D2u i α (x, t)) := fun i =>
    (hfam i).congr_ae (hfam i).zero.symm
      (fun α hα => Filter.Eventually.of_forall fun x => rfl)
  have h := ESS.LPS.lps_h1_vector_sobolev_hessian_eq_laplacian
    (D := fun i α x => ESS.LPS.lpsH1SpatialFamily u Du D2u i α (x, t)) hD
  have hint (i j k : Fin 3) : Integrable (fun x : Vec3 => (D2u (x, t) i j k) ^ 2) volume := by
    have hm : MemLp (fun x : Vec3 => D2u (x, t) i j k) 2 volume := by
      have := (hfam i).memL2 [j, k] (by simp)
      rw [Measure.restrict_univ] at this
      exact this
    exact (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mp hm
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    integrable_finsetSum _ fun k _ => hint i j k]
  simp only [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hint _ j k,
    integral_finsetSum _ fun k _ => hint _ _ k]
  exact h

end ESS

end
