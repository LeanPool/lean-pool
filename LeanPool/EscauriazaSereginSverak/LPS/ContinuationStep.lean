/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.ContinuationBound
public import LeanPool.EscauriazaSereginSverak.LPS.ContinuationCompare
public import LeanPool.EscauriazaSereginSverak.LPS.ContinuationTrace
public import LeanPool.EscauriazaSereginSverak.LPS.ContinuationGradient
public import LeanPool.EscauriazaSereginSverak.LPS.ContinuationConcatAux

/-!
# One step of the continuation

From a strong solution agreeing with a Leray–Hopf solution on `(t₀, t₁)`, the local
strong existence theorem started at its terminal slice, glued to it, gives a strong
solution agreeing with the Leray–Hopf solution on a longer interval, whose length
increases by a lower bound depending only on the `H¹` norm of the slice
(`lem:lps-continuation`).
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The power `-4` is decreasing on the positive reals. -/
theorem lps_rpow_neg_four_anti {x y : ℝ} (hy : 0 < y) (h : y ≤ x) :
    Real.rpow x (-4 : ℝ) ≤ Real.rpow y (-4 : ℝ) := by
  show x ^ (-4 : ℝ) ≤ y ^ (-4 : ℝ)
  rw [Real.rpow_neg (hy.le.trans h), Real.rpow_neg hy.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos hy _) (Real.rpow_le_rpow hy.le h (by norm_num))

/-- One continuation step past a terminal time `t₁ ≤ T` of a strong solution that agrees
with a Leray–Hopf solution of finite Serrin norm (`lem:lps-continuation`). -/
theorem lps_continuation_step {c : ℝ} (hc : 0 ≤ c)
    (hLocal : ∀ (t : ℝ) (b : Vec3 → Vec3) (Db : Vec3 → Fin 3 → Vec3),
      IsLpsGoodTime (fun z : ParabolicPoint => b z.1) (fun z i => Db z.1 i) t →
      ∃ τ : ℝ, 0 < τ ∧
        c * Real.rpow (1 + Real.sqrt (∫ x : Vec3,
          (∑ i : Fin 3, (b x i) ^ 2) + ∑ i : Fin 3, ∑ j : Fin 3, (Db x i j) ^ 2)) (-4 : ℝ) ≤ τ ∧
        ∃ (W : ParabolicPoint → Vec3) (DW : ParabolicPoint → Fin 3 → Vec3)
          (pW : ParabolicPoint → ℝ),
          IsLpsStrongSolution t (t + τ) W DW pW ∧
          (fun x : Vec3 => W (x, t)) =ᵐ[volume] b)
    {T t₀ t₁ S : ℝ} {a : Vec3 → Vec3} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du)
    (hSerrin :
      (∃ s : ℝ, 3 < s ∧
        (∫⁻ t in Ioo (0 : ℝ) T,
          (∫⁻ x : Vec3, ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ s) ^
            ((2 * s / (s - 3)) / s)) < ⊤) ∨
      (∫⁻ t in Ioo (0 : ℝ) T,
        (essSup (fun x : Vec3 => ENNReal.ofReal (vec3EuclideanNorm (u (x, t))))
          (volume : Measure Vec3)) ^ (2 : ℝ)) < ⊤)
    (ht₀ : 0 < t₀) (ht₁ : t₁ ≤ T)
    {U : ParabolicPoint → Vec3} {DU : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (hU : IsLpsStrongSolution t₀ t₁ U DU p)
    (hU0 : (fun x : Vec3 => U (x, t₀)) =ᵐ[volume] (fun x : Vec3 => u (x, t₀)))
    (hae : U =ᵐ[volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ t₁))] u)
    (hEq₀ : ENNReal.ofReal (1 / 2 : ℝ) * (∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, t₀))) ^ (2 : ℝ)) +
      (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀),
        ENNReal.ofReal (spatialGradientSq u Du z)) =
      ENNReal.ofReal (1 / 2 : ℝ) * ∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (a x)) ^ (2 : ℝ))
    (hS : (∫ x : Vec3, (∑ i : Fin 3, (U (x, t₁) i) ^ 2) +
        ∑ i : Fin 3, ∑ j : Fin 3, (DU (x, t₁) i j) ^ 2) ≤ S) :
    ∃ t₁' : ℝ, t₁ + c * Real.rpow (1 + Real.sqrt S) (-4 : ℝ) ≤ t₁' ∧
      ∃ (U' : ParabolicPoint → Vec3) (DU' : ParabolicPoint → Fin 3 → Vec3)
        (p' : ParabolicPoint → ℝ),
        IsLpsStrongSolution t₀ t₁' U' DU' p' ∧
        (∀ x : Vec3, U' (x, t₀) = U (x, t₀)) ∧
        (∀ x : Vec3, DU' (x, t₀) = DU (x, t₀)) ∧
        U' =ᵐ[volume.restrict
          (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ (min t₁' T)))] u := by
  have hlt : t₀ < t₁ := hU.1
  have ht₁pos : 0 < t₁ := ht₀.trans hlt
  have hgood : IsLpsGoodTime (fun z : ParabolicPoint => (fun x : Vec3 => U (x, t₁)) z.1)
      (fun z i => (fun (x : Vec3) (i : Fin 3) => DU (x, t₁) i) z.1 i) t₁ := by
    have hg := lps_strong_solution_endpoint_good_time hU
    unfold IsLpsGoodTime at hg ⊢
    exact hg
  obtain ⟨τ, hτ, hlb, W, DW, pW, hW, hW0⟩ :=
    hLocal t₁ (fun x : Vec3 => U (x, t₁)) (fun (x : Vec3) (i : Fin 3) => DU (x, t₁) i) hgood
  have hgradW : (fun x : Vec3 => DW (x, t₁)) =ᵐ[volume] (fun x : Vec3 => DU (x, t₁)) := by
    have hUt : ∀ i : Fin 3, ∃ h : H1Function (Set.univ : Set Vec3),
        h.toFun = (fun x : Vec3 => U (x, t₁) i) ∧ h.grad = (fun x j => DU (x, t₁) i j) :=
      (lps_strong_solution_endpoint_good_time hU).1
    have hWt : ∀ i : Fin 3, ∃ h : H1Function (Set.univ : Set Vec3),
        h.toFun = (fun x : Vec3 => W (x, t₁) i) ∧ h.grad = (fun x j => DW (x, t₁) i j) :=
      (hW.2.1 t₁ ⟨le_rfl, by linarith only [hτ]⟩).2
    have := lps_h1_gradient_ae_eq_of_slice_ae_eq hWt hUt hW0
    have h2 : ∀ i : Fin 3, (fun x : Vec3 => DW (x, t₁) i) =ᵐ[volume] (fun x : Vec3 => DU (x, t₁)
      i) := by
      intro i
      filter_upwards [ae_all_iff.2 (this i)] with x hx
      exact funext hx
    filter_upwards [ae_all_iff.2 h2] with x hx
    exact funext hx
  have hEW := lps_restart_energy hLH hU ht₀ ht₁ hae hU0 hEq₀ hW0
  have hweakEq : ∀ w : Vec3 → Vec3, MemLp w 2 volume →
      (∫ x : Vec3, ∑ i : Fin 3, W (x, t₁) i * w x i) =
        ∫ x : Vec3, ∑ i : Fin 3, u (x, t₁) i * w x i := by
    intro w hw
    rw [← lps_weak_slice_eq hLH hU ht₀.le ht₁ hae w hw]
    refine integral_congr_ae ?_
    filter_upwards [hW0] with x hx
    rw [hx]
  have hcmp := lps_continuation_compare hLH hSerrin ht₁pos ht₁ hW hweakEq hEW
  have hG := lps_strong_solution_glue hU hW hW0 hgradW
  refine ⟨t₁ + τ, ?_, lpsGlue t₁ U W, lpsGlue t₁ DU DW, lpsGlue t₁ p pW, hG,
    fun x => lpsGlue_of_le hlt.le, fun x => lpsGlue_of_le hlt.le, ?_⟩
  · -- the lifespan bound
    have hX : (∫ x : Vec3, (∑ i : Fin 3, (U (x, t₁) i) ^ 2) +
        ∑ i : Fin 3, ∑ j : Fin 3, (DU (x, t₁) i j) ^ 2) ≤ S := hS
    have hX0 : 0 ≤ (∫ x : Vec3, (∑ i : Fin 3, (U (x, t₁) i) ^ 2) +
        ∑ i : Fin 3, ∑ j : Fin 3, (DU (x, t₁) i j) ^ 2) :=
      integral_nonneg fun x => add_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _)
        (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
    have hsq := Real.sqrt_le_sqrt hX
    have hpos : 0 < 1 + Real.sqrt (∫ x : Vec3, (∑ i : Fin 3, (U (x, t₁) i) ^ 2) +
        ∑ i : Fin 3, ∑ j : Fin 3, (DU (x, t₁) i j) ^ 2) := by
      have := Real.sqrt_nonneg (∫ x : Vec3, (∑ i : Fin 3, (U (x, t₁) i) ^ 2) +
        ∑ i : Fin 3, ∑ j : Fin 3, (DU (x, t₁) i j) ^ 2)
      linarith only [this]
    have hmono : Real.rpow (1 + Real.sqrt S) (-4 : ℝ) ≤
        Real.rpow (1 + Real.sqrt (∫ x : Vec3, (∑ i : Fin 3, (U (x, t₁) i) ^ 2) +
          ∑ i : Fin 3, ∑ j : Fin 3, (DU (x, t₁) i j) ^ 2)) (-4 : ℝ) :=
      lps_rpow_neg_four_anti hpos (by linarith only [hsq])
    have hlb' : c * Real.rpow (1 + Real.sqrt (∫ x : Vec3, (∑ i : Fin 3, (U (x, t₁) i) ^ 2) +
        ∑ i : Fin 3, ∑ j : Fin 3, (DU (x, t₁) i j) ^ 2)) (-4 : ℝ) ≤ τ := hlb
    linarith only [mul_le_mul_of_nonneg_left hmono hc, hlb']
  · have hmin : t₁ ≤ min (t₁ + τ) T := le_min (by linarith only [hτ]) ht₁
    rw [Filter.EventuallyEq, lps_slab_restrict_eq_add hlt.le hmin, ae_add_measure_iff]
    have hmeas : ∀ {c d : ℝ}, MeasurableSet (spaceTimeSet (Set.univ : Set Vec3) (Ioo c d)) :=
      fun {c d} => MeasurableSet.univ.prod measurableSet_Ioo
    refine ⟨?_, ?_⟩
    · filter_upwards [hae, ae_restrict_mem hmeas] with z hz hzm
      rw [lpsGlue_of_le hzm.2.2.le]
      exact hz
    · filter_upwards [hcmp, ae_restrict_mem hmeas] with z hz hzm
      rw [lpsGlue_of_gt hzm.2.1]
      exact hz

/-- The first continuation step, from a good time `t₀ ≤ T` of the Leray–Hopf solution at
which the energy equality holds (`lem:lps-continuation`). -/
theorem lps_continuation_base {c : ℝ} (hc : 0 ≤ c)
    (hLocal : ∀ (t : ℝ) (b : Vec3 → Vec3) (Db : Vec3 → Fin 3 → Vec3),
      IsLpsGoodTime (fun z : ParabolicPoint => b z.1) (fun z i => Db z.1 i) t →
      ∃ τ : ℝ, 0 < τ ∧
        c * Real.rpow (1 + Real.sqrt (∫ x : Vec3,
          (∑ i : Fin 3, (b x i) ^ 2) + ∑ i : Fin 3, ∑ j : Fin 3, (Db x i j) ^ 2)) (-4 : ℝ) ≤ τ ∧
        ∃ (W : ParabolicPoint → Vec3) (DW : ParabolicPoint → Fin 3 → Vec3)
          (pW : ParabolicPoint → ℝ),
          IsLpsStrongSolution t (t + τ) W DW pW ∧
          (fun x : Vec3 => W (x, t)) =ᵐ[volume] b)
    {T t₀ S : ℝ} {a : Vec3 → Vec3} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du)
    (hSerrin :
      (∃ s : ℝ, 3 < s ∧
        (∫⁻ t in Ioo (0 : ℝ) T,
          (∫⁻ x : Vec3, ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ s) ^
            ((2 * s / (s - 3)) / s)) < ⊤) ∨
      (∫⁻ t in Ioo (0 : ℝ) T,
        (essSup (fun x : Vec3 => ENNReal.ofReal (vec3EuclideanNorm (u (x, t))))
          (volume : Measure Vec3)) ^ (2 : ℝ)) < ⊤)
    (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T) (hGood : IsLpsGoodTime u Du t₀)
    (hEq₀ : ENNReal.ofReal (1 / 2 : ℝ) * (∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, t₀))) ^ (2 : ℝ)) +
      (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀),
        ENNReal.ofReal (spatialGradientSq u Du z)) =
      ENNReal.ofReal (1 / 2 : ℝ) * ∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (a x)) ^ (2 : ℝ))
    (hS : (∫ x : Vec3, (∑ i : Fin 3, (u (x, t₀) i) ^ 2) +
        ∑ i : Fin 3, ∑ j : Fin 3, (Du (x, t₀) i j) ^ 2) ≤ S) :
    ∃ t₁ : ℝ, t₀ + c * Real.rpow (1 + Real.sqrt S) (-4 : ℝ) ≤ t₁ ∧
      ∃ (U : ParabolicPoint → Vec3) (DU : ParabolicPoint → Fin 3 → Vec3)
        (p : ParabolicPoint → ℝ),
        IsLpsStrongSolution t₀ t₁ U DU p ∧
        (fun x : Vec3 => U (x, t₀)) =ᵐ[volume] (fun x : Vec3 => u (x, t₀)) ∧
        (fun x : Vec3 => DU (x, t₀)) =ᵐ[volume] (fun x : Vec3 => Du (x, t₀)) ∧
        U =ᵐ[volume.restrict
          (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ (min t₁ T)))] u := by
  have hgood : IsLpsGoodTime (fun z : ParabolicPoint => (fun x : Vec3 => u (x, t₀)) z.1)
      (fun z i => (fun (x : Vec3) (i : Fin 3) => Du (x, t₀) i) z.1 i) t₀ := by
    have hg := hGood
    unfold IsLpsGoodTime at hg ⊢
    exact hg
  obtain ⟨τ, hτ, hlb, W, DW, pW, hW, hW0⟩ :=
    hLocal t₀ (fun x : Vec3 => u (x, t₀)) (fun (x : Vec3) (i : Fin 3) => Du (x, t₀) i) hgood
  have hgradW : (fun x : Vec3 => DW (x, t₀)) =ᵐ[volume] (fun x : Vec3 => Du (x, t₀)) := by
    have hUt : ∀ i : Fin 3, ∃ h : H1Function (Set.univ : Set Vec3),
        h.toFun = (fun x : Vec3 => u (x, t₀) i) ∧ h.grad = (fun x j => Du (x, t₀) i j) :=
      hGood.1
    have hWt : ∀ i : Fin 3, ∃ h : H1Function (Set.univ : Set Vec3),
        h.toFun = (fun x : Vec3 => W (x, t₀) i) ∧ h.grad = (fun x j => DW (x, t₀) i j) :=
      (hW.2.1 t₀ ⟨le_rfl, by linarith only [hτ]⟩).2
    have := lps_h1_gradient_ae_eq_of_slice_ae_eq hWt hUt hW0
    have h2 : ∀ i : Fin 3, (fun x : Vec3 => DW (x, t₀) i) =ᵐ[volume] (fun x : Vec3 => Du (x, t₀)
      i) := by
      intro i
      filter_upwards [ae_all_iff.2 (this i)] with x hx
      exact funext hx
    filter_upwards [ae_all_iff.2 h2] with x hx
    exact funext hx
  have hEW : ENNReal.ofReal (1 / 2 : ℝ) * (∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (W (x, t₀))) ^ (2 : ℝ)) +
      (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀),
        ENNReal.ofReal (spatialGradientSq u Du z)) =
      ENNReal.ofReal (1 / 2 : ℝ) * ∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (a x)) ^ (2 : ℝ) := by
    have EW : (∫⁻ x : Vec3, ENNReal.ofReal (vec3EuclideanNorm (W (x, t₀))) ^ (2 : ℝ)) =
        ∫⁻ x : Vec3, ENNReal.ofReal (vec3EuclideanNorm (u (x, t₀))) ^ (2 : ℝ) := by
      refine lintegral_congr_ae ?_
      filter_upwards [hW0] with x hx
      rw [hx]
    rw [EW]
    exact hEq₀
  have hweakEq : ∀ w : Vec3 → Vec3, MemLp w 2 volume →
      (∫ x : Vec3, ∑ i : Fin 3, W (x, t₀) i * w x i) =
        ∫ x : Vec3, ∑ i : Fin 3, u (x, t₀) i * w x i := by
    intro w hw
    refine integral_congr_ae ?_
    filter_upwards [hW0] with x hx
    rw [hx]
  have hcmp := lps_continuation_compare hLH hSerrin ht₀ ht₀T hW hweakEq hEW
  refine ⟨t₀ + τ, ?_, W, DW, pW, hW, hW0, hgradW, hcmp⟩
  have hX0 : 0 ≤ (∫ x : Vec3, (∑ i : Fin 3, (u (x, t₀) i) ^ 2) +
      ∑ i : Fin 3, ∑ j : Fin 3, (Du (x, t₀) i j) ^ 2) :=
    integral_nonneg fun x => add_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _)
      (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
  have hsq := Real.sqrt_le_sqrt hS
  have hpos : 0 < 1 + Real.sqrt (∫ x : Vec3, (∑ i : Fin 3, (u (x, t₀) i) ^ 2) +
      ∑ i : Fin 3, ∑ j : Fin 3, (Du (x, t₀) i j) ^ 2) := by
    have := Real.sqrt_nonneg (∫ x : Vec3, (∑ i : Fin 3, (u (x, t₀) i) ^ 2) +
      ∑ i : Fin 3, ∑ j : Fin 3, (Du (x, t₀) i j) ^ 2)
    linarith only [this]
  have hmono : Real.rpow (1 + Real.sqrt S) (-4 : ℝ) ≤
      Real.rpow (1 + Real.sqrt (∫ x : Vec3, (∑ i : Fin 3, (u (x, t₀) i) ^ 2) +
        ∑ i : Fin 3, ∑ j : Fin 3, (Du (x, t₀) i j) ^ 2)) (-4 : ℝ) :=
    lps_rpow_neg_four_anti hpos (by linarith only [hsq])
  have hlb' : c * Real.rpow (1 + Real.sqrt (∫ x : Vec3, (∑ i : Fin 3, (u (x, t₀) i) ^ 2) +
      ∑ i : Fin 3, ∑ j : Fin 3, (Du (x, t₀) i j) ^ 2)) (-4 : ℝ) ≤ τ := hlb
  linarith only [mul_le_mul_of_nonneg_left hmono hc, hlb']

end ESS

end
