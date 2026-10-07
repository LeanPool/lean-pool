/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.SerrinSliceTrilinear
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinEstimate
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcePressureSlice

/-!
# The relative convection bound at a fixed time

At a fixed time the relative convection form `∑ₖ uₖ ∑ⱼ wⱼ ∂ⱼ wₖ` is bounded by
half the dissipation of `w` plus a multiple of `‖u‖₅⁵ ‖w‖₂²`, by Hölder's
inequality, the three-dimensional interpolation `‖w‖_{10/3} ≲ ‖w‖₂^{2/5}
‖∇w‖₂^{3/5}` and Young's inequality with exponents `5/4` and `5`. This is the
Gronwall coefficient bound of `lem:pv-serrin-uniqueness`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

private theorem serrin_sq_eLpNorm_le {E : Type} [NormedAddCommGroup E] {w : Vec3 → E}
    (hw : MemLp w 2 volume) (S : Vec3 → ℝ) (hc : ∀ x, ‖w x‖ ^ 2 ≤ S x)
    (hci : Integrable S volume) :
    (eLpNorm w 2 volume).toReal ^ 2 ≤ ∫ x : Vec3, S x := by
  have hint : Integrable (fun x => ‖w x‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm hw.aestronglyMeasurable).mp hw
  have heq : (eLpNorm w 2 volume).toReal ^ 2 = ∫ x : Vec3, ‖w x‖ ^ 2 := by
    have hnn : 0 ≤ ∫ x : Vec3, ‖w x‖ ^ (2 : ℝ) := integral_nonneg fun x => by positivity
    rw [hw.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
      ENNReal.toReal_ofReal (by positivity)]
    simp only [ENNReal.toReal_ofNat]
    have hinv : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
    rw [hinv, ← Real.sqrt_eq_rpow, Real.sq_sqrt hnn]
    congr 1
    funext x
    exact Real.rpow_two _
  rw [heq]
  exact integral_mono hint hci hc

private theorem serrin_norm_sq_le_sum_sq (v : Vec3) : ‖v‖ ^ 2 ≤ ∑ k : Fin 3, v k ^ 2 := by
  have hs : 0 ≤ ∑ k : Fin 3, v k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  have h : ‖v‖ ≤ Real.sqrt (∑ k : Fin 3, v k ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun k => ?_
    rw [Real.norm_eq_abs]
    refine Real.abs_le_sqrt ?_
    exact Finset.single_le_sum (f := fun k => v k ^ 2) (fun k _ => sq_nonneg _)
      (Finset.mem_univ k)
  calc
    ‖v‖ ^ 2 ≤ Real.sqrt (∑ k : Fin 3, v k ^ 2) ^ 2 := by gcongr
    _ = ∑ k : Fin 3, v k ^ 2 := Real.sq_sqrt hs

private theorem serrin_norm_sq_le_sum_sq₂ (v : Fin 3 → Vec3) :
    ‖v‖ ^ 2 ≤ ∑ k : Fin 3, ∑ j : Fin 3, v k j ^ 2 := by
  have hs : 0 ≤ ∑ k : Fin 3, ∑ j : Fin 3, v k j ^ 2 :=
    Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have h : ‖v‖ ≤ Real.sqrt (∑ k : Fin 3, ∑ j : Fin 3, v k j ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun k => ?_
    refine Real.le_sqrt_of_sq_le ?_
    calc
      ‖v k‖ ^ 2 ≤ ∑ j : Fin 3, v k j ^ 2 := serrin_norm_sq_le_sum_sq (v k)
      _ ≤ ∑ k : Fin 3, ∑ j : Fin 3, v k j ^ 2 :=
        Finset.single_le_sum (f := fun k => ∑ j : Fin 3, v k j ^ 2)
          (fun k _ => Finset.sum_nonneg fun j _ => sq_nonneg _) (Finset.mem_univ k)
  calc
    ‖v‖ ^ 2 ≤ Real.sqrt (∑ k : Fin 3, ∑ j : Fin 3, v k j ^ 2) ^ 2 := by gcongr
    _ = _ := Real.sq_sqrt hs

private theorem serrin_triple_pointwise (u w : Vec3) (Dw : Fin 3 → Vec3) :
    |∑ k : Fin 3, u k * ∑ j : Fin 3, w j * Dw k j| ≤ 9 * (‖u‖ * ‖w‖ * ‖Dw‖) := by
  have hu (k : Fin 3) : |u k| ≤ ‖u‖ := norm_le_pi_norm u k
  have hw (j : Fin 3) : |w j| ≤ ‖w‖ := norm_le_pi_norm w j
  have hD (k j : Fin 3) : |Dw k j| ≤ ‖Dw‖ := (norm_le_pi_norm (Dw k) j).trans (norm_le_pi_norm Dw k)
  calc
    |∑ k : Fin 3, u k * ∑ j : Fin 3, w j * Dw k j| ≤
        ∑ k : Fin 3, ∑ j : Fin 3, |u k| * (|w j| * |Dw k j|) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      rw [abs_mul, ← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
      exact Finset.sum_congr rfl fun j _ => abs_mul _ _
    _ ≤ ∑ _k : Fin 3, ∑ _j : Fin 3, ‖u‖ * (‖w‖ * ‖Dw‖) := by
      gcongr with k _ j _
      · exact hu k
      · exact hw j
      · exact hD k j
    _ = 9 * (‖u‖ * ‖w‖ * ‖Dw‖) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- The Gronwall bound for the relative convection form at a fixed time. -/
theorem serrin_slice_relative_bound : ∃ K : ℝ, 0 ≤ K ∧
    ∀ {u w : Vec3 → Vec3} {Dw : Vec3 → Fin 3 → Vec3},
      MemLp u (ENNReal.ofReal 5) volume → MemLp w 2 volume → MemLp Dw 2 volume →
      (∀ i : Fin 3, HasWeakGradientOn (Set.univ : Set Vec3)
        (fun x => w x i) (fun x => Dw x i)) →
      |∫ x : Vec3, ∑ k : Fin 3, u x k * ∑ j : Fin 3, w x j * Dw x k j| ≤
        (1 / 2 : ℝ) * (∫ x : Vec3, ∑ k : Fin 3, ∑ j : Fin 3, Dw x k j ^ 2) +
          K * (eLpNorm u (ENNReal.ofReal 5) volume).toReal ^ 5 *
            ∫ x : Vec3, ∑ k : Fin 3, w x k ^ 2 := by
  set Cg : ℝ := (3 * gagliardoNirenbergSobolevConstant ^ (3 / 5 : ℝ) *
    (2 : ℝ≥0∞) ^ (3 / 5 : ℝ)).toReal
  have hCg : 0 ≤ Cg := ENNReal.toReal_nonneg
  refine ⟨(32 / 5 : ℝ) * (9 * Cg) ^ 5, by positivity, ?_⟩
  intro u w Dw hu5 hw2 hDw2 hgrad
  -- the componentwise `H¹` functions of `w`
  let hH1 : ∀ i : Fin 3, H1Function (Set.univ : Set Vec3) := fun i =>
    { toFun := fun x => w x i
      grad := fun x => Dw x i
      memL2 := by
        simpa [CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn, Measure.restrict_univ] using hw2.eval i
      gradMemL2 := by
        intro j
        simpa [CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn, Measure.restrict_univ] using
          (hDw2.eval i).eval j
      hasWeakGradient := hgrad i }
  have hinterp := serrin_vector_spatial_tenThirds (w := w) (Dw := Dw) hw2 hH1
    (fun _ => rfl) (fun _ => rfl)
  set U : ℝ := (eLpNorm u (ENNReal.ofReal 5) volume).toReal
  set W : ℝ := (eLpNorm w 2 volume).toReal
  set D : ℝ := (eLpNorm Dw 2 volume).toReal
  set N : ℝ := (eLpNorm w (ENNReal.ofReal (10 / 3)) volume).toReal
  have hN : N ≤ Cg * W ^ (2 / 5 : ℝ) * D ^ (3 / 5 : ℝ) := by
    have hfin : 3 * gagliardoNirenbergSobolevConstant ^ (3 / 5 : ℝ) * (2 : ℝ≥0∞) ^ (3 / 5 : ℝ) *
        eLpNorm w 2 volume ^ (2 / 5 : ℝ) * eLpNorm Dw 2 volume ^ (3 / 5 : ℝ) ≠ ⊤ := by
      have h1 := CKN.Leray.gagliardoNirenbergSobolevConstant_ne_top
      have h2 := hw2.eLpNorm_ne_top
      have h3 := hDw2.eLpNorm_ne_top
      finiteness
    have h := ENNReal.toReal_mono hfin hinterp
    simp only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow] at h
    simp only [Cg, ENNReal.toReal_mul, ← ENNReal.toReal_rpow]
    calc
      N ≤ _ := h
      _ = _ := by ring
  -- Hölder's inequality for the pointwise product of norms
  have hw103 : MemLp w (ENNReal.ofReal (10 / 3)) volume := by
    have hfin : 3 * gagliardoNirenbergSobolevConstant ^ (3 / 5 : ℝ) * (2 : ℝ≥0∞) ^ (3 / 5 : ℝ) *
        eLpNorm w 2 volume ^ (2 / 5 : ℝ) * eLpNorm Dw 2 volume ^ (3 / 5 : ℝ) ≠ ⊤ := by
      have h1 := CKN.Leray.gagliardoNirenbergSobolevConstant_ne_top
      have h2 := hw2.eLpNorm_ne_top
      have h3 := hDw2.eLpNorm_ne_top
      finiteness
    exact lt_of_le_of_lt hinterp hfin.lt_top
  have hprod : (∫ x : Vec3, ‖u x‖ * ‖w x‖ * ‖Dw x‖) ≤ U * N * D := by
    have H1 : ENNReal.HolderTriple (ENNReal.ofReal 5) (ENNReal.ofReal (10 / 3))
        (ENNReal.ofReal 2) := serrin_holder_ofReal3 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)
    have h12 : eLpNorm (fun x => ‖u x‖ * ‖w x‖) (ENNReal.ofReal 2) volume ≤
        eLpNorm u (ENNReal.ofReal 5) volume * eLpNorm w (ENNReal.ofReal (10 / 3)) volume := by
      have h := eLpNorm_smul_le_mul_eLpNorm (p := ENNReal.ofReal 5) (q := ENNReal.ofReal (10 / 3))
        (r := ENNReal.ofReal 2) hu5.aestronglyMeasurable.norm hw103.aestronglyMeasurable.norm
      rw [eLpNorm_norm u hu5.aestronglyMeasurable, eLpNorm_norm w hw103.aestronglyMeasurable] at h
      exact h
    have h3 : eLpNorm (fun x => ‖u x‖ * ‖w x‖ * ‖Dw x‖) 1 volume ≤
        eLpNorm (fun x => ‖u x‖ * ‖w x‖) 2 volume * eLpNorm Dw 2 volume := by
      have h := eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1)
        (hu5.aestronglyMeasurable.norm.mul hw103.aestronglyMeasurable.norm)
        hDw2.aestronglyMeasurable.norm
      rw [eLpNorm_norm Dw hDw2.aestronglyMeasurable] at h
      exact h
    have hm : AEStronglyMeasurable (fun x => ‖u x‖ * ‖w x‖ * ‖Dw x‖) volume :=
      (hu5.aestronglyMeasurable.norm.mul hw103.aestronglyMeasurable.norm).mul
        hDw2.aestronglyMeasurable.norm
    have hfin : eLpNorm u (ENNReal.ofReal 5) volume * eLpNorm w (ENNReal.ofReal (10 / 3)) volume *
        eLpNorm Dw 2 volume ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.mul_ne_top hu5.eLpNorm_ne_top hw103.eLpNorm_ne_top)
        hDw2.eLpNorm_ne_top
    have hchain : eLpNorm (fun x => ‖u x‖ * ‖w x‖ * ‖Dw x‖) 1 volume ≤
        eLpNorm u (ENNReal.ofReal 5) volume * eLpNorm w (ENNReal.ofReal (10 / 3)) volume *
          eLpNorm Dw 2 volume := by
      refine h3.trans ?_
      gcongr
      rw [ENNReal.ofReal_ofNat] at h12
      exact h12
    calc
      (∫ x : Vec3, ‖u x‖ * ‖w x‖ * ‖Dw x‖) =
          (∫⁻ x : Vec3, ENNReal.ofReal (‖u x‖ * ‖w x‖ * ‖Dw x‖)).toReal :=
        integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => by positivity) hm
      _ = (eLpNorm (fun x => ‖u x‖ * ‖w x‖ * ‖Dw x‖) 1 volume).toReal := by
        rw [eLpNorm_one_eq_lintegral_enorm hm]
        congr 1
        refine lintegral_congr fun x => ?_
        rw [Real.enorm_eq_ofReal (by positivity)]
      _ ≤ (eLpNorm u (ENNReal.ofReal 5) volume * eLpNorm w (ENNReal.ofReal (10 / 3)) volume *
          eLpNorm Dw 2 volume).toReal := ENNReal.toReal_mono hfin hchain
      _ = U * N * D := by simp only [U, N, D, ENNReal.toReal_mul]
  have hprodInt : Integrable (fun x => ‖u x‖ * ‖w x‖ * ‖Dw x‖) volume := by
    have H1 : ENNReal.HolderTriple (ENNReal.ofReal 5) (ENNReal.ofReal (10 / 3))
        (ENNReal.ofReal 2) := serrin_holder_ofReal3 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)
    have h12 : MemLp (fun x => ‖u x‖ * ‖w x‖) (ENNReal.ofReal 2) volume :=
      hu5.norm.mul hw103.norm
    rw [ENNReal.ofReal_ofNat] at h12
    exact memLp_one_iff_integrable.mp (h12.mul (r := 1) hDw2.norm)
  have hsqD : Integrable (fun x => ∑ k : Fin 3, ∑ j : Fin 3, Dw x k j ^ 2) volume :=
    integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ =>
      (memLp_two_iff_integrable_sq_norm ((hDw2.eval k).eval j).aestronglyMeasurable).mp
        ((hDw2.eval k).eval j) |>.congr (Eventually.of_forall fun x => by simp)
  have hsqW : Integrable (fun x => ∑ k : Fin 3, w x k ^ 2) volume :=
    integrable_finsetSum _ fun k _ =>
      (memLp_two_iff_integrable_sq_norm (hw2.eval k).aestronglyMeasurable).mp
        (hw2.eval k) |>.congr (Eventually.of_forall fun x => by simp)
  have hD2 : D ^ 2 ≤ ∫ x : Vec3, ∑ k : Fin 3, ∑ j : Fin 3, Dw x k j ^ 2 :=
    serrin_sq_eLpNorm_le hDw2 _ (fun x => serrin_norm_sq_le_sum_sq₂ (Dw x)) hsqD
  have hW2 : W ^ 2 ≤ ∫ x : Vec3, ∑ k : Fin 3, w x k ^ 2 :=
    serrin_sq_eLpNorm_le hw2 _ (fun x => serrin_norm_sq_le_sum_sq (w x)) hsqW
  have hU0 : 0 ≤ U := ENNReal.toReal_nonneg
  have hW0 : 0 ≤ W := ENNReal.toReal_nonneg
  have hD0 : 0 ≤ D := ENNReal.toReal_nonneg
  have hyoung := serrin_interpolation_young (K := Cg) (A := 9 * U) (B := W) (D := D) (N := N)
    hCg (by positivity) hW0 hD0 hN
  calc
    |∫ x : Vec3, ∑ k : Fin 3, u x k * ∑ j : Fin 3, w x j * Dw x k j| ≤
        ∫ x : Vec3, |∑ k : Fin 3, u x k * ∑ j : Fin 3, w x j * Dw x k j| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x : Vec3, 9 * (‖u x‖ * ‖w x‖ * ‖Dw x‖) :=
      integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _)
        (hprodInt.const_mul 9) (Eventually.of_forall fun x =>
          serrin_triple_pointwise (u x) (w x) (Dw x))
    _ = 9 * ∫ x : Vec3, ‖u x‖ * ‖w x‖ * ‖Dw x‖ := integral_const_mul _ _
    _ ≤ 9 * (U * N * D) := by gcongr
    _ = (9 * U) * N * D := by ring
    _ ≤ (1 / 2 : ℝ) * D ^ 2 + (32 / 5 : ℝ) * (Cg * (9 * U)) ^ 5 * W ^ 2 := hyoung
    _ = (1 / 2 : ℝ) * D ^ 2 + (32 / 5 : ℝ) * (9 * Cg) ^ 5 * U ^ 5 * W ^ 2 := by ring
    _ ≤ (1 / 2 : ℝ) * (∫ x : Vec3, ∑ k : Fin 3, ∑ j : Fin 3, Dw x k j ^ 2) +
        (32 / 5 : ℝ) * (9 * Cg) ^ 5 * U ^ 5 * ∫ x : Vec3, ∑ k : Fin 3, w x k ^ 2 := by
      gcongr

end ESS
