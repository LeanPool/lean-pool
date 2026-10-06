/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Statements.IsLerayHopfSolution
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.Analysis.MeanInequalities

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

private theorem lps_sqrt_sum_sq_le_sum_abs {ι : Type} [Fintype ι] (f : ι → ℝ) :
    Real.sqrt (∑ i : ι, f i ^ 2) ≤ ∑ i : ι, |f i| := by
  have hsum : ∑ i : ι, f i ^ 2 ≤ (∑ i : ι, |f i|) ^ 2 := by
    simpa only [sq_abs] using
      Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
        (f := fun i => |f i|) (fun i hi => abs_nonneg (f i))
  rw [Real.sqrt_le_iff]
  exact ⟨Finset.sum_nonneg fun i _ => abs_nonneg (f i), hsum⟩

private theorem lps_endpoint_gradient_norm_memLp
    {Du : Vec3 → Fin 3 → Vec3}
    (hDuMeas : AEStronglyMeasurable Du volume)
    (hDuEntry2 : ∀ i j, MemLp (fun x : Vec3 => Du x i j) 2 volume) :
    MemLp (fun x : Vec3 => Real.sqrt
      (∑ i : Fin 3, ∑ j : Fin 3, Du x i j ^ 2)) 2 volume := by
  let G : Vec3 → ℝ := fun x => Real.sqrt
    (∑ i : Fin 3, ∑ j : Fin 3, Du x i j ^ 2)
  let W : Vec3 → ℝ := fun x => ∑ i : Fin 3, ∑ j : Fin 3, |Du x i j|
  have hEntry (i j : Fin 3) : MemLp (fun x : Vec3 => |Du x i j|) 2 volume := by
    simpa only [Real.norm_eq_abs] using (hDuEntry2 i j).norm
  have hRow (i : Fin 3) : MemLp (fun x : Vec3 => ∑ j : Fin 3, |Du x i j|) 2 volume := by
    simpa only [Finset.sum_apply] using
      (memLp_finsetSum (p := (2 : ℝ≥0∞)) (μ := volume) Finset.univ
        (fun j _ => hEntry i j))
  have hW : MemLp W 2 volume := by
    simpa only [Finset.sum_apply] using
      (memLp_finsetSum (p := (2 : ℝ≥0∞)) (μ := volume) Finset.univ
        (fun i _ => hRow i))
  have hGmeas : AEStronglyMeasurable G volume := by
    have hcont : Continuous (fun D : Fin 3 → Vec3 => Real.sqrt
        (∑ i : Fin 3, ∑ j : Fin 3, D i j ^ 2)) := by fun_prop
    exact hcont.comp_aestronglyMeasurable hDuMeas
  have hpoint : ∀ x : Vec3, ‖G x‖ ≤ ‖W x‖ := by
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun i _ =>
        Finset.sum_nonneg fun j _ => abs_nonneg (Du x i j))]
    let row : Fin 3 → ℝ := fun i => Real.sqrt (∑ j : Fin 3, Du x i j ^ 2)
    have houter : Real.sqrt (∑ i : Fin 3, row i ^ 2) ≤ ∑ i : Fin 3, row i := by
      calc
        Real.sqrt (∑ i : Fin 3, row i ^ 2) ≤ ∑ i : Fin 3, |row i| :=
          lps_sqrt_sum_sq_le_sum_abs row
        _ = ∑ i : Fin 3, row i := by
          apply Finset.sum_congr rfl
          intro i hi
          exact abs_of_nonneg (Real.sqrt_nonneg _)
    have hrow (i : Fin 3) : row i ≤ ∑ j : Fin 3, |Du x i j| := by
      simpa [row] using lps_sqrt_sum_sq_le_sum_abs (fun j : Fin 3 => Du x i j)
    have hEq : Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3, Du x i j ^ 2) =
        Real.sqrt (∑ i : Fin 3, row i ^ 2) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      dsimp [row]
      rw [Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg (Du x i j))]
    rw [hEq]
    calc
      Real.sqrt (∑ i : Fin 3, row i ^ 2) ≤ ∑ i : Fin 3, row i := houter
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, |Du x i j| :=
        Finset.sum_le_sum fun i _ => hrow i
  exact hW.of_le hGmeas (Eventually.of_forall hpoint)

/-- The endpoint (`s = ∞`) spatial Hölder--Young estimate. The velocity field
`v` is controlled in spatial `L∞`; the gradient term is the Frobenius norm of
the explicit slice gradient `Du` (`lem:lps-comparison`). -/
theorem lps_slice_trilinear_bound_infinite
    {u v : Vec3 → Vec3} {Du : Vec3 → Fin 3 → Vec3}
    (hu2 : MemLp u 2 volume)
    (hvMeas : AEStronglyMeasurable v volume)
    (hDuMeas : AEStronglyMeasurable Du volume)
    (hDuEntry2 : ∀ i j, MemLp (fun x : Vec3 => Du x i j) 2 volume)
    (hvInf : eLpNorm (fun x : Vec3 => vec3EuclideanNorm (v x)) ⊤ volume < ⊤) :
    ∫ x : Vec3, vec3EuclideanNorm (u x) *
      Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3, Du x i j ^ 2) *
      vec3EuclideanNorm (v x) ≤
      (1 / 2 : ℝ) * (∫ x : Vec3,
        (Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3, Du x i j ^ 2)) ^ 2) +
        (1 / 2 : ℝ) * (∫ x : Vec3, vec3EuclideanNorm (u x) ^ 2) *
          (eLpNorm (fun x : Vec3 => vec3EuclideanNorm (v x)) ⊤ volume).toReal ^ 2 := by
  let U : Vec3 → ℝ := fun x => vec3EuclideanNorm (u x)
  let G : Vec3 → ℝ := fun x => Real.sqrt
    (∑ i : Fin 3, ∑ j : Fin 3, Du x i j ^ 2)
  let V : Vec3 → ℝ := fun x => vec3EuclideanNorm (v x)
  let M : ℝ := (eLpNorm V ⊤ volume).toReal
  have hUmeas : AEStronglyMeasurable U volume :=
    CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.comp_aestronglyMeasurable
      hu2.aestronglyMeasurable
  have hU2 : MemLp U 2 volume := by
    apply MemLp.of_le_mul (hu2.norm) hUmeas
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (vec3EuclideanNorm_nonneg _),
      Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact vec3EuclideanNorm_le_sqrt_three_mul_norm (u x)
  have hG2 : MemLp G 2 volume := lps_endpoint_gradient_norm_memLp hDuMeas hDuEntry2
  have hVmeas : AEStronglyMeasurable V volume :=
    CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.comp_aestronglyMeasurable
      hvMeas
  have hVtop : MemLp V ⊤ volume := by
    simpa only [memLp_iff] using hvInf
  have hVbound : ∀ᵐ x ∂volume, V x ≤ M := by
    have hEss := enorm_ae_le_eLpNormEssSup V volume
    rw [← eLpNorm_exponent_top hVmeas] at hEss
    filter_upwards [hEss] with x hx
    have hVnonneg : 0 ≤ V x := vec3EuclideanNorm_nonneg _
    have hVeq : ‖V x‖ₑ = ENNReal.ofReal (V x) := Real.enorm_eq_ofReal hVnonneg
    have hle : ENNReal.ofReal (V x) ≤ eLpNorm V ⊤ volume := by
      simpa only [hVeq] using hx
    have hreal := ENNReal.toReal_mono hvInf.ne hle
    rw [ENNReal.toReal_ofReal hVnonneg] at hreal
    simpa [M, V] using hreal
  have hHolder : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 := by
    exact ENNReal.HolderConjugate.instTwoTwo
  have hUG : MemLp (fun x => U x * G x) 1 volume := by
    exact hU2.mul hG2 (hpqr := hHolder)
  have hUGInt : Integrable (fun x => U x * G x) volume :=
    memLp_one_iff_integrable.mp hUG
  have hBoundedProd : MemLp (fun x => U x * G x * V x) 1 volume := by
    have hHolderInf : ENNReal.HolderTriple 1 ⊤ 1 := by
      refine ⟨?_⟩
      simp
    convert hUG.mul hVtop (hpqr := hHolderInf) using 1
  have hProdInt : Integrable (fun x => U x * G x * V x) volume :=
    memLp_one_iff_integrable.mp hBoundedProd
  have hHolderInt : ∫ x : Vec3, U x * G x ≤
      (∫ x : Vec3, U x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
        (∫ x : Vec3, G x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
    have hConj : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
    have hnonnegU : 0 ≤ᵐ[volume] U := Eventually.of_forall fun x => vec3EuclideanNorm_nonneg _
    have hnonnegG : 0 ≤ᵐ[volume] G := Eventually.of_forall fun x => Real.sqrt_nonneg _
    have h := integral_mul_le_Lp_mul_Lq_of_nonneg (p := 2) (q := 2)
      hConj hnonnegU hnonnegG
      (by simpa only [ENNReal.ofReal_ofNat] using hU2)
      (by simpa only [ENNReal.ofReal_ofNat] using hG2)
    exact h
  have hDomInt : Integrable (fun x : Vec3 => M * (U x * G x)) volume := hUGInt.const_mul M
  have hProdLe : ∀ᵐ x ∂volume, U x * G x * V x ≤ M * (U x * G x) := by
    filter_upwards [hVbound] with x hx
    have hU : 0 ≤ U x := vec3EuclideanNorm_nonneg _
    have hG : 0 ≤ G x := Real.sqrt_nonneg _
    calc
      U x * G x * V x = (U x * G x) * V x := by ring
      _ ≤ (U x * G x) * M := mul_le_mul_of_nonneg_left hx (mul_nonneg hU hG)
      _ = M * (U x * G x) := by ring
  have hIntLe : ∫ x : Vec3, U x * G x * V x ≤
      M * ∫ x : Vec3, U x * G x := by
    calc
      ∫ x : Vec3, U x * G x * V x ≤ ∫ x : Vec3, M * (U x * G x) :=
        integral_mono_ae hProdInt hDomInt hProdLe
      _ = M * ∫ x : Vec3, U x * G x := integral_const_mul _ _
  have hIU : 0 ≤ ∫ x : Vec3, U x ^ (2 : ℝ) :=
    integral_nonneg (fun x => Real.rpow_nonneg (vec3EuclideanNorm_nonneg (u x)) _)
  have hIG : 0 ≤ ∫ x : Vec3, G x ^ (2 : ℝ) :=
    integral_nonneg (fun x => Real.rpow_nonneg (Real.sqrt_nonneg _) _)
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  have hRootU : (∫ x : Vec3, U x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) =
      Real.sqrt (∫ x : Vec3, U x ^ (2 : ℝ)) := by rw [← Real.sqrt_eq_rpow]
  have hRootG : (∫ x : Vec3, G x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) =
      Real.sqrt (∫ x : Vec3, G x ^ (2 : ℝ)) := by rw [← Real.sqrt_eq_rpow]
  have hpow2 (z : ℝ) : z ^ (2 : ℝ) = z ^ 2 := Real.rpow_natCast z 2
  have hYoung := Real.young_inequality_of_nonneg
    (a := M * Real.sqrt (∫ x : Vec3, U x ^ (2 : ℝ)))
    (b := Real.sqrt (∫ x : Vec3, G x ^ (2 : ℝ)))
    (p := (2 : ℝ)) (q := (2 : ℝ))
    (mul_nonneg hM (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    Real.HolderConjugate.two_two
  have hYoungFinal :
      ∫ x : Vec3, U x * G x * V x ≤
        (1 / 2 : ℝ) * (∫ x : Vec3, G x ^ (2 : ℝ)) +
          (1 / 2 : ℝ) * (∫ x : Vec3, U x ^ (2 : ℝ)) * M ^ 2 := by
    calc
      ∫ x : Vec3, U x * G x * V x ≤ M * ∫ x : Vec3, U x * G x := hIntLe
      _ ≤ M * ((∫ x : Vec3, U x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
        (∫ x : Vec3, G x ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hHolderInt hM
      _ = (M * Real.sqrt (∫ x : Vec3, U x ^ (2 : ℝ))) *
        Real.sqrt (∫ x : Vec3, G x ^ (2 : ℝ)) := by rw [hRootU, hRootG]; ring
      _ ≤ (M * Real.sqrt (∫ x : Vec3, U x ^ (2 : ℝ))) ^ (2 : ℝ) / 2 +
        (Real.sqrt (∫ x : Vec3, G x ^ (2 : ℝ))) ^ (2 : ℝ) / 2 := hYoung
      _ = (1 / 2 : ℝ) * (∫ x : Vec3, G x ^ (2 : ℝ)) +
        (1 / 2 : ℝ) * (∫ x : Vec3, U x ^ (2 : ℝ)) * M ^ 2 := by
        rw [hpow2, hpow2, mul_pow, Real.sq_sqrt hIU, Real.sq_sqrt hIG]
        ring
  simpa only [U, G, V, M, hpow2] using hYoungFinal

end ESS

end
