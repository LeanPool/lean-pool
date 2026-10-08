/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.HarmonicReplacementNegativeBesovAtErrorOrder

/-!
# High-contrast homogenization: Provider.Regularity.HarmonicReplacementL2AtErrorOrder

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Identity-harmonic approximation at a prescribed error order

For every positive response-error order below one half, a weak solution on a
centered cube admits an identity-harmonic same-trace replacement whose
normalized `L²` error is controlled at that same response-error order.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

private theorem homogenizationComparisonFluxSeminorm_nonneg_at_error_order
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (a : Book.Ch03.CoeffFamily d) (a0 : Book.Ch03.ConstantCoeffMatrix d)
    (s : ℝ) (hs : 0 < s)
    (u v : H1Function (Book.Ch02.cubeDomain Q : Set (Vec d))) :
    0 ≤ cubeBesovNegativeVectorSeminormTwo Q s
      (Book.Ch03.homogenizationComparisonFluxField Q a a0 u v) := by
  have huGrad : MemVectorL2 (cubeSet Q) u.grad := by
    simpa using (Book.Ch03.publicH1ToCubeSet u).grad_memVectorL2
  have hvGrad : MemVectorL2 (cubeSet Q) v.grad := by
    simpa using (Book.Ch03.publicH1ToCubeSet v).grad_memVectorL2
  have hEll0 :
      IsEllipticFieldOn a0.lam a0.Lam (cubeSet Q)
        (constantCoeffField a0.matrix) :=
    Book.Ch03.constantCoeffMatrix_isEllipticFieldOn_constantCoeffField a0
      (measurableSet_cubeSet Q)
  let Ginternal : Vec d → Vec d :=
    fluxComparison (Book.Ch03.publicCoeffField Q a) a0.matrix u.grad v.grad
  have hfluxA : MemVectorL2 (cubeSet Q)
      (fun x => matVecMul (Book.Ch03.publicCoeffField Q a x) (u.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn
      (Book.Ch03.publicCoeffField_isEllipticFieldOn_cubeSet Q a) huGrad
  have hflux0 : MemVectorL2 (cubeSet Q)
      (fun x => matVecMul a0.matrix (v.grad x)) := by
    simpa [constantCoeffField] using
      memVectorL2_matVecMul_of_isEllipticFieldOn hEll0 hvGrad
  have hGinternal : MemVectorL2 (cubeSet Q) Ginternal := by
    dsimp [Ginternal, fluxComparison]
    exact hfluxA.sub hflux0
  have hae :
      Book.Ch03.homogenizationComparisonFluxField Q a a0 u v
        =ᵐ[volumeMeasureOn (cubeSet Q)] Ginternal :=
    Book.Ch03.homogenizationComparisonFluxField_ae_eq_fluxComparison_publicCoeffField_cubeSet
      (Q := Q) (a := a) (a0 := a0) u v
  have hmem : MemVectorL2 (cubeSet Q)
      (Book.Ch03.homogenizationComparisonFluxField Q a a0 u v) :=
    MeasureTheory.MemLp.ae_eq hae.symm hGinternal
  have hmemNormalized :
      MeasureTheory.MemLp
        (Book.Ch03.homogenizationComparisonFluxField Q a a0 u v)
        (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet Q hmem
  exact cubeBesovNegativeVectorSeminormTwo_nonneg_of_memLp Q hs _ hmemNormalized

/-- The normalized `L²` distance to the identity-harmonic same-trace
replacement is controlled by the response error at any prescribed positive
order below one half. -/
theorem exists_identityHarmonicReplacementL2EstimateConstant_at_error_order
    (d : ℕ) [NeZero d] (b : ℝ) (hb : 0 < b) (hb_lt : b < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : Book.Ch03.CoeffFamily d) (m : ℤ)
        (u : H1Function
          (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d)))
        (hu : IsWeakSolutionOn (a.coeffOn (originCube d m)).toCoeffField
          (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d)) u.grad),
        cubeBesovScaleWeight (1 : ℝ) (originCube d m) *
            cubeLpNorm (originCube d m) (2 : ℝ≥0∞)
              (fun x => u.toFun x -
                (identityHarmonicReplacementDatum a m u hu).v.toFun x) ≤
          C * scalarIdentityWeakError a b m *
            Book.Ch03.h1EnergyNormOnCube (originCube d m) a u := by
  let t : ℝ := (b + 1 / 2) / 2
  have hbt : b < t := by
    dsimp [t]
    linarith only [hb_lt]
  have ht : 0 < t := hb.trans hbt
  have ht_lt : t < 1 / 2 := by
    dsimp [t]
    linarith only [hb_lt]
  have h2b : 2 * b < 2 * t :=
    mul_lt_mul_of_pos_left hbt (by norm_num : (0 : ℝ) < 2)
  have hsOut_lt : 2 * t < 1 := by
    calc
      2 * t < 2 * (1 / 2 : ℝ) :=
        mul_lt_mul_of_pos_left ht_lt (by norm_num)
      _ = 1 := by ring
  rcases
      exists_identityHarmonicReplacementNegativeBesovEstimateConstant_at_error_order
        d (2 * t) b hb h2b hsOut_lt with
    ⟨Cweak, hCweak, hweak⟩
  let K : ℝ :=
    (((d : ℝ) * Legacy.cubeNeumannW22CalderonZygmundConstant d *
          (3 : ℝ) ^ ((d : ℝ) + 1) * (d : ℝ) +
        2 * (3 : ℝ) ^ ((d : ℝ) + 1)) *
      Real.sqrt ((1 - Real.rpow (3 : ℝ) (-2 * ((1 / 2 : ℝ) - t)))⁻¹))
  let C : ℝ := max 1 (K * Cweak)
  have hK_nonneg : 0 ≤ K := by
    have hcz : 0 ≤ Legacy.cubeNeumannW22CalderonZygmundConstant d :=
      Legacy.cubeNeumannW22CalderonZygmundConstant_nonneg d
    dsimp [K]
    exact mul_nonneg
      (add_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (by exact_mod_cast Nat.zero_le d) hcz)
              (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _))
          (by exact_mod_cast Nat.zero_le d))
        (mul_nonneg (by norm_num)
          (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)))
      (Real.sqrt_nonneg _)
  have hC : 0 < C :=
    lt_of_lt_of_le zero_lt_one (le_max_left 1 (K * Cweak))
  refine ⟨C, hC, ?_⟩
  intro a m u hu
  let Q := originCube d m
  let W := identityHarmonicReplacementDatum a m u hu
  let E := scalarIdentityWeakError a b m
  let A := Book.Ch03.h1EnergyNormOnCube Q a u
  let N := cubeBesovNegativeVectorSeminormTwo Q (2 * t)
    (Book.Ch03.homogenizationComparisonConstantGradientField
      (identityConstantCoeffMatrix d) W.u W.v)
  let L := Book.Ch03.homogenizationComparisonNegativeBesovLHS Q a
    (identityConstantCoeffMatrix d) (2 * t) W.u W.v
  rcases (identityHarmonicReplacementDatum_characterization a m u hu).2 with
    ⟨w, hw⟩
  have hwCube :
      w.toH1Function.toFun =ᵐ[volume.restrict (cubeSet Q)]
        fun x => u.toFun x - W.v.toFun x := by
    simpa [Q, W, Book.Ch02.cubeDomain_coe, volumeMeasureOn,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] using hw
  have hwNormalized :
      w.toH1Function.toFun =ᵐ[normalizedCubeMeasure Q]
        fun x => u.toFun x - W.v.toFun x := by
    rw [normalizedCubeMeasure, Filter.EventuallyEq]
    exact MeasureTheory.Measure.ae_smul_measure hwCube _
  have hfunNorm :
      cubeLpNorm Q (2 : ℝ≥0∞) (fun x => w.toH1Function.toFun x) =
        cubeLpNorm Q (2 : ℝ≥0∞) (fun x => u.toFun x - W.v.toFun x) := by
    unfold cubeLpNorm
    rw [MeasureTheory.eLpNorm_congr_ae hwNormalized]
  have hwOpen :
      w.toH1Function.toFun =ᵐ[
        volume.restrict (Book.Ch02.cubeDomain Q : Set (Vec d))]
          (u - W.v).toFun := by
    simpa only [H1Function.sub_toFun] using hw
  have hgradOpen :
      w.toH1Function.grad =ᵐ[
        volume.restrict (Book.Ch02.cubeDomain Q : Set (Vec d))]
          fun x => u.grad x - W.v.grad x := by
    have h := Book.Ch03.H1Function.grad_ae_eq_of_toFun_ae_eq
      (Book.Ch02.cubeDomain Q).isOpen
      (u := w.toH1Function) (v := u - W.v) hwOpen
    simpa only [H1Function.sub_grad] using h
  have hgradCube :
      w.toH1Function.grad =ᵐ[volume.restrict (cubeSet Q)]
        Book.Ch03.homogenizationComparisonConstantGradientField
          (identityConstantCoeffMatrix d) W.u W.v := by
    have hWu : W.u = u := identityHarmonicReplacementDatum_u a m u hu
    have hcomparison :
        Book.Ch03.homogenizationComparisonConstantGradientField
            (identityConstantCoeffMatrix d) W.u W.v =
          fun x => u.grad x - W.v.grad x := by
      funext x
      rw [hWu]
      simp [Book.Ch03.homogenizationComparisonConstantGradientField,
        identityConstantCoeffMatrix_matrix, HCPolySupport.matVecMul_one]
    rw [hcomparison]
    simpa [Book.Ch02.cubeDomain_coe,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] using hgradOpen
  have hN_eq :
      cubeBesovNegativeVectorSeminormTwo Q (2 * t)
          (fun x => w.toH1Function.grad x) = N := by
    simpa [N] using
      cubeBesovNegativeVectorSeminormTwo_eq_of_ae_eq_on_cubeSet
        (2 * t) hgradCube
  have hPoincareRaw :
      cubeBesovScaleWeight (1 : ℝ) Q *
          cubeLpNorm Q (2 : ℝ≥0∞)
            (fun x => w.toH1Function.toFun x) ≤
        K * cubeBesovNegativeVectorSeminormTwo Q (2 * t)
          (fun x => w.toH1Function.grad x) := by
    simpa [K] using
      Book.Ch03.cubeBesovScaleWeight_one_mul_cubeLpNorm_h10_le_grad_negativeBesovTwo
        Q (Book.Ch03.publicH10ToCubeSet w) ht ht_lt
  have hPoincare :
      cubeBesovScaleWeight (1 : ℝ) Q *
          cubeLpNorm Q (2 : ℝ≥0∞)
            (fun x => w.toH1Function.toFun x) ≤ K * N := by
    simpa only [hN_eq] using hPoincareRaw
  have hflux_nonneg :
      0 ≤ cubeBesovNegativeVectorSeminormTwo Q (2 * t)
        (Book.Ch03.homogenizationComparisonFluxField Q a
          (identityConstantCoeffMatrix d) W.u W.v) :=
    homogenizationComparisonFluxSeminorm_nonneg_at_error_order Q a
      (identityConstantCoeffMatrix d) (2 * t)
      (mul_pos (by norm_num : (0 : ℝ) < 2) ht) W.u W.v
  have hNL : N ≤ L := by
    dsimp [L, Book.Ch03.homogenizationComparisonNegativeBesovLHS]
    exact le_add_of_nonneg_right hflux_nonneg
  have hweak' : L ≤ Cweak * E * A := by
    simpa [L, E, A, Q, W] using hweak a m u hu
  have htail_nonneg : 0 ≤ E * A := by
    exact mul_nonneg (scalarIdentityWeakError_nonneg a b m)
      (by dsimp [A, Book.Ch03.h1EnergyNormOnCube]; exact Real.sqrt_nonneg _)
  calc
    cubeBesovScaleWeight (1 : ℝ) (originCube d m) *
        cubeLpNorm (originCube d m) (2 : ℝ≥0∞)
          (fun x => u.toFun x -
            (identityHarmonicReplacementDatum a m u hu).v.toFun x) =
        cubeBesovScaleWeight (1 : ℝ) Q *
          cubeLpNorm Q (2 : ℝ≥0∞)
            (fun x => u.toFun x - W.v.toFun x) := rfl
    _ = cubeBesovScaleWeight (1 : ℝ) Q *
          cubeLpNorm Q (2 : ℝ≥0∞)
            (fun x => w.toH1Function.toFun x) := by rw [hfunNorm]
    _ ≤ K * N := hPoincare
    _ ≤ K * L := mul_le_mul_of_nonneg_left hNL hK_nonneg
    _ ≤ K * (Cweak * E * A) :=
      mul_le_mul_of_nonneg_left hweak' hK_nonneg
    _ = (K * Cweak) * (E * A) := by ring
    _ ≤ C * (E * A) :=
      mul_le_mul_of_nonneg_right (le_max_right 1 (K * Cweak)) htail_nonneg
    _ = C * scalarIdentityWeakError a b m *
        Book.Ch03.h1EnergyNormOnCube (originCube d m) a u := by
      dsimp [E, A, Q]
      ring

end

end HighContrast
end HCPolySupport
