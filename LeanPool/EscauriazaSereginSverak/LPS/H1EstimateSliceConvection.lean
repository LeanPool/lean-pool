/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.H1EstimateSpatial
public import LeanPool.EscauriazaSereginSverak.LPS.H1EstimateNonlinearity
public import LeanPool.EscauriazaSereginSverak.LPS.H1EstimateSolenoidalDense
public import LeanPool.EscauriazaSereginSverak.LPS.RegularisedH1Convection
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcePressureSlice
public import LeanPool.CaffarelliKohnNirenberg.Leray.JSpaceFourierLimit
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Equation
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinTrilinear
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.SerrinPairingLimit

/-!
# Fixed-time convection identities for `H²` fields

At a fixed time the convection field `(u·∇)u` of a solenoidal `H²` field is
square integrable, and pairing it with a smooth compactly supported field
integrates by parts onto the transported product `u ⊗ u`
(`lem:lps-H1-estimate`).
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Each term `uⱼ ∂ⱼuₖ` of the convection field of an `H²` field is square
integrable: the velocity is in `L⁶` and the gradient in `L³` by Sobolev
interpolation (`lem:lps-H1-estimate`). -/
theorem lps_h1_convection_term_memLp_two
    {u : Vec3 → Vec3} {Du : Vec3 → Fin 3 → Vec3}
    {D2u : Vec3 → Fin 3 → Fin 3 → Vec3}
    (hu2 : MemLp u 2 volume) (hDu2 : MemLp Du 2 volume)
    (hD2u2 : MemLp D2u 2 volume)
    (hH1 : ∀ i : Fin 3, ∃ h : H1Function (Set.univ : Set Vec3),
      h.toFun = (fun x : Vec3 => u x i) ∧ h.grad = (fun x j => Du x i j))
    (hgrad : ∀ i j : Fin 3, HasWeakGradientOn (Set.univ : Set Vec3)
      (fun x => Du x i j) (fun x => D2u x i j)) (j k : Fin 3) :
    MemLp (fun x : Vec3 => u x j * Du x k j) 2 volume := by
  have h6 := ESS.LPS.lps_regularised_h1_vector_six_bound hu2 hDu2 hH1
  have hu6 : MemLp u 6 volume := by
    refine lt_of_le_of_lt h6 ?_
    have hG := CKN.Leray.gagliardoNirenbergSobolevConstant_ne_top
    have h1 := hDu2.eLpNorm_ne_top
    finiteness
  have hUh6 : MemLp (fun x : Vec3 => vec3EuclideanNorm (u x)) 6 volume := by
    have hmeas : AEStronglyMeasurable (fun x : Vec3 => vec3EuclideanNorm (u x)) volume :=
      continuous_vec3EuclideanNorm.comp_aestronglyMeasurable hu2.aestronglyMeasurable
    refine MemLp.of_le_mul (g := fun x : Vec3 => u x) (c := Real.sqrt 3) hu6 hmeas
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (vec3EuclideanNorm_nonneg _)]
    exact vec3EuclideanNorm_le_sqrt_three_mul_norm _
  have hgi := lps_h1_gradient_interpolation (s := 6) (by norm_num) hDu2 hD2u2 hgrad
  have hHh3 : MemLp (fun x : Vec3 => ∑ i : Fin 3, ‖Du x i‖) (ENNReal.ofReal 3) volume := by
    have hmeas : AEStronglyMeasurable (fun x : Vec3 => ∑ i : Fin 3, ‖Du x i‖) volume := by
      refine Finset.univ.aestronglyMeasurable_fun_sum ?_
      intro i _
      exact ((continuous_apply i).comp_aestronglyMeasurable hDu2.aestronglyMeasurable).norm
    have h3 : (2 * 6 / (6 - 2) : ℝ) = 3 := by norm_num
    rw [h3] at hgi
    refine lt_of_le_of_lt hgi ?_
    have hG := CKN.Leray.gagliardoNirenbergSobolevConstant_ne_top
    have h1 := hDu2.eLpNorm_ne_top
    have h2 := hD2u2.eLpNorm_ne_top
    finiteness
  have H : ENNReal.HolderTriple (ENNReal.ofReal 6) (ENNReal.ofReal 3) (ENNReal.ofReal 2) :=
    serrin_holder_ofReal3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hprod : MemLp (fun x : Vec3 => vec3EuclideanNorm (u x) * ∑ i : Fin 3, ‖Du x i‖)
      (ENNReal.ofReal 2) volume := by
    have h6' : MemLp (fun x : Vec3 => vec3EuclideanNorm (u x)) (ENNReal.ofReal 6) volume := by
      simpa [ENNReal.ofReal_ofNat] using hUh6
    exact h6'.mul hHh3
  rw [ENNReal.ofReal_ofNat] at hprod
  have hmeasN : AEStronglyMeasurable (fun x : Vec3 => u x j * Du x k j) volume :=
    ((continuous_apply j).comp_aestronglyMeasurable hu2.aestronglyMeasurable).mul
      ((continuous_apply j).comp_aestronglyMeasurable
        ((continuous_apply k).comp_aestronglyMeasurable hDu2.aestronglyMeasurable))
  refine MemLp.of_le_mul (c := 1) hprod hmeasN (Eventually.of_forall fun x => ?_)
  have hu : |u x j| ≤ vec3EuclideanNorm (u x) := abs_apply_le_vec3EuclideanNorm _ j
  have hD : |Du x k j| ≤ ∑ i : Fin 3, ‖Du x i‖ :=
    (norm_le_pi_norm (Du x k) j).trans
      (Finset.single_le_sum (f := fun i : Fin 3 => ‖Du x i‖) (fun i _ => norm_nonneg _)
        (Finset.mem_univ k))
  have hnn : 0 ≤ vec3EuclideanNorm (u x) * ∑ i : Fin 3, ‖Du x i‖ :=
    mul_nonneg (vec3EuclideanNorm_nonneg _) (Finset.sum_nonneg fun i _ => norm_nonneg _)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn, one_mul, abs_mul]
  exact mul_le_mul hu hD (abs_nonneg _) (vec3EuclideanNorm_nonneg _)

/-- The convection field `(u·∇)u` of a solenoidal `H²` field is square
integrable (`lem:lps-H1-estimate`). -/
theorem lps_h1_convection_memLp_two
    {u : Vec3 → Vec3} {Du : Vec3 → Fin 3 → Vec3}
    {D2u : Vec3 → Fin 3 → Fin 3 → Vec3}
    (hu2 : MemLp u 2 volume) (hDu2 : MemLp Du 2 volume)
    (hD2u2 : MemLp D2u 2 volume)
    (hH1 : ∀ i : Fin 3, ∃ h : H1Function (Set.univ : Set Vec3),
      h.toFun = (fun x : Vec3 => u x i) ∧ h.grad = (fun x j => Du x i j))
    (hgrad : ∀ i j : Fin 3, HasWeakGradientOn (Set.univ : Set Vec3)
      (fun x => Du x i j) (fun x => D2u x i j)) (k : Fin 3) :
    MemLp (fun x : Vec3 => ∑ j : Fin 3, u x j * Du x k j) 2 volume :=
  memLp_finsetSum Finset.univ fun j _ =>
    lps_h1_convection_term_memLp_two hu2 hDu2 hD2u2 hH1 hgrad j k

/-- A smooth compactly supported test field is square integrable together with
its first derivatives. -/
private theorem lps_h1_test_memLp_two {ψ : Vec3 → Vec3}
    (hψ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => ψ x i))
    (hψc : ∀ i, HasCompactSupport (fun x => ψ x i)) (i j : Fin 3) :
    MemLp (fun x => ψ x i) 2 volume ∧
      MemLp (fun x => spatialDeriv (fun y => ψ y i) j x) 2 volume := by
  refine ⟨(hψ i).continuous.memLp_of_hasCompactSupport (hψc i), ?_⟩
  have hc : Continuous (fun x => spatialDeriv (fun y => ψ y i) j x) :=
    (contDiff_spatialDeriv_smooth (hψ i) j).continuous
  have hcs : HasCompactSupport (fun x => spatialDeriv (fun y => ψ y i) j x) :=
    (hψc i).fderiv_apply (𝕜 := ℝ) (basisVec j)
  exact hc.memLp_of_hasCompactSupport hcs

/-- Pairing the convection field with a smooth compactly supported field
integrates by parts onto the transported product `u ⊗ u`, since `u` is
solenoidal (`lem:lps-H1-estimate`). -/
theorem lps_h1_convection_test_identity
    {u : Vec3 → Vec3} {Du : Vec3 → Fin 3 → Vec3}
    {D2u : Vec3 → Fin 3 → Fin 3 → Vec3} {ψ : Vec3 → Vec3}
    (hu2 : MemLp u 2 volume) (hDu2 : MemLp Du 2 volume)
    (hD2u2 : MemLp D2u 2 volume)
    (hH1 : ∀ i : Fin 3, ∃ h : H1Function (Set.univ : Set Vec3),
      h.toFun = (fun x : Vec3 => u x i) ∧ h.grad = (fun x j => Du x i j))
    (hgu : ∀ i : Fin 3, HasWeakGradientOn (Set.univ : Set Vec3)
      (fun x => u x i) (fun x => Du x i))
    (hgrad : ∀ i j : Fin 3, HasWeakGradientOn (Set.univ : Set Vec3)
      (fun x => Du x i j) (fun x => D2u x i j))
    (htr : ∀ᵐ x ∂volume, ∑ j : Fin 3, Du x j j = 0)
    (hψ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => ψ x i))
    (hψc : ∀ i, HasCompactSupport (fun x => ψ x i)) :
    ∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3,
        u x i * u x j * spatialDeriv (fun y => ψ y i) j x =
      -∫ x : Vec3, ∑ i : Fin 3, (∑ j : Fin 3, u x j * Du x i j) * ψ x i := by
  have h6 := ESS.LPS.lps_regularised_h1_vector_six_bound hu2 hDu2 hH1
  have hu6 : MemLp u 6 volume := by
    refine lt_of_le_of_lt h6 ?_
    have hG := CKN.Leray.gagliardoNirenbergSobolevConstant_ne_top
    have h1 := hDu2.eLpNorm_ne_top
    finiteness
  have hu4 : MemLp u 4 volume :=
    serrin_memLp_interpolate (p := 2) (q := 6) (r := 4) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hu2 hu6
  have H22 : ENNReal.HolderTriple 2 2 1 := ⟨by simp [ENNReal.inv_two_add_inv_two]⟩
  have H44 : ENNReal.HolderTriple 4 4 2 := by
    have h := serrin_holder_ofReal3 (p := 4) (q := 4) (r := 2) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
    simpa only [ENNReal.ofReal_ofNat] using h
  set Dg : Vec3 → Fin 3 → Vec3 := fun x k j => spatialDeriv (fun y => ψ y k) j x with hDg
  have hg2 : MemLp ψ 2 volume :=
    memLp_pi_iff.mpr fun i => (lps_h1_test_memLp_two hψ hψc i 0).1
  have hDg2 : MemLp Dg 2 volume :=
    memLp_pi_iff.mpr fun k => memLp_pi_iff.mpr fun j => (lps_h1_test_memLp_two hψ hψc k j).2
  have hggrad : ∀ i : Fin 3, HasWeakGradientOn (Set.univ : Set Vec3)
      (fun x => ψ x i) (fun x => Dg x i) := fun i =>
    CKN.HasWeakGradientOn.of_contDiff (U := Set.univ) ((hψ i).of_le (by simp))
  have hbf : ∀ j k : Fin 3, MemLp (fun x => u x j * u x k) 2 volume := fun j k => by
    exact (hu4.eval j).mul (r := 2) (hu4.eval k)
  have hbDf : ∀ j k : Fin 3, MemLp (fun x => u x j * Du x k j) 2 volume := fun j k =>
    lps_h1_convection_term_memLp_two hu2 hDu2 hD2u2 hH1 hgrad j k
  have hvan := serrin_trilinear_vanish (b := u) (f := u) (g := ψ) (Db := Du) (Df := Du)
    (Dg := Dg) hu2 hDu2 hgu htr hu2 hDu2 hgu hg2 hDg2 hggrad (r := 2) (s := 2)
    (by norm_num) (by norm_num) hbf hbDf (fun k => hg2.eval k)
  -- integrability of the two pieces
  have hA (k j : Fin 3) : Integrable (fun x => u x j * Du x k j * ψ x k) volume :=
    ((hbDf j k).integrable_mul ((hg2.eval k)))
  have hB (k j : Fin 3) : Integrable (fun x => u x j * u x k * Dg x k j) volume :=
    ((hbf j k).integrable_mul ((hDg2.eval k).eval j))
  have hsplit : (∫ x : Vec3, ∑ k : Fin 3, ∑ j : Fin 3,
      u x j * (Du x k j * ψ x k + u x k * Dg x k j)) =
      (∫ x : Vec3, ∑ k : Fin 3, ∑ j : Fin 3, u x j * Du x k j * ψ x k) +
        ∫ x : Vec3, ∑ k : Fin 3, ∑ j : Fin 3, u x j * u x k * Dg x k j := by
    rw [← integral_add
      (integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ => hA k j)
      (integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ => hB k j)]
    congr 1
    funext x
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hsplit] at hvan
  have hA' : (∫ x : Vec3, ∑ k : Fin 3, ∑ j : Fin 3, u x j * Du x k j * ψ x k) =
      ∫ x : Vec3, ∑ i : Fin 3, (∑ j : Fin 3, u x j * Du x i j) * ψ x i := by
    congr 1
    funext x
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul]
  have hB' : (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3,
        u x i * u x j * spatialDeriv (fun y => ψ y i) j x) =
      ∫ x : Vec3, ∑ k : Fin 3, ∑ j : Fin 3, u x j * u x k * Dg x k j := by
    congr 1
    funext x
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [hDg]
    ring
  rw [hB', ← hA']
  linarith only [hvan]

/-- Pairing the second-derivative trace with a smooth compactly supported field
integrates by parts onto the first derivatives (`lem:lps-H1-estimate`). -/
theorem lps_h1_laplacian_test_identity
    {Du : Vec3 → Fin 3 → Vec3}
    {D2u : Vec3 → Fin 3 → Fin 3 → Vec3} {ψ : Vec3 → Vec3}
    (hgrad : ∀ i j : Fin 3, HasWeakGradientOn (Set.univ : Set Vec3)
      (fun x => Du x i j) (fun x => D2u x i j))
    (hψ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => ψ x i))
    (hψc : ∀ i, HasCompactSupport (fun x => ψ x i))
    (hDu2 : MemLp Du 2 volume) (hD2u2 : MemLp D2u 2 volume) :
    ∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3,
        Du x i j * spatialDeriv (fun y => ψ y i) j x =
      -∫ x : Vec3, ∑ i : Fin 3, (∑ j : Fin 3, D2u x i j j) * ψ x i := by
  have hpair (i j : Fin 3) :
      ∫ x : Vec3, Du x i j * spatialDeriv (fun y => ψ y i) j x =
        -∫ x : Vec3, D2u x i j j * ψ x i := by
    have h := hgrad i j j (fun x => ψ x i) (hψ i) (hψc i) (Set.subset_univ _)
    simpa only [Measure.restrict_univ, spatialDeriv] using h
  have hint1 (i j : Fin 3) : Integrable (fun x => Du x i j * spatialDeriv (fun y => ψ y i) j x)
      volume :=
    ((hDu2.eval i).eval j).integrable_mul (lps_h1_test_memLp_two hψ hψc i j).2
  have hint2 (i j : Fin 3) : Integrable (fun x => D2u x i j j * ψ x i) volume :=
    (((hD2u2.eval i).eval j).eval j).integrable_mul (lps_h1_test_memLp_two hψ hψc i j).1
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint1 i j]
  have hrhs : (∫ x : Vec3, ∑ i : Fin 3, (∑ j : Fin 3, D2u x i j j) * ψ x i) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∫ x : Vec3, D2u x i j j * ψ x i := by
    have : (fun x : Vec3 => ∑ i : Fin 3, (∑ j : Fin 3, D2u x i j j) * ψ x i) =
        fun x => ∑ i : Fin 3, ∑ j : Fin 3, D2u x i j j * ψ x i := by
      funext x
      exact Finset.sum_congr rfl fun i _ => Finset.sum_mul _ _ _
    rw [this, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint2 i j]
    exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ => hint2 i j
  rw [hrhs, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hint1 i j, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => hpair i j

private theorem lps_h1_spatialDeriv_sum {f : Fin 3 → Vec3 → ℝ}
    (hf : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (f j)) (i : Fin 3) :
    spatialDeriv (fun x => ∑ j : Fin 3, f j x) i =
      fun x => ∑ j : Fin 3, spatialDeriv (f j) i x := by
  funext x
  have hd (j : Fin 3) : DifferentiableAt ℝ (f j) x := (hf j).differentiable (by simp) x
  have := fderiv_fun_sum (u := Finset.univ) (A := f) (x := x) (fun j _ => hd j)
  simp only [spatialDeriv, this, sum_apply]

/-- The second-derivative trace of a weakly solenoidal `H²` field is weakly
solenoidal (`lem:lps-H1-estimate`). -/
theorem lps_h1_laplacian_weak_div_free
    {u : Vec3 → Vec3} {Du : Vec3 → Fin 3 → Vec3}
    {D2u : Vec3 → Fin 3 → Fin 3 → Vec3}
    (hu2 : MemLp u 2 volume) (hDu2 : MemLp Du 2 volume)
    (hD2u2 : MemLp D2u 2 volume)
    (hgu : ∀ i : Fin 3, HasWeakGradientOn (Set.univ : Set Vec3)
      (fun x => u x i) (fun x => Du x i))
    (hgrad : ∀ i j : Fin 3, HasWeakGradientOn (Set.univ : Set Vec3)
      (fun x => Du x i j) (fun x => D2u x i j))
    (hdiv : ∀ ψ : WeakTestFunction (Set.univ : Set Vec3),
      ∫ x : Vec3, ∑ i : Fin 3, u x i * ψ.partialDeriv i x = 0) :
    IsWeakDivFreeL2 (fun x i => ∑ j : Fin 3, D2u x i j j) := by
  refine ⟨?_, fun ψ => ?_⟩
  · exact ESS.LPS.lps_h1_laplacian_memLp_two hD2u2 (fun x i => rfl)
  · have hψs : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => (ψ.partialDeriv i x)) := fun i =>
      contDiff_spatialDeriv_smooth ψ.contDiff i
    have hψc : ∀ i, HasCompactSupport (fun x => ψ.partialDeriv i x) := fun i =>
      ψ.hasCompactSupport.fderiv_apply (𝕜 := ℝ) (basisVec i)
    -- the vector field `Ψ x i = ∂ᵢψ`
    have h1 := lps_h1_laplacian_test_identity (Du := Du) (D2u := D2u)
      (ψ := fun x i => ψ.partialDeriv i x) hgrad hψs hψc hDu2 hD2u2
    have hlhs : (∫ x : Vec3, ∑ i : Fin 3, (fun x i => ∑ j : Fin 3, D2u x i j j) x i *
        ψ.partialDeriv i x) =
        ∫ x : Vec3, ∑ i : Fin 3, (∑ j : Fin 3, D2u x i j j) * ψ.partialDeriv i x := rfl
    rw [hlhs, ← neg_eq_zero, ← h1]
    -- second integration by parts onto `u`
    let ψ0 : Vec3 → ℝ := ψ.toFun
    have hψ0 : ContDiff ℝ (⊤ : ℕ∞) ψ0 := ψ.contDiff
    let D1 : Fin 3 → Vec3 → ℝ := fun i => spatialDeriv ψ0 i
    let D2 : Fin 3 → Fin 3 → Vec3 → ℝ := fun i j => spatialDeriv (D1 i) j
    have hD1 (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (D1 i) := contDiff_spatialDeriv_smooth hψ0 i
    have hD2 (i j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (D2 i j) :=
      contDiff_spatialDeriv_smooth (hD1 i) j
    have hD1c (i : Fin 3) : HasCompactSupport (D1 i) :=
      ψ.hasCompactSupport.fderiv_apply (𝕜 := ℝ) (basisVec i)
    have hD2c (i j : Fin 3) : HasCompactSupport (D2 i j) :=
      (hD1c i).fderiv_apply (𝕜 := ℝ) (basisVec j)
    have hswap1 (i j : Fin 3) : D2 i j = spatialDeriv (D1 j) i := by
      funext x
      exact mixedSecond_swap hψ0 j i x
    have hswap2 (i j : Fin 3) : spatialDeriv (D2 i j) j = spatialDeriv (D2 j j) i := by
      funext x
      rw [hswap1 i j]
      exact mixedSecond_swap (hD1 j) j i x
    have hpair2 (i j : Fin 3) :
        ∫ x : Vec3, Du x i j * D2 i j x = -∫ x : Vec3, u x i * spatialDeriv (D2 i j) j x := by
      have h := hgu i j (D2 i j) (hD2 i j) (hD2c i j) (Set.subset_univ _)
      simp only [Measure.restrict_univ] at h
      have h' : ∫ x : Vec3, u x i * spatialDeriv (D2 i j) j x =
          -∫ x : Vec3, Du x i j * D2 i j x := h
      linarith only [h']
    have hD2mem (i j : Fin 3) : MemLp (D2 i j) 2 volume :=
      (hD2 i j).continuous.memLp_of_hasCompactSupport (hD2c i j)
    have hD3mem (i j : Fin 3) : MemLp (spatialDeriv (D2 i j) j) 2 volume :=
      (contDiff_spatialDeriv_smooth (hD2 i j) j).continuous.memLp_of_hasCompactSupport
        ((hD2c i j).fderiv_apply (𝕜 := ℝ) (basisVec j))
    have hint1 (i j : Fin 3) : Integrable (fun x => Du x i j * D2 i j x) volume :=
      ((hDu2.eval i).eval j).integrable_mul (hD2mem i j)
    have hint2 (i j : Fin 3) :
        Integrable (fun x => u x i * spatialDeriv (D2 i j) j x) volume :=
      (hu2.eval i).integrable_mul (hD3mem i j)
    -- the test function `Δψ`
    have hL : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (D2 j j) := fun j => hD2 j j
    have hLs : ContDiff ℝ (⊤ : ℕ∞) (fun x => ∑ j : Fin 3, D2 j j x) := by
      exact ContDiff.sum (fun j _ => hL j)
    have hLc : HasCompactSupport (fun x => ∑ j : Fin 3, D2 j j x) := by
      simp only [Fin.sum_univ_three]
      exact ((hD2c 0 0).add (hD2c 1 1)).add (hD2c 2 2)
    let ψ' : WeakTestFunction (Set.univ : Set Vec3) := ⟨_, hLs, hLc, Set.subset_univ _⟩
    have hd := hdiv ψ'
    have hderiv (i : Fin 3) : ψ'.partialDeriv i = fun x => ∑ j : Fin 3, spatialDeriv (D2 j j) i x :=
      lps_h1_spatialDeriv_sum hL i
    have hsum : (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, Du x i j * D2 i j x) =
        -∫ x : Vec3, ∑ i : Fin 3, u x i * ψ'.partialDeriv i x := by
      rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint1 i j]
      have : (∫ x : Vec3, ∑ i : Fin 3, u x i * ψ'.partialDeriv i x) =
          ∑ i : Fin 3, ∑ j : Fin 3, ∫ x : Vec3, u x i * spatialDeriv (D2 i j) j x := by
        have hΨmem (i : Fin 3) : MemLp (ψ'.partialDeriv i) 2 volume := by
          rw [hderiv i]
          exact memLp_finsetSum Finset.univ fun j _ =>
            ((contDiff_spatialDeriv_smooth (hL j) i).continuous.memLp_of_hasCompactSupport
              ((hD2c j j).fderiv_apply (𝕜 := ℝ) (basisVec i)))
        have hintΨ (i : Fin 3) : Integrable (fun x => u x i * ψ'.partialDeriv i x) volume :=
          (hu2.eval i).integrable_mul (hΨmem i)
        rw [integral_finsetSum _ fun i _ => hintΨ i]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hfun : (fun x => u x i * ψ'.partialDeriv i x) =
            fun x => ∑ j : Fin 3, u x i * spatialDeriv (D2 i j) j x := by
          funext x
          rw [hderiv i, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hswap2 i j]
        rw [hfun, integral_finsetSum _ fun j _ => hint2 i j]
      rw [this, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum _ fun j _ => hint1 i j, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun j _ => hpair2 i j
    have hgoal : (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3,
        Du x i j * spatialDeriv (fun y => ψ.partialDeriv i y) j x) =
        ∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, Du x i j * D2 i j x := rfl
    rw [hgoal, hsum, hd, neg_zero]

end ESS

end
