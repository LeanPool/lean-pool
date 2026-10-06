/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorIntrinsicGrowthGoodTail
public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteLipschitzCoreBase

/-!
# High-contrast homogenization: Provider.Regularity.CorrectorCoarseOscillationGrowth

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Coarse-grained cube growth of the anchored corrector

At a good scale the large-scale Poincare inequality on nested adapted cubes
bounds the normalized `L²` oscillation of a cube solution by the scale times its
coefficient energy, with a constant depending only on the dimension and the
multiscale order: the lower ellipticity entering it is the coarse-grained
response average of the good cube, never a pointwise ellipticity constant.

Applied to the affine-plus-corrector cube solution, and after removing the
affine part by the elementary bound on a centered linear function, this is the
scale-linear oscillation growth of the anchored corrector itself, which is what
the anchored mean telescope consumes.  No representative of the physical
coefficient field appears in it.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- A pointwise bound on a cube controls every finite normalized cube
`Lᵖ` norm. -/
theorem cubeLpNorm_le_of_bound_on_cubeSet
    {d : ℕ} (Q : TriadicCube d) (p : ℝ≥0∞) (hp : p ≠ 0)
    (f : Vec d → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x ∈ cubeSet Q, ‖f x‖ ≤ B) :
    cubeLpNorm Q p f ≤ B := by
  by_cases hfm : AEStronglyMeasurable f (normalizedCubeMeasure Q)
  swap
  · rw [cubeLpNorm, eLpNorm_of_not_aestronglyMeasurable hfm, ENNReal.toReal_top]
    exact hB
  have hboundCube : ∀ᵐ x ∂ (cubeMeasure Q), ‖f x‖ ≤ ‖B‖ := by
    rw [cubeMeasure,
      MeasureTheory.ae_restrict_iff' (measurableSet_cubeSet Q)]
    exact Filter.Eventually.of_forall fun x hx => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg hB] using hbound x hx
  have hboundNormalized : ∀ᵐ x ∂ (normalizedCubeMeasure Q), ‖f x‖ ≤ ‖B‖ := by
    simpa only [normalizedCubeMeasure] using
      Measure.ae_smul_measure hboundCube
        (ENNReal.ofReal ((cubeVolume Q)⁻¹))
  have hle : eLpNorm f p (normalizedCubeMeasure Q) ≤
      eLpNorm (fun _ : Vec d => B) p (normalizedCubeMeasure Q) :=
    eLpNorm_mono_ae hfm hboundNormalized
  have htop : eLpNorm (fun _ : Vec d => B) p
      (normalizedCubeMeasure Q) ≠ ⊤ := by
    exact (memLp_const B).eLpNorm_ne_top
  have hreal := ENNReal.toReal_mono htop hle
  calc
    cubeLpNorm Q p f ≤
        cubeLpNorm Q p (fun _ : Vec d => B) := by
      simpa only [cubeLpNorm] using hreal
    _ = ‖B‖ := cubeLpNorm_const Q p B hp
    _ = B := by rw [Real.norm_eq_abs, abs_of_nonneg hB]

/-- The normalized `L²` norm of a centered affine function is bounded by
half its coordinate `ℓ¹` slope times the cube side length. -/
theorem cubeLpNorm_originCube_vecDot_le
    {d : ℕ} (q : ℕ) (e : Vec d) :
    cubeLpNorm (originCube d (q : ℤ)) 2 (fun x => vecDot e x) ≤
      ((∑ i : Fin d, |e i|) / 2) * (3 : ℝ) ^ q := by
  let B : ℝ := ((∑ i : Fin d, |e i|) / 2) * (3 : ℝ) ^ q
  have hB : 0 ≤ B := by
    dsimp only [B]
    positivity
  apply cubeLpNorm_le_of_bound_on_cubeSet
    (originCube d (q : ℤ)) 2 (by norm_num) _ hB
  intro x hx
  have hxcoord : ∀ i : Fin d, |x i| ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ q := by
    intro i
    rcases (mem_cubeSet_originCube_iff.mp hx) i with ⟨hlo, hhi⟩
    rw [abs_le]
    constructor
    · simp only [zpow_natCast] at hlo
      linarith only [hlo]
    · simpa only [zpow_natCast] using hhi.le
  calc
    ‖vecDot e x‖ = |∑ i : Fin d, e i * x i| := by
      rw [Real.norm_eq_abs]
      rfl
    _ ≤ ∑ i : Fin d, |e i * x i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin d, |e i| * |x i| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [abs_mul]
    _ ≤ ∑ i : Fin d, |e i| * ((1 / 2 : ℝ) * (3 : ℝ) ^ q) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hxcoord i) (abs_nonneg (e i))
    _ = B := by
      dsimp only [B]
      rw [← Finset.sum_mul]
      ring

/-- The coordinate sum of a vector is at most the dimension times its Euclidean
norm. -/
private theorem sum_abs_le_dim_mul_euclideanNorm {d : ℕ} (e : Vec d) :
    ∑ i : Fin d, |e i| ≤ (d : ℝ) * euclideanNorm e := by
  calc ∑ i : Fin d, |e i| ≤ ∑ _i : Fin d, euclideanNorm e :=
        Finset.sum_le_sum fun i _ => abs_coordinate_le_euclideanNorm e i
    _ = (d : ℝ) * euclideanNorm e := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **Coarse-grained Poincare for the joint local corrector.**  At a good scale
the normalized `L²` oscillation of the anchored corrector on a centered triadic
cube is bounded by the scale times the Euclidean slope, with a constant
depending only on the dimension and the multiscale order. -/
theorem exists_scalarIdentityGoodTailCorrectorOscillationConstant
    (d : ℕ) [NeZero d] (s : ℝ) (hs : 0 < s) (hs_lt : s < 1 / 2) :
    ∃ K c : ℝ, 0 < K ∧ c ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ) (n : ℤ),
        delta ∈ Set.Ioc (0 : ℝ) c →
        ScalarIdentityGoodTail a s delta n →
        ∀ (hCauchy : FiniteAffineCorrectionLocalCauchy a)
          (e : Vec d) (q : ℕ), n ≤ (q : ℤ) →
          cubeBesovOscillation (originCube d (q : ℤ)) (2 : ℝ≥0∞)
              ((finiteAffineCorrectionJointLocalLimit a hCauchy e).localH1Function
                q).toFun ≤
            K * euclideanNorm e * (3 : ℝ) ^ q := by
  obtain ⟨CP, hCP, hpoin⟩ := exists_finiteLipschitzPoincareConstant d s hs hs_lt
  obtain ⟨B, c, hB, hc, hweighted⟩ :=
    exists_scalarIdentityGoodTailJointWeightedGradientBoundConstant d s hs hs_lt
  refine ⟨2 * (CP * B) + (d : ℝ), c, by positivity, hc, ?_⟩
  intro a delta n hdelta hgood hCauchy e q hnq
  let Q : TriadicCube d := originCube d (q : ℤ)
  let u : Book.Ch03.CubeSolution Q a :=
    finiteAffineCorrectionJointLocalCubeSolution a hCauchy e q
  let phi : H1Function (openCubeSet Q) :=
    (finiteAffineCorrectionJointLocalLimit a hCauchy e).localH1Function q
  let ell : H1Function (openCubeSet Q) := finiteAffineBoundaryH1 (q : ℤ) e
  have hellFun : ell.toFun = fun x => vecDot e x := by
    simpa only [ell] using finiteAffineBoundaryH1_toFun (m := (q : ℤ)) e
  have hweak : scalarIdentityWeakError a s (q : ℤ) ≤ 1 :=
    (hgood.weakError_le hnq).trans (hdelta.2.trans hc.2.le)
  have hscalePos : (0 : ℝ) < (3 : ℝ) ^ q := by positivity
  have hweight : cubeBesovScaleWeight 1 Q = ((3 : ℝ) ^ q)⁻¹ := by
    simp only [Q, cubeBesovScaleWeight, Real.rpow_neg_one,
      cubeScaleFactor_originCube, zpow_natCast]
  have henergy :
      Book.Ch03.h1EnergyNormOnCube Q a u.toH1 ≤ B * euclideanNorm e := by
    have hbound := hweighted a delta n hdelta hgood hCauchy e q hnq
    have heq :
        weightedGradNorm (a.coeffOn Q).toCoeffField (openCubeSet Q) u.toH1.grad =
          ENNReal.ofReal (Book.Ch03.h1EnergyNormOnCube Q a u.toH1) :=
      weightedGradNorm_eq_ofReal_h1EnergyNormOnCube Q a u.toH1
    refine (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg hB.le (euclideanNorm_nonneg e))).1 ?_
    rw [← heq]
    simpa only [Q, u, localGradientCube,
      finiteAffineCorrectionJointLocalCubeSolution_toH1] using hbound
  have hoscFull :
      cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u.toH1.toFun) ≤
        (3 : ℝ) ^ q * (CP * (B * euclideanNorm e)) := by
    have h := hpoin a (q : ℤ) u hweak
    rw [hweight, inv_mul_le_iff₀ hscalePos] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left henergy hCP.le) hscalePos.le)
  have hmemU : MemLp u.toH1.toFun (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    u.toH1.memL2_normalizedCubeMeasure
  have hmemPhi : MemLp phi.toFun (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    phi.memL2_normalizedCubeMeasure
  have hmemAffine : MemLp (fun x : Vec d => vecDot e x) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) := by
    rw [← hellFun]
    exact ell.memL2_normalizedCubeMeasure
  have hsplit : ∀ x : Vec d, u.toH1.toFun x = vecDot e x + phi.toFun x := by
    intro x
    have h : u.toH1.toFun x = ell.toFun x + phi.toFun x := by
      simp only [u, phi, ell, finiteAffineCorrectionJointLocalCubeSolution_toH1,
        finiteAffineCorrectionJointLocalH1, H1Function.add_toFun]
      rfl
    rw [h, hellFun]
  let cbar : ℝ := cubeAverage Q u.toH1.toFun
  let g : Vec d → ℝ := fun x => phi.toFun x - cbar
  have hmemG : MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    hmemPhi.sub (memLp_const cbar)
  have hfluctEq : cubeFluctuation Q g = cubeFluctuation Q phi.toFun :=
    cubeFluctuation_sub_const_of_memLp_two Q hmemPhi cbar
  have hgEq : g = cubeFluctuation Q u.toH1.toFun + (fun x => -(vecDot e x)) := by
    funext x
    simp only [g, cbar, cubeFluctuation, Pi.add_apply, hsplit x]
    ring
  have hmemFluct : MemLp (cubeFluctuation Q u.toH1.toFun) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) := hmemU.sub (memLp_const _)
  have htri := cubeLpNorm_add_le Q (2 : ℝ≥0∞)
    (cubeFluctuation Q u.toH1.toFun) (fun x : Vec d => -(vecDot e x))
    hmemFluct hmemAffine.neg (by norm_num)
  have hneg : cubeLpNorm Q (2 : ℝ≥0∞) (fun x : Vec d => -(vecDot e x)) =
      cubeLpNorm Q (2 : ℝ≥0∞) (fun x : Vec d => vecDot e x) := by
    unfold cubeLpNorm
    rw [show (fun x : Vec d => -(vecDot e x)) =
      -(fun x : Vec d => vecDot e x) from rfl, MeasureTheory.eLpNorm_neg]
  have haffine : cubeLpNorm Q (2 : ℝ≥0∞) (fun x : Vec d => vecDot e x) ≤
      ((d : ℝ) / 2) * euclideanNorm e * (3 : ℝ) ^ q := by
    refine (cubeLpNorm_originCube_vecDot_le q e).trans ?_
    have hsum := sum_abs_le_dim_mul_euclideanNorm e
    have hhalf : (∑ i : Fin d, |e i|) / 2 ≤ ((d : ℝ) * euclideanNorm e) / 2 := by
      linarith only [hsum]
    calc (∑ i : Fin d, |e i|) / 2 * (3 : ℝ) ^ q
        ≤ ((d : ℝ) * euclideanNorm e) / 2 * (3 : ℝ) ^ q :=
          mul_le_mul_of_nonneg_right hhalf hscalePos.le
      _ = ((d : ℝ) / 2) * euclideanNorm e * (3 : ℝ) ^ q := by ring
  calc cubeBesovOscillation Q (2 : ℝ≥0∞) phi.toFun
      = cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q g) := by
        show cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q phi.toFun) =
          cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q g)
        rw [hfluctEq]
    _ ≤ 2 * cubeLpNorm Q (2 : ℝ≥0∞) g :=
        cubeLpNorm_two_cubeFluctuation_le_two_mul Q g hmemG
    _ ≤ 2 * (cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u.toH1.toFun) +
          cubeLpNorm Q (2 : ℝ≥0∞) (fun x : Vec d => vecDot e x)) := by
        rw [hgEq, ← hneg]
        exact mul_le_mul_of_nonneg_left htri (by norm_num)
    _ ≤ 2 * ((3 : ℝ) ^ q * (CP * (B * euclideanNorm e)) +
          ((d : ℝ) / 2) * euclideanNorm e * (3 : ℝ) ^ q) :=
        mul_le_mul_of_nonneg_left (add_le_add hoscFull haffine) (by norm_num)
    _ = (2 * (CP * B) + (d : ℝ)) * euclideanNorm e * (3 : ℝ) ^ q := by ring

end

end HighContrast
end HCPolySupport
