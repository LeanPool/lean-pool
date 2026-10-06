/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.C1FixedProjectionIncrement
public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteAffineGradientExcessRateSelection

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Corrector.C1FiniteFixedBaseDecay

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# One base minimizer on every intermediate cube

The exact minimizer chosen on the base cube is retained while the observation
cube varies.  Consecutive minimizer increments are propagated by the available
quarter-power energy growth and summed against the available real-rate excess
decay.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open MeasureTheory
open scoped ENNReal

noncomputable section

private theorem finiteAffineGradientExcess_ne_top_fixed
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    {n m : ℤ} (hnm : n ≤ m)
    (u : Book.Ch03.CubeSolution (originCube d m) a) :
    finiteAffineGradientExcess a n m u ≠ ∞ := by
  have hcandidate : weightedGradNorm
      (a.coeffOn (originCube d n)).toCoeffField
      (openCubeSet (originCube d n))
      (fun x ↦ u.toH1.grad x -
        (finiteAffineSolution a m (0 : Vec d)).toH1.grad x) ≠ ∞ := by
    rw [weightedGradNorm_finiteAffineGradientResidual a hnm u 0]
    exact ENNReal.ofReal_ne_top
  exact ne_top_of_le_ne_top hcandidate
    (finiteAffineGradientExcess_le a n m u 0)

private theorem excess_toReal_le_of_rate_fixed
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    {n m : ℤ}
    (u : Book.Ch03.CubeSolution (originCube d m) a)
    (K : ℝ) (hK : 0 ≤ K)
    (hdecay : finiteAffineGradientExcess a n m u ≤
      ENNReal.ofReal K * finiteAffineGradientExcess a m m u) :
    (finiteAffineGradientExcess a n m u).toReal ≤
      K * (finiteAffineGradientExcess a m m u).toReal := by
  have hterminal := finiteAffineGradientExcess_ne_top_fixed a le_rfl u
  have hproduct : ENNReal.ofReal K * finiteAffineGradientExcess a m m u ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hterminal
  have hreal := ENNReal.toReal_mono hproduct hdecay
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hK] using hreal

@[expose]
public noncomputable def finiteTrialGradientLinearMap_field
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    {q m : ℕ} (hqm : q ≤ m) :
    Vec d →ₗ[ℝ] LocalGradientL2 d q where
  toFun e := ((finiteTrialHarmonicGradientLinearMap a hqm) e :
    LocalGradientL2 d q)
  map_add' e e' := by
    exact congrArg Subtype.val
      (map_add (finiteTrialHarmonicGradientLinearMap a hqm) e e')
  map_smul' c e := by
    exact congrArg Subtype.val
      (map_smul (finiteTrialHarmonicGradientLinearMap a hqm) c e)

private theorem finiteTrialGradientLinearMap_energy
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    {q m : ℕ} (hqm : q ≤ m) (b : Vec d) :
    Real.sqrt (normalizedLocalSymmetricEnergy
        (Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
          (originCube d (q : ℤ)) a)
        (finiteTrialGradientLinearMap_field a hqm b)) =
      finiteCenteredCubeSolutionEnergy a (m : ℤ)
        (finiteAffineCubeSolution a (m : ℤ) b) (q : ℤ) := by
  let w := finiteCubeSolutionRestriction a
    (show (q : ℤ) ≤ (m : ℤ) by exact_mod_cast hqm)
    (finiteAffineCubeSolution a (m : ℤ) b)
  have hclass : finiteTrialGradientLinearMap_field a hqm b =
      w.toH1.gradToHilbertVectorL2 := by rfl
  have hsqrt := sqrt_normalizedEnergy_grad_eq_weightedGradNorm_toReal
    (Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
      (originCube d (q : ℤ)) a) w.toH1
  erw [hclass, hsqrt]
  rw [weightedGradNorm_congr_coeff_ae_on _
    (Book.Ch03.publicCoeffField_ae_eq_openCubeSet
      (originCube d (q : ℤ)) a)]
  rw [weightedGradNorm_eq_ofReal_h1EnergyNormOnCube]
  rw [ENNReal.toReal_ofReal]
  · exact (finiteCenteredCubeSolutionEnergy_eq_of_le a (m : ℤ)
      (finiteAffineCubeSolution a (m : ℤ) b) (q : ℤ)
      (by exact_mod_cast hqm)).symm
  · unfold Book.Ch03.h1EnergyNormOnCube
    exact Real.sqrt_nonneg _

/-- The trial-map residual is the restricted affine residual gradient class. -/
theorem finiteTrialGradientResidual_eq
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    {q m : ℕ} (hqm : q ≤ m)
    (u : Book.Ch03.CubeSolution (originCube d (m : ℤ)) a) (b : Vec d) :
    let J : LocalGradientL2 d q := (finiteCubeSolutionRestriction a
      (show (q : ℤ) ≤ (m : ℤ) by exact_mod_cast hqm) u).toH1.gradToHilbertVectorL2
    J - finiteTrialGradientLinearMap_field a hqm b =
        (finiteAffineGradientResidual a
          (show (q : ℤ) ≤ (m : ℤ) by exact_mod_cast hqm) u b).toH1.gradToHilbertVectorL2 := by
  dsimp only
  let uQ := finiteCubeSolutionRestriction a
    (show (q : ℤ) ≤ (m : ℤ) by exact_mod_cast hqm) u
  have hTfield : finiteTrialGradientLinearMap_field a hqm b =
      (finiteCubeSolutionRestriction a
        (show (q : ℤ) ≤ (m : ℤ) by exact_mod_cast hqm)
        (finiteAffineCubeSolution a (m : ℤ) b)).toH1.gradToHilbertVectorL2 := by
    rfl
  rw [hTfield]
  apply MeasureTheory.Lp.ext
  filter_upwards [uQ.toH1.coeFn_gradToHilbertVectorL2,
      (finiteCubeSolutionRestriction a
        (show (q : ℤ) ≤ (m : ℤ) by exact_mod_cast hqm)
        (finiteAffineCubeSolution a (m : ℤ) b)).toH1.coeFn_gradToHilbertVectorL2,
      ((finiteAffineGradientResidual a
        (show (q : ℤ) ≤ (m : ℤ) by exact_mod_cast hqm) u b).toH1).coeFn_gradToHilbertVectorL2,
      MeasureTheory.Lp.coeFn_sub uQ.toH1.gradToHilbertVectorL2
        (finiteCubeSolutionRestriction a
          (show (q : ℤ) ≤ (m : ℤ) by exact_mod_cast hqm)
          (finiteAffineCubeSolution a (m : ℤ) b)).toH1.gradToHilbertVectorL2]
    with x huq htrial hres hsub
  erw [hsub, Pi.sub_apply, huq, htrial, hres]
  simp only [uQ, finiteCubeSolutionRestriction_grad,
    finiteAffineGradientResidual_grad]
  change WithLp.toLp 2 _ - WithLp.toLp 2 _ = WithLp.toLp 2 _
  rw [← WithLp.toLp_sub]
  rfl

private theorem rpow_eta_le_three {eta : ℝ}
    (heta1 : eta < 1) : Real.rpow 3 eta ≤ 3 := by
  calc
    Real.rpow 3 eta ≤ Real.rpow 3 1 :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) heta1.le
    _ = 3 := by norm_num

private theorem finite_trial_minimizer_residual_real_decay
    {d : ℕ} [NeZero d] (s eta cdec Cdec Cfamily : ℝ) (hCdec : 0 < Cdec)
    (hdecay : ∀ (a : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ) (n m : ℤ),
      n < m → delta ∈ Set.Ioc (0 : ℝ) cdec →
        ScalarIdentityGoodMaxOnInterval a s delta n m →
        ∃ Q : ℤ → Mat d,
          IsFiniteAffineSlopeFamily a delta Cfamily n m Q ∧
          ∀ u : Book.Ch03.CubeSolution (originCube d m) a,
            finiteAffineGradientExcess a n m u ≤
              ENNReal.ofReal (Cdec * Real.rpow 3 (-eta * ((m - n : ℤ) : ℝ))) *
                finiteAffineGradientExcess a m m u)
    (a : Book.Ch02.TriadicCoeffFamily d) {delta : ℝ} {n m q : ℕ}
    (hnq : n ≤ q) (hqm : q ≤ m)
    (hgood : ScalarIdentityGoodTail a s delta (n : ℤ))
    (hdeltaDec : delta ∈ Set.Ioc (0 : ℝ) cdec)
    (u : Book.Ch03.CubeSolution (originCube d (m : ℤ)) a)
    (b : ℤ → Vec d)
    (hb_at : ∀ {j : ℤ} (hjm : j ≤ (m : ℤ)),
      b j = finiteAffineExactMinimizer a hjm u)
    : Real.sqrt (normalizedLocalSymmetricEnergy
        (Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
          (originCube d (q : ℤ)) a)
        ((finiteCubeSolutionRestriction a
          (show (q : ℤ) ≤ (m : ℤ) by exact_mod_cast hqm) u).toH1.gradToHilbertVectorL2 -
          finiteTrialGradientLinearMap_field a hqm (b (q : ℤ)))) ≤
      max 1 Cdec * Real.rpow 3 (-eta * (((m : ℤ) : ℝ) - ((q : ℤ) : ℝ))) *
        (finiteAffineGradientExcess a (m : ℤ) (m : ℤ) u).toReal := by
  let A : ℝ := max 1 Cdec
  let Em : ℝ := (finiteAffineGradientExcess a (m : ℤ) (m : ℤ) u).toReal
  let T := finiteTrialGradientLinearMap_field a hqm
  let hEll := Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
    (originCube d (q : ℤ)) a
  have hEm : 0 ≤ Em := ENNReal.toReal_nonneg
  have hCdecA : Cdec ≤ A := le_max_right _ _
  let uQ := finiteCubeSolutionRestriction a
    (show (q : ℤ) ≤ (m : ℤ) by exact_mod_cast hqm) u
  let J : LocalGradientL2 d q := uQ.toH1.gradToHilbertVectorL2
  have hbq := finiteAffineExactMinimizer_spec a
    (show (q : ℤ) ≤ (m : ℤ) by exact_mod_cast hqm) u
  have hres : J - T (b (q : ℤ)) =
      (finiteAffineGradientResidual a
        (show (q : ℤ) ≤ (m : ℤ) by exact_mod_cast hqm) u
        (b (q : ℤ))).toH1.gradToHilbertVectorL2 := by
    simpa only [J, uQ, T] using
      finiteTrialGradientResidual_eq a hqm u (b (q : ℤ))
  erw [hres, sqrt_normalizedEnergy_grad_eq_weightedGradNorm_toReal]
  have hbq' : weightedGradNorm
        (a.coeffOn (originCube d (q : ℤ))).toCoeffField
        (openCubeSet (originCube d (q : ℤ)))
        (fun x ↦ u.toH1.grad x -
          (finiteAffineSolution a (m : ℤ) (b (q : ℤ))).toH1.grad x) =
      finiteAffineGradientExcess a (q : ℤ) (m : ℤ) u := by
    simpa only [hb_at (show (q : ℤ) ≤ (m : ℤ) by exact_mod_cast hqm)] using hbq
  rw [weightedGradNorm_congr_coeff_ae_on _
    (Book.Ch03.publicCoeffField_ae_eq_openCubeSet
      (originCube d (q : ℤ)) a)]
  rw [finiteAffineGradientResidual_grad, hbq']
  by_cases hqmEq : q = m
  · subst q
    have hrateOne : Real.rpow 3
        (-eta * (((m : ℤ) : ℝ) - ((m : ℤ) : ℝ))) = 1 := by
      norm_num
    rw [hrateOne, mul_one]
    exact le_mul_of_one_le_left hEm (le_max_left _ _)
  · have hqmt : (q : ℤ) < (m : ℤ) := by exact_mod_cast lt_of_le_of_ne hqm hqmEq
    have hgoodQ := (hgood.mono_start (by exact_mod_cast hnq)).goodMaxOnInterval
      hqmt.le
    obtain ⟨_Q, _hQ, hrate⟩ := hdecay a delta (q : ℤ) (m : ℤ)
      hqmt hdeltaDec hgoodQ
    have hrateExpanded : finiteAffineGradientExcess a (q : ℤ) (m : ℤ) u ≤
        ENNReal.ofReal (Cdec * Real.rpow 3
          (-eta * (((m : ℤ) : ℝ) - ((q : ℤ) : ℝ)))) *
          finiteAffineGradientExcess a (m : ℤ) (m : ℤ) u := by
      simpa only [Int.cast_sub] using hrate u
    have hreal := excess_toReal_le_of_rate_fixed a u
      (Cdec * Real.rpow 3 (-eta * (((m : ℤ) : ℝ) - ((q : ℤ) : ℝ))))
      (mul_nonneg hCdec.le (Real.rpow_nonneg (by norm_num) _)) hrateExpanded
    exact hreal.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCdecA
        (Real.rpow_nonneg (by norm_num) _)) hEm)

private theorem finite_trial_minimizer_increment_real_decay
    {d : ℕ} [NeZero d] (s eta cgrow Cgrow cdec Cdec Cfamily : ℝ)
    (heta1 : eta < 1) (hCdec : 0 < Cdec)
    (hgrowth : ∀ (a : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ)
      (n m : ℤ), n < m →
      delta ∈ Set.Ioc (0 : ℝ) cgrow →
      ScalarIdentityGoodMaxOnInterval a s delta n m →
      ∀ (j : ℤ) (_hj : j ∈ Finset.Icc n m)
        (k : ℤ) (_hk : k ∈ Finset.Icc n m), j ≤ k → ∀ b : Vec d,
        finiteCenteredCubeSolutionEnergy a m
            (finiteAffineCubeSolution a m b) k ≤
          Cgrow ^ 2 * Real.rpow 3
              (((Int.toNat (k - j) : ℕ) : ℝ) / 4) *
            finiteCenteredCubeSolutionEnergy a m
              (finiteAffineCubeSolution a m b) j)
    (hdecay : ∀ (a : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ) (n m : ℤ),
      n < m → delta ∈ Set.Ioc (0 : ℝ) cdec →
        ScalarIdentityGoodMaxOnInterval a s delta n m →
        ∃ Q : ℤ → Mat d,
          IsFiniteAffineSlopeFamily a delta Cfamily n m Q ∧
          ∀ u : Book.Ch03.CubeSolution (originCube d m) a,
            finiteAffineGradientExcess a n m u ≤
              ENNReal.ofReal (Cdec * Real.rpow 3 (-eta * ((m - n : ℤ) : ℝ))) *
                finiteAffineGradientExcess a m m u)
    (a : Book.Ch02.TriadicCoeffFamily d) {delta : ℝ} {n m q : ℕ}
    (hnm2 : n + 2 ≤ m) (hqm : q ≤ m)
    (hgood : ScalarIdentityGoodTail a s delta (n : ℤ))
    (hdeltaDec : delta ∈ Set.Ioc (0 : ℝ) cdec)
    (u : Book.Ch03.CubeSolution (originCube d (m : ℤ)) a)
    (b : ℤ → Vec d)
    (hb_at : ∀ {j : ℤ} (hjm : j ≤ (m : ℤ)),
      b j = finiteAffineExactMinimizer a hjm u)
    (hdeltaGrow : delta ∈ Set.Ioc (0 : ℝ) cgrow) :
    ∀ j ∈ Finset.Ico (n : ℤ) (q : ℤ),
      Real.sqrt (normalizedLocalSymmetricEnergy
          (Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
            (originCube d (q : ℤ)) a)
          (finiteTrialGradientLinearMap_field a hqm (b (j + 1) - b j))) ≤
        (Cgrow ^ 2 * max 1 Cdec * (1 + 3 * ((3 ^ d : ℕ) : ℝ))) *
          Real.rpow 3 ((((q : ℤ) : ℝ) - (j : ℝ)) / 4) *
          Real.rpow 3 (-eta * (((m : ℤ) : ℝ) - (j : ℝ))) *
          (finiteAffineGradientExcess a (m : ℤ) (m : ℤ) u).toReal := by
  let A : ℝ := max 1 Cdec
  let Em : ℝ := (finiteAffineGradientExcess a (m : ℤ) (m : ℤ) u).toReal
  let T := finiteTrialGradientLinearMap_field a hqm
  let hEll := Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
    (originCube d (q : ℤ)) a
  have hEm : 0 ≤ Em := ENNReal.toReal_nonneg
  have hA0 : 0 ≤ A := (le_max_left (1 : ℝ) Cdec).trans' zero_le_one
  have hCdecA : Cdec ≤ A := le_max_right _ _
  let D : ℝ := ((3 ^ d : ℕ) : ℝ)
  let B : ℝ := Cgrow ^ 2 * A * (1 + 3 * D)
  have hgoodNM : ScalarIdentityGoodMaxOnInterval a s delta
      (n : ℤ) (m : ℤ) := hgood.goodMaxOnInterval (by omega)
  intro j hj
  have hjm : j + 1 ≤ (m : ℤ) := by
    have := Finset.mem_Ico.mp hj
    omega
  have henergy := finiteAffineExactMinimizerIncrementEnergy_le
    s cgrow Cgrow hgrowth a delta (by omega : (n : ℤ) < (m : ℤ))
    hdeltaGrow hgoodNM hj (by exact_mod_cast hqm) u
  rw [← hb_at (by omega : j ≤ (m : ℤ)),
    ← hb_at hjm] at henergy
  have hEj : (finiteAffineGradientExcess a j (m : ℤ) u).toReal ≤
      A * Real.rpow 3 (-eta * (((m : ℤ) : ℝ) - (j : ℝ))) * Em := by
    have hnj : (n : ℤ) ≤ j := (Finset.mem_Ico.mp hj).1
    have hjmLt : j < (m : ℤ) := by omega
    have hgoodJ := (hgood.mono_start hnj).goodMaxOnInterval hjmLt.le
    obtain ⟨_Q, _hQ, hrate⟩ := hdecay a delta j (m : ℤ)
      hjmLt hdeltaDec hgoodJ
    have hrateExpanded : finiteAffineGradientExcess a j (m : ℤ) u ≤
        ENNReal.ofReal (Cdec * Real.rpow 3
          (-eta * (((m : ℤ) : ℝ) - (j : ℝ)))) *
          finiteAffineGradientExcess a (m : ℤ) (m : ℤ) u := by
      simpa only [Int.cast_sub] using hrate u
    have hreal := excess_toReal_le_of_rate_fixed a u _
      (mul_nonneg hCdec.le (Real.rpow_nonneg (by norm_num) _)) hrateExpanded
    exact hreal.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCdecA
        (Real.rpow_nonneg (by norm_num) _)) hEm)
  have hEj1 : (finiteAffineGradientExcess a (j + 1) (m : ℤ) u).toReal ≤
      3 * A * Real.rpow 3
        (-eta * (((m : ℤ) : ℝ) - (j : ℝ))) * Em := by
    have hnj : (n : ℤ) ≤ j := (Finset.mem_Ico.mp hj).1
    have hnj1 : (n : ℤ) ≤ j + 1 := by omega
    by_cases hj1mEq : j + 1 = (m : ℤ)
    · rw [hj1mEq]
      have hgap : (((m : ℤ) : ℝ) - (j : ℝ)) = 1 := by
        have hjcast : (j : ℝ) + 1 = ((m : ℤ) : ℝ) := by
          exact_mod_cast hj1mEq
        linarith only [hjcast]
      rw [hgap, mul_one]
      have hthreeRate : 1 ≤ 3 * Real.rpow 3 (-eta) := by
        calc
          1 = Real.rpow 3 0 := by norm_num
          _ ≤ Real.rpow 3 (1 - eta) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
              linarith only [heta1])
          _ = Real.rpow 3 1 * Real.rpow 3 (-eta) := by
            rw [show 1 - eta = 1 + (-eta) by ring]
            exact Real.rpow_add (by norm_num : (0 : ℝ) < 3) _ _
          _ = 3 * Real.rpow 3 (-eta) := by norm_num
      calc
        Em ≤ A * Em := le_mul_of_one_le_left hEm (le_max_left _ _)
        _ ≤ 3 * A * Real.rpow 3 (-eta) * Em := by
          calc
            A * Em = 1 * (A * Em) := by ring
            _ ≤ (3 * Real.rpow 3 (-eta)) * (A * Em) :=
              mul_le_mul_of_nonneg_right hthreeRate (mul_nonneg hA0 hEm)
            _ = _ := by ring
    · have hj1mLt : j + 1 < (m : ℤ) := lt_of_le_of_ne hjm hj1mEq
      have hgoodJ1 := (hgood.mono_start hnj1).goodMaxOnInterval hj1mLt.le
      obtain ⟨_Q, _hQ, hrate⟩ := hdecay a delta (j + 1) (m : ℤ)
        hj1mLt hdeltaDec hgoodJ1
      have hrateExpanded :
          finiteAffineGradientExcess a (j + 1) (m : ℤ) u ≤
            ENNReal.ofReal (Cdec * Real.rpow 3
              (-eta * (((m : ℤ) : ℝ) - (((j + 1 : ℤ) : ℝ))))) *
              finiteAffineGradientExcess a (m : ℤ) (m : ℤ) u := by
        simpa only [Int.cast_sub] using hrate u
      have hreal := excess_toReal_le_of_rate_fixed a u _
        (mul_nonneg hCdec.le (Real.rpow_nonneg (by norm_num) _)) hrateExpanded
      change (finiteAffineGradientExcess a (j + 1) (m : ℤ) u).toReal ≤
        Cdec * Real.rpow 3
          (-eta * (((m : ℤ) : ℝ) - (((j + 1 : ℤ) : ℝ)))) * Em at hreal
      have hfactor : Real.rpow 3
          (-eta * (((m : ℤ) : ℝ) - (((j + 1 : ℤ) : ℝ)))) =
          Real.rpow 3 eta * Real.rpow 3
            (-eta * (((m : ℤ) : ℝ) - (j : ℝ))) := by
        calc
          _ = Real.rpow 3
              (eta + (-eta * (((m : ℤ) : ℝ) - (j : ℝ)))) := by
            congr 1
            push_cast
            ring
          _ = _ := Real.rpow_add (by norm_num : (0 : ℝ) < 3) _ _
      rw [hfactor] at hreal
      have heta3 := rpow_eta_le_three heta1
      calc
        _ ≤ Cdec * (Real.rpow 3 eta *
              Real.rpow 3 (-eta * (((m : ℤ) : ℝ) - (j : ℝ)))) * Em := hreal
        _ = (Cdec * Real.rpow 3 eta) *
              Real.rpow 3 (-eta * (((m : ℤ) : ℝ) - (j : ℝ))) * Em := by ring
        _ ≤ (A * 3) *
              Real.rpow 3 (-eta * (((m : ℤ) : ℝ) - (j : ℝ))) * Em := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul hCdecA heta3
                (Real.rpow_nonneg (by norm_num) _) hA0)
              (Real.rpow_nonneg (by norm_num) _)) hEm
        _ = A * (3 *
              Real.rpow 3 (-eta * (((m : ℤ) : ℝ) - (j : ℝ)))) * Em := by ring
        _ = _ := by ring
  have hsum : (finiteAffineGradientExcess a j (m : ℤ) u).toReal +
        D * (finiteAffineGradientExcess a (j + 1) (m : ℤ) u).toReal ≤
      A * (1 + 3 * D) *
        Real.rpow 3 (-eta * (((m : ℤ) : ℝ) - (j : ℝ))) * Em := by
    have hD : 0 ≤ D := by dsimp only [D]; positivity
    calc
      _ ≤ A * Real.rpow 3
            (-eta * (((m : ℤ) : ℝ) - (j : ℝ))) * Em +
          D * (3 * A * Real.rpow 3
            (-eta * (((m : ℤ) : ℝ) - (j : ℝ))) * Em) :=
        add_le_add hEj (mul_le_mul_of_nonneg_left hEj1 hD)
      _ = _ := by ring
  have hnegSlope : b (j + 1) - b j = -(b j - b (j + 1)) := by abel
  calc
    _ = Real.sqrt (normalizedLocalSymmetricEnergy hEll
        (T (b j - b (j + 1)))) := by
          rw [hnegSlope, map_neg]
          erw [sqrt_normalizedLocalSymmetricEnergy_neg_increment]
    _ = finiteCenteredCubeSolutionEnergy a (m : ℤ)
        (finiteAffineCubeSolution a (m : ℤ) (b j - b (j + 1)))
          (q : ℤ) := finiteTrialGradientLinearMap_energy a hqm _
    _ ≤ Cgrow ^ 2 * Real.rpow 3
        ((((q : ℤ) : ℝ) - (j : ℝ)) / 4) *
        ((finiteAffineGradientExcess a j (m : ℤ) u).toReal +
          D * (finiteAffineGradientExcess a (j + 1) (m : ℤ) u).toReal) := by
      simpa only [D] using henergy
    _ ≤ Cgrow ^ 2 * Real.rpow 3
        ((((q : ℤ) : ℝ) - (j : ℝ)) / 4) *
        (A * (1 + 3 * D) *
          Real.rpow 3 (-eta * (((m : ℤ) : ℝ) - (j : ℝ))) * Em) :=
      mul_le_mul_of_nonneg_left hsum
        (mul_nonneg (sq_nonneg Cgrow) (Real.rpow_nonneg (by norm_num) _))
    _ = B * Real.rpow 3 ((((q : ℤ) : ℝ) - (j : ℝ)) / 4) *
        Real.rpow 3 (-eta * (((m : ℤ) : ℝ) - (j : ℝ))) * Em := by
      dsimp only [B]
      ring

/-- The fixed base minimizer has the same real-rate decay on every
intermediate centered cube. -/
theorem exists_scalarIdentityFiniteAffineFixedBaseDecayConstants
    (d : ℕ) [NeZero d] (s eta : ℝ)
    (hs : 0 < s) (hs_lt : s < 1 / 2)
    (hetaHalf : 1 / 2 ≤ eta) (heta1 : eta < 1) :
    ∃ C c : ℝ, 0 < C ∧ c ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ)
        (n m : ℕ),
        delta ∈ Set.Ioc (0 : ℝ) c →
        ScalarIdentityGoodTail a s delta (n : ℤ) → (hnm2 : n + 2 ≤ m) →
        ∀ u : Book.Ch03.CubeSolution (originCube d (m : ℤ)) a,
          let bBase := finiteAffineExactMinimizer a
            (by exact_mod_cast (show n ≤ m by omega) :
              (n : ℤ) ≤ (m : ℤ)) u
          ∀ q : ℕ, q ∈ Finset.Icc n m →
            weightedGradNorm
                (a.coeffOn (originCube d (q : ℤ))).toCoeffField
                (openCubeSet (originCube d (q : ℤ)))
                (fun x ↦ u.toH1.grad x -
                  (finiteAffineSolution a (m : ℤ) bBase).toH1.grad x) ≤
              ENNReal.ofReal
                  (C * Real.rpow 3 (-eta * ((m - q : ℕ) : ℝ))) *
                finiteAffineGradientExcess a (m : ℤ) (m : ℤ) u := by
  obtain ⟨Cgrow, cgrow, hCgrow, hcgrow, hgrowth⟩ :=
    exists_scalarIdentityFiniteAffineBestFitEnergyGrowthConstants
      d s hs hs_lt
  obtain ⟨_Cfamily, cdec, Cdec, _hCfamily, hcdec, hCdec, hdecay⟩ :=
    exists_scalarIdentityFiniteAffineGradientExcessRealRateDecayConstants
      d s eta hs hs_lt
        (le_trans (by norm_num : (0 : ℝ) ≤ 1 / 2) hetaHalf) heta1
  let D : ℝ := ((3 ^ d : ℕ) : ℝ)
  let A : ℝ := max 1 Cdec
  let B : ℝ := Cgrow ^ 2 * A * (1 + 3 * D)
  let geom : ℝ := 1 / (1 - Real.rpow 3 (-(eta - 1 / 4)))
  let C : ℝ := A + B * geom
  let c : ℝ := min cgrow (min cdec (1 / 2))
  have hcgrow0 : 0 < cgrow := hcgrow.1
  have hc0 : 0 < c := by
    dsimp only [c]
    exact lt_min hcgrow0 (lt_min hcdec (by norm_num))
  have hc1 : c < 1 :=
    (min_le_right cgrow (min cdec (1 / 2))).trans_lt
      ((min_le_right cdec (1 / 2)).trans_lt (by norm_num))
  have hB : 0 < B := by
    have hA : 0 < A := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    dsimp only [B, D]
    exact mul_pos (mul_pos (sq_pos_of_pos (lt_of_lt_of_le zero_lt_one hCgrow))
      hA) (by positivity)
  have hgeom : 0 < geom := by
    have hgap : 0 < eta - 1 / 4 := by linarith only [hetaHalf]
    have hr : Real.rpow 3 (-(eta - 1 / 4)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_lt_zero.mpr hgap)
    exact div_pos zero_lt_one (sub_pos.mpr hr)
  have hC : 0 < C := by
    dsimp only [C]
    exact add_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
      (mul_pos hB hgeom)
  refine ⟨C, c, hC, ⟨hc0, hc1⟩, ?_⟩
  intro a delta n m hdelta hgood hnm2 u
  dsimp only
  let b : ℤ → Vec d := fun j =>
    if hjm : j ≤ (m : ℤ) then finiteAffineExactMinimizer a hjm u else 0
  have hb_at {j : ℤ} (hjm : j ≤ (m : ℤ)) :
      b j = finiteAffineExactMinimizer a hjm u := by
    simp only [b, hjm, dite_true]
  have hdeltaGrow : delta ∈ Set.Ioc (0 : ℝ) cgrow :=
    ⟨hdelta.1, hdelta.2.trans (min_le_left _ _)⟩
  have hdeltaDec : delta ∈ Set.Ioc (0 : ℝ) cdec :=
    ⟨hdelta.1, hdelta.2.trans
      ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hgoodNM : ScalarIdentityGoodMaxOnInterval a s delta
      (n : ℤ) (m : ℤ) := hgood.goodMaxOnInterval (by omega)
  intro q hq
  have hnq : n ≤ q := (Finset.mem_Icc.mp hq).1
  have hqm : q ≤ m := (Finset.mem_Icc.mp hq).2
  let T := finiteTrialGradientLinearMap_field a hqm
  let uQ := finiteCubeSolutionRestriction a
    (show (q : ℤ) ≤ (m : ℤ) by exact_mod_cast hqm) u
  let J : LocalGradientL2 d q := uQ.toH1.gradToHilbertVectorL2
  let hEll := Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
    (originCube d (q : ℤ)) a
  have hvol : 0 < volume (openCubeSet (originCube d (q : ℤ))) :=
    (ENNReal.toReal_pos_iff.mp
      (volume_openCubeSet_originCube_toReal_pos (d := d) (q : ℤ))).1
  have hvoltop : volume (openCubeSet (originCube d (q : ℤ))) ≠ ⊤ :=
    (volume_openCubeSet_lt_top (originCube d (q : ℤ))).ne
  let Em : ℝ := (finiteAffineGradientExcess a (m : ℤ) (m : ℤ) u).toReal
  have hEm : 0 ≤ Em := ENNReal.toReal_nonneg
  have hA0 : 0 ≤ A := (le_max_left (1 : ℝ) Cdec).trans' zero_le_one
  have hCdecA : Cdec ≤ A := le_max_right _ _
  have hmin : Real.sqrt (normalizedLocalSymmetricEnergy hEll
      (J - T (b (q : ℤ)))) ≤
      A * Real.rpow 3 (-eta * (((m : ℤ) : ℝ) - ((q : ℤ) : ℝ))) * Em :=
    finite_trial_minimizer_residual_real_decay s eta cdec Cdec _Cfamily hCdec
      hdecay a hnq hqm hgood hdeltaDec u b hb_at
  have hincrement : ∀ j ∈ Finset.Ico (n : ℤ) (q : ℤ),
      Real.sqrt (normalizedLocalSymmetricEnergy hEll
          (T (b (j + 1) - b j))) ≤
        B * Real.rpow 3 ((((q : ℤ) : ℝ) - (j : ℝ)) / 4) *
          Real.rpow 3 (-eta * (((m : ℤ) : ℝ) - (j : ℝ))) * Em :=
    finite_trial_minimizer_increment_real_decay s eta cgrow Cgrow cdec Cdec _Cfamily
      heta1 hCdec hgrowth hdecay a hnm2 hqm hgood hdeltaDec u b hb_at hdeltaGrow
  have hfixed := sqrt_normalizedEnergy_fixed_realRateDecay_of_incrementRows
    hEll hvol hvoltop T J b
    (show (n : ℤ) ≤ (q : ℤ) by exact_mod_cast hnq)
    (show (q : ℤ) ≤ (m : ℤ) by exact_mod_cast hqm)
    eta A B Em hetaHalf hB.le hEm hmin hincrement
  have hresBase : J - T (b (n : ℤ)) =
      (finiteAffineGradientResidual a
        (show (q : ℤ) ≤ (m : ℤ) by exact_mod_cast hqm) u
        (b (n : ℤ))).toH1.gradToHilbertVectorL2 := by
    simpa only [J, uQ, T] using
      finiteTrialGradientResidual_eq a hqm u (b (n : ℤ))
  have hfixedResidual : Real.sqrt (normalizedLocalSymmetricEnergy hEll
      (finiteAffineGradientResidual a
        (show (q : ℤ) ≤ (m : ℤ) by exact_mod_cast hqm) u
        (b (n : ℤ))).toH1.gradToHilbertVectorL2) ≤
      (A + B * (1 / (1 - Real.rpow 3 (-(eta - 1 / 4))))) *
        Real.rpow 3 (-eta * (((m : ℤ) : ℝ) - ((q : ℤ) : ℝ))) * Em := by
    calc
      _ = Real.sqrt (normalizedLocalSymmetricEnergy hEll
          (J - T (b (n : ℤ)))) := congrArg
            (fun F ↦ Real.sqrt (normalizedLocalSymmetricEnergy hEll F)) hresBase.symm
      _ ≤ _ := hfixed
  erw [sqrt_normalizedEnergy_grad_eq_weightedGradNorm_toReal] at hfixedResidual
  have hfixedCoeff : (weightedGradNorm
      (a.coeffOn (originCube d (q : ℤ))).toCoeffField
      (openCubeSet (originCube d (q : ℤ)))
      (finiteAffineGradientResidual a
        (show (q : ℤ) ≤ (m : ℤ) by exact_mod_cast hqm) u
        (b (n : ℤ))).toH1.grad).toReal ≤
      (A + B * (1 / (1 - Real.rpow 3 (-(eta - 1 / 4))))) *
        Real.rpow 3 (-eta * (((m : ℤ) : ℝ) - ((q : ℤ) : ℝ))) * Em := by
    calc
      _ = (weightedGradNorm
          (Book.Ch03.publicCoeffField (originCube d (q : ℤ)) a)
          (openCubeSet (originCube d (q : ℤ)))
          (finiteAffineGradientResidual a
            (show (q : ℤ) ≤ (m : ℤ) by omega) u
            (b (n : ℤ))).toH1.grad).toReal := congrArg ENNReal.toReal
              (weightedGradNorm_congr_coeff_ae_on _
                (Book.Ch03.publicCoeffField_ae_eq_openCubeSet
                  (originCube d (q : ℤ)) a)).symm
      _ ≤ _ := hfixedResidual
  have hleftNeTop : weightedGradNorm
      (a.coeffOn (originCube d (q : ℤ))).toCoeffField
      (openCubeSet (originCube d (q : ℤ)))
      (finiteAffineGradientResidual a
        (show (q : ℤ) ≤ (m : ℤ) by omega) u
        (b (n : ℤ))).toH1.grad ≠ ∞ := by
    rw [finiteAffineGradientResidual_grad,
      weightedGradNorm_finiteAffineGradientResidual a
        (show (q : ℤ) ≤ (m : ℤ) by omega) u (b (n : ℤ))]
    exact ENNReal.ofReal_ne_top
  have hfieldEq : (fun x ↦ u.toH1.grad x -
        (finiteAffineSolution a (m : ℤ)
          (finiteAffineExactMinimizer a
            (by exact_mod_cast (show n ≤ m by omega) :
              (n : ℤ) ≤ (m : ℤ)) u)).toH1.grad x) =
      (finiteAffineGradientResidual a
        (show (q : ℤ) ≤ (m : ℤ) by omega) u
        (b (n : ℤ))).toH1.grad := by
    funext x
    rw [finiteAffineGradientResidual_grad,
      hb_at (show (n : ℤ) ≤ (m : ℤ) by omega)]
  rw [hfieldEq]
  change weightedGradNorm
      (a.coeffOn (originCube d (q : ℤ))).toCoeffField
      (openCubeSet (originCube d (q : ℤ)))
      (finiteAffineGradientResidual a
        (show (q : ℤ) ≤ (m : ℤ) by omega) u
        (b (n : ℤ))).toH1.grad ≤ _
  apply (ENNReal.toReal_le_toReal hleftNeTop
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (finiteAffineGradientExcess_ne_top_fixed a le_rfl u))).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal]
  · simpa only [C, B, geom, Em, Int.cast_natCast,
      Int.cast_sub, Nat.cast_sub hqm,
      hb_at (show (n : ℤ) ≤ (m : ℤ) by
        exact_mod_cast (show n ≤ m by omega))] using hfixedCoeff
  · exact mul_nonneg hC.le (Real.rpow_nonneg (by norm_num) _)

end

end Root
end HighContrast
end HCPolySupport
