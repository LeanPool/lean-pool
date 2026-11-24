/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.LocalCurrents
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.PositiveDistributionMeasure
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Topology.Algebra.Order.Archimedean

/-!
# Pending local-current calculus and positivity

Mixed distribution derivatives, the coefficient identity `d² = 0`, and the
passage from constant-direction positivity to variable vector squares are
proved below. No global geometry or concurrently written geometry file is
imported.

The coefficient/current wedge-pairing identification is outside this slice;
the conclusion remains a statement about actual distribution-valued forms.
-/

@[expose] public section

noncomputable section

open Set Function MeasureTheory TopologicalSpace
open scoped Distributions CompactlySupported
open SGPT.Foundations.Analysis.LocalCurrents

namespace SGPT.Foundations.Analysis.Pending.LocalCurrents

/-- Mixed distribution derivatives commute by transposing the symmetry of the
second Fréchet derivative of every smooth compactly supported test function. -/
theorem distribution_derivatives_commute
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : Opens E) (T : 𝓓'(Ω, ℝ)) (v w : E) :
    Distribution.lineDerivCLM (n := ⊤) (k := ⊤) v
        (Distribution.lineDerivCLM (n := ⊤) (k := ⊤) w T) =
      Distribution.lineDerivCLM (n := ⊤) (k := ⊤) w
        (Distribution.lineDerivCLM (n := ⊤) (k := ⊤) v T) := by
  ext φ
  simp only [Distribution.lineDerivCLM_apply, neg_neg]
  congr 1
  ext x
  simp only [TestFunction.lineDerivCLM_apply, le_top, ↓reduceIte]
  have hφdiff : Differentiable ℝ (φ : E → ℝ) :=
    φ.contDiff.differentiable (by simp)
  have htest (a : E) :
      (fun y => (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ a φ) y) =
        fun y => fderiv ℝ (φ : E → ℝ) y a := by
    funext y
    rw [TestFunction.lineDerivCLM_apply]
    simp only [le_top, ↓reduceIte]
    exact (hφdiff y).lineDeriv_eq_fderiv
  have horder : (1 : WithTop ℕ∞) + 1 ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) := by
    norm_num
  have hc : DifferentiableAt ℝ (fderiv ℝ (φ : E → ℝ)) x :=
    (φ.contDiff.contDiffAt.fderiv_right horder).differentiableAt one_ne_zero
  have happ (a : E) :
      DifferentiableAt ℝ (fun y => fderiv ℝ (φ : E → ℝ) y a) x :=
    hc.clm_apply (differentiableAt_const a)
  have hcomp (a b : E) :
      fderiv ℝ (fun y => fderiv ℝ (φ : E → ℝ) y a) x b =
        fderiv ℝ (fderiv ℝ (φ : E → ℝ)) x b a := by
    have h := congrArg (fun L : E →L[ℝ] ℝ => L b)
      (fderiv_clm_apply hc (differentiableAt_const a))
    simpa using h
  change lineDeriv ℝ
      (fun y => (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v φ) y) x w =
    lineDeriv ℝ
      (fun y => (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ w φ) y) x v
  rw [htest v, htest w, (happ v).lineDeriv_eq_fderiv,
    (happ w).lineDeriv_eq_fderiv, hcomp v w, hcomp w v]
  apply φ.contDiff.contDiffAt.isSymmSndFDerivAt
  rw [minSmoothness_of_isRCLikeNormedField]
  exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)

/-- Pair the alternating-sum terms using mixed-derivative commutation. This is
the actual coefficient differential, not an abstract operator assumed to
square to zero in a structure. -/
theorem exteriorDerivative_sq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} {k : ℕ} (A : DistributionForm Ω k) :
    exteriorDerivative (exteriorDerivative A) = 0 := by
  let second : E →ₗ[ℝ] E →ₗ[ℝ] DistributionForm Ω k :=
    { toFun := fun v => coefficientDerivative (coefficientDerivative A v)
      map_add' := by
        intro v w
        ext u x φ
        simp [coefficientDerivative, map_add]
      map_smul' := by
        intro c v
        ext u x φ
        simp [coefficientDerivative, map_smul] }
  have hsecond (v w : E) : second v w = second w v := by
    ext x φ
    exact congrArg (fun S : 𝓓'(Ω, ℝ) => S φ)
      (distribution_derivatives_commute Ω (A x) w v)
  have hcoeff : coefficientDerivative (exteriorDerivative A) =
      AlternatingMap.alternatizeUncurryFinLM ∘ₗ second := by
    ext v x φ
    change directionalLM v (exteriorDerivative A x) φ =
      AlternatingMap.alternatizeUncurryFin (second v) x φ
    rw [exteriorDerivative_apply, AlternatingMap.alternatizeUncurryFin_apply, map_sum]
    simp only [sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    simp only [map_zsmul, smul_apply]
    congr 1
    exact congrArg (fun S : 𝓓'(Ω, ℝ) => S φ)
      (distribution_derivatives_commute Ω (A (i.removeNth x)) v (x i))
  rw [exteriorDerivative, hcoeff]
  exact AlternatingMap.alternatizeUncurryFin_alternatizeUncurryFinLM_comp_of_symmetric hsecond

/-- The coefficient identity `d² = 0` gives closedness of `ddᶜT`. -/
theorem ddC_isClosed
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    {Ω : Opens E} (T : 𝓓'(Ω, ℝ)) : IsClosed (ddC T) :=
  exteriorDerivative_sq (dc T)

/-- Commutation of mixed distribution derivatives gives type `(1,1)`. -/
theorem ddC_isOneOne
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    {Ω : Opens E} (T : 𝓓'(Ω, ℝ)) : IsOneOne (ddC T) := by
  intro v w
  have hJ (a : E) : Complex.I • (Complex.I • a) = -a := by
    simp [smul_smul]
  have hneg (a : E) :
      Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (-a) T =
        -Distribution.lineDerivCLM (n := ⊤) (k := ⊤) a T := by
    rw [show -a = (-1 : ℝ) • a by simp, Distribution.lineDerivCLM_smul]
    simp
  rw [ddC_apply, ddC_apply, hJ, hJ, hneg, hneg, map_neg, map_neg,
    distribution_derivatives_commute Ω T (Complex.I • v) w,
    distribution_derivatives_commute Ω T (Complex.I • w) v]
  congr 1
  abel

/-- A real two-form of type `(1,1)` induces a symmetric real bilinear
coefficient pairing after applying the complex structure in the second slot. -/
theorem oneOne_pairing_symmetric
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedSpace ℂ E]
    {Ω : Opens E} (A : DistributionForm Ω 2) (h11 : IsOneOne A) (v w : E) :
    A ![v, Complex.I • w] = A ![w, Complex.I • v] := by
  have hJ : Complex.I • (Complex.I • v) = -v := by
    simp [smul_smul]
  have htype := h11 w (Complex.I • v)
  rw [hJ] at htype
  have hneg : A ![Complex.I • w, -v] = -A ![Complex.I • w, v] := by
    have hleft : ![Complex.I • w, -v] =
        Function.update ![Complex.I • w, 0] 1 (-v) := by
      funext i
      fin_cases i <;> simp
    have hright : ![Complex.I • w, v] =
        Function.update ![Complex.I • w, 0] 1 v := by
      funext i
      fin_cases i <;> simp
    rw [hleft, hright]
    exact A.map_update_neg (v' := ![Complex.I • w, 0]) (i := (1 : Fin 2)) v
  rw [hneg] at htype
  have hswap := A.map_swap (v := ![v, Complex.I • w])
    (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by decide)
  have : A ![Complex.I • w, v] = -A ![v, Complex.I • w] := by
    simpa using hswap
  rw [this, neg_neg] at htype
  exact htype

/-- Positivity in every constant direction gives positivity of every finite
constant quadratic combination of the coefficient distributions. -/
theorem constant_quadratic_positive
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    {Ω : Opens E} (A : DistributionForm Ω 2)
    (hpos : ConstantDirectionPositive A) {r : ℕ}
    (v : Fin r → E) (c : Fin r → ℝ) :
    PositiveDistribution
      (∑ i, ∑ j, (c i * c j) • A ![v i, Complex.I • v j]) := by
  let B : E →ₗ[ℝ] E →ₗ[ℝ] 𝓓'(Ω, ℝ) :=
    { toFun := fun x =>
        { toFun := fun y => A ![x, Complex.I • y]
          map_add' := by
            intro y z
            rw [smul_add]
            have hleft : ![x, Complex.I • y + Complex.I • z] =
                Function.update ![x, 0] 1 (Complex.I • y + Complex.I • z) := by
              funext i
              fin_cases i <;> simp
            have hy : ![x, Complex.I • y] =
                Function.update ![x, 0] 1 (Complex.I • y) := by
              funext i
              fin_cases i <;> simp
            have hz : ![x, Complex.I • z] =
                Function.update ![x, 0] 1 (Complex.I • z) := by
              funext i
              fin_cases i <;> simp
            rw [hleft, hy, hz]
            exact A.map_update_add (v := ![x, 0]) (i := (1 : Fin 2))
              (Complex.I • y) (Complex.I • z)
          map_smul' := by
            intro a y
            rw [smul_comm Complex.I a]
            have hleft : ![x, a • Complex.I • y] =
                Function.update ![x, 0] 1 (a • Complex.I • y) := by
              funext i
              fin_cases i <;> simp
            have hright : ![x, Complex.I • y] =
                Function.update ![x, 0] 1 (Complex.I • y) := by
              funext i
              fin_cases i <;> simp
            rw [hleft, hright]
            exact A.map_update_smul (v := ![x, 0]) (i := (1 : Fin 2)) a
              (Complex.I • y) }
      map_add' := by
        intro x y
        apply LinearMap.ext
        intro z
        change A ![x + y, Complex.I • z] = A ![x, Complex.I • z] +
          A ![y, Complex.I • z]
        have hleft : ![x + y, Complex.I • z] =
            Function.update ![0, Complex.I • z] 0 (x + y) := by
          funext i
          fin_cases i <;> simp
        have hx : ![x, Complex.I • z] =
            Function.update ![0, Complex.I • z] 0 x := by
          funext i
          fin_cases i <;> simp
        have hy : ![y, Complex.I • z] =
            Function.update ![0, Complex.I • z] 0 y := by
          funext i
          fin_cases i <;> simp
        rw [hleft, hx, hy]
        exact A.map_update_add (v := ![0, Complex.I • z]) (i := (0 : Fin 2)) x y
      map_smul' := by
        intro a x
        apply LinearMap.ext
        intro z
        change A ![a • x, Complex.I • z] = a • A ![x, Complex.I • z]
        have hleft : ![a • x, Complex.I • z] =
            Function.update ![0, Complex.I • z] 0 (a • x) := by
          funext i
          fin_cases i <;> simp
        have hright : ![x, Complex.I • z] =
            Function.update ![0, Complex.I • z] 0 x := by
          funext i
          fin_cases i <;> simp
        rw [hleft, hright]
        exact A.map_update_smul (v := ![0, Complex.I • z]) (i := (0 : Fin 2)) a x }
  have h := hpos (∑ i, c i • v i)
  convert h using 1
  change (∑ i, ∑ j, (c i * c j) • B (v i) (v j)) =
    B (∑ i, c i • v i) (∑ i, c i • v i)
  calc
    _ = ∑ j, ∑ i, (c i * c j) • B (v i) (v j) := Finset.sum_comm
    _ = _ := by simp [map_sum, map_smul, Finset.smul_sum, smul_smul, mul_comm]

private theorem locallyIntegrable_rnDeriv_toReal
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [LocallyCompactSpace X]
    (μ ν : Measure X) [IsLocallyFiniteMeasure μ] :
    LocallyIntegrable (fun x => (μ.rnDeriv ν x).toReal) ν := by
  rw [locallyIntegrable_iff]
  intro K hK
  exact Measure.integrableOn_toReal_rnDeriv hK.measure_ne_top

private theorem distributionMatrix_polarization
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} {r : ℕ}
    (S : Fin r → Fin r → 𝓓'(Ω, ℝ)) (hsymm : ∀ i j, S i j = S j i)
    (i j : Fin r) :
    let e : Fin r → Fin r → ℝ := fun i k => if k = i then 1 else 0
    let Q : (Fin r → ℝ) → 𝓓'(Ω, ℝ) := fun c => ∑ i, ∑ j, (c i * c j) • S i j
    S i j = (1 / 4 : ℝ) • (Q (e i + e j) - Q (e i - e j)) := by
  intro e Q
  let p : Fin r → Fin r → Fin r → ℝ := fun i j => e i + e j
  let m : Fin r → Fin r → Fin r → ℝ := fun i j => e i - e j
  change S i j = (1 / 4 : ℝ) • (Q (p i j) - Q (m i j))
  ext φ
  have hdelta (a b : Fin r) :
      (∑ x, ∑ y, e a x * e b y * S x y φ) = S a b φ := by
    simp [e]
  simp only [Q, one_div, smul_apply, sub_apply, smul_eq_mul, _root_.sum_apply]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  have hexpand :
      (∑ x, ∑ y,
        ((p i j x * p i j y) * S x y φ -
          (m i j x * m i j y) * S x y φ)) =
        2 * ((∑ x, ∑ y, e i x * e j y * S x y φ) +
          ∑ x, ∑ y, e j x * e i y * S x y φ) := by
    simp only [p, m, Pi.add_apply, Pi.sub_apply]
    rw [mul_add]
    simp_rw [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    simp_rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [hexpand, hdelta, hdelta, ← congrArg (fun T : 𝓓'(Ω, ℝ) => T φ) (hsymm j i)]
  ring

/-- A finite symmetric matrix of distributions whose every constant real quadratic
combination is positive remains positive when tested against compactly supported
smooth vector-valued functions. The proof uses a common dominating measure for
the polarized coefficient measures and a Radon--Nikodym matrix density. -/
theorem positiveDistributionMatrix_variable_square
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {Ω : Opens E} {r : ℕ}
    (S : Fin r → Fin r → 𝓓'(Ω, ℝ))
    (hsymm : ∀ i j, S i j = S j i)
    (hpos : ∀ c : Fin r → ℝ,
      PositiveDistribution (∑ i, ∑ j, (c i * c j) • S i j))
    (f : Fin r → 𝓓(Ω, ℝ)) :
    0 ≤ ∑ i, ∑ j, S i j (testProduct (f i) (f j)) := by
  classical
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  let : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  let e : Fin r → Fin r → ℝ := fun i k => if k = i then 1 else 0
  let p : Fin r → Fin r → Fin r → ℝ := fun i j => e i + e j
  let m : Fin r → Fin r → Fin r → ℝ := fun i j => e i - e j
  let Q : (Fin r → ℝ) → 𝓓'(Ω, ℝ) :=
    fun c => ∑ i, ∑ j, (c i * c j) • S i j
  have hpolar (i j : Fin r) : S i j = (1 / 4 : ℝ) • (Q (p i j) - Q (m i j)) :=
    distributionMatrix_polarization S hsymm i j
  have hpPos (i j : Fin r) : PositiveDistribution (Q (p i j)) := by
    simpa only [Q] using hpos (p i j)
  have hmPos (i j : Fin r) : PositiveDistribution (Q (m i j)) := by
    simpa only [Q] using hpos (m i j)
  let μp : Fin r → Fin r → Measure Ω := fun i j =>
    Classical.choose (hpPos i j).exists_regular_measure
  let μm : Fin r → Fin r → Measure Ω := fun i j =>
    Classical.choose (hmPos i j).exists_regular_measure
  have hμp (i j : Fin r) :
      (μp i j).Regular ∧ IsLocallyFiniteMeasure (μp i j) ∧
        ∀ φ : 𝓓(Ω, ℝ), (∫ x : Ω, φ x ∂μp i j) = Q (p i j) φ :=
    Classical.choose_spec (hpPos i j).exists_regular_measure
  have hμm (i j : Fin r) :
      (μm i j).Regular ∧ IsLocallyFiniteMeasure (μm i j) ∧
        ∀ φ : 𝓓(Ω, ℝ), (∫ x : Ω, φ x ∂μm i j) = Q (m i j) φ :=
    Classical.choose_spec (hmPos i j).exists_regular_measure
  let μ : (Fin r × Fin r) × Bool → Measure Ω := fun a =>
    if a.2 then μp a.1.1 a.1.2 else μm a.1.1 a.1.2
  let ν : Measure Ω := Measure.sum μ
  let _ : IsLocallyFiniteMeasure ν :=
    Measure.isLocallyFiniteMeasure_sum_finite μ (fun a => by
      rcases a with ⟨⟨i, j⟩, b⟩
      cases b <;> simp only [μ, Bool.false_eq_true, ↓reduceIte]
      · exact (hμm i j).2.1
      · exact (hμp i j).2.1)
  have hμp_le (i j : Fin r) : μp i j ≤ ν := by
    change μp i j ≤ Measure.sum μ
    simpa only [μ, ↓reduceIte] using Measure.le_sum μ ((i, j), true)
  have hμm_le (i j : Fin r) : μm i j ≤ ν := by
    change μm i j ≤ Measure.sum μ
    simpa only [μ, Bool.false_eq_true, ↓reduceIte] using
      Measure.le_sum μ ((i, j), false)
  have hμp_ac (i j : Fin r) : μp i j ≪ ν :=
    Measure.absolutelyContinuous_of_le (hμp_le i j)
  have hμm_ac (i j : Fin r) : μm i j ≪ ν :=
    Measure.absolutelyContinuous_of_le (hμm_le i j)
  let s : Fin r → Fin r → Ω → ℝ := fun i j x =>
    (1 / 4 : ℝ) *
      ((μp i j).rnDeriv ν x).toReal -
      (1 / 4 : ℝ) * ((μm i j).rnDeriv ν x).toReal
  have hs_meas (i j : Fin r) : Measurable (s i j) := by
    exact ((Measure.measurable_rnDeriv _ _).ennreal_toReal.const_mul (1 / 4 : ℝ)).sub
      ((Measure.measurable_rnDeriv _ _).ennreal_toReal.const_mul (1 / 4 : ℝ))
  have hs_loc (i j : Fin r) : LocallyIntegrable (s i j) ν := by
    let : IsLocallyFiniteMeasure (μp i j) := (hμp i j).2.1
    let : IsLocallyFiniteMeasure (μm i j) := (hμm i j).2.1
    have hp := locallyIntegrable_rnDeriv_toReal (μp i j) ν
    have hm := locallyIntegrable_rnDeriv_toReal (μm i j) ν
    exact (hp.smul (1 / 4 : ℝ)).sub (hm.smul (1 / 4 : ℝ))
  have hs_rep (i j : Fin r) (φ : 𝓓(Ω, ℝ)) :
      S i j φ = ∫ x : Ω, φ x * s i j x ∂ν := by
    let gp : C_c(Ω, ℝ) := testFunctionToCompactlySupportedLM Ω φ
    let _ : IsLocallyFiniteMeasure (μp i j) := (hμp i j).2.1
    let _ : IsLocallyFiniteMeasure (μm i j) := (hμm i j).2.1
    have hφp : Integrable (fun x : Ω => φ x) (μp i j) :=
      gp.continuous.integrable_of_hasCompactSupport gp.hasCompactSupport
    have hφm : Integrable (fun x : Ω => φ x) (μm i j) :=
      gp.continuous.integrable_of_hasCompactSupport gp.hasCompactSupport
    have hpint : Integrable
        (fun x : Ω => ((μp i j).rnDeriv ν x).toReal * φ x) ν :=
      (integrable_toReal_rnDeriv_mul_iff (hμp_ac i j)).2 hφp
    have hmint : Integrable
        (fun x : Ω => ((μm i j).rnDeriv ν x).toReal * φ x) ν :=
      (integrable_toReal_rnDeriv_mul_iff (hμm_ac i j)).2 hφm
    calc
      S i j φ = (1 / 4 : ℝ) * (Q (p i j) φ - Q (m i j) φ) := by
        simpa using congrArg (fun T : 𝓓'(Ω, ℝ) => T φ) (hpolar i j)
      _ = (1 / 4 : ℝ) *
          ((∫ x : Ω, φ x ∂μp i j) - ∫ x : Ω, φ x ∂μm i j) := by
        rw [(hμp i j).2.2 φ, (hμm i j).2.2 φ]
      _ = (1 / 4 : ℝ) *
          ((∫ x : Ω, ((μp i j).rnDeriv ν x).toReal * φ x ∂ν) -
            ∫ x : Ω, ((μm i j).rnDeriv ν x).toReal * φ x ∂ν) := by
        rw [integral_toReal_rnDeriv_mul (hμp_ac i j),
          integral_toReal_rnDeriv_mul (hμm_ac i j)]
      _ = ∫ x : Ω, φ x * s i j x ∂ν := by
        rw [← integral_sub hpint hmint, ← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with x
        simp only [s]
        ring
  let q : (Fin r → ℝ) → Ω → ℝ := fun c x =>
    ∑ i, ∑ j, (c i * c j) * s i j x
  have hq_meas (c : Fin r → ℝ) : Measurable (q c) := by
    fun_prop
  have hq_loc (c : Fin r → ℝ) : LocallyIntegrable (q c) ν := by
    apply locallyIntegrable_finsetSum Finset.univ
    intro i _
    apply locallyIntegrable_finsetSum Finset.univ
    intro j _
    have h := (hs_loc i j).smul (c i * c j)
    have heq : (c i * c j) • s i j =
        fun x => (c i * c j) * s i j x := by
      funext x
      simp [smul_eq_mul]
    rw [← heq]
    exact h
  have hq_rep (c : Fin r → ℝ) (φ : 𝓓(Ω, ℝ)) :
      Q c φ = ∫ x : Ω, φ x * q c x ∂ν := by
    let g : C_c(Ω, ℝ) := testFunctionToCompactlySupportedLM Ω φ
    have hint (i j : Fin r) :
        Integrable (fun x : Ω => (c i * c j) * (φ x * s i j x)) ν := by
      have hbase : Integrable (fun x : Ω => φ x * s i j x) ν := by
        simpa [g, smul_eq_mul] using
          (hs_loc i j).integrable_smul_left_of_hasCompactSupport
            g.continuous g.hasCompactSupport
      exact hbase.const_mul _
    calc
      Q c φ = ∑ i, ∑ j, (c i * c j) * S i j φ := by simp [Q]
      _ = ∑ i, ∑ j, (c i * c j) *
          (∫ x : Ω, φ x * s i j x ∂ν) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [hs_rep]
      _ = ∫ x : Ω, φ x * q c x ∂ν := by
        simp_rw [← integral_const_mul]
        have hinner (i : Fin r) :
            (∑ j, ∫ x : Ω, (c i * c j) * (φ x * s i j x) ∂ν) =
              ∫ x : Ω, ∑ j, (c i * c j) * (φ x * s i j x) ∂ν := by
          exact (integral_finsetSum Finset.univ (fun j _ => hint i j)).symm
        simp_rw [hinner]
        rw [← integral_finsetSum]
        · congr 1
          funext x
          simp only [q]
          rw [Finset.mul_sum]
          simp_rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          ring
        · intro i _
          exact integrable_finsetSum Finset.univ (fun j _ => hint i j)
  have hq_nonneg (c : Fin r → ℝ) : ∀ᵐ x ∂ν, 0 ≤ q c x :=
    ae_nonneg_of_positiveDistribution_integral (hpos c) ν (hq_meas c)
      (hq_loc c) (fun φ => hq_rep c φ)
  have hrat : ∀ᵐ x ∂ν, ∀ c : Fin r → ℚ,
      0 ≤ q (fun i => (c i : ℝ)) x :=
    ae_all_iff.2 fun c => hq_nonneg (fun i => (c i : ℝ))
  have hall : ∀ᵐ x ∂ν, ∀ c : Fin r → ℝ, 0 ≤ q c x := by
    filter_upwards [hrat] with x hx
    intro c
    have hdense : DenseRange
        (Pi.map fun _ : Fin r => ((↑) : ℚ → ℝ)) :=
      DenseRange.piMap fun _ => Rat.denseRange_cast
    refine isClosed_property (p := fun a : Fin r → ℝ => 0 ≤ q a x)
      hdense ?_ ?_ c
    · change IsClosed ((fun a : Fin r → ℝ => q a x) ⁻¹' Set.Ici 0)
      apply isClosed_Ici.preimage
      unfold q
      fun_prop
    · intro a
      change 0 ≤ q (fun i => (a i : ℝ)) x
      exact hx a
  have hfinalInt (i j : Fin r) :
      Integrable (fun x : Ω => (f i x * f j x) * s i j x) ν := by
    let gij : C_c(Ω, ℝ) :=
      testFunctionToCompactlySupportedLM Ω (testProduct (f i) (f j))
    simpa [gij, testProduct_apply, smul_eq_mul] using
      (hs_loc i j).integrable_smul_left_of_hasCompactSupport
        gij.continuous gij.hasCompactSupport
  calc
    ∑ i, ∑ j, S i j (testProduct (f i) (f j)) =
        ∑ i, ∑ j, ∫ x : Ω, (f i x * f j x) * s i j x ∂ν := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simpa only [testProduct_apply] using hs_rep i j (testProduct (f i) (f j))
    _ = ∫ x : Ω, q (fun i => f i x) x ∂ν := by
      have hinner (i : Fin r) :
          (∑ j, ∫ x : Ω, (f i x * f j x) * s i j x ∂ν) =
            ∫ x : Ω, ∑ j, (f i x * f j x) * s i j x ∂ν :=
        (integral_finsetSum Finset.univ (fun j _ => hfinalInt i j)).symm
      simp_rw [hinner]
      rw [← integral_finsetSum]
      · intro i _
        exact integrable_finsetSum Finset.univ (fun j _ => hfinalInt i j)
    _ ≥ 0 := integral_nonneg_of_ae (hall.mono fun x hx => hx (fun i => f i x))

/-- Constant-direction positivity upgrades to positivity on compactly
supported smooth vector squares through the finite distribution-matrix
Radon--Nikodym argument above. -/
theorem squarePositive_of_constantDirectionPositive
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
    {Ω : Opens E} (A : DistributionForm Ω 2)
    (h11 : IsOneOne A) (hpos : ConstantDirectionPositive A) :
    SquarePositive A := by
  intro r v f
  exact positiveDistributionMatrix_variable_square
    (fun i j => A ![v i, Complex.I • v j])
    (fun i j => oneOne_pairing_symmetric A h11 (v i) (v j))
    (fun c => constant_quadratic_positive A hpos v c) f

/-- First-pass composition of closedness, type `(1,1)`, and square positivity. -/
theorem ddC_closed_oneOne_squarePositive
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
    {Ω : Opens E} {T : 𝓓'(Ω, ℝ)} (hT : HasNonnegativeDistributionalLevi T) :
    IsClosed (ddC T) ∧ IsOneOne (ddC T) ∧ SquarePositive (ddC T) :=
  ⟨ddC_isClosed T, ddC_isOneOne T,
    squarePositive_of_constantDirectionPositive (ddC T) (ddC_isOneOne T)
      (constantDirectionPositive_ddC hT)⟩

end SGPT.Foundations.Analysis.Pending.LocalCurrents
