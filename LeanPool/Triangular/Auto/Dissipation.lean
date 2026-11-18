/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Claude
-/
module

public import LeanPool.Triangular.Auto.HeatFlow

/-!
# Integrated heat dissipation and averaged trace estimates

Derived from the corresponding part of the upstream triangular Hilbert form proof.

The regularized energy limit adapts `TwoCommuting/Auto/Sec5OutputDependentIntervals.lean`.
Joris Roos’s `lean-twocommuting` revision `33b69ccacc013c703a151421658187ea4d2029fb`
credits these Apache-2.0 Lean proofs to Claude.
-/

@[expose] public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal

open Matrix MeasureTheory Filter Topology Real

namespace Triangular.Auto

noncomputable section

section GaussianPlane

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace HeatData

variable (Hd : HeatData ι)

lemma Gm_eq (β s : ℝ) (p : Fin 3 → ℝ) :
    Gm β 0 s p = gaussian (β * s) (p 0 + p 1 + p 2) := by
  simp [Gm, gaussianD_zero]

end HeatData

end GaussianPlane

section EnergyIntegrability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace HeatData

variable (Hd : HeatData ι) {kk : ι → ℤ}

lemma Jbar_integrable (hh : 0 < Hd.h) {η : ℝ} (hη : 0 < η) {α : Fin 3 → ℝ} (hα1 : ∀ k, 1 ≤ α k)
    (hα2 : ∀ k, α k ≤ 2) {s : ℝ} (hs : 0 < s) :
    Integrable (fun p => Gm (1 / 10) 0 s p * ∑ v, Hd.qE α η v s p) := by
  have e : (fun p => Gm (1 / 10) 0 s p * ∑ v, Hd.qE α η v s p) =
      fun p => ∑ v, Gm (1 / 10) 0 s p * Hd.qE α η v s p := by
    funext p; rw [Finset.mul_sum]
  rw [e]
  refine integrable_finsetSum _ fun v _ => ?_
  exact (Hd.weighted_integrable α η v hh hη hα1 hα2 (by norm_num : (0 : ℝ) < 1 / 10) hs le_rfl
    (.base .energy) 0).1 s ⟨le_rfl, le_rfl⟩

end HeatData

end EnergyIntegrability

section MatrixNorm

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {kk : ι → ℤ}

/-- The entrywise cubic norm with lattice area weight `h²`. -/
def nNorm (h : ℝ) (A : Matrix ι ι ℂ) : ℝ := (h ^ 2 * ∑ i, ∑ j, ‖A i j‖ ^ 3) ^ (1 / 3 : ℝ)

end MatrixNorm

section RegularizationLimit

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma tendsto_sqrt_add_smul {P : Matrix n n ℂ} (hP : P.PosSemidef) {η : ℕ → ℝ}
    (hη0 : ∀ m, 0 ≤ η m) (hη : Tendsto η atTop (𝓝 0)) :
    Tendsto (fun m => CFC.sqrt (P + (η m : ℂ) • 1)) atTop (𝓝 (CFC.sqrt P)) := by
  have converges : Tendsto (fun m => P + (η m : ℂ) • 1) atTop (𝓝 P) := by
    simpa only [Function.comp_apply, Complex.ofReal_zero, zero_smul, add_zero] using
      (tendsto_const_nhds (x := P)).add
        (((Complex.continuous_ofReal.tendsto 0).comp hη).smul_const (1 : Matrix n n ℂ))
  have positive : ∀ m, 0 ≤ P + (η m : ℂ) • (1 : Matrix n n ℂ) := fun m =>
    (hP.add (Matrix.PosSemidef.one.smul (by exact_mod_cast hη0 m))).nonneg
  have within : Tendsto (fun m => P + (η m : ℂ) • 1) atTop (𝓝[Set.Ici 0] P) :=
    tendsto_nhdsWithin_iff.mpr ⟨converges, Eventually.of_forall positive⟩
  exact (CFC.continuousOn_sqrt P hP.nonneg).tendsto.comp within

lemma matCost_le_liminf {P : Matrix n n ℂ} (hP : P.PosSemidef) (K : Matrix n n ℂ) {η : ℕ → ℝ}
    (hη0 : ∀ m, 0 ≤ η m) (hη : Tendsto η atTop (𝓝 0)) :
    matCost P K ≤ liminf (fun m => matCost (P + (η m : ℂ) • 1) K) atTop := by
  refine iSup_le fun X => ?_
  have hc : Continuous fun A : Matrix n n ℂ => costInt A K X := by
    unfold costInt hsRe
    fun_prop
  have hlim : Tendsto (fun m => ENNReal.ofReal ((3 / 2) * costInt (CFC.sqrt (P + (η m : ℂ) • 1))
      K X)) atTop (𝓝 (ENNReal.ofReal ((3 / 2) * costInt (CFC.sqrt P) K X))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp
      ((hc.tendsto _).comp (tendsto_sqrt_add_smul hP hη0 hη) |>.const_mul (3 / 2))
  rw [← hlim.liminf_eq]
  exact liminf_le_liminf (Eventually.of_forall fun m => le_iSup (fun X =>
    ENNReal.ofReal ((3 / 2) * costInt (CFC.sqrt (P + (η m : ℂ) • 1)) K X)) X)

lemma tendsto_energyReg {P : Matrix n n ℂ} (hP : P.IsHermitian) {η : ℕ → ℝ}
    (hη : Tendsto η atTop (𝓝 0)) :
    Tendsto (fun m => energyReg (η m) P) atTop (𝓝 (energyReg 0 P)) := by
  simp only [energyReg, trF_eq_sum _ hP]
  refine tendsto_finsetSum _ fun i _ => ?_
  have hc : Continuous fun e : ℝ => (hP.eigenvalues i + e) ^ (3 / 2 : ℝ) - e ^ (3 / 2 : ℝ) :=
    ((Real.continuous_rpow_const (by norm_num)).comp (continuous_const.add continuous_id)).sub
      (Real.continuous_rpow_const (by norm_num))
  exact (hc.tendsto 0).comp hη

end RegularizationLimit

section EnergyNonnegativity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace HeatData

variable (Hd : HeatData ι)

lemma Jbar_nonneg (α : Fin 3 → ℝ) {η : ℝ} (hη : 0 ≤ η) (s : ℝ) : 0 ≤ Hd.Jbar α η s := by
  refine integral_nonneg fun p => mul_nonneg ?_ (Finset.sum_nonneg fun v _ =>
    (energyReg_bounds (Matrix.posSemidef_conjTranspose_mul_self _) hη).1)
  rw [Gm_eq]; exact gaussian_nonneg' _ _

end HeatData

end EnergyNonnegativity

section IntegratedRegularization

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace HeatData

variable (Hd : HeatData ι)

theorem tendsto_Jbar (hh : 0 < Hd.h) {α : Fin 3 → ℝ} (hα1 : ∀ k, 1 ≤ α k) (hα2 : ∀ k, α k ≤ 2)
    {s : ℝ} (hs : 0 < s) {η : ℕ → ℝ} (hη0 : ∀ m, 0 < η m) (hη1 : ∀ m, η m ≤ 1)
    (hlim : Tendsto η atTop (𝓝 0)) :
    Tendsto (fun m => Hd.Jbar α (η m) s) atTop (𝓝 (Hd.Jbar α 0 s)) := by
  set σ := sig α s
  have hσ : ∀ k, 0 < σ k := fun k => mul_pos (zero_lt_one.trans_le (hα1 k)) hs
  have hσr : ∀ k, σ k ∈ Set.Icc s (2 * s) := fun k => by
    constructor
    · simp only [σ, sig]; nlinarith [hα1 k]
    · simp only [σ, sig]; nlinarith [hα2 k]
  set L : Fin 3 → (Fin 3 → ℝ) → ℝ := fun v p => (Hd.T p σ v).trace.re
  set bnd : (Fin 3 → ℝ) → ℝ := fun p =>
    Gm (1 / 10) 0 s p * ∑ v, 2 * L v p * √(L v p + 1)
  have hTp : ∀ p v, (Hd.T p σ v).PosSemidef := fun p v =>
    Matrix.posSemidef_conjTranspose_mul_self _
  have hL0 : ∀ v p, 0 ≤ L v p := fun v p => re_trace_nonneg_of_posSemidef (hTp p v)
  have hG0 : ∀ p, 0 ≤ Gm (1 / 10) 0 s p := fun p => by rw [Gm_eq]; exact gaussian_nonneg' _ _
  have hbnd : Integrable bnd := by
    obtain ⟨C₀, hC₀, hent⟩ := Hd.entry_bounds hh.le (σa := s) (σb := 2 * s) hs (by linarith)
    obtain ⟨Cg, hCg, hG⟩ := abs_Gm_le 0 (β := 1 / 10) (by norm_num) hs (sb := s)
    set N : ℝ := (Fintype.card (ι ⊕ ι) : ℝ)
    set K := 2 * N * C₀ * √(N * (4 * C₀) + 1)
    have hK : 0 ≤ K := by positivity
    set ε := min (1 / (8 * (2 * s))) (1 / (4 * (1 / 10 * s))) / 4
    have hε : 0 < ε := by positivity
    have hc : Continuous bnd := by
      have cG : Continuous fun p : Fin 3 → ℝ => Gm (1 / 10) 0 s p := by
        have : (fun p : Fin 3 → ℝ => Gm (1 / 10) 0 s p) =
            fun p => gaussian (1 / 10 * s) (p 0 + p 1 + p 2) := by funext p; rw [Gm_eq]
        rw [this]; exact (continuous_gaussian' _).comp (by fun_prop)
      have cL : ∀ v, Continuous (L v) := fun v =>
        continuous_re_trace (Hd.continuous_mats continuous_id continuous_const
          (fun _ => hσ) v).1
      exact cG.mul (continuous_finsetSum _ fun v _ => (continuous_const.mul (cL v)).mul
        (Real.continuous_sqrt.comp ((cL v).add continuous_const)))
    refine integrable_of_le_gdom hc hε (C := Cg * K * 4 * 3) fun p => ?_
    have hφ : ∀ v, L v p ≤ N * (C₀ * phi (2 * s) v p ^ 2) := fun v =>
      re_trace_le_of_entry_le _ fun a b => ((hent p σ hσr v).1 a b).1
    have hφ2 : ∀ v, phi (2 * s) v p ≤ 2 := fun v => phi_le_two (by positivity) v p
    have hterm : ∀ v, 2 * L v p * √(L v p + 1) ≤ K * phi (2 * s) v p ^ 2 := by
      intro v
      have h1 := hφ v
      have hφ0 := phi_nonneg (2 * s) v p
      have h4 : phi (2 * s) v p ^ 2 ≤ 4 := by nlinarith [hφ2 v]
      have hL4 : L v p ≤ N * (4 * C₀) := by
        have : N * (C₀ * phi (2 * s) v p ^ 2) ≤ N * (C₀ * 4) := by gcongr
        linarith
      have hs1 : √(L v p + 1) ≤ √(N * (4 * C₀) + 1) := Real.sqrt_le_sqrt (by linarith)
      calc 2 * L v p * √(L v p + 1) ≤ 2 * (N * (C₀ * phi (2 * s) v p ^ 2)) *
            √(N * (4 * C₀) + 1) := by
            gcongr
        _ = K * phi (2 * s) v p ^ 2 := by simp only [K]; ring
    have hG1 := hG s ⟨le_rfl, le_rfl⟩ p
    rw [abs_of_nonneg (hG0 p)] at hG1
    have hdec : ∀ v, phi (2 * s) v p ^ 2 *
        Real.exp (-(p 0 + p 1 + p 2) ^ 2 / (4 * (1 / 10 * s))) ≤ 4 * gdom ε p := fun v =>
      phi_sq_mul_exp_le (by positivity) (by positivity) v p
    have hsumv : ∑ v, 2 * L v p * √(L v p + 1) ≤ K * ∑ v, phi (2 * s) v p ^ 2 := by
      rw [Finset.mul_sum]; exact Finset.sum_le_sum fun v _ => hterm v
    have hE := Real.exp_pos (-(p 0 + p 1 + p 2) ^ 2 / (4 * (1 / 10 * s)))
    have hnn : 0 ≤ ∑ v, 2 * L v p * √(L v p + 1) := Finset.sum_nonneg fun v _ =>
      mul_nonneg (mul_nonneg zero_le_two (hL0 v p)) (Real.sqrt_nonneg _)
    rw [abs_of_nonneg (mul_nonneg (hG0 p) hnn)]
    calc Gm (1 / 10) 0 s p * ∑ v, 2 * L v p * √(L v p + 1)
        ≤ (Cg * Real.exp (-(p 0 + p 1 + p 2) ^ 2 / (4 * (1 / 10 * s)))) *
            (K * ∑ v, phi (2 * s) v p ^ 2) := mul_le_mul hG1 hsumv hnn (by positivity)
      _ = Cg * K * ∑ v, phi (2 * s) v p ^ 2 *
            Real.exp (-(p 0 + p 1 + p 2) ^ 2 / (4 * (1 / 10 * s))) := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun v _ => by ring
      _ ≤ Cg * K * ∑ _v : Fin 3, 4 * gdom ε p :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun v _ => hdec v) (by positivity)
      _ = Cg * K * 4 * 3 * gdom ε p := by simp; ring
  refine tendsto_integral_of_dominated_convergence bnd
    (fun m => (Hd.Jbar_integrable hh (hη0 m) hα1 hα2 hs).aestronglyMeasurable) hbnd
    (fun m => Eventually.of_forall fun p => ?_) (Eventually.of_forall fun p => ?_)
  · have hnn : 0 ≤ Gm (1 / 10) 0 s p * ∑ v, Hd.qE α (η m) v s p :=
      mul_nonneg (hG0 p) (Finset.sum_nonneg fun v _ =>
        (energyReg_bounds (hTp p v) (hη0 m).le).1)
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun v _ => ?_) (hG0 p)
    have := (energyReg_bounds (hTp p v) (hη0 m).le).2
    refine this.trans ?_
    gcongr
    · exact mul_nonneg zero_le_two (hL0 v p)
    · exact hη1 m
  · refine Tendsto.const_mul _ (tendsto_finsetSum _ fun v _ => ?_)
    exact tendsto_energyReg (hTp p v).1 hlim

end HeatData

end IntegratedRegularization

section CostDensity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace HeatData

variable (Hd : HeatData ι)

/-- The sum of regularized row costs against the Gaussian weight on the center plane. -/
def costDensity (α : Fin 3 → ℝ) (η : ℝ) (z : ℝ × (Fin 3 → ℝ)) : ℝ :=
  Gm (1 / 10) 0 z.1 z.2 * ∑ v, Hd.qV α η v z.1 z.2

lemma costDensity_integrable (hh : 0 < Hd.h) {η : ℝ} (hη : 0 < η) {α : Fin 3 → ℝ}
    (hα1 : ∀ k, 1 ≤ α k) (hα2 : ∀ k, α k ≤ 2) {ta tb : ℝ} (hta : 0 < ta) (hab : ta ≤ tb) :
    Integrable (Hd.costDensity α η) ((volume.restrict (Set.Ioc ta tb)).prod volume) := by
  have e : Hd.costDensity α η = fun z => ∑ v, Gm (1 / 10) 0 z.1 z.2 * Hd.qV α η v z.1 z.2 := by
    funext z; rw [costDensity, Finset.mul_sum]
  rw [e]
  refine integrable_finsetSum _ fun v _ => ?_
  exact (Hd.weighted_integrable α η v hh hη hα1 hα2 (by norm_num : (0 : ℝ) < 1 / 10) hta hab
    (.base .centerCost) 0).2

lemma costDensity_nonneg (α : Fin 3 → ℝ) (η : ℝ) (z : ℝ × (Fin 3 → ℝ)) :
    0 ≤ Hd.costDensity α η z := by
  refine mul_nonneg ?_ (Finset.sum_nonneg fun v _ => ENNReal.toReal_nonneg)
  rw [Gm_eq]; exact gaussian_nonneg' _ _

lemma ofReal_costDensity {η : ℝ} (hη : 0 < η) (α : Fin 3 → ℝ) (z : ℝ × (Fin 3 → ℝ)) :
    ENNReal.ofReal (Hd.costDensity α η z) = ENNReal.ofReal (Gm (1 / 10) 0 z.1 z.2) * ∑ v,
      matCost (Hd.T z.2 (sig α z.1) v + (η : ℂ) • 1) (Hd.Ui z.2 (sig α z.1) v) := by
  have hG : 0 ≤ Gm (1 / 10) 0 z.1 z.2 := by rw [Gm_eq]; exact gaussian_nonneg' _ _
  simp only [costDensity, qV, vertexValue, V]
  rw [ENNReal.ofReal_mul hG, ENNReal.ofReal_sum_of_nonneg
    (fun v _ => ENNReal.toReal_nonneg)]
  congr 1
  refine Finset.sum_congr rfl fun v _ => ?_
  exact ENNReal.ofReal_toReal (matCost_ne_top (posDef_add_smul_one
    (Matrix.posSemidef_conjTranspose_mul_self _) hη) _)

lemma integral_Vbar_eq (hh : 0 < Hd.h) {η : ℝ} (hη : 0 < η) {α : Fin 3 → ℝ} (hα1 : ∀ k, 1 ≤ α k)
    (hα2 : ∀ k, α k ≤ 2) {ta tb : ℝ} (hta : 0 < ta) (hab : ta ≤ tb) :
    ∫ s in ta..tb, ∑ v, Hd.Vbar α η v s = ∫ z, Hd.costDensity α η z ∂((volume.restrict (Set.Ioc
      ta tb)).prod volume) := by
  rw [intervalIntegral.integral_of_le hab,
    integral_prod _ (Hd.costDensity_integrable hh hη hα1 hα2 hta hab)]
  refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
  have hs0 : 0 < s := hta.trans hs.1
  simp only [costDensity, Vbar]
  rw [← integral_finsetSum]
  · congr 1; funext p; rw [Finset.mul_sum]
  · intro v _
    exact (Hd.weighted_integrable α η v hh hη hα1 hα2 (by norm_num : (0 : ℝ) < 1 / 10) hta hab
      (.base .centerCost) 0).1 s ⟨hs.1.le, hs.2⟩

lemma ofReal_integral_Vbar (hh : 0 < Hd.h) {η : ℝ} (hη : 0 < η) {α : Fin 3 → ℝ}
    (hα1 : ∀ k, 1 ≤ α k) (hα2 : ∀ k, α k ≤ 2) {ta tb : ℝ} (hta : 0 < ta) (hab : ta ≤ tb) :
    ENNReal.ofReal (∫ s in ta..tb, ∑ v, Hd.Vbar α η v s) = ∫⁻ z, ENNReal.ofReal (Gm (1 / 10) 0
      z.1 z.2) * ∑ v, matCost (Hd.T z.2 (sig α z.1) v + (η : ℂ) • 1) (Hd.Ui z.2 (sig α z.1) v)
      ∂((volume.restrict (Set.Ioc ta tb)).prod volume) := by
  rw [Hd.integral_Vbar_eq hh hη hα1 hα2 hta hab, ofReal_integral_eq_lintegral_ofReal
    (Hd.costDensity_integrable hh hη hα1 hα2 hta hab)
    (Eventually.of_forall (Hd.costDensity_nonneg α η))]
  exact lintegral_congr fun z => Hd.ofReal_costDensity hη α z

end HeatData

end CostDensity

section GaussianComparison

lemma poly_exp_bound (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y : ℝ, (1 + |y|) ^ d * Real.exp (-ε * y ^ 2) ≤ B := by
  set K := max 1 (√(2 * ε))⁻¹
  have hK : 1 ≤ K := le_max_left _ _
  have hs : 0 < √(2 * ε) := Real.sqrt_pos.2 (by positivity)
  refine ⟨K ^ d * (d.factorial * Real.exp 2), by positivity, fun y => ?_⟩
  set z := √(2 * ε) * y
  have hzy : 1 + |y| ≤ K * (1 + |z|) := by
    have : |y| = (√(2 * ε))⁻¹ * |z| := by
      rw [abs_mul, abs_of_pos hs, ← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul]
    rw [this]
    have h1 : (√(2 * ε))⁻¹ ≤ K := le_max_right _ _
    nlinarith [abs_nonneg z]
  have hez : Real.exp (-ε * y ^ 2) = gaussProfile z := by
    unfold gaussProfile; congr 1
    simp only [z]; rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
  rw [hez]
  calc (1 + |y|) ^ d * gaussProfile z ≤ (K * (1 + |z|)) ^ d * gaussProfile z :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hzy d)
          (gaussProfile_pos z).le
    _ = K ^ d * ((1 + |z|) ^ d * gaussProfile z) := by rw [mul_pow]; ring
    _ ≤ K ^ d * (d.factorial * Real.exp 2 * Real.exp (-(z ^ 2) / 4)) :=
        mul_le_mul_of_nonneg_left (one_add_abs_pow_mul_gaussProfile_le d z) (by positivity)
    _ ≤ K ^ d * (d.factorial * Real.exp 2 * 1) := by
        gcongr; rw [Real.exp_le_one_iff]; have := sq_nonneg z; linarith
    _ = _ := by ring

theorem gaussianD_ratio_le (d : ℕ) {q l : ℝ} (hq : 0 < q) (hql : q < l) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 < s → ∀ x : ℝ, √s ^ d * |gaussianD d (q * s) x| ≤ C * gaussian
      (l * s) x := by
  have hl : 0 < l := hq.trans hql
  obtain ⟨C0, hC0, hprof⟩ := abs_gaussProfileD_le d
  set ε := (1 - q / l) / 2
  have hε : 0 < ε := by
    have : q / l < 1 := (div_lt_one hl).2 hql
    simp only [ε]; linarith
  obtain ⟨B, hB0, hB⟩ := poly_exp_bound d hε
  have hsq : 0 < √q := Real.sqrt_pos.2 hq
  have hsl : 0 < √l := Real.sqrt_pos.2 hl
  refine ⟨(√q)⁻¹ ^ (d + 1) * C0 * B * √l, by positivity, fun s hs x => ?_⟩
  have hss : 0 < √s := Real.sqrt_pos.2 hs
  have h2π : 0 < √(2 * π) := Real.sqrt_pos.2 (by positivity)
  set y := (√(q * s))⁻¹ * x
  have hqs : √(q * s) = √q * √s := Real.sqrt_mul hq.le s
  rw [gaussianD_eq_profile d (by positivity), abs_mul, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < (√(2 * π))⁻¹),
    abs_of_pos (by positivity : (0 : ℝ) < (√(q * s))⁻¹ ^ (d + 1))]
  have hp := hprof y
  have hφ : gaussProfile y = Real.exp (-(q / l) * y ^ 2 / 2) * Real.exp (-ε * y ^ 2) := by
    unfold gaussProfile; rw [← Real.exp_add]; congr 1; simp only [ε]; ring
  have hx : Real.exp (-(x ^ 2) / (2 * (l * s))) = Real.exp (-(q / l) * y ^ 2 / 2) := by
    congr 1
    simp only [y]
    rw [mul_pow, inv_pow, Real.sq_sqrt (by positivity)]
    field_simp
  have hg : gaussian (l * s) x = (√(2 * π))⁻¹ * (√l)⁻¹ * (√s)⁻¹ *
      Real.exp (-(q / l) * y ^ 2 / 2) := by
    unfold gaussian
    rw [hx, show 2 * π * (l * s) = (2 * π) * l * s by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_mul (by positivity)]
    rw [mul_inv, mul_inv]
  have hpow : √s ^ d * (√(q * s))⁻¹ ^ (d + 1) = (√q)⁻¹ ^ (d + 1) * (√s)⁻¹ := by
    rw [hqs, mul_inv, mul_pow, pow_succ (√s)⁻¹, inv_pow (√s) d]
    field_simp
  have hE := Real.exp_pos (-(q / l) * y ^ 2 / 2)
  calc √s ^ d * ((√(2 * π))⁻¹ * (√(q * s))⁻¹ ^ (d + 1) * |gaussProfileD d y|)
      = (√(2 * π))⁻¹ * (√s ^ d * (√(q * s))⁻¹ ^ (d + 1)) * |gaussProfileD d y| := by ring
    _ ≤ (√(2 * π))⁻¹ * (√s ^ d * (√(q * s))⁻¹ ^ (d + 1)) *
          (C0 * (1 + |y|) ^ d * gaussProfile y) := by gcongr
    _ = (√(2 * π))⁻¹ * ((√q)⁻¹ ^ (d + 1) * (√s)⁻¹) * C0 *
          ((1 + |y|) ^ d * Real.exp (-ε * y ^ 2)) * Real.exp (-(q / l) * y ^ 2 / 2) := by
        rw [hpow, hφ]; ring
    _ ≤ (√(2 * π))⁻¹ * ((√q)⁻¹ ^ (d + 1) * (√s)⁻¹) * C0 * B *
          Real.exp (-(q / l) * y ^ 2 / 2) := by gcongr; exact hB y
    _ = (√q)⁻¹ ^ (d + 1) * C0 * B * √l * gaussian (l * s) x := by rw [hg]; field_simp

end GaussianComparison

section TraceExpansion

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma trace_mul_three (X Y Z : Matrix ι ι ℂ) :
    (X * Y * Z).trace = ∑ i, ∑ j, ∑ k, X i j * Y j k * Z k i := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm]

lemma trace_cyclic_diag (x₀ x₁ x₂ r₀ r₁ r₂ : ι → ℝ) (B₀ B₁ B₂ : Matrix ι ι ℂ) :
    (rdiag x₀ * (rdiag r₀ * B₀ * rdiag r₁) * rdiag x₁ * (rdiag r₁ * B₁ * rdiag r₂) * rdiag x₂ *
      (rdiag r₂ * B₂ * rdiag r₀)).trace = ∑ i, ∑ j, ∑ k, B₀ i j * B₁ j k * B₂ k i * ((x₀ i * r₀ i
      ^ 2 : ℝ) * (x₁ j * r₁ j ^ 2 : ℝ) * (x₂ k * r₂ k ^ 2 : ℝ) : ℝ) := by
  have e : rdiag x₀ * (rdiag r₀ * B₀ * rdiag r₁) * rdiag x₁ * (rdiag r₁ * B₁ * rdiag r₂) *
      rdiag x₂ * (rdiag r₂ * B₂ * rdiag r₀) =
      (rdiag x₀ * (rdiag r₀ * B₀ * rdiag r₁)) * (rdiag x₁ * (rdiag r₁ * B₁ * rdiag r₂)) *
        (rdiag x₂ * (rdiag r₂ * B₂ * rdiag r₀)) := by
    simp only [Matrix.mul_assoc]
  rw [e, trace_mul_three]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => ?_
  simp only [rdiag, Matrix.diagonal_mul, Matrix.mul_diagonal]
  push_cast; ring

/-- The point with first coordinates `q 0`, `q 1` on the plane whose coordinates sum to zero. -/
def planePt (q : Fin 2 → ℝ) : Fin 3 → ℝ := ![q 0, q 1, -q 0 - q 1]

lemma integrable_fin2_prod {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g) :
    Integrable (fun q : Fin 2 → ℝ => f (q 0) * g (q 1)) := by
  have := Integrable.fintype_prod (f := ![f, g]) (μ := fun _ : Fin 2 => (volume : Measure ℝ))
    (fun i => by fin_cases i; exacts [hf, hg])
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at this
  exact this

theorem plane_gaussD_three (d₀ d₁ d₂ : ℕ) {σ : ℝ} (hσ : 0 < σ) (c₀ c₁ c₂ : ℝ) :
    Integrable (fun q : Fin 2 → ℝ => ((gaussianD d₀ σ (c₀ - q 0) * gaussianD d₁ σ (c₁ - q 1) *
      gaussianD d₂ σ (c₂ + q 0 + q 1) : ℝ) : ℂ)) ∧ ∫ q : Fin 2 → ℝ, ((gaussianD d₀ σ (c₀ - q 0) *
      gaussianD d₁ σ (c₁ - q 1) * gaussianD d₂ σ (c₂ + q 0 + q 1) : ℝ) : ℂ) = (gaussianD (d₂ + d₁
      + d₀) (σ + σ + σ) (c₀ + c₁ + c₂) : ℂ) := by
  obtain ⟨M, hM⟩ := abs_gaussianD_le_const d₂ hσ
  have h0 : Integrable (fun x => gaussianD d₀ σ (c₀ - x)) :=
    (integrable_gaussianD d₀ hσ).comp_sub_left c₀
  have h1 : Integrable (fun x => gaussianD d₁ σ (c₁ - x)) :=
    (integrable_gaussianD d₁ hσ).comp_sub_left c₁
  have hcont : Continuous (fun q : Fin 2 → ℝ => gaussianD d₀ σ (c₀ - q 0) *
      gaussianD d₁ σ (c₁ - q 1) * gaussianD d₂ σ (c₂ + q 0 + q 1)) := by
    have := continuous_gaussianD d₀ σ
    have := continuous_gaussianD d₁ σ
    have := continuous_gaussianD d₂ σ
    fun_prop
  have hI : Integrable (fun q : Fin 2 → ℝ => gaussianD d₀ σ (c₀ - q 0) *
      gaussianD d₁ σ (c₁ - q 1) * gaussianD d₂ σ (c₂ + q 0 + q 1)) := by
    refine ((integrable_fin2_prod h0 h1).norm.const_mul M).mono' hcont.aestronglyMeasurable
      (Eventually.of_forall fun q => ?_)
    rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs, abs_mul]
    have := hM (c₂ + q 0 + q 1)
    have := abs_nonneg (gaussianD d₀ σ (c₀ - q 0))
    have := abs_nonneg (gaussianD d₁ σ (c₁ - q 1))
    nlinarith [mul_nonneg (abs_nonneg (gaussianD d₀ σ (c₀ - q 0)))
      (abs_nonneg (gaussianD d₁ σ (c₁ - q 1)))]
  refine ⟨hI.ofReal, ?_⟩
  rw [integral_complex_ofReal]
  congr 1
  have hfin : ∫ q : Fin 2 → ℝ, gaussianD d₀ σ (c₀ - q 0) * gaussianD d₁ σ (c₁ - q 1) *
      gaussianD d₂ σ (c₂ + q 0 + q 1) = ∫ x, ∫ y, gaussianD d₀ σ (c₀ - x) *
        gaussianD d₁ σ (c₁ - y) * gaussianD d₂ σ (c₂ + x + y) := by
    have h2 := (volume_preserving_finTwoArrow ℝ).symm
    rw [← h2.integral_comp' (g := fun q : Fin 2 → ℝ => gaussianD d₀ σ (c₀ - q 0) *
      gaussianD d₁ σ (c₁ - q 1) * gaussianD d₂ σ (c₂ + q 0 + q 1)), Measure.volume_eq_prod,
      integral_prod]
    · rfl
    · exact (h2.integrable_comp_emb MeasurableEquiv.finTwoArrow.symm.measurableEmbedding).2 hI
  rw [hfin]
  have inner : ∀ x, ∫ y, gaussianD d₀ σ (c₀ - x) * gaussianD d₁ σ (c₁ - y) *
      gaussianD d₂ σ (c₂ + x + y) =
      gaussianD d₀ σ (c₀ - x) * gaussianD (d₂ + d₁) (σ + σ) (c₂ + x + c₁) := by
    intro x
    rw [← gaussianD_conv_gaussianD d₂ d₁ hσ hσ, ← integral_const_mul]
    rw [← integral_sub_left_eq_self (fun d => gaussianD d₀ σ (c₀ - x) *
      (gaussianD d₂ σ (c₂ + x + c₁ - d) * gaussianD d₁ σ d)) volume c₁]
    congr 1; funext y
    rw [show c₂ + x + c₁ - (c₁ - y) = c₂ + x + y by ring]; ring
  simp_rw [inner]
  rw [← gaussianD_conv_gaussianD (d₂ + d₁) d₀ (by positivity : 0 < σ + σ) hσ,
    ← integral_sub_left_eq_self (fun d => gaussianD (d₂ + d₁) (σ + σ) (c₀ + c₁ + c₂ - d) *
      gaussianD d₀ σ d) volume c₀]
  congr 1; funext x
  rw [show c₀ + c₁ + c₂ - (c₀ - x) = c₂ + x + c₁ by ring]; ring

end TraceExpansion

section VertexDerivatives

/-- The derivative order at each vertex for the third- or fourth-order Gaussian kernel. -/
def dexp (m : ℕ) (v : Fin 3) : ℕ := if v = 0 ∧ m = 4 then 2 else 1

lemma dexp_sum {m : ℕ} (hm : m = 3 ∨ m = 4) :
    dexp m 2 + dexp m 1 + dexp m 0 = m := by
  rcases hm with rfl | rfl <;> simp [dexp]

/-- A scaled Gaussian derivative expressed as a multiplier of a wider Gaussian. -/
def Dfun (d : ℕ) (s x : ℝ) : ℝ :=
  √s ^ d * gaussianD d (21 / 20 * s) x / gaussian (11 / 10 * s) x

/-- The coefficient for expressing a Gaussian derivative by averaging shifted centers. -/
def acoef (j : ℕ) (s d : ℝ) : ℝ :=
  -(√s ^ j * gaussianD (j - 1) (1 / 20 * s) d / gaussian (1 / 10 * s) d)

lemma gaussian_pos {σ : ℝ} (hσ : 0 < σ) (t : ℝ) : 0 < gaussian σ t := by
  unfold gaussian
  have : 0 < √(2 * π * σ) := Real.sqrt_pos.2 (by positivity)
  positivity

lemma Dfun_bound (d : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ s, 0 < s → ∀ x, |Dfun d s x| ≤ C := by
  obtain ⟨C, hC, h⟩ := gaussianD_ratio_le d (q := 21 / 20) (l := 11 / 10) (by norm_num)
    (by norm_num)
  refine ⟨C, hC, fun s hs x => ?_⟩
  have hg := gaussian_pos (by positivity : (0 : ℝ) < 11 / 10 * s) x
  rw [Dfun, abs_div, abs_of_pos hg, abs_mul, abs_of_nonneg (pow_nonneg (Real.sqrt_nonneg _) _),
    div_le_iff₀ hg]
  exact h s hs x

lemma acoef_bound (j : ℕ) (hj : 1 ≤ j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s, 0 < s → ∀ d, |acoef j s d| ≤ C * √s := by
  obtain ⟨C, hC, h⟩ := gaussianD_ratio_le (j - 1) (q := 1 / 20) (l := 1 / 10) (by norm_num)
    (by norm_num)
  refine ⟨C, hC, fun s hs d => ?_⟩
  have hg := gaussian_pos (by positivity : (0 : ℝ) < 1 / 10 * s) d
  rw [acoef, abs_neg, abs_div, abs_of_pos hg, abs_mul,
    abs_of_nonneg (pow_nonneg (Real.sqrt_nonneg _) _), div_le_iff₀ hg]
  have hj' : j = (j - 1) + 1 := by omega
  rw [hj', pow_succ]
  have := h s hs d
  have hs' := Real.sqrt_nonneg s
  calc √s ^ (j - 1) * √s * |gaussianD (j - 1 + 1 - 1) (1 / 20 * s) d|
      = √s * (√s ^ (j - 1) * |gaussianD (j - 1) (1 / 20 * s) d|) := by
        rw [show j - 1 + 1 - 1 = j - 1 by omega]; ring
    _ ≤ √s * (C * gaussian (1 / 10 * s) d) := mul_le_mul_of_nonneg_left this hs'
    _ = _ := by ring

end VertexDerivatives

section GaussianAverages

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Gaussian measure of variance `s / 10` used to average center shifts. -/
def avgMeasure (s : ℝ) : Measure ℝ :=
  volume.withDensity fun d => ((gaussian (1 / 10 * s) d).toNNReal : ℝ≥0∞)

lemma measurable_gaussian_toNNReal (τ : ℝ) : Measurable fun d => (gaussian τ d).toNNReal :=
  (continuous_gaussian' τ).measurable.real_toNNReal

instance avgMeasure_prob {s : ℝ} [Fact (0 < s)] : IsProbabilityMeasure (avgMeasure s) := by
  have hs : 0 < s := Fact.out
  constructor
  rw [avgMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have : ∫⁻ d, ((gaussian (1 / 10 * s) d).toNNReal : ℝ≥0∞) =
      ENNReal.ofReal (∫ d, gaussian (1 / 10 * s) d) := by
    rw [ofReal_integral_eq_lintegral_ofReal (integrable_gaussian' (by positivity))
      (Eventually.of_forall fun d => gaussian_nonneg' _ _)]
    rfl
  rw [this, integral_gaussian_eq_one (by positivity), ENNReal.ofReal_one]

lemma lintegral_avgMeasure (s : ℝ) (F : ℝ → ℝ≥0∞) :
    ∫⁻ d, F d ∂(avgMeasure s) = ∫⁻ d, ENNReal.ofReal (gaussian (1 / 10 * s) d) * F d := by
  rw [avgMeasure, lintegral_withDensity_eq_lintegral_mul_non_measurable _
    (measurable_gaussian_toNNReal _).coe_nnreal_ennreal
    (Eventually.of_forall fun d => ENNReal.coe_lt_top)]
  rfl

lemma matCost_smul_le {n : Type*} [Fintype n] [DecidableEq n] (P K : Matrix n n ℂ) (c : ℝ) :
    matCost P ((c : ℂ) • K) ≤ ENNReal.ofReal (c ^ 2) * matCost P K := by
  by_cases hc : c = 0
  · subst hc
    simp only [Complex.ofReal_zero, zero_smul]
    refine le_trans (iSup_le fun X => ?_) (zero_le (a := ENNReal.ofReal (0 ^ 2) * matCost P K))
    refine (ENNReal.ofReal_eq_zero.2 ?_).le
    have hA : (CFC.sqrt P - ((0 : ℝ) : ℂ) • (1 : Matrix n n ℂ)).PosSemidef := by
      simpa using (CFC.sqrt_nonneg P).posSemidef
    have h := sylvester_lower hA hA X
    rw [hsRe_add_right] at h
    simp only [costInt, hsRe, Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.trace_zero,
      Complex.zero_re, mul_zero, zero_sub] at h ⊢
    nlinarith [hsSq_nonneg X]
  · have e : (c : ℂ) • K = c • K := by ext i j; simp [Complex.real_smul]
    rw [e, matCost_smul P K hc]

end GaussianAverages

section WeightedCostComparison

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma integral_avgMeasure_real (s : ℝ) (f : ℝ → ℝ) :
    ∫ d, f d ∂(avgMeasure s) = ∫ d, gaussian (1 / 10 * s) d * f d := by
  rw [avgMeasure, integral_withDensity_eq_integral_smul (measurable_gaussian_toNNReal _)]
  refine integral_congr_ae (Eventually.of_forall fun d => ?_)
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (gaussian_nonneg' _ _), smul_eq_mul]

lemma integrable_avgMeasure_real (s : ℝ) {f : ℝ → ℝ}
    (hf : Integrable (fun d => gaussian (1 / 10 * s) d * f d)) :
    Integrable f (avgMeasure s) := by
  rw [avgMeasure, integrable_withDensity_iff_integrable_smul (measurable_gaussian_toNNReal _)]
  refine hf.congr (Eventually.of_forall fun d => ?_)
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (gaussian_nonneg' _ _), smul_eq_mul]

lemma matIntegral_wGram {κ : Type*} {ν : Measure ℝ} (B : Matrix ι κ ℂ) (f : ℝ → ι → ℝ)
    (hf : ∀ i, Integrable (fun d => f d i) ν) :
    (∀ a b, Integrable (fun d => wGram B (f d) a b) ν) ∧ matIntegral ν (fun d => wGram B (f d))
      = wGram B (fun i => ∫ d, f d i ∂ν) := by
  have hc : ∀ a b i, Integrable (fun d => star (B i a) * (f d i : ℂ) * B i b) ν := fun a b i =>
    (((hf i).ofReal).const_mul (star (B i a))).mul_const (B i b)
  refine ⟨fun a b => ?_, ?_⟩
  · simp_rw [wGram_apply]
    exact integrable_finsetSum _ fun i _ => hc a b i
  · ext a b
    rw [matIntegral_apply, wGram_apply]
    simp_rw [wGram_apply]
    rw [integral_finsetSum _ fun i _ => hc a b i]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_mul_const, integral_const_mul, integral_complex_ofReal]

namespace HeatData

variable (Hd : HeatData ι)

omit [Fintype ι] [DecidableEq ι] in
lemma w_update2 (p σ : Fin 3 → ℝ) (v : Fin 3) (q τ : ℝ) :
    Hd.w (Function.update p v q) (Function.update σ v τ) v = gweight Hd.u Hd.h τ q := by
  simp [w]

lemma Brow_update2 (p σ : Fin 3 → ℝ) (v : Fin 3) (q τ : ℝ) :
    Hd.Brow (Function.update p v q) (Function.update σ v τ) v = Hd.Brow p σ v := by
  rw [Brow_update, Brow_update_σ]

omit [Fintype ι] [DecidableEq ι] in
lemma dw_update2 (p σ : Fin 3 → ℝ) (v : Fin 3) (q τ : ℝ) :
    Hd.dw (Function.update p v q) (Function.update σ v τ) v = fun i => -(Hd.h * gaussianD 1 τ
      (Hd.u i - q)) := by
  rw [dw_def]; simp

lemma R_insert_eq (hh : 0 ≤ Hd.h) (p σ : Fin 3 → ℝ) (v : Fin 3) (D : ι → ℝ) :
    (Hd.R p σ v)ᴴ * rdiag D * Hd.R p σ v = wGram (Hd.Brow p σ v) (fun i => Hd.w p σ v i * D i) := by
  rw [R_eq, wGram, Brow]
  have hw : (fun i => Hd.w p σ v i * D i) = Hd.sqw p σ v * D * Hd.sqw p σ v := by
    funext i
    simp only [Pi.mul_apply]
    rw [← Hd.sq_mul_sq p σ hh]; simp only [Pi.mul_apply]; ring
  rw [hw, ← rdiag_mul_rdiag, ← rdiag_mul_rdiag]
  simp only [Matrix.conjTranspose_mul, rdiag_conjTranspose, Matrix.mul_assoc]

theorem vertex_avg (hh : 0 < Hd.h) (v : Fin 3) {j : ℕ} (hj : 1 ≤ j) {Ca : ℝ}
    (hCa : ∀ s, 0 < s → ∀ d, |acoef j s d| ≤ Ca * √s) (p : Fin 3 → ℝ) {s : ℝ} (hs : 0 < s) :
    matCost (Hd.T p (fun _ => 11 / 10 * s) v) ((Hd.R p (fun _ => 11 / 10 * s) v)ᴴ * rdiag (fun i
      => Dfun j s (Hd.u i - p v)) * Hd.R p (fun _ => 11 / 10 * s) v) ≤ ENNReal.ofReal (Ca ^ 2 * s)
      * ∫⁻ d, ENNReal.ofReal (gaussian (1 / 10 * s) d) * matCost (Hd.T (Function.update p v (p v +
      d)) (Function.update (fun _ => 11 / 10 * s) v s) v) (Hd.Ui (Function.update p v (p v + d))
      (Function.update (fun _ => 11 / 10 * s) v s) v) := by
  have : Fact (0 < s) := ⟨hs⟩
  set σB : Fin 3 → ℝ := fun _ => 11 / 10 * s
  set σV := Function.update σB v s
  set Bw := Hd.Brow p σB v
  set ν := avgMeasure s
  have hβ : (0 : ℝ) < 1 / 10 * s := by positivity
  set fT : ℝ → ι → ℝ := fun d i => gweight Hd.u Hd.h s (p v + d) i
  set fK : ℝ → ι → ℝ := fun d i => acoef j s d * -(Hd.h * gaussianD 1 s (Hd.u i - (p v + d)))
  have hT : ∀ d, Hd.T (Function.update p v (p v + d)) σV v = wGram Bw (fT d) := fun d => by
    rw [T_eq_wGram Hd _ _ hh.le, Brow_update2, w_update2]
  have hK : ∀ d, ((acoef j s d : ℝ) : ℂ) • Hd.Ui (Function.update p v (p v + d)) σV v =
      wGram Bw (fK d) := fun d => by
    rw [Ui, Brow_update2, dw_update2, ← wGram_smul]
    congr 1
  have hfT : ∀ i, Integrable (fun d => fT d i) ν := by
    intro i
    refine integrable_avgMeasure_real s ?_
    exact (integrable_gaussian' hβ).mul_bdd (c := Hd.h * (√(2 * π * s))⁻¹)
      ((continuous_const.mul ((continuous_gaussian' s).comp
        (continuous_const.sub (continuous_const.add continuous_id)))).aestronglyMeasurable)
      (Eventually.of_forall fun d => by
        rw [Real.norm_eq_abs, abs_of_nonneg (gweight_nonneg _ hh.le _ _ _)]
        exact mul_le_mul_of_nonneg_left (gaussian_le_sup _ _) hh.le)
  have hgK : ∀ d, gaussian (1 / 10 * s) d * acoef j s d =
      -(√s ^ j * gaussianD (j - 1) (1 / 20 * s) d) := fun d => by
    have hne := (gaussian_pos hβ d).ne'
    simp only [acoef]
    rw [mul_neg, mul_div_assoc', mul_comm (gaussian (1 / 10 * s) d), mul_div_assoc,
      div_self hne, mul_one]
  have hfK : ∀ i, Integrable (fun d => fK d i) ν := by
    intro i
    refine integrable_avgMeasure_real s ?_
    obtain ⟨M, hM⟩ := abs_gaussianD_le_const 1 hs
    have h1 : Integrable (fun d => -(√s ^ j * gaussianD (j - 1) (1 / 20 * s) d)) :=
      ((integrable_gaussianD (j - 1) (by positivity)).const_mul _).neg
    have hc1 : Continuous fun d => -(Hd.h * gaussianD 1 s (Hd.u i - (p v + d))) := by
      have := continuous_gaussianD 1 s
      fun_prop
    have := h1.mul_bdd (c := Hd.h * M) hc1.aestronglyMeasurable
      (Eventually.of_forall fun d => by
        change ‖-(Hd.h * gaussianD 1 s (Hd.u i - (p v + d)))‖ ≤ _
        rw [Real.norm_eq_abs, abs_neg, abs_mul, abs_of_pos hh]
        exact mul_le_mul_of_nonneg_left (hM _) hh.le)
    refine this.congr (Eventually.of_forall fun d => ?_)
    change -(√s ^ j * gaussianD (j - 1) (1 / 20 * s) d) *
      -(Hd.h * gaussianD 1 s (Hd.u i - (p v + d))) = gaussian (1 / 10 * s) d * fK d i
    simp only [fK]; rw [← mul_assoc, hgK]
  have hIT : ∀ i, ∫ d, fT d i ∂ν = Hd.w p σB v i := by
    intro i
    rw [integral_avgMeasure_real]
    simp only [fT, gweight, w, σB]
    have := gaussian_conv_gaussian hs hβ (Hd.u i - p v)
    rw [show s + 1 / 10 * s = 11 / 10 * s by ring] at this
    rw [← this, ← integral_const_mul]
    congr 1; funext d
    rw [show Hd.u i - (p v + d) = Hd.u i - p v - d by ring]; ring
  have hIK : ∀ i, ∫ d, fK d i ∂ν = Hd.w p σB v i * Dfun j s (Hd.u i - p v) := by
    intro i
    rw [integral_avgMeasure_real]
    have e : ∀ d, gaussian (1 / 10 * s) d * fK d i = Hd.h * √s ^ j *
        (gaussianD 1 s (Hd.u i - p v - d) * gaussianD (j - 1) (1 / 20 * s) d) := fun d => by
      simp only [fK]
      rw [← mul_assoc, hgK, show Hd.u i - (p v + d) = Hd.u i - p v - d by ring]; ring
    simp_rw [e]
    rw [integral_const_mul, gaussianD_conv_gaussianD 1 (j - 1) hs (by positivity),
      show 1 + (j - 1) = j by omega, show s + 1 / 20 * s = 21 / 20 * s by ring]
    have hg := (gaussian_pos (by positivity : (0 : ℝ) < 11 / 10 * s) (Hd.u i - p v)).ne'
    simp only [w, gweight, σB, Dfun]
    rw [show Hd.h * gaussian (11 / 10 * s) (Hd.u i - p v) *
        (√s ^ j * gaussianD j (21 / 20 * s) (Hd.u i - p v) / gaussian (11 / 10 * s) (Hd.u i - p
            v)) =
        Hd.h * (gaussian (11 / 10 * s) (Hd.u i - p v) *
          (√s ^ j * gaussianD j (21 / 20 * s) (Hd.u i - p v)) /
            gaussian (11 / 10 * s) (Hd.u i - p v)) by ring, mul_div_cancel_left₀ _ hg]
    ring
  obtain ⟨iT, mT⟩ := matIntegral_wGram (ν := ν) Bw fT hfT
  obtain ⟨iK, mK⟩ := matIntegral_wGram (ν := ν) Bw fK hfK
  have hTavg : matIntegral ν (fun d => wGram Bw (fT d)) = Hd.T p σB v := by
    rw [mT, T_eq_wGram Hd p σB hh.le]
    simp_rw [hIT]
    rfl
  have hKavg : matIntegral ν (fun d => wGram Bw (fK d)) =
      (Hd.R p σB v)ᴴ * rdiag (fun i => Dfun j s (Hd.u i - p v)) * Hd.R p σB v := by
    rw [mK, R_insert_eq Hd hh.le p σB v _]
    simp_rw [hIK]
    rfl
  have hTm : Measurable fun d => wGram Bw (fT d) := by
    have : Continuous fun d => wGram Bw (fT d) := continuous_wGram continuous_const fun i =>
      continuous_const.mul ((continuous_gaussian' s).comp
        (continuous_const.sub (continuous_const.add continuous_id)))
    exact this.measurable
  have hTpsd : ∀ d, (wGram Bw (fT d)).PosSemidef := fun d =>
    wGram_posSemidef _ fun i => gweight_nonneg _ hh.le _ _ _
  have h03 := matCost_average_le hTm hTpsd iT iK
  rw [hTavg, hKavg] at h03
  refine h03.trans ?_
  rw [lintegral_avgMeasure, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun d => ?_
  rw [← hT d, ← hK d]
  have hc := matCost_smul_le (Hd.T (Function.update p v (p v + d)) σV v)
    (Hd.Ui (Function.update p v (p v + d)) σV v) (acoef j s d)
  have ha2 : acoef j s d ^ 2 ≤ Ca ^ 2 * s := by
    have := hCa s hs d
    have h0 := abs_nonneg (acoef j s d)
    rw [← sq_abs]
    calc |acoef j s d| ^ 2 ≤ (Ca * √s) ^ 2 := pow_le_pow_left₀ h0 this 2
      _ = Ca ^ 2 * s := by rw [mul_pow, Real.sq_sqrt hs.le]
  calc ENNReal.ofReal (gaussian (1 / 10 * s) d) *
        matCost (Hd.T (Function.update p v (p v + d)) σV v)
          (((acoef j s d : ℝ) : ℂ) • Hd.Ui (Function.update p v (p v + d)) σV v)
      ≤ ENNReal.ofReal (gaussian (1 / 10 * s) d) * (ENNReal.ofReal (acoef j s d ^ 2) *
          matCost (Hd.T (Function.update p v (p v + d)) σV v)
            (Hd.Ui (Function.update p v (p v + d)) σV v)) := mul_le_mul' le_rfl hc
    _ ≤ ENNReal.ofReal (gaussian (1 / 10 * s) d) * (ENNReal.ofReal (Ca ^ 2 * s) *
          matCost (Hd.T (Function.update p v (p v + d)) σV v)
            (Hd.Ui (Function.update p v (p v + d)) σV v)) :=
        mul_le_mul' le_rfl (mul_le_mul' (ENNReal.ofReal_le_ofReal ha2) le_rfl)
    _ = _ := by ring

end HeatData

end WeightedCostComparison

section PlaneShifts

lemma matCost_eq_iSup {n : Type*} [Fintype n] [DecidableEq n] {P : Matrix n n ℂ}
    (hP : P.PosSemidef) (K : Matrix n n ℂ) :
    matCost P K = ⨆ m : ℕ, matCost (P + ((1 / ((m : ℝ) + 1) : ℝ) : ℂ) • 1) K := by
  refine le_antisymm ?_ (iSup_le fun m => ?_)
  · refine (matCost_le_liminf hP K (η := fun m : ℕ => 1 / ((m : ℝ) + 1)) (fun m => by positivity)
      tendsto_one_div_add_atTop_nhds_zero_nat).trans ?_
    exact (liminf_le_limsup (f := atTop)).trans limsup_le_iSup
  · refine matCost_anti (posDef_add_smul_one hP (by positivity)).posSemidef ?_ K
    rw [Matrix.le_iff, add_sub_cancel_left]
    exact Matrix.PosSemidef.one.smul (by exact_mod_cast (by positivity : (0 : ℝ) ≤ 1 / ((m : ℝ)
        + 1)))

/-- The linear coordinate change from center-plane coordinates and a shift at vertex `v`. -/
def shiftMat (v : Fin 3) : Matrix (Fin 3) (Fin 3) ℝ := fun r c =>
  if c = 2 then (if r = v then 1 else 0) else (if r = 2 then -1 else if r = c then 1 else 0)

lemma shiftMat_mulVec (v : Fin 3) (x : Fin 3 → ℝ) :
    shiftMat v *ᵥ x = Function.update (planePt ![x 0, x 1]) v (planePt ![x 0, x 1] v + x 2) := by
  ext r
  fin_cases v <;> fin_cases r <;>
    simp [shiftMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three, planePt] <;> ring

lemma det_shiftMat (v : Fin 3) :
    (shiftMat v).det = 1 := by
  fin_cases v <;> simp [Matrix.det_fin_three, shiftMat]

theorem lintegral_plane_shift (v : Fin 3) {F : (Fin 3 → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ q : Fin 2 → ℝ, ∫⁻ d, F (Function.update (planePt q) v (planePt q v + d)) = ∫⁻ p, F p := by
  set L := Matrix.toLin' (shiftMat v)
  have hdet : (shiftMat v).det ≠ 0 := by rw [det_shiftMat]; norm_num
  have hmap : Measure.map L volume = (volume : Measure (Fin 3 → ℝ)) := by
    rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hdet, det_shiftMat]; simp
  have hLm : Measurable L := (LinearMap.continuous_on_pi L).measurable
  rw [← hmap, lintegral_map hF hLm]
  simp only [L, Matrix.toLin'_apply, shiftMat_mulVec]
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2
  have hmp : MeasurePreserving e.symm ((volume : Measure ℝ).prod (volume : Measure (Fin 2 → ℝ)))
      volume := (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).symm
  set G : (Fin 3 → ℝ) → ℝ≥0∞ := fun x =>
    F (Function.update (planePt ![x 0, x 1]) v (planePt ![x 0, x 1] v + x 2))
  have hG : Measurable G := by
    refine hF.comp ?_
    have : (fun x : Fin 3 → ℝ => Function.update (planePt ![x 0, x 1]) v
        (planePt ![x 0, x 1] v + x 2)) = fun x => shiftMat v *ᵥ x := by
      funext x; rw [shiftMat_mulVec]
    rw [this]
    exact (Matrix.toLin' (shiftMat v)).continuous_on_pi.measurable
  change ∫⁻ q : Fin 2 → ℝ, ∫⁻ d, F (Function.update (planePt q) v (planePt q v + d)) = ∫⁻ x, G x
  rw [← hmp.lintegral_comp hG,
    lintegral_prod_symm (fun z => G (e.symm z)) (hG.comp e.symm.measurable).aemeasurable]
  refine lintegral_congr fun q => lintegral_congr fun d => ?_
  simp only [G]
  have h0 : e.symm (d, q) 0 = q 0 := rfl
  have h1 : e.symm (d, q) 1 = q 1 := rfl
  have h2 : e.symm (d, q) 2 = d := rfl
  rw [h0, h1, h2]
  congr 3; ext i; fin_cases i <;> rfl

end PlaneShifts

section AveragedTrace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace HeatData

variable (Hd : HeatData ι)

/-- The diagonal matrix of Gaussian derivative multipliers at vertex `v`. -/
def Dmat (m : ℕ) (v : Fin 3) (p : Fin 3 → ℝ) (s : ℝ) : Matrix ι ι ℂ :=
  rdiag fun i => Dfun (dexp m v) s (Hd.u i - p v)

/-- The cyclic trace of the three weighted edge matrices with diagonal derivatives inserted. -/
def baseTrace (m : ℕ) (p : Fin 3 → ℝ) (s : ℝ) : ℂ :=
  (Hd.Dmat m 0 p s * Hd.W p (fun _ => 11 / 10 * s) 0 * Hd.Dmat m 1 p s *
    Hd.W p (fun _ => 11 / 10 * s) 1 * Hd.Dmat m 2 p s * Hd.W p (fun _ => 11 / 10 * s) 2).trace

omit [Fintype ι] [DecidableEq ι] in
lemma Dfun_mul_w (hh : 0 ≤ Hd.h) (d : ℕ) {s : ℝ} (hs : 0 < s) (p : Fin 3 → ℝ) (v : Fin 3)
    (i : ι) :
    Dfun d s (Hd.u i - p v) * Hd.sqw p (fun _ => 11 / 10 * s) v i ^ 2 = Hd.h * (√s ^ d *
      gaussianD d (21 / 20 * s) (Hd.u i - p v)) := by
  rw [show Hd.sqw p (fun _ => 11 / 10 * s) v i ^ 2 = Hd.w p (fun _ => 11 / 10 * s) v i from
    Real.sq_sqrt (gweight_nonneg _ hh _ _ _)]
  have hg := (gaussian_pos (by positivity : (0 : ℝ) < 11 / 10 * s) (Hd.u i - p v)).ne'
  simp only [w, gweight, Dfun]
  rw [div_mul_eq_mul_div, div_eq_iff hg]; ring

theorem baseTrace_eq (hh : 0 ≤ Hd.h) {m : ℕ} (hm : m = 3 ∨ m = 4) {s : ℝ} (hs : 0 < s)
    (p : Fin 3 → ℝ) :
    Hd.baseTrace m p s = ((Hd.h ^ 3 * √s ^ m : ℝ) : ℂ) * ∑ i, ∑ j, ∑ k, Hd.A 0 i j * Hd.A 1 j k
      * Hd.A 2 k i * ((gaussianD (dexp m 0) (21 / 20 * s) (Hd.u i - p 0) * gaussianD (dexp m 1)
      (21 / 20 * s) (Hd.u j - p 1) * gaussianD (dexp m 2) (21 / 20 * s) (Hd.u k - p 2) : ℝ) : ℂ) :=
          by
  have e1 : (0 : Fin 3) + 1 = 1 := rfl
  have e2 : (1 : Fin 3) + 1 = 2 := rfl
  have e3 : (2 : Fin 3) + 1 = 0 := rfl
  rw [baseTrace, Dmat, Dmat, Dmat, W, W, W, e1, e2, e3, trace_cyclic_diag, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Hd.Dfun_mul_w hh _ hs, Hd.Dfun_mul_w hh _ hs, Hd.Dfun_mul_w hh _ hs]
  have hsum := dexp_sum hm
  have hpow : √s ^ dexp m 0 * √s ^ dexp m 1 * √s ^ dexp m 2 = √s ^ m := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have : (Hd.h * (√s ^ dexp m 0 * gaussianD (dexp m 0) (21 / 20 * s) (Hd.u i - p 0)) *
      (Hd.h * (√s ^ dexp m 1 * gaussianD (dexp m 1) (21 / 20 * s) (Hd.u j - p 1))) *
      (Hd.h * (√s ^ dexp m 2 * gaussianD (dexp m 2) (21 / 20 * s) (Hd.u k - p 2)))) =
      Hd.h ^ 3 * √s ^ m * (gaussianD (dexp m 0) (21 / 20 * s) (Hd.u i - p 0) *
        gaussianD (dexp m 1) (21 / 20 * s) (Hd.u j - p 1) *
        gaussianD (dexp m 2) (21 / 20 * s) (Hd.u k - p 2)) := by
    rw [← hpow]; ring
  rw [this]
  push_cast; ring

theorem integral_baseTrace (hh : 0 ≤ Hd.h) {m : ℕ} (hm : m = 3 ∨ m = 4) {s : ℝ} (hs : 0 < s) :
    Integrable (fun q : Fin 2 → ℝ => Hd.baseTrace m (planePt q) s) ∧ ∫ q : Fin 2 → ℝ,
      Hd.baseTrace m (planePt q) s = ((Hd.h ^ 3 * √s ^ m : ℝ) : ℂ) * ∑ i, ∑ j, ∑ k, Hd.A 0 i j *
      Hd.A 1 j k * Hd.A 2 k i * (gaussianD m (63 / 20 * s) (Hd.u i + Hd.u j + Hd.u k) : ℂ) := by
  have hq : (0 : ℝ) < 21 / 20 * s := by positivity
  have hpl : ∀ (i j k : ι), (fun q : Fin 2 → ℝ =>
      ((gaussianD (dexp m 0) (21 / 20 * s) (Hd.u i - planePt q 0) *
        gaussianD (dexp m 1) (21 / 20 * s) (Hd.u j - planePt q 1) *
        gaussianD (dexp m 2) (21 / 20 * s) (Hd.u k - planePt q 2) : ℝ) : ℂ)) =
      fun q => ((gaussianD (dexp m 0) (21 / 20 * s) (Hd.u i - q 0) *
        gaussianD (dexp m 1) (21 / 20 * s) (Hd.u j - q 1) *
        gaussianD (dexp m 2) (21 / 20 * s) (Hd.u k + q 0 + q 1) : ℝ) : ℂ) := by
    intro i j k; funext q
    simp only [planePt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    congr 3; ring
  have hint : ∀ i j k, Integrable (fun q : Fin 2 → ℝ => Hd.A 0 i j * Hd.A 1 j k * Hd.A 2 k i *
      ((gaussianD (dexp m 0) (21 / 20 * s) (Hd.u i - planePt q 0) *
        gaussianD (dexp m 1) (21 / 20 * s) (Hd.u j - planePt q 1) *
        gaussianD (dexp m 2) (21 / 20 * s) (Hd.u k - planePt q 2) : ℝ) : ℂ)) := by
    intro i j k
    have := (plane_gaussD_three (dexp m 0) (dexp m 1) (dexp m 2) hq (Hd.u i) (Hd.u j)
      (Hd.u k)).1.const_mul (Hd.A 0 i j * Hd.A 1 j k * Hd.A 2 k i)
    refine this.congr (Eventually.of_forall fun q => ?_)
    have h' := congrFun (hpl i j k) q
    simp only at h' ⊢
    rw [h']
  have hval : ∀ i j k, ∫ q : Fin 2 → ℝ, Hd.A 0 i j * Hd.A 1 j k * Hd.A 2 k i *
      ((gaussianD (dexp m 0) (21 / 20 * s) (Hd.u i - planePt q 0) *
        gaussianD (dexp m 1) (21 / 20 * s) (Hd.u j - planePt q 1) *
        gaussianD (dexp m 2) (21 / 20 * s) (Hd.u k - planePt q 2) : ℝ) : ℂ) =
      Hd.A 0 i j * Hd.A 1 j k * Hd.A 2 k i *
        (gaussianD m (63 / 20 * s) (Hd.u i + Hd.u j + Hd.u k) : ℂ) := by
    intro i j k
    rw [integral_const_mul, hpl i j k, (plane_gaussD_three (dexp m 0) (dexp m 1) (dexp m 2) hq
      (Hd.u i) (Hd.u j) (Hd.u k)).2, dexp_sum hm,
      show 21 / 20 * s + 21 / 20 * s + 21 / 20 * s = 63 / 20 * s by ring]
  simp only [Hd.baseTrace_eq hh hm hs]
  refine ⟨(integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    integrable_finsetSum _ fun k _ => hint i j k).const_mul _, ?_⟩
  rw [integral_const_mul, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    integrable_finsetSum _ fun k _ => hint i j k]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hint i j k]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum _ fun k _ => hint i j k]
  exact Finset.sum_congr rfl fun k _ => hval i j k

end HeatData

end AveragedTrace

section GaussianIntervalKernel

/-- The scale integrand in the Gaussian interval kernel. -/
def kernIntegrand (m : ℕ) (s t : ℝ) : ℝ := √s ^ m * gaussianD m (63 / 20 * s) t / s

/-- The Gaussian derivative kernel integrated over the scale interval `a..b`. -/
def Kern (m : ℕ) (a b t : ℝ) : ℝ := ∫ s in a..b, kernIntegrand m s t

end GaussianIntervalKernel

section CostMeasurability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace HeatData

variable (Hd : HeatData ι)

lemma measurable_rowCost (σ : Fin 3 → ℝ) (hσ : ∀ k, 0 < σ k) (v : Fin 3) :
    Measurable fun p : Fin 3 → ℝ => matCost (Hd.T p σ v) (Hd.Ui p σ v) := by
  have e : (fun p : Fin 3 → ℝ => matCost (Hd.T p σ v) (Hd.Ui p σ v)) = fun p =>
      ⨆ m : ℕ, ENNReal.ofReal (Hd.V p σ (1 / ((m : ℝ) + 1)) v) := by
    funext p
    rw [matCost_eq_iSup (P := Hd.T p σ v) (Matrix.posSemidef_conjTranspose_mul_self _)]
    congr 1; funext m
    exact (ENNReal.ofReal_toReal (matCost_ne_top (posDef_add_smul_one
      (Matrix.posSemidef_conjTranspose_mul_self (Hd.R p σ v))
        (one_div_pos.2 (by positivity : (0 : ℝ) < (m : ℝ) + 1))) (Hd.Ui p σ v))).symm
  rw [e]
  refine Measurable.iSup fun m => ENNReal.measurable_ofReal.comp ?_
  exact ((Hd.continuous_scalars continuous_id continuous_const (fun _ => hσ)
    (by positivity : (0 : ℝ) < 1 / ((m : ℝ) + 1)) v .centerCost)).measurable

end HeatData

end CostMeasurability

section VarianceChoices

/-- The variances grow at rate one at the selected vertex and at rate `11 / 10` elsewhere. -/
def rateAt (v : Fin 3) : Fin 3 → ℝ := fun k => if k = v then 1 else 11 / 10

lemma rateAt_cases (v : Fin 3) : ∀ k, rateAt v k = 1 ∨ rateAt v k = 11 / 10 := fun k => by
  unfold rateAt; split_ifs <;> simp

lemma rateAt_sum (v : Fin 3) :
    rateAt v 0 + rateAt v 1 + rateAt v 2 = 16 / 5 := by
  fin_cases v <;> simp [rateAt] <;> norm_num

lemma sig_rateAt (v : Fin 3) (s : ℝ) :
    HeatData.sig (rateAt v) s = Function.update (fun _ => 11 / 10 * s) v s := by
  funext k
  simp only [HeatData.sig, rateAt, Function.update_apply]
  split_ifs <;> ring

lemma dexp_cases (m : ℕ) (v : Fin 3) :
    dexp m v = 1 ∨ dexp m v = 2 := by
  unfold dexp; split_ifs <;> simp

/-- A common nonnegative bound for the two Gaussian derivative multipliers. -/
def constD : ℝ := Classical.choose (Dfun_bound 1) + Classical.choose (Dfun_bound 2)

/-- A common coefficient for the first- and second-order shift averages. -/
def constA : ℝ := Classical.choose (acoef_bound 1 le_rfl) +
  Classical.choose (acoef_bound 2 (by norm_num))

lemma constD_spec :
    0 ≤ constD ∧ ∀ (m : ℕ) (v : Fin 3) (s : ℝ), 0 < s → ∀ x, |Dfun (dexp m v) s x| ≤ constD := by
  have h1 := Classical.choose_spec (Dfun_bound 1)
  have h2 := Classical.choose_spec (Dfun_bound 2)
  refine ⟨add_nonneg h1.1 h2.1, fun m v s hs x => ?_⟩
  rcases dexp_cases m v with h | h <;> rw [h] <;> unfold constD
  · linarith [h1.2 s hs x, h2.1]
  · linarith [h2.2 s hs x, h1.1]

lemma constA_spec :
    0 ≤ constA ∧ ∀ (m : ℕ) (v : Fin 3) (s : ℝ), 0 < s → ∀ d, |acoef (dexp m v) s d| ≤ constA *
      √s := by
  have h1 := Classical.choose_spec (acoef_bound 1 le_rfl)
  have h2 := Classical.choose_spec (acoef_bound 2 (by norm_num))
  refine ⟨add_nonneg h1.1 h2.1, fun m v s hs d => ?_⟩
  have hs' := Real.sqrt_nonneg s
  rcases dexp_cases m v with h | h <;> rw [h] <;> unfold constA
  · nlinarith [h1.2 s hs d, mul_nonneg h2.1 hs']
  · nlinarith [h2.2 s hs d, mul_nonneg h1.1 hs']

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

end VarianceChoices

section NormNormalization

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma eq_zero_of_nNorm_eq_zero {h : ℝ} (hh : 0 < h) {A : Matrix ι ι ℂ} (hA : nNorm h A = 0) :
    A = 0 := by
  unfold nNorm at hA
  have hS : 0 ≤ h ^ 2 * ∑ i, ∑ j, ‖A i j‖ ^ 3 := by positivity
  rw [Real.rpow_eq_zero hS (by norm_num)] at hA
  have hS0 : ∑ i, ∑ j, ‖A i j‖ ^ 3 = 0 := by
    rcases mul_eq_zero.1 hA with h1 | h1
    · exact absurd h1 (by positivity)
    · exact h1
  ext i j
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg fun j _ =>
    by positivity)).1 hS0 i (Finset.mem_univ i)
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by positivity)).1 h1 j
    (Finset.mem_univ j)
  simpa using h2

end NormNormalization

end

end Triangular.Auto

@[expose] public section
open scoped ENNReal NNReal

open MeasureTheory Filter Topology Real

namespace Triangular.Auto

noncomputable section

section Kernels

lemma Kern_eq (m : ℕ) (a b t : ℝ) : Kern m a b t = ∫ s in a..b, kernIntegrand m s t := rfl

lemma continuousOn_kernIntegrand_joint (m : ℕ) :
    ContinuousOn (fun z : ℝ × ℝ => kernIntegrand m z.1 z.2) {z | 0 < z.1} := by
  let rescale : ℝ × ℝ → ℝ × ℝ := fun z => (63 / 20 * z.1, z.2)
  have fst : Continuous (fun z : ℝ × ℝ => z.1) := continuous_fst
  have scale : Continuous (fun z : ℝ × ℝ => 63 / 20 * z.1) := continuous_const.mul fst
  have hmap : Continuous rescale := scale.prodMk continuous_snd
  have hpositive : Set.MapsTo rescale {z | 0 < z.1} {z | 0 < z.1} :=
    fun _ hz => mul_pos (by norm_num : (0 : ℝ) < 63 / 20) hz
  have hg := (continuousOn_gaussianD_joint m).comp' hmap.continuousOn hpositive
  simp only [rescale] at hg
  have numerator : Continuous (fun z : ℝ × ℝ => √z.1 ^ m) :=
    (Real.continuous_sqrt.comp fst).pow m
  have nonzero (z : ℝ × ℝ) (hz : z ∈ {z : ℝ × ℝ | 0 < z.1}) : z.1 ≠ 0 := ne_of_gt hz
  unfold kernIntegrand
  exact (numerator.continuousOn.mul hg).div fst.continuousOn nonzero

lemma continuous_Kern (m : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : Continuous (Kern m a b) := by
  have e : Kern m a b = fun t => ∫ s in a..b, kernIntegrand m (max a s) t := by
    funext t
    rw [Kern_eq]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le hab] at hs
    simp [max_eq_right hs.1]
  rw [e]
  have hc : Continuous fun z : ℝ × ℝ => kernIntegrand m (max a z.2) z.1 :=
    (continuousOn_kernIntegrand_joint m).comp_continuous
      ((continuous_const.max continuous_snd).prodMk continuous_fst)
      fun z => lt_of_lt_of_le ha (le_max_left _ _)
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
    (f := fun t s => kernIntegrand m (max a s) t) hc a b

end Kernels

end

end Triangular.Auto

/-! Direct fixed-interval heat estimate. -/

@[expose] public section

namespace Triangular.Auto

open MeasureTheory Filter Topology Matrix

open scoped ENNReal NNReal MatrixOrder Matrix.Norms.L2Operator ComplexOrder

noncomputable section

/-- The regularized spectral cost converges to the supported cost. -/
lemma matCost_tendsto_regularization {n : Type*} [Fintype n] [DecidableEq n]
    {P : Matrix n n ℂ} (hP : P.PosSemidef) (K : Matrix n n ℂ)
    {η : ℕ → ℝ} (hη0 : ∀ m, 0 ≤ η m) (hη : Tendsto η atTop (𝓝 0)) :
    Tendsto (fun m => matCost (P + (η m : ℂ) • 1) K) atTop (𝓝 (matCost P K)) := by
  apply tendsto_of_le_liminf_of_limsup_le (matCost_le_liminf hP K hη0 hη)
  apply limsup_le_of_le isCobounded_le_of_bot
  filter_upwards [] with m
  have hi : ((η m : ℂ) • (1 : Matrix n n ℂ)).PosSemidef :=
    Matrix.PosSemidef.one.smul (by exact_mod_cast hη0 m)
  exact matCost_anti (hP.add hi) (le_add_of_nonneg_right hi.nonneg) K

/-- The nonnegative Gaussian-weighted dissipation density. -/
def heatCost {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Hd : HeatData ι) (α : Fin 3 → ℝ) (z : ℝ × (Fin 3 → ℝ)) : ℝ≥0∞ :=
  ENNReal.ofReal (Gm (1 / 10) 0 z.1 z.2) *
    ∑ v, matCost (Hd.T z.2 (HeatData.sig α z.1) v) (Hd.Ui z.2 (HeatData.sig α z.1) v)

lemma heatCost_tendsto {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Hd : HeatData ι) (α : Fin 3 → ℝ) (z : ℝ × (Fin 3 → ℝ))
    {η : ℕ → ℝ} (hη0 : ∀ m, 0 < η m) (hη : Tendsto η atTop (𝓝 0)) :
    Tendsto (fun m => ENNReal.ofReal (Hd.costDensity α (η m) z)) atTop
      (𝓝 (heatCost Hd α z)) := by
  simp only [Hd.ofReal_costDensity (hη0 _), heatCost]
  apply ENNReal.Tendsto.const_mul _ (Or.inr ENNReal.ofReal_ne_top)
  apply tendsto_finsetSum
  intro v _
  exact matCost_tendsto_regularization (Matrix.posSemidef_conjTranspose_mul_self _)
    _ (fun m => (hη0 m).le) hη

/-- The dissipation on one Gaussian scale interval is bounded by its initial energy. -/
theorem heatCost_interval_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Hd : HeatData ι) {kk : ι → ℤ} (hk : Function.Injective kk)
    (hu : ∀ i, Hd.u i = Hd.h * kk i) (hh : 0 < Hd.h)
    {α : Fin 3 → ℝ} (hα : ∀ v, α v = 1 ∨ α v = 11 / 10)
    (hsum : α 0 + α 1 + α 2 = 16 / 5) {a b : ℝ}
    (ha : Hd.h ^ 2 ≤ a) (hab : a ≤ b) :
    ∫⁻ z, heatCost Hd α z ∂((volume.restrict (Set.Ioc a b)).prod volume) ≤
      ENNReal.ofReal (28 * (2 * Real.sqrt 2 * (1 + Real.sqrt (2 / Real.pi))) *
        ∑ v, Hd.nCube v) := by
  let η : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1)
  have hη0 : ∀ m, 0 < η m := fun m => by positivity
  have hη1 : ∀ m, η m ≤ 1 := fun m => by
    exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) m])
  have hη : Tendsto η atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity) ha
  have hα1 : ∀ v, 1 ≤ α v := by
    intro v
    rcases hα v with h | h <;> norm_num [h]
  have hα2 : ∀ v, α v ≤ 2 := by
    intro v
    rcases hα v with h | h <;> norm_num [h]
  let μ := (volume.restrict (Set.Ioc a b)).prod (volume : Measure (Fin 3 → ℝ))
  let f : ℕ → ℝ × (Fin 3 → ℝ) → ℝ≥0∞ :=
    fun m z => ENNReal.ofReal (Hd.costDensity α (η m) z)
  have hf : ∀ m, AEMeasurable (f m) μ := fun m =>
    (Hd.costDensity_integrable hh (hη0 m) hα1 hα2 ha0
      hab).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hpt : ∀ z, Tendsto (fun m => f m z) atTop (𝓝 (heatCost Hd α z)) :=
    fun z => heatCost_tendsto Hd α z hη0 hη
  have hbound : ∀ m, ∫⁻ z, f m z ∂μ ≤ ENNReal.ofReal (28 * Hd.Jbar α (η m) a) := by
    intro m
    have hd := Hd.smeared_plane_dissipation α (η m) hh (hη0 m) hα hsum ha0 hab
    have hj := Hd.Jbar_nonneg α (hη0 m).le b
    rw [show (∫⁻ z, f m z ∂μ) = ENNReal.ofReal
      (∫ s in a..b, ∑ v, Hd.Vbar α (η m) v s) by
        simpa only [f, μ, Hd.ofReal_costDensity (hη0 m)] using
          (Hd.ofReal_integral_Vbar hh (hη0 m) hα1 hα2 ha0 hab).symm]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hlim : Tendsto (fun m => ENNReal.ofReal (28 * Hd.Jbar α (η m) a)) atTop
      (𝓝 (ENNReal.ofReal (28 * Hd.Jbar α 0 a))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp
      ((Hd.tendsto_Jbar hh hα1 hα2 ha0 hη0 hη1 hη).const_mul 28)
  calc
    ∫⁻ z, heatCost Hd α z ∂μ = ∫⁻ z, liminf (fun m => f m z) atTop ∂μ :=
      lintegral_congr fun z => (hpt z).liminf_eq.symm
    _ ≤ liminf (fun m => ∫⁻ z, f m z ∂μ) atTop := lintegral_liminf_le' hf
    _ ≤ ENNReal.ofReal (28 * Hd.Jbar α 0 a) := by
      rw [← hlim.liminf_eq]
      exact liminf_le_liminf (Eventually.of_forall hbound)
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      have hJ := Hd.Jbar_zero_le hh kk hk hu α hα1 ha
      nlinarith)

end

end Triangular.Auto
