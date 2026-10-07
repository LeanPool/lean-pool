/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedSchwartzTensorBilinear
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselSchwartzCore
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Even Bessel norms of Schwartz tensors through physical derivatives

For a complex tensor-valued Schwartz field, the Bessel potential of even
order 2k is the k-fold iterate of the second-order operator
1 - (2π)⁻² Δ. Consequently the complete H²ᵏ norm of the canonical
Sobolev lift is the L² norm of that iterate, and every derivative of the
iterate is controlled pointwise by the derivatives of the field up to
2k further orders.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform SchwartzMap Laplacian

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic LineDeriv

/-- Each Fréchet derivative of a directional derivative of a Schwartz
field is bounded by the next derivative of the field times the length of
the direction. -/
theorem regularisedSchwartz_iteratedFDeriv_lineDerivOp_norm_le
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ψ : 𝓢(L2Vec3, F)) (v : L2Vec3) (n : ℕ) (x : L2Vec3) :
    ‖iteratedFDeriv ℝ n ⇑(∂_{v} ψ : 𝓢(L2Vec3, F)) x‖ ≤
      ‖v‖ * ‖iteratedFDeriv ℝ (n + 1) ψ x‖ := by
  have hfun : ⇑(∂_{v} ψ : 𝓢(L2Vec3, F)) = fun y => fderiv ℝ ψ y v := by
    funext y
    exact SchwartzMap.lineDerivOp_apply_eq_fderiv v ψ y
  have hsmooth : ContDiff ℝ n (fderiv ℝ (ψ : L2Vec3 → F)) :=
    (ψ.smooth (n + 1 : ℕ)).fderiv_right (by norm_cast)
  rw [hfun, ← norm_iteratedFDeriv_fderiv]
  exact norm_iteratedFDeriv_clm_apply_const hsmooth.contDiffAt le_rfl

/-- Each Fréchet derivative of the Laplacian of a Schwartz field is
bounded by three times the derivative two orders higher. -/
theorem regularisedSchwartz_iteratedFDeriv_laplacian_norm_le
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ψ : 𝓢(L2Vec3, F)) (n : ℕ) (x : L2Vec3) :
    ‖iteratedFDeriv ℝ n ⇑(Δ ψ : 𝓢(L2Vec3, F)) x‖ ≤
      (Module.finrank ℝ L2Vec3 : ℝ) * ‖iteratedFDeriv ℝ (n + 2) ψ x‖ := by
  let b := stdOrthonormalBasis ℝ L2Vec3
  have hfun : ⇑(Δ ψ : 𝓢(L2Vec3, F)) =
      fun y => ∑ i ∈ Finset.univ, ⇑(∂_{b i} (∂_{b i} ψ) : 𝓢(L2Vec3, F)) y := by
    funext y
    rw [SchwartzMap.laplacian_eq_sum b]
    exact sum_apply _ _ _
  have hsmooth : ∀ i ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ L2Vec3))),
      ContDiff ℝ n ⇑(∂_{b i} (∂_{b i} ψ) : 𝓢(L2Vec3, F)) :=
    fun i _ => (∂_{b i} (∂_{b i} ψ)).smooth n
  rw [hfun, iteratedFDeriv_sum hsmooth, Finset.sum_apply]
  have hterm (i : Fin (Module.finrank ℝ L2Vec3)) :
      ‖iteratedFDeriv ℝ n ⇑(∂_{b i} (∂_{b i} ψ) : 𝓢(L2Vec3, F)) x‖ ≤
        ‖iteratedFDeriv ℝ (n + 2) ψ x‖ := by
    have h1 := regularisedSchwartz_iteratedFDeriv_lineDerivOp_norm_le
      (∂_{b i} ψ) (b i) n x
    have h2 := regularisedSchwartz_iteratedFDeriv_lineDerivOp_norm_le
      ψ (b i) (n + 1) x
    rw [b.norm_eq_one, one_mul] at h1 h2
    exact h1.trans h2
  calc
    ‖∑ i ∈ Finset.univ,
        iteratedFDeriv ℝ n ⇑(∂_{b i} (∂_{b i} ψ) : 𝓢(L2Vec3, F)) x‖ ≤
        ∑ i ∈ Finset.univ,
          ‖iteratedFDeriv ℝ n ⇑(∂_{b i} (∂_{b i} ψ) : 𝓢(L2Vec3, F)) x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _i ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ L2Vec3))),
          ‖iteratedFDeriv ℝ (n + 2) ψ x‖ :=
      Finset.sum_le_sum fun i _ => hterm i
    _ = (Module.finrank ℝ L2Vec3 : ℝ) * ‖iteratedFDeriv ℝ (n + 2) ψ x‖ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The second-order Bessel step ψ ↦ ψ - c Δψ on Schwartz fields. -/
@[expose]
def regularisedSchwartzBesselStep
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (c : ℝ) (ψ : 𝓢(L2Vec3, F)) : 𝓢(L2Vec3, F) :=
  ψ - c • Δ ψ

/-- One Bessel step costs two derivatives in every pointwise derivative
bound. -/
theorem regularisedSchwartzBesselStep_iteratedFDeriv_norm_le
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (c : ℝ) (ψ : 𝓢(L2Vec3, F)) (n : ℕ) (x : L2Vec3) :
    ‖iteratedFDeriv ℝ n ⇑(regularisedSchwartzBesselStep c ψ) x‖ ≤
      ‖iteratedFDeriv ℝ n ψ x‖ +
        |c| * (Module.finrank ℝ L2Vec3 : ℝ) *
          ‖iteratedFDeriv ℝ (n + 2) ψ x‖ := by
  have hfun : ⇑(regularisedSchwartzBesselStep c ψ) =
      (ψ : L2Vec3 → F) - c • ⇑(Δ ψ : 𝓢(L2Vec3, F)) := by
    funext y
    simp [regularisedSchwartzBesselStep]
  have hψ : ContDiffAt ℝ n (ψ : L2Vec3 → F) x := (ψ.smooth n).contDiffAt
  have hΔ : ContDiffAt ℝ n ⇑(Δ ψ : 𝓢(L2Vec3, F)) x := ((Δ ψ).smooth n).contDiffAt
  have hcΔ : ContDiffAt ℝ n (c • ⇑(Δ ψ : 𝓢(L2Vec3, F))) x := hΔ.const_smul c
  rw [hfun, iteratedFDeriv_sub_apply hψ hcΔ,
    iteratedFDeriv_const_smul_apply hΔ]
  have hLap := regularisedSchwartz_iteratedFDeriv_laplacian_norm_le ψ n x
  calc
    ‖iteratedFDeriv ℝ n (ψ : L2Vec3 → F) x -
        c • iteratedFDeriv ℝ n ⇑(Δ ψ : 𝓢(L2Vec3, F)) x‖ ≤
        ‖iteratedFDeriv ℝ n (ψ : L2Vec3 → F) x‖ +
          ‖c • iteratedFDeriv ℝ n ⇑(Δ ψ : 𝓢(L2Vec3, F)) x‖ :=
      norm_sub_le _ _
    _ = ‖iteratedFDeriv ℝ n (ψ : L2Vec3 → F) x‖ +
          |c| * ‖iteratedFDeriv ℝ n ⇑(Δ ψ : 𝓢(L2Vec3, F)) x‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ‖iteratedFDeriv ℝ n (ψ : L2Vec3 → F) x‖ +
          |c| * ((Module.finrank ℝ L2Vec3 : ℝ) *
            ‖iteratedFDeriv ℝ (n + 2) ψ x‖) := by
      gcongr
    _ = ‖iteratedFDeriv ℝ n ψ x‖ +
        |c| * (Module.finrank ℝ L2Vec3 : ℝ) *
          ‖iteratedFDeriv ℝ (n + 2) ψ x‖ := by
      rw [mul_assoc]

/-- The k-fold Bessel step is controlled pointwise, at every derivative
order, by the next 2k derivatives of the field. -/
theorem regularisedSchwartzBesselStep_iterate_iteratedFDeriv_norm_le
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (c : ℝ) (k : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (ψ : 𝓢(L2Vec3, F)) (n : ℕ) (x : L2Vec3),
      ‖iteratedFDeriv ℝ n
          ⇑((regularisedSchwartzBesselStep c)^[k] ψ) x‖ ≤
        A * ∑ m ∈ Finset.range (2 * k + 1),
          ‖iteratedFDeriv ℝ (n + m) ψ x‖ := by
  induction k with
  | zero =>
      refine ⟨1, zero_le_one, ?_⟩
      intro ψ n x
      simp
  | succ k ih =>
      obtain ⟨A, hA, hBound⟩ := ih
      let d : ℝ := |c| * (Module.finrank ℝ L2Vec3 : ℝ)
      have hd : 0 ≤ d := by positivity
      refine ⟨A + A * d, by positivity, ?_⟩
      intro ψ n x
      let a : ℕ → ℝ := fun m => ‖iteratedFDeriv ℝ (n + m) ψ x‖
      have ha : ∀ m, 0 ≤ a m := fun m => norm_nonneg _
      let S : ℝ := ∑ m ∈ Finset.range (2 * (k + 1) + 1), a m
      have hS1 : ∑ m ∈ Finset.range (2 * k + 1), a m ≤ S := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro m hm
          simp only [Finset.mem_range] at hm ⊢
          omega
        · intro m _ _
          exact ha m
      have hS2 : ∑ m ∈ Finset.range (2 * k + 1), a (m + 2) ≤ S := by
        have hsplit : S = ∑ m ∈ Finset.range 2, a m +
            ∑ m ∈ Finset.range (2 * k + 1), a (2 + m) := by
          simp only [S]
          rw [show 2 * (k + 1) + 1 = 2 + (2 * k + 1) by ring]
          exact Finset.sum_range_add a 2 (2 * k + 1)
        have hfirst : 0 ≤ ∑ m ∈ Finset.range 2, a m :=
          Finset.sum_nonneg fun m _ => ha m
        have hcongr : ∑ m ∈ Finset.range (2 * k + 1), a (m + 2) =
            ∑ m ∈ Finset.range (2 * k + 1), a (2 + m) :=
          Finset.sum_congr rfl fun m _ => by rw [add_comm m 2]
        rw [hcongr, hsplit]
        linarith only [hfirst]
      have hStep (m : ℕ) :
          ‖iteratedFDeriv ℝ (n + m)
              ⇑(regularisedSchwartzBesselStep c ψ) x‖ ≤
            a m + d * a (m + 2) := by
        have h := regularisedSchwartzBesselStep_iteratedFDeriv_norm_le
          c ψ (n + m) x
        have e : n + (m + 2) = n + m + 2 := by omega
        simp only [a, d]
        rw [e]
        exact h
      rw [Function.iterate_succ_apply]
      calc
        ‖iteratedFDeriv ℝ n
            ⇑((regularisedSchwartzBesselStep c)^[k]
              (regularisedSchwartzBesselStep c ψ)) x‖ ≤
            A * ∑ m ∈ Finset.range (2 * k + 1),
              ‖iteratedFDeriv ℝ (n + m)
                ⇑(regularisedSchwartzBesselStep c ψ) x‖ :=
          hBound _ n x
        _ ≤ A * ∑ m ∈ Finset.range (2 * k + 1), (a m + d * a (m + 2)) := by
          gcongr with m hm
          exact hStep m
        _ = A * (∑ m ∈ Finset.range (2 * k + 1), a m) +
            A * d * ∑ m ∈ Finset.range (2 * k + 1), a (m + 2) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          ring
        _ ≤ A * S + A * d * S := by
          have hAd : 0 ≤ A * d := mul_nonneg hA hd
          gcongr
        _ = (A + A * d) * S := by ring

/-- The order-two Bessel potential on complex tensor distributions is the
identity minus (2π)⁻² times the Laplacian. -/
theorem regularisedTensor_besselPotential_two_eq
    (D : 𝓢'(L2Vec3, ComplexTensor3)) :
    TemperedDistribution.besselPotential L2Vec3 ComplexTensor3 2 D =
      D - ((2 * Real.pi) ^ 2)⁻¹ • Laplacian.laplacian D := by
  let q : L2Vec3 → ℂ := fun ξ => ((‖ξ‖ ^ 2 : ℝ) : ℂ)
  have hq : q.HasTemperateGrowth := by
    dsimp [q]
    fun_prop
  have hOne : (fun _ξ : L2Vec3 => (1 : ℂ)).HasTemperateGrowth := by
    fun_prop
  have hSymbol : (fun ξ : L2Vec3 =>
      (((1 + ‖ξ‖ ^ 2) ^ ((2 : ℝ) / 2) : ℝ) : ℂ)) =
      (fun ξ => (1 : ℂ) + q ξ) := by
    funext ξ
    simp [q]
  have hBessel : TemperedDistribution.besselPotential L2Vec3 ComplexTensor3 2 D =
      D + TemperedDistribution.fourierMultiplierCLM ComplexTensor3 q D := by
    rw [TemperedDistribution.besselPotential,
      TemperedDistribution.fourierMultiplierCLM_apply, hSymbol]
    change 𝓕⁻ ((TemperedDistribution.smulLeftCLM ComplexTensor3
        ((fun _ξ : L2Vec3 => (1 : ℂ)) + q)) (𝓕 D)) = _
    rw [TemperedDistribution.smulLeftCLM_add hOne hq,
      add_apply, fourierInv_add]
    simp only [TemperedDistribution.smulLeftCLM_const,
      one_smul, fourierInv_fourier_eq]
    rfl
  have hLap := TemperedDistribution.laplacian_eq_fourierMultiplierCLM D
  have hne : ((2 * Real.pi) ^ 2 : ℝ) ≠ 0 := by positivity
  rw [hBessel, hLap, smul_smul]
  have hcoef : ((2 * Real.pi) ^ 2)⁻¹ * -(2 * Real.pi) ^ 2 = (-1 : ℝ) := by
    field_simp
  rw [hcoef, neg_one_smul, sub_neg_eq_add]

/-- On a Schwartz tensor, the even Bessel potential of order 2k is the
k-fold second-order Bessel step with constant (2π)⁻². -/
theorem regularisedTensor_besselPotential_even_schwartz
    (k : ℕ) (T : 𝓢(L2Vec3, ComplexTensor3)) :
    TemperedDistribution.besselPotential L2Vec3 ComplexTensor3 ((2 * k : ℕ) : ℝ)
        (T : 𝓢'(L2Vec3, ComplexTensor3)) =
      (((regularisedSchwartzBesselStep ((2 * Real.pi) ^ 2)⁻¹)^[k] T :
        𝓢(L2Vec3, ComplexTensor3)) : 𝓢'(L2Vec3, ComplexTensor3)) := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hcast : ((2 * (k + 1) : ℕ) : ℝ) = ((2 * k : ℕ) : ℝ) + 2 := by
        push_cast
        ring
      rw [hcast, ← TemperedDistribution.besselPotential_besselPotential_apply, ih,
        regularisedTensor_besselPotential_two_eq, Function.iterate_succ_apply',
        TemperedDistribution.laplacian_toTemperedDistributionCLM_eq]
      rw [regularisedSchwartzBesselStep, map_sub,
        ContinuousLinearMap.map_smul_of_tower]

/-- The complete H²ᵏ norm of the canonical Sobolev lift of a Schwartz
tensor is the L² norm of its k-fold second-order Bessel step. -/
theorem regularisedTensor_schwartz_bessel_even_norm_eq
    (k : ℕ) (T : 𝓢(L2Vec3, ComplexTensor3)) :
    ‖(T.memSobolev (s := ((2 * k : ℕ) : ℝ)) (p := 2)).toBesselPotentialSpace‖ =
      ‖((regularisedSchwartzBesselStep ((2 * Real.pi) ^ 2)⁻¹)^[k] T).toLp 2‖ := by
  have hv : (T.memSobolev (s := ((2 * k : ℕ) : ℝ)) (p := 2)).toBesselPotentialSpace.toDistr =
      (T : 𝓢'(L2Vec3, ComplexTensor3)) :=
    (T.memSobolev (s := ((2 * k : ℕ) : ℝ)) (p := 2)).toBesselPotentialSpace_toDistr
  generalize (T.memSobolev (s := ((2 * k : ℕ) : ℝ)) (p := 2)).toBesselPotentialSpace = v at hv ⊢
  have hspec := v.bessel_toDistr_eq_toLp
  rw [hv, regularisedTensor_besselPotential_even_schwartz,
    ← Lp.toTemperedDistribution_toLp_eq (p := 2) (μ := volume)] at hspec
  have hLp : v.toLp =
      ((regularisedSchwartzBesselStep ((2 * Real.pi) ^ 2)⁻¹)^[k] T).toLp 2 := by
    apply (LinearMap.ker_eq_bot.mp
      (MeasureTheory.Lp.ker_toTemperedDistributionCLM_eq_bot
        (F := ComplexTensor3) (μ := volume) (p := 2)))
    exact hspec.symm
  rw [← BesselPotentialSpace.norm_toLp_eq]
  exact congrArg norm hLp

end CKN.Leray

end
