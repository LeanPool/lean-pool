/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch01.FieldSpaces
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.EuclideanL2CZ
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.SmoothLimit

/-!
# H10SkewDivergence

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Weak divergence of an antisymmetric matrix of `H¹₀` potentials

This file supplies the model-free analytic core for the `G` leg of the
piecewise-affine competitor.  Given scalar potentials `u i ∈ H¹₀(U)`, it
represents the weak divergence of

```text
Dᵢⱼ = (d - 1)⁻¹ (qⱼ uᵢ - qᵢ uⱼ)
```

directly through their weak gradients.  Antisymmetry and the commutation of
mixed weak derivatives imply that this vector field is in the public
`L²_sol,0(U)` class.

The construction is independent of the Section 3 geometry.  A later file may
identify particular `H¹₀` potentials with the superposed piecewise-affine
competitor and then transport the conclusion by almost-everywhere equality.
-/

namespace Algsuperdiff.Section3.Provider.Affine

open Filter HCPolySupport MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Algebraic construction and `L²` membership -/

/-- The manuscript normalization `(d - 1)⁻¹` in the antisymmetric matrix
`Dᵢⱼ = (d - 1)⁻¹ (qⱼ uᵢ - qᵢ uⱼ)`. -/
def h10SkewDimInv (d : ℕ) : ℝ := 1 / ((d : ℝ) - 1)

/-- The skew-gradient vector field
`(∂_b u) e_a - (∂_a u) e_b`. -/
def skewGradientField (g : Vec d → Vec d) (a b : Fin d) : Vec d → Vec d :=
  fun x => g x b • basisVec a - g x a • basisVec b

private theorem skewGradientField_apply (g : Vec d → Vec d) (a b : Fin d)
    (x : Vec d) (k : Fin d) :
    skewGradientField g a b x k =
      g x b * basisVec a k - g x a * basisVec b k := by
  rw [skewGradientField, Pi.sub_apply, Pi.smul_apply, Pi.smul_apply,
    smul_eq_mul, smul_eq_mul]

private theorem vecDot_skewGradientField (g : Vec d → Vec d) (a b : Fin d)
    (x : Vec d) (w : Vec d) :
    vecDot (skewGradientField g a b x) w = g x b * w a - g x a * w b := by
  have hexp : vecDot (skewGradientField g a b x) w =
      ∑ k, (g x b * (basisVec a k * w k) -
        g x a * (basisVec b k * w k)) := by
    rw [vecDot]
    apply Finset.sum_congr rfl
    intro k _
    rw [skewGradientField_apply]
    ring
  rw [hexp, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have ha : (∑ k, basisVec (d := d) a k * w k) = w a :=
    vecDot_basisVec_left a w
  have hb : (∑ k, basisVec (d := d) b k * w k) = w b :=
    vecDot_basisVec_left b w
  rw [ha, hb]

/-- The weak divergence of the antisymmetric matrix
`(q_j u_i - q_i u_j)/(d-1)`, represented directly by the weak gradients of
the zero-trace scalar potentials. -/
def h10SkewMatrixDiv {U : Set (Vec d)}
    (u : Fin d → H10Function U) (q : Vec d) : Vec d → Vec d :=
  fun x => h10SkewDimInv d • ∑ i : Fin d, ∑ j : Fin d,
    q j • skewGradientField (u i).toH1Function.grad j i x

private theorem memVectorL2_skewGradientField {U : Set (Vec d)}
    (v : H1Function U) (a b : Fin d) :
    MemVectorL2 U (skewGradientField v.grad a b) := by
  have hcoord : ∀ k : Fin d,
      MemLp (fun x => skewGradientField v.grad a b x k) 2 (volumeMeasureOn U) := by
    intro k
    have hfirst :
        MemLp (fun x => v.grad x b * basisVec a k) 2 (volumeMeasureOn U) :=
      (v.gradMemL2 b).mul_const _
    have hsecond :
        MemLp (fun x => v.grad x a * basisVec b k) 2 (volumeMeasureOn U) :=
      (v.gradMemL2 a).mul_const _
    exact MeasureTheory.MemLp.ae_eq
      (Filter.Eventually.of_forall fun x =>
        (skewGradientField_apply v.grad a b x k).symm)
      (hfirst.sub hsecond)
  simpa only [MemVectorL2] using MeasureTheory.MemLp.of_eval hcoord

private theorem memVectorL2_finsetSum {U : Set (Vec d)} {I : Type*}
    (s : Finset I) (f : I → Vec d → Vec d)
    (hf : ∀ i ∈ s, MemVectorL2 U (f i)) :
    MemVectorL2 U (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty =>
      exact (MeasureTheory.MemLp.zero : MemVectorL2 U (0 : Vec d → Vec d))
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (hf i (Finset.mem_insert_self i s)).add
        (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- The weak skew-divergence correction is an `L²` vector field. -/
theorem memVectorL2_h10SkewMatrixDiv {U : Set (Vec d)}
    (u : Fin d → H10Function U) (q : Vec d) :
    MemVectorL2 U (h10SkewMatrixDiv u q) := by
  have hsum : MemVectorL2 U
      (∑ i : Fin d, ∑ j : Fin d,
        q j • skewGradientField (u i).toH1Function.grad j i) := by
    apply memVectorL2_finsetSum Finset.univ
    intro i _
    apply memVectorL2_finsetSum Finset.univ
    intro j _
    exact (memVectorL2_skewGradientField (u i).toH1Function j i).const_smul _
  change MemLp
    (fun x => h10SkewDimInv d • ∑ i : Fin d, ∑ j : Fin d,
      q j • skewGradientField (u i).toH1Function.grad j i x)
    2 (volumeMeasureOn U)
  have hfun : (fun x => h10SkewDimInv d • ∑ i : Fin d, ∑ j : Fin d,
      q j • skewGradientField (u i).toH1Function.grad j i x) =
      h10SkewDimInv d • (∑ i : Fin d, ∑ j : Fin d,
        q j • skewGradientField (u i).toH1Function.grad j i) := by
    funext x
    simp only [Pi.smul_apply, Finset.sum_apply]
  rw [hfun]
  exact hsum.const_smul (h10SkewDimInv d)

/-- Coordinate formula for the weak divergence of the antisymmetric matrix. -/
theorem h10SkewMatrixDiv_apply {U : Set (Vec d)}
    (u : Fin d → H10Function U) (q x : Vec d) (k : Fin d) :
    h10SkewMatrixDiv u q x k =
      h10SkewDimInv d *
        (q k * ∑ i : Fin d, (u i).toH1Function.grad x i -
          ∑ i : Fin d, q i * (u k).toH1Function.grad x i) := by
  classical
  rw [h10SkewMatrixDiv]
  simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  simp_rw [skewGradientField_apply, mul_sub, Finset.sum_sub_distrib]
  rw [show (∑ i : Fin d, ∑ j : Fin d,
      q j * ((u i).toH1Function.grad x i * basisVec j k)) =
      q k * ∑ i : Fin d, (u i).toH1Function.grad x i by
    calc
      (∑ i : Fin d, ∑ j : Fin d,
          q j * ((u i).toH1Function.grad x i * basisVec j k)) =
          ∑ i : Fin d, (u i).toH1Function.grad x i *
            (∑ j : Fin d, q j * basisVec j k) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = q k * ∑ i : Fin d, (u i).toH1Function.grad x i := by
        simp [basisVec_apply]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring,
    show (∑ i : Fin d, ∑ j : Fin d,
      q j * ((u i).toH1Function.grad x j * basisVec i k)) =
      ∑ i : Fin d, q i * (u k).toH1Function.grad x i by
    calc
      (∑ i : Fin d, ∑ j : Fin d,
          q j * ((u i).toH1Function.grad x j * basisVec i k)) =
          ∑ j : Fin d, q j *
            (∑ i : Fin d, (u i).toH1Function.grad x j * basisVec i k) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.mul_sum]
      _ = ∑ i : Fin d, q i * (u k).toH1Function.grad x i := by
        simp [basisVec_apply]]
  ring

/-! ## Commutation of mixed weak gradients -/

private theorem memScalarL2_of_continuous_hasCompactSupport {U : Set (Vec d)}
    {f : Vec d → ℝ} (hf : Continuous f) (hs : HasCompactSupport f) :
    MemScalarL2 U f :=
  (hf.memLp_of_hasCompactSupport (μ := volume) hs).restrict U

private theorem memScalarL2_approx_coordDeriv {U : Set (Vec d)}
    (u : H10Function U) (i : Fin d) (n : ℕ) :
    MemScalarL2 U (euclideanCoordDeriv i (u.approx n)) :=
  memScalarL2_of_continuous_hasCompactSupport
    (contDiff_euclideanCoordDeriv (u.approx_smooth n) i).continuous
    (hasCompactSupport_euclideanCoordDeriv (u.approx_hasCompactSupport n) i)

private theorem tendsto_approx_coordDeriv_toScalarL2 {U : Set (Vec d)}
    (u : H10Function U) (i : Fin d) :
    Tendsto (fun n => toScalarL2 (memScalarL2_approx_coordDeriv u i n)) atTop
      (nhds (toScalarL2 (u.toH1Function.gradMemL2 i))) :=
  tendsto_toScalarL2_of_tendsto_eLpNorm
    (memScalarL2_approx_coordDeriv u i) (u.toH1Function.gradMemL2 i)
    (by simpa only [euclideanCoordDeriv] using u.tendsto_approx_grad i)

private theorem integral_coordDeriv_grad_swap {U : Set (Vec d)}
    (φ : H1Function U) {ψ : Vec d → ℝ}
    (hψs : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hψsub : tsupport ψ ⊆ U) (a b : Fin d) :
    (∫ x in U, φ.grad x a * euclideanCoordDeriv b ψ x ∂volume) =
      ∫ x in U, φ.grad x b * euclideanCoordDeriv a ψ x ∂volume := by
  have hWa := (φ.hasWeakGradient a) (euclideanCoordDeriv b ψ)
    (contDiff_euclideanCoordDeriv hψs b)
    (hasCompactSupport_euclideanCoordDeriv hψc b)
    ((tsupport_euclideanCoordDeriv_subset_tsupport b ψ).trans hψsub)
  have hWb := (φ.hasWeakGradient b) (euclideanCoordDeriv a ψ)
    (contDiff_euclideanCoordDeriv hψs a)
    (hasCompactSupport_euclideanCoordDeriv hψc a)
    ((tsupport_euclideanCoordDeriv_subset_tsupport a ψ).trans hψsub)
  have hmixed : ∀ x,
      (fderiv ℝ (euclideanCoordDeriv b ψ) x) (basisVec a) =
        (fderiv ℝ (euclideanCoordDeriv a ψ) x) (basisVec b) := by
    intro x
    change euclideanCoordSecondDeriv b a ψ x =
      euclideanCoordSecondDeriv a b ψ x
    exact euclideanCoordSecondDeriv_comm hψs b a x
  have hleft :
      (∫ x in U, φ.toFun x *
        (fderiv ℝ (euclideanCoordDeriv b ψ) x) (basisVec a) ∂volume) =
      ∫ x in U, φ.toFun x *
        (fderiv ℝ (euclideanCoordDeriv a ψ) x) (basisVec b) ∂volume := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    change φ.toFun x * (fderiv ℝ (euclideanCoordDeriv b ψ) x) (basisVec a) =
      φ.toFun x * (fderiv ℝ (euclideanCoordDeriv a ψ) x) (basisVec b)
    rw [hmixed x]
  have hneg :
      -(∫ x in U, φ.grad x a * euclideanCoordDeriv b ψ x ∂volume) =
        -(∫ x in U, φ.grad x b * euclideanCoordDeriv a ψ x ∂volume) := by
    rw [← hWa, ← hWb]
    exact hleft
  exact neg_injective hneg

/-- Mixed weak derivatives commute after pairing an `H¹₀` function with an
arbitrary `H¹` function. -/
theorem integral_grad_swap {U : Set (Vec d)} (u : H10Function U)
    (φ : H1Function U) (a b : Fin d) :
    (∫ x in U, φ.grad x a * u.toH1Function.grad x b ∂volume) =
      ∫ x in U, φ.grad x b * u.toH1Function.grad x a ∂volume := by
  have hleft : Tendsto
      (fun n => ∫ x in U,
        φ.grad x a * euclideanCoordDeriv b (u.approx n) x ∂volume)
      atTop (nhds (∫ x in U,
        φ.grad x a * u.toH1Function.grad x b ∂volume)) :=
    tendsto_integral_mul_of_tendsto_toScalarL2 (φ.gradMemL2 a)
      (memScalarL2_approx_coordDeriv u b) (u.toH1Function.gradMemL2 b)
      (tendsto_approx_coordDeriv_toScalarL2 u b)
  have hright : Tendsto
      (fun n => ∫ x in U,
        φ.grad x b * euclideanCoordDeriv a (u.approx n) x ∂volume)
      atTop (nhds (∫ x in U,
        φ.grad x b * u.toH1Function.grad x a ∂volume)) :=
    tendsto_integral_mul_of_tendsto_toScalarL2 (φ.gradMemL2 b)
      (memScalarL2_approx_coordDeriv u a) (u.toH1Function.gradMemL2 a)
      (tendsto_approx_coordDeriv_toScalarL2 u a)
  refine tendsto_nhds_unique hleft ?_
  refine hright.congr fun n => ?_
  exact (integral_coordDeriv_grad_swap φ (u.approx_smooth n)
    (u.approx_hasCompactSupport n) (u.approx_support_subset n) a b).symm

/-! ## Zero-normal solenoidality -/

instance : ENNReal.HolderTriple 2 2 1 :=
  ⟨by rw [inv_one]; exact ENNReal.inv_two_add_inv_two⟩

private theorem integrable_mul_memScalarL2 {U : Set (Vec d)}
    {f g : Vec d → ℝ} (hf : MemScalarL2 U f) (hg : MemScalarL2 U g) :
    Integrable (fun x => f x * g x) (volumeMeasureOn U) :=
  memLp_one_iff_integrable.mp (hf.fun_mul hg)

private theorem integral_skewGradientField_pairing_eq_zero {U : Set (Vec d)}
    (u : H10Function U) (φ : H1Function U) (a b : Fin d) :
    ∫ x in U, vecDot (skewGradientField u.toH1Function.grad a b x) (φ.grad x)
        ∂volume = 0 := by
  rw [show (fun x =>
      vecDot (skewGradientField u.toH1Function.grad a b x) (φ.grad x)) =
      fun x => u.toH1Function.grad x b * φ.grad x a -
        u.toH1Function.grad x a * φ.grad x b by
    funext x
    exact vecDot_skewGradientField u.toH1Function.grad a b x (φ.grad x),
    integral_sub
      (integrable_mul_memScalarL2 (u.toH1Function.gradMemL2 b) (φ.gradMemL2 a))
      (integrable_mul_memScalarL2 (u.toH1Function.gradMemL2 a) (φ.gradMemL2 b))]
  have hswap := integral_grad_swap u φ a b
  rw [show (∫ x in U, u.toH1Function.grad x b * φ.grad x a ∂volume) =
      ∫ x in U, φ.grad x a * u.toH1Function.grad x b ∂volume by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        ring,
    show (∫ x in U, u.toH1Function.grad x a * φ.grad x b ∂volume) =
      ∫ x in U, φ.grad x b * u.toH1Function.grad x a ∂volume by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        ring,
    hswap, sub_self]

private theorem vecDot_finsetSum_left {I : Type*} (s : Finset I)
    (f : I → Vec d) (v : Vec d) :
    vecDot (∑ i ∈ s, f i) v = ∑ i ∈ s, vecDot (f i) v := by
  classical
  induction s using Finset.induction with
  | empty => simp [vecDot]
  | insert i s hi ih =>
      simp only [Finset.sum_insert hi, vecDot_add_left, ih]

private theorem h10SkewMatrixDiv_isSolenoidalZeroNormalTraceOn
    {U : Set (Vec d)} (u : Fin d → H10Function U) (q : Vec d) :
    IsSolenoidalZeroNormalTraceOn U (h10SkewMatrixDiv u q) := by
  intro φ
  have hterm : ∀ i j : Fin d, Integrable
      (fun x => q j * vecDot
        (skewGradientField (u i).toH1Function.grad j i x) (φ.grad x))
      (volumeMeasureOn U) := by
    intro i j
    exact (integrableOn_vecDot_of_memVectorL2
      (memVectorL2_skewGradientField (u i).toH1Function j i)
      φ.grad_memVectorL2).const_mul _
  have hsum : Integrable
      (fun x => ∑ i : Fin d, ∑ j : Fin d,
        q j * vecDot
          (skewGradientField (u i).toH1Function.grad j i x) (φ.grad x))
      (volumeMeasureOn U) :=
    integrable_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ => hterm i j
  have hpoint :
      (fun x => vecDot (h10SkewMatrixDiv u q x) (φ.grad x)) =
      fun x => h10SkewDimInv d * ∑ i : Fin d, ∑ j : Fin d,
        q j * vecDot
          (skewGradientField (u i).toH1Function.grad j i x) (φ.grad x) := by
    funext x
    rw [h10SkewMatrixDiv, vecDot_smul_left,
      vecDot_finsetSum_left Finset.univ]
    simp_rw [vecDot_finsetSum_left]
    simp only [vecDot_smul_left]
  rw [hpoint, integral_const_mul]
  have hintegral :
      (∫ x in U, ∑ i : Fin d, ∑ j : Fin d,
        q j * vecDot
          (skewGradientField (u i).toH1Function.grad j i x) (φ.grad x)
        ∂volume) = 0 := by
    rw [integral_finsetSum]
    · refine Finset.sum_eq_zero fun i _ => ?_
      rw [integral_finsetSum]
      · refine Finset.sum_eq_zero fun j _ => ?_
        rw [integral_const_mul,
          integral_skewGradientField_pairing_eq_zero, mul_zero]
      · intro j _
        exact hterm i j
    · intro i _
      exact integrable_finsetSum _ fun j _ => hterm i j
  rw [hintegral, mul_zero]

/-- The weak divergence of the antisymmetric `H¹₀` matrix belongs to the
public `L²` solenoidal space with zero normal trace. -/
theorem solenoidalZeroNormalTraceFieldOn_h10SkewMatrixDiv
    {U : Set (Vec d)} (u : Fin d → H10Function U) (q : Vec d) :
    Book.Ch01.SolenoidalZeroNormalTraceFieldOn U (h10SkewMatrixDiv u q) :=
  ⟨memVectorL2_h10SkewMatrixDiv u q,
    h10SkewMatrixDiv_isSolenoidalZeroNormalTraceOn u q⟩

/-- The public zero-normal solenoidal predicate is insensitive to changing the
vector field almost everywhere on its domain. -/
theorem solenoidalZeroNormalTraceFieldOn_congr_ae {U : Set (Vec d)}
    {f g : Vec d → Vec d} (hfg : f =ᵐ[volumeMeasureOn U] g)
    (hf : Book.Ch01.SolenoidalZeroNormalTraceFieldOn U f) :
    Book.Ch01.SolenoidalZeroNormalTraceFieldOn U g := by
  refine ⟨MeasureTheory.MemLp.ae_eq hfg hf.1, ?_⟩
  intro φ
  calc
    ∫ x in U, vecDot (g x) (φ.grad x) ∂volume =
        ∫ x in U, vecDot (f x) (φ.grad x) ∂volume := by
          refine integral_congr_ae ?_
          filter_upwards [hfg] with x hx
          rw [← hx]
    _ = 0 := hf.2 φ

end

end Algsuperdiff.Section3.Provider.Affine
