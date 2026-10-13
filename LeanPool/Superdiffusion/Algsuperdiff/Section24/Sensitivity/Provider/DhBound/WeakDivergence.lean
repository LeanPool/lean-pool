/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.DhBound.SkewCancellation
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.EuclideanL2CZ

/-!
# WeakDivergence

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Weak product rule and the divergence-free skew test field

Source: ABK26 (`e.sensitivity.basic.split`), preparation for the genuine weak
integration by parts.

For a smooth compactly supported `φ` and an a.e. antisymmetric matrix field
`h` with weak first derivatives `Dh`, the auxiliary vector field

  `t_j := ∑ i (∂_i φ · h_{ij} + φ · ∂_i h_{ij})`  (weakly, `t_j = ∑ i ∂_i (φ h_{ij})`)

is divergence free in the weak sense: it annihilates every smooth compactly
supported test gradient.  This is the structural mechanism behind the paper's
integration by parts `⨍ ∇u · h ∇w = -⨍ u (∇·h) · ∇w`, and it isolates the
step where antisymmetry of `h` meets the symmetry of a second derivative.

This module proves:

* `integrable_memScalarL2_mul_of_bounded`, `memScalarL2_bounded_mul` —
  integrability bookkeeping for `L²` fields against bounded continuous factors
  on a finite-volume carrier;
* `hasWeakPartialDerivOn_smooth_mul` — the weak Leibniz rule
  `∂_i (φ f) = ∂_i φ · f + φ · ∂_i f` for smooth compactly supported `φ`;
* `sum_integral_skewTestField_mul_deriv_eq_zero` — weak divergence-freeness of
  the skew test field against smooth compactly supported tests.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.DhBound

open HCPolySupport MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- An `L²` field times a bounded continuous factor is integrable on a
finite-volume carrier. -/
theorem integrable_memScalarL2_mul_of_bounded {U : Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn U)]
    {f g : Vec d → ℝ} (hf : MemScalarL2 U f) (hgc : Continuous g)
    {C : ℝ} (hgb : ∀ x, |g x| ≤ C) :
    Integrable (fun x => f x * g x) (volumeMeasureOn U) := by
  have hg_top : MemLp g ∞ (volumeMeasureOn U) :=
    memLp_top_of_bound hgc.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun x => by
        simpa [Real.norm_eq_abs] using hgb x)
  have h2 : MemLp (fun x => g x * f x) 2 (volumeMeasureOn U) := hg_top.fun_mul (r := 2) hf
  have h1 : Integrable (fun x => g x * f x) (volumeMeasureOn U) :=
    h2.integrable (by norm_num)
  simpa [mul_comm] using h1

/-- A bounded continuous factor preserves `L²` membership. -/
theorem memScalarL2_bounded_mul {U : Set (Vec d)}
    {f g : Vec d → ℝ} (hf : MemScalarL2 U f) (hgc : Continuous g)
    {C : ℝ} (hgb : ∀ x, |g x| ≤ C) :
    MemScalarL2 U (fun x => g x * f x) := by
  have hg_top : MemLp g ∞ (volumeMeasureOn U) :=
    memLp_top_of_bound hgc.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun x => by
        simpa [Real.norm_eq_abs] using hgb x)
  exact hg_top.fun_mul (r := 2) hf

/-- Global bound for a continuous compactly supported function. -/
theorem exists_abs_bound_of_continuous_of_hasCompactSupport
    {g : Vec d → ℝ} (hgc : Continuous g) (hgs : HasCompactSupport g) :
    ∃ C : ℝ, ∀ x, |g x| ≤ C := by
  obtain ⟨C, hC⟩ := hgs.exists_bound_of_continuous hgc
  exact ⟨C, fun x => by simpa [Real.norm_eq_abs] using hC x⟩

/-- **Weak Leibniz rule.**  If `f` has weak `i`-th partial derivative `fi` on
`U` and `φ` is smooth and compactly supported, then `φ f` has weak `i`-th
partial derivative `∂_i φ · f + φ · fi` on `U`. -/
theorem hasWeakPartialDerivOn_smooth_mul {U : Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn U)]
    {i : Fin d} {f fi : Vec d → ℝ}
    (hf2 : MemScalarL2 U f) (hfi2 : MemScalarL2 U fi)
    (hf : HasWeakPartialDerivOn U i f fi)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) :
    HasWeakPartialDerivOn U i (fun x => φ x * f x)
      (fun x => euclideanCoordDeriv i φ x * f x + φ x * fi x) := by
  intro ψ hψ hψc hψsub
  have hχ : ContDiff ℝ (⊤ : ℕ∞) (fun x => φ x * ψ x) := hφ.mul hψ
  have hχc : HasCompactSupport (fun x => φ x * ψ x) := by
    exact hψc.mul_left
  have hχsub : tsupport (fun x => φ x * ψ x) ⊆ U := by
    refine subset_trans ?_ hψsub
    exact tsupport_mul_subset_right (f := φ) (g := ψ)
  have hkey := hf _ hχ hχc hχsub
  -- expand the derivative of the product test
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hprod : ∀ x : Vec d,
      (fderiv ℝ (fun y => φ y * ψ y) x) (basisVec i) =
        φ x * euclideanCoordDeriv i ψ x + ψ x * euclideanCoordDeriv i φ x := by
    intro x
    have hfd : fderiv ℝ (fun y => φ y * ψ y) x = fderiv ℝ (φ * ψ) x := rfl
    rw [hfd, fderiv_mul (hφd x) (hψd x)]
    simp [euclideanCoordDeriv]
  -- bounded continuous factors
  have hφ_cont : Continuous φ := hφ.continuous
  have hψ_cont : Continuous ψ := hψ.continuous
  have hdφ_cont : Continuous (euclideanCoordDeriv i φ) :=
    (contDiff_euclideanCoordDeriv hφ i).continuous
  have hdψ_cont : Continuous (euclideanCoordDeriv i ψ) :=
    (contDiff_euclideanCoordDeriv hψ i).continuous
  obtain ⟨C₁, hC₁⟩ :=
    exists_abs_bound_of_continuous_of_hasCompactSupport
      (hφ_cont.mul hdψ_cont) (HasCompactSupport.mul_right hφc)
  obtain ⟨C₂, hC₂⟩ :=
    exists_abs_bound_of_continuous_of_hasCompactSupport
      (hψ_cont.mul hdφ_cont) (HasCompactSupport.mul_right hψc)
  obtain ⟨C₃, hC₃⟩ :=
    exists_abs_bound_of_continuous_of_hasCompactSupport
      (hφ_cont.mul hψ_cont) (HasCompactSupport.mul_right hφc)
  obtain ⟨C₄, hC₄⟩ :=
    exists_abs_bound_of_continuous_of_hasCompactSupport
      (hdφ_cont.mul hψ_cont)
      (by
        have := hasCompactSupport_euclideanCoordDeriv hφc i
        exact this.mul_right)
  -- the six named integrals
  set A : ℝ := ∫ x in U, f x * (φ x * euclideanCoordDeriv i ψ x)
      ∂MeasureTheory.volume with hA
  set B : ℝ := ∫ x in U, f x * (ψ x * euclideanCoordDeriv i φ x)
      ∂MeasureTheory.volume with hB
  set Cint : ℝ := ∫ x in U, fi x * (φ x * ψ x) ∂MeasureTheory.volume with hCint
  have hintA : Integrable (fun x => f x * (φ x * euclideanCoordDeriv i ψ x))
      (volumeMeasureOn U) :=
    integrable_memScalarL2_mul_of_bounded hf2 (hφ_cont.mul hdψ_cont) hC₁
  have hintB : Integrable (fun x => f x * (ψ x * euclideanCoordDeriv i φ x))
      (volumeMeasureOn U) :=
    integrable_memScalarL2_mul_of_bounded hf2 (hψ_cont.mul hdφ_cont) hC₂
  have hintC : Integrable (fun x => fi x * (φ x * ψ x))
      (volumeMeasureOn U) :=
    integrable_memScalarL2_mul_of_bounded hfi2 (hφ_cont.mul hψ_cont) hC₃
  -- key identity in the normal form `A + B = -Cint`
  have hkey' : A + B = -Cint := by
    have hleft :
        (∫ x in U, f x * (fderiv ℝ (fun y => φ y * ψ y) x) (basisVec i)
            ∂MeasureTheory.volume) = A + B := by
      have hsplit :
          (fun x => f x * (fderiv ℝ (fun y => φ y * ψ y) x) (basisVec i)) =
            fun x => f x * (φ x * euclideanCoordDeriv i ψ x) +
              f x * (ψ x * euclideanCoordDeriv i φ x) := by
        funext x
        rw [hprod x]
        ring
      rw [hsplit]
      exact integral_add hintA hintB
    rw [hleft] at hkey
    linarith
  -- assemble the goal from the normal forms
  have hgoal_left :
      (∫ x in U, (fun x => φ x * f x) x * (fderiv ℝ ψ x) (basisVec i)
          ∂MeasureTheory.volume) = A := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show φ x * f x * (fderiv ℝ ψ x) (basisVec i) =
      f x * (φ x * euclideanCoordDeriv i ψ x)
    unfold euclideanCoordDeriv
    ring
  have hgoal_right :
      (∫ x in U,
          (fun x => euclideanCoordDeriv i φ x * f x + φ x * fi x) x * ψ x
          ∂MeasureTheory.volume) = B + Cint := by
    have hsplit :
        (fun x => (euclideanCoordDeriv i φ x * f x + φ x * fi x) * ψ x) =
          fun x => f x * (ψ x * euclideanCoordDeriv i φ x) +
            fi x * (φ x * ψ x) := by
      funext x
      ring
    calc
      (∫ x in U,
          (fun x => euclideanCoordDeriv i φ x * f x + φ x * fi x) x * ψ x
            ∂MeasureTheory.volume)
          = ∫ x in U, (fun x => f x * (ψ x * euclideanCoordDeriv i φ x) +
              fi x * (φ x * ψ x)) x ∂MeasureTheory.volume := by rw [hsplit]
      _ = B + Cint := integral_add hintB hintC
  rw [hgoal_left, hgoal_right]
  linarith

/-- The skew test field `t_j = ∑ i (∂_i φ · h_{ij} + φ · ∂_i h_{ij})` attached
to a smooth compactly supported `φ` and weak derivative data `Dh` for `h`. -/
def skewTestField (h : Vec d → Mat d) (Dh : Fin d → Vec d → Mat d)
    (φ : Vec d → ℝ) (x : Vec d) : Vec d :=
  fun j => ∑ i, (euclideanCoordDeriv i φ x * h x i j + φ x * Dh i x i j)

/-- Each summand of the skew test field is square integrable. -/
theorem memScalarL2_skewTestField_summand {U : Set (Vec d)}
    {h : Vec d → Mat d} {Dh : Fin d → Vec d → Mat d}
    (hmem : ∀ i j, MemScalarL2 U fun x => h x i j)
    (hDmem : ∀ k i j, MemScalarL2 U fun x => Dh k x i j)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (i j : Fin d) :
    MemScalarL2 U
      (fun x => euclideanCoordDeriv i φ x * h x i j + φ x * Dh i x i j) := by
  obtain ⟨C₁, hC₁⟩ :=
    exists_abs_bound_of_continuous_of_hasCompactSupport
      (contDiff_euclideanCoordDeriv hφ i).continuous
      (hasCompactSupport_euclideanCoordDeriv hφc i)
  obtain ⟨C₂, hC₂⟩ :=
    exists_abs_bound_of_continuous_of_hasCompactSupport hφ.continuous hφc
  exact (memScalarL2_bounded_mul (hmem i j)
      (contDiff_euclideanCoordDeriv hφ i).continuous hC₁).add
    (memScalarL2_bounded_mul (hDmem i i j) hφ.continuous hC₂)

/-- The skew test field is coordinatewise square integrable. -/
theorem memScalarL2_skewTestField {U : Set (Vec d)}
    {h : Vec d → Mat d} {Dh : Fin d → Vec d → Mat d}
    (hmem : ∀ i j, MemScalarL2 U fun x => h x i j)
    (hDmem : ∀ k i j, MemScalarL2 U fun x => Dh k x i j)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (j : Fin d) :
    MemScalarL2 U (fun x => skewTestField h Dh φ x j) := by
  have hsum : MemLp
      (fun x => ∑ i, (euclideanCoordDeriv i φ x * h x i j + φ x * Dh i x i j)) 2
      (volumeMeasureOn U) :=
    memLp_finsetSum (s := Finset.univ)
      (f := fun i => fun x =>
        euclideanCoordDeriv i φ x * h x i j + φ x * Dh i x i j)
      fun i _ => memScalarL2_skewTestField_summand hmem hDmem hφ hφc i j
  simpa [skewTestField] using hsum

/-- The skew test field vanishes off the support of `φ`. -/
theorem skewTestField_eq_zero_of_notMem_tsupport
    {h : Vec d → Mat d} {Dh : Fin d → Vec d → Mat d}
    {φ : Vec d → ℝ} {x : Vec d} (hx : x ∉ tsupport φ) :
    skewTestField h Dh φ x = 0 := by
  have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
  have hdφx : ∀ i : Fin d, euclideanCoordDeriv i φ x = 0 := by
    intro i
    have hxsupp : x ∉ tsupport (euclideanCoordDeriv i φ) := fun hmem =>
      hx (tsupport_euclideanCoordDeriv_subset_tsupport (u := φ) (i := i) hmem)
    exact image_eq_zero_of_notMem_tsupport hxsupp
  funext j
  simp [skewTestField, hφx, hdφx]

/-- **Weak divergence-freeness of the skew test field.**  For a.e.
antisymmetric `h` with weak first derivatives `Dh`, a smooth compactly
supported `φ` with support in `U`, and every smooth compactly supported test
`ψ` with support in `U`,

  `∑ j ∫ t_j ∂_j ψ = 0`,  `t_j = ∑ i (∂_i φ h_{ij} + φ ∂_i h_{ij})`.

The proof pairs the weak Leibniz rule with the second-derivative symmetry of
`ψ`, so that the antisymmetry of `h` cancels the resulting Hessian pairing. -/
theorem sum_integral_skewTestField_mul_deriv_eq_zero {U : Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn U)]
    {h : Vec d → Mat d} {Dh : Fin d → Vec d → Mat d}
    (hskew : ∀ᵐ x ∂ volumeMeasureOn U, symmPart (h x) = 0)
    (hmem : ∀ i j, MemScalarL2 U fun x => h x i j)
    (hDmem : ∀ k i j, MemScalarL2 U fun x => Dh k x i j)
    (hweak : ∀ k i j,
      HasWeakPartialDerivOn U k (fun x => h x i j) fun x => Dh k x i j)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hψsub : tsupport ψ ⊆ U) :
    ∑ j, ∫ x in U, skewTestField h Dh φ x j * euclideanCoordDeriv j ψ x
        ∂MeasureTheory.volume = 0 := by
  classical
  -- bounded continuous factors built from ψ
  have hdψ_cont : ∀ j : Fin d, Continuous (euclideanCoordDeriv j ψ) := fun j =>
    (contDiff_euclideanCoordDeriv hψ j).continuous
  have hdψ_bound : ∀ j : Fin d, ∃ C : ℝ, ∀ x, |euclideanCoordDeriv j ψ x| ≤ C :=
    fun j =>
      exists_abs_bound_of_continuous_of_hasCompactSupport (hdψ_cont j)
        (hasCompactSupport_euclideanCoordDeriv hψc j)
  -- split each coordinate integral into its (i, j) summands
  have hsplit : ∀ j : Fin d,
      (∫ x in U, skewTestField h Dh φ x j * euclideanCoordDeriv j ψ x
          ∂MeasureTheory.volume) =
        ∑ i, ∫ x in U,
          (euclideanCoordDeriv i φ x * h x i j + φ x * Dh i x i j) *
            euclideanCoordDeriv j ψ x ∂MeasureTheory.volume := by
    intro j
    obtain ⟨C, hC⟩ := hdψ_bound j
    have hexp :
        (fun x => skewTestField h Dh φ x j * euclideanCoordDeriv j ψ x) =
          fun x => ∑ i,
            (euclideanCoordDeriv i φ x * h x i j + φ x * Dh i x i j) *
              euclideanCoordDeriv j ψ x := by
      funext x
      rw [skewTestField, Finset.sum_mul]
    rw [hexp]
    exact integral_finsetSum Finset.univ fun i _ =>
      integrable_memScalarL2_mul_of_bounded
        (memScalarL2_skewTestField_summand hmem hDmem hφ hφc i j)
        (hdψ_cont j) hC
  -- rewrite each (i, j) summand by the weak Leibniz rule against `∂_j ψ`
  have hterm : ∀ i j : Fin d,
      (∫ x in U,
          (euclideanCoordDeriv i φ x * h x i j + φ x * Dh i x i j) *
            euclideanCoordDeriv j ψ x ∂MeasureTheory.volume) =
        -∫ x in U, φ x * h x i j * euclideanCoordSecondDeriv j i ψ x
          ∂MeasureTheory.volume := by
    intro i j
    have hleib :
        HasWeakPartialDerivOn U i (fun x => φ x * h x i j)
          (fun x => euclideanCoordDeriv i φ x * h x i j + φ x * Dh i x i j) :=
      hasWeakPartialDerivOn_smooth_mul (hmem i j) (hDmem i i j)
        (hweak i i j) hφ hφc
    have htest := hleib (euclideanCoordDeriv j ψ)
      (contDiff_euclideanCoordDeriv hψ j)
      (hasCompactSupport_euclideanCoordDeriv hψc j)
      (subset_trans
        (tsupport_euclideanCoordDeriv_subset_tsupport (u := ψ) (i := j)) hψsub)
    have hsecond :
        (∫ x in U, (fun x => φ x * h x i j) x *
            (fderiv ℝ (euclideanCoordDeriv j ψ) x) (basisVec i)
            ∂MeasureTheory.volume) =
          ∫ x in U, φ x * h x i j * euclideanCoordSecondDeriv j i ψ x
            ∂MeasureTheory.volume := rfl
    rw [hsecond] at htest
    linarith [htest]
  -- assemble and cancel via the skew algebra
  have hswap :
      (∑ j, ∑ i, -∫ x in U,
          φ x * h x i j * euclideanCoordSecondDeriv j i ψ x
          ∂MeasureTheory.volume) =
        -∫ x in U,
          φ x * ∑ i, ∑ j, h x i j * euclideanCoordSecondDeriv j i ψ x
          ∂MeasureTheory.volume := by
    have hint : ∀ i j : Fin d,
        Integrable
          (fun x => φ x * h x i j * euclideanCoordSecondDeriv j i ψ x)
          (volumeMeasureOn U) := by
      intro i j
      obtain ⟨C₂, hC₂⟩ :=
        exists_abs_bound_of_continuous_of_hasCompactSupport hφ.continuous hφc
      obtain ⟨C₃, hC₃⟩ :=
        exists_abs_bound_of_continuous_of_hasCompactSupport
          (contDiff_euclideanCoordSecondDeriv hψ j i).continuous
          (hasCompactSupport_euclideanCoordSecondDeriv hψc j i)
      have hbase : MemScalarL2 U (fun x => φ x * h x i j) :=
        memScalarL2_bounded_mul (hmem i j) hφ.continuous hC₂
      exact integrable_memScalarL2_mul_of_bounded hbase
        (contDiff_euclideanCoordSecondDeriv hψ j i).continuous hC₃
    calc
      (∑ j, ∑ i, -∫ x in U,
          φ x * h x i j * euclideanCoordSecondDeriv j i ψ x
          ∂MeasureTheory.volume)
          = -∑ j, ∑ i, ∫ x in U,
              φ x * h x i j * euclideanCoordSecondDeriv j i ψ x
              ∂MeasureTheory.volume := by
            rw [← Finset.sum_neg_distrib]
            exact Finset.sum_congr rfl fun j _ => by
              rw [← Finset.sum_neg_distrib]
      _ = -∫ x in U, ∑ j, ∑ i,
              φ x * h x i j * euclideanCoordSecondDeriv j i ψ x
              ∂MeasureTheory.volume := by
            congr 1
            calc
              (∑ j, ∑ i, ∫ x in U,
                  φ x * h x i j * euclideanCoordSecondDeriv j i ψ x
                  ∂MeasureTheory.volume)
                  = ∑ j, ∫ x in U, ∑ i,
                      φ x * h x i j * euclideanCoordSecondDeriv j i ψ x
                      ∂MeasureTheory.volume :=
                    Finset.sum_congr rfl fun j _ =>
                      (integral_finsetSum Finset.univ fun i _ => hint i j).symm
              _ = ∫ x in U, ∑ j, ∑ i,
                      φ x * h x i j * euclideanCoordSecondDeriv j i ψ x
                      ∂MeasureTheory.volume :=
                    (integral_finsetSum Finset.univ fun j _ =>
                      integrable_finsetSum Finset.univ fun i _ => hint i j).symm
      _ = -∫ x in U,
              φ x * ∑ i, ∑ j, h x i j * euclideanCoordSecondDeriv j i ψ x
              ∂MeasureTheory.volume := by
            congr 1
            refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
            show
              (∑ j, ∑ i, φ x * h x i j * euclideanCoordSecondDeriv j i ψ x) =
                φ x * ∑ i, ∑ j, h x i j * euclideanCoordSecondDeriv j i ψ x
            rw [Finset.mul_sum, Finset.sum_comm]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun j _ => by ring
  have hzero :
      (∫ x in U,
          φ x * ∑ i, ∑ j, h x i j * euclideanCoordSecondDeriv j i ψ x
          ∂MeasureTheory.volume) = 0 := by
    have hae :
        (fun x =>
            φ x * ∑ i, ∑ j, h x i j * euclideanCoordSecondDeriv j i ψ x)
          =ᵐ[volumeMeasureOn U] fun _ => (0 : ℝ) := by
      filter_upwards [hskew] with x hx
      have hcancel :
          (∑ i, ∑ j, h x i j *
            (fun i j : Fin d => euclideanCoordSecondDeriv j i ψ x) i j) = 0 :=
        sum_entry_mul_eq_zero_of_symmPart_eq_zero hx fun i j =>
          congrFun (euclideanCoordSecondDeriv_comm_fun hψ j i) x
      calc
        φ x * ∑ i, ∑ j, h x i j * euclideanCoordSecondDeriv j i ψ x =
            φ x * 0 := by rw [← hcancel]
        _ = 0 := mul_zero _
    rw [integral_congr_ae hae]
    simp
  calc
    (∑ j, ∫ x in U, skewTestField h Dh φ x j * euclideanCoordDeriv j ψ x
        ∂MeasureTheory.volume)
        = ∑ j, ∑ i, ∫ x in U,
            (euclideanCoordDeriv i φ x * h x i j + φ x * Dh i x i j) *
              euclideanCoordDeriv j ψ x ∂MeasureTheory.volume :=
          Finset.sum_congr rfl fun j _ => hsplit j
    _ = ∑ j, ∑ i, -∫ x in U,
            φ x * h x i j * euclideanCoordSecondDeriv j i ψ x
            ∂MeasureTheory.volume :=
          Finset.sum_congr rfl fun j _ =>
            Finset.sum_congr rfl fun i _ => hterm i j
    _ = -∫ x in U,
            φ x * ∑ i, ∑ j, h x i j * euclideanCoordSecondDeriv j i ψ x
            ∂MeasureTheory.volume := hswap
    _ = 0 := by rw [hzero]; ring

end

end Algsuperdiff.Section24.Sensitivity.Provider.DhBound
