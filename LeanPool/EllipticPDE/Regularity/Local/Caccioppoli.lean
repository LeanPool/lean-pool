/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Regularity.Local.WeakSolution


/-!
# Caccioppoli estimate for a weak solution in `H¹`

`caccioppoli` bounds the cutoff-weighted gradient energy of a weak solution in `H₀¹(Ω)` by
`‖f‖² + ‖u‖²`. Its proof tests the equation with `ζ² u`, and that test function is admissible
for a local weak solution `U ∈ W12 Ω` as well (`cutoffMul_mem_H01_of_mem_W12`), with the
identity against it supplied by `IsLocalWeakSolution.weakForm`. Nothing else in the proof uses
the boundary condition, so the statement holds for `W12` solutions with the same constant.

This is the step Evans, *Partial Differential Equations* (2nd ed.), §6.3.1, Theorem 1 takes in
the proof before (8) to replace `‖u‖_{H¹(U)}` by `‖u‖_{L²(U)}` on the right of the estimate.

## Main declarations

* `caccioppoli_W12`: the energy estimate.
* `exists_norm_mulTest_grad_le`: its consequence for each gradient coordinate, with the norms
  unsquared.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ}

/-- **Caccioppoli estimate for a weak solution in `H¹`.** For a local weak solution
`U ∈ W12 Ω` of `L U = f` on an open `Ω`, with no boundary condition, and a test function `ζ` of
`Ω`, the cutoff-weighted gradient energy `(λ/2) Σ ‖ζ ∂_i U‖²` is bounded by
`C (‖f‖² + ‖U₀‖²)`, with `C` quantified before the solution and the datum. The proof is that of
`caccioppoli`, with `IsLocalWeakSolution.weakForm` against `ζ² U` in place of the `H₀¹` weak
formulation. -/
theorem caccioppoli_W12 (Op : FullEllipticOp d) {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩo : IsOpen Ω) {ζ : EuclideanSpace ℝ (Fin d) → ℝ} (hζ : IsTestFn Ω ζ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : H1amb Ω) (f : L2D Ω), IsLocalWeakSolution Op Ω U f →
      Op.lam / 2 * ∑ i : Fin d, ‖mulTest hζ (U i.succ)‖ ^ 2
        ≤ C * (‖f‖ ^ 2 + ‖U 0‖ ^ 2) := by
  classical
  set A := Op.toEllipticCoeff with hA
  set Z : ℝ := (exists_abs_bound hζ).choose with hZ
  set Z2 : ℝ := (exists_abs_bound (isTestFn_mul hζ hζ)).choose with hZ2
  set SW : ℝ := ∑ j : Fin d, (exists_abs_bound_partialD hζ j).choose with hSW
  set β : ℝ := 2 * A.Λ * SW + Op.Bsup * Z with hβ
  have hZ2n : (0 : ℝ) ≤ Z2 :=
    le_trans (abs_nonneg _) ((exists_abs_bound (isTestFn_mul hζ hζ)).choose_spec 0)
  -- The constant, fixed before the solution and the datum.
  have hβn : (0 : ℝ) ≤ (d : ℝ) * β ^ 2 / (2 * A.lam) :=
    div_nonneg (by positivity) (by have := A.lam_pos; linarith)
  have hCu : (0 : ℝ) ≤ Z2 ^ 2 / 2 + (d : ℝ) * β ^ 2 / (2 * A.lam) + Op.Csup * Z2 :=
    by linarith [hβn, mul_nonneg Op.Csup_nonneg hZ2n, sq_nonneg Z2]
  refine ⟨1 / 2 + Z2 ^ 2 / 2 + (d : ℝ) * β ^ 2 / (2 * A.lam) + Op.Csup * Z2,
    by linarith, ?_⟩
  intro U f hsol
  set V : H1amb Ω := cutoffMul (isTestFn_mul hζ hζ) U with hVdef
  have hVmem : V ∈ H01 Ω := cutoffMul_mem_H01_of_mem_W12 hΩo (isTestFn_mul hζ hζ) hsol.1
  set E : ℝ := ∑ i : Fin d, ‖mulTest hζ (U i.succ)‖ ^ 2 with hE
  -- Coordinate values of the test element `ζ² u`.
  have hv0 : V 0 = mulTest (isTestFn_mul hζ hζ) (U 0) := by
    change cutoffMul (isTestFn_mul hζ hζ) U 0 = _
    rw [cutoffMul_apply_zero]
  have hv0succ : ∀ j : Fin d, V j.succ
      = mulTest (isTestFn_mul hζ hζ) (U j.succ)
        + mulTestPartial (isTestFn_mul hζ hζ) j (U 0) := by
    intro j
    change cutoffMul (isTestFn_mul hζ hζ) U j.succ = _
    rw [cutoffMul_apply_succ]
  -- Principal expansion of the bilinear form on `ζ² u`.
  have hbil : (∑ i : Fin d, ∑ j : Fin d, ⟪A.actL i j (U i.succ), V j.succ⟫)
      = (∑ i : Fin d, ∑ j : Fin d,
          ⟪A.actL i j (U i.succ),
            mulTest (isTestFn_mul hζ hζ) (U j.succ)⟫)
        + ∑ i : Fin d, ∑ j : Fin d,
          ⟪A.actL i j (U i.succ),
            mulTestPartial (isTestFn_mul hζ hζ) j (U 0)⟫ := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hv0succ j, inner_add_right]
  -- Ellipticity lower bound for the principal part after regrouping one `ζ`.
  have hen : A.lam * E
      ≤ ∑ i : Fin d, ∑ j : Fin d,
          ⟪A.actL i j (U i.succ),
            mulTest (isTestFn_mul hζ hζ) (U j.succ)⟫ := by
    calc A.lam * E
        = A.lam * ∑ i : Fin d, ‖mulTest hζ (U i.succ)‖ ^ 2 := by rw [hE]
      _ ≤ ∑ i : Fin d, ∑ j : Fin d,
            ⟪A.actL i j (mulTest hζ (U i.succ)),
              mulTest hζ (U j.succ)⟫ := by
          have h := energy_ge A (fun i => mulTest hζ (U i.succ))
          simpa using h
      _ = ∑ i : Fin d, ∑ j : Fin d,
            ⟪A.actL i j (U i.succ),
              mulTest (isTestFn_mul hζ hζ) (U j.succ)⟫ :=
          Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl
            (fun j _ => actL_mulTest_regroup A hζ i j _ _))
  -- Weak equation: the principal part equals data minus the lower-order form.
  have hweak : (∑ i : Fin d, ∑ j : Fin d, ⟪A.actL i j (U i.succ), V j.succ⟫)
      = (∫ x in Ω, (f x : ℝ) * (V 0 x : ℝ))
        - ((∑ i : Fin d, ⟪Op.bAct i (U i.succ),
              mulTest (isTestFn_mul hζ hζ) (U 0)⟫)
          + ⟪Op.cAct (U 0),
              mulTest (isTestFn_mul hζ hζ) (U 0)⟫) := by
    have hfb := pairL_apply Op U V
    rw [hsol.weakForm hVmem] at hfb
    simp only [← hA] at hfb
    have hlow : (∑ i : Fin d, ⟪Op.bAct i (U i.succ), V 0⟫) + ⟪Op.cAct (U 0), V 0⟫
        = (∑ i : Fin d, ⟪Op.bAct i (U i.succ),
              mulTest (isTestFn_mul hζ hζ) (U 0)⟫)
          + ⟪Op.cAct (U 0),
              mulTest (isTestFn_mul hζ hζ) (U 0)⟫ := by
      simp only [hv0]
    linarith [hfb, hlow]
  -- Right-hand side as an inner product, bounded by Cauchy-Schwarz and Young.
  have hRHSeq : (∫ x in Ω, (f x : ℝ) * (V 0 x : ℝ))
      = ⟪f, mulTest (isTestFn_mul hζ hζ) (U 0)⟫ := by
    rw [hv0, L2.inner_def]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [Real.inner_apply]
  have hRHSf : (∫ x in Ω, (f x : ℝ) * (V 0 x : ℝ))
      ≤ 1 / 2 * ‖f‖ ^ 2 + Z2 ^ 2 / 2 * ‖U 0‖ ^ 2 := by
    rw [hRHSeq]
    calc ⟪f, mulTest (isTestFn_mul hζ hζ) (U 0)⟫
        ≤ ‖f‖ * ‖mulTest (isTestFn_mul hζ hζ) (U 0)‖ := real_inner_le_norm _ _
      _ ≤ ‖f‖ * (Z2 * ‖U 0‖) :=
          mul_le_mul_of_nonneg_left (norm_mulTest_le (isTestFn_mul hζ hζ) _) (norm_nonneg _)
      _ = Z2 * ‖f‖ * ‖U 0‖ := by ring
      _ ≤ 1 / 2 * ‖f‖ ^ 2 + Z2 ^ 2 / 2 * ‖U 0‖ ^ 2 := by
          have hy := young_peterPaul (lam := 1) (B := Z2) (x := ‖f‖)
            (y := ‖U 0‖) one_pos
          have h2l : (2 : ℝ) * 1 = 2 := by norm_num
          rw [h2l] at hy
          linarith [hy]
  -- Zeroth-order term bounded (no absorption needed).
  have hZthbound :
      -(⟪Op.cAct (U 0),
          mulTest (isTestFn_mul hζ hζ) (U 0)⟫)
        ≤ Op.Csup * Z2 * ‖U 0‖ ^ 2 :=
    calc -(⟪Op.cAct (U 0),
            mulTest (isTestFn_mul hζ hζ) (U 0)⟫)
        ≤ |⟪Op.cAct (U 0),
            mulTest (isTestFn_mul hζ hζ) (U 0)⟫| := neg_le_abs _
      _ ≤ ‖Op.cAct (U 0)‖
            * ‖mulTest (isTestFn_mul hζ hζ) (U 0)‖ := abs_real_inner_le_norm _ _
      _ ≤ (Op.Csup * ‖U 0‖) * (Z2 * ‖U 0‖) :=
          mul_le_mul (Op.norm_cAct_le _) (norm_mulTest_le (isTestFn_mul hζ hζ) _)
            (norm_nonneg _) (mul_nonneg Op.Csup_nonneg (norm_nonneg _))
      _ = Op.Csup * Z2 * ‖U 0‖ ^ 2 := by ring
  -- Per-index absorption bound for the cross and transport terms.
  have hbnd : ∀ i : Fin d, (0 : ℝ) ≤
      (A.lam / 2 * ‖mulTest hζ (U i.succ)‖ ^ 2
        + β ^ 2 / (2 * A.lam) * ‖U 0‖ ^ 2)
      + ((∑ j : Fin d,
          ⟪A.actL i j (U i.succ),
            mulTestPartial (isTestFn_mul hζ hζ) j (U 0)⟫)
        + ⟪Op.bAct i (U i.succ),
            mulTest (isTestFn_mul hζ hζ) (U 0)⟫) := by
    exact caccioppoli_cross_transport_bound Op hζ hSW hβ U
  -- Sum the per-index bound to absorb the cross and transport totals.
  have hTsum : (0 : ℝ)
      ≤ (A.lam / 2 * E + (d : ℝ) * β ^ 2 / (2 * A.lam) * ‖U 0‖ ^ 2)
        + ((∑ i : Fin d, ∑ j : Fin d,
            ⟪A.actL i j (U i.succ),
              mulTestPartial (isTestFn_mul hζ hζ) j (U 0)⟫)
          + ∑ i : Fin d, ⟪Op.bAct i (U i.succ),
              mulTest (isTestFn_mul hζ hζ) (U 0)⟫) := by
    have hsum := Finset.sum_le_sum
      (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) => hbnd i)
    rw [Finset.sum_const_zero] at hsum
    calc (0 : ℝ)
        ≤ ∑ i : Fin d, ((A.lam / 2 * ‖mulTest hζ (U i.succ)‖ ^ 2
            + β ^ 2 / (2 * A.lam) * ‖U 0‖ ^ 2)
          + ((∑ j : Fin d,
              ⟪A.actL i j (U i.succ),
                mulTestPartial (isTestFn_mul hζ hζ) j (U 0)⟫)
            + ⟪Op.bAct i (U i.succ),
                mulTest (isTestFn_mul hζ hζ) (U 0)⟫)) := hsum
      _ = (A.lam / 2 * E + (d : ℝ) * β ^ 2 / (2 * A.lam) * ‖U 0‖ ^ 2)
          + ((∑ i : Fin d, ∑ j : Fin d,
              ⟪A.actL i j (U i.succ),
                mulTestPartial (isTestFn_mul hζ hζ) j (U 0)⟫)
            + ∑ i : Fin d, ⟪Op.bAct i (U i.succ),
                mulTest (isTestFn_mul hζ hζ) (U 0)⟫) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
            ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, ← hE]
          ring
  -- Assemble: the absorbed energy leaves the desired estimate.
  have hrel : A.lam * E = 2 * (A.lam / 2 * E) := by ring
  have hfin : A.lam / 2 * E
      ≤ 1 / 2 * ‖f‖ ^ 2 + Z2 ^ 2 / 2 * ‖U 0‖ ^ 2
        + (d : ℝ) * β ^ 2 / (2 * A.lam) * ‖U 0‖ ^ 2
        + Op.Csup * Z2 * ‖U 0‖ ^ 2 := by
    linarith [hen, hbil, hweak, hRHSf, hTsum, hZthbound, hrel]
  nlinarith [hfin, sq_nonneg ‖U 0‖, sq_nonneg ‖f‖,
    mul_nonneg hCu (sq_nonneg ‖f‖)]

/-- A term of a sum of squares, from a bound on the weighted sum, with the square root
taken. -/
theorem le_sqrt_mul_of_sum_sq_le {ι : Type*} [Fintype ι] (g : ι → ℝ) (hg : ∀ j, 0 ≤ g j)
    {lam C0 a b : ℝ} (hlam : 0 < lam) (hC0 : 0 ≤ C0) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : lam / 2 * ∑ j, g j ^ 2 ≤ C0 * (a ^ 2 + b ^ 2)) (i : ι) :
    g i ≤ Real.sqrt (2 * C0 / lam) * (a + b) := by
  have hC'0 : 0 ≤ 2 * C0 / lam := div_nonneg (by linarith) hlam.le
  have hsum : ∑ j, g j ^ 2 ≤ 2 * C0 / lam * (a ^ 2 + b ^ 2) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlam]
    linarith [h]
  have hi : g i ^ 2 ≤ ∑ j, g j ^ 2 :=
    Finset.single_le_sum (f := fun j => g j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have hsq : a ^ 2 + b ^ 2 ≤ (a + b) ^ 2 := by nlinarith
  have hkey : g i ^ 2 ≤ (Real.sqrt (2 * C0 / lam) * (a + b)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hC'0]
    exact hi.trans (hsum.trans (mul_le_mul_of_nonneg_left hsq hC'0))
  have h1 := Real.sqrt_le_sqrt hkey
  rwa [Real.sqrt_sq (hg i),
    Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _) (add_nonneg ha hb))] at h1

/-- **Cutoff gradient bounded by the function and the datum.** Each gradient coordinate of a
local weak solution, cut off by a test function `ζ`, is bounded in `L²(Ω)` by
`C (‖f‖ + ‖U₀‖)`: the square root of `caccioppoli_W12`. -/
theorem exists_norm_mulTest_grad_le (Op : FullEllipticOp d) {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩo : IsOpen Ω) {ζ : EuclideanSpace ℝ (Fin d) → ℝ} (hζ : IsTestFn Ω ζ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : H1amb Ω) (f : L2D Ω), IsLocalWeakSolution Op Ω U f →
      ∀ i : Fin d, ‖mulTest hζ (U i.succ)‖ ≤ C * (‖f‖ + ‖U 0‖) := by
  obtain ⟨C0, hC0, h⟩ := caccioppoli_W12 Op hΩo hζ
  exact ⟨_, Real.sqrt_nonneg _, fun U f hsol i =>
    le_sqrt_mul_of_sum_sq_le (fun j : Fin d => ‖mulTest hζ (U j.succ)‖) (fun _ => norm_nonneg _)
      Op.lam_pos hC0 (norm_nonneg f) (norm_nonneg (U 0)) (h U f hsol) i⟩

end EllipticPdes.Regularity
