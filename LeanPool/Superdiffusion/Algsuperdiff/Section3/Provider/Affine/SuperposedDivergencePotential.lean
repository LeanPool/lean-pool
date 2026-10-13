/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Affine.H10SkewDivergence
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Affine.SuperposedDivergence

/-!
# SuperposedDivergencePotential

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Solenoidality of the superposed divergence from potential basis defects

This file connects the geometric `G` field already defined in
`SuperposedDivergence.lean` to the model-free antisymmetric-divergence theorem
of `H10SkewDivergence.lean`.

The only analytic input is the internally produced `hFbasis` interface: each
basis-load slope defect is a public zero-trace potential field.  Choosing its
`H¹₀` witness identifies the superposed divergence defect almost everywhere
with `h10SkewMatrixDiv`; no continuity, local-finiteness, mesh, or trace
hypothesis is added here.
-/

namespace Algsuperdiff.Section3.Provider.Affine

open Filter HCPolySupport MeasureTheory
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-! ## Pointwise algebra -/

private theorem antisymmetricDivergence_sub_eq (hd : 2 ≤ d) (q : Vec d)
    (S : Fin d → Vec d) :
    (fun j => ∑ i, ((d : ℝ) - 1)⁻¹ * (q j * S i i - q i * S j i)) - q =
      fun j => ((d : ℝ) - 1)⁻¹ *
        ((∑ i, (S i - basisVec i) i) * q j -
          ∑ i, q i * (S j - basisVec j) i) := by
  have hdReal : (2 : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast hd
  have hdenom : ((d : ℝ) - 1) ≠ 0 := by
    intro h
    linarith
  have hdiag : ∑ i : Fin d, basisVec (d := d) i i = (d : ℝ) := by
    simp [basisVec_apply]
  have hrow : ∀ j : Fin d, ∑ i, q i * basisVec (d := d) j i = q j := by
    intro j
    rw [Finset.sum_eq_single j]
    · simp [basisVec_apply]
    · intro i _ hij
      simp [basisVec_apply, hij]
    · intro h
      exact absurd (Finset.mem_univ j) h
  funext j
  have hleft :
      ∑ i, ((d : ℝ) - 1)⁻¹ * (q j * S i i - q i * S j i) =
        ((d : ℝ) - 1)⁻¹ *
          (q j * (∑ i, S i i) - ∑ i, q i * S j i) := by
    have hterm : ∀ i : Fin d,
        ((d : ℝ) - 1)⁻¹ * (q j * S i i - q i * S j i) =
          ((d : ℝ) - 1)⁻¹ * q j * S i i -
            ((d : ℝ) - 1)⁻¹ * (q i * S j i) :=
      fun i => by ring
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hterm i),
      Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    ring
  have hslope :
      ∑ i, (S i - basisVec i) i = (∑ i, S i i) - (d : ℝ) := by
    simp only [Pi.sub_apply]
    rw [Finset.sum_sub_distrib, hdiag]
  have hweighted :
      ∑ i, q i * (S j - basisVec j) i = (∑ i, q i * S j i) - q j := by
    simp only [Pi.sub_apply, mul_sub]
    rw [Finset.sum_sub_distrib, hrow j]
  rw [Pi.sub_apply, hleft, hslope, hweighted]
  field_simp
  ring

/-- Pointwise deviation identity for the superposed divergence field.  With
`u_i = ∇ℓ̂_{e_i} - e_i`, it reads

```text
∇·D̂_q - q = (d-1)⁻¹ ((∑_i (u_i)_i) q - u_·ᵀ q).
```
-/
theorem superposedCompetitorDivergence_sub_eq (hd : 2 ≤ d) (m : ℤ)
    (hn : ℕ → ℕ) (I : Set (TriadicCube d)) (q : Vec d) (x : Vec d) :
    superposedCompetitorDivergence m hn I q x - q =
      fun j => ((d : ℝ) - 1)⁻¹ *
        ((∑ i,
            (superposedCompetitorSlope m hn I (basisVec i) x - basisVec i) i) * q j -
          ∑ i, q i *
            (superposedCompetitorSlope m hn I (basisVec j) x - basisVec j) i) := by
  change
    (fun j => ∑ i, ((d : ℝ) - 1)⁻¹ *
      (q j * superposedCompetitorSlope m hn I (basisVec i) x i -
        q i * superposedCompetitorSlope m hn I (basisVec j) x i)) - q = _
  exact antisymmetricDivergence_sub_eq hd q fun i =>
    superposedCompetitorSlope m hn I (basisVec i) x

/-! ## Conditional local `G`-leg A -/

/-- If every basis-load superposed slope defect is a public zero-trace
potential field on `U`, then the superposed divergence defect is a public
solenoidal field with zero normal trace on `U`.

The `hFbasis` premise is an internal producer interface.  It is the exact
finite family needed to construct the antisymmetric matrix; it is not an
additional hypothesis of any frozen theorem. -/
theorem superposedCompetitorDivergence_sub_solenoidalZeroNormalTraceFieldOn
    {U : Set (Vec d)} (hd : 2 ≤ d) (m : ℤ) (hn : ℕ → ℕ)
    (I : Set (TriadicCube d)) (q : Vec d)
    (hFbasis : ∀ i : Fin d,
      Book.Ch01.PotentialZeroTraceFieldOn U
        (fun x => superposedCompetitorSlope m hn I (basisVec i) x - basisVec i)) :
    Book.Ch01.SolenoidalZeroNormalTraceFieldOn U
      (fun x => superposedCompetitorDivergence m hn I q x - q) := by
  classical
  let u : Fin d → H10Function U := fun i => Classical.choose (hFbasis i).2
  have hu : ∀ i : Fin d,
      (fun x => superposedCompetitorSlope m hn I (basisVec i) x - basisVec i) =ᵐ[
        volumeMeasureOn U] (u i).toH1Function.grad := by
    intro i
    dsimp only [u]
    exact Classical.choose_spec (hFbasis i).2
  have hall : ∀ᵐ x ∂volumeMeasureOn U, ∀ i : Fin d,
      superposedCompetitorSlope m hn I (basisVec i) x - basisVec i =
        (u i).toH1Function.grad x :=
    ae_all_iff.mpr hu
  have hae :
      (fun x => superposedCompetitorDivergence m hn I q x - q) =ᵐ[
        volumeMeasureOn U] h10SkewMatrixDiv u q := by
    filter_upwards [hall] with x hx
    rw [superposedCompetitorDivergence_sub_eq hd]
    funext j
    rw [h10SkewMatrixDiv_apply]
    have hxcoord : ∀ i k : Fin d,
        (superposedCompetitorSlope m hn I (basisVec i) x - basisVec i) k =
          (u i).toH1Function.grad x k := by
      intro i k
      exact congrFun (hx i) k
    simp_rw [hxcoord]
    rw [h10SkewDimInv]
    ring
  refine solenoidalZeroNormalTraceFieldOn_congr_ae hae.symm ?_
  exact solenoidalZeroNormalTraceFieldOn_h10SkewMatrixDiv u q

/-- Arbitrary-load form of the conditional bridge.  It specializes the
potential hypothesis only at the basis vectors used by `D̂_q`. -/
theorem superposedCompetitorDivergence_sub_solenoidalZeroNormalTraceFieldOn_of_forall
    {U : Set (Vec d)} (hd : 2 ≤ d) (m : ℤ) (hn : ℕ → ℕ)
    (I : Set (TriadicCube d)) (q : Vec d)
    (hF : ∀ p : Vec d,
      Book.Ch01.PotentialZeroTraceFieldOn U
        (fun x => superposedCompetitorSlope m hn I p x - p)) :
    Book.Ch01.SolenoidalZeroNormalTraceFieldOn U
      (fun x => superposedCompetitorDivergence m hn I q x - q) :=
  superposedCompetitorDivergence_sub_solenoidalZeroNormalTraceFieldOn
    hd m hn I q fun i => hF (basisVec i)

end

end Algsuperdiff.Section3.Provider.Affine
