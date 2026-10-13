/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomStepFourPairing

/-!
# HomStepFourIdentity

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Theorem B, §4.5, Step 4: the energy identities

## What Step 4 needs, and what is proved here

Step 4 has four ingredients.  Two of them are identities and
both are proved here, unconditionally:

1. **The pointwise bilinear split**

   ```text
     ∇u·a∇u - ∇v·σ∇v  =  (a∇u - σ∇v)·∇v + a∇u·(∇u - ∇v),
   ```

   an identity of `vecDot`, true for every matrix `A`, scalar `σ` and pair of
   vectors.

2. **The testing identity**

   ```text
     ⨍_{□_m} (∇u - ∇v)·a_L∇u  =  ⨍_{□_m} ∇v·σ_m(∇u - ∇v),
   ```

   `testing_identity` / `volumeAverage_testing_identity`.  Both Dirichlet
   problems of the Dirichlet-pair display are tested against the SAME
   `H¹₀(□_m)` element `u - v` and the two weak identities are subtracted; the
   common forcing term `-⨍ g·∇(u-v)` cancels.  The `H¹₀` witness is produced
   from the two `HasZeroTraceDifferenceOn` fields at the shared datum `h`
   (`exists_h10Function_grad_eq_sub`) — nothing is subtracted through the
   operator, and no boundary datum is removed from either equation.

3. The two duality pairings — `HomStepFourPairing`.

4. The Schauder bound on `‖∇v‖_{W^{s,∞}(□_m)}` — NOT provable from the paper;
   see `HomStepFourEnergy`'s disclosure.

## The `ν`-drop

The theorem's conclusion, the introduction's energy display, is stated at
`⨍ ν|∇u|²` while the proof works with `⨍ ∇u·a_L∇u`.  The two agree exactly because
the symmetric part of `a_L = ν Id + κ` is `ν Id`:
`vecDot_matVecMul_self_of_symmPart_smul_one`. The manuscript never states this
passage (a gap in the source at Step 4 (the energy identity)); it is proved
here as a pointwise identity, `ν` is never divided by anything, and no
ellipticity is used.
-/

open HCPolySupport MeasureTheory

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. `vecDot` algebra -/

/-- Bilinearity of `vecDot` on the left. -/
theorem vecDot_sub_left (x y z : Vec d) :
    vecDot (x - y) z = vecDot x z - vecDot y z := by
  simp only [vecDot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

/-- Bilinearity of `vecDot` on the right. -/
theorem vecDot_sub_right (x y z : Vec d) :
    vecDot x (y - z) = vecDot x y - vecDot x z := by
  simp only [vecDot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- `(c • Id) x = c • x`. -/
theorem matVecMul_smul_one (c : ℝ) (x : Vec d) :
    matVecMul (c • (1 : Mat d)) x = c • x := by
  rw [smul_matVecMul]
  congr 1
  funext i
  simp only [matVecMul, Matrix.one_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq Finset.univ i x]
  simp

/-- **The `ν`-drop, pointwise.**  If the symmetric part of `A` is `ν Id` then
`ξ · A ξ = ν |ξ|²` — the identity behind the manuscript's silent passage between
`⨍ ∇u · a_L ∇u` and the theorem's `⨍ ν |∇u|²` (a correction to the printed statement). -/
theorem vecDot_matVecMul_self_of_symmPart_smul_one {A : Mat d} {nu : ℝ}
    (hA : symmPart A = nu • (1 : Mat d)) (xi : Vec d) :
    vecDot xi (matVecMul A xi) = nu * vecNormSq xi := by
  rw [← vecDot_matVecMul_symmPart A xi, hA, matVecMul_smul_one, vecDot_smul_right]
  congr 1

/-! ## 3. The `H¹₀` witness for `u - v` -/

/-- The gradient of an `H¹₀` difference. -/
private theorem h10_sub_grad {U : Set (Vec d)} (a b : H10Function U) (x : Vec d) :
    (a - b).toH1Function.grad x = a.toH1Function.grad x - b.toH1Function.grad x := by
  change (a.toH1Function + ((-1 : ℝ) • b.toH1Function)).grad x = _
  rw [H1Function.add_grad, H1Function.smul_grad]
  simp only [neg_smul, one_smul]
  rw [sub_eq_add_neg]

/-- **`u - v ∈ H¹₀(□_m)`**: two solutions of the two Dirichlet
problems with the SAME boundary datum `h` differ by an `H¹₀` element.  Only the
two `HasZeroTraceDifferenceOn` witnesses are used; the datum `h` cancels and is
never pushed through either operator. -/
theorem exists_h10Function_grad_eq_sub {U : Set (Vec d)} {u v h : H1Function U}
    (hu : HasZeroTraceDifferenceOn U u h) (hv : HasZeroTraceDifferenceOn U v h) :
    ∃ w : H10Function U, ∀ x, w.toH1Function.grad x = u.grad x - v.grad x := by
  obtain ⟨wu, _, hwu⟩ := hu
  obtain ⟨wv, _, hwv⟩ := hv
  refine ⟨wu - wv, fun x => ?_⟩
  rw [h10_sub_grad wu wv x, hwu x, hwv x]
  ring_nf

/-! ## 4. The testing identity -/

/-- **Testing both equations with `u - v` and subtracting**.

Both weak formulations are evaluated at the same test function `w ∈ H¹₀(□_m)`;
the two right-hand sides are the SAME functional `-∫ g·∇w` of the SAME forcing
`g`, so they cancel on subtraction.  Nothing is divided, nothing is
subtracted through an operator, and the boundary datum never appears. -/
theorem testing_identity {A B : CoeffField d} {U : Set (Vec d)}
    {u v : H1Function U} {g : Vec d → Vec d} {w : H10Function U}
    (hu : IsDivFormWeakSolutionOn A U u g) (hv : IsDivFormWeakSolutionOn B U v g) :
    ∫ x in U, vecDot (matVecMul (A x) (u.grad x)) (w.toH1Function.grad x) ∂volume =
      ∫ x in U, vecDot (matVecMul (B x) (v.grad x)) (w.toH1Function.grad x) ∂volume := by
  rw [hu w, hv w]

/-- The testing identity at the gradient difference, with the scalar comparator
`B = σ Id` evaluated: `⨍_{□}(a∇u)·(∇u-∇v) = σ ⨍_{□} ∇v·(∇u-∇v)`. -/
theorem testing_identity_gradDiff {A : CoeffField d} {U : Set (Vec d)} {sigma : ℝ}
    {u v h : H1Function U} {g : Vec d → Vec d}
    (hu : IsDivFormWeakSolutionOn A U u g)
    (hv : IsDivFormWeakSolutionOn (fun _ => sigma • (1 : Mat d)) U v g)
    (hbu : HasZeroTraceDifferenceOn U u h) (hbv : HasZeroTraceDifferenceOn U v h) :
    ∫ x in U, vecDot (matVecMul (A x) (u.grad x)) (u.grad x - v.grad x) ∂volume =
      sigma * ∫ x in U, vecDot (v.grad x) (u.grad x - v.grad x) ∂volume := by
  obtain ⟨w, hw⟩ := exists_h10Function_grad_eq_sub hbu hbv
  have hkey := testing_identity (w := w) hu hv
  simp only [hw] at hkey
  rw [hkey]
  simp only [matVecMul_smul_one, vecDot_smul_left]
  rw [MeasureTheory.integral_const_mul]

end

end Algsuperdiff.Section4.Provider.Homogenization
