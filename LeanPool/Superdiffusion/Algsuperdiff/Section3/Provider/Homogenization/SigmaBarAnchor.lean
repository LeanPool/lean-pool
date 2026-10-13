/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Annealed.RunningDiffusivity.Characterization
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.VarianceCarrierSeam

/-!
# SigmaBarAnchor

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The `σ_L` anchor: the Step-2 downscale display in the infinite-volume limit

ABK26, Proposition `p.combine.under.S`.  Step 1 produces a deterministic
residual `(σ_L σ_{L,*}^{-1}(□_m) - 1)^2` from the third block of the variance
split, and disposes of it by citing the sandwich `σ_{L,*}(□_m) ≤ σ_L ≤ 2
σ_{L,*}(□_m)`.  That citation is defective: the sandwich only gives `1 ≤ σ_L
σ_{L,*}^{-1}(□_m) ≤ 2`, so the residual is `O(1)` and no term of that shape
appears in `(e.initial.JL.bound)`.

The genuine bound on the residual is the Step-2 display
`(e.means.downscale.by.defect)` evaluated in the limit `n → ∞`, which is
legitimate because `σ_L^{-1}` *is* that limit -- it is the defining
characterization of `σ_L` (`Annealed.sigmaBar_characterization`) -- and
because Step 2 does not depend on Step 1, so the forward reference is harmless.
The constant is the explicit numeral `4`.

## What is proved

1. *The anchor.*  `tendsto_annealedSigmaStarInvScalarAtScale`: the Step-2 scalar
   `σ_{L,*}^{-1}(□_n) = annealedSigmaStarInvScalarAtScale M L n` converges to
   `σ_L^{-1}` as `n → ∞` along `ℕ`.  This is the `(inr 0, inr 0)` entry of the
   matrix limit carried by `Annealed.sigmaBar_characterization`, whose limit
   point is `blockDiag (σ_L • 1) (σ_L^{-1} • 1)`.
2. *The residual bound.*
   `coefficientCutoffLaw_sq_sigmaBar_mul_annealedSigmaStarInvScalarAtScale_sub_one_le`:
   under exactly the premises of the proved Step-2 display, `(σ_L
   σ_{L,*}^{-1}(□_m) - 1)^2 ≤ 4 δ₁^2` for every `L ≤ m`.
3. *The sandwich half.*
   `coefficientCutoffLaw_annealedSigmaStarInvScalarAtScale_le_two_mul_inv_sigmaBar`:
   under the same premises, `σ_{L,*}^{-1}(□_m) ≤ 2 σ_L^{-1}`, which is the
   printed half of the sandwich.

## References

* ABK26.
-/

namespace Algsuperdiff.Section3.Provider.Homogenization

open Filter MeasureTheory
open _root_.HCPolySupport _root_.HCPolySupport.Book

noncomputable section

variable {d : ℕ} [NeZero d]

/-- **The `σ_L` anchor.**  The Step-2 scalar `σ_{L,*}^{-1}(□_n)` converges to
`σ_L^{-1}` as the cube scale `n` runs to `+∞` along `ℕ`.

This is the defining characterization of the running diffusivity read on one
entry: `Annealed.sigmaBar_characterization` states that the full block matrices
`toFullBlockMat (annealedBlockMatrixAtScale (coefficientCutoffLaw M L) n)`
converge to `toFullBlockMat (blockDiag (σ_L • 1) (σ_L^{-1} • 1))`, whose
`(inr 0, inr 0)` entry is `σ_L^{-1}`; the same entry of the approximants is
`annealedSigmaStarInvScalarAtScale M L n` definitionally, since
`annealedSigmaStarInv` is the `lowerRight` block of `annealedBlockMatrix`. -/
theorem tendsto_annealedSigmaStarInvScalarAtScale (M : ABKModel d) (L : ℤ) :
    Tendsto (fun n : ℕ => annealedSigmaStarInvScalarAtScale M L n) atTop
      (nhds ((Annealed.sigmaBar M L : ℝ)⁻¹)) := by
  obtain ⟨-, hlim, -⟩ := Annealed.sigmaBar_characterization M L
  have h1 := (tendsto_pi_nhds.mp hlim) (Sum.inr (0 : Fin d))
  have h2 := (tendsto_pi_nhds.mp h1) (Sum.inr (0 : Fin d))
  simpa [toFullBlockMat, Ch02.blockDiag, Matrix.one_apply,
    annealedSigmaStarInvScalarAtScale] using! h2

/-- `(shom_L shom_{L,*}^{-1}(cu_m) - 1)^2 <= 4 delta_1^2`.

The printed proof disposes of this residual by citing the sandwich
`shom_{L,*}(cu_m) <= shom_L <= 2 shom_{L,*}(cu_m)`, which only bounds it by
`O(1)`.  The route taken here is Step 2 in the limit: the `shom_L`-normalized
downscale display holds at every pair `m <= k`, its left-hand side converges to
this residual as `k -> +infinity` by the anchor above, and the right-hand side
`4 delta_1^2` does not move.  The universal constant is the explicit numeral
`4`. -/
theorem coefficientCutoffLaw_sq_sigmaBar_mul_annealedSigmaStarInvScalarAtScale_sub_one_le
    (M : ABKModel d) {L m : ℤ} (hLm : L ≤ m)
    {s : ℝ} (hs : 0 < s) {delta1 : ℝ} (hdelta1 : delta1 ∈ Set.Ioc (0 : ℝ) (1 / 2))
    (hmoment : ∫⁻ omega, ENNReal.ofReal
        (Observable.cutoffHomogenizationErrorRepresentative M L L hs
          (Annealed.sigmaBar M L) omega ^ 4)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (delta1 ^ 2))
    {p q : Vec d} (hpq : q = (Annealed.sigmaBar M L : ℝ) • p)
    (hqnorm : vecNormSq q = (Annealed.sigmaBar M L : ℝ)) :
    ((Annealed.sigmaBar M L : ℝ) * annealedSigmaStarInvScalarAtScale M L m - 1) ^ 2 ≤
      4 * delta1 ^ 2 := by
  have hsigma : (0 : ℝ) < (Annealed.sigmaBar M L : ℝ) := (Annealed.sigmaBar M L).property
  have hev : ∀ᶠ k : ℕ in atTop,
      ((Annealed.sigmaBar M L : ℝ) *
          (annealedSigmaStarInvScalarAtScale M L k -
            annealedSigmaStarInvScalarAtScale M L m)) ^ 2 ≤ 4 * delta1 ^ 2 := by
    filter_upwards [eventually_ge_atTop m.toNat] with k hk
    have hmk : m ≤ (k : ℤ) := le_trans (Int.self_le_toNat m) (by exact_mod_cast hk)
    exact
      annealedInverseDiffusivity_defect_bound
        M L hLm hmk hs hdelta1 hmoment hpq hqnorm
  have hseq :
      Tendsto
        (fun k : ℕ =>
          ((Annealed.sigmaBar M L : ℝ) *
            (annealedSigmaStarInvScalarAtScale M L k -
              annealedSigmaStarInvScalarAtScale M L m)) ^ 2)
        atTop
        (nhds
          (((Annealed.sigmaBar M L : ℝ) *
            ((Annealed.sigmaBar M L : ℝ)⁻¹ -
              annealedSigmaStarInvScalarAtScale M L m)) ^ 2)) :=
    (((tendsto_annealedSigmaStarInvScalarAtScale M L).sub_const _).const_mul _).pow 2
  have hkey := le_of_tendsto hseq hev
  have hone : (Annealed.sigmaBar M L : ℝ) * (Annealed.sigmaBar M L : ℝ)⁻¹ = 1 :=
    mul_inv_cancel₀ (ne_of_gt hsigma)
  calc ((Annealed.sigmaBar M L : ℝ) * annealedSigmaStarInvScalarAtScale M L m - 1) ^ 2
      = ((Annealed.sigmaBar M L : ℝ) *
          ((Annealed.sigmaBar M L : ℝ)⁻¹ -
            annealedSigmaStarInvScalarAtScale M L m)) ^ 2 := by
        rw [mul_sub, hone]
        ring
    _ ≤ 4 * delta1 ^ 2 := hkey

end

end Algsuperdiff.Section3.Provider.Homogenization
