/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.BoundsEaL.LambdaSlotB5
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.BoundsEaL.LambdaWindow
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.LambdaBudget
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.Maximum

/-!
# LambdaIndexUpscale

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Bullet (B5) at the indices: the domain/field upscaling for `λ^{-1}`

## The index gap this module closes

`LambdaSlotB5.lean` delivers bullet (B5) at the anchor's own matched triple
`(□_{k−2}, 𝐚_{k−2}, σ_{k−3})`.  Read in the Step-4 indices this is the cube
`□_j` with the field `𝐚_j`, whereas the printed bullet carries the field
`𝐚_{j−2}` at the same cube `□_j` and the same gauge `σ_{j−1}`.

## The route, and every constant it costs

Read the delivered atom at the lower index `k = j`, i.e. at the triple `(□_{j−2},
𝐚_{j−2}, σ_{j−3})`, and raise the domain back to `□_j`:

1. **The domain raise.**  `lambdaSq_finite_two_inv_le_nine_pow_mul_max_descendants_sub_two`
   (`Annular/LambdaMatrixRoute.lean`) gives
   `λ_{γ,2}^{-1}(□_j;𝐚_{j−2}) ≤ (1 + 9^d 3^{−4γ}) max_R λ_{γ,2}^{-1}(R;𝐚_{j−2})`
   over the `9^d` scale-`(j−2)` descendants `R` of `□_j`, at the SAME gauge and
   the SAME field.  The sharp constant is only relaxed to `1 + 9^d`.
2. **The atom tail at every descendant.**  Each descendant is the cube
   `3^{j−2}w + □_{j−2}` at the field `𝐚_{j−2}`, i.e. exactly the delivered atom
   at `k = j` and the real centre `3^{j−2}w`; the proved
   `Proportion.exists_cgExcess_atomTail` holds real centre, and
   `LambdaWindow.exists_cgExcess_atomTail_unconditional` removes its window.
3. **The Orlicz finite maximum.**  `Orlicz.isBigOWith_gammaSigma_finset_sup'_of_nonempty`
   at `σ = 1/3` converts the `9^d` individual `Γ_{1/3}` tails into one tail for
   their maximum, at the common amplitude times
   `(3 max{1, log 9^d})^{3}` (the `q^{1/σ}` normalization at `σ = 1/3`), a
   `d`-only factor.
4. **W3's index steps, twice.**  `Annular.sigmaBar_sub_two_le_eight_mul_sigmaBar_sub_three`
   gives `σ_{j−1} ≤ 8 σ_{j−2} ≤ 64 σ_{j−3}`, i.e. `σ_{j−3}^{-1} ≤ 64 σ_{j−1}^{-1}`,
   which is what turns the delivered gauge into the printed one.

Net deterministic constant `64(1 + 9^d)`, `d`-only; the Orlicz leg carries in
addition the `d`-only maximum factor of step 3.  **No `γ`-exponent and no
`s`-power is moved anywhere in this module**: the gauge stays `γ`, the exponent
stays `q = 2`, and the amplitude stays the `exp(−C_cg^{−1}E^{−2}γ^{−1})`.

## References

* ABK26, `l.bounds.mathcal.E.aL` bullet (B5); `p.cg.ellipticity.bounds`.
-/

namespace Algsuperdiff.Section4.Provider.BoundsEaL

open HCPolySupport HCPolySupport.Book HCPolySupport.IndependentSums MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Provider.Annular

noncomputable section

variable {d : ℕ}

/-! ## 1. Three local re-derivations -/

/-- The dimension of a model is nonzero.  Local re-derivation (distinct name)
of the `private neZero_of_model` of six proved modules. -/
private theorem neZeroFromModel (M : ABKModel d) : NeZero d :=
  ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩

/-- The `𝒢₀` exponent slot at `q = 2`, unbundled.  Local re-derivation
(distinct name) of `Annular.LambdaBudget.coarseTwo_val`. -/
private theorem coarseTwoValue :
    Support.coarseEllipticityExponentTwo.1 = (Ch02.MultiscaleExponent.finite 2) := rfl

/-- The centred `λ`-literal at independent domain and cutoff scales is
`λ_{s,q}^{-1}(□_domain; 𝐚_cutoff)` of the Chapter 2 carrier.  This is a
re-derivation, under a distinct name, of `LambdaSlotB5.literal_eq_inv_lambdaSq`,
whose module is not in this file's import closure. -/
private theorem literalEqInvLambdaSqScales (M : ABKModel d)
    (domainScale cutoffScale : ℤ) (s : ℝ) (q : CoarseEllipticityExponent)
    (omega : Cutoff.CutoffSample d) :
    Observable.cutoffLowerEllipticityInvLiteral M domainScale cutoffScale s q omega =
      (Ch02.lambdaSq (originCube d domainScale) s q.1
        (Cutoff.coefficientCutoffTriadicCoeffFamily M cutoffScale omega))⁻¹ := by
  rw [← Algsuperdiff.Section3.Provider.BadEvents.cubeLowerEllipticityInvLiteral_originCube
      M domainScale cutoffScale s q,
    Algsuperdiff.Section3.Provider.Multiscale.cubeLowerEllipticityInvLiteral_eq_lambdaSq_inv]

/-! ## 2. The printed atom and its descendant family -/

/-- **The (B5) left-hand side**, `λ_{γ,2}^{-1}(z + □_j; 𝐚_{j−2})`: domain scale
`j`, cutoff scale `j − 2`, gauge `γ`, exponent `q = 2`, with the cube translate
realized on the sample (resolution A4).  At `z = 0` this is the manuscript's
centred `λ_{γ,2}^{-1}(□_j; 𝐚_{j−2})` verbatim. -/
def lambdaPrintedAtom (M : ABKModel d) (j : ℤ) (z : Vec d) :
    Cutoff.CutoffSample d → ℝ :=
  fun omega =>
    Observable.cutoffLowerEllipticityInvLiteral M j (j - 2) M.gamma
      Support.coarseEllipticityExponentTwo (Cutoff.translateCutoffSample z omega)

private theorem originCubeEqLatticeCube (d : ℕ) (j : ℤ) :
    originCube d j = latticeCube j (0 : Fin d → ℤ) := rfl

/-- The `9^d` scale-`(j−2)` descendants of `□_j` are never empty. -/
theorem descendantsAtScale_originCube_sub_two_nonempty (d : ℕ) (j : ℤ) :
    (descendantsAtScale (originCube d j) (j - 2)).Nonempty := by
  rw [originCubeEqLatticeCube d j]
  exact descendantsAtScale_latticeCube_sub_two_nonempty j (0 : Fin d → ℤ)

/-- Their number is exactly `9^d`. -/
theorem card_descendantsAtScale_originCube_sub_two (d : ℕ) (j : ℤ) :
    (((descendantsAtScale (originCube d j) (j - 2)).card : ℕ) : ℝ) = (9 : ℝ) ^ d := by
  have hscale : (originCube d j).scale = j := rfl
  have hn : j - 2 ≤ (originCube d j).scale := by rw [hscale]; omega
  have hdepth : Int.toNat ((originCube d j).scale - (j - 2)) = 2 := by
    rw [hscale]; omega
  rw [descendantsAtScale_eq_descendantsAtDepth (originCube d j) hn, descendantsAtDepth_card,
    hdepth]
  push_cast
  rw [← pow_mul, mul_comm d 2, pow_mul]
  norm_num

/-- **The `𝒢₀` bracket, maximized over the `9^d` descendants of `z + □_j`.**
This is the single random variable the Orlicz finite-maximum estimate produces,
and the one that carries the whole `Γ_{1/3}` tail of the upscaled bullet. -/
def cgExcessDescendantMax (M : ABKModel d) (Ccg : ℝ) (j : ℤ) (z : Vec d)
    (omega : Cutoff.CutoffSample d) : ℝ :=
  (descendantsAtScale (originCube d j) (j - 2)).sup'
    (descendantsAtScale_originCube_sub_two_nonempty d j)
    fun R => Localize.cgExcess M Ccg (j - 2)
      (Support.triadicLatticePoint (j - 2) R.index) (Cutoff.translateCutoffSample z omega)

theorem cgExcessDescendantMax_nonneg (M : ABKModel d) (Ccg : ℝ) (j : ℤ) (z : Vec d)
    (omega : Cutoff.CutoffSample d) : 0 ≤ cgExcessDescendantMax M Ccg j z omega := by
  obtain ⟨R, hR⟩ := descendantsAtScale_originCube_sub_two_nonempty d j
  refine le_trans (Localize.cgExcess_nonneg M Ccg (j - 2)
    (Support.triadicLatticePoint (j - 2) R.index) (Cutoff.translateCutoffSample z omega)) ?_
  exact Finset.le_sup' (f := fun R : TriadicCube d => Localize.cgExcess M Ccg (j - 2)
    (Support.triadicLatticePoint (j - 2) R.index) (Cutoff.translateCutoffSample z omega)) hR

theorem measurable_cgExcessDescendantMax (M : ABKModel d) (Ccg : ℝ) (j : ℤ) (z : Vec d) :
    Measurable (cgExcessDescendantMax M Ccg j z) := by
  have hfun : cgExcessDescendantMax M Ccg j z =
      (descendantsAtScale (originCube d j) (j - 2)).sup'
        (descendantsAtScale_originCube_sub_two_nonempty d j)
        (fun R omega => Localize.cgExcess M Ccg (j - 2)
          (Support.triadicLatticePoint (j - 2) R.index)
          (Cutoff.translateCutoffSample z omega)) := by
    funext omega
    rw [Finset.sup'_apply]
    rfl
  rw [hfun]
  refine Finset.measurable_sup' _ fun R _ => ?_
  exact (measurable_cgExcess M Ccg j (Support.triadicLatticePoint (j - 2) R.index)).comp
    (Cutoff.measurable_translateCutoffSample z)

/-! ## 3. The pointwise upscaling (state-free) -/

/-- **A7's domain raise, read at the `𝒢₀` bracket.**

`λ_{γ,2}^{-1}(z+□_j;𝐚_{j−2}) ≤ (1+9^d)(σ_{j−3}^{-1}C_cg + σ_{j−3}^{-1}𝒳^{max})`,
where `𝒳^{max}` is the maximum of the `𝒢₀` brackets over the `9^d` scale-`(j−2)`
descendants.  No induction state and no probability enters: this is the
deterministic half of the upscaling. -/
theorem lambdaPrintedAtom_le_descendantMax (M : ABKModel d) {Ccg : ℝ} (hCcg : 0 ≤ Ccg)
    (j : ℤ) (z : Vec d) (omega : Cutoff.CutoffSample d) :
    lambdaPrintedAtom M j z omega ≤
      (1 + (9 : ℝ) ^ d) * (((Annealed.sigmaBar M (j - 3) : ℝ))⁻¹ * Ccg) +
        (1 + (9 : ℝ) ^ d) * (((Annealed.sigmaBar M (j - 3) : ℝ))⁻¹ *
          cgExcessDescendantMax M Ccg j z omega) := by
  classical
  have : NeZero d := neZeroFromModel M
  have hg0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hs3 : (0 : ℝ) < (Annealed.sigmaBar M (j - 3) : ℝ) := (Annealed.sigmaBar M (j - 3)).2
  set omega' : Cutoff.CutoffSample d := Cutoff.translateCutoffSample z omega with homega'
  set a := Cutoff.coefficientCutoffTriadicCoeffFamily M (j - 2) omega' with ha
  set B : ℝ := ((Annealed.sigmaBar M (j - 3) : ℝ))⁻¹ * Ccg +
    ((Annealed.sigmaBar M (j - 3) : ℝ))⁻¹ * cgExcessDescendantMax M Ccg j z omega with hB
  -- the carrier identification
  have hlit : lambdaPrintedAtom M j z omega =
      (Ch02.lambdaSq (originCube d j) M.gamma (.finite 2) a)⁻¹ := by
    rw [lambdaPrintedAtom, literalEqInvLambdaSqScales M j (j - 2) M.gamma
      Support.coarseEllipticityExponentTwo omega', coarseTwoValue, ← ha]
  -- A7's raise at separation two
  have hscale : (originCube d j).scale = j := rfl
  have hraise : (Ch02.lambdaSq (originCube d j) M.gamma (.finite 2) a)⁻¹ ≤
      (1 + ((9 : ℝ) ^ d) * (3 : ℝ) ^ (-(4 * M.gamma))) *
        Ch02.finsetSupReal (descendantsAtScale (originCube d j) (j - 2)) fun R =>
          (Ch02.lambdaSq R M.gamma (.finite 2) a)⁻¹ := by
    have h := lambdaSq_finite_two_inv_le_nine_pow_mul_max_descendants_sub_two
      (originCube d j) a hg0
    rw [hscale] at h
    exact h
  -- every descendant is a delivered atom, and is dominated by the maximum
  have hsup : Ch02.finsetSupReal (descendantsAtScale (originCube d j) (j - 2))
      (fun R => (Ch02.lambdaSq R M.gamma (.finite 2) a)⁻¹) ≤ B := by
    refine Ch02.finsetSupReal_le _ (descendantsAtScale_originCube_sub_two_nonempty d j)
      fun R hR => ?_
    have hRscale : R.scale = j - 2 := by
      rw [originCubeEqLatticeCube d j] at hR
      exact (descendantsAtScale_latticeCube_sub_two_data hR).1
    have hRe : R = Localize.latticeCube (j - 2) R.index := by
      rw [← hRscale]
      rfl
    have hatom := Localize.lambdaAnnulusAtom_eq_inv_lambdaSq M j R.index omega'
    rw [coarseTwoValue, ← ha] at hatom
    rw [hRe, ← hatom]
    refine le_trans (lambdaAnnulusAtom_le_inv_sigmaBar_mul_add M Ccg j
      (Support.triadicLatticePoint (j - 2) R.index) omega') ?_
    rw [hB]
    refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ (inv_pos.2 hs3).le)
    exact Finset.le_sup' (f := fun R : TriadicCube d => Localize.cgExcess M Ccg (j - 2)
      (Support.triadicLatticePoint (j - 2) R.index) omega') hR
  -- the constants
  have hcard : (0 : ℝ) ≤ (9 : ℝ) ^ d := by positivity
  have hdisc : (3 : ℝ) ^ (-(4 * M.gamma)) ≤ 1 := by
    have hmono := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
      (show -(4 * M.gamma) ≤ (0 : ℝ) by linarith only [hg0])
    rwa [Real.rpow_zero] at hmono
  have hCd0 : (0 : ℝ) ≤ 1 + ((9 : ℝ) ^ d) * (3 : ℝ) ^ (-(4 * M.gamma)) := by positivity
  have hCd : 1 + ((9 : ℝ) ^ d) * (3 : ℝ) ^ (-(4 * M.gamma)) ≤ 1 + (9 : ℝ) ^ d := by
    have h := mul_le_mul_of_nonneg_left hdisc hcard
    linarith only [h]
  have hB0 : (0 : ℝ) ≤ B := by
    rw [hB]
    exact add_nonneg (mul_nonneg (inv_pos.2 hs3).le hCcg)
      (mul_nonneg (inv_pos.2 hs3).le (cgExcessDescendantMax_nonneg M Ccg j z omega))
  calc lambdaPrintedAtom M j z omega
      = (Ch02.lambdaSq (originCube d j) M.gamma (.finite 2) a)⁻¹ := hlit
    _ ≤ (1 + ((9 : ℝ) ^ d) * (3 : ℝ) ^ (-(4 * M.gamma))) * B :=
        le_trans hraise (mul_le_mul_of_nonneg_left hsup hCd0)
    _ ≤ (1 + (9 : ℝ) ^ d) * B := mul_le_mul_of_nonneg_right hCd hB0
    _ = (1 + (9 : ℝ) ^ d) * (((Annealed.sigmaBar M (j - 3) : ℝ))⁻¹ * Ccg) +
          (1 + (9 : ℝ) ^ d) * (((Annealed.sigmaBar M (j - 3) : ℝ))⁻¹ *
            cgExcessDescendantMax M Ccg j z omega) := by rw [hB]; ring

/-! ## 4. W3's two index steps -/

/-- **`σ_{j−3}^{-1} ≤ 64 σ_{j−1}^{-1}`** — two applications of the one-step
running-diffusivity ratio `σ_{n−2} ≤ 8 σ_{n−3}`.  This is what converts the
delivered gauge `σ_{j−3}` into the printed `σ_{j−1}`. -/
theorem inv_sigmaBar_sub_three_le_sixtyfour (M : ABKModel d) {m0 : ℤ}
    {E : {E : ℝ // 1 ≤ E}} (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 E)
    {j : ℤ} (hj : j - 1 ≤ m0) :
    ((Annealed.sigmaBar M (j - 3) : ℝ))⁻¹ ≤ 64 * ((Annealed.sigmaBar M (j - 1) : ℝ))⁻¹ := by
  have hs1 : (0 : ℝ) < (Annealed.sigmaBar M (j - 1) : ℝ) := (Annealed.sigmaBar M (j - 1)).2
  have hs3 : (0 : ℝ) < (Annealed.sigmaBar M (j - 3) : ℝ) := (Annealed.sigmaBar M (j - 3)).2
  have h1 := sigmaBar_sub_two_le_eight_mul_sigmaBar_sub_three M hS
    (n := j + 1) (by omega)
  have h2 := sigmaBar_sub_two_le_eight_mul_sigmaBar_sub_three M hS (n := j) (by omega)
  rw [show j + 1 - 2 = j - 1 from by ring, show j + 1 - 3 = j - 2 from by ring] at h1
  have hchain : (Annealed.sigmaBar M (j - 1) : ℝ) ≤ 64 * (Annealed.sigmaBar M (j - 3) : ℝ) := by
    have h3 := mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 8)
    linarith only [h1, h3]
  have hmul := mul_le_mul_of_nonneg_left hchain
    (mul_nonneg (inv_pos.2 hs1).le (inv_pos.2 hs3).le)
  have e1 : (((Annealed.sigmaBar M (j - 1) : ℝ))⁻¹ * ((Annealed.sigmaBar M (j - 3) : ℝ))⁻¹) *
      (Annealed.sigmaBar M (j - 1) : ℝ) = ((Annealed.sigmaBar M (j - 3) : ℝ))⁻¹ := by
    field_simp
  have e2 : (((Annealed.sigmaBar M (j - 1) : ℝ))⁻¹ * ((Annealed.sigmaBar M (j - 3) : ℝ))⁻¹) *
      (64 * (Annealed.sigmaBar M (j - 3) : ℝ)) = 64 * ((Annealed.sigmaBar M (j - 1) : ℝ))⁻¹ := by
    field_simp
  rwa [e1, e2] at hmul

/-! ## 5. The upscaled bullet, at the printed indices -/

/-- The `d`-only deterministic constant of the upscaling, `64(1 + 9^d)`: `64`
is W3's two index steps and `1 + 9^d` is A7's domain raise. -/
def lambdaUpscaleConst (d : ℕ) : ℝ := 64 * (1 + 9 ^ d)

theorem lambdaUpscaleConst_pos (d : ℕ) : 0 < lambdaUpscaleConst d := by
  have h9 : (0 : ℝ) < (9 : ℝ) ^ d := by positivity
  rw [lambdaUpscaleConst]
  positivity

/-- The `d`-only Orlicz factor of the finite maximum over the `9^d`
descendants, `(3 max{1, log 9^d})^{1/σ}` at `σ = 1/3`. -/
def lambdaMaxOrliczConst (d : ℕ) : ℝ :=
  (3 * max 1 (Real.log ((9 : ℝ) ^ d))) ^ (3 : ℝ)

theorem lambdaMaxOrliczConst_pos (d : ℕ) : 0 < lambdaMaxOrliczConst d := by
  have hbase : (0 : ℝ) < 3 * max 1 (Real.log ((9 : ℝ) ^ d)) := by
    have h := le_max_left (1 : ℝ) (Real.log ((9 : ℝ) ^ d))
    linarith only [h]
  rw [lambdaMaxOrliczConst]
  exact Real.rpow_pos_of_pos hbase _

/-- **The `Γ_{1/3}` tail of the descendant maximum.** -/
theorem isBigOWith_cgExcessDescendantMax (M : ABKModel d) {A : ℝ} (hA : 0 ≤ A) (j : ℤ)
    (z : Vec d)
    (htail : ∀ (k : ℤ) (y : Vec d),
      IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma (1 / 3 : ℝ))
        (fun omega =>
          Localize.cgExcess M (Support.cgEllipLowerConstant d) (k - 2) y omega) A) :
    IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma (1 / 3 : ℝ))
      (cgExcessDescendantMax M (Support.cgEllipLowerConstant d) j z)
      (lambdaMaxOrliczConst d * A) := by
  classical
  have hper : ∀ R ∈ descendantsAtScale (originCube d j) (j - 2),
      IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma (1 / 3 : ℝ))
        (fun omega => Localize.cgExcess M (Support.cgEllipLowerConstant d) (j - 2)
          (Support.triadicLatticePoint (j - 2) R.index)
          (Cutoff.translateCutoffSample z omega)) A := by
    intro R _
    exact Proportion.isBigOWith_comp_measurePreserving
      (GoodEvents.measurePreserving_translateCutoffSample M z)
      (measurable_cgExcess M (Support.cgEllipLowerConstant d) j
        (Support.triadicLatticePoint (j - 2) R.index))
      (htail j (Support.triadicLatticePoint (j - 2) R.index))
  have hmax := Provider.Orlicz.isBigOWith_gammaSigma_finset_sup'_of_nonempty
    (μ := (Cutoff.cutoffSampleLaw M).toMeasure)
    (descendantsAtScale (originCube d j) (j - 2))
    (descendantsAtScale_originCube_sub_two_nonempty d j)
    (X := fun R omega => Localize.cgExcess M (Support.cgEllipLowerConstant d) (j - 2)
      (Support.triadicLatticePoint (j - 2) R.index) (Cutoff.translateCutoffSample z omega))
    (A := A) (σ := (1 / 3 : ℝ)) (by norm_num) hA hper
  rw [card_descendantsAtScale_originCube_sub_two d j,
    show ((1 : ℝ) / 3)⁻¹ = (3 : ℝ) from by norm_num] at hmax
  exact hmax

/-- **Bullet (B5) at the printed indices, at every moment `q ∈ [1,∞)`.**

```
E[ λ_{γ,2}^{-q}(z + □_j; 𝐚_{j−2}) ]^{1/q}
  ≤ 64(1+9^d) σ_{j−1}^{-1} C_cg
      + C(1/3) q³ · 64(1+9^d)(3 max{1,log 9^d})³ σ_{j−1}^{-1} exp(−C_cg^{−1}E^{−2}γ^{−1}) ,
```

The `q³` is `q^{1/σ}` at `σ = 1/3`.  Every constant is `d`-only. -/
theorem lintegral_rpow_lambdaPrintedAtom_le (M : ABKModel d) {m0 : ℤ}
    {E F : {E : ℝ // 1 ≤ E}} (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 E)
    (htail : ∀ (k : ℤ) (y : Vec d),
      IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma (1 / 3 : ℝ))
        (fun omega =>
          Localize.cgExcess M (Support.cgEllipLowerConstant d) (k - 2) y omega)
        (Proportion.cgTailScale M (F : ℝ)))
    {j : ℤ} (hj : j - 1 ≤ m0) (z : Vec d) {p : ℝ} (hp : 1 ≤ p) :
    ∫⁻ omega : Cutoff.CutoffSample d,
        ENNReal.ofReal (lambdaPrintedAtom M j z omega) ^ p
        ∂(Cutoff.cutoffSampleLaw M).toMeasure
      ≤ ENNReal.ofReal
          (lambdaUpscaleConst d * (((Annealed.sigmaBar M (j - 1) : ℝ))⁻¹ *
              Support.cgEllipLowerConstant d) +
            gammaMomentBound (1 / 3) p
              (lambdaUpscaleConst d * lambdaMaxOrliczConst d *
                (((Annealed.sigmaBar M (j - 1) : ℝ))⁻¹ *
                  Proportion.cgTailScale M (F : ℝ)))) ^ p := by
  classical
  have hs1 : (0 : ℝ) < (Annealed.sigmaBar M (j - 1) : ℝ) := (Annealed.sigmaBar M (j - 1)).2
  have hs3 : (0 : ℝ) < (Annealed.sigmaBar M (j - 3) : ℝ) := (Annealed.sigmaBar M (j - 3)).2
  have hCcg : (0 : ℝ) < Support.cgEllipLowerConstant d := Support.cgEllipLowerConstant_pos d
  have hA : (0 : ℝ) < Proportion.cgTailScale M (F : ℝ) := Proportion.cgTailScale_pos M (F : ℝ)
  have hgauge := inv_sigmaBar_sub_three_le_sixtyfour M hS hj
  have h9 : (0 : ℝ) ≤ (9 : ℝ) ^ d := by positivity
  -- the pointwise domination, at the printed gauge
  have hpoint : ∀ omega : Cutoff.CutoffSample d,
      lambdaPrintedAtom M j z omega ≤
        lambdaUpscaleConst d * (((Annealed.sigmaBar M (j - 1) : ℝ))⁻¹ *
            Support.cgEllipLowerConstant d) +
          lambdaUpscaleConst d * ((Annealed.sigmaBar M (j - 1) : ℝ))⁻¹ *
            cgExcessDescendantMax M (Support.cgEllipLowerConstant d) j z omega := by
    intro omega
    have hbase := lambdaPrintedAtom_le_descendantMax M hCcg.le j z omega
    have hz0 : (0 : ℝ) ≤ cgExcessDescendantMax M (Support.cgEllipLowerConstant d) j z omega :=
      cgExcessDescendantMax_nonneg M (Support.cgEllipLowerConstant d) j z omega
    have hone : ((Annealed.sigmaBar M (j - 3) : ℝ))⁻¹ * Support.cgEllipLowerConstant d ≤
        64 * (((Annealed.sigmaBar M (j - 1) : ℝ))⁻¹ * Support.cgEllipLowerConstant d) := by
      have h := mul_le_mul_of_nonneg_right hgauge hCcg.le
      linarith only [h]
    have htwo : ((Annealed.sigmaBar M (j - 3) : ℝ))⁻¹ *
        cgExcessDescendantMax M (Support.cgEllipLowerConstant d) j z omega ≤
        64 * (((Annealed.sigmaBar M (j - 1) : ℝ))⁻¹ *
          cgExcessDescendantMax M (Support.cgEllipLowerConstant d) j z omega) := by
      have h := mul_le_mul_of_nonneg_right hgauge hz0
      linarith only [h]
    have hone' := mul_le_mul_of_nonneg_left hone (by positivity : (0 : ℝ) ≤ 1 + (9 : ℝ) ^ d)
    have htwo' := mul_le_mul_of_nonneg_left htwo (by positivity : (0 : ℝ) ≤ 1 + (9 : ℝ) ^ d)
    rw [lambdaUpscaleConst]
    linarith only [hbase, hone', htwo']
  -- the Orlicz half
  have hbig := IsBigOWith.const_mul
    (mul_nonneg (lambdaUpscaleConst_pos d).le (inv_pos.2 hs1).le)
    (isBigOWith_cgExcessDescendantMax M hA.le j z htail)
  have hamp : lambdaUpscaleConst d * ((Annealed.sigmaBar M (j - 1) : ℝ))⁻¹ *
      (lambdaMaxOrliczConst d * Proportion.cgTailScale M (F : ℝ)) =
      lambdaUpscaleConst d * lambdaMaxOrliczConst d *
        (((Annealed.sigmaBar M (j - 1) : ℝ))⁻¹ * Proportion.cgTailScale M (F : ℝ)) := by
    ring
  rw [hamp] at hbig
  refine lintegral_rpow_le_of_isBigOWith_add_const_of_ae_le (by norm_num)
    (mul_pos (mul_pos (lambdaUpscaleConst_pos d) (lambdaMaxOrliczConst_pos d))
      (mul_pos (inv_pos.2 hs1) hA)) hp
    (mul_nonneg (lambdaUpscaleConst_pos d).le (mul_nonneg (inv_pos.2 hs1).le hCcg.le))
    (fun omega => mul_nonneg (mul_nonneg (lambdaUpscaleConst_pos d).le (inv_pos.2 hs1).le)
      (cgExcessDescendantMax_nonneg M (Support.cgEllipLowerConstant d) j z omega))
    ((measurable_cgExcessDescendantMax M (Support.cgEllipLowerConstant d) j z).const_mul
      _).aemeasurable hbig ?_ le_rfl
  exact Filter.Eventually.of_forall fun omega => ENNReal.ofReal_le_ofReal (hpoint omega)

/-- **The upscaled bullet, packaged and unconditional in the printed regime.**

There is a `d`-only constant `C` such that every model with `γ ≤
C^{−10}c⋆^{10}` satisfies bullet (B5) at the printed cube, field and gauge, at
every scale `j`, every real centre `z` and every moment `q ∈ [1,∞)`, with NO
remaining hypothesis: the induction state comes from its all-scales budget and the
`s`-window from `LambdaWindow.cgTailScale_le_half_gamma`. -/
theorem exists_lintegral_rpow_lambdaPrintedAtom_le (d : ℕ) :
    ∃ C : ℝ, 6 ≤ C ∧
      ∀ M : ABKModel d,
        M.gamma ≤ (C⁻¹) ^ 10 * (Disorder.cstar M) ^ 10 →
        ∃ E : {E : ℝ // 1 ≤ E},
          (E : ℝ) = C * (Disorder.cstar M)⁻¹ ∧
            ∀ (j : ℤ) (z : Vec d) (p : ℝ), 1 ≤ p →
              ∫⁻ omega : Cutoff.CutoffSample d,
                  ENNReal.ofReal (lambdaPrintedAtom M j z omega) ^ p
                  ∂(Cutoff.cutoffSampleLaw M).toMeasure
                ≤ ENNReal.ofReal
                    (lambdaUpscaleConst d * (((Annealed.sigmaBar M (j - 1) : ℝ))⁻¹ *
                        Support.cgEllipLowerConstant d) +
                      gammaMomentBound (1 / 3) p
                        (lambdaUpscaleConst d * lambdaMaxOrliczConst d *
                          (((Annealed.sigmaBar M (j - 1) : ℝ))⁻¹ *
                            Proportion.cgTailScale M (E : ℝ)))) ^ p := by
  obtain ⟨C1, hC16, -, hstateAll⟩ := GoodEvents.exists_allScalesInductionState_ge d 0
  obtain ⟨C2, hC26, htailAll⟩ := exists_cgExcess_atomTail_unconditional d
  refine ⟨max C1 C2, le_trans hC16 (le_max_left _ _), ?_⟩
  intro M hreg
  set C : ℝ := max C1 C2 with hCdef
  have hC1le : C1 ≤ C := le_max_left _ _
  have hC2le : C2 ≤ C := le_max_right _ _
  have hC10 : (0 : ℝ) < C1 := by linarith only [hC16]
  have hC20 : (0 : ℝ) < C2 := by linarith only [hC26]
  have hC6 : (6 : ℝ) ≤ C := le_trans hC16 hC1le
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le hC10 hC1le
  have hcs : (0 : ℝ) ≤ (Disorder.cstar M) ^ 10 := by positivity
  have hcs0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hcsle : Disorder.cstar M ≤ 3 / 2 :=
    Algsuperdiff.Section3.Provider.Disorder.cstar_le_three_halves M
  have hlower : ∀ C' : ℝ, 0 < C' → C' ≤ C →
      M.gamma ≤ (C'⁻¹) ^ 10 * (Disorder.cstar M) ^ 10 := by
    intro C' hC'0 hC'le
    have hinv : C⁻¹ ≤ C'⁻¹ := by
      have hp := mul_le_mul_of_nonneg_left hC'le
        (mul_nonneg (inv_nonneg.mpr hC'0.le) (inv_nonneg.mpr hCpos.le))
      have e1 : (C'⁻¹ * C⁻¹) * C' = C⁻¹ := by field_simp
      have e2 : (C'⁻¹ * C⁻¹) * C = C'⁻¹ := by field_simp
      rwa [e1, e2] at hp
    have hpow : (C⁻¹) ^ 10 ≤ (C'⁻¹) ^ 10 :=
      pow_le_pow_left₀ (inv_nonneg.mpr hCpos.le) hinv 10
    exact le_trans hreg (mul_le_mul_of_nonneg_right hpow hcs)
  obtain ⟨E1, -, -, hstate⟩ := hstateAll M (hlower C1 hC10 hC1le)
  obtain ⟨E2, hE2val, htail⟩ := htailAll M (hlower C2 hC20 hC2le)
  -- promote the budget to `C`; the amplitude only grows
  have hone : (1 : ℝ) ≤ C * (Disorder.cstar M)⁻¹ := by
    have hge : (2 : ℝ) / 3 ≤ (Disorder.cstar M)⁻¹ := by
      rw [le_inv_comm₀ (by norm_num : (0 : ℝ) < 2 / 3) hcs0]
      calc Disorder.cstar M ≤ 3 / 2 := hcsle
        _ = ((2 : ℝ) / 3)⁻¹ := by norm_num
    have hstep : (6 : ℝ) * (2 / 3) ≤ C * (Disorder.cstar M)⁻¹ :=
      mul_le_mul hC6 hge (by norm_num) (by linarith only [hC6])
    linarith only [hstep]
  have hE2pos : (0 : ℝ) < (E2 : ℝ) := lt_of_lt_of_le zero_lt_one E2.2
  have hE2le : (E2 : ℝ) ≤ C * (Disorder.cstar M)⁻¹ := by
    rw [hE2val]
    exact mul_le_mul_of_nonneg_right hC2le (inv_pos.mpr hcs0).le
  refine ⟨⟨C * (Disorder.cstar M)⁻¹, hone⟩, rfl, fun j z p hp => ?_⟩
  refine lintegral_rpow_lambdaPrintedAtom_le M (hstate (j - 1)) (fun k y => ?_) le_rfl z hp
  exact (htail k y).mono_scale (cgTailScale_mono M hE2pos hE2le)

end

end Algsuperdiff.Section4.Provider.BoundsEaL
