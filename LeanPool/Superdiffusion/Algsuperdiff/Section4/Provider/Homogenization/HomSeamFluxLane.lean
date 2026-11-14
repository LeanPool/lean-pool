/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSchauderUniform
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSeamFluxCoefficient

/-!
# HomSeamFluxLane

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The §4.5 duality lane, RE-INSTANTIATED at the printed field `ã_{L,m}`

## Why this file exists

The lane (`HomSpineRecutSupport`, `HomSchauderSwap`) is
pinned at the UNCUT cutoff field `a_L`, while the manuscript runs Step 3 and
Step 4 at the flux-corrected field `ã_{L,m} = a_L - (k_L - k_m)_{□_m}`.
`HomSeamFluxCoefficient` showed the `a_L`-sided seam bridge is not available;
the lane is therefore re-instantiated at `ã`, which is what this file does.

Nothing new is estimated.  Every mathematical step of the lane is already
GENERIC in the coefficient:

* `HomCGDischargeInstantiation.exists_printedCoarseGraining_of_dirichletPair`
  quantifies over `a: CoeffOn (cubeDomain □_m)`;
* `HomCGFinalLegs.weakNegDualBounds_of_smoothDualDisplay` is generic in `a`;
* `HomCGCarrierRHS.localCoarseGrainingLpRHS_{toReal_le,ne_top}` and
  `HomCGCarrierEnergy.weightedLocalSymmetricEnergyLp_le_ofReal` are generic
  in `a`;
* `HomSpineRecutClose.integrableOn_{self,cross}Energy` are generic in `a`;
* `HomStepFourEnergy.energy_split` is generic in the field `A` and reads it
  only through `symmPart A = ν·Id`.

The only pinned bytes were the INSTANTIATIONS, and they are re-made here at
`ã`, using
`HomSeamFluxCoefficient.isDirichletSolutionOn_fluxCorrected_of_cutoff` to
transport the spine's Dirichlet binder.

## The `C∇u` shift never materializes (the price of the re-instantiation)

`ã∇u = a_L∇u - C∇u` with `C = (k_L - k_m)_{□_m}` constant and skew.  The shift
would cost something only if some consumer needed the flux leg in its
`a_L`-form.  None does:

* the two weak negative-norm slots are consumed ONLY by
  `HomStepFourEnergy.stepFourEnergyDisplay`, against the Schauder gauge of
  `∇v`, and `energy_split` supplies the identity at whichever field is used;
* the identity's left-hand side is `⨍ ν|∇u|²`, produced from
  `symmPart(ã) = ν·Id` — the SAME function as at `a_L`
  (`symmPart_fluxCorrectedCoeffOn_eq_nu` below);
* the Step-4 payoff and the Step-3c payoff of `HomSpineFinalEndpoint`'s clause
  supplier are coefficient-FREE (`⨍ ν|∇u|²`, `⨍ σ|∇v|²`, `|u - v|`).

So the whole lane moves at constant `1`, and the `C∇u` shift is invisible at
every slot.  (Consistency check: `ã` solves the same Dirichlet problem, so the
testing identity gives `∫_{□_m} C∇u·(∇u - ∇v) = 0`, and `∫ C∇u·∇u = 0` by
skewness — the two energy splits agree term by term.)

## Scope

Nothing here is a source-facing claim.  All declarations are conditional APIs
or named helpers of this tree; the printed proposition the general
coarse-graining proposition enters exactly as it does in the lane, at the same
finite `p` and the same constant `C(p,d)`.
-/

open HCPolySupport HCPolySupport.Book.Ch03 HCPolySupport.Book.Ch03.ABK26 MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. The symmetric part of `ã_{L,m}` is still `ν Id` -/

/-- **THE `ν`-DROP IS BLIND TO THE FLUX CORRECTION.**  The subtracted matrix is
constant and skew, so the symmetric part of `ã_{L,m}` is the symmetric part of
`a_L`, namely `ν Id`.  This is the single fact that makes the Step-4 energy
identity fire at the printed field with the printed left-hand side. -/
theorem symmPart_fluxCorrectedCoeffOn_eq_nu (M : ABKModel d) (L m : ℤ)
    (Q : TriadicCube d) (omega : Cutoff.CutoffSample d) (x : Vec d) :
    symmPart ((fluxCorrectedCoeffOn M L m Q omega).toCoeffField x) =
      (M.nu : ℝ) • (1 : Mat d) := by
  calc symmPart ((fluxCorrectedCoeffOn M L m Q omega).toCoeffField x)
      = symmPart (Cutoff.coefficientCutoff M.nu L omega x -
          fluxIncrementAverage M L m Q omega) := rfl
    _ = symmPart (Cutoff.coefficientCutoff M.nu L omega x) :=
        symmPart_sub_const_of_skew (matTranspose_fluxIncrementAverage M L m Q omega) _
    _ = (M.nu : ℝ) • (1 : Mat d) := Cutoff.symmPart_coefficientCutoff M.nu L omega x

/-! ## 2. The printed display at `ã_{L,m}` -/

/-- **THE PRINTED FINITE-`p` DISPLAY, AT THE PRINT'S OWN COEFFICIENT.**

The printed display at the spine's own cutoff pair, with
the coefficient slot filled by the flux-corrected field instead of the uncut
`a_L`. The elliptic pair fed in is still the spine's own (the root's binder is
at `a_L`); the transport to `ã` is
`isDirichletSolutionOn_fluxCorrected_of_cutoff`, i.e. the printed display's own
sentence.  The constant is the SAME `C(p,d)`, produced before the model and
before the coefficient. -/
theorem exists_printedCoarseGraining_of_fluxPair (d : ℕ) (hd : 2 ≤ d)
    (p : FiniteLpExponent) (hp : (2 : ℝ≥0∞) ≤ p.exponent) :
    letI : NeZero d := ⟨by omega⟩
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : ABKModel d) (L : ℤ) (omega : Cutoff.CutoffSample d)
        (m n : ℤ) (hnm : n < m) (s1 s s2 : FractionalOrder),
        s1.1 < s.1 → s.1 < s2.1 →
      ∀ (sigma0 : ℝ) (hsigma0 : 0 < sigma0) (g : Vec d → Vec d),
        MemCubeEuclideanFullWsp (originCube d m) s2 p g →
      ∀ u v h : H1Function (openCubeSet (originCube d m)),
        IsDirichletSolutionOn (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
          (originCube d m) u h g →
        IsDirichletSolutionOn (fun _ => sigma0 • (1 : Mat d)) (originCube d m) v h g →
        ENNReal.ofReal (Real.rpow 3 (-s.1 * (m : ℝ))) *
            centeredCubeFluxComparisonSmoothDualLHS m
              (fluxCorrectedCoeffOn M L m (originCube d m) omega) sigma0 u v s p ≤
          localCoarseGrainingLpRHS C (originCube d m) n
            (by simpa [originCube] using hnm.le)
            (fluxCorrectedCoeffOn M L m (originCube d m) omega) sigma0 hsigma0 g u
            s1 s s2 p := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨C, hCtop, hC⟩ := exists_printedCoarseGraining_of_dirichletPair d hd p hp
  refine ⟨C, hCtop, ?_⟩
  intro M L omega m n hnm s1 s s2 hs1s hss2 sigma0 hsigma0 g hg u v h hsol hcomp
  exact hC m n hnm s1 s s2 hs1s hss2
    (fluxCorrectedCoeffOn M L m (originCube d m) omega) sigma0 hsigma0 g hg u v h
    (isDirichletSolutionOn_fluxCorrected_of_cutoff M L m omega hsol) hcomp

/-! ## 3. The two duality legs, generic in the coefficient -/

/-- **The two Step-4 duality slots from the display, GENERIC in the coefficient.**

The two endpoint-level duality slots of the display, with the
coefficient slot freed: the inner producer
`HomCGFinalLegs.weakNegDualBounds_of_smoothDualDisplay` never looks at the
field, and the two level transports are scalar arithmetic. -/
theorem weakNegDualBounds_endpointLevels_of_displayOn {m : ℤ}
    {a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain (originCube d m))}
    {sigma0 : ℝ} (hsigma0 : 0 < sigma0)
    {u v : H1Function (openCubeSet (originCube d m))}
    (s' s : FractionalOrder) (p : FiniteLpExponent)
    (hlo : 0 < (s.1 - s'.1) * p.conjugate.exponent.toReal)
    (hhi : (s.1 - s'.1) * p.conjugate.exponent.toReal < (d : ℝ))
    {R : ℝ≥0∞} (hRtop : R ≠ ⊤)
    (hdisp : ENNReal.ofReal (Real.rpow 3 (-s'.1 * (m : ℝ))) *
        centeredCubeFluxComparisonSmoothDualLHS m a sigma0 u v s' p ≤ R)
    {Level : ℝ}
    (hlevelDual : cgTestConst d (originCube d m) s.1 s'.1 p.conjugate.exponent.toReal *
        (Real.rpow 3 (s'.1 * (m : ℝ)) * R.toReal) ≤
      Real.rpow 3 (s.1 * (m : ℝ)) * (sigma0 * Level)) :
    WeakNegDualBoundOn (originCube d m) s.1
        (Real.rpow 3 (s.1 * (m : ℝ)) * sigma0 * Level)
        (fun x => matVecMul (a.toCoeffField x) (u.grad x) - sigma0 • v.grad x) ∧
      WeakNegDualBoundOn (originCube d m) s.1 (Real.rpow 3 (s.1 * (m : ℝ)) * Level)
        (fun x => u.grad x - v.grad x) := by
  obtain ⟨hgrad, hflux⟩ :=
    weakNegDualBounds_of_smoothDualDisplay (a := a) hsigma0 s' s p hlo hhi hRtop hdisp
  refine ⟨hflux.mono ?_, hgrad.mono ?_⟩
  · calc cgTestConst d (originCube d m) s.1 s'.1 p.conjugate.exponent.toReal *
          (Real.rpow 3 (s'.1 * (m : ℝ)) * R.toReal)
        ≤ Real.rpow 3 (s.1 * (m : ℝ)) * (sigma0 * Level) := hlevelDual
      _ = Real.rpow 3 (s.1 * (m : ℝ)) * sigma0 * Level := by ring
  · have hinv : (0 : ℝ) ≤ sigma0⁻¹ := le_of_lt (inv_pos.mpr hsigma0)
    have hstep := mul_le_mul_of_nonneg_left hlevelDual hinv
    have hleft : sigma0⁻¹ * (cgTestConst d (originCube d m) s.1 s'.1
          p.conjugate.exponent.toReal * (Real.rpow 3 (s'.1 * (m : ℝ)) * R.toReal)) =
        cgTestConst d (originCube d m) s.1 s'.1 p.conjugate.exponent.toReal *
          (sigma0⁻¹ * (Real.rpow 3 (s'.1 * (m : ℝ)) * R.toReal)) := by ring
    have hright : sigma0⁻¹ * (Real.rpow 3 (s.1 * (m : ℝ)) * (sigma0 * Level)) =
        Real.rpow 3 (s.1 * (m : ℝ)) * Level := by
      field_simp
    rw [hleft, hright] at hstep
    exact hstep

/-! ## 4. The two legs at `ã_{L,m}`, from the root's own binders -/

/-- **THE TWO STEP-4 DUALITY SLOTS AT THE PRINT'S COEFFICIENT.**

The two duality slots at the spine's own cutoff pair, re-instantiated at
`ã_{L,m}`.  The inputs are unchanged in kind:

* the root's two `IsDirichletSolutionOn` binders — still stated at `a_L`, and
  transported to `ã` by `isDirichletSolutionOn_fluxCorrected_of_cutoff`;
* the root's `C^{0,1/2}` binder on `𝐠`;
* the four slot dominations and the `S`-slot comparison, now read at `ã`;
* the arithmetic side condition `hlevelDual`.

The produced flux leg carries `ã∇u - σ∇v`, which is exactly what the printed
Step 4 pairs against the Schauder gauge of `∇v`. -/
theorem exists_weakNegDualBounds_of_fluxPair (d : ℕ) (hd : 2 ≤ d)
    (p : FiniteLpExponent) (hp : (2 : ℝ≥0∞) ≤ p.exponent) :
    letI : NeZero d := ⟨by omega⟩
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : ABKModel d) (L : ℤ) (omega : Cutoff.CutoffSample d)
        (m n : ℤ) (hnm : n < m) (jn : ℕ) (s1' s' s2 s : FractionalOrder),
        s1'.1 < s'.1 → s'.1 < s2.1 →
        0 < (s.1 - s'.1) * p.conjugate.exponent.toReal →
        (s.1 - s'.1) * p.conjugate.exponent.toReal < (d : ℝ) →
        (jn : ℤ) = m - n →
      ∀ (sigma0 : ℝ) (hsigma0 : 0 < sigma0) (g : Vec d → Vec d)
        (u v h : H1Function (openCubeSet (originCube d m))),
        IsDirichletSolutionOn (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
          (originCube d m) u h g →
        IsDirichletSolutionOn (fun _ => sigma0 • (1 : Mat d)) (originCube d m) v h g →
      ∀ Kg : ℝ, 0 ≤ Kg →
        s2.1 < 1 / 2 → 1 / 2 - (d : ℝ) / p.exponent.toReal < s2.1 →
        HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kg g →
      ∀ (Ccg E1 E2 Dg S Level : ℝ), 0 ≤ Ccg → 0 ≤ E1 → 0 ≤ E2 → 0 ≤ Dg → 0 ≤ S →
        C ≤ ENNReal.ofReal Ccg →
        Book.Ch02.parentTruncatedHomogenizationErrorInfinityOneScalar (originCube d m) n
            (by simpa [originCube] using hnm.le)
            (fluxCorrectedCoeffOn M L m (originCube d m) omega) sigma0 hsigma0 s1' ≤
          ENNReal.ofReal E1 →
        Book.Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar (originCube d m) n
            (by simpa [originCube] using hnm.le)
            (fluxCorrectedCoeffOn M L m (originCube d m) omega) sigma0 hsigma0
            (fractionalOrderHalf s1') ≤ ENNReal.ofReal E2 →
        ABK26.cubeEuclideanPositiveBesovOverlapESeminorm (originCube d m) s2 p g ≤
          ENNReal.ofReal Dg →
      ∀ (wgap : ℝ) (Gen : TriadicCube d → ℝ), wgap ≤ s'.1 - s1'.1 →
        (∀ R : TriadicCube d, 0 ≤ Gen R) →
        (∀ R : TriadicCube d,
          printedLocalEnergy (fluxCorrectedCoeffOn M L m (originCube d m) omega) u R ≤
            Gen R) →
        (∀ N : ℕ,
          coarseGrainingEnergyPartial (originCube d m) p.exponent.toReal wgap jn N Gen ≤
            S) →
        cgTestConst d (originCube d m) s.1 s'.1 p.conjugate.exponent.toReal *
            (Real.rpow 3 (s'.1 * (m : ℝ)) *
              coarseGrainingFinitePRHS Ccg s'.1 s2.1 sigma0 E1 E2 Dg S n) ≤
          Real.rpow 3 (s.1 * (m : ℝ)) * (sigma0 * Level) →
        WeakNegDualBoundOn (originCube d m) s.1
            (Real.rpow 3 (s.1 * (m : ℝ)) * sigma0 * Level)
            (fun x => matVecMul
              ((fluxCorrectedCoeffOn M L m (originCube d m) omega).toCoeffField x)
              (u.grad x) - sigma0 • v.grad x) ∧
          WeakNegDualBoundOn (originCube d m) s.1 (Real.rpow 3 (s.1 * (m : ℝ)) * Level)
            (fun x => u.grad x - v.grad x) := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨C, hCtop, hC⟩ := exists_printedCoarseGraining_of_fluxPair d hd p hp
  refine ⟨C, hCtop, ?_⟩
  intro M L omega m n hnm jn s1' s' s2 s hs1s hss2 hlo hhi hjn sigma0 hsigma0 g u v h
    hsol hcomp Kg hKg0 hs2lt hs2gt hKg Ccg E1 E2 Dg S Level hCcg0 hE10 hE20 hDg0 hS0
    hCdom hE1 hE2 hDg wgap Gen hw hGen0 hGen hS hlevelDual
  have hn : n ≤ (originCube d m).scale := by simpa [originCube] using hnm.le
  have hjn' : (jn : ℤ) = (originCube d m).scale - n := by
    simpa [originCube] using hjn
  set a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain (originCube d m)) :=
    fluxCorrectedCoeffOn M L m (originCube d m) omega with hadef
  have hgmem : MemCubeEuclideanFullWsp (originCube d m) s2 p g :=
    memCubeEuclideanFullWsp_of_holderHalf hKg0 hs2lt hs2gt hKg
  have hdisp := hC M L omega m n hnm s1' s' s2 hs1s hss2 sigma0 hsigma0 g hgmem u v h
    hsol hcomp
  have hSlot : weightedLocalSymmetricEnergyLp (originCube d m) n hn a u s1' s' p ≤
      ENNReal.ofReal S :=
    weightedLocalSymmetricEnergyLp_le_ofReal hn a u s1' s' p hw hjn' hGen0 hGen hS0 hS
  have hRle := localCoarseGrainingLpRHS_toReal_le hn a hsigma0 g u s1' s' s2 p hss2
    hCcg0 hE10 hE20 hDg0 hS0 hCdom hE1 hE2 hDg hSlot
  have hRtop := localCoarseGrainingLpRHS_ne_top hn a hsigma0 g u s1' s' s2 p hss2
    hCcg0 hE10 hE20 hDg0 hS0 hCdom hE1 hE2 hDg hSlot
  have hK0 : (0 : ℝ) ≤ cgTestConst d (originCube d m) s.1 s'.1 p.conjugate.exponent.toReal :=
    cgTestConst_nonneg d (originCube d m) hlo
  have hstep : cgTestConst d (originCube d m) s.1 s'.1 p.conjugate.exponent.toReal *
      (Real.rpow 3 (s'.1 * (m : ℝ)) *
        (localCoarseGrainingLpRHS C (originCube d m) n hn a sigma0 hsigma0 g u
          s1' s' s2 p).toReal) ≤
      Real.rpow 3 (s.1 * (m : ℝ)) * (sigma0 * Level) := by
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hK0) hlevelDual
    exact mul_le_mul_of_nonneg_left hRle (three_rpow_nonneg _)
  exact weakNegDualBounds_endpointLevels_of_displayOn (a := a) hsigma0 s' s p hlo hhi
    hRtop hdisp hstep

/-! ## 5. The produced constant at `ã`, NAMED -/

open Classical in
/-- **The printed coarse-graining constant `C(p,d)` of the `ã` lane, named.**

The sibling of the `a_L` lane's coarse-graining dual-bound constant: the re-cut
bundle refers to it in the slot condition `C(p,d) ≤ Ccg`. -/
def cgDualBoundConstFlux (d : ℕ) (p : FiniteLpExponent) : ℝ≥0∞ :=
  if h : 2 ≤ d ∧ (2 : ℝ≥0∞) ≤ p.exponent then
    Classical.choose (exists_weakNegDualBounds_of_fluxPair d h.1 p h.2)
  else 0

theorem cgDualBoundConstFlux_eq (d : ℕ) (hd : 2 ≤ d) (p : FiniteLpExponent)
    (hp : (2 : ℝ≥0∞) ≤ p.exponent) :
    cgDualBoundConstFlux d p =
      Classical.choose (exists_weakNegDualBounds_of_fluxPair d hd p hp) := by
  unfold cgDualBoundConstFlux
  rw [dite_eq_left (⟨hd, hp⟩ : 2 ≤ d ∧ (2 : ℝ≥0∞) ≤ p.exponent)]

theorem cgDualBoundConstFlux_lt_top (d : ℕ) (hd : 2 ≤ d) (p : FiniteLpExponent)
    (hp : (2 : ℝ≥0∞) ≤ p.exponent) : cgDualBoundConstFlux d p < ∞ := by
  have hspec := Classical.choose_spec (exists_weakNegDualBounds_of_fluxPair d hd p hp)
  rw [cgDualBoundConstFlux_eq d hd p hp]
  exact hspec.1

/-- The `Ccg` domination is free at the canonical pin. -/
theorem cgDualBoundConstFlux_dominates_self (d : ℕ) (hd : 2 ≤ d) (p : FiniteLpExponent)
    (hp : (2 : ℝ≥0∞) ≤ p.exponent) :
    cgDualBoundConstFlux d p ≤ ENNReal.ofReal (cgDualBoundConstFlux d p).toReal := by
  rw [ENNReal.ofReal_toReal (cgDualBoundConstFlux_lt_top d hd p hp).ne]

/-! ## 6. The Step-4 endpoint, generic in the field -/

/-- **THE STEP-4 ENDPOINT, GENERIC IN THE COEFFICIENT FIELD.**

The Step-4 energy endpoint with the cutoff field replaced by an
arbitrary field whose symmetric part is `ν Id`.  The proof is unchanged:
`HomStepFourEnergy.energy_split` reads the field only through `hsym`, and
`stepFourEnergyDisplay` never sees it at all.  The conclusion is
coefficient-FREE. -/
theorem stepFourEnergyEndpointOfField {m : ℤ} {A : CoeffField d} {nu : ℝ}
    {sigmaBarM s Kg Kh KhInf Cw Csch EB Ksup KHol : ℝ}
    {u v h : H1Function (openCubeSet (originCube d m))} {g : Vec d → Vec d}
    (hsym : ∀ x : Vec d, symmPart (A x) = nu • (1 : Mat d))
    (hsig : 0 < sigmaBarM) (hCw : 0 ≤ Cw) (hEB : 0 ≤ EB)
    (hD : 0 ≤ dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh)
    (hsup : 0 ≤ Ksup) (hhol : 0 ≤ KHol)
    (hsol : IsDirichletSolutionOn A (originCube d m) u h g)
    (hcomp : IsDirichletSolutionOn
      (fun _ => sigmaBarM • (1 : Mat d)) (originCube d m) v h g)
    (hiU : IntegrableOn (fun x => vecDot (u.grad x) (matVecMul (A x) (u.grad x)))
      (openCubeSet (originCube d m)) volume)
    (hiV : IntegrableOn (fun x => vecDot (v.grad x) (sigmaBarM • v.grad x))
      (openCubeSet (originCube d m)) volume)
    (hiC : IntegrableOn (fun x => vecDot (matVecMul (A x) (u.grad x)) (v.grad x))
      (openCubeSet (originCube d m)) volume)
    (hb : ∀ x ∈ openCubeSet (originCube d m), ‖v.grad x‖ ≤ Ksup)
    (hH : HolderSeminormBoundOn (openCubeSet (originCube d m)) s KHol v.grad)
    (hSch : wsInftyGauge (originCube d m) s Ksup KHol ≤
      Csch * (Real.rpow 3 (s * (m : ℝ)))⁻¹ *
        dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh)
    (hWf : WeakNegDualBoundOn (originCube d m) s
      (Real.rpow 3 (s * (m : ℝ)) * sigmaBarM *
        (Cw * EB * dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh))
      (fun x => matVecMul (A x) (u.grad x) - sigmaBarM • v.grad x))
    (hWg : WeakNegDualBoundOn (originCube d m) s
      (Real.rpow 3 (s * (m : ℝ)) *
        (Cw * EB * dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh))
      (fun x => u.grad x - v.grad x)) :
    |volumeAverage (openCubeSet (originCube d m))
          (fun y => nu * vecNormSq (u.grad y)) -
        volumeAverage (openCubeSet (originCube d m))
          (fun y => sigmaBarM * vecNormSq (v.grad y))| ≤
      2 * Cw * Csch * EB *
        (Real.sqrt sigmaBarM⁻¹ * Real.rpow 3 ((m : ℝ) / 2) * Kg +
            Real.sqrt sigmaBarM * (KhInf + Real.rpow 3 ((m : ℝ) / 2) * Kh)) ^ (2 : ℕ) := by
  have hsplit := energy_split (A := A) (Qc := originCube d m) (sigma := sigmaBarM)
    (nu := nu) (u := u) (v := v) (h := h) (g := g)
    (F := fun x => matVecMul (A x) (u.grad x))
    (fun _ => rfl) hsym hsol.2 hcomp.2 hsol.1 hcomp.1 hiU hiV hiC
  exact stepFourEnergyDisplay hsig hCw hEB hD hsup hhol hsplit hb hH hSch hWf hWg

/-! ## 7. Clause (C4)'s payload at `ã`, at the `s`-free Schauder constant -/

/-- **CLAUSE (C4)'s PAYLOAD, AT `ã_{L,m}` AND THE `s`-FREE CONSTANT.**

`HomSchauderSwap.stepFourEnergy_of_dualBounds_uniform` with every occurrence of
the cutoff field replaced by the printed flux-corrected field.  The conclusion
is byte-identical: it never mentions a coefficient. -/
theorem stepFourEnergyFlux_of_dualBounds_uniform (dimension : 2 ≤ d) {s : ℝ}
    (s_pos : 0 < s) (s_le : s ≤ 1 / 2) (M : ABKModel d) (L m : ℤ)
    (omega : Cutoff.CutoffSample d) (sigmaBarM Kg Kh KhInf Cw EB : ℝ)
    (u h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d)
    (hsig : 0 < sigmaBarM) (hCw : 0 ≤ Cw) (hEB : 0 ≤ EB)
    (hD : 0 ≤ dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh)
    (hKg : HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kg g)
    (hKhInf : ∀ x ∈ openCubeSet (originCube d m), ‖h.grad x‖ ≤ KhInf)
    (hKh : HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kh h.grad)
    (hsol : IsDirichletSolutionOn
      (fluxCorrectedCoeffOn M L m (originCube d m) omega).toCoeffField
      (originCube d m) u h g)
    (hiU : IntegrableOn (fun x => vecDot (u.grad x)
      (matVecMul ((fluxCorrectedCoeffOn M L m (originCube d m) omega).toCoeffField x)
        (u.grad x))) (openCubeSet (originCube d m)) volume)
    (hframe : ∀ v : H1Function (openCubeSet (originCube d m)),
      IsDirichletSolutionOn (fun _ => sigmaBarM • (1 : Mat d)) (originCube d m) v h g →
        IntegrableOn (fun x => vecDot (v.grad x) (sigmaBarM • v.grad x))
            (openCubeSet (originCube d m)) volume ∧
          IntegrableOn (fun x => vecDot
              (matVecMul
                ((fluxCorrectedCoeffOn M L m (originCube d m) omega).toCoeffField x)
                (u.grad x)) (v.grad x)) (openCubeSet (originCube d m)) volume ∧
            (WeakNegDualBoundOn (originCube d m) s
                (Real.rpow 3 (s * (m : ℝ)) * sigmaBarM *
                  (Cw * EB *
                    dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh))
                (fun x => matVecMul
                  ((fluxCorrectedCoeffOn M L m (originCube d m) omega).toCoeffField x)
                  (u.grad x) - sigmaBarM • v.grad x) ∧
              WeakNegDualBoundOn (originCube d m) s
                (Real.rpow 3 (s * (m : ℝ)) *
                  (Cw * EB *
                    dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh))
                (fun x => u.grad x - v.grad x))) :
    ∃ v : H1Function (openCubeSet (originCube d m)),
      IsDirichletSolutionOn (fun _ => sigmaBarM • (1 : Mat d)) (originCube d m) v h g ∧
        |volumeAverage (openCubeSet (originCube d m))
              (fun y => M.nu * vecNormSq (u.grad y)) -
            volumeAverage (openCubeSet (originCube d m))
              (fun y => sigmaBarM * vecNormSq (v.grad y))| ≤
          2 * Cw * stepFourSchauderConstU d * EB *
            (Real.sqrt sigmaBarM⁻¹ * Real.rpow 3 ((m : ℝ) / 2) * Kg +
                Real.sqrt sigmaBarM *
                  (KhInf + Real.rpow 3 ((m : ℝ) / 2) * Kh)) ^ (2 : ℕ) := by
  have hspec :=
    Classical.choose_spec (exists_comparator_schauder_package_uniform (d := d) dimension)
  rw [← show stepFourSchauderConstU d =
      Classical.choose (exists_comparator_schauder_package_uniform (d := d) dimension) by
    rw [stepFourSchauderConstU, dite_eq_left dimension]] at hspec
  obtain ⟨_hCschPos, hpack⟩ := hspec
  obtain ⟨v, hcomp, Ksup, KHol, hsup, hhol, hb, hH, hgauge⟩ :=
    hpack s s_pos s_le m sigmaBarM hsig g h Kg KhInf Kh hKg hKhInf hKh
  obtain ⟨hiV, hiC, hWf, hWg⟩ := hframe v hcomp
  exact ⟨v, hcomp, stepFourEnergyEndpointOfField
    (symmPart_fluxCorrectedCoeffOn_eq_nu M L m (originCube d m) omega)
    hsig hCw hEB hD hsup hhol hsol hcomp hiU hiV hiC hb hH hgauge hWf hWg⟩

end

end Algsuperdiff.Section4.Provider.Homogenization
