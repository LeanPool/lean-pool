/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.ConstantDatumCoreEnergy
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.ReindexSlot

/-!
# ReindexEnergy

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The interior Caccioppoli energy at the slot `n+3`: the `(n+3)` family on `□_{n+2}`

The sharpened interior energy estimate is proved at
the **proved** slot: the coefficient family is `ã_{L,n+2}`, the comparator is
`σ_{n+2}`, and the good event is `𝒢(n+2, z; s/8, 1/2)`.  The frozen general
clause reads the good event and the flux index at `n+3`, so this module
re-runs the same estimate with

* the **comparator** `σ_{n+3}` in place of `σ_{n+2}`;
* the **caps** read on the chain's own cube `□_{n+2}` through the depth-`1`
  centre-child transport of `ReindexSlot` (factor `3^{s/8} ≤ 3^{1/8}`).

Everything geometric is **unchanged**: the Caccioppoli triple is the author's
own `outer = □_{n+2}`, `patch = w + □_{n+1}`, `core = w + □_n`.  The cube of
the display, its `3`-power weights `3^{-2(n+2)}` and `3^{2s(n+2)}`, the
parameter pair `(1/4, s/4)`, the Besov index `s/2 → s` comparison and the force
envelope `s^{-6}` are all the proved ones, byte-for-byte.

## References

* ABK26, `l.coarse.grained.Caccioppoli.RHS`; `e.energy.bound.interior`;
  `l.harmonic.approximation.good.scales`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03 MeasureTheory
open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The display object, in the cube's own frame -/

/-- **The sharpened interior Caccioppoli right-hand side at the `n+3` slot.**
The sharpened interior right-hand side with the comparator index
moved to `n+3`; the cube and both `3`-power weights are unchanged. -/
def constantDatumEnergyRHSAddThree (M : ABKModel d) (n : ℤ) (s : ℝ)
    (u : H1Function (Ch02.cubeDomain (originCube d (n + 2)) : Set (Vec d)))
    (g : Vec d → Vec d) : ℝ :=
  (Annealed.sigmaBar M (n + 3) : ℝ) *
      Real.rpow (3 : ℝ) (-2 * (((n + 2 : ℤ)) : ℝ)) *
      normalizedL2SqOnSet (openCubeSet (originCube d (n + 2)))
        (fun y => u.toFun y -
          volumeAverage (openCubeSet (originCube d (n + 2))) u.toFun) +
    Real.rpow s (-6 : ℝ) * (Annealed.sigmaBar M (n + 3) : ℝ)⁻¹ *
      scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d (n + 2)) s g ^ (2 : ℕ)

/-! ## 2. The two `private` arithmetic helpers -/

/-- Squaring a real power of a positive base. -/
private theorem rpow_sq {x : ℝ} (hx : 0 < x) (a : ℝ) :
    Real.rpow x a ^ (2 : ℕ) = Real.rpow x (2 * a) := by
  have h : Real.rpow x (a + a) = Real.rpow x a * Real.rpow x a := Real.rpow_add hx a a
  have h2 : (2 : ℝ) * a = a + a := by ring
  rw [h2, h, pow_two]

/-- `(s/4)^{-3} = 64 s^{-3}`. -/
private theorem rpow_quarter_neg_three {s : ℝ} (hs : 0 < s) :
    Real.rpow (s / 4) (-3 : ℝ) = 64 * Real.rpow s (-3 : ℝ) := by
  have h4 : Real.rpow (4 : ℝ) (-3 : ℝ) = (64 : ℝ)⁻¹ := by
    rw [Real.rpow_eq_pow, show (-3 : ℝ) = ((-3 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
    norm_num
  rw [Real.rpow_eq_pow, Real.div_rpow hs.le (by norm_num),
    ← Real.rpow_eq_pow s, ← Real.rpow_eq_pow (4 : ℝ), h4]
  field_simp

/-- The cap composition of the sharpened display, on abstract reals. -/
private theorem constantDatum_cap_arith
    {E P Pb lam1 Kc sig S X t3 linv B Bs s3 s6 KC Cout : ℝ}
    (hmain : E ≤ KC * (P * lam1 * (S * X + (t3 * linv * B) ^ (2 : ℕ)) +
      t3 * linv * B ^ (2 : ℕ)))
    (hP : P ≤ Pb) (hPb0 : 0 ≤ Pb)
    (hlam1 : lam1 ≤ Kc * sig) (hlam10 : 0 ≤ lam1)
    (hlinv : linv ≤ Kc * sig⁻¹) (hlinv0 : 0 ≤ linv)
    (ht3 : t3 = 64 * s3) (hs3s6 : s3 ≤ s6) (hs30 : 0 ≤ s3) (hs32 : s3 ^ (2 : ℕ) = s6)
    (hB : B ≤ Bs) (hB0 : 0 ≤ B)
    (hS0 : 0 ≤ S) (hX0 : 0 ≤ X) (hsig : 0 < sig) (hKc0 : 0 ≤ Kc) (hKC0 : 0 ≤ KC)
    (hCout : KC * (Pb * Kc + 4096 * (Pb * Kc ^ (3 : ℕ)) + 64 * Kc) ≤ Cout) :
    E ≤ Cout * (sig * S * X + s6 * sig⁻¹ * Bs ^ (2 : ℕ)) := by
  have hsiginv0 : (0 : ℝ) ≤ sig⁻¹ := inv_nonneg.mpr hsig.le
  have hs60 : (0 : ℝ) ≤ s6 := le_trans hs30 hs3s6
  have hBs0 : (0 : ℝ) ≤ Bs := le_trans hB0 hB
  have hA1 : (0 : ℝ) ≤ sig * S * X := mul_nonneg (mul_nonneg hsig.le hS0) hX0
  have hA2 : (0 : ℝ) ≤ s6 * sig⁻¹ * Bs ^ (2 : ℕ) :=
    mul_nonneg (mul_nonneg hs60 hsiginv0) (pow_nonneg hBs0 2)
  have hT1 : P * lam1 * (S * X) ≤ Pb * Kc * (sig * S * X) := by
    have h1 : P * lam1 ≤ Pb * (Kc * sig) := mul_le_mul hP hlam1 hlam10 hPb0
    have h2 := mul_le_mul_of_nonneg_right h1 (mul_nonneg hS0 hX0)
    calc P * lam1 * (S * X) ≤ Pb * (Kc * sig) * (S * X) := h2
      _ = Pb * Kc * (sig * S * X) := by ring
  have hprod : t3 * linv * B ≤ 64 * s3 * (Kc * sig⁻¹) * Bs := by
    have hfac : (0 : ℝ) ≤ 64 * s3 := by linarith only [hs30]
    have h1 : 64 * s3 * linv ≤ 64 * s3 * (Kc * sig⁻¹) :=
      mul_le_mul_of_nonneg_left hlinv hfac
    have h2 : (0 : ℝ) ≤ 64 * s3 * (Kc * sig⁻¹) :=
      mul_nonneg hfac (mul_nonneg hKc0 hsiginv0)
    rw [ht3]
    exact mul_le_mul h1 hB hB0 h2
  have hprod0 : (0 : ℝ) ≤ t3 * linv * B := by
    rw [ht3]
    exact mul_nonneg (mul_nonneg (by linarith only [hs30]) hlinv0) hB0
  have hsq : (t3 * linv * B) ^ (2 : ℕ) ≤
      4096 * s6 * (Kc ^ (2 : ℕ) * (sig⁻¹) ^ (2 : ℕ)) * Bs ^ (2 : ℕ) := by
    refine le_trans (pow_le_pow_left₀ hprod0 hprod 2) (le_of_eq ?_)
    rw [← hs32]
    ring
  have hsigsq : sig * (sig⁻¹) ^ (2 : ℕ) = sig⁻¹ := by
    field_simp
  have hT2 : P * lam1 * (t3 * linv * B) ^ (2 : ℕ) ≤
      4096 * (Pb * Kc ^ (3 : ℕ)) * (s6 * sig⁻¹ * Bs ^ (2 : ℕ)) := by
    have h1 : P * lam1 ≤ Pb * (Kc * sig) := mul_le_mul hP hlam1 hlam10 hPb0
    have hstep := mul_le_mul h1 hsq (pow_nonneg hprod0 2)
      (mul_nonneg hPb0 (mul_nonneg hKc0 hsig.le))
    refine le_trans hstep (le_of_eq ?_)
    calc Pb * (Kc * sig) * (4096 * s6 * (Kc ^ (2 : ℕ) * (sig⁻¹) ^ (2 : ℕ)) * Bs ^ (2 : ℕ))
        = 4096 * (Pb * Kc ^ (3 : ℕ)) * (s6 * (sig * (sig⁻¹) ^ (2 : ℕ)) * Bs ^ (2 : ℕ)) := by
          ring
      _ = 4096 * (Pb * Kc ^ (3 : ℕ)) * (s6 * sig⁻¹ * Bs ^ (2 : ℕ)) := by rw [hsigsq]
  have hT3 : t3 * linv * B ^ (2 : ℕ) ≤ 64 * Kc * (s6 * sig⁻¹ * Bs ^ (2 : ℕ)) := by
    have hBsq : B ^ (2 : ℕ) ≤ Bs ^ (2 : ℕ) := pow_le_pow_left₀ hB0 hB 2
    have h1 : t3 * linv ≤ 64 * s6 * (Kc * sig⁻¹) := by
      have ha : t3 ≤ 64 * s6 := by
        rw [ht3]
        linarith only [hs3s6]
      have hb : (0 : ℝ) ≤ 64 * s6 := by linarith only [hs60]
      exact mul_le_mul ha hlinv hlinv0 hb
    have h2 : (0 : ℝ) ≤ 64 * s6 * (Kc * sig⁻¹) :=
      mul_nonneg (by linarith only [hs60]) (mul_nonneg hKc0 hsiginv0)
    refine le_trans (mul_le_mul h1 hBsq (pow_nonneg hB0 2) h2) (le_of_eq ?_)
    ring
  have hsum : P * lam1 * (S * X + (t3 * linv * B) ^ (2 : ℕ)) + t3 * linv * B ^ (2 : ℕ) ≤
      (Pb * Kc + 4096 * (Pb * Kc ^ (3 : ℕ)) + 64 * Kc) *
        (sig * S * X + s6 * sig⁻¹ * Bs ^ (2 : ℕ)) := by
    have hexp : P * lam1 * (S * X + (t3 * linv * B) ^ (2 : ℕ)) =
        P * lam1 * (S * X) + P * lam1 * (t3 * linv * B) ^ (2 : ℕ) := by ring
    have hc1 : Pb * Kc * (sig * S * X) ≤
        (Pb * Kc + 4096 * (Pb * Kc ^ (3 : ℕ)) + 64 * Kc) * (sig * S * X) := by
      have hrest : (0 : ℝ) ≤ 4096 * (Pb * Kc ^ (3 : ℕ)) + 64 * Kc := by
        have h1 : (0 : ℝ) ≤ Pb * Kc ^ (3 : ℕ) := mul_nonneg hPb0 (pow_nonneg hKc0 3)
        linarith only [h1, hKc0]
      have := mul_le_mul_of_nonneg_right hrest hA1
      linarith only [this]
    have hc2 : (4096 * (Pb * Kc ^ (3 : ℕ)) + 64 * Kc) * (s6 * sig⁻¹ * Bs ^ (2 : ℕ)) ≤
        (Pb * Kc + 4096 * (Pb * Kc ^ (3 : ℕ)) + 64 * Kc) * (s6 * sig⁻¹ * Bs ^ (2 : ℕ)) := by
      have hrest : (0 : ℝ) ≤ Pb * Kc := mul_nonneg hPb0 hKc0
      have := mul_le_mul_of_nonneg_right hrest hA2
      linarith only [this]
    have hd : 4096 * (Pb * Kc ^ (3 : ℕ)) * (s6 * sig⁻¹ * Bs ^ (2 : ℕ)) +
        64 * Kc * (s6 * sig⁻¹ * Bs ^ (2 : ℕ)) =
        (4096 * (Pb * Kc ^ (3 : ℕ)) + 64 * Kc) * (s6 * sig⁻¹ * Bs ^ (2 : ℕ)) := by ring
    have hexpand : (Pb * Kc + 4096 * (Pb * Kc ^ (3 : ℕ)) + 64 * Kc) *
        (sig * S * X + s6 * sig⁻¹ * Bs ^ (2 : ℕ)) =
        (Pb * Kc + 4096 * (Pb * Kc ^ (3 : ℕ)) + 64 * Kc) * (sig * S * X) +
          (Pb * Kc + 4096 * (Pb * Kc ^ (3 : ℕ)) + 64 * Kc) *
            (s6 * sig⁻¹ * Bs ^ (2 : ℕ)) := by ring
    rw [hexp, hexpand]
    linarith only [hT1, hT2, hT3, hc1, hc2, hd]
  have hbig : (0 : ℝ) ≤ sig * S * X + s6 * sig⁻¹ * Bs ^ (2 : ℕ) := by
    linarith only [hA1, hA2]
  calc E ≤ KC * (P * lam1 * (S * X + (t3 * linv * B) ^ (2 : ℕ)) + t3 * linv * B ^ (2 : ℕ)) :=
        hmain
    _ ≤ KC * ((Pb * Kc + 4096 * (Pb * Kc ^ (3 : ℕ)) + 64 * Kc) *
          (sig * S * X + s6 * sig⁻¹ * Bs ^ (2 : ℕ))) := mul_le_mul_of_nonneg_left hsum hKC0
    _ = KC * (Pb * Kc + 4096 * (Pb * Kc ^ (3 : ℕ)) + 64 * Kc) *
          (sig * S * X + s6 * sig⁻¹ * Bs ^ (2 : ℕ)) := by ring
    _ ≤ Cout * (sig * S * X + s6 * sig⁻¹ * Bs ^ (2 : ℕ)) :=
        mul_le_mul_of_nonneg_right hCout hbig

/-- The sub-cube ratio maximum, unfolded.  A `rfl` lemma, the `On` sibling of
`LambdaCaps.fluxCorrectedEllipticityRatioMax_def`. -/
private theorem fluxCorrectedEllipticityRatioMaxOn_def (M : ABKModel d) (L k : ℤ)
    (Q : TriadicCube d) (s : ℝ) (omega : Cutoff.CutoffSample d) :
    fluxCorrectedEllipticityRatioMaxOn M L k Q s omega =
      max ((Annealed.sigmaBar M k : ℝ)⁻¹ *
          Ch02.LambdaSq Q s (.finite 2)
            (Support.fluxCorrectedCoeffFamily M L k (originCube d k) omega))
        ((Annealed.sigmaBar M k : ℝ) *
          (Ch02.lambdaSq Q s (.finite 2)
            (Support.fluxCorrectedCoeffFamily M L k (originCube d k) omega))⁻¹) :=
  rfl

/-! ## 3. The equation at the `(n+3)` family -/

theorem isForcedEquation_fluxCorrectedCoeffFamily_translated_addThree {m n : ℤ}
    (M : ABKModel d) (L : ℤ) (z : Vec d) (omega : Cutoff.CutoffSample d)
    {u : H1Function (openCubeSet (originCube d m))} {g : Vec d → Vec d}
    (hz : z ∈ openCubeSet (originCube d m))
    (hfr : ((fun y => z + y) '' openCubeSet (originCube d (n + 2))) ∩
        frontier (openCubeSet (originCube d m)) = ∅)
    (heq : Support.IsDivFormWeakSolutionOn
      (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
      (openCubeSet (originCube d m)) u g) :
    IsForcedEquation (originCube d (n + 2))
      (Support.fluxCorrectedCoeffFamily M L (n + 3) (originCube d (n + 3))
        (Cutoff.translateCutoffSample z omega))
      (H1Function.untranslate z
        (u.restrict (isOpen_translateSet_openCubeSet z (n + 2))
          (translateSet_openCubeSet_subset_of_frontier_inter_empty hz hfr)))
      (fun x => -g (x + z)) := by
  have hrestrict := isDivFormWeakSolutionOn_restrict
    (isOpen_translateSet_openCubeSet z (n + 2))
    (translateSet_openCubeSet_subset_of_frontier_inter_empty hz hfr) heq
  have huntrans := isDivFormWeakSolutionOn_translateCutoffSample M L z omega hrestrict
  have hshift := isDivFormWeakSolutionOn_fluxCorrectedField M L (n + 3)
    (originCube d (n + 3)) (Cutoff.translateCutoffSample z omega) huntrans
  refine isForcedEquation_neg_of_isDivFormWeakSolutionOn ?_
  rw [fluxCorrectedCoeffFamily_coeffOn_toCoeffField M L (n + 3)
    (originCube d (n + 3)) (originCube d (n + 2))
    (Cutoff.translateCutoffSample z omega)]
  exact hshift

/-! ## 4. The energy estimate on the good event, in the cube's own frame -/

/-- **The sharpened `e.energy.bound.interior` at the `n+3` slot.**

Almost surely on the frozen general clause's good event
`𝒢(n+3, z; s/8, 1/2)`, for every `L ≥ n+3`, every window centre `w` whose
Dirichlet patch `w + □_{n+1}` sits inside `□_{n+2}`, and every `H¹(□_{n+2})`
solution of `-∇·ã_{L,n+3}∇u = ∇·g`,

```text
  ⨍_{□_{n+2} ∩ (w+□_n)} ∇u · ã_{L,n+3} ∇u ≤ Cout · constantDatumEnergyRHSAddThree M n s u g .
```
-/
theorem ae_constantDatumEnergy_harmonicSlot_addThree (d : ℕ) [NeZero d] :
    ∃ C Cout : ℝ, 0 < C ∧ 0 < Cout ∧
      ∀ (M : ABKModel d) (s : ℝ), s ∈ Set.Icc (64 * M.gamma) 1 →
        M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
            Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * (1 / 2) →
        ∀ hs : 0 < s, ∀ (n : ℤ) (z : Vec d),
          ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
            omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
                (Support.cgEllipLowerConstant d) (n + 3) z
                ⟨s / 8, by linarith only [hs]⟩ (1 / 2) →
              ∀ L : ℤ, n + 3 ≤ L → ∀ (w : Vec d) (g : Vec d → Vec d)
                (u : H1Function
                  (Ch02.cubeDomain (originCube d (n + 2)) : Set (Vec d))),
                openCubeAtScale w (n + 1) ⊆ openCubeSet (originCube d (n + 2)) →
                ForceBesovRegularity (originCube d (n + 2)) s g →
                IsForcedEquation (originCube d (n + 2))
                    (Support.fluxCorrectedCoeffFamily M L (n + 3)
                      (originCube d (n + 3))
                      (Cutoff.translateCutoffSample z omega)) u g →
                  localizedCoeffEnergyValue
                      (caccioppoliCoreSet (originCube d (n + 2)) w)
                      ((Support.fluxCorrectedCoeffFamily M L (n + 3)
                        (originCube d (n + 3))
                        (Cutoff.translateCutoffSample z omega)).coeffOn
                        (originCube d (n + 2))) u ≤
                    Cout * constantDatumEnergyRHSAddThree M n s u g := by
  obtain ⟨C₁, KC, hC₁, hKC, hcore⟩ := exists_constantDatumCoreEnergy d
  obtain ⟨C, Kc, hCpos, hKcpos, hcaps⟩ := ae_boundLambdasByEs_centreChild d
  set Pb : ℝ := (2 * max 1 C₁) ^ (4 : ℕ) * 4 * (Kc ^ (2 : ℕ)) ^ (2 : ℕ) with hPbdef
  have hPbpos : 0 < Pb := by
    have hCm : (0 : ℝ) < 2 * max 1 C₁ := by
      have : (1 : ℝ) ≤ max 1 C₁ := le_max_left _ _
      linarith only [this]
    rw [hPbdef]
    positivity
  refine ⟨C, KC * (Pb * Kc + 4096 * (Pb * Kc ^ (3 : ℕ)) + 64 * Kc), hCpos, ?_, ?_⟩
  · have h1 : 0 < Pb * Kc := mul_pos hPbpos hKcpos
    have h2 : 0 < 4096 * (Pb * Kc ^ (3 : ℕ)) := by positivity
    have h3 : 0 < 64 * Kc := by linarith only [hKcpos]
    exact mul_pos hKC (by linarith only [h1, h2, h3])
  intro M s hsrange hregime hsmall hs n z
  filter_upwards [hcaps M s hsrange hregime hsmall hs n z] with omega hcap
  intro hmem L hL w g u hpatch hgreg hu
  have hs1 : s ≤ 1 := hsrange.2
  have hsig : (0 : ℝ) < (Annealed.sigmaBar M (n + 3) : ℝ) := (Annealed.sigmaBar M (n + 3)).2
  set aFam : CoeffFamily d := Support.fluxCorrectedCoeffFamily M L (n + 3)
    (originCube d (n + 3)) (Cutoff.translateCutoffSample z omega) with haFam
  have hgreg' : ForceBesovRegularity (originCube d (n + 2)) (2 * (s / 4)) g :=
    CubeVectorBesovHRegularity.of_exponent_le hgreg (by linarith only [hs])
  have hscale : (originCube d (n + 2)).scale - 1 = n + 1 := by
    change n + 2 - 1 = n + 1
    ring
  have hpatch' : openCubeAtScale w ((originCube d (n + 2)).scale - 1) ⊆
      openCubeSet (originCube d (n + 2)) := by
    rw [hscale]
    exact hpatch
  have hmain := hcore (t := s / 4)
    (c := volumeAverage (openCubeSet (originCube d (n + 2))) u.toFun) u hu
    (by linarith only [hs]) (by linarith only [hs1]) hpatch' hgreg'
  -- the two `q = 2` caps, read off the centre-child ratio maximum
  have hcapU : (Annealed.sigmaBar M (n + 3) : ℝ)⁻¹ *
      Ch02.LambdaSq (originCube d (n + 2)) (1 / 4 / 2) (.finite 2) aFam ≤ Kc := by
    have h := hcap hmem L hL (1 / 4 / 2) (by linarith only [hs1])
    rw [fluxCorrectedEllipticityRatioMaxOn_def] at h
    exact le_trans (le_max_left _ _) h
  have hcapL : (Annealed.sigmaBar M (n + 3) : ℝ) *
      (Ch02.lambdaSq (originCube d (n + 2)) (s / 4 / 2) (.finite 2) aFam)⁻¹ ≤ Kc := by
    have h := hcap hmem L hL (s / 4 / 2) (by linarith only [])
    rw [fluxCorrectedEllipticityRatioMaxOn_def] at h
    exact le_trans (le_max_right _ _) h
  have hcapL2 : (Annealed.sigmaBar M (n + 3) : ℝ) *
      (Ch02.lambdaSq (originCube d (n + 2)) (s / 4) (.finite 2) aFam)⁻¹ ≤ Kc := by
    have h := hcap hmem L hL (s / 4) (by linarith only [hs])
    rw [fluxCorrectedEllipticityRatioMaxOn_def] at h
    exact le_trans (le_max_right _ _) h
  -- the `q = 1` ingredients and the prefactor
  have hLam := LambdaS_le_of_ratio_cap (originCube d (n + 2)) aFam (u := 1 / 4)
    (by norm_num) hsig hcapU
  have hlamInv := lambdaS_inv_le_of_ratio_cap (originCube d (n + 2)) aFam (u := s / 4)
    (by linarith only [hs]) hsig hcapL
  have hlam1 : Ch02.lambdaS (originCube d (n + 2)) (s / 4) aFam ≤ Kc *
      (Annealed.sigmaBar M (n + 3) : ℝ) :=
    le_trans (lambdaS_le_LambdaS (originCube d (n + 2)) _ (by norm_num)
      (by linarith only [hs])) hLam
  have hTheta : Ch02.ThetaRatio (originCube d (n + 2)) (1 / 4) (s / 4) aFam ≤
      (Kc ^ (2 : ℕ)) := by
    have h := thetaRatio_le_of_caps (originCube d (n + 2)) aFam
      (by norm_num : (0 : ℝ) < 1 / 4) (by linarith only [hs] : (0 : ℝ) < s / 4)
      hLam hlamInv
    have heq : Kc * (Annealed.sigmaBar M (n + 3) : ℝ) *
        (Kc * (Annealed.sigmaBar M (n + 3) : ℝ)⁻¹) = Kc ^ (2 : ℕ) := by
      field_simp
    rw [heq] at h
    exact h
  have hP := caccioppoliWithRHSPrefactor_quarter_le (Q := originCube d (n + 2))
    (a := aFam) (C := C₁) (s := s) hC₁ hs hs1 hTheta
  have hlinv : Real.rpow (Ch02.lambdaSq (originCube d (n + 2)) (s / 4) (.finite 2) aFam)
      (-1 : ℝ) ≤ Kc * (Annealed.sigmaBar M (n + 3) : ℝ)⁻¹ := by
    rw [Real.rpow_eq_pow, Real.rpow_neg_one]
    have h2 := mul_le_mul_of_nonneg_left hcapL2 (inv_nonneg.mpr hsig.le)
    rw [inv_mul_cancel_left₀ hsig.ne'] at h2
    calc (Ch02.lambdaSq (originCube d (n + 2)) (s / 4) (.finite 2) aFam)⁻¹
        ≤ (Annealed.sigmaBar M (n + 3) : ℝ)⁻¹ * Kc := h2
      _ = Kc * (Annealed.sigmaBar M (n + 3) : ℝ)⁻¹ := by ring
  have hlam10 : 0 ≤ Ch02.lambdaS (originCube d (n + 2)) (s / 4) aFam := by
    rw [Ch02.lambdaS]
    exact Ch02.lambdaSq_finite_nonneg _ _ (by linarith only [hs]) (by norm_num)
  have hlinv0 : (0 : ℝ) ≤ Real.rpow
      (Ch02.lambdaSq (originCube d (n + 2)) (s / 4) (.finite 2) aFam) (-1 : ℝ) :=
    Real.rpow_nonneg
      (Ch02.lambdaSq_finite_nonneg _ _ (by linarith only [hs]) (by norm_num)) _
  have hBnn : 0 ≤ scaleNormalizedPositiveBesovVectorSeminormTwo
      (originCube d (n + 2)) (2 * (s / 4)) g :=
    cubeBesovPositiveVectorSeminormTwo_nonneg_of_bddAbove _ _ g
      hgreg'.partialSeminorms_bddAbove
  have hB : scaleNormalizedPositiveBesovVectorSeminormTwo
        (originCube d (n + 2)) (2 * (s / 4)) g ≤
      scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d (n + 2)) s g :=
    cubeBesovPositiveVectorSeminormTwo_le_of_exponent_le_of_bddAbove
      (originCube d (n + 2)) g (by linarith only [hs])
      hgreg.partialSeminorms_bddAbove
  have hS0 : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (-2 * (((n + 2 : ℤ)) : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hX0 : 0 ≤ normalizedL2SqOnSet (openCubeSet (originCube d (n + 2)))
      (fun y => u.toFun y -
        volumeAverage (openCubeSet (originCube d (n + 2))) u.toFun) :=
    normalizedL2SqOnSet_nonneg _ _ (measurableSet_openCubeSet _)
  have ht3 : Real.rpow (s / 4) (-3 : ℝ) = 64 * Real.rpow s (-3 : ℝ) :=
    rpow_quarter_neg_three hs
  have hs3s6 : Real.rpow s (-3 : ℝ) ≤ Real.rpow s (-6 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hs hs1 (by norm_num)
  have hs30 : (0 : ℝ) ≤ Real.rpow s (-3 : ℝ) := Real.rpow_nonneg hs.le _
  have hs32 : Real.rpow s (-3 : ℝ) ^ (2 : ℕ) = Real.rpow s (-6 : ℝ) := by
    rw [rpow_sq hs]
    congr 1
    norm_num
  have hscaleeq : (((originCube d (n + 2)).scale : ℤ) : ℝ) = (((n + 2 : ℤ)) : ℝ) := by
    rw [scale_originCube]
  rw [hscaleeq] at hmain
  rw [constantDatumEnergyRHSAddThree]
  exact constantDatum_cap_arith hmain hP hPbpos.le hlam1 hlam10 hlinv hlinv0 ht3
    hs3s6 hs30 hs32 hB hBnn hS0 hX0 hsig hKcpos.le hKC.le (le_refl _)

/-! ## 5. The display in the frozen theorem's own carriers -/

/-- **The sharpened right-hand side at the `n+3` slot, in the anchor's own
carriers.** -/
def constantDatumAnchorEnergyRHSOnAddThree (M : ABKModel d) (n : ℤ) (s : ℝ) (W : Set (Vec d))
    (f : Vec d → ℝ) (g : Vec d → Vec d) : ℝ :=
  (Annealed.sigmaBar M (n + 3) : ℝ) *
      Real.rpow (3 : ℝ) (-2 * (((n + 2 : ℤ)) : ℝ)) *
      (eLpNorm (fun y => f y - volumeAverage W f) 2
        (Support.normalizedVolumeMeasureOn W)).toReal ^ (2 : ℕ) +
    Real.rpow s (-6 : ℝ) * (Annealed.sigmaBar M (n + 3) : ℝ)⁻¹ *
      Real.rpow (3 : ℝ) (2 * s * (((n + 2 : ℤ)) : ℝ)) *
      (Support.normalizedGagliardoESeminormOn W s g).toReal ^ (2 : ℕ)

/-- **The carrier conversion of the `n+3` display.** -/
theorem constantDatumEnergyRHS_le_anchorRHS_addThree [NeZero d] (M : ABKModel d) (n : ℤ)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) {z : Vec d} {f : Vec d → ℝ}
    (v : H1Function (Ch02.cubeDomain (originCube d (n + 2)) : Set (Vec d)))
    (hv : v.toFun = fun y => f (y + z))
    (hmem : MemLp (fun y => f (y + z)) 2 (normalizedCubeMeasure (originCube d (n + 2))))
    (g : Vec d → Vec d)
    (hgL2 : MemLp g 2 (Support.normalizedVolumeMeasureOn
      ((fun y' => z + y') '' openCubeSet (originCube d (n + 2)))))
    (hgW : MemLp (Gagliardo.gagliardoKernel s 2 g) 2
      (Support.normalizedGagliardoMeasureOn
        ((fun y' => z + y') '' openCubeSet (originCube d (n + 2))))) :
    constantDatumEnergyRHSAddThree M n s v (fun y => -g (y + z)) ≤
      (besovGagliardoConstant d ^ (2 : ℕ) + 1) *
        constantDatumAnchorEnergyRHSOnAddThree M n s
          ((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) f g := by
  have hsig : (0 : ℝ) < (Annealed.sigmaBar M (n + 3) : ℝ) :=
    (Annealed.sigmaBar M (n + 3)).2
  have hgreg : ForceBesovRegularity (originCube d (n + 2)) s (fun y => -g (y + z)) :=
    forceBesovRegularity_translated_neg (originCube d (n + 2)) hs hs1 hgL2 hgW
  have hbes := besovVectorSeminormTwo_translated_neg_le_gagliardo_window
    (originCube d (n + 2)) hs hs1 hgL2 hgW
  have hBesnn : 0 ≤ scaleNormalizedPositiveBesovVectorSeminormTwo
      (originCube d (n + 2)) s (fun y => -g (y + z)) :=
    cubeBesovPositiveVectorSeminormTwo_nonneg_of_bddAbove _ s _
      hgreg.partialSeminorms_bddAbove
  rw [constantDatumEnergyRHSAddThree, constantDatumAnchorEnergyRHSOnAddThree]
  simp only [hv]
  rw [normalizedL2SqOnSet_translate_sub_average_eq_eLpNorm_sq_image_add
      (originCube d (n + 2)) f hmem,
    ← cubeBesovScaleWeight_neg_originCube_sq (d := d) (n + 2) s]
  exact anchor_stitch
    (mul_nonneg hsig.le (Real.rpow_nonneg (by norm_num) _))
    (mul_nonneg (Real.rpow_nonneg hs.le _) (inv_nonneg.mpr hsig.le))
    (pow_nonneg ENNReal.toReal_nonneg 2) hBesnn (besovGagliardoConstant_nonneg d)
    (cubeBesovScaleWeight_nonneg (-s) _) ENNReal.toReal_nonneg hbes

/-! ## 6. The energy estimate at the anchor's own geometry -/

/-- **The `(n+3)` interior energy estimate, at the frozen statement's binders.**

Verbatim the sharpened interior energy estimate — same
hypotheses (with the frozen binder `n + 3 ≤ m` and the general clause's good
event),
same left-hand energy value, same window — with the coefficient family and the
comparator index at `n+3`. -/
theorem ae_constantDatumEnergy_anchorWindow_addThree (d : ℕ) [NeZero d] :
    ∃ C Cout : ℝ, 0 < C ∧ 0 < Cout ∧
      ∀ (M : ABKModel d) (s : ℝ), s ∈ Set.Icc (64 * M.gamma) 1 →
        M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
            Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * (1 / 2) →
        ∀ hs : 0 < s, ∀ L m n : ℤ, m ≤ L → n + 3 ≤ m → ∀ x z : Vec d,
          ∀ hz : z ∈ openCubeSet (originCube d m),
            (fun y => x + y) '' openCubeSet (originCube d n) ⊆
              ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
                openCubeSet (originCube d m) →
            ∀ hfr : ((fun y => z + y) '' openCubeSet (originCube d (n + 2))) ∩
                frontier (openCubeSet (originCube d m)) = ∅,
              ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
                omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
                    (Support.cgEllipLowerConstant d) (n + 3) z
                    ⟨s / 8, by linarith only [hs]⟩ (1 / 2) →
                  ∀ (u hdat : H1Function (openCubeSet (originCube d m)))
                    (g : Vec d → Vec d),
                    Support.IsDirichletSolutionOn
                        (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                        (originCube d m) u hdat g →
                    MemLp g 2
                      (Support.normalizedVolumeMeasureOn
                        (((fun y' => z + y') ''
                            openCubeSet (originCube d (n + 2))) ∩
                          openCubeSet (originCube d m))) →
                    MemLp (Gagliardo.gagliardoKernel s 2 g) 2
                      (Support.normalizedGagliardoMeasureOn
                        (((fun y' => z + y') ''
                            openCubeSet (originCube d (n + 2))) ∩
                          openCubeSet (originCube d m))) →
                      localizedCoeffEnergyValue
                          ((fun y => (x - z) + y) '' openCubeSet (originCube d n))
                          ((Support.fluxCorrectedCoeffFamily M L (n + 3)
                            (originCube d (n + 3))
                            (Cutoff.translateCutoffSample z omega)).coeffOn
                            (originCube d (n + 2)))
                          (H1Function.untranslate z
                            (u.restrict (isOpen_translateSet_openCubeSet z (n + 2))
                              (translateSet_openCubeSet_subset_of_frontier_inter_empty
                                hz hfr))) ≤
                        Cout * constantDatumAnchorEnergyRHSOnAddThree M n s
                          (((fun y' => z + y') ''
                              openCubeSet (originCube d (n + 2))) ∩
                            openCubeSet (originCube d m)) u.toFun g := by
  obtain ⟨C, Cout, hCpos, hCoutpos, hmain⟩ := ae_constantDatumEnergy_harmonicSlot_addThree d
  refine ⟨C, Cout * (besovGagliardoConstant d ^ (2 : ℕ) + 1), hCpos, ?_, ?_⟩
  · have hK : (0 : ℝ) ≤ besovGagliardoConstant d := besovGagliardoConstant_nonneg d
    positivity
  intro M s hsrange hregime hsmall hs L m n hmL hnm x z hz hsub hfr
  filter_upwards [hmain M s hsrange hregime hsmall hs n z] with omega hbound
  intro hmem u hdat g hsol hgL2 hgW
  have hs1 : s ≤ 1 := hsrange.2
  have hwin : (((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) ∩
      openCubeSet (originCube d m)) =
      (fun y' => z + y') '' openCubeSet (originCube d (n + 2)) :=
    inter_eq_of_frontier_inter_empty hz hfr
  rw [hwin] at hgL2 hgW
  rw [hwin]
  have heq := isForcedEquation_fluxCorrectedCoeffFamily_translated_addThree
    (n := n) M L z omega hz hfr hsol.2
  have hgreg : ForceBesovRegularity (originCube d (n + 2)) s (fun y => -g (y + z)) :=
    forceBesovRegularity_translated_neg (originCube d (n + 2)) hs hs1 hgL2 hgW
  have hpatch : openCubeAtScale (x - z) (n + 1) ⊆
      openCubeSet (originCube d (n + 2)) :=
    openCubeAtScale_patch_subset_of_anchorGeometry hsub
  have hstep := hbound hmem L (le_trans hnm hmL) (x - z) (fun y => -g (y + z)) _
    hpatch hgreg heq
  rw [← caccioppoliCoreSet_eq_image_add_of_anchorGeometry hsub]
  have hmemL2 : MemLp (fun y => u.toFun (y + z)) 2
      (normalizedCubeMeasure (originCube d (n + 2))) :=
    memLp_two_normalizedCubeMeasure_of_h1 (originCube d (n + 2))
      (H1Function.untranslate z
        (u.restrict (isOpen_translateSet_openCubeSet z (n + 2))
          (translateSet_openCubeSet_subset_of_frontier_inter_empty hz hfr)))
  have hRHS := constantDatumEnergyRHS_le_anchorRHS_addThree M n hs hs1 (f := u.toFun)
    (H1Function.untranslate z
      (u.restrict (isOpen_translateSet_openCubeSet z (n + 2))
        (translateSet_openCubeSet_subset_of_frontier_inter_empty hz hfr)))
    rfl hmemL2 g hgL2 hgW
  refine le_trans hstep ?_
  calc Cout * constantDatumEnergyRHSAddThree M n s
        (H1Function.untranslate z
          (u.restrict (isOpen_translateSet_openCubeSet z (n + 2))
            (translateSet_openCubeSet_subset_of_frontier_inter_empty hz hfr)))
        (fun y => -g (y + z))
      ≤ Cout * ((besovGagliardoConstant d ^ (2 : ℕ) + 1) *
          constantDatumAnchorEnergyRHSOnAddThree M n s
            ((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) u.toFun g) :=
        mul_le_mul_of_nonneg_left hRHS hCoutpos.le
    _ = Cout * (besovGagliardoConstant d ^ (2 : ℕ) + 1) *
          constantDatumAnchorEnergyRHSOnAddThree M n s
            ((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) u.toFun g := by
        ring

end

end Algsuperdiff.Section4.Provider.ExcessDecay
