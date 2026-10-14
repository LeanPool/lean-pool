/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BesovBridge
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.CaccioppoliInteriorEnergy
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.L2Bridge
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.TranslationTransportAssembly

/-!
# InteriorClause

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The interior clause's Caccioppoli input, in the frozen theorem's own carriers

This module closes the interior Caccioppoli seam of §4.3.

```text
  ⨍_{(x-z)+□_n} ∇u_tilde · ã_{L,n+2} ∇u_tilde
      ≤ C(d) ( σ_{n+2} 3^{-2(n+2)} ‖u - (u)_W‖²_{L²(W)}
               + s^{-11} σ_{n+2}^{-1} 3^{2s(n+2)} [g]²_{H^s(W)} ) ,
      W = ((z+□_{n+2}) ∩ □_m) ,
```

almost surely on the anchor's good event `𝒢(n+2, z; s/8, 1/2)`, for every
`H¹(□_m)` solution `u` of the anchor's own Dirichlet problem whose forcing `g`
lies in `H^s(W;ℝ^d)`, under the anchor's geometry binder and its **interior**
(frontier-empty) gate.

## What each unit contributes

* the force carrier: `ForceTransport.lean` (the real-translation covariance of
  the Gagliardo seminorm and of the force datum) and `BesovBridge.lean`
  (`Besov ≤ C(d)·3^{s(n+2)}·Gagliardo`, and the `ForceBesovRegularity`
  discharge);
* the `L²` carrier: `L2Bridge.lean` (an exact identity, no constant);

## Two disclosed frame facts (inputs to the consumer, not gaps in this estimate)

1. **The left-hand side is stated in the translated frame** — at the core
   `(x-z) + □_n`, for the transported solution `u(· + z)` and the
   flux-corrected family at `translateCutoffSample z ω`, which is where every
   proved §4.3 cap lives.  Reading the same quantity at the anchor's own core
   `x + □_n` is one application of `normalizedSetAverage_translateSet` away
   *once the flux-corrected family is rebuilt at the untranslated sample*; that
   construction is not performed here.

## The force binder, and where it differs from the frozen statement

The frozen statement carries the equation but *not* the `g`- and
`h`-regularity clauses: it quantifies over an arbitrary `g : Vec d → Vec d`.
The estimate below carries the paper's own clause for `g` — in the anchor's own
window carriers — because `l.coarse.grained.Caccioppoli` has it as a premise.
(When the Gagliardo seminorm is `⊤` the frozen statement's interior clause is
trivially true, so only the finite-seminorm-but-not-`H^s` case is at issue.)

## References

* ABK26, `l.harmonic.approximation.good.scales`; `e.energy.bound.interior`;
  `l.coarse.grained.Caccioppoli.RHS`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03 MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## 1. The scale weight of the parent cube -/

/-- The Besov scale weight of an origin cube, as an explicit `3`-power. -/
theorem cubeBesovScaleWeight_neg_originCube (k : ℤ) (s : ℝ) :
    cubeBesovScaleWeight (-s) (originCube d k) = Real.rpow (3 : ℝ) (s * (k : ℝ)) := by
  have h3 : (0 : ℝ) ≤ 3 := by norm_num
  rw [cubeBesovScaleWeight, cubeScaleFactor_originCube, neg_neg,
    ← Real.rpow_intCast (3 : ℝ) k, ← Real.rpow_mul h3]
  congr 1
  ring

/-- Its square, the weight the force leg carries. -/
theorem cubeBesovScaleWeight_neg_originCube_sq (k : ℤ) (s : ℝ) :
    cubeBesovScaleWeight (-s) (originCube d k) ^ (2 : ℕ) =
      Real.rpow (3 : ℝ) (2 * s * (k : ℝ)) := by
  have h3 : (0 : ℝ) ≤ 3 := by norm_num
  have hbase : cubeBesovScaleWeight (-s) (originCube d k) = (3 : ℝ) ^ (s * (k : ℝ)) :=
    cubeBesovScaleWeight_neg_originCube k s
  change cubeBesovScaleWeight (-s) (originCube d k) ^ (2 : ℕ) =
    (3 : ℝ) ^ (2 * s * (k : ℝ))
  rw [hbase, ← Real.rpow_natCast ((3 : ℝ) ^ (s * (k : ℝ))) 2, ← Real.rpow_mul h3]
  congr 1
  push_cast
  ring

/-! ## 2. The right-hand side in the anchor's carriers -/

/-- **The interior Caccioppoli right-hand side, in the frozen theorem's own
carriers, on an arbitrary window `W`.**

The mean-subtracted `L²` norm and the fractional force seminorm are the frozen
statement's own objects (`eLpNorm … (normalizedVolumeMeasureOn W)` and
`normalizedGagliardo W s g`); the `3`- and `s`-powers are explicit.  The
composed estimate below instantiates `W` at the anchor's own window
`((z+□_{n+2}) ∩ □_m)`. -/
def interiorAnchorEnergyRHSOn (M : ABKModel d) (n : ℤ) (s : ℝ) (W : Set (Vec d))
    (f : Vec d → ℝ) (g : Vec d → Vec d) : ℝ :=
  (Annealed.sigmaBar M (n + 2) : ℝ) *
      Real.rpow (3 : ℝ) (-2 * (((n + 2 : ℤ)) : ℝ)) *
      (eLpNorm (fun y => f y - volumeAverage W f) 2
        (Support.normalizedVolumeMeasureOn W)).toReal ^ (2 : ℕ) +
    Real.rpow s (-11 : ℝ) * (Annealed.sigmaBar M (n + 2) : ℝ)⁻¹ *
      Real.rpow (3 : ℝ) (2 * s * (((n + 2 : ℤ)) : ℝ)) *
      (Support.normalizedGagliardoESeminormOn W s g).toReal ^ (2 : ℕ)

theorem interiorAnchorEnergyRHSOn_def (M : ABKModel d) (n : ℤ) (s : ℝ)
    (W : Set (Vec d)) (f : Vec d → ℝ) (g : Vec d → Vec d) :
    interiorAnchorEnergyRHSOn M n s W f g =
      (Annealed.sigmaBar M (n + 2) : ℝ) *
          Real.rpow (3 : ℝ) (-2 * (((n + 2 : ℤ)) : ℝ)) *
          (eLpNorm (fun y => f y - volumeAverage W f) 2
            (Support.normalizedVolumeMeasureOn W)).toReal ^ (2 : ℕ) +
        Real.rpow s (-11 : ℝ) * (Annealed.sigmaBar M (n + 2) : ℝ)⁻¹ *
          Real.rpow (3 : ℝ) (2 * s * (((n + 2 : ℤ)) : ℝ)) *
          (Support.normalizedGagliardoESeminormOn W s g).toReal ^ (2 : ℕ) :=
  rfl

/-! ## 3. The arithmetic stitch -/

/-- Abstract in every quantity, so no analytic content hides here. -/
theorem anchor_stitch {A L2 B Bes K W G : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hL2 : 0 ≤ L2) (hBes : 0 ≤ Bes) (hK : 0 ≤ K) (hW : 0 ≤ W) (hG : 0 ≤ G)
    (hbes : Bes ≤ K * W * G) :
    A * L2 + B * Bes ^ (2 : ℕ) ≤
      (K ^ (2 : ℕ) + 1) * (A * L2 + B * W ^ (2 : ℕ) * G ^ (2 : ℕ)) := by
  have hsq : Bes ^ (2 : ℕ) ≤ K ^ (2 : ℕ) * (W ^ (2 : ℕ) * G ^ (2 : ℕ)) := by
    calc Bes ^ (2 : ℕ) ≤ (K * W * G) ^ (2 : ℕ) := pow_le_pow_left₀ hBes hbes 2
      _ = K ^ (2 : ℕ) * (W ^ (2 : ℕ) * G ^ (2 : ℕ)) := by ring
  have hAL2 : 0 ≤ A * L2 := mul_nonneg hA hL2
  have hWG : (0 : ℝ) ≤ W ^ (2 : ℕ) * G ^ (2 : ℕ) :=
    mul_nonneg (pow_nonneg hW 2) (pow_nonneg hG 2)
  have hK2 : (0 : ℝ) ≤ K ^ (2 : ℕ) := pow_nonneg hK 2
  have hBWG : 0 ≤ B * (W ^ (2 : ℕ) * G ^ (2 : ℕ)) := mul_nonneg hB hWG
  have hterm : B * Bes ^ (2 : ℕ) ≤ K ^ (2 : ℕ) * (B * (W ^ (2 : ℕ) * G ^ (2 : ℕ))) := by
    calc B * Bes ^ (2 : ℕ) ≤ B * (K ^ (2 : ℕ) * (W ^ (2 : ℕ) * G ^ (2 : ℕ))) :=
          mul_le_mul_of_nonneg_left hsq hB
      _ = K ^ (2 : ℕ) * (B * (W ^ (2 : ℕ) * G ^ (2 : ℕ))) := by ring
  have hexp : (K ^ (2 : ℕ) + 1) * (A * L2 + B * W ^ (2 : ℕ) * G ^ (2 : ℕ)) =
      K ^ (2 : ℕ) * (A * L2) + K ^ (2 : ℕ) * (B * (W ^ (2 : ℕ) * G ^ (2 : ℕ))) +
        (A * L2 + B * (W ^ (2 : ℕ) * G ^ (2 : ℕ))) := by ring
  have hpos1 : 0 ≤ K ^ (2 : ℕ) * (A * L2) := mul_nonneg hK2 hAL2
  rw [hexp]
  linarith only [hterm, hpos1, hBWG]

/-- **The right-hand-side conversion.**

The `L²` leg is an identity; the force leg costs the Besov-versus-Gagliardo
constant. -/
theorem interiorEnergyRHSPrinted_le_anchorRHS [NeZero d] (M : ABKModel d) (n : ℤ)
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
    interiorEnergyRHSPrinted M n s v (fun y => -g (y + z)) ≤
      (besovGagliardoConstant d ^ (2 : ℕ) + 1) *
        interiorAnchorEnergyRHSOn M n s
          ((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) f g := by
  have hsig : (0 : ℝ) < (Annealed.sigmaBar M (n + 2) : ℝ) :=
    (Annealed.sigmaBar M (n + 2)).2
  have hgreg : ForceBesovRegularity (originCube d (n + 2)) s (fun y => -g (y + z)) :=
    forceBesovRegularity_translated_neg (originCube d (n + 2)) hs hs1 hgL2 hgW
  have hbes := besovVectorSeminormTwo_translated_neg_le_gagliardo_window
    (originCube d (n + 2)) hs hs1 hgL2 hgW
  have hBesnn : 0 ≤ scaleNormalizedPositiveBesovVectorSeminormTwo
      (originCube d (n + 2)) s (fun y => -g (y + z)) :=
    cubeBesovPositiveVectorSeminormTwo_nonneg_of_bddAbove _ s _
      hgreg.partialSeminorms_bddAbove
  rw [interiorEnergyRHSPrinted, interiorAnchorEnergyRHSOn_def]
  simp only [hv]
  rw [normalizedL2SqOnSet_translate_sub_average_eq_eLpNorm_sq_image_add
      (originCube d (n + 2)) f hmem,
    ← cubeBesovScaleWeight_neg_originCube_sq (d := d) (n + 2) s]
  exact anchor_stitch
    (mul_nonneg hsig.le (Real.rpow_nonneg (by norm_num) _))
    (mul_nonneg (Real.rpow_nonneg hs.le _) (inv_nonneg.mpr hsig.le))
    (pow_nonneg ENNReal.toReal_nonneg 2) hBesnn (besovGagliardoConstant_nonneg d)
    (cubeBesovScaleWeight_nonneg (-s) _) ENNReal.toReal_nonneg hbes

/-! ## 5. The composed interior estimate -/

/-- **The interior clause's Caccioppoli input.**

Entered at the frozen theorem's own binders — its Dirichlet datum on `□_m`, its
geometry binder, its interior (frontier-empty) gate, its good event, its
hoisted smallness clauses and its `s`-range — and concluded in the anchor's own
right-hand-side carriers on the anchor's own window `W = ((z+□_{n+2}) ∩ □_m)`:

```text
  ⨍_{(x-z)+□_n} ∇u_tilde · ã_{L,n+2} ∇u_tilde  ·  1_𝒢
      ≤ Cout ( σ_{n+2} 3^{-2(n+2)} ‖u - (u)_W‖²_{L²(W)}
               + s^{-11} σ_{n+2}^{-1} 3^{2s(n+2)} [g]²_{H^s(W)} ) ,
```

where `u_tilde = u(· + z)` is the transported solution and `ã_{L,n+2}` the
flux-corrected field at the translated sample.  The force hypothesis is the
manuscript's `g ∈ H^s(W;ℝ^d)` in the anchor's own carriers. -/
theorem ae_interiorCaccioppoliEnergy_anchorWindow (d : ℕ) [NeZero d] :
    ∃ C Cout : ℝ, 0 < C ∧ 0 < Cout ∧
      ∀ (M : ABKModel d) (s : ℝ), s ∈ Set.Icc (64 * M.gamma) 1 →
        M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
            Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * (1 / 2) →
        ∀ hs : 0 < s, ∀ L m n : ℤ, m ≤ L → n + 2 ≤ m → ∀ x z : Vec d,
          ∀ hz : z ∈ openCubeSet (originCube d m),
            (fun y => x + y) '' openCubeSet (originCube d n) ⊆
              ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
                openCubeSet (originCube d m) →
            ∀ hfr : ((fun y => z + y) '' openCubeSet (originCube d (n + 2))) ∩
                frontier (openCubeSet (originCube d m)) = ∅,
              ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
                omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
                    (Support.cgEllipLowerConstant d) (n + 2) z
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
                          ((Support.fluxCorrectedCoeffFamily M L (n + 2)
                            (originCube d (n + 2))
                            (Cutoff.translateCutoffSample z omega)).coeffOn
                            (originCube d (n + 2)))
                          (H1Function.untranslate z
                            (u.restrict (isOpen_translateSet_openCubeSet z (n + 2))
                              (translateSet_openCubeSet_subset_of_frontier_inter_empty
                                hz hfr))) ≤
                        Cout * interiorAnchorEnergyRHSOn M n s
                          (((fun y' => z + y') ''
                              openCubeSet (originCube d (n + 2))) ∩
                            openCubeSet (originCube d m)) u.toFun g := by
  obtain ⟨C, Cout, hCpos, hCoutpos, hmain⟩ := ae_interiorCaccioppoliEnergy_originCube d
  refine ⟨C, Cout * (besovGagliardoConstant d ^ (2 : ℕ) + 1), hCpos, ?_, ?_⟩
  · have hK : (0 : ℝ) ≤ besovGagliardoConstant d := besovGagliardoConstant_nonneg d
    positivity
  intro M s hsrange hregime hsmall hs L m n hmL hnm x z hz hsub hfr
  filter_upwards [hmain M s hsrange hregime hsmall hs m n x z hsub] with omega hbound
  intro hmem u hdat g hsol hgL2 hgW
  have hs1 : s ≤ 1 := hsrange.2
  have hwin : (((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) ∩
      openCubeSet (originCube d m)) =
      (fun y' => z + y') '' openCubeSet (originCube d (n + 2)) :=
    inter_eq_of_frontier_inter_empty hz hfr
  rw [hwin] at hgL2 hgW
  rw [hwin]
  have heq := isForcedEquation_fluxCorrectedCoeffFamily_of_isDirichletSolutionOn
    (n := n) M L z omega hz hfr hsol
  have hgreg : ForceBesovRegularity (originCube d (n + 2)) s (fun y => -g (y + z)) :=
    forceBesovRegularity_translated_neg (originCube d (n + 2)) hs hs1 hgL2 hgW
  have hstep := hbound hmem L (le_trans hnm hmL) (fun y => -g (y + z)) _ hgreg heq
  have hmemL2 : MemLp (fun y => u.toFun (y + z)) 2
      (normalizedCubeMeasure (originCube d (n + 2))) :=
    memLp_two_normalizedCubeMeasure_of_h1 (originCube d (n + 2))
      (H1Function.untranslate z
        (u.restrict (isOpen_translateSet_openCubeSet z (n + 2))
          (translateSet_openCubeSet_subset_of_frontier_inter_empty hz hfr)))
  have hRHS := interiorEnergyRHSPrinted_le_anchorRHS M n hs hs1 (f := u.toFun)
    (H1Function.untranslate z
      (u.restrict (isOpen_translateSet_openCubeSet z (n + 2))
        (translateSet_openCubeSet_subset_of_frontier_inter_empty hz hfr)))
    rfl hmemL2 g hgL2 hgW
  refine le_trans hstep ?_
  calc Cout * interiorEnergyRHSPrinted M n s
        (H1Function.untranslate z
          (u.restrict (isOpen_translateSet_openCubeSet z (n + 2))
            (translateSet_openCubeSet_subset_of_frontier_inter_empty hz hfr)))
        (fun y => -g (y + z))
      ≤ Cout * ((besovGagliardoConstant d ^ (2 : ℕ) + 1) *
          interiorAnchorEnergyRHSOn M n s
            ((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) u.toFun g) :=
        mul_le_mul_of_nonneg_left hRHS hCoutpos.le
    _ = Cout * (besovGagliardoConstant d ^ (2 : ℕ) + 1) *
          interiorAnchorEnergyRHSOn M n s
            ((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) u.toFun g := by
        ring

end

end Algsuperdiff.Section4.Provider.ExcessDecay
