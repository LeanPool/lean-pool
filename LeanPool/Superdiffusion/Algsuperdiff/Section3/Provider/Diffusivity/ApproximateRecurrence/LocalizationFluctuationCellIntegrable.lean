/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationEnvelopeWire
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationOscillationDisplay

/-!
# LocalizationFluctuationCellIntegrable

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Sample integrability of the per-cell coarse energies of `e.def.w`

`LocalizationOscillationDisplay` and `LocalizationOscillationEndpoint` carry one
surviving hypothesis about the sample space, `hcellInt`:

```
  forall R in the interior meso grid,
    Integrable (fun omega => meshEnergyCell (m - h) (grad w_omega) R ^ 4) P .
```

This module discharges it.  Nothing here is a step of the manuscript's
argument; it is the measure-theoretic bookkeeping the manuscript leaves
implicit.

## The obstruction and the route

`CorrectorMeasurableQuartic` proves that the *quartic* window observable
`omega |-> fint_W |grad w_omega|^4` is Borel, by a countable supremum of
truncations, because `F |-> int_S ‖F‖^4` is not continuous on `L^2`.  The
observable `meshEnergyCell` needs instead the *quadratic* window observable
`omega |-> fint_W |grad w_omega|^2`, and for that no truncation is needed: the
functional

```
  F |-> ( eLpNorm F 2 ((volumeMeasureOn U).restrict S) ).toReal
```

is **`1`-Lipschitz** on `L^2(U)`, because restriction only decreases the
seminorm and the seminorm obeys the triangle inequality.  Its square is the
window integral of `‖F‖^2`, so the quadratic window observable is continuous --
not merely Borel -- in the `L^2` class, and composing with
`CorrectorMeasurableGradient`'s measurable gradient map gives measurability in
the sample.

Integrability then follows by domination:

```
  meshEnergyCell^4 <= mesoWindowFourthEnergy            (per-window Jensen)
                   <= |cu_K| |W|^{-1} originCubeFourthEnergy
                   <= |cu_K| |W|^{-1} (2 Chead^2 + 2 T'^2) ,
```

with `T' = max(sqrt(originCubeFourthEnergy) - Chead, 0)` the measurable
dominating fluctuation of `LocalizationEnvelopeWire` -- rebuilt here because it
is `private` there -- whose square is integrable from the `Gamma_1` tail of
`e.nablaw.in.L.eight`.

## Main results

* `measurable_volumeAverage_vecNormSq_freshShellDirichletGrad` and its Neumann
  mirror -- the quadratic window observable is measurable in the sample.
* `exists_gamma0_integrable_freshShellDirichlet_meshEnergyCell_rpow_four` and
  its Neumann mirror -- the binder `hcellInt` of the oscillation endpoint, as a
  theorem.

## Scope

There is no `sorry`.

## References

* ABK26, `e.def.w`, `e.nablaw.oscillations`, `e.nablaw.in.L.eight`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open MeasureTheory
open HCPolySupport HCPolySupport.Book.Ch03
open Algsuperdiff.Section3
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The Lipschitz window functional on `L^2` -/

section LpWindow

variable {alpha E : Type*} [MeasurableSpace alpha] [NormedAddCommGroup E]

/-- The `L^2` size of an `L^2` class over a window, read through the seminorm
of the restricted measure. -/
def lpWindowNorm (mu : Measure alpha) (S : Set alpha) (F : Lp E 2 mu) : ℝ :=
  (eLpNorm (F : alpha → E) 2 (mu.restrict S)).toReal

private theorem lpWindowNorm_ne_top (mu : Measure alpha) (S : Set alpha) (F : Lp E 2 mu) :
    eLpNorm (F : alpha → E) 2 (mu.restrict S) ≠ ⊤ :=
  ne_top_of_le_ne_top (Lp.memLp F).eLpNorm_ne_top
    (eLpNorm_mono_measure _ Measure.restrict_le_self)

private theorem eLpNorm_restrict_sub_le (mu : Measure alpha) (S : Set alpha)
    (F G : Lp E 2 mu) :
    eLpNorm (F : alpha → E) 2 (mu.restrict S) ≤
      eLpNorm (G : alpha → E) 2 (mu.restrict S) +
        eLpNorm ((F : alpha → E) - (G : alpha → E)) 2 (mu.restrict S) := by
  have hsplit : (F : alpha → E) =
      (G : alpha → E) + ((F : alpha → E) - (G : alpha → E)) := by
    funext x; simp
  calc eLpNorm (F : alpha → E) 2 (mu.restrict S)
      = eLpNorm ((G : alpha → E) + ((F : alpha → E) - (G : alpha → E))) 2
          (mu.restrict S) := by rw [← hsplit]
    _ ≤ eLpNorm (G : alpha → E) 2 (mu.restrict S) +
          eLpNorm ((F : alpha → E) - (G : alpha → E)) 2 (mu.restrict S) :=
        eLpNorm_add_le (by norm_num)

/-- **The window `L^2` functional is `1`-Lipschitz on `L^2`.**  Restriction only
decreases the seminorm, so the ambient `L^2` distance controls the window one. -/
private theorem lipschitzWith_lpWindowNorm (mu : Measure alpha) (S : Set alpha) :
    LipschitzWith 1 (lpWindowNorm (E := E) mu S) := by
  refine LipschitzWith.of_dist_le_mul fun F G => ?_
  have hdiff : eLpNorm ((F : alpha → E) - (G : alpha → E)) 2 mu =
      eLpNorm ((F - G : Lp E 2 mu) : alpha → E) 2 mu :=
    eLpNorm_congr_ae (Lp.coeFn_sub F G).symm
  have hdifftop : eLpNorm ((F : alpha → E) - (G : alpha → E)) 2 mu ≠ ⊤ := by
    rw [hdiff]; exact (Lp.memLp (F - G)).eLpNorm_ne_top
  have hrestr : eLpNorm ((F : alpha → E) - (G : alpha → E)) 2 (mu.restrict S) ≤
      eLpNorm ((F : alpha → E) - (G : alpha → E)) 2 mu :=
    eLpNorm_mono_measure _ Measure.restrict_le_self
  have hrestrtop : eLpNorm ((F : alpha → E) - (G : alpha → E)) 2 (mu.restrict S) ≠ ⊤ :=
    ne_top_of_le_ne_top hdifftop hrestr
  have hdist : dist F G =
      (eLpNorm ((F : alpha → E) - (G : alpha → E)) 2 mu).toReal := by
    rw [hdiff, dist_eq_norm, Lp.norm_def]
  have hsym : eLpNorm ((G : alpha → E) - (F : alpha → E)) 2 (mu.restrict S) =
      eLpNorm ((F : alpha → E) - (G : alpha → E)) 2 (mu.restrict S) :=
    eLpNorm_sub_comm _ _ _ _
  have h1 : lpWindowNorm mu S F - lpWindowNorm mu S G ≤
      (eLpNorm ((F : alpha → E) - (G : alpha → E)) 2 (mu.restrict S)).toReal := by
    have hmono := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨lpWindowNorm_ne_top mu S G, hrestrtop⟩)
      (eLpNorm_restrict_sub_le mu S F G)
    rw [ENNReal.toReal_add (lpWindowNorm_ne_top mu S G) hrestrtop] at hmono
    change (eLpNorm (F : alpha → E) 2 (mu.restrict S)).toReal -
      (eLpNorm (G : alpha → E) 2 (mu.restrict S)).toReal ≤ _
    linarith
  have h2 : lpWindowNorm mu S G - lpWindowNorm mu S F ≤
      (eLpNorm ((F : alpha → E) - (G : alpha → E)) 2 (mu.restrict S)).toReal := by
    have hbase := eLpNorm_restrict_sub_le mu S G F
    rw [hsym] at hbase
    have hmono := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨lpWindowNorm_ne_top mu S F, hrestrtop⟩) hbase
    rw [ENNReal.toReal_add (lpWindowNorm_ne_top mu S F) hrestrtop] at hmono
    change (eLpNorm (G : alpha → E) 2 (mu.restrict S)).toReal -
      (eLpNorm (F : alpha → E) 2 (mu.restrict S)).toReal ≤ _
    linarith
  have hfin : (eLpNorm ((F : alpha → E) - (G : alpha → E)) 2 (mu.restrict S)).toReal ≤
      (eLpNorm ((F : alpha → E) - (G : alpha → E)) 2 mu).toReal :=
    ENNReal.toReal_mono hdifftop hrestr
  rw [Real.dist_eq, abs_le]
  refine ⟨?_, ?_⟩ <;> simp only [NNReal.coe_one, one_mul] <;> rw [hdist] <;> linarith

/-- The square of the window functional is the window integral of `‖F‖^2`. -/
private theorem lpWindowNorm_sq (mu : Measure alpha) (S : Set alpha) (F : Lp E 2 mu) :
    lpWindowNorm mu S F ^ 2 = ∫ x in S, ‖(F : alpha → E) x‖ ^ 2 ∂mu := by
  have hmem : MemLp (F : alpha → E) 2 (mu.restrict S) := (Lp.memLp F).restrict S
  have hnn : (0 : ℝ) ≤ ∫ x in S, ‖(F : alpha → E) x‖ ^ (2 : ℝ) ∂mu :=
    integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  have hrw : ∫ x in S, ‖(F : alpha → E) x‖ ^ (2 : ℝ) ∂mu =
      ∫ x in S, ‖(F : alpha → E) x‖ ^ (2 : ℕ) ∂mu := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp
  rw [lpWindowNorm, hmem.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  have hto : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [hto, ENNReal.toReal_ofReal (Real.rpow_nonneg hnn _),
    ← Real.rpow_natCast ((∫ x in S, ‖(F : alpha → E) x‖ ^ (2 : ℝ) ∂mu) ^ (2 : ℝ)⁻¹) 2,
    ← Real.rpow_mul hnn,
    show ((2 : ℝ)⁻¹ * ((2 : ℕ) : ℝ)) = 1 by norm_num, Real.rpow_one, hrw]

end LpWindow

/-! ## The quadratic window observable at a gradient class -/

variable {U : Set (Vec d)}

/-- The window `L^2` functional at the gradient class of an `H^1` function is
the ordinary Lebesgue integral of `|grad w|^2` over the window. -/
private theorem setIntegral_vecNormSq_eq (w : H1Function U) {S : Set (Vec d)}
    (hS : MeasurableSet S) (hSU : S ⊆ U) :
    ∫ x in S, ‖(w.gradToHilbertVectorL2 : Vec d → HilbertVec d) x‖ ^ 2
        ∂(volumeMeasureOn U) =
      ∫ x in S, vecNormSq (w.grad x) ∂volume := by
  have hrestrict : (volumeMeasureOn U).restrict S = volume.restrict S := by
    rw [volumeMeasureOn, Measure.restrict_restrict hS,
      Set.inter_eq_self_of_subset_left hSU]
  have hae : ∀ᵐ x ∂((volumeMeasureOn U).restrict S),
      ‖(w.gradToHilbertVectorL2 : Vec d → HilbertVec d) x‖ ^ 2 =
        vecNormSq (w.grad x) := by
    refine (w.coeFn_gradToHilbertVectorL2.filter_mono
      (ae_mono Measure.restrict_le_self)).mono fun x hx => ?_
    rw [hx, hilbertifyVecField]
    exact HilbertVec.norm_sq_ofVec (w.grad x)
  rw [integral_congr_ae hae, hrestrict]

/-- Unconditional: for a measurable family of `L^2` classes, the normalized
*second* energy over a window of `U` is a measurable function of the sample. -/
private theorem measurable_volumeAverage_vecNormSq_aux {Omega : Type*}
    [MeasurableSpace Omega] {S : Set (Vec d)} (hS : MeasurableSet S) (hSU : S ⊆ U)
    {F : Omega → HilbertVectorL2 U} (hF : Measurable F)
    {w : Omega → H1Function U}
    (hw : ∀ omega, F omega = (w omega).gradToHilbertVectorL2) :
    Measurable fun omega => volumeAverage S (fun x => vecNormSq ((w omega).grad x)) := by
  have hEq : (fun omega => volumeAverage S (fun x => vecNormSq ((w omega).grad x))) =
      fun omega => (volume S).toReal⁻¹ *
        lpWindowNorm (volumeMeasureOn U) S (F omega) ^ 2 := by
    funext omega
    rw [lpWindowNorm_sq, hw omega, setIntegral_vecNormSq_eq (w omega) hS hSU,
      volumeAverage]
  rw [hEq]
  exact measurable_const.mul
    (((lipschitzWith_lpWindowNorm (volumeMeasureOn U) S).continuous.measurable.comp
      hF).pow_const 2)

/-- Unconditional: **the normalized second energy of the Dirichlet corrector
gradient over any measurable window of the cube is a measurable function of the
sample.**

`wD` is an arbitrary family of zero-trace weak solutions of the fresh-shell
Dirichlet problem `e.def.w`; no measurability, continuity or selection property
of the family is assumed. -/
theorem measurable_volumeAverage_vecNormSq_freshShellDirichletGrad [NeZero d]
    (Q : TriadicCube d) (sigmaInv : ℝ) (n m : ℤ) (e : Vec d)
    {S : Set (Vec d)} (hS : MeasurableSet S) (hSU : S ⊆ openCubeSet Q)
    (wD : Cutoff.ShellSeq d → H10Function (openCubeSet Q))
    (hwD : ∀ omega : Cutoff.ShellSeq d,
      IsZeroTraceDirichletRhsWeakSolution
        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
        (openCubeSet Q) (wD omega)
        (fun x => -Corrector.streamForcing sigmaInv omega n m e x)) :
    Measurable fun omega =>
      volumeAverage S (fun x => vecNormSq ((wD omega).toH1Function.grad x)) :=
  measurable_volumeAverage_vecNormSq_aux hS hSU
    (Corrector.measurable_freshShellDirichletGradL2 Q sigmaInv n m e wD hwD)
    (w := fun omega => (wD omega).toH1Function) fun _ => rfl

/-- Unconditional: the Neumann mirror of the previous statement. -/
theorem measurable_volumeAverage_vecNormSq_freshShellNeumannGrad
    (Q : TriadicCube d) (sigmaInv : ℝ) (n m : ℤ) (e : Vec d)
    {S : Set (Vec d)} (hS : MeasurableSet S) (hSU : S ⊆ openCubeSet Q)
    (wN : Cutoff.ShellSeq d → H1MeanZeroFunction (openCubeSet Q))
    (hwN : ∀ omega : Cutoff.ShellSeq d,
      IsMeanZeroNeumannRhsWeakSolution
        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
        (openCubeSet Q) (wN omega)
        (fun x => -Corrector.streamForcing sigmaInv omega n m e x)) :
    Measurable fun omega =>
      volumeAverage S (fun x => vecNormSq ((wN omega).toH1Function.grad x)) :=
  measurable_volumeAverage_vecNormSq_aux hS hSU
    (Corrector.measurable_freshShellNeumannGradL2 Q sigmaInv n m e wN hwN)
    (w := fun omega => (wN omega).toH1Function) fun _ => rfl

/-! ## The per-cell coarse energy as a square -/

/-- The fourth power of the per-cell coarse energy is the square of the window
average of `|u|^2`.

: the caller supplies integrability on the window of the coordinate squares of
`u`. -/
theorem meshEnergyCell_rpow_four_eq_sq_volumeAverage (ell : ℤ) (u : Vec d → Vec d)
    (R : TriadicCube d)
    (hcoord : ∀ k : Fin d, IntegrableOn (fun x => (u x k) ^ 2)
      (openCubeAtScale (triadicCubeShift R) ell) volume) :
    meshEnergyCell ell u R ^ (4 : ℝ) =
      (volumeAverage (openCubeAtScale (triadicCubeShift R) ell)
        (fun x => vecNormSq (u x))) ^ 2 := by
  have hint : ∀ k : Fin d,
      IntegrableOn (fun x => (u x k - (0 : Vec d) k) ^ 2)
        (openCubeAtScale (triadicCubeShift R) ell) volume := by
    intro k
    simpa using hcoord k
  have hmsd : Book.Ch01.meanSquareDeviationVecOn
      (openCubeAtScale (triadicCubeShift R) ell) u 0 =
      volumeAverage (openCubeAtScale (triadicCubeShift R) ell)
        fun x => vecNormSq (u x) := by
    rw [Book.Ch01.meanSquareDeviationVecOn_eq_volumeAverage_vecNormSq_sub hint]
    simp
  have hnn : 0 ≤ Book.Ch01.meanSquareDeviationVecOn
      (openCubeAtScale (triadicCubeShift R) ell) u 0 := by
    rw [hmsd]
    exact volumeAverage_nonneg_of_nonneg_on (measurableSet_openCubeAtScale _ _)
      fun x _ => vecNormSq_nonneg _
  rw [meshEnergyCell, rpow_four_eq_pow_four,
    show Real.sqrt (Book.Ch01.meanSquareDeviationVecOn
        (openCubeAtScale (triadicCubeShift R) ell) u 0) ^ (4 : ℕ) =
      (Real.sqrt (Book.Ch01.meanSquareDeviationVecOn
        (openCubeAtScale (triadicCubeShift R) ell) u 0) ^ 2) ^ 2 by ring,
    Real.sq_sqrt hnn, hmsd]

/-! ## The window is dominated by the cube -/

/-- The window fourth energy is at most the volume ratio times the global
fourth energy, for any window contained in `cu_K`.

: the caller supplies `hsub` (the containment) and `hfour` (integrability of
`|u|^4` on `cu_K`). -/
theorem mesoWindowFourthEnergy_le_ratio_mul_originCubeFourthEnergy'
    {K ell : ℤ} {R : TriadicCube d} (u : Vec d → Vec d)
    (hsub : openCubeAtScale (triadicCubeShift R) ell ⊆ openCubeSet (originCube d K))
    (hfour : IntegrableOn (fun x => vecNormSq (u x) ^ 2)
      (openCubeSet (originCube d K)) volume) :
    mesoWindowFourthEnergy ell u R ≤
      (volume (openCubeAtScale (triadicCubeShift R) ell)).toReal⁻¹ *
          (volume (openCubeSet (originCube d K))).toReal *
        originCubeFourthEnergy K u := by
  exact mesoWindowFourthEnergy_le_ratio_mul_originCubeFourthEnergy u hsub hfour

/-! ## The integrability core -/

/-- **The generic integrability step.**  Given the pathwise `L^8` bound with a
`Gamma_1` fluctuation, the measurability of the two window observables, and the
three spatial integrability families on `cu_K`, the fourth power of the per-cell
coarse energy is integrable in the sample.

: complete binder census beyond the typing binders `d, Omega, its
MeasurableSpace instance, mu, K, ell, R, u, Chead, A, T`:
`[IsProbabilityMeasure mu]`; `hChead : 0 <= Chead`; `hA : 0 < A`; `hT0`, `hT`
(the `Gamma_1` tail); `hmem`, `hpath` (the spatial `L^8` membership and the
pathwise `L^8` bound); `hcoord`, `hsq`, `hfour` on `cu_K`; `hsub` (the window
containment); and `hglobMeas`, `hcellMeas` (measurability in the sample of the
global fourth energy and of the window second energy).  No integrability in the
sample is assumed. -/
theorem integrable_meshEnergyCell_rpow_four_of_measurable
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsProbabilityMeasure mu] {K ell : ℤ} {R : TriadicCube d}
    (u : Omega → Vec d → Vec d) {Chead A : ℝ} (hChead : 0 ≤ Chead) (hA : 0 < A)
    {T : Omega → ℝ} (hT0 : ∀ omega, 0 ≤ T omega)
    (hT : IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma 1) T A)
    (hmem : ∀ omega, MemLp (fun x => Book.Ch02.vecNorm (u omega x)) 8
      (normalizedCubeMeasure (originCube d K)))
    (hpath : ∀ omega,
      Corrector.cubeEuclideanLpNorm (originCube d K) 8 (u omega) ^ (2 : ℕ) ≤
        Chead + T omega)
    (hcoord : ∀ (omega : Omega) (k : Fin d), IntegrableOn (fun x => (u omega x k) ^ 2)
      (openCubeSet (originCube d K)) volume)
    (hsq : ∀ omega, IntegrableOn (fun x => vecNormSq (u omega x))
      (openCubeSet (originCube d K)) volume)
    (hfour : ∀ omega, IntegrableOn (fun x => vecNormSq (u omega x) ^ 2)
      (openCubeSet (originCube d K)) volume)
    (hsub : openCubeAtScale (triadicCubeShift R) ell ⊆ openCubeSet (originCube d K))
    (hglobMeas : Measurable fun omega => originCubeFourthEnergy K (u omega))
    (hcellMeas : Measurable fun omega =>
      volumeAverage (openCubeAtScale (triadicCubeShift R) ell)
        (fun x => vecNormSq (u omega x))) :
    Integrable (fun omega => meshEnergyCell ell (u omega) R ^ (4 : ℝ)) mu := by
  classical
  set G : Omega → ℝ := fun omega => originCubeFourthEnergy K (u omega) with hGdef
  have hG0 : ∀ omega, 0 ≤ G omega := fun omega => originCubeFourthEnergy_nonneg K (u omega)
  set T' : Omega → ℝ := fun omega => max (Real.sqrt (G omega) - Chead) 0 with hT'def
  have hT'0 : ∀ omega, 0 ≤ T' omega := fun _ => le_max_right _ _
  have hT'meas : Measurable T' :=
    ((hglobMeas.sqrt).sub measurable_const).max measurable_const
  have hGT : ∀ omega, G omega ≤ (Chead + T omega) ^ (2 : ℕ) := fun omega =>
    originCubeFourthEnergy_le_sq_of_cubeEuclideanLpNorm_sq_le K (u omega)
      (hmem omega) (hpath omega)
  have hT'le : ∀ omega, T' omega ≤ T omega := by
    intro omega
    have hnn : (0 : ℝ) ≤ Chead + T omega := by linarith [hT0 omega]
    have hsqrt : Real.sqrt (G omega) ≤ Chead + T omega := by
      have h := Real.sqrt_le_sqrt (hGT omega)
      rwa [Real.sqrt_sq hnn] at h
    exact max_le (by linarith) (hT0 omega)
  have hT'tail : IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma 1) T' A :=
    hT.of_le hT'le
  have hGT' : ∀ omega, G omega ≤ (Chead + T' omega) ^ (2 : ℕ) := by
    intro omega
    have hle : Real.sqrt (G omega) ≤ Chead + T' omega := by
      have := le_max_left (Real.sqrt (G omega) - Chead) 0
      linarith
    have hsq2 : Real.sqrt (G omega) ^ (2 : ℕ) = G omega := Real.sq_sqrt (hG0 omega)
    calc G omega = Real.sqrt (G omega) ^ (2 : ℕ) := hsq2.symm
      _ ≤ (Chead + T' omega) ^ (2 : ℕ) := pow_le_pow_left₀ (Real.sqrt_nonneg _) hle 2
  have hmaj : ∀ omega, G omega ≤ 2 * Chead ^ (2 : ℕ) + 2 * T' omega ^ (2 : ℕ) := by
    intro omega
    have h := hGT' omega
    nlinarith [sq_nonneg (Chead - T' omega)]
  have hT'sqInt : Integrable (fun omega => T' omega ^ (2 : ℕ)) mu :=
    integrable_sq_of_isBigOWith_gammaSigma_one hA hT'0 hT'meas.aemeasurable hT'tail
  -- the dominating variable
  set ratio : ℝ :=
    (volume (openCubeAtScale (triadicCubeShift R) ell)).toReal⁻¹ *
      (volume (openCubeSet (originCube d K))).toReal with hratio
  have hratio0 : 0 ≤ ratio := by positivity
  have hdomInt : Integrable
      (fun omega => ratio * (2 * Chead ^ (2 : ℕ) + 2 * T' omega ^ (2 : ℕ))) mu :=
    (((integrable_const _).add (hT'sqInt.const_mul 2)).const_mul ratio)
  -- the per-window restrictions of the three spatial families
  have hcoordW : ∀ (omega : Omega) (k : Fin d),
      IntegrableOn (fun x => (u omega x k) ^ 2)
        (openCubeAtScale (triadicCubeShift R) ell) volume :=
    fun omega k => (hcoord omega k).mono_set hsub
  have hsqW : ∀ omega, IntegrableOn (fun x => vecNormSq (u omega x))
      (openCubeAtScale (triadicCubeShift R) ell) volume :=
    fun omega => (hsq omega).mono_set hsub
  have hfourW : ∀ omega, IntegrableOn (fun x => vecNormSq (u omega x) ^ 2)
      (openCubeAtScale (triadicCubeShift R) ell) volume :=
    fun omega => (hfour omega).mono_set hsub
  -- the observable, as a square of the measurable window average
  have hobs : (fun omega => meshEnergyCell ell (u omega) R ^ (4 : ℝ)) =
      fun omega => (volumeAverage (openCubeAtScale (triadicCubeShift R) ell)
        (fun x => vecNormSq (u omega x))) ^ 2 := by
    funext omega
    exact meshEnergyCell_rpow_four_eq_sq_volumeAverage ell (u omega) R (hcoordW omega)
  have hmeasObs : Measurable fun omega => meshEnergyCell ell (u omega) R ^ (4 : ℝ) := by
    rw [hobs]
    exact hcellMeas.pow_const 2
  refine hdomInt.mono' hmeasObs.aestronglyMeasurable
    (Filter.Eventually.of_forall fun omega => ?_)
  have hnn : 0 ≤ meshEnergyCell ell (u omega) R ^ (4 : ℝ) :=
    Real.rpow_nonneg (meshEnergyCell_nonneg _ _ _) _
  rw [Real.norm_of_nonneg hnn]
  calc meshEnergyCell ell (u omega) R ^ (4 : ℝ)
      ≤ mesoWindowFourthEnergy ell (u omega) R :=
        mesoWindowEnergy_rpow_four_le ell (u omega) R (hcoordW omega) (hsqW omega)
          (hfourW omega)
    _ ≤ ratio * G omega :=
        mesoWindowFourthEnergy_le_ratio_mul_originCubeFourthEnergy' (u omega) hsub
          (hfour omega)
    _ ≤ ratio * (2 * Chead ^ (2 : ℕ) + 2 * T' omega ^ (2 : ℕ)) :=
        mul_le_mul_of_nonneg_left (hmaj omega) hratio0

/-! ## The two wired consumers -/

/-- **`hcellInt` for the Dirichlet corrector of `e.def.w`, as a theorem.**

For every `gamma` below one explicit threshold, in the whole parameter range of
`e.recurrence.params`, and for every sample family of zero-trace weak solutions
of `e.def.w` obeying the four spatial families on `cu_K`, the fourth power of
the per-cell coarse energy over any window contained in `cu_K` is integrable in
the sample.

Reaches exactly the external anchor
`Algsuperdiff.Frozen.External.calderon_zygmund`, a **proved** external,
inherited from `exists_freshShell_cubeEuclideanL8_leg_bound`. -/
theorem exists_gamma0_integrable_freshShellDirichlet_meshEnergyCell_rpow_four
    (d : ℕ) (hd : 2 ≤ d) :
    ∃ gamma0 : ℝ, 0 < gamma0 ∧ gamma0 ≤ 1 / 4 ∧
      ∀ (M : ABKModel d), M.gamma ≤ gamma0 →
        ∀ (m0 : ℤ) (Eind : {E : ℝ // 1 ≤ E}),
          Algsuperdiff.Frozen.Section3.inductionState M m0 Eind →
          ∀ (m K : ℤ) (hh : ℕ), 0 < hh → m - (hh : ℤ) ≤ m0 →
            (hh : ℝ) ≤ 6 * Disorder.cstar M * M.gamma⁻¹ →
            (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ ≤ (K : ℝ) - (m : ℝ) →
            ∀ e e' : Vec d, Book.Ch02.vecNorm e ≤ 1 →
              Book.Ch02.vecNorm e' ≤ 1 →
              ∀ wD : Cutoff.ShellSeq d → H10Function (openCubeSet (originCube d K)),
                (∀ omega, IsZeroTraceDirichletRhsWeakSolution
                    (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
                    (openCubeSet (originCube d K)) (wD omega)
                    (fun x => -Corrector.streamForcing
                      ((Annealed.sigmaBar M (m - (hh : ℤ)) : ℝ))⁻¹ omega
                      (m - (hh : ℤ)) m e x)) →
                (∀ omega, MemLp (fun x => Book.Ch02.vecNorm
                    ((wD omega).toH1Function.grad x)) 8
                    (normalizedCubeMeasure (originCube d K))) →
                (∀ (omega : Cutoff.ShellSeq d) (k : Fin d),
                  IntegrableOn (fun x => ((wD omega).toH1Function.grad x k) ^ 2)
                    (openCubeSet (originCube d K)) volume) →
                (∀ omega, IntegrableOn
                  (fun x => vecNormSq ((wD omega).toH1Function.grad x))
                  (openCubeSet (originCube d K)) volume) →
                (∀ omega, IntegrableOn
                  (fun x => vecNormSq ((wD omega).toH1Function.grad x) ^ 2)
                  (openCubeSet (originCube d K)) volume) →
                ∀ (ell : ℤ) (R : TriadicCube d),
                  openCubeAtScale (triadicCubeShift R) ell ⊆
                      openCubeSet (originCube d K) →
                  Integrable (fun omega : Cutoff.ShellSeq d =>
                    meshEnergyCell ell (wD omega).toH1Function.grad R ^ (4 : ℝ))
                    M.P.toMeasure := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨Chead, hCheadpos, gamma0, hg0pos, hg0quarter, hleg⟩ :=
    exists_freshShell_cubeEuclideanL8_leg_bound d hd
  refine ⟨gamma0, hg0pos, hg0quarter, ?_⟩
  intro M hMgamma m0 Eind hstate m K hh hhpos hm0 hcstar hK e e' he he' wD hsol hmem
    hcoord hsq hfour ell R hsub
  obtain ⟨Tfluct, hTnn, hTtail, hD, -⟩ :=
    hleg M hMgamma m0 Eind hstate m K hh hhpos hm0 hcstar hK e e' he he'
  have hApos : (0 : ℝ) < M.gamma ^ (100 : ℕ) := pow_pos M.shellPrefix.gamma_pos _
  exact integrable_meshEnergyCell_rpow_four_of_measurable
    (fun omega => (wD omega).toH1Function.grad) hCheadpos.le hApos hTnn hTtail hmem
    (fun omega => hD omega (wD omega) (hsol omega)) hcoord hsq hfour hsub
    (Corrector.measurable_volumeAverage_vecNormSq_sq_freshShellDirichletGrad
      (originCube d K) ((Annealed.sigmaBar M (m - (hh : ℤ)) : ℝ))⁻¹
      (m - (hh : ℤ)) m e (measurableSet_openCubeSet _) subset_rfl wD hsol)
    (measurable_volumeAverage_vecNormSq_freshShellDirichletGrad
      (originCube d K) ((Annealed.sigmaBar M (m - (hh : ℤ)) : ℝ))⁻¹
      (m - (hh : ℤ)) m e (measurableSet_openCubeAtScale _ _) hsub wD hsol)

/-- **`hcellInt` for the Neumann corrector of `e.def.w`, as a theorem.**  The
mean-zero Neumann mirror of the previous statement. -/
theorem exists_gamma0_integrable_freshShellNeumann_meshEnergyCell_rpow_four
    (d : ℕ) (hd : 2 ≤ d) :
    ∃ gamma0 : ℝ, 0 < gamma0 ∧ gamma0 ≤ 1 / 4 ∧
      ∀ (M : ABKModel d), M.gamma ≤ gamma0 →
        ∀ (m0 : ℤ) (Eind : {E : ℝ // 1 ≤ E}),
          Algsuperdiff.Frozen.Section3.inductionState M m0 Eind →
          ∀ (m K : ℤ) (hh : ℕ), 0 < hh → m - (hh : ℤ) ≤ m0 →
            (hh : ℝ) ≤ 6 * Disorder.cstar M * M.gamma⁻¹ →
            (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ ≤ (K : ℝ) - (m : ℝ) →
            ∀ e e' : Vec d, Book.Ch02.vecNorm e ≤ 1 →
              Book.Ch02.vecNorm e' ≤ 1 →
              ∀ wN : Cutoff.ShellSeq d →
                  H1MeanZeroFunction (openCubeSet (originCube d K)),
                (∀ omega, IsMeanZeroNeumannRhsWeakSolution
                    (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
                    (openCubeSet (originCube d K)) (wN omega)
                    (fun x => -Corrector.streamForcing
                      ((Annealed.sigmaBar M (m - (hh : ℤ)) : ℝ))⁻¹ omega
                      (m - (hh : ℤ)) m e' x)) →
                (∀ omega, MemLp (fun x => Book.Ch02.vecNorm
                    ((wN omega).toH1Function.grad x)) 8
                    (normalizedCubeMeasure (originCube d K))) →
                (∀ (omega : Cutoff.ShellSeq d) (k : Fin d),
                  IntegrableOn (fun x => ((wN omega).toH1Function.grad x k) ^ 2)
                    (openCubeSet (originCube d K)) volume) →
                (∀ omega, IntegrableOn
                  (fun x => vecNormSq ((wN omega).toH1Function.grad x))
                  (openCubeSet (originCube d K)) volume) →
                (∀ omega, IntegrableOn
                  (fun x => vecNormSq ((wN omega).toH1Function.grad x) ^ 2)
                  (openCubeSet (originCube d K)) volume) →
                ∀ (ell : ℤ) (R : TriadicCube d),
                  openCubeAtScale (triadicCubeShift R) ell ⊆
                      openCubeSet (originCube d K) →
                  Integrable (fun omega : Cutoff.ShellSeq d =>
                    meshEnergyCell ell (wN omega).toH1Function.grad R ^ (4 : ℝ))
                    M.P.toMeasure := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨Chead, hCheadpos, gamma0, hg0pos, hg0quarter, hleg⟩ :=
    exists_freshShell_cubeEuclideanL8_leg_bound d hd
  refine ⟨gamma0, hg0pos, hg0quarter, ?_⟩
  intro M hMgamma m0 Eind hstate m K hh hhpos hm0 hcstar hK e e' he he' wN hsol hmem
    hcoord hsq hfour ell R hsub
  obtain ⟨Tfluct, hTnn, hTtail, -, hN⟩ :=
    hleg M hMgamma m0 Eind hstate m K hh hhpos hm0 hcstar hK e e' he he'
  have hApos : (0 : ℝ) < M.gamma ^ (100 : ℕ) := pow_pos M.shellPrefix.gamma_pos _
  exact integrable_meshEnergyCell_rpow_four_of_measurable
    (fun omega => (wN omega).toH1Function.grad) hCheadpos.le hApos hTnn hTtail hmem
    (fun omega => hN omega (wN omega) (hsol omega)) hcoord hsq hfour hsub
    (Corrector.measurable_volumeAverage_vecNormSq_sq_freshShellNeumannGrad
      (originCube d K) ((Annealed.sigmaBar M (m - (hh : ℤ)) : ℝ))⁻¹
      (m - (hh : ℤ)) m e' (measurableSet_openCubeSet _) subset_rfl wN hsol)
    (measurable_volumeAverage_vecNormSq_freshShellNeumannGrad
      (originCube d K) ((Annealed.sigmaBar M (m - (hh : ℤ)) : ℝ))⁻¹
      (m - (hh : ℤ)) m e' (measurableSet_openCubeAtScale _ _) hsub wN hsol)

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
