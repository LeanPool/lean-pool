/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenCaccFinalCore
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenVolume
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.NuIdentification
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.TranslationTransportNorms
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.EdFinalInputs
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BesovBridge
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.InteriorGlueWindow
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.TranslationTransportAssembly
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenSandwich

/-!
# StepSevenCaccFinalInterior

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


namespace Algsuperdiff.Section4.Provider.Regularity

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03 MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. The interior geometry -/

/-- **The concentric Caccioppoli core is the cube two scales down.**  At the
Dirichlet-patch centre `x = 0` the lemma's core `□_Q ∩ (x + □_{Q.scale-2})` is
`□_{j-2}` — the set the §4.4 volume step passes to. -/
theorem caccioppoliCoreSet_originCube_zero (j : ℤ) :
    caccioppoliCoreSet (originCube d j) 0 = openCubeSet (originCube d (j - 2)) := by
  rw [caccioppoliCoreSet, openCubeAtScale_eq_image_add]
  have h0 : (fun y : Vec d => (0 : Vec d) + y) '' openCubeSet (originCube d (j - 2)) =
      openCubeSet (originCube d (j - 2)) := by simp
  have hsc : (originCube d j).scale = j := rfl
  rw [hsc, h0]
  exact Set.inter_eq_right.mpr (openCubeSet_originCube_subset_of_le (by omega))

/-- **The Dirichlet-patch binder at the concentric centre**, discharged: the patch
`0 + □_{j-1}` sits inside `□_j`. -/
theorem openCubeAtScale_zero_pred_subset (j : ℤ) :
    openCubeAtScale (0 : Vec d) ((originCube d j).scale - 1) ⊆
      openCubeSet (originCube d j) := by
  rw [openCubeAtScale_eq_image_add]
  have h0 : (fun y : Vec d => (0 : Vec d) + y) '' openCubeSet (originCube d (j - 1)) =
      openCubeSet (originCube d (j - 1)) := by simp
  have hsc : (originCube d j).scale = j := rfl
  rw [hsc, h0]
  exact openCubeSet_originCube_subset_of_le (by omega)

/-- **The window IS the cube on the interior branch.**  For `z ∈ □_{m-1}` and `j ≤
m-1` the truncation is inert: `U_j = (z+□_j) ∩ □_m = z + □_j`. -/
theorem truncatedWindow_eq_translateSet_of_mem_inner {m j : ℤ} {z : Vec d}
    (hz : z ∈ openCubeSet (originCube d (m - 1))) (hj : j ≤ m - 1) :
    truncatedWindow z m j = translateSet z (openCubeSet (originCube d j)) := by
  rw [truncatedWindow, ← image_add_eq_translateSet]
  exact Set.inter_eq_left.mpr (image_add_subset_openCubeSet_of_mem_inner hz hj)

/-! ## 2. The display's own gradient scalar -/

/-- **`ν^{1/2}‖∇u‖_{L²(V)}`**, the left-hand side of `e.gradient.with.shom` and
the Caccioppoli's core energy, as ONE named scalar: for the §4.4 family
`𝐚_{L,k} = ν I + 𝐤` with `𝐤` antisymmetric the symmetric coefficient energy IS
`ν ⨍|∇u|²`. -/
def stepSevenNuGradNorm (nu : ℝ) (V : Set (Vec d)) (G : Vec d → Vec d) : ℝ :=
  Real.sqrt (nu * volumeAverage V (fun x => vecNormSq (G x)))

theorem stepSevenNuGradNorm_nonneg (nu : ℝ) (V : Set (Vec d)) (G : Vec d → Vec d) :
    0 ≤ stepSevenNuGradNorm nu V G := Real.sqrt_nonneg _

/-- **The named scalar IS the root display's own left-hand side.**
`RootAssemblyConditional.RootLatticeDisplay` writes the same quantity as `√ν ·
‖ |∇u| ‖_{L²(V)}` with the pointwise Euclidean norm inside; the two agree
exactly. -/
theorem stepSevenNuGradNorm_eq_sqrt_mul_normalizedL2On {nu : ℝ} (hnu : 0 ≤ nu)
    (V : Set (Vec d)) (G : Vec d → Vec d) :
    stepSevenNuGradNorm nu V G =
      Real.sqrt nu * normalizedL2On V (fun y => Real.sqrt (vecNormSq (G y))) := by
  have hfun : (fun x => Real.sqrt (vecNormSq (G x)) ^ 2) = fun x => vecNormSq (G x) := by
    funext x
    exact Real.sq_sqrt (vecNormSq_nonneg (G x))
  rw [stepSevenNuGradNorm, normalizedL2On, hfun, ← Real.sqrt_mul hnu]

/-- The named scalar in the ratio spelling's volume step uses. -/
theorem stepSevenNuGradNorm_eq_sqrt_div (nu : ℝ) (V : Set (Vec d)) (G : Vec d → Vec d) :
    stepSevenNuGradNorm nu V G =
      Real.sqrt ((nu * ∫ x in V, vecNormSq (G x) ∂volume) / (volume V).toReal) := by
  rw [stepSevenNuGradNorm, volumeAverage]
  congr 1
  field_simp

/-! ## 3. The `gradCore` identification -/

/-- ** residue, the `gradCore` identification.**

The Caccioppoli's left-hand side, read at the concentric patch centre in the
translated frame, IS the display's `ν^{1/2}‖∇u‖_{L²(U_{j-2})}` on the §4.4
window: the `ν`-identification removes the coefficient and the translation
transport moves the frame, both without constants.  `v` is the transported
solution (`v = u(·+z)`, `∇v = ∇u(·+z)` — the builder's own two clauses). -/
theorem sqrt_localizedCoeffEnergyValue_core_eq_nuGradNorm (M : ABKModel d)
    (L mf m j : ℤ) (Qf : TriadicCube d) {z : Vec d} (omega : Cutoff.CutoffSample d)
    (v : H1Function (Ch02.cubeDomain (originCube d j) : Set (Vec d)))
    (G : Vec d → Vec d) (hg : ∀ y, v.grad y = G (y + z))
    (hz : z ∈ openCubeSet (originCube d (m - 1))) (hj : j - 2 ≤ m - 1) :
    Real.sqrt (localizedCoeffEnergyValue (caccioppoliCoreSet (originCube d j) 0)
        ((Support.fluxCorrectedCoeffFamily M L mf Qf
          (Cutoff.translateCutoffSample z omega)).coeffOn (originCube d j)) v) =
      stepSevenNuGradNorm (M.nu : ℝ) (truncatedWindow z m (j - 2)) G := by
  rw [stepSevenNuGradNorm]
  congr 1
  rw [localizedCoeffEnergyValue_fluxCorrectedCoeffFamily_eq,
    caccioppoliCoreSet_originCube_zero]
  have hfun : (fun x => vecNormSq (v.grad x)) = fun x => vecNormSq (G (x + z)) := by
    funext x; rw [hg x]
  have h1 := normalizedSetAverage_vecNormSq_translateSet z
    (openCubeSet (originCube d (j - 2))) G
  rw [truncatedWindow_eq_translateSet_of_mem_inner hz hj, hfun]
  exact congrArg (fun t : ℝ => (M.nu : ℝ) * t) h1.symm

/-! ## 4. The `oscLo` match -/

/-- ** residue, the cube-versus-window `oscLo` match.** -/
theorem normalizedL2On_openCubeSet_sub_eq_truncatedWindow {m j : ℤ} {z : Vec d}
    (w : Vec d → ℝ) (v : Vec d → ℝ) (hv : ∀ y, v y = w (y + z)) (c : ℝ)
    (hz : z ∈ openCubeSet (originCube d (m - 1))) (hj : j ≤ m - 1) :
    normalizedL2On (openCubeSet (originCube d j)) (fun y => v y - c) =
      normalizedL2On (truncatedWindow z m j) (fun x => w x - c) := by
  have hfun : (fun y => v y - c) = fun x => w (x + z) - c := by
    funext y; rw [hv y]
  have h1 := normalizedL2SqOnSet_translateSet z (openCubeSet (originCube d j))
    (fun x => w x - c)
  rw [truncatedWindow_eq_translateSet_of_mem_inner hz hj, hfun]
  exact congrArg Real.sqrt h1.symm

/-! ## 5. `hvol` with the mass monotonicity discharged -/

/-- The gradient square of an `H¹(□_m)` function is integrable on every subset of
`□_m`. -/
theorem integrableOn_vecNormSq_grad_of_subset {m : ℤ}
    (u : H1Function (openCubeSet (originCube d m))) {V : Set (Vec d)}
    (hV : V ⊆ openCubeSet (originCube d m)) :
    IntegrableOn (fun x => vecNormSq (u.grad x)) V volume := by
  have h : IntegrableOn (fun x => vecNormSq (u.grad x))
      (openCubeSet (originCube d m)) volume := by
    simpa [vecNormSq] using integrableOn_vecDot_of_memVectorL2 u.grad_memVectorL2
      u.grad_memVectorL2
  exact h.mono_set hV

/-- **'s mass comparison, discharged.** (b)'s integral monotonicity `I_S ≤ I_T` on
nested windows is not an estimate: the integrand is a square and `u ∈ H¹(□_m)`. -/
theorem stepSevenGradMass_mono {m : ℤ} {nu : ℝ} (hnu : 0 ≤ nu)
    (u : H1Function (openCubeSet (originCube d m))) {S T : Set (Vec d)}
    (hST : S ⊆ T) (hT : T ⊆ openCubeSet (originCube d m)) :
    nu * ∫ x in S, vecNormSq (u.grad x) ∂volume ≤
      nu * ∫ x in T, vecNormSq (u.grad x) ∂volume := by
  have hmono := setIntegral_mono_set (integrableOn_vecNormSq_grad_of_subset u hT)
    (Filter.Eventually.of_forall fun x => vecNormSq_nonneg (u.grad x))
    (Filter.Eventually.of_forall hST)
  exact mul_le_mul_of_nonneg_left hmono hnu

/-- **`hvol` at the §4.4 carriers ((b)), unconditional.**

```text
  ν^{1/2}‖∇u‖_{L²(U_{n+1})} ≤ 3^{(d/2)(n'-n)} · ν^{1/2}‖∇u‖_{L²(U_{n'-2})} .
```

The volume-factor producer with its one caller-side input — the mass comparison
— discharged from `u ∈ H¹(□_m)`.  The side condition `n+1 ≤ n'-2` is free at
the Step-7a selection. -/
theorem stepSevenNuGradNorm_le_volumeRatio (d : ℕ) {m n n' : ℤ} {z : Vec d} {nu : ℝ}
    (hnu : 0 ≤ nu) (hz : z ∈ openCubeSet (originCube d m)) (hnm : n ≤ m)
    (hcore : n + 1 ≤ n' - 2) (u : H1Function (openCubeSet (originCube d m))) :
    stepSevenNuGradNorm nu (truncatedWindow z m (n + 1)) u.grad ≤
      Real.rpow (3 : ℝ) (((d : ℝ) / 2) * ((n' : ℝ) - (n : ℝ))) *
        stepSevenNuGradNorm nu (truncatedWindow z m (n' - 2)) u.grad := by
  have hmono := stepSevenGradMass_mono hnu u
    (truncatedWindow_succ_subset_caccCore z m hcore)
    (truncatedWindow_subset_domain z m (n' - 2))
  have h := stepSevenVolumeRatio_le d (n' := n') hz hnm hmono
  rw [stepSevenNuGradNorm_eq_sqrt_div, stepSevenNuGradNorm_eq_sqrt_div]
  exact h

/-! ## 6. The `hcacc` slot at the §4.4 interior carriers -/

/-- **The `hcacc` slot on the interior branch.**

`l.coarse.grained.Caccioppoli.RHS` at the §4.4 exponent pin, in the energy-norm
shape `StepSevenCaccGradient.stepSevenGradientWithShom` consumes, with every
scalar read on the §4.4 windows:

```text
  ν^{1/2}‖∇u‖_{L²(U_{n'-2})}
    ≤ Ccacc · ( √λ_{1/8,1} · 3^{-n'}‖u - (u)_{U_{n'}}‖_{L²(U_{n'})} )
      + Ccacc · dataM ,
  Ccacc = √(caccioppoliWithRHSPrefactor C □_{n'} 𝐚 (1/4) (1/8)) ,
  dataM = √(F · λ_{1/8,1}^{-1}) · [𝐠]_{B^{1/4}(□_{n'})} .
```

Conditional on NOTHING beyond the pinned lemma's own equation and forcing
binders and the printed interior gate `z ∈ □_{m-1}`: the Dirichlet patch is
discharged at the concentric centre, the window/cube and frame identifications
are the exact equalities of §§1--4, and the `∇h` summand of the printed display
is absent exactly because the gate is the printed indicator's own condition (
residue). -/
theorem exists_stepSevenCaccHcacc_interior (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (L mf m n' : ℤ) (Qf : TriadicCube d) {z : Vec d}
        (omega : Cutoff.CutoffSample d)
        (u : H1Function (openCubeSet (originCube d m)))
        (v : H1Function (Ch02.cubeDomain (originCube d n') : Set (Vec d)))
        {g : Vec d → Vec d} (c : ℝ),
        (∀ y, v.toFun y = u.toFun (y + z)) → (∀ y, v.grad y = u.grad (y + z)) →
        z ∈ openCubeSet (originCube d (m - 1)) → n' ≤ m - 1 →
        IsForcedEquation (originCube d n')
          (Support.fluxCorrectedCoeffFamily M L mf Qf
            (Cutoff.translateCutoffSample z omega)) v g →
        ForceBesovRegularity (originCube d n') stepOneS g →
          stepSevenNuGradNorm (M.nu : ℝ) (truncatedWindow z m (n' - 2)) u.grad ≤
            Real.sqrt (caccioppoliWithRHSPrefactor C (originCube d n')
                (Support.fluxCorrectedCoeffFamily M L mf Qf
                  (Cutoff.translateCutoffSample z omega))
                stepSevenCaccS stepSevenCaccT) *
                (Real.sqrt (Ch02.lambdaS (originCube d n')
                    stepSevenCaccT
                    (Support.fluxCorrectedCoeffFamily M L mf Qf
                      (Cutoff.translateCutoffSample z omega))) *
                  ((3 : ℝ) ^ (-n') *
                    normalizedL2On (truncatedWindow z m n') (fun x => u.toFun x - c))) +
              Real.sqrt (caccioppoliWithRHSPrefactor C (originCube d n')
                  (Support.fluxCorrectedCoeffFamily M L mf Qf
                    (Cutoff.translateCutoffSample z omega))
                  stepSevenCaccS stepSevenCaccT) *
                (Real.sqrt (stepSevenCaccForcingFactor *
                    (Ch02.lambdaS (originCube d n') stepSevenCaccT
                      (Support.fluxCorrectedCoeffFamily M L mf Qf
                        (Cutoff.translateCutoffSample z omega)))⁻¹) *
                  scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d n')
                    stepOneS g) := by
  obtain ⟨C, hCpos, hC⟩ := exists_stepSevenCaccioppoliEnergyNorm d
  refine ⟨C, hCpos, ?_⟩
  intro M L mf m n' Qf z omega u v g c hval hgrad hz hn' heq hforce
  have hbase := hC (x := (0 : Vec d)) v c heq (openCubeAtScale_zero_pred_subset n') hforce
  have hcore := sqrt_localizedCoeffEnergyValue_core_eq_nuGradNorm M L mf m n' Qf omega v
    u.grad hgrad hz (by omega : n' - 2 ≤ m - 1)
  have hosc := normalizedL2On_openCubeSet_sub_eq_truncatedWindow (m := m) (j := n')
    u.toFun v.toFun hval c hz (by omega : n' ≤ m - 1)
  have hsc : (originCube d n').scale = n' := rfl
  rw [hcore, hsc, hosc] at hbase
  exact hbase

/-- ** residue, the Gagliardo ↔ `ForceBesovRegularity` bridge, at the Step-7c
interior carriers.**

The §4.4 forcing datum is carried on `□_m` as the manuscript's `𝐠 ∈ H^{1/4}`
(`MemLp` for the normalized cube measure and for the Gagliardo product measure
— literally the two `MemLp` binders the Step-6 interior endpoint carries), while
`l.coarse.grained.Caccioppoli.RHS` asks for CoarseGraining's
`ForceBesovRegularity`
at the good-scale cube in the translated frame.  No new analysis, and no
constant. -/
theorem forceBesovRegularity_stepSevenCacc_interior [NeZero d] {m n' : ℤ} {z : Vec d}
    {g : Vec d → Vec d} (hz : z ∈ openCubeSet (originCube d (m - 1))) (hn' : n' ≤ m - 1)
    (hgL2 : MemLp g 2
      (Support.normalizedVolumeMeasureOn (openCubeSet (originCube d m))))
    (hgW : MemLp (Gagliardo.gagliardoKernel stepOneS 2 g) 2
      (Support.normalizedGagliardoMeasureOn (openCubeSet (originCube d m)))) :
    ForceBesovRegularity (originCube d n') stepOneS (fun x => -g (x + z)) := by
  have hsub : (fun y => z + y) '' openCubeSet (originCube d n') ⊆
      openCubeSet (originCube d m) := image_add_subset_openCubeSet_of_mem_inner hz hn'
  have hL2 := memLp_two_child_of_clause_iv hsub hgL2
  have hW := memLp_normalizedGagliardoMeasureOn_subset hsub
    (volume_openCubeSet_ne_zero (originCube d m))
    (volume_openCubeSet_ne_top (originCube d m))
    (volume_image_add_openCubeSet_ne_zero z (originCube d n')) hgW
  exact forceBesovRegularity_translated_neg (originCube d n') stepOneS_pos
    (by rw [stepOneS]; norm_num) hL2 hW

/-! ## 8. The transported solution of the good-scale cube -/

/-- `StepSevenGradForcedSolution.isForcedEquation_fluxCorrected_of_subset`
re-derived with the flux-correction parameters `(scale, cube)` left free
instead of pinned to the solution cube's own `(k, □_k)`.  The freedom is what
lets the clause-(B) producer
(`StepSevenLambdaEndpoint.ae_stepSevenLambdaSlots`, which caps the family `(k,
□_k)` on the cube `□_{k-1}`) and the good-scale Caccioppoli (whose cube is
`□_{n'}`) speak about one family: take `(mf, Qf) = (n'+1, □_{n'+1})`.  A
re-derivation, not a new statement. -/
theorem isForcedEquation_fluxCorrected_freeFlux {m n' mf : ℤ} (M : ABKModel d)
    (L : ℤ) (Qf : TriadicCube d) (z : Vec d) (omega : Cutoff.CutoffSample d)
    {uglob : H1Function (openCubeSet (originCube d m))} {gsrc : Vec d → Vec d}
    (hsub : translateSet z (openCubeSet (originCube d n')) ⊆
      openCubeSet (originCube d m))
    (heq : Support.IsDivFormWeakSolutionOn
      (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
      (openCubeSet (originCube d m)) uglob gsrc) :
    IsForcedEquation (originCube d n')
      (Support.fluxCorrectedCoeffFamily M L mf Qf (Cutoff.translateCutoffSample z omega))
      (H1Function.untranslate z
        (uglob.restrict (isOpen_translateSet_openCubeSet z n') hsub))
      (fun x => -gsrc (x + z)) := by
  have hrestrict := isDivFormWeakSolutionOn_restrict
    (isOpen_translateSet_openCubeSet z n') hsub heq
  have huntrans := isDivFormWeakSolutionOn_translateCutoffSample M L z omega hrestrict
  have hshift := isDivFormWeakSolutionOn_fluxCorrectedField M L mf Qf
    (Cutoff.translateCutoffSample z omega) huntrans
  refine isForcedEquation_neg_of_isDivFormWeakSolutionOn ?_
  rw [fluxCorrectedCoeffFamily_coeffOn_toCoeffField M L mf Qf (originCube d n')
    (Cutoff.translateCutoffSample z omega)]
  exact hshift

/-- **The Caccioppoli's solution object, built from `t.regularity`'s own
Dirichlet datum on the interior branch.**

At `z ∈ □_{m-1}` and `n' ≤ m-1` the translate `z + □_{n'}` sits inside `□_m`,
so the transport applies at the lattice centre `z` itself — no clamp, no off-grid
centre.  The flux pair `(mf, Qf)` is free, so the caller may take the pair the
clause-(B) caps are stated at.  The two frame identities the `hcacc` producer
consumes are the proved `untranslate` clauses. -/
theorem exists_stepSevenCaccInteriorSolution {m n' mf : ℤ} (M : ABKModel d) (L : ℤ)
    (Qf : TriadicCube d) {z : Vec d} (omega : Cutoff.CutoffSample d)
    {uglob hdat : H1Function (openCubeSet (originCube d m))} {gsrc : Vec d → Vec d}
    (hz : z ∈ openCubeSet (originCube d (m - 1))) (hn' : n' ≤ m - 1)
    (hsol : Support.IsDirichletSolutionOn
      (Cutoff.coefficientCutoff M.nu L omega).toCoeffField (originCube d m) uglob hdat
      gsrc) :
    ∃ v : H1Function (Ch02.cubeDomain (originCube d n') : Set (Vec d)),
      (∀ y, v.toFun y = uglob.toFun (y + z)) ∧
      (∀ y, v.grad y = uglob.grad (y + z)) ∧
      IsForcedEquation (originCube d n')
        (Support.fluxCorrectedCoeffFamily M L mf Qf
          (Cutoff.translateCutoffSample z omega)) v (fun x => -gsrc (x + z)) := by
  have hsub : translateSet z (openCubeSet (originCube d n')) ⊆
      openCubeSet (originCube d m) := by
    rw [← image_add_eq_translateSet]
    exact image_add_subset_openCubeSet_of_mem_inner hz hn'
  refine ⟨H1Function.untranslate z
      (uglob.restrict (isOpen_translateSet_openCubeSet z n') hsub), ?_, ?_, ?_⟩
  · intro y
    exact untranslate_restrict_toFun uglob hsub y
  · intro y
    rfl
  · exact isForcedEquation_fluxCorrected_freeFlux M L Qf z omega hsub hsol.2

end

end Algsuperdiff.Section4.Provider.Regularity
