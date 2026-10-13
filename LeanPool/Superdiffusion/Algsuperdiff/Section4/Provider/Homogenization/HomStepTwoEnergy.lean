/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomBridgeDirichlet
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.LambdaCaps
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.EnergyRHS.Theory
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MultiscaleEllipticity.Finite.Properties
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.StabilityIndexCube

/-!
# HomStepTwoEnergy

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Theorem B, §4.5, Step 2a: the energy-from-data display

## The target (Theorem B, Step 2: the energy from data)

```
  ν^{1/2} ‖∇u‖_{L²(□_m)}
    ≤ C ( 1 + 𝓔_{1/4,∞,2}(□_m; ã_{L,m}, σ_m) ) ( σ_m^{-1/2} 3^{m/2} + σ_m^{1/2} 3^{m/2} )
```

proved, per the node's own `EDGE`s, from the coarse-graining right-hand side
and the display bounding the `Λ`'s by the `𝓔`'s.

## What is proved here, exactly

The two named inputs, composed on the carriers:

* the coarse-graining right-hand side = `CoarseGraining`'s `Ch03.energyConsequencesRHSTheory`
(Dirichlet half),
  entered through the carrier map `dirichletForcedCubeSolutionOfIsDirichlet
  SolutionOn` (obstruction 2) and read on the left through the `ν`-drop
  (obstruction 1);
* the display bounding the `Λ`'s by the `𝓔`'s = `CoarseGraining`'s
  `Ch02.max_weightedEllipticity_finite_two_le_card_mul_homogenizationError_sq_add_one`
  at the constant `2d`, transported by `ExcessDecay.max_ellipticityRatio_le_
  homogenizationError`.

The output (`exists_sqrt_nu_mul_gradL2_le`) is

```
  ν^{1/2} ‖∇u‖_{L²(□_m)}
    ≤ C(d) t^{-3/2} · σ_m^{-1/2} √(2d) ( 1 + 𝓔_{t/2}(□_m; ã_{L,m}, σ_m) ) · B_g
    + C(d) t^{-1/2} · σ_m^{ 1/2} √(2d) ( 1 + 𝓔_{t}  (□_m; ã_{L,m}, σ_m) ) · B_h
```

with `B_g`, `B_h` `CoarseGraining`'s own note-normalized Besov data quantities
at index `t` (`√(2d)` is the display bounding the `Λ`'s by the `𝓔`'s's own
dimensional loss, kept visible).

## The three deviations from the printed display

Each is visible in the statement; none is absorbed.

1. **TWO error indices, not one.**  `CoarseGraining`'s coarse-graining right-hand side places `λ` at
the index
   `t/2` and `Λ` at the index `t` (this is confirmed
   here in the definition of
   `Ch03.dirichletEnergyWithRHSRHS`).  the display bounding the `Λ`'s by the `𝓔`'s is therefore
   instantiated TWICE, at `t/2` and at `t`, and the display carries
   `𝓔_{t/2}` and `𝓔_t` separately.  Collapsing them to the printed single
   `𝓔_{1/4}` needs an index-monotonicity of `𝓔_{·,∞,2}` that is NOT available:
   `Ch02.geometricWeight` normalizes the scale weights to a probability
   distribution, so `s ↦ 𝓔_{s,∞,2}` is a weighted average whose monotonicity
   depends on the response sequence.  The printed choice `1/4` moreover forces
   `t = 1/2`, at which the DATA leg is infinite for `C^{0,1/2}` data (correction
).  RECORDED AS A SOURCE FINDING; the two-index display is the
   honest one and is what Step 3 can consume.
2. **The `t`-powers stay displayed**: `t^{-3/2}` and
   `t^{-1/2}` are `CoarseGraining`'s own prefactors of the coarse-graining right-hand side.  At the
   §4.5 value
   `t = s = |log γ|⁻¹` they are `|log γ|^{3/2}` and `|log γ|^{1/2}`, NOT
   constants; the source absorbs them into `C` silently and the node's own
   `NOTE` licenses the absorption only because it is spent once.  Nothing is
   absorbed here.
3. **The data legs are `CoarseGraining`'s Besov quantities, not `3^{m/2}`.**  The passage
   `B_g, B_h ≤ C 3^{m/2}` is the data embedding, given in
   the `H^s`/Gagliardo carrier
   (`HomBridgeDataEmbedding.three_rpow_mul_normalizedGagliardo_originCube_le_
   pinned`), but `CoarseGraining`'s coarse-graining right-hand side states its data legs in the
   DYADIC-descendant
   `cubeBesov` carrier.  The Gagliardo → `cubeBesov` bridge exists
   (`Provider.ExcessDecay.scaleNormalizedPositiveBesovVectorSeminormTwo_le_
   gagliardo`); its two side conditions — `MemLp g 2` and `Gagliardo.MemWsp Q t 2 g`
   from a Hölder bound — do NOT exist and are the exact residue
   (they are the two Gagliardo-side atoms of the Step-2b family).  Since
   `ForceBesovRegularity` is ALSO a hypothesis of the coarse-graining right-hand side itself, the
   two
   residues are the same two atoms; nothing else is missing.
-/

open Algsuperdiff.Section3
open Algsuperdiff.Section3.Observable
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03 MeasureTheory

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. Two `rpow` spellings

Disclosed re-derivation: the same two spellings are available in
`Provider/ExcessDecay/InteriorEllipticity.lean`; they are re-proved here (three
lines each) to keep this module's import cone off the excess-decay boundary
tree, which is under concurrent edit. -/

theorem homRpowHalf (x : ℝ) : Real.rpow x (1 / 2 : ℝ) = Real.sqrt x := by
  change x ^ (1 / 2 : ℝ) = _
  rw [← Real.sqrt_eq_rpow]

theorem homRpowNegHalf {x : ℝ} (hx : 0 < x) :
    Real.rpow x (-(1 / 2 : ℝ)) = Real.sqrt x⁻¹ := by
  change x ^ (-(1 / 2 : ℝ)) = _
  rw [Real.rpow_neg hx.le, ← Real.inv_rpow hx.le, ← Real.sqrt_eq_rpow]

/-! ## 2. the display bounding the `Λ`'s by the `𝓔`'s at `CoarseGraining`'s two ellipticity factors
-/

/-- The `𝓔`-envelope `√(2d(𝓔² + 1))` of the display bounding the `Λ`'s by the `𝓔`'s, at the cube
`Q`, the family `A`, the index `t` and the comparator `σ Id`. -/
def homErrorEnvelope (d : ℕ) [NeZero d] (Q : TriadicCube d) (A : CoeffFamily d)
    (t sigma : ℝ) : ℝ :=
  Real.sqrt (2 * (d : ℝ) *
    (Ch02.HomogenizationErrorOnCube Q t .infinity (.finite 2) A
      (scalarMatrix (d := d) sigma) ^ 2 + 1))

/-- **the display bounding the `Λ`'s by the `𝓔`'s, lower half.**  `CoarseGraining`'s
`λ_{t,2}^{-1/2}` factor is
at most `σ^{-1/2} √(2d(𝓔_t² + 1))`. -/
theorem poincareLowerEllipticityFactor_le [NeZero d] (Q : TriadicCube d)
    (A : CoeffFamily d) {t sigma : ℝ} (ht : 0 < t) (hsigma : 0 < sigma) :
    poincareLowerEllipticityFactor Q A t (.finite 2) ≤
      Real.sqrt sigma⁻¹ * homErrorEnvelope d Q A t sigma := by
  have hlam : (0 : ℝ) < Ch02.lambdaSq Q t (.finite 2) A :=
    Ch02.lambdaSq_finite_pos Q A ht (by norm_num)
  have hmax := max_ellipticityRatio_le_homogenizationError (d := d) Q A ht hsigma
  have hhalf : sigma * (Ch02.lambdaSq Q t (.finite 2) A)⁻¹ ≤
      2 * (d : ℝ) *
        (Ch02.HomogenizationErrorOnCube Q t .infinity (.finite 2) A
          (scalarMatrix (d := d) sigma) ^ 2 + 1) :=
    le_trans (le_max_right _ _) hmax
  have hinv : (Ch02.lambdaSq Q t (.finite 2) A)⁻¹ ≤
      sigma⁻¹ * (2 * (d : ℝ) *
        (Ch02.HomogenizationErrorOnCube Q t .infinity (.finite 2) A
          (scalarMatrix (d := d) sigma) ^ 2 + 1)) := by
    rw [← le_div_iff₀' hsigma] at hhalf
    rwa [inv_mul_eq_div]
  rw [poincareLowerEllipticityFactor, homRpowNegHalf hlam, homErrorEnvelope,
    ← Real.sqrt_mul (le_of_lt (inv_pos.mpr hsigma))]
  exact Real.sqrt_le_sqrt hinv

/-- **the display bounding the `Λ`'s by the `𝓔`'s, upper half.**  `CoarseGraining`'s `Λ_{t,2}^{1/2}`
factor is at
most `σ^{1/2} √(2d(𝓔_t² + 1))`. -/
theorem poincareUpperEllipticityFactor_le [NeZero d] (Q : TriadicCube d)
    (A : CoeffFamily d) {t sigma : ℝ} (ht : 0 < t) (hsigma : 0 < sigma) :
    poincareUpperEllipticityFactor Q A t (.finite 2) ≤
      Real.sqrt sigma * homErrorEnvelope d Q A t sigma := by
  have hmax := max_ellipticityRatio_le_homogenizationError (d := d) Q A ht hsigma
  have hhalf : sigma⁻¹ * Ch02.LambdaSq Q t (.finite 2) A ≤
      2 * (d : ℝ) *
        (Ch02.HomogenizationErrorOnCube Q t .infinity (.finite 2) A
          (scalarMatrix (d := d) sigma) ^ 2 + 1) :=
    le_trans (le_max_left _ _) hmax
  have hup : Ch02.LambdaSq Q t (.finite 2) A ≤
      sigma * (2 * (d : ℝ) *
        (Ch02.HomogenizationErrorOnCube Q t .infinity (.finite 2) A
          (scalarMatrix (d := d) sigma) ^ 2 + 1)) := by
    rw [inv_mul_eq_div, div_le_iff₀' hsigma] at hhalf
    exact hhalf
  rw [poincareUpperEllipticityFactor, homRpowHalf, homErrorEnvelope,
    ← Real.sqrt_mul (le_of_lt hsigma)]
  exact Real.sqrt_le_sqrt hup

/-- The envelope in the source's `1 + 𝓔` shape: `√(2d(𝓔² + 1)) ≤ √(2d)(1 + 𝓔)`. -/
theorem homErrorEnvelope_le_one_add [NeZero d] (Q : TriadicCube d) (A : CoeffFamily d)
    {t sigma : ℝ} (ht : 0 < t) :
    homErrorEnvelope d Q A t sigma ≤
      Real.sqrt (2 * (d : ℝ)) *
        (1 + Ch02.HomogenizationErrorOnCube Q t .infinity (.finite 2) A
          (scalarMatrix (d := d) sigma)) := by
  have hE : (0 : ℝ) ≤ Ch02.HomogenizationErrorOnCube Q t .infinity (.finite 2) A
      (scalarMatrix (d := d) sigma) :=
    homogenizationErrorOnCube_infinity_two_nonneg Q A _ ht
  have hsq : Ch02.HomogenizationErrorOnCube Q t .infinity (.finite 2) A
        (scalarMatrix (d := d) sigma) ^ 2 + 1 ≤
      (1 + Ch02.HomogenizationErrorOnCube Q t .infinity (.finite 2) A
        (scalarMatrix (d := d) sigma)) ^ 2 := by
    have hexp : (1 + Ch02.HomogenizationErrorOnCube Q t .infinity (.finite 2) A
        (scalarMatrix (d := d) sigma)) ^ 2 =
        Ch02.HomogenizationErrorOnCube Q t .infinity (.finite 2) A
          (scalarMatrix (d := d) sigma) ^ 2 + 1 +
          2 * Ch02.HomogenizationErrorOnCube Q t .infinity (.finite 2) A
            (scalarMatrix (d := d) sigma) := by ring
    rw [hexp]
    linarith only [hE]
  have hdnn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hd : (0 : ℝ) ≤ 2 * (d : ℝ) := by linarith only [hdnn]
  rw [homErrorEnvelope, Real.sqrt_mul hd]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  calc Real.sqrt (Ch02.HomogenizationErrorOnCube Q t .infinity (.finite 2) A
          (scalarMatrix (d := d) sigma) ^ 2 + 1)
      ≤ Real.sqrt ((1 + Ch02.HomogenizationErrorOnCube Q t .infinity (.finite 2) A
          (scalarMatrix (d := d) sigma)) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = 1 + Ch02.HomogenizationErrorOnCube Q t .infinity (.finite 2) A
          (scalarMatrix (d := d) sigma) := Real.sqrt_sq (by linarith only [hE])

/-! ## 3. The carrier composition: the coarse-graining right-hand side read at the §4.5 data -/

/-- The flux-corrected family's coefficient field on any cube is `ã_{L,k}`. -/
theorem fluxCorrectedCoeffFamily_coeffOn_toCoeffField (M : ABKModel d) (L k : ℤ)
    (Q R : TriadicCube d) (omega : Cutoff.CutoffSample d) :
    ((fluxCorrectedCoeffFamily M L k Q omega).coeffOn R).toCoeffField =
      fluxCorrectedField M L k Q omega :=
  fluxCorrectedRegField_toFun M L k Q omega

/-- The §4.5 Dirichlet solution, entered into `CoarseGraining`'s Dirichlet carrier at the
flux-corrected family `ã_{L,m}` (the field the source's own remark
"the first equation is unchanged if we replace `a_L` by `ã_{L,m}`",
licenses). -/
def homDirichletSolution (M : ABKModel d) (L m : ℤ) (omega : Cutoff.CutoffSample d)
    {u hdat : H1Function (openCubeSet (originCube d m))} {g : Vec d → Vec d}
    (hsol : IsDirichletSolutionOn (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
      (originCube d m) u hdat g) :
    DirichletForcedCubeSolution (originCube d m)
      (fluxCorrectedCoeffFamily M L m (originCube d m) omega) (fun x => -g x) :=
  dirichletForcedCubeSolutionOfIsDirichletSolutionOn
    (A := fluxCorrectedCoeffFamily M L m (originCube d m) omega)
    (u := u) (h := hdat) (g := g)
    (by
      rw [fluxCorrectedCoeffFamily_coeffOn_toCoeffField]
      exact isDirichletSolutionOn_fluxCorrectedField M L m (originCube d m) omega hsol)

/-- The `ν`-drop read at `CoarseGraining`'s price of the entered solution: the left-hand side
of the energy-from-data display. -/
theorem dirichletForcedSolutionEnergyNorm_homDirichletSolution (M : ABKModel d) (L m : ℤ)
    (omega : Cutoff.CutoffSample d) {u hdat : H1Function (openCubeSet (originCube d m))}
    {g : Vec d → Vec d}
    (hsol : IsDirichletSolutionOn (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
      (originCube d m) u hdat g) :
    dirichletForcedSolutionEnergyNorm (originCube d m)
        (fluxCorrectedCoeffFamily M L m (originCube d m) omega)
        (homDirichletSolution M L m omega hsol) =
      Real.sqrt (M.nu : ℝ) *
        Real.sqrt (normalizedSetAverage (openCubeSet (originCube d m))
          (fun y => vecNormSq (u.grad y))) :=
  sqrt_localizedCoeffEnergyValue_fluxCorrectedCoeffFamily M L m (originCube d m)
    (originCube d m) omega (openCubeSet (originCube d m)) u

/-! ## 4. the energy-from-data display -/

/-- The two-term combination step, isolated so the display's association is
visible: each leg is `C · (t-power) · (ellipticity factor) · (data quantity)`,
and only the ellipticity factor is replaced. -/
private theorem homStepTwoCombine {C p1 p2 f1 f2 e1 e2 B1 B2 : ℝ}
    (hC1 : 0 ≤ C * p1) (hC2 : 0 ≤ C * p2) (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2)
    (h1 : f1 ≤ e1) (h2 : f2 ≤ e2) :
    C * p1 * f1 * B1 + C * p2 * f2 * B2 ≤ C * p1 * e1 * B1 + C * p2 * e2 * B2 :=
  add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hC1) hB1)
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hC2) hB2)

/-- **Step 2a — the energy-from-data display.**

For every §4.5 Dirichlet pair `(u, h)` with forcing `g` on `□_m`, every `L`,
every `ω`, and every `t ∈ (0,1)` at which the data are Besov-regular,

```
  ν^{1/2} ‖∇u‖_{L²(□_m)}
    ≤ C t^{-3/2} · σ_m^{-1/2} √(2d) ( 1 + 𝓔_{t/2,∞,2}(□_m; ã_{L,m}, σ_m) ) · B_g
    + C t^{-1/2} · σ_m^{ 1/2} √(2d) ( 1 + 𝓔_{t,∞,2}  (□_m; ã_{L,m}, σ_m) ) · B_h,
```

`C = C(d)` `CoarseGraining`'s dimensional constant of the coarse-graining
right-hand side, `B_g` and `B_h` the note-normalized Besov data quantities.
The association is `(σ^{∓1/2}) · (the `𝓔`-bracket)`; the source writes the
same product as `(1 + 𝓔)(σ^{-1/2}·… + σ^{1/2}·…)`.  See the module docstring
for the three disclosed deviations from the printed display. -/
theorem exists_sqrt_nu_mul_gradL2_le (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (L m : ℤ) (omega : Cutoff.CutoffSample d)
        {u hdat : H1Function (openCubeSet (originCube d m))} {g : Vec d → Vec d} {t : ℝ},
        IsDirichletSolutionOn (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
          (originCube d m) u hdat g →
        0 < t → t < 1 →
        ForceBesovRegularity (originCube d m) t (fun x => -g x) →
        ForceBesovRegularity (originCube d m) t hdat.grad →
          Real.sqrt (M.nu : ℝ) *
              Real.sqrt (normalizedSetAverage (openCubeSet (originCube d m))
                (fun y => vecNormSq (u.grad y))) ≤
            C * Real.rpow t (-(3 / 2 : ℝ)) *
                (Real.sqrt ((Annealed.sigmaBar M m : ℝ))⁻¹ *
                  (Real.sqrt (2 * (d : ℝ)) *
                    (1 + Ch02.HomogenizationErrorOnCube (originCube d m) (t / 2) .infinity
                      (.finite 2) (fluxCorrectedCoeffFamily M L m (originCube d m) omega)
                      (scalarMatrix (d := d) ((Annealed.sigmaBar M m : ℝ)))))) *
                scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d m) t
                  (fun x => -g x)
              + C * Real.rpow t (-(1 / 2 : ℝ)) *
                (Real.sqrt ((Annealed.sigmaBar M m : ℝ)) *
                  (Real.sqrt (2 * (d : ℝ)) *
                    (1 + Ch02.HomogenizationErrorOnCube (originCube d m) t .infinity
                      (.finite 2) (fluxCorrectedCoeffFamily M L m (originCube d m) omega)
                      (scalarMatrix (d := d) ((Annealed.sigmaBar M m : ℝ)))))) *
                scaleNormalizedPositiveBesovVectorNormTwo (originCube d m) t hdat.grad := by
  obtain ⟨C, hCpos, hdir, _hneu⟩ := (energyConsequencesRHSTheory (d := d)).exists_constant
  refine ⟨C, hCpos, ?_⟩
  intro M L m omega u hdat g t hsol ht0 ht1 hgB hhB
  have hsigma : (0 : ℝ) < (Annealed.sigmaBar M m : ℝ) := (Annealed.sigmaBar M m).2
  have ht2 : (0 : ℝ) < t / 2 := by linarith only [ht0]
  have hbd : dirichletBoundaryGradientField (homDirichletSolution M L m omega hsol) =
      hdat.grad := rfl
  have hmain := hdir (homDirichletSolution M L m omega hsol) ht0 ht1 hgB
    (by rw [hbd]; exact hhB)
  rw [dirichletForcedSolutionEnergyNorm_homDirichletSolution M L m omega hsol] at hmain
  refine hmain.trans ?_
  rw [dirichletEnergyWithRHSRHS, hbd]
  have hCt1 : (0 : ℝ) ≤ C * Real.rpow t (-(3 / 2 : ℝ)) :=
    mul_nonneg hCpos.le (Real.rpow_nonneg ht0.le _)
  have hCt2 : (0 : ℝ) ≤ C * Real.rpow t (-(1 / 2 : ℝ)) :=
    mul_nonneg hCpos.le (Real.rpow_nonneg ht0.le _)
  have hBg : (0 : ℝ) ≤ scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d m) t
      (fun x => -g x) :=
    scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity hgB
  have hBh : (0 : ℝ) ≤ scaleNormalizedPositiveBesovVectorNormTwo (originCube d m) t
      hdat.grad := by
    have hsem :=
      scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity hhB
    have hmean : (0 : ℝ) ≤
        Real.sqrt (vecNormSq (cubeAverageVec (originCube d m) hdat.grad)) :=
      Real.sqrt_nonneg _
    rw [scaleNormalizedPositiveBesovVectorNormTwo]
    linarith only [hsem, hmean]
  have hlow : poincareLowerEllipticityFactor (originCube d m)
        (fluxCorrectedCoeffFamily M L m (originCube d m) omega) (t / 2) (.finite 2) ≤
      Real.sqrt ((Annealed.sigmaBar M m : ℝ))⁻¹ *
        (Real.sqrt (2 * (d : ℝ)) *
          (1 + Ch02.HomogenizationErrorOnCube (originCube d m) (t / 2) .infinity (.finite 2)
            (fluxCorrectedCoeffFamily M L m (originCube d m) omega)
            (scalarMatrix (d := d) ((Annealed.sigmaBar M m : ℝ))))) :=
    (poincareLowerEllipticityFactor_le (originCube d m)
      (fluxCorrectedCoeffFamily M L m (originCube d m) omega) ht2 hsigma).trans
      (mul_le_mul_of_nonneg_left
        (homErrorEnvelope_le_one_add (originCube d m)
          (fluxCorrectedCoeffFamily M L m (originCube d m) omega) ht2)
        (Real.sqrt_nonneg _))
  have hupp : poincareUpperEllipticityFactor (originCube d m)
        (fluxCorrectedCoeffFamily M L m (originCube d m) omega) t (.finite 2) ≤
      Real.sqrt ((Annealed.sigmaBar M m : ℝ)) *
        (Real.sqrt (2 * (d : ℝ)) *
          (1 + Ch02.HomogenizationErrorOnCube (originCube d m) t .infinity (.finite 2)
            (fluxCorrectedCoeffFamily M L m (originCube d m) omega)
            (scalarMatrix (d := d) ((Annealed.sigmaBar M m : ℝ))))) :=
    (poincareUpperEllipticityFactor_le (originCube d m)
      (fluxCorrectedCoeffFamily M L m (originCube d m) omega) ht0 hsigma).trans
      (mul_le_mul_of_nonneg_left
        (homErrorEnvelope_le_one_add (originCube d m)
          (fluxCorrectedCoeffFamily M L m (originCube d m) omega) ht0)
        (Real.sqrt_nonneg _))
  exact homStepTwoCombine hCt1 hCt2 hBg hBh hlow hupp

/-! ## 5. The error carrier: `CoarseGraining`'s `𝓔` IS the flux-corrected error -/

/-- The `𝓔` appearing in Step 2a is literally the flux-corrected
error observable's representative (`Support.fluxCorrectedError_characterization`,
plus `isotropicComparatorMatrix σ = scalarMatrix σ` by `rfl`).  Recorded so the
Step-2a display and `EthmB(m)` speak of the same random variable. -/
theorem homogenizationErrorOnCube_scalarMatrix_eq_fluxCorrectedError [NeZero d]
    (M : ABKModel d) (L m : ℤ) (t : ℝ) (omega : Cutoff.CutoffSample d) :
    Ch02.HomogenizationErrorOnCube (originCube d m) t .infinity (.finite 2)
        (fluxCorrectedCoeffFamily M L m (originCube d m) omega)
        (scalarMatrix (d := d) ((Annealed.sigmaBar M m : ℝ))) =
      fluxCorrectedError M L m t omega :=
  (fluxCorrectedError_characterization M L m t omega).symm

end

end Algsuperdiff.Section4.Provider.Homogenization
