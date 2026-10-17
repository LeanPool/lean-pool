/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationOverlapTransfer
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationOscillationGridMoment
public import LeanPool.HighContrastHomogenization.Support.Book.Ch01.Theorems.MeanSquareDeviation

/-!
# LocalizationEnvelopeMesh

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
NOTE: this module is an ordinary Provider helper / conditional A.  The binder
descriptions below are an informal inventory only.

# Provider: the meso-window energy primitives, on a small cone

Source displays in ABK26:

* `e.lower.bound.oscillations` (label; display);
* `e.nablaw.oscillations` (label; display, claim opened);
* `e.nablaw.in.L.eight` (label; display).

## Why this module exists

The window energy `‖grad w‖_{L2bar(z + cu_{m-h})}` that `e.nablaw.oscillations`
puts on its right-hand side is a *low-level* quantity: a normalized `L^2`
deviation on one translated triadic cube.  In the development it was first
written down inside `LocalizationOscillationDisplay`, a module that also
carries the whole assembly and therefore drags in the nested Campanato tower,
the harmonic-approximation layer and the shell-derivative gauge.  Any consumer
that needs only the low-level quantity pays for all of it.

This module re-states the three low-level carriers from first principles on the
CoarseGraining cube/`volumeAverage` A, and re-derives the covering discharge on
top of them, so that the discharge sits on a cone consisting of exactly
`LocalizationGrid`, `Corrector.OscillationCubeFamily`,
`LocalizationOverlapCount`, `LocalizationOverlapTransfer`,
`LocalizationOscillationTail` and `LocalizationOscillationGridMoment`.

The carriers are *definitionally equal* to the ones in
`LocalizationOscillationDisplay` and `LocalizationOverlapCoarse`
(`mesoWindowEnergy = meshEnergyCell`, `mesoWindowFourthEnergy =
meshFourthEnergyCell`, `originCubeFourthEnergy = cubeFourthEnergy`, each by
`rfl`); the equalities are recorded in the separate bridge module, which is the
only place where the large cone is paid for.

## What is proved

* `mesoWindowEnergy`, `mesoWindowFourthEnergy`, `originCubeFourthEnergy` -- the
  window energy `‖u‖_{L2bar(z+cu_ell)}`, the window fourth energy
  `fint_{z+cu_ell} |u|^4`, and the global fourth energy `fint_{cu_K} |u|^4`,
  the last two written with CoarseGraining's `vecNormSq` so that
  `originCubeFourthEnergy K u` is exactly `‖u‖_{L4bar(cu_K)}^4` in the
  manuscript's normalization.
* `mesoWindowEnergy_rpow_four_le` -- the per-window Jensen step
  `‖u‖^4_{L2bar(W)} <= fint_W |u|^4`, with constant `1`.
* `gridFourthMoment_mesoWindowEnergy_le` -- **the covering discharge.**  The
  grid fourth moment of the window energies over the interior meso grid is at
  most `3^d` times the annealed global fourth energy on `cu_K`.  The overlap
  multiplicity `3^{dN}` of `LocalizationOverlapCount` cancels *exactly* against
  the window volume; the surviving `3^d` is the interior-grid deficit of
  `card_mesoCubeGrid_le_three_pow_mul_card_interior`.  Restating it with the
  amplitude `(3^d E)^{1/4}`, in the shape a display binder has, is left to the
  consumer.

## What is NOT proved here

* **The envelope is still a binder in this module.**  `henv` asks for
  `int_Omega fint_{cu_K} |u|^4 <= E`; deriving it from the manuscript's
  `e.nablaw.in.L.eight` is the business of the companion modules
  `LocalizationEnvelopeSpatial`, `LocalizationEnvelopeMoment` and
  `LocalizationEnvelopeHenv`, and is not attempted below.
* **No integrability or measurability side condition is discharged.**  Fourth
  power integrability on `cu_K` in space, and integrability in the sample of
  the window and global fourth energies, are binders.

## Divergences from the printed statement

* **The Jensen step is at `p = 2`, not Minkowski.**  `‖u‖^4_{L2bar(W)}` is
  bounded by `fint_W |u|^4` with constant `1`; this is normalized
  Cauchy--Schwarz and no constant is lost.

## References

* ABK26, `e.lower.bound.oscillations`; `e.nablaw.oscillations`;
  `e.nablaw.in.L.eight`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open MeasureTheory
open HCPolySupport HCPolySupport.Book.Ch03

noncomputable section

variable {d : ℕ}

/-! ## The three low-level carriers -/

/-- The window energy of `e.nablaw.oscillations`: the normalized `L^2` size of
`u` on the meso window `z + cu_ell` based at the site `z = triadicCubeShift R`,
i.e. `‖u‖_{L2bar(z+cu_ell)}`.

This is definitionally `LocalizationOscillationDisplay.meshEnergyCell`. -/
def mesoWindowEnergy (ell : ℤ) (u : Vec d → Vec d) (R : TriadicCube d) : ℝ :=
  Real.sqrt (Book.Ch01.meanSquareDeviationVecOn
    (openCubeAtScale (triadicCubeShift R) ell) u 0)

/-- The normalized fourth energy of `u` on the meso window `z + cu_ell`:
`fint_{z+cu_ell} |u|^4`.

This is definitionally `LocalizationOverlapCoarse.meshFourthEnergyCell`. -/
def mesoWindowFourthEnergy (ell : ℤ) (u : Vec d → Vec d) (R : TriadicCube d) : ℝ :=
  volumeAverage (openCubeAtScale (triadicCubeShift R) ell) fun x => vecNormSq (u x) ^ 2

/-- The normalized fourth energy of `u` on `cu_K`: `fint_{cu_K} |u|^4`, i.e.
`‖u‖_{L4bar(cu_K)}^4` in the manuscript's normalization.

This is definitionally `LocalizationOverlapCoarse.cubeFourthEnergy`. -/
def originCubeFourthEnergy (K : ℤ) (u : Vec d → Vec d) : ℝ :=
  volumeAverage (openCubeSet (originCube d K)) fun x => vecNormSq (u x) ^ 2

/-- Unconditional: the window fourth energy is nonnegative. -/
theorem mesoWindowFourthEnergy_nonneg (ell : ℤ) (u : Vec d → Vec d)
    (R : TriadicCube d) : 0 ≤ mesoWindowFourthEnergy ell u R :=
  volumeAverage_nonneg_of_nonneg_on (measurableSet_openCubeAtScale _ _)
    fun _ _ => sq_nonneg _

/-- Unconditional: the global fourth energy is nonnegative. -/
theorem originCubeFourthEnergy_nonneg (K : ℤ) (u : Vec d → Vec d) :
    0 ≤ originCubeFourthEnergy K u :=
  volumeAverage_nonneg_of_nonneg_on (measurableSet_openCubeSet _) fun _ _ => sq_nonneg _

/-! ## Cauchy--Schwarz against the constant, re-derived -/

/-- Cauchy--Schwarz against `1` on a finite-measure set:
`(int_V g)^2 <= |V| int_V g^2`.

: the caller supplies `hfin : volume V ≠ ⊤`, `hpos : 0 < (volume V).toReal`,
and the two integrability hypotheses `hg`, `hg2`. -/
theorem sq_setIntegral_le_volume_mul_setIntegral_sq {V : Set (Vec d)}
    (hfin : volume V ≠ ⊤) (hpos : 0 < (volume V).toReal) {g : Vec d → ℝ}
    (hg : IntegrableOn g V volume) (hg2 : IntegrableOn (fun x => g x ^ 2) V volume) :
    (∫ x in V, g x ∂volume) ^ 2 ≤
      (volume V).toReal * ∫ x in V, g x ^ 2 ∂volume := by
  set m : ℝ := (volume V).toReal with hmdef
  set I : ℝ := ∫ x in V, g x ∂volume with hIdef
  set J : ℝ := ∫ x in V, g x ^ 2 ∂volume with hJdef
  set t : ℝ := I / m with htdef
  have hmne : m ≠ 0 := ne_of_gt hpos
  have hconst : IntegrableOn (fun _ : Vec d => t ^ 2) V volume := integrableOn_const hfin
  have hexp : (fun x => (g x - t) ^ 2)
      = fun x => g x ^ 2 + (-(2 * t) * g x + t ^ 2) := by
    funext x
    ring
  have hint2 : IntegrableOn (fun x => -(2 * t) * g x + t ^ 2) V volume :=
    (hg.const_mul (-(2 * t))).add hconst
  have hcalc : ∫ x in V, (g x - t) ^ 2 ∂volume = J + (-(2 * t) * I + t ^ 2 * m) := by
    rw [hexp, integral_add hg2 hint2, integral_add (hg.const_mul (-(2 * t))) hconst,
      integral_const_mul, setIntegral_const, measureReal_def, smul_eq_mul]
    ring
  have hnn : (0 : ℝ) ≤ ∫ x in V, (g x - t) ^ 2 ∂volume :=
    integral_nonneg fun _ => sq_nonneg _
  rw [hcalc] at hnn
  have ht : t * m = I := by
    rw [htdef]
    field_simp
  have hexpand : m * (J + (-(2 * t) * I + t ^ 2 * m)) = m * J - I ^ 2 := by
    linear_combination (t * m - I) * ht
  have hmul : (0 : ℝ) ≤ m * (J + (-(2 * t) * I + t ^ 2 * m)) := mul_nonneg hpos.le hnn
  rw [hexpand] at hmul
  linarith

/-- Normalized Cauchy--Schwarz on a meso window: the square of the window
average is at most the window average of the square.

: the caller supplies the two integrability hypotheses `hg`, `hg2` on the
window. -/
private theorem sq_volumeAverage_le_volumeAverage_sq_openCubeAtScale (z : Vec d) (m : ℤ)
    {g : Vec d → ℝ}
    (hg : IntegrableOn g (openCubeAtScale z m) volume)
    (hg2 : IntegrableOn (fun x => g x ^ 2) (openCubeAtScale z m) volume) :
    volumeAverage (openCubeAtScale z m) g ^ 2 ≤
      volumeAverage (openCubeAtScale z m) fun x => g x ^ 2 := by
  have hfin := Corrector.volume_openCubeAtScale_ne_top z m
  have hpos := Corrector.volume_openCubeAtScale_toReal_pos z m
  have hcs := sq_setIntegral_le_volume_mul_setIntegral_sq hfin hpos hg hg2
  change ((volume (openCubeAtScale z m)).toReal⁻¹ *
      ∫ x in openCubeAtScale z m, g x ∂volume) ^ 2 ≤
    (volume (openCubeAtScale z m)).toReal⁻¹ *
      ∫ x in openCubeAtScale z m, g x ^ 2 ∂volume
  rw [mul_pow]
  calc ((volume (openCubeAtScale z m)).toReal⁻¹) ^ 2 *
        (∫ x in openCubeAtScale z m, g x ∂volume) ^ 2
      ≤ ((volume (openCubeAtScale z m)).toReal⁻¹) ^ 2 *
          ((volume (openCubeAtScale z m)).toReal *
            ∫ x in openCubeAtScale z m, g x ^ 2 ∂volume) :=
        mul_le_mul_of_nonneg_left hcs (by positivity)
    _ = (volume (openCubeAtScale z m)).toReal⁻¹ *
          ∫ x in openCubeAtScale z m, g x ^ 2 ∂volume := by field_simp

/-! ## The per-window Jensen step -/

/-- **The per-window Jensen step.**  The fourth power of the window energy
`‖u‖_{L2bar(z+cu_ell)}` is at most the window's normalized fourth energy.  The
constant is `1`.

: the caller supplies `hcoord`, integrability on the window of the coordinate
squares of `u`; `hsq`, integrability on the window of `|u|^2 = vecNormSq o u`;
and `hfour`, integrability on the window of `|u|^4 = (vecNormSq o u)^2`.  No
other hypothesis is used. -/
theorem mesoWindowEnergy_rpow_four_le (ell : ℤ) (u : Vec d → Vec d) (R : TriadicCube d)
    (hcoord : ∀ k : Fin d, IntegrableOn (fun x => (u x k) ^ 2)
      (openCubeAtScale (triadicCubeShift R) ell) volume)
    (hsq : IntegrableOn (fun x => vecNormSq (u x))
      (openCubeAtScale (triadicCubeShift R) ell) volume)
    (hfour : IntegrableOn (fun x => vecNormSq (u x) ^ 2)
      (openCubeAtScale (triadicCubeShift R) ell) volume) :
    mesoWindowEnergy ell u R ^ (4 : ℝ) ≤ mesoWindowFourthEnergy ell u R := by
  set V : Set (Vec d) := openCubeAtScale (triadicCubeShift R) ell with hV
  have hint : ∀ k : Fin d,
      IntegrableOn (fun x => (u x k - (0 : Vec d) k) ^ 2) V volume := by
    intro k
    simpa using hcoord k
  have hmsd : Book.Ch01.meanSquareDeviationVecOn V u 0 =
      volumeAverage V fun x => vecNormSq (u x) := by
    rw [Book.Ch01.meanSquareDeviationVecOn_eq_volumeAverage_vecNormSq_sub hint]
    simp
  have hnn : 0 ≤ Book.Ch01.meanSquareDeviationVecOn V u 0 := by
    rw [hmsd]
    exact volumeAverage_nonneg_of_nonneg_on (measurableSet_openCubeAtScale _ _)
      fun x _ => vecNormSq_nonneg _
  have hpow : mesoWindowEnergy ell u R ^ (4 : ℝ) =
      (Book.Ch01.meanSquareDeviationVecOn V u 0) ^ 2 := by
    rw [mesoWindowEnergy, rpow_four_eq_pow_four,
      show Real.sqrt (Book.Ch01.meanSquareDeviationVecOn V u 0) ^ (4 : ℕ) =
        (Real.sqrt (Book.Ch01.meanSquareDeviationVecOn V u 0) ^ 2) ^ 2 by ring,
      Real.sq_sqrt hnn]
  rw [hpow, hmsd, mesoWindowFourthEnergy]
  exact sq_volumeAverage_le_volumeAverage_sq_openCubeAtScale _ _ hsq hfour

/-! ## The window containment supplied by the interior grid -/

/-- Unconditional: membership in the interior grid at outer scale `n + N - 1` is
exactly the containment `z + cu_{n+N} subset cu_K` printed. -/
theorem openCubeAtScale_subset_openCubeSet_of_mem_interiorMesoCubeGrid {K n : ℤ} {N : ℕ}
    {R : TriadicCube d} (hR : R ∈ interiorMesoCubeGrid d K n (n + (N : ℤ) - 1)) :
    openCubeAtScale (triadicCubeShift R) (n + (N : ℤ)) ⊆ openCubeSet (originCube d K) := by
  have h := window_subset_of_mem_interiorMesoCubeGrid hR
  rw [show (n + (N : ℤ) - 1) + 1 = n + (N : ℤ) by ring] at h
  rwa [openCubeAtScale_eq_translateSet, openCubeAtScale_zero_eq_openCubeSet_originCube]

/-! ## The covering discharge -/

/-- **The meso-window energy average, from the global fourth energy.**

This is the manuscript's step "by `e.nablaw.in.L.eight`", made explicit: the
grid fourth moment of the window energies over the interior meso grid is at
most `3^d` times the annealed global fourth energy on `cu_K`.

The overlap multiplicity `3^{dN}` of `LocalizationOverlapCount` cancels
*exactly* against the window volume; the surviving `3^d` is the interior-grid
deficit of `card_mesoCubeGrid_le_three_pow_mul_card_interior`.

Complete binder census, beyond the typing binders `d, Omega, inst, mu, K, n, N,
u, E`:

* `hn : n <= K - 1` -- interior-grid scale gate;
* `hN : n + N <= K - 1` -- interior-grid outer scale gate;
* `hcoord` -- integrability on `cu_K`, for every sample, of the coordinate
  squares of `u omega`;
* `hsq` -- integrability on `cu_K`, for every sample, of `|u omega|^2`;
* `hfour` -- integrability on `cu_K`, for every sample, of `|u omega|^4`;
* `hcellInt` -- integrability in the sample of the window fourth energy, for
  every cube of the interior grid;
* `hglobInt` -- integrability in the sample of the global fourth energy;
* `henv` -- the envelope `int_Omega fint_{cu_K} |u|^4 dmu <= E`.

None of them is discharged here.  No measurability of `u` in the sample is
assumed, and none is used: every sample-space statement above is an
`Integrable` hypothesis supplied by the caller. -/
theorem gridFourthMoment_mesoWindowEnergy_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {K n : ℤ} {N : ℕ} (hn : n ≤ K - 1) (hN : n + (N : ℤ) ≤ K - 1)
    (u : Ω → Vec d → Vec d) {E : ℝ}
    (hcoord : ∀ (ω : Ω) (k : Fin d), IntegrableOn (fun x => (u ω x k) ^ 2)
      (openCubeSet (originCube d K)) volume)
    (hsq : ∀ ω, IntegrableOn (fun x => vecNormSq (u ω x))
      (openCubeSet (originCube d K)) volume)
    (hfour : ∀ ω, IntegrableOn (fun x => vecNormSq (u ω x) ^ 2)
      (openCubeSet (originCube d K)) volume)
    (hcellInt : ∀ R ∈ interiorMesoCubeGrid d K n (n + (N : ℤ) - 1),
      Integrable (fun ω => mesoWindowFourthEnergy (n + (N : ℤ)) (u ω) R) μ)
    (hglobInt : Integrable (fun ω => originCubeFourthEnergy K (u ω)) μ)
    (henv : ∫ ω, originCubeFourthEnergy K (u ω) ∂μ ≤ E) :
    gridFourthMoment μ (interiorMesoCubeGrid d K n (n + (N : ℤ) - 1))
        (fun R ω => mesoWindowEnergy (n + (N : ℤ)) (u ω) R) ≤ (3 : ℝ) ^ d * E := by
  classical
  have hwin : ∀ R ∈ interiorMesoCubeGrid d K n (n + (N : ℤ) - 1),
      openCubeAtScale (triadicCubeShift R) (n + (N : ℤ)) ⊆
        openCubeSet (originCube d K) := fun _ hR =>
    openCubeAtScale_subset_openCubeSet_of_mem_interiorMesoCubeGrid hR
  have hcube : ∀ R ∈ interiorMesoCubeGrid d K n (n + (N : ℤ) - 1),
      (∫ ω, mesoWindowEnergy (n + (N : ℤ)) (u ω) R ^ (4 : ℝ) ∂μ) ≤
        ∫ ω, mesoWindowFourthEnergy (n + (N : ℤ)) (u ω) R ∂μ := by
    intro R hR
    refine integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun ω => rpow_four_nonneg _) (hcellInt R hR)
      (Filter.Eventually.of_forall fun ω => ?_)
    exact mesoWindowEnergy_rpow_four_le _ _ _
      (fun k => (hcoord ω k).mono_set (hwin R hR))
      ((hsq ω).mono_set (hwin R hR)) ((hfour ω).mono_set (hwin R hR))
  have hswap : cubeFamilyAverage (interiorMesoCubeGrid d K n (n + (N : ℤ) - 1))
        (fun R => ∫ ω, mesoWindowFourthEnergy (n + (N : ℤ)) (u ω) R ∂μ) =
      ∫ ω, cubeFamilyAverage (interiorMesoCubeGrid d K n (n + (N : ℤ) - 1))
        (fun R => mesoWindowFourthEnergy (n + (N : ℤ)) (u ω) R) ∂μ := by
    unfold cubeFamilyAverage
    rw [← integral_finsetSum _ hcellInt, ← integral_const_mul]
  have hptw : ∀ ω, cubeFamilyAverage (interiorMesoCubeGrid d K n (n + (N : ℤ) - 1))
      (fun R => mesoWindowFourthEnergy (n + (N : ℤ)) (u ω) R) ≤
        (3 : ℝ) ^ d * originCubeFourthEnergy K (u ω) := fun ω =>
    cubeFamilyAverage_volumeAverage_openCubeAtScale_interior_le hn hN (hfour ω)
      fun _ => sq_nonneg _
  have hint1 : Integrable (fun ω => cubeFamilyAverage
      (interiorMesoCubeGrid d K n (n + (N : ℤ) - 1))
      (fun R => mesoWindowFourthEnergy (n + (N : ℤ)) (u ω) R)) μ := by
    unfold cubeFamilyAverage
    exact (integrable_finsetSum _ hcellInt).const_mul _
  calc gridFourthMoment μ (interiorMesoCubeGrid d K n (n + (N : ℤ) - 1))
        (fun R ω => mesoWindowEnergy (n + (N : ℤ)) (u ω) R)
      ≤ cubeFamilyAverage (interiorMesoCubeGrid d K n (n + (N : ℤ) - 1))
          (fun R => ∫ ω, mesoWindowFourthEnergy (n + (N : ℤ)) (u ω) R ∂μ) :=
        cubeFamilyAverage_mono hcube
    _ = ∫ ω, cubeFamilyAverage (interiorMesoCubeGrid d K n (n + (N : ℤ) - 1))
          (fun R => mesoWindowFourthEnergy (n + (N : ℤ)) (u ω) R) ∂μ := hswap
    _ ≤ ∫ ω, (3 : ℝ) ^ d * originCubeFourthEnergy K (u ω) ∂μ :=
        integral_mono hint1 (hglobInt.const_mul _) hptw
    _ = (3 : ℝ) ^ d * ∫ ω, originCubeFourthEnergy K (u ω) ∂μ := integral_const_mul _ _
    _ ≤ (3 : ℝ) ^ d * E := mul_le_mul_of_nonneg_left henv (by positivity)

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
