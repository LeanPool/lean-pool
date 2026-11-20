/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Global.TorusGlobalVelocityLipschitz
public import LeanPool.FastDynamo.Global.TransverseFundamentalBox

/-!
# The stored derivatives of the global velocity are its classical derivatives

The global velocity of the construction (`eq:global-u`, `lem:global-velocity`) carries two
descriptions of its first derivatives.

* The `W^{1,∞}` bundle `parameterizedFullGlobalW1Inf` stores, for each transverse direction `j`,
  an `L^∞` class whose a.e. representative is the pointwise sum of the descended cell
  derivatives,
  `parameterizedHelicalGlobalRealTorusFirstDerivative j + axialOffsetGlobalTorusDerivative j`
  (`transverseW1InfDeriv_parameterizedFullGlobalW1Inf_coe_ae`).
* The periodised chart field `parameterizedFullGlobalPeriodizedRealSource : ℝ × ℝ → R3` is
  differentiable at every point of the plane
  (`differentiable_parameterizedFullGlobalPeriodizedRealSource`),
  with its classical Fréchet derivative.

This module identifies the two.  The identity holds at **every** point of the plane, not only
almost everywhere: after reduction to the fundamental box `(0,1]²` by periodicity, a point either
lies in the buffer disc of a single cell, where the periodised field is that cell and the stored
derivative is the descended cell derivative, or it lies in no buffer disc, where both sides
vanish (at the accumulation point by the quadratic flatness of the field, elsewhere because the
field is locally a finite sum of cells all of whose derivatives vanish there).

Consequences:

* `transverseW1InfDeriv_parameterizedFullGlobalW1Inf_ae_eq_fderiv`: the stored derivative classes
  are the classical derivatives of the periodised field, almost everywhere on `(0,1]²`;
* `fderiv_parameterizedFullGlobalPeriodizedRealSource_transverseDivergence`: the classical
  derivative of the periodised field is transversally divergence free at every point of the
  plane, `∂₁u₁ + ∂₂u₂ = 0` (the paper's `Div u = 0` of `lem:global-velocity`, pointwise).
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace ScaleFamily.TorusCellPlacement

variable {p : LocalSeedParameters} {r : ScaleRatios p}

namespace FullVelocityConcrete

open UnitBoxPeriodization EuclideanCellSourceCertificate

variable (h : PonomarenkoSmoothingWidth)
variable (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
variable (angularSpeed axialSpeed tau : ℝ)

/-- At a point lying in no buffer disc the derivative of the chart-side global velocity vanishes:
at the accumulation point by quadratic flatness, elsewhere because near the point the field is a
finite sum of cells, each of whose coordinate derivatives vanishes off its own buffer disc. -/
theorem fderiv_parameterizedFullGlobalEuclideanRealSource_eq_zero_of_outside_buffers
    (htau : 0 ≤ tau) {x : ℝ × ℝ} (hx : ∀ n : ℕ, x ∉ P.scaleFamily.bufferDisk n) :
    fderiv ℝ (parameterizedFullGlobalEuclideanRealSource h P angularSpeed axialSpeed tau) x =
      0 := by
  by_cases hacc : x = accumulationPoint
  · subst hacc
    exact fderiv_parameterizedFullGlobalEuclideanRealSource_accumulationPoint
      h P angularSpeed axialSpeed tau htau
  · obtain ⟨N, heq⟩ :=
      exists_eventuallyEq_finsetSum_of_ne_accumulationPoint
        h P angularSpeed axialSpeed tau hacc
    have hsum : HasFDerivAt
        (fun y ↦ ∑ n ∈ Finset.range N,
          parameterizedFullEuclideanCellRealSource h P angularSpeed axialSpeed tau n y)
        (∑ n ∈ Finset.range N,
          fderiv ℝ (parameterizedFullEuclideanCellRealSource
            h P angularSpeed axialSpeed tau n) x) x :=
      HasFDerivAt.fun_sum fun n _ ↦
        ((differentiable_parameterizedFullEuclideanCellRealSource
          h P angularSpeed axialSpeed tau n) x).hasFDerivAt
    have hcellzero : ∀ n ∈ Finset.range N,
        fderiv ℝ (parameterizedFullEuclideanCellRealSource
          h P angularSpeed axialSpeed tau n) x = 0 := by
      intro n _
      refine continuousLinearMap_eq_zero_pairBasis ?_ ?_ <;>
        · rw [fderiv_parameterizedFullEuclideanCellRealSource_apply_pairBasis]
          exact parameterizedFullEuclideanCellRealSourceDeriv_eq_zero_of_not_mem_bufferDisk
            h P angularSpeed axialSpeed tau n _ (hx n)
    rw [(hsum.congr_of_eventuallyEq heq).fderiv, Finset.sum_eq_zero hcellzero]

/-- **The classical derivative of the periodised global velocity is the stored cell
derivative**, at every point of the plane: the derivative of
`parameterizedFullGlobalPeriodizedRealSource` in the direction `pairBasis j` is the sum of the
descended helical and axial cell derivatives at the image point on the transverse torus. -/
theorem fderiv_parameterizedFullGlobalPeriodizedRealSource_apply_pairBasis (htau : 0 ≤ tau)
    (j : Fin 2) (x : ℝ × ℝ) :
    fderiv ℝ (parameterizedFullGlobalPeriodizedRealSource h P angularSpeed axialSpeed tau) x
        (pairBasis j) =
      parameterizedHelicalGlobalRealTorusFirstDerivative h P angularSpeed axialSpeed j
          (transverseTorusPoint x) +
        P.axialOffsetGlobalTorusDerivative tau j (transverseTorusPoint x) := by
  obtain ⟨m, hm⟩ := LatticePeriodic.exists_int_sub_mem_Ioc x.1
  obtain ⟨n, hn⟩ := LatticePeriodic.exists_int_sub_mem_Ioc x.2
  set c : ℝ × ℝ := ((m : ℝ), (n : ℝ))
  set z : ℝ × ℝ := x - c
  have hz1 : z.1 ∈ Set.Ioc (0 : ℝ) (0 + 1) := by
    rw [zero_add]
    exact hm
  have hz2 : z.2 ∈ Set.Ioc (0 : ℝ) (0 + 1) := by
    rw [zero_add]
    exact hn
  have hshift : (fun y ↦ parameterizedFullGlobalPeriodizedRealSource
      h P angularSpeed axialSpeed tau (y - c)) =
      parameterizedFullGlobalPeriodizedRealSource h P angularSpeed axialSpeed tau :=
    funext fun y ↦ (isLatticePeriodic_parameterizedFullGlobalPeriodizedRealSource
      h P angularSpeed axialSpeed tau).sub_int y m n
  have hderiv : fderiv ℝ (parameterizedFullGlobalPeriodizedRealSource
      h P angularSpeed axialSpeed tau) x =
      fderiv ℝ (parameterizedFullGlobalPeriodizedRealSource
        h P angularSpeed axialSpeed tau) z := by
    conv_lhs => rw [← hshift]
    exact fderiv_comp_sub c
  have hq : transverseTorusPoint x = transverseTorusPoint z :=
    (transverseTorusPoint_sub_int x m n).symm
  have hrep : transverseIocRepresentative (transverseTorusPoint z) = z :=
    transverseIocRepresentative_transverseTorusPoint_of_mem_Ioc hz1 hz2
  rw [hderiv, hq]
  by_cases hbuffer : ∃ k : ℕ, z ∈ P.scaleFamily.bufferDisk k
  · obtain ⟨k, hk⟩ := hbuffer
    have hloc : parameterizedFullGlobalPeriodizedRealSource h P angularSpeed axialSpeed tau
        =ᶠ[𝓝 z] parameterizedFullGlobalEuclideanRealSource h P angularSpeed axialSpeed tau := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hk] with y hy
      obtain ⟨h1, h2⟩ := P.bufferDisk_subset_chart k hy
      rw [Set.mem_Ioo] at h1 h2
      exact parameterizedFullGlobalPeriodizedRealSource_eq_of_mem_Ioc
        h P angularSpeed axialSpeed tau ⟨h1.1, by linarith⟩ ⟨by linarith, by linarith⟩
    have hqk : transverseTorusPoint z ∈ P.torusBufferDisk k := by
      rw [P.mem_torusBufferDisk_iff_transverseIocRepresentative, hrep]
      exact hk
    rw [hloc.fderiv_eq,
      fderiv_parameterizedFullGlobalEuclideanRealSource_eq_cell_of_mem_bufferDisk
        h P angularSpeed axialSpeed tau hk,
      fderiv_parameterizedFullEuclideanCellRealSource_apply_pairBasis,
      parameterizedHelicalGlobalRealTorusFirstDerivative,
      parameterizedHelicalGlobalTorusFirstDerivative_eq_cell_of_mem_buffer
        h P angularSpeed axialSpeed hqk j,
      torusFirstDerivative_transverseTorusPoint_eq_firstDerivative_of_mem_Ioc
        (parameterizedHelicalEuclideanCellCertificate h P angularSpeed axialSpeed k) j hz1 hz2,
      P.axialOffsetGlobalTorusDerivative_eq_cell_of_mem_buffer tau hqk j,
      axialOffsetTorusDerivative,
      torusPeriodizedExtension_transverseTorusPoint_of_mem_Ioc P k _
        (fun _ hy ↦ P.axialOffsetEuclideanDerivative_eq_zero_of_not_mem_bufferDisk tau k j hy)
        hz1 hz2]
    rfl
  · push Not at hbuffer
    have hqout : ∀ k : ℕ, transverseTorusPoint z ∉ P.torusBufferDisk k := by
      intro k hk
      rw [P.mem_torusBufferDisk_iff_transverseIocRepresentative, hrep] at hk
      exact hbuffer k hk
    set k := localTranslationIndex z
    have hloc : parameterizedFullGlobalPeriodizedRealSource h P angularSpeed axialSpeed tau
        =ᶠ[𝓝 z] fun y ↦ parameterizedFullGlobalEuclideanRealSource
          h P angularSpeed axialSpeed tau (y - ((k.1 : ℝ), (k.2 : ℝ))) :=
      eventuallyEq_translate
        (supportedInPlacementChart_parameterizedFullGlobalEuclideanRealSource
          h P angularSpeed axialSpeed tau) z
    have hout : ∀ i : ℕ, z - ((k.1 : ℝ), (k.2 : ℝ)) ∉ P.scaleFamily.bufferDisk i := by
      intro i hi
      obtain ⟨h1, h2⟩ := P.bufferDisk_subset_chart i hi
      simp only [Prod.fst_sub, Prod.snd_sub, Set.mem_Ioo] at h1 h2
      rw [zero_add, Set.mem_Ioc] at hz1 hz2
      have hk1lt : ((k.1 : ℤ) : ℝ) < 1 := by linarith
      have hk1gt : ((-1 : ℤ) : ℝ) < ((k.1 : ℤ) : ℝ) := by
        push_cast
        linarith
      have hk2lt : ((k.2 : ℤ) : ℝ) < 1 := by linarith
      have hk2gt : ((-1 : ℤ) : ℝ) < ((k.2 : ℤ) : ℝ) := by
        push_cast
        linarith
      have hk1lt' : k.1 < 1 := by exact_mod_cast hk1lt
      have hk1gt' : (-1 : ℤ) < k.1 := by exact_mod_cast hk1gt
      have hk2lt' : k.2 < 1 := by exact_mod_cast hk2lt
      have hk2gt' : (-1 : ℤ) < k.2 := by exact_mod_cast hk2gt
      have hk10 : k.1 = 0 := by omega
      have hk20 : k.2 = 0 := by omega
      have hzero : z - ((k.1 : ℝ), (k.2 : ℝ)) = z := by
        rw [hk10, hk20]
        refine Prod.ext ?_ ?_ <;> simp
      exact hbuffer i (hzero ▸ hi)
    rw [hloc.fderiv_eq, fderiv_comp_sub,
      fderiv_parameterizedFullGlobalEuclideanRealSource_eq_zero_of_outside_buffers
        h P angularSpeed axialSpeed tau htau hout,
      parameterizedHelicalGlobalRealTorusFirstDerivative,
      parameterizedHelicalGlobalTorusFirstDerivative_eq_zero_of_outside_buffers
        h P angularSpeed axialSpeed hqout j,
      P.axialOffsetGlobalTorusDerivative_eq_zero_of_outside_buffers tau hqout j]
    ext i
    simp

/-- **The stored `W^{1,∞}` derivatives of the global velocity are its classical derivatives.**
For almost every point `x` of the fundamental box `(0,1]²`, the `j`-th stored derivative class of
`parameterizedFullGlobalW1Inf`, read at the image of `x` on the transverse torus, is the classical
derivative of the periodised velocity at `x` in the direction `pairBasis j`. -/
theorem transverseW1InfDeriv_parameterizedFullGlobalW1Inf_ae_eq_fderiv (htau : 0 ≤ tau)
    (j : Fin 2) :
    ∀ᵐ x : ℝ × ℝ, x ∈ pairUnitIocBox →
      (transverseW1InfDeriv j (parameterizedFullGlobalW1Inf
          h P angularSpeed axialSpeed tau htau) : TransverseTorus → R3)
          (transverseTorusPoint x) =
        fderiv ℝ (parameterizedFullGlobalPeriodizedRealSource h P angularSpeed axialSpeed tau) x
          (pairBasis j) := by
  have hpull := measurePreserving_transverseTorusPoint.quasiMeasurePreserving.ae_eq_comp
    (transverseW1InfDeriv_parameterizedFullGlobalW1Inf_coe_ae
      h P angularSpeed axialSpeed tau htau j)
  rw [EventuallyEq, ae_restrict_iff' measurableSet_pairUnitIocBox] at hpull
  filter_upwards [hpull] with x hx hbox
  rw [fderiv_parameterizedFullGlobalPeriodizedRealSource_apply_pairBasis
      h P angularSpeed axialSpeed tau htau j x]
  exact hx hbox

/-- **The periodised global velocity is transversally divergence free at every point**:
`∂₁u₁ + ∂₂u₂ = 0` for its classical derivative.  This is the paper's `Div u = 0`
(`lem:global-velocity`) for the transverse field, holding pointwise everywhere on the plane. -/
theorem fderiv_parameterizedFullGlobalPeriodizedRealSource_transverseDivergence (htau : 0 ≤ tau)
    (x : ℝ × ℝ) :
    fderiv ℝ (parameterizedFullGlobalPeriodizedRealSource h P angularSpeed axialSpeed tau) x
        (pairBasis 0) 0 +
      fderiv ℝ (parameterizedFullGlobalPeriodizedRealSource h P angularSpeed axialSpeed tau) x
        (pairBasis 1) 1 = 0 := by
  rw [fderiv_parameterizedFullGlobalPeriodizedRealSource_apply_pairBasis
      h P angularSpeed axialSpeed tau htau 0 x,
    fderiv_parameterizedFullGlobalPeriodizedRealSource_apply_pairBasis
      h P angularSpeed axialSpeed tau htau 1 x]
  have hhel := congrArg Complex.re
    (parameterizedHelicalGlobalTorusFirstDerivative_transverseDivergence
      h P angularSpeed axialSpeed (transverseTorusPoint x))
  have hax := P.axialOffsetGlobalTorusDerivative_transverseDivergence tau (transverseTorusPoint x)
  rw [Complex.add_re, Complex.zero_re] at hhel
  simp only [PiLp.add_apply, parameterizedHelicalGlobalRealTorusFirstDerivative, vecRe_apply]
  linarith

end FullVelocityConcrete

end ScaleFamily.TorusCellPlacement

end

end FastDynamo
