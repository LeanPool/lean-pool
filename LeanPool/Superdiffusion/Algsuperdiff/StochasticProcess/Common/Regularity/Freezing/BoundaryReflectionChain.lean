/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Freezing.BoundaryOddPairing
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Freezing.BoundaryReflectedCoeff
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.HarmonicityTransferFace
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.SectorReflectionGeometry
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepPartialReflection

/-!
# BoundaryReflectionChain

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Unfolding a sector weak solution into the full ball

A divergence-form weak solution on a Euclidean ball sector whose values vanish
on the flat faces extends oddly, one face at a time, to the whole centred ball.
At each unfolding step the coefficient is conjugated by the coordinate sign
flip and the scalar source is extended oddly, so the small-contrast bound is
preserved and the source only doubles.  The chain records the resulting weak
equation together with the pointwise oddness and the pinning to the original
sector datum.

The same induction over the same sector geometry, with the same four invariants,
appears once more for the Laplacian in
`Regularity/SectorReflectionHarmonic.lean`.  Harmonicity is the special case
`a = 1`, `g = 0` of the equation unfolded here, so the harmonic chain is an
instance of this one; it is kept separate only because it additionally exports
gradient-level reflection symmetry to the sector energy comparison.  Once the
sector Campanato route no longer needs that export, the harmonic chain should be
re-derived from this one behind a single equivalence between the harmonic
predicate and its divergence-form reading.
-/

namespace Algsuperdiff.StochasticProcess.Common.Regularity.Freezing

open MeasureTheory HCPolySupport Filter
open Algsuperdiff.Section4.Provider.ExcessDecay
open Algsuperdiff.StochasticProcess.Common.Regularity
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported

noncomputable section

variable {d : ℕ}

/-! ## 1. Pointwise algebra of the reflected flux -/

private theorem matVecMul_zero_vec (A : Mat d) :
    matVecMul A (0 : Vec d) = 0 := by
  funext j
  simp [matVecMul]

private theorem matVecMul_sub_vec (A : Mat d) (u v : Vec d) :
    matVecMul A (u - v) = matVecMul A u - matVecMul A v := by
  funext j
  simp only [matVecMul, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

private theorem mem_faceHalf_reflection_of_notMem
    {U : Set (Vec d)} {i : Fin d} {c sigma : ℝ} (hsigma : sigma ≠ 0)
    (hUsymm : ∀ z : Vec d, coordFaceReflection c i z ∈ U ↔ z ∈ U)
    {y : Vec d} (hyU : y ∈ U) (hyH : y ∉ faceHalf U i c sigma) (hyplane : y i ≠ c) :
    coordFaceReflection c i y ∈ faceHalf U i c sigma := by
  refine ⟨(hUsymm y).2 hyU, ?_⟩
  have hle : ¬ (0 < sigma * (c - y i)) := fun hpos => hyH ⟨hyU, hpos⟩
  have hnezero : sigma * (c - y i) ≠ 0 := by
    intro hzero
    rcases mul_eq_zero.1 hzero with hcase | hcase
    · exact hsigma hcase
    · exact hyplane (by linarith only [hcase])
  have hneg : sigma * (c - y i) < 0 := lt_of_le_of_ne (not_lt.1 hle) hnezero
  change (0 : ℝ) < sigma * (c - coordFaceReflection c i y i)
  rw [coordFaceReflection_coord]
  have hid : sigma * (c - (2 * c - y i)) = -(sigma * (c - y i)) := by ring
  rw [hid]
  exact neg_pos.2 hneg

/-- The reflected coefficient applied to the odd extension of a gradient is the
odd extension of the original flux. -/
private theorem matVecMul_faceReflectedCoeff_oddFaceExtendGrad
    {U : Set (Vec d)} {i : Fin d} {c sigma : ℝ} (hsigma : sigma ≠ 0)
    (hUsymm : ∀ z : Vec d, coordFaceReflection c i z ∈ U ↔ z ∈ U)
    (b : CoeffField d) (G : Vec d → Vec d) {y : Vec d}
    (hyU : y ∈ U) (hyplane : y i ≠ c) :
    matVecMul (faceReflectedCoeff c i sigma b y)
        (oddFaceExtendGrad c i (zeroExtendGrad (faceHalf U i c sigma) G) y) =
      oddFaceExtendGrad c i
        (zeroExtendGrad (faceHalf U i c sigma)
          (fun z => matVecMul (b z) (G z))) y := by
  classical
  by_cases hyH : y ∈ faceHalf U i c sigma
  · have hry : coordFaceReflection c i y ∉ faceHalf U i c sigma :=
      coordFaceReflection_notMem_faceHalf hyH
    rw [faceReflectedCoeff_eq_on_faceHalf (U := U) b hyH]
    simp only [oddFaceExtendGrad, zeroExtendGrad_of_mem _ hyH,
      zeroExtendGrad_of_notMem _ hry, map_zero, sub_zero]
  · have hrmem : coordFaceReflection c i y ∈ faceHalf U i c sigma :=
      mem_faceHalf_reflection_of_notMem hsigma hUsymm hyU hyH hyplane
    rw [faceReflectedCoeff_eq_reflected (U := U) b hyU hyH hyplane hsigma]
    simp only [oddFaceExtendGrad, zeroExtendGrad_of_notMem _ hyH,
      zeroExtendGrad_of_mem _ hrmem]
    rw [matVecMul_sub_vec, matVecMul_zero_vec,
      matVecMul_faceReflectMat_coordReflectionLinear]

private theorem isMatrixDivFormWeakSolutionZerothOrderOn_h1FunctionOfSetEq
    {U V : Set (Vec d)} (hUV : U = V) {a : CoeffField d} {u : H1Function U}
    {g : Vec d → ℝ}
    (hu : IsMatrixDivFormWeakSolutionZerothOrderOn a U u g 0) :
    IsMatrixDivFormWeakSolutionZerothOrderOn a V (h1FunctionOfSetEq hUV u) g 0 := by
  subst hUV
  exact hu

/-! ## 2. The unfolding chain -/

private theorem boundaryReflectionChain_estimate1 :
    ∀ {d : ℕ} {x₀ : Vec d} {r : ℝ} {S : Finset (Fin d)}
      {sigma : Fin d → ℝ} (i : Fin d) (T : Finset (Fin d)) (w : H1Function (partialReflectedBallSector x₀ r S sigma T))
      (b : CoeffField d)
      (hFluxTL2 :
        ∀ (k : Fin d),
          MemLp
            (fun (y : Vec d) =>
              zeroExtendGrad (partialReflectedBallSector x₀ r S sigma T) (fun (z : Vec d) => matVecMul (b z) (w.grad z)) y
                k)
            (2 : ENNReal) volume)
      (j : Fin d),
      MemLp
        (fun (y : Vec d) =>
          oddFaceExtendGrad (x₀ i) i
            (zeroExtendGrad (partialReflectedBallSector x₀ r S sigma T) fun (z : Vec d) => matVecMul (b z) (w.grad z)) y j)
        (2 : ENNReal) volume := by
  intro d x₀ r S sigma i T w b hFluxTL2 j
  have hFTr : MemLp (fun y => zeroExtendGrad
      (partialReflectedBallSector x₀ r S sigma T)
      (fun z => matVecMul (b z) (w.grad z))
      (coordFaceReflection (x₀ i) i y) j) 2 (volume : Measure (Vec d)) :=
    (hFluxTL2 j).comp_measurePreserving
      (measurePreserving_coordFaceReflection (x₀ i) i)
  have hcoord : (fun y => oddFaceExtendGrad (x₀ i) i
      (zeroExtendGrad (partialReflectedBallSector x₀ r S sigma T)
        (fun z => matVecMul (b z) (w.grad z))) y j) =
      fun y => zeroExtendGrad (partialReflectedBallSector x₀ r S sigma T)
          (fun z => matVecMul (b z) (w.grad z)) y j -
        (if j = i then (-1 : ℝ) else 1) *
          zeroExtendGrad (partialReflectedBallSector x₀ r S sigma T)
            (fun z => matVecMul (b z) (w.grad z))
            (coordFaceReflection (x₀ i) i y) j := by
    funext y
    rw [oddFaceExtendGrad]
    simp only [Pi.sub_apply]
    rw [coordReflectionLinear_apply_coord]
  rw [hcoord]
  exact (hFluxTL2 j).sub (hFTr.const_mul _)

private theorem boundaryReflectionChain_estimate2 :
    ∀ {d : ℕ} {x₀ : Vec d} {r : ℝ} {S : Finset (Fin d)}
      {sigma : Fin d → ℝ} (i : Fin d) (T : Finset (Fin d)) (w : H1Function (partialReflectedBallSector x₀ r S sigma T))
      (b : CoeffField d)
      (hset :
        faceHalf (partialReflectedBallSector x₀ r S sigma (insert i T)) i (x₀ i) (sigma i) =
          partialReflectedBallSector x₀ r S sigma T)
      (hPIopen : IsOpen (partialReflectedBallSector x₀ r S sigma (insert i T)))
      (hsymmB :
        ∀ (y : Vec d),
          coordFaceReflection (x₀ i) i y ∈ partialReflectedBallSector x₀ r S sigma (insert i T) ↔
            y ∈ partialReflectedBallSector x₀ r S sigma (insert i T))
      (w' : H1Function (partialReflectedBallSector x₀ r S sigma (insert i T)))
      (hfluxIdentity :
        ∀ᵐ (y : Vec d) ∂volume.restrict (partialReflectedBallSector x₀ r S sigma (insert i T)),
          matVecMul (faceReflectedCoeff (x₀ i) i (sigma i) b y) (w'.grad y) =
            oddFaceExtendGrad (x₀ i) i
              (zeroExtendGrad (partialReflectedBallSector x₀ r S sigma T) fun (z : Vec d) => matVecMul (b z) (w.grad z)) y)
      (φ : Vec d → ℝ) (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hφc : HasCompactSupport φ)
      (hFluxHalf :
        ∀ (k : Fin d),
          MemLp
            (fun (y : Vec d) =>
              zeroExtendGrad (faceHalf (partialReflectedBallSector x₀ r S sigma (insert i T)) i (x₀ i) (sigma i))
                (fun (z : Vec d) => matVecMul (b z) (w.grad z)) y k)
            (2 : ENNReal) volume),
      ∫ (y : Vec d) in partialReflectedBallSector x₀ r S sigma (insert i T),
          vecDot (matVecMul (faceReflectedCoeff (x₀ i) i (sigma i) b y) (w'.grad y)) (euclideanGradient φ y) =
        ∫ (y : Vec d) in partialReflectedBallSector x₀ r S sigma T,
          vecDot (matVecMul (b y) (w.grad y))
            (euclideanGradient (fun (z : Vec d) => φ z - φ (coordFaceReflection (x₀ i) i z)) y) := by
  intro d x₀ r S sigma i T w b hset hPIopen hsymmB w' hfluxIdentity φ hφ hφc hFluxHalf
  have hcongr : ∫ y in partialReflectedBallSector x₀ r S sigma (insert i T),
        vecDot (matVecMul (faceReflectedCoeff (x₀ i) i (sigma i) b y)
          (w'.grad y)) (euclideanGradient φ y) ∂volume =
      ∫ y in partialReflectedBallSector x₀ r S sigma (insert i T),
        vecDot (oddFaceExtendGrad (x₀ i) i
          (zeroExtendGrad (partialReflectedBallSector x₀ r S sigma T)
            (fun z => matVecMul (b z) (w.grad z))) y)
          (euclideanGradient φ y) ∂volume := by
    refine integral_congr_ae ?_
    filter_upwards [hfluxIdentity] with y hy
    rw [hy]
  rw [hcongr]
  have hmain := integral_vecDot_oddFaceExtendGrad_eq (U :=
      partialReflectedBallSector x₀ r S sigma (insert i T))
    hPIopen (i := i) (c := x₀ i) (sigma := sigma i) hsymmB
    (F := fun z => matVecMul (b z) (w.grad z)) hFluxHalf hφ hφc
  rw [hset] at hmain
  exact hmain

private theorem boundaryReflectionChain_estimate3 :
    ∀ {d : ℕ} {x₀ : Vec d} {r : ℝ} {S : Finset (Fin d)}
      {sigma : Fin d → ℝ} (i : Fin d) (T : Finset (Fin d)) (φ : Vec d → ℝ)
      (hφPI : tsupport φ ⊆ partialReflectedBallSector x₀ r S sigma (insert i T))
      (hφrPI :
        (tsupport fun (z : Vec d) => φ (coordFaceReflection (x₀ i) i z)) ⊆
          partialReflectedBallSector x₀ r S sigma (insert i T)),
      (tsupport fun (z : Vec d) => φ z - φ (coordFaceReflection (x₀ i) i z)) ⊆
        partialReflectedBallSector x₀ r S sigma (insert i T) := by
  intro d x₀ r S sigma i T φ hφPI hφrPI
  have hsupp : Function.support
      (fun z => φ z - φ (coordFaceReflection (x₀ i) i z)) ⊆
      tsupport φ ∪ tsupport (fun z => φ (coordFaceReflection (x₀ i) i z)) := by
    intro q hq
    simp only [Function.mem_support] at hq
    by_contra hcon
    simp only [Set.mem_union, not_or] at hcon
    have h1 : φ q = 0 := image_eq_zero_of_notMem_tsupport hcon.1
    have h2 : φ (coordFaceReflection (x₀ i) i q) = 0 :=
      image_eq_zero_of_notMem_tsupport
        (f := fun z => φ (coordFaceReflection (x₀ i) i z)) hcon.2
    exact hq (by rw [h1, h2, sub_self])
  have hclosed : IsClosed (tsupport φ ∪
      tsupport (fun z => φ (coordFaceReflection (x₀ i) i z))) :=
    (isClosed_tsupport φ).union (isClosed_tsupport _)
  exact (closure_minimal hsupp hclosed).trans (Set.union_subset hφPI hφrPI)

private theorem boundaryReflectionChain_estimate4 :
    ∀ {d : ℕ} {x₀ : Vec d} {r : ℝ} {S : Finset (Fin d)}
      {sigma : Fin d → ℝ} (i : Fin d) (T : Finset (Fin d)) (w : H1Function (partialReflectedBallSector x₀ r S sigma T))
      (b : CoeffField d) (hsigmai0 : sigma i ≠ (0 : ℝ))
      (hset :
        faceHalf (partialReflectedBallSector x₀ r S sigma (insert i T)) i (x₀ i) (sigma i) =
          partialReflectedBallSector x₀ r S sigma T)
      (hPImeas : MeasurableSet (partialReflectedBallSector x₀ r S sigma (insert i T)))
      (hsymmB :
        ∀ (y : Vec d),
          coordFaceReflection (x₀ i) i y ∈ partialReflectedBallSector x₀ r S sigma (insert i T) ↔
            y ∈ partialReflectedBallSector x₀ r S sigma (insert i T))
      (w' : H1Function (partialReflectedBallSector x₀ r S sigma (insert i T)))
      (hgrad :
        ∀ (y : Vec d),
          w'.grad y = oddFaceExtendGrad (x₀ i) i (zeroExtendGrad (partialReflectedBallSector x₀ r S sigma T) w.grad) y)
      (hplaneAE : ∀ᵐ (y : Vec d), y i ≠ x₀ i),
      ∀ᵐ (y : Vec d) ∂volume.restrict (partialReflectedBallSector x₀ r S sigma (insert i T)),
        matVecMul (faceReflectedCoeff (x₀ i) i (sigma i) b y) (w'.grad y) =
          oddFaceExtendGrad (x₀ i) i
            (zeroExtendGrad (partialReflectedBallSector x₀ r S sigma T) fun (z : Vec d) => matVecMul (b z) (w.grad z)) y := by
  intro d x₀ r S sigma i T w b hsigmai0 hset hPImeas hsymmB w' hgrad hplaneAE
  filter_upwards [ae_restrict_mem hPImeas,
    (ae_restrict_of_ae hplaneAE :
      ∀ᵐ y ∂volume.restrict
        (partialReflectedBallSector x₀ r S sigma (insert i T)), y i ≠ x₀ i)]
    with y hyPI hyplane
  rw [hgrad y]
  have hstep := matVecMul_faceReflectedCoeff_oddFaceExtendGrad hsigmai0 hsymmB b
    w.grad hyPI hyplane
  rw [hset] at hstep
  exact hstep

private theorem oddReflection_testFunctionExtension :
    ∀ {d : ℕ} {x₀ : Vec d} {r : ℝ} {S : Finset (Fin d)}
      {sigma : Fin d → ℝ} (i : Fin d) (T : Finset (Fin d)) (w : H1Function (partialReflectedBallSector x₀ r S sigma T))
      (b : CoeffField d) (h : Vec d → ℝ)
      (hweq :
        IsMatrixDivFormWeakSolutionZerothOrderOn b (partialReflectedBallSector x₀ r S sigma T) w h (0 : Vec d → Vec d))
      (hsigmai : |sigma i| = (1 : ℝ))
      (hset :
        faceHalf (partialReflectedBallSector x₀ r S sigma (insert i T)) i (x₀ i) (sigma i) =
          partialReflectedBallSector x₀ r S sigma T)
      (hPIdom : IsOpenBoundedConvexDomain (partialReflectedBallSector x₀ r S sigma (insert i T)))
      (hPIopen : IsOpen (partialReflectedBallSector x₀ r S sigma (insert i T)))
      (hPTopen : IsOpen (partialReflectedBallSector x₀ r S sigma T))
      (hPTfinite : IsFiniteMeasure (volume.restrict (partialReflectedBallSector x₀ r S sigma T)))
      (hsymmB :
        ∀ (y : Vec d),
          coordFaceReflection (x₀ i) i y ∈ partialReflectedBallSector x₀ r S sigma (insert i T) ↔
            y ∈ partialReflectedBallSector x₀ r S sigma (insert i T))
      (w' : H1Function (partialReflectedBallSector x₀ r S sigma (insert i T)))
      (hZL2 : MemLp (zeroExtend (partialReflectedBallSector x₀ r S sigma T) h) (2 : ENNReal) volume)
      (hOddScalarL2 :
        MemLp (oddFaceExtend (x₀ i) i (zeroExtend (partialReflectedBallSector x₀ r S sigma T) h)) (2 : ENNReal) volume)
      (hFluxTL2 :
        ∀ (k : Fin d),
          MemLp
            (fun (y : Vec d) =>
              zeroExtendGrad (partialReflectedBallSector x₀ r S sigma T) (fun (z : Vec d) => matVecMul (b z) (w.grad z)) y
                k)
            (2 : ENNReal) volume)
      (hfluxIdentity :
        ∀ᵐ (y : Vec d) ∂volume.restrict (partialReflectedBallSector x₀ r S sigma (insert i T)),
          matVecMul (faceReflectedCoeff (x₀ i) i (sigma i) b y) (w'.grad y) =
            oddFaceExtendGrad (x₀ i) i
              (zeroExtendGrad (partialReflectedBallSector x₀ r S sigma T) fun (z : Vec d) => matVecMul (b z) (w.grad z)) y)
      (hfluxPI :
        ∀ (j : Fin d),
          MemLp (fun (y : Vec d) => matVecMul (faceReflectedCoeff (x₀ i) i (sigma i) b y) (w'.grad y) j) (2 : ENNReal)
            (volume.restrict (partialReflectedBallSector x₀ r S sigma (insert i T)))),
      IsMatrixDivFormWeakSolutionZerothOrderOn (faceReflectedCoeff (x₀ i) i (sigma i) b)
        (partialReflectedBallSector x₀ r S sigma (insert i T)) w'
        (oddFaceExtend (x₀ i) i (zeroExtend (partialReflectedBallSector x₀ r S sigma T) h)) (0 : Vec d → Vec d) := by
  intro d x₀ r S sigma i T w b h hweq hsigmai hset hPIdom hPIopen hPTopen hPTfinite hsymmB w' hZL2 hOddScalarL2 hFluxTL2 hfluxIdentity hfluxPI
  refine isMatrixDivFormWeakSolutionZerothOrderOn_of_contDiff_tests hfluxPI
    (hOddScalarL2.restrict _) ?_
  intro φ hφ hφc hφPI
  have hφr : ContDiff ℝ (⊤ : ℕ∞) fun z => φ (coordFaceReflection (x₀ i) i z) := by
    simpa [Function.comp] using! hφ.comp (contDiff_coordFaceReflection (x₀ i) i)
  have hφrc : HasCompactSupport fun z => φ (coordFaceReflection (x₀ i) i z) :=
    hasCompactSupport_comp_coordFaceReflection hφc (x₀ i) i
  have hφrPI : tsupport (fun z => φ (coordFaceReflection (x₀ i) i z)) ⊆
      partialReflectedBallSector x₀ r S sigma (insert i T) :=
    tsupport_comp_coordFaceReflection_subset (x₀ i) i hsymmB hφPI
  have hψ : ContDiff ℝ (⊤ : ℕ∞)
      fun z => φ z - φ (coordFaceReflection (x₀ i) i z) := hφ.sub hφr
  have hψc : HasCompactSupport
      fun z => φ z - φ (coordFaceReflection (x₀ i) i z) := hφc.sub hφrc
  have hψPI : tsupport (fun z => φ z - φ (coordFaceReflection (x₀ i) i z)) ⊆
      partialReflectedBallSector x₀ r S sigma (insert i T)  := @boundaryReflectionChain_estimate3 (d) (x₀) (r) (S) (sigma) (i) (T) (φ) (hφPI) (hφrPI)
  have hψ0 : ∀ y : Vec d, y i = x₀ i →
      φ y - φ (coordFaceReflection (x₀ i) i y) = 0 := by
    intro y hy
    rw [coordFaceReflection_eq_self hy, sub_self]
  have hmemH10 : MemH10 (partialReflectedBallSector x₀ r S sigma T)
      fun z => φ z - φ (coordFaceReflection (x₀ i) i z) := by
    have h := memH10_faceHalf_of_contDiff_of_vanishing_on_face hPIdom hsigmai
      hψ hψc hψPI hψ0
    rwa [hset] at h
  have hFluxHalf : ∀ k : Fin d, MemLp (fun y => zeroExtendGrad
      (faceHalf (partialReflectedBallSector x₀ r S sigma (insert i T))
        i (x₀ i) (sigma i))
      (fun z => matVecMul (b z) (w.grad z)) y k) 2
      (volume : Measure (Vec d)) := by
    rw [hset]
    exact hFluxTL2
  have hScalarHalf : MemLp (zeroExtend
      (faceHalf (partialReflectedBallSector x₀ r S sigma (insert i T))
        i (x₀ i) (sigma i)) h) 2 (volume : Measure (Vec d)) := by
    rw [hset]
    exact hZL2
  have hleft : ∫ y in partialReflectedBallSector x₀ r S sigma (insert i T),
        vecDot (matVecMul (faceReflectedCoeff (x₀ i) i (sigma i) b y)
          (w'.grad y)) (euclideanGradient φ y) ∂volume =
      ∫ y in partialReflectedBallSector x₀ r S sigma T,
        vecDot (matVecMul (b y) (w.grad y))
          (euclideanGradient
            (fun z => φ z - φ (coordFaceReflection (x₀ i) i z)) y) ∂volume  := @boundaryReflectionChain_estimate2 (d) (x₀) (r) (S) (sigma) (i) (T) (w) (b) (hset) (hPIopen) (hsymmB) (w') (hfluxIdentity) (φ) (hφ) (hφc) (hFluxHalf)
  have hright : ∫ y in partialReflectedBallSector x₀ r S sigma (insert i T),
        oddFaceExtend (x₀ i) i
          (zeroExtend (partialReflectedBallSector x₀ r S sigma T) h) y *
          φ y ∂volume =
      ∫ y in partialReflectedBallSector x₀ r S sigma T,
        h y * (φ y - φ (coordFaceReflection (x₀ i) i y)) ∂volume := by
    have hmain := integral_mul_oddFaceExtend_eq (U :=
        partialReflectedBallSector x₀ r S sigma (insert i T))
      hPIopen (i := i) (c := x₀ i) (sigma := sigma i) hsymmB
      (h := h) hScalarHalf hφ hφc
    rw [hset] at hmain
    exact hmain
  rw [hleft, hright]
  exact integral_pairing_eq_of_memH10 hPTopen hweq hψ hmemH10


private theorem oddReflection_remainingFaceSymmetry :
    ∀ {d : ℕ} {x₀ : Vec d} {r : ℝ} {S : Finset (Fin d)}
      {sigma : Fin d → ℝ} (i : Fin d) (T : Finset (Fin d)) (hiT : i ∉ T) (hsub : insert i T ⊆ S) (hiS : i ∈ S)
      (w : H1Function (partialReflectedBallSector x₀ r S sigma T)) (b : CoeffField d) (h : Vec d → ℝ)
      (hwodd : ∀ j ∈ T, ∀ (z : Vec d), w.toFun (coordFaceReflection (x₀ j) j z) = -w.toFun z)
      (hsigmai : |sigma i| = (1 : ℝ)) (hsigmai0 : sigma i ≠ (0 : ℝ))
      (hset :
        faceHalf (partialReflectedBallSector x₀ r S sigma (insert i T)) i (x₀ i) (sigma i) =
          partialReflectedBallSector x₀ r S sigma T)
      (hPIdom : IsOpenBoundedConvexDomain (partialReflectedBallSector x₀ r S sigma (insert i T)))
      (hPIopen : IsOpen (partialReflectedBallSector x₀ r S sigma (insert i T)))
      (hPImeas : MeasurableSet (partialReflectedBallSector x₀ r S sigma (insert i T)))
      (hsymmB :
        ∀ (y : Vec d),
          coordFaceReflection (x₀ i) i y ∈ partialReflectedBallSector x₀ r S sigma (insert i T) ↔
            y ∈ partialReflectedBallSector x₀ r S sigma (insert i T))
      (hsymmBall : ∀ (y : Vec d), coordFaceReflection (x₀ i) i y ∈ euclideanBall x₀ r ↔ y ∈ euclideanBall x₀ r)
      (hBsub : partialReflectedBallSector x₀ r S sigma (insert i T) ⊆ euclideanBall x₀ r)
      (hztT :
        LocalizedZeroTraceFunctionOn (partialReflectedBallSector x₀ r S sigma T)
          (partialReflectedBallSector x₀ r S sigma (insert i T)) w.toFun)
      (w' : H1Function (partialReflectedBallSector x₀ r S sigma (insert i T)))
      (hval' :
        ∀ (y : Vec d),
          w'.toFun y =
            oddFaceExtend (x₀ i) i
              (zeroExtend (faceHalf (partialReflectedBallSector x₀ r S sigma (insert i T)) i (x₀ i) (sigma i))
                (h1FunctionOfSetEq (Eq.symm hset) w).toFun)
              y)
      (hgrad' :
        ∀ (y : Vec d),
          w'.grad y =
            oddFaceExtendGrad (x₀ i) i
              (zeroExtendGrad (faceHalf (partialReflectedBallSector x₀ r S sigma (insert i T)) i (x₀ i) (sigma i))
                (h1FunctionOfSetEq (Eq.symm hset) w).grad)
              y)
      (hval :
        ∀ (y : Vec d),
          w'.toFun y = oddFaceExtend (x₀ i) i (zeroExtend (partialReflectedBallSector x₀ r S sigma T) w.toFun) y)
      (hgrad :
        ∀ (y : Vec d),
          w'.grad y = oddFaceExtendGrad (x₀ i) i (zeroExtendGrad (partialReflectedBallSector x₀ r S sigma T) w.grad) y)
      (hplaneAE : ∀ᵐ (y : Vec d), y i ≠ x₀ i)
      (hZrL2 :
        MemLp (fun (y : Vec d) => zeroExtend (partialReflectedBallSector x₀ r S sigma T) h (coordFaceReflection (x₀ i) i y))
          (2 : ENNReal) volume)
      (hOddScalarL2 :
        MemLp (oddFaceExtend (x₀ i) i (zeroExtend (partialReflectedBallSector x₀ r S sigma T) h)) (2 : ENNReal) volume)
      (hOddFluxL2 :
        ∀ (j : Fin d),
          MemLp
            (fun (y : Vec d) =>
              oddFaceExtendGrad (x₀ i) i
                (zeroExtendGrad (partialReflectedBallSector x₀ r S sigma T) fun (z : Vec d) => matVecMul (b z) (w.grad z)) y
                j)
            (2 : ENNReal) volume)
      (hfluxIdentity :
        ∀ᵐ (y : Vec d) ∂volume.restrict (partialReflectedBallSector x₀ r S sigma (insert i T)),
          matVecMul (faceReflectedCoeff (x₀ i) i (sigma i) b y) (w'.grad y) =
            oddFaceExtendGrad (x₀ i) i
              (zeroExtendGrad (partialReflectedBallSector x₀ r S sigma T) fun (z : Vec d) => matVecMul (b z) (w.grad z)) y)
      (hfluxPI :
        ∀ (j : Fin d),
          MemLp (fun (y : Vec d) => matVecMul (faceReflectedCoeff (x₀ i) i (sigma i) b y) (w'.grad y) j) (2 : ENNReal)
            (volume.restrict (partialReflectedBallSector x₀ r S sigma (insert i T)))),
      ∀ j ∈ insert i T, ∀ (z : Vec d), w'.toFun (coordFaceReflection (x₀ j) j z) = -w'.toFun z := by
  intro d x₀ r S sigma i T hiT hsub hiS w b h hwodd hsigmai hsigmai0 hset hPIdom hPIopen hPImeas hsymmB hsymmBall hBsub hztT w' hval' hgrad' hval hgrad hplaneAE hZrL2 hOddScalarL2 hOddFluxL2 hfluxIdentity hfluxPI j hj z
  rcases Finset.mem_insert.mp hj with hji | hjT
  · subst hji
    rw [hval (coordFaceReflection (x₀ j) j z), hval z]
    exact oddFaceExtend_comp_coordFaceReflection (x₀ j) j _ z
  · have hji : j ≠ i := fun hcon => hiT (hcon ▸ hjT)
    have hjinv := mem_partialReflectedBallSector_coordFaceReflection_iff
      (S := S) (sigma := sigma) (r := r) (x₀ := x₀) hjT
    have hZodd : ∀ q : Vec d,
        zeroExtend (partialReflectedBallSector x₀ r S sigma T) w.toFun
            (coordFaceReflection (x₀ j) j q) =
          -zeroExtend (partialReflectedBallSector x₀ r S sigma T) w.toFun q := by
      intro q
      by_cases hq : q ∈ partialReflectedBallSector x₀ r S sigma T
      · rw [zeroExtend_of_mem _ ((hjinv q).2 hq), zeroExtend_of_mem _ hq]
        exact hwodd j hjT q
      · rw [zeroExtend_of_notMem _ (fun hc => hq ((hjinv q).1 hc)),
          zeroExtend_of_notMem _ hq, neg_zero]
    rw [hval (coordFaceReflection (x₀ j) j z), hval z]
    change zeroExtend (partialReflectedBallSector x₀ r S sigma T) w.toFun
          (coordFaceReflection (x₀ j) j z)
        - zeroExtend (partialReflectedBallSector x₀ r S sigma T) w.toFun
            (coordFaceReflection (x₀ i) i (coordFaceReflection (x₀ j) j z))
      = -(zeroExtend (partialReflectedBallSector x₀ r S sigma T) w.toFun z
        - zeroExtend (partialReflectedBallSector x₀ r S sigma T) w.toFun
            (coordFaceReflection (x₀ i) i z))
    rw [hZodd z, coordFaceReflection_comm hji.symm _ _ z,
      hZodd (coordFaceReflection (x₀ i) i z)]
    ring


/-- **Odd unfolding of a sector weak solution.**  At every intermediate ball
sector the odd extension solves the divergence-form equation for the
conjugated coefficient with the oddly extended source, retains the
small-contrast bound, restricts to the original datum, is odd under every
unfolded face reflection, and keeps the localized zero-trace property needed by
the next step. -/
theorem exists_oddReflection_weakSolution_chain
    {x₀ : Vec d} {r : ℝ} (hr : 0 < r) {S : Finset (Fin d)} {sigma : Fin d → ℝ}
    (hsigma : ∀ i ∈ S, |sigma i| = 1)
    {a : CoeffField d} {delta M : ℝ} (hM : 0 ≤ M)
    (hameas : Measurable a)
    (hcontrast : CoefficientIdentityDistanceLE (ballSector x₀ r S sigma) a delta)
    (v : H1Function (ballSector x₀ r S sigma))
    (hzt : LocalizedZeroTraceFunctionOn (ballSector x₀ r S sigma)
      (euclideanBall x₀ r) v.toFun)
    {g : Vec d → ℝ}
    (hgL2 : MemLp g 2 (volume.restrict (ballSector x₀ r S sigma)))
    (hgM : ∀ᵐ y ∂volume.restrict (ballSector x₀ r S sigma), |g y| ≤ M)
    (hflux : ∀ j, MemLp (fun y => matVecMul (a y) (v.grad y) j) 2
      (volume.restrict (ballSector x₀ r S sigma)))
    (hv : IsMatrixDivFormWeakSolutionZerothOrderOn a (ballSector x₀ r S sigma) v g 0) :
    ∀ T : Finset (Fin d), T ⊆ S →
      ∃ (w : H1Function (partialReflectedBallSector x₀ r S sigma T))
        (b : CoeffField d) (h : Vec d → ℝ),
        Measurable b ∧
        CoefficientIdentityDistanceLE
          (partialReflectedBallSector x₀ r S sigma T) b delta ∧
        MemLp h 2 (volume : Measure (Vec d)) ∧
        (∀ᵐ y ∂(volume : Measure (Vec d)), |h y| ≤ 2 ^ T.card * M) ∧
        (∀ j, MemLp (fun y => matVecMul (b y) (w.grad y) j) 2
          (volume.restrict (partialReflectedBallSector x₀ r S sigma T))) ∧
        IsMatrixDivFormWeakSolutionZerothOrderOn b
          (partialReflectedBallSector x₀ r S sigma T) w h 0 ∧
        (∀ y ∈ ballSector x₀ r S sigma, w.toFun y = v.toFun y) ∧
        (∀ j ∈ T, ∀ z : Vec d,
          w.toFun (coordFaceReflection (x₀ j) j z) = -w.toFun z) ∧
        LocalizedZeroTraceFunctionOn (partialReflectedBallSector x₀ r S sigma T)
          (euclideanBall x₀ r) w.toFun := by
  classical
  intro T
  induction T using Finset.induction_on with
  | empty =>
      intro _hsub
      have hWmeas : MeasurableSet (ballSector x₀ r S sigma) :=
        (isOpen_partialReflectedBallSector x₀ r S sigma ∅).measurableSet
      refine ⟨v, a, zeroExtend (ballSector x₀ r S sigma) g, hameas, hcontrast,
        (memLp_indicator_iff_restrict hWmeas).2 hgL2, ?_, hflux, ?_,
        fun y _hy => rfl, ?_, hzt⟩
      · have hgGlobal : ∀ᵐ y ∂(volume : Measure (Vec d)),
            y ∈ ballSector x₀ r S sigma → |g y| ≤ M :=
          (ae_restrict_iff' hWmeas).1 hgM
        filter_upwards [hgGlobal] with y hy
        by_cases hyW : y ∈ ballSector x₀ r S sigma
        · rw [zeroExtend_of_mem _ hyW]
          simpa only [Finset.card_empty, pow_zero, one_mul] using hy hyW
        · rw [zeroExtend_of_notMem _ hyW, abs_zero]
          simpa only [Finset.card_empty, pow_zero, one_mul] using hM
      · intro phi
        have hmain := hv phi
        have hcongr : ∫ y in partialReflectedBallSector x₀ r S sigma ∅,
              zeroExtend (ballSector x₀ r S sigma) g y *
                phi.toH1Function.toFun y ∂volume =
            ∫ y in partialReflectedBallSector x₀ r S sigma ∅,
              g y * phi.toH1Function.toFun y ∂volume := by
          refine setIntegral_congr_fun hWmeas fun y hy => ?_
          have hy' : y ∈ ballSector x₀ r S sigma := hy
          rw [zeroExtend_of_mem _ hy']
        rw [hcongr]
        exact hmain
      · intro j hj
        exact absurd hj (Finset.notMem_empty j)
  | @insert i T hiT ih =>
      intro hsub
      have hTsub : T ⊆ S := fun j hj => hsub (Finset.mem_insert_of_mem hj)
      have hiS : i ∈ S := hsub (Finset.mem_insert_self i T)
      obtain ⟨w, b, h, hbmeas, hbcontrast, hhL2, hhM, hbflux, hweq, hwpin, hwodd,
        hwzt⟩ := ih hTsub
      have hsigmai : |sigma i| = 1 := hsigma i hiS
      have hsigmai0 : sigma i ≠ 0 := by
        intro hzero
        rw [hzero, abs_zero] at hsigmai
        norm_num at hsigmai
      have hset : faceHalf (partialReflectedBallSector x₀ r S sigma (insert i T))
          i (x₀ i) (sigma i) = partialReflectedBallSector x₀ r S sigma T :=
        faceHalf_partialReflectedBallSector_insert hiS hiT
      have hPIdom : IsOpenBoundedConvexDomain
          (partialReflectedBallSector x₀ r S sigma (insert i T)) :=
        isOpenBoundedConvexDomain_partialReflectedBallSector x₀ hr S sigma (insert i T)
      have hPIopen : IsOpen (partialReflectedBallSector x₀ r S sigma (insert i T)) :=
        hPIdom.isOpen
      have hPImeas : MeasurableSet
          (partialReflectedBallSector x₀ r S sigma (insert i T)) :=
        hPIopen.measurableSet
      have hPTopen : IsOpen (partialReflectedBallSector x₀ r S sigma T) :=
        isOpen_partialReflectedBallSector x₀ r S sigma T
      have hPTmeas : MeasurableSet (partialReflectedBallSector x₀ r S sigma T) :=
        hPTopen.measurableSet
      have hPTfinite : IsFiniteMeasure
          (volume.restrict (partialReflectedBallSector x₀ r S sigma T)) :=
        (isOpenBoundedConvexDomain_partialReflectedBallSector x₀ hr S sigma
          T).isFiniteMeasure_restrict_volume
      have hsymmB : ∀ y : Vec d,
          coordFaceReflection (x₀ i) i y ∈
              partialReflectedBallSector x₀ r S sigma (insert i T) ↔
            y ∈ partialReflectedBallSector x₀ r S sigma (insert i T) :=
        mem_partialReflectedBallSector_coordFaceReflection_iff
          (S := S) (sigma := sigma) (r := r) (x₀ := x₀) (Finset.mem_insert_self i T)
      have hsymmBall := mem_euclideanBall_coordFaceReflection_center_iff x₀ r i
      have hBsub : partialReflectedBallSector x₀ r S sigma (insert i T) ⊆
          euclideanBall x₀ r := fun y hy => (mem_partialReflectedBallSector_iff.mp hy).1
      have hztT : LocalizedZeroTraceFunctionOn
          (partialReflectedBallSector x₀ r S sigma T)
          (partialReflectedBallSector x₀ r S sigma (insert i T)) w.toFun :=
        localizedZeroTraceFunctionOn_mono_window hBsub hwzt
      obtain ⟨w', hval', hgrad'⟩ := exists_h1Function_oddFaceExtend hPIdom hsymmB
        (h1FunctionOfSetEq hset.symm w)
        (by rw [h1FunctionOfSetEq_toFun, hset]; exact hztT)
      have hval : ∀ y, w'.toFun y = oddFaceExtend (x₀ i) i
          (zeroExtend (partialReflectedBallSector x₀ r S sigma T) w.toFun) y := by
        intro y
        rw [hval' y, h1FunctionOfSetEq_toFun, hset]
      have hgrad : ∀ y, w'.grad y = oddFaceExtendGrad (x₀ i) i
          (zeroExtendGrad (partialReflectedBallSector x₀ r S sigma T) w.grad) y := by
        intro y
        rw [hgrad' y, h1FunctionOfSetEq_grad, hset]
      have hplaneAE : ∀ᵐ y ∂(volume : Measure (Vec d)), y i ≠ x₀ i := by
        rw [ae_iff]
        simpa only [not_not] using
          Algsuperdiff.Section4.Provider.ExcessDecay.Schauder.volume_coordHyperplane_eq_zero
            i (x₀ i)
      have hZL2 : MemLp (zeroExtend (partialReflectedBallSector x₀ r S sigma T) h) 2
          (volume : Measure (Vec d)) :=
        (memLp_indicator_iff_restrict hPTmeas).2 (hhL2.restrict _)
      have hZrL2 : MemLp (fun y => zeroExtend
          (partialReflectedBallSector x₀ r S sigma T) h
            (coordFaceReflection (x₀ i) i y)) 2 (volume : Measure (Vec d)) :=
        hZL2.comp_measurePreserving (measurePreserving_coordFaceReflection (x₀ i) i)
      have hOddScalarL2 : MemLp (oddFaceExtend (x₀ i) i
          (zeroExtend (partialReflectedBallSector x₀ r S sigma T) h)) 2
          (volume : Measure (Vec d)) := hZL2.sub hZrL2
      have hFluxTL2 : ∀ k : Fin d, MemLp (fun y => zeroExtendGrad
          (partialReflectedBallSector x₀ r S sigma T)
          (fun z => matVecMul (b z) (w.grad z)) y k) 2
          (volume : Measure (Vec d)) := by
        intro k
        rw [zeroExtendGrad_apply_coord]
        exact (memLp_indicator_iff_restrict hPTmeas).2 (hbflux k)
      have hOddFluxL2 : ∀ j : Fin d, MemLp (fun y => oddFaceExtendGrad (x₀ i) i
          (zeroExtendGrad (partialReflectedBallSector x₀ r S sigma T)
            (fun z => matVecMul (b z) (w.grad z))) y j) 2
          (volume : Measure (Vec d))  := @boundaryReflectionChain_estimate1 (d) (x₀) (r) (S) (sigma) (i) (T) (w) (b) (hFluxTL2)
      have hfluxIdentity : ∀ᵐ y ∂volume.restrict
          (partialReflectedBallSector x₀ r S sigma (insert i T)),
          matVecMul (faceReflectedCoeff (x₀ i) i (sigma i) b y) (w'.grad y) =
            oddFaceExtendGrad (x₀ i) i
              (zeroExtendGrad (partialReflectedBallSector x₀ r S sigma T)
                (fun z => matVecMul (b z) (w.grad z))) y  := @boundaryReflectionChain_estimate4 (d) (x₀) (r) (S) (sigma) (i) (T) (w) (b) (hsigmai0) (hset) (hPImeas) (hsymmB) (w') (hgrad) (hplaneAE)
      have hfluxPI : ∀ j : Fin d,
          MemLp (fun y => matVecMul (faceReflectedCoeff (x₀ i) i (sigma i) b y)
            (w'.grad y) j) 2 (volume.restrict
              (partialReflectedBallSector x₀ r S sigma (insert i T))) := by
        intro j
        refine ((hOddFluxL2 j).restrict _).ae_eq ?_
        filter_upwards [hfluxIdentity] with y hy
        rw [hy]
      -- the reflected coefficient and source
      refine ⟨w', faceReflectedCoeff (x₀ i) i (sigma i) b,
        oddFaceExtend (x₀ i) i
          (zeroExtend (partialReflectedBallSector x₀ r S sigma T) h),
        measurable_faceReflectedCoeff hbmeas, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · have hbase : CoefficientIdentityDistanceLE
            (faceHalf (partialReflectedBallSector x₀ r S sigma (insert i T))
              i (x₀ i) (sigma i)) b delta := by
          rw [hset]
          exact hbcontrast
        exact coefficientIdentityDistanceLE_faceReflectedCoeff hsigmai0 hPIopen
          hsymmB hbase
      · have hZ : MemLp (zeroExtend (partialReflectedBallSector x₀ r S sigma T) h) 2
            (volume : Measure (Vec d)) :=
          (memLp_indicator_iff_restrict hPTmeas).2 (hhL2.restrict _)
        have hZr : MemLp (fun y => zeroExtend
            (partialReflectedBallSector x₀ r S sigma T) h
              (coordFaceReflection (x₀ i) i y)) 2 (volume : Measure (Vec d)) :=
          hZ.comp_measurePreserving (measurePreserving_coordFaceReflection (x₀ i) i)
        exact hZ.sub hZr
      · have hZbound : ∀ᵐ y ∂(volume : Measure (Vec d)),
            |zeroExtend (partialReflectedBallSector x₀ r S sigma T) h y| ≤
              2 ^ T.card * M := by
          filter_upwards [hhM] with y hy
          by_cases hyT : y ∈ partialReflectedBallSector x₀ r S sigma T
          · rw [zeroExtend_of_mem _ hyT]
            exact hy
          · rw [zeroExtend_of_notMem _ hyT, abs_zero]
            positivity
        have hZrbound : ∀ᵐ y ∂(volume : Measure (Vec d)),
            |zeroExtend (partialReflectedBallSector x₀ r S sigma T) h
              (coordFaceReflection (x₀ i) i y)| ≤ 2 ^ T.card * M :=
          (measurePreserving_coordFaceReflection (x₀ i) i).quasiMeasurePreserving.ae
            hZbound
        filter_upwards [hZbound, hZrbound] with y hy hry
        have hcard : (insert i T).card = T.card + 1 := Finset.card_insert_of_notMem hiT
        rw [oddFaceExtend, hcard]
        calc
          |zeroExtend (partialReflectedBallSector x₀ r S sigma T) h y -
              zeroExtend (partialReflectedBallSector x₀ r S sigma T) h
                (coordFaceReflection (x₀ i) i y)| ≤
              |zeroExtend (partialReflectedBallSector x₀ r S sigma T) h y| +
                |zeroExtend (partialReflectedBallSector x₀ r S sigma T) h
                  (coordFaceReflection (x₀ i) i y)| := abs_sub _ _
          _ ≤ 2 ^ T.card * M + 2 ^ T.card * M := add_le_add hy hry
          _ = 2 ^ (T.card + 1) * M := by ring
      · exact hfluxPI
      · exact @oddReflection_testFunctionExtension (d) (x₀) (r) (S) (sigma) (i) (T) (w) (b) (h) (hweq) (hsigmai) (hset) (hPIdom) (hPIopen) (hPTopen) (by infer_instance) (hsymmB) (w') (hZL2) (hOddScalarL2) (hFluxTL2) (hfluxIdentity) (hfluxPI)
      · intro y hy
        have hyT : y ∈ partialReflectedBallSector x₀ r S sigma T :=
          ballSector_subset_partialReflectedBallSector x₀ r S sigma T hy
        have hry : coordFaceReflection (x₀ i) i y ∉
            partialReflectedBallSector x₀ r S sigma T := by
          rw [← hset] at hyT ⊢
          exact coordFaceReflection_notMem_faceHalf hyT
        rw [hval y, oddFaceExtend_zeroExtend_of_mem w.toFun (x₀ i) i hyT hry]
        exact hwpin y hy
      · exact @oddReflection_remainingFaceSymmetry (d) (x₀) (r) (S) (sigma) (i) (T) (hiT) (hsub) (hiS) (w) (b) (h) (hwodd) (hsigmai) (hsigmai0) (hset) (hPIdom) (hPIopen) (hPImeas) (hsymmB) (hsymmBall) (hBsub) (hztT) (w') (hval') (hgrad') (hval) (hgrad) (hplaneAE) (hZrL2) (hOddScalarL2) (hOddFluxL2) (hfluxIdentity) (hfluxPI)
      · have htrans := localizedZeroTraceFunctionOn_oddFaceExtend hPTmeas hPIopen
          (by rw [← hset]; exact faceHalf_subset _ _ _ _) hsymmB hsymmBall hwzt
        have hfun : w'.toFun = oddFaceExtend (x₀ i) i
            (zeroExtend (partialReflectedBallSector x₀ r S sigma T) w.toFun) :=
          funext hval
        rw [hfun]
        exact htrans

/-- **The odd reflection across all flat faces solves a small-contrast
equation on the whole centred ball.**  This is the `T = S` case of the chain,
transported along the identification of the fully unfolded sector with the
ball. -/
theorem exists_oddReflection_weakSolution_ball
    {x₀ : Vec d} {r : ℝ} (hr : 0 < r) {S : Finset (Fin d)} {sigma : Fin d → ℝ}
    (hsigma : ∀ i ∈ S, |sigma i| = 1)
    {a : CoeffField d} {delta M : ℝ} (hM : 0 ≤ M)
    (hameas : Measurable a)
    (hcontrast : CoefficientIdentityDistanceLE (ballSector x₀ r S sigma) a delta)
    (v : H1Function (ballSector x₀ r S sigma))
    (hzt : LocalizedZeroTraceFunctionOn (ballSector x₀ r S sigma)
      (euclideanBall x₀ r) v.toFun)
    {g : Vec d → ℝ}
    (hgL2 : MemLp g 2 (volume.restrict (ballSector x₀ r S sigma)))
    (hgM : ∀ᵐ y ∂volume.restrict (ballSector x₀ r S sigma), |g y| ≤ M)
    (hflux : ∀ j, MemLp (fun y => matVecMul (a y) (v.grad y) j) 2
      (volume.restrict (ballSector x₀ r S sigma)))
    (hv : IsMatrixDivFormWeakSolutionZerothOrderOn a (ballSector x₀ r S sigma) v g 0) :
    ∃ (w : H1Function (euclideanBall x₀ r)) (b : CoeffField d) (h : Vec d → ℝ),
      Measurable b ∧
      CoefficientIdentityDistanceLE (euclideanBall x₀ r) b delta ∧
      MemScalarLInfOn (euclideanBall x₀ r) h ∧
      IsMatrixDivFormWeakSolutionZerothOrderOn b (euclideanBall x₀ r) w h 0 ∧
      (∀ y ∈ ballSector x₀ r S sigma, w.toFun y = v.toFun y) ∧
      (∀ j ∈ S, ∀ z : Vec d,
        w.toFun (coordFaceReflection (x₀ j) j z) = -w.toFun z) := by
  obtain ⟨w, b, h, hbmeas, hbcontrast, hhL2, hhM, -, hweq, hwpin, hwodd, -⟩ :=
    exists_oddReflection_weakSolution_chain hr hsigma hM hameas hcontrast v hzt
      hgL2 hgM hflux hv S (subset_refl S)
  have hself : partialReflectedBallSector x₀ r S sigma S = euclideanBall x₀ r :=
    partialReflectedBallSector_self x₀ r S sigma
  refine ⟨h1FunctionOfSetEq hself w, b, h, hbmeas, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hself]
    exact hbcontrast
  · refine memLp_top_of_bound ((hhL2.restrict (euclideanBall x₀ r)).aestronglyMeasurable)
      (2 ^ S.card * M) ?_
    exact ae_restrict_of_ae (by
      filter_upwards [hhM] with y hy
      simpa only [Real.norm_eq_abs] using hy)
  · exact isMatrixDivFormWeakSolutionZerothOrderOn_h1FunctionOfSetEq hself hweq
  · intro y hy
    rw [h1FunctionOfSetEq_toFun]
    exact hwpin y hy
  · intro j hj z
    rw [h1FunctionOfSetEq_toFun]
    exact hwodd j hj z

end

end Algsuperdiff.StochasticProcess.Common.Regularity.Freezing
