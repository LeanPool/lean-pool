/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.Order.Interval.Set.Basic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.SmoothIBP
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.TestFunction
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.WeakDerivative
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet
public import LeanPool.CaffarelliKohnNirenberg.Leray.JSpace

/-!
# Leray Hopf Limit Prop Class

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory
open Filter
open scoped ENNReal
open CKN
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- Space-time `L²` membership of the velocity and gradient gives the joint
energy integrability in (LH1) of `def:leray-hopf`. -/
theorem lerayHopfLimit_joint_lintegral_finite
    {α E F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E]
    [NormedAddCommGroup F]
    (μ : Measure α) (u : α → E) (D : α → F)
    (hu : MemLp u (2 : ℝ≥0∞) μ) (hD : MemLp D (2 : ℝ≥0∞) μ) :
    (∫⁻ x, ‖u x‖ₑ ^ (2 : ℝ) + ‖D x‖ₑ ^ (2 : ℝ) ∂μ) < ⊤ := by
  have huInt : (∫⁻ x, ‖u x‖ₑ ^ (2 : ℝ) ∂μ) < ⊤ := by
    have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) hu.eLpNorm_lt_top
    norm_num at h ⊢
    exact h
  have hDInt : (∫⁻ x, ‖D x‖ₑ ^ (2 : ℝ) ∂μ) < ⊤ := by
    have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) hD.eLpNorm_lt_top
    norm_num at h ⊢
    exact h
  have humeas : AEMeasurable (fun x => ‖u x‖ₑ ^ (2 : ℝ)) μ :=
    hu.aestronglyMeasurable.enorm.pow_const (2 : ℝ)
  rw [lintegral_add_left' humeas]
  exact ENNReal.add_lt_top.mpr ⟨huInt, hDInt⟩

/-- The divergence condition in (LH1) is closed under the all-time weak slice
convergence in `prop:leray-limit`. -/
theorem lerayHopfLimit_divergence_of_weakSlice
    (U : ℕ → Vec3 → Vec3) (u : Vec3 → Vec3)
    (hdiv : ∀ n, IsWeakDivFreeL2 (U n))
    (hweak : ∀ w : Vec3 → Vec3, MemLp w (2 : ℝ≥0∞) volume →
      Tendsto (fun n => ∫ x : Vec3, ∑ i : Fin 3, U n x i * w x i)
        atTop (nhds (∫ x : Vec3, ∑ i : Fin 3, u x i * w x i))) :
    ∀ ψ : CKN.WeakTestFunction (Set.univ : Set Vec3),
      ∫ x : Vec3, ∑ i : Fin 3, u x i * ψ.partialDeriv i x = 0 := by
  intro ψ
  let w : Vec3 → Vec3 := fun x i => ψ.partialDeriv i x
  have hwi (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => w x i) := by
    change ContDiff ℝ (⊤ : ℕ∞) (CKN.spatialDeriv ψ.toFun i)
    exact CKN.contDiff_spatialDeriv_smooth ψ.contDiff i
  have hwCompact (i : Fin 3) : HasCompactSupport (fun x : Vec3 => w x i) := by
    change HasCompactSupport (fun x => (fderiv ℝ ψ.toFun x) (CKN.basisVec i))
    exact ψ.hasCompactSupport.fderiv_apply (𝕜 := ℝ) (CKN.basisVec i)
  have hw : MemLp w (2 : ℝ≥0∞) volume := by
    apply (continuous_pi fun i => (hwi i).continuous).memLp_of_hasCompactSupport
    let K : Set Vec3 := ⋃ i : Fin 3, tsupport (fun x : Vec3 => w x i)
    have hKcompact : IsCompact K := by
      dsimp [K]
      exact isCompact_iUnion fun i => (hwCompact i).isCompact
    have hKclosed : IsClosed K := by
      dsimp [K]
      exact isClosed_iUnion_of_finite fun i =>
        isClosed_tsupport (f := fun x : Vec3 => w x i)
    refine HasCompactSupport.intro' hKcompact hKclosed ?_
    intro x hx
    funext i
    change x ∉ ⋃ j : Fin 3, tsupport (fun y : Vec3 => w y j) at hx
    apply image_eq_zero_of_notMem_tsupport (f := fun y : Vec3 => w y i) (x := x)
    intro hxi
    exact hx (Set.mem_iUnion.mpr ⟨i, hxi⟩)
  have hlimit := hweak w hw
  have hzero : Tendsto
      (fun n => ∫ x : Vec3, ∑ i : Fin 3, U n x i * w x i) atTop (nhds 0) := by
    have heq : (fun n => ∫ x : Vec3, ∑ i : Fin 3, U n x i * w x i) =
        fun _ => (0 : ℝ) := by
      funext n
      simpa [w] using (hdiv n).2 ψ
    rw [heq]
    exact tendsto_const_nhds
  have hresult := tendsto_nhds_unique hlimit hzero
  simpa [w] using hresult

/-- The measurable, finite-energy, weak-gradient, and divergence clauses of
(LH1) follow from the space-time limit and its all-time weak slice pairings. -/
theorem lerayHopfLimit_LH1_core
    (T : ℝ) (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3)
    (U : ℕ → ParabolicPoint → Vec3)
    (humeas : AEStronglyMeasurable u
      (volume.restrict (spaceTimeSet Set.univ (Set.Ioo 0 T))))
    (hDmeas : AEStronglyMeasurable Du
      (volume.restrict (spaceTimeSet Set.univ (Set.Ioo 0 T))))
    (hu : MemLp u 2
      (volume.restrict (spaceTimeSet Set.univ (Set.Ioo 0 T))))
    (hDu : MemLp Du 2
      (volume.restrict (spaceTimeSet Set.univ (Set.Ioo 0 T))))
    (hgradient : ∀ᵐ s ∂(volume.restrict (Set.Ioo 0 T)), ∀ i : Fin 3,
      HasWeakGradientOn Set.univ (fun x => u (x,s) i)
        (fun x => Du (x,s) i))
    (hdivU : ∀ n t, 0 ≤ t → IsWeakDivFreeL2 (fun x => U n (x,t)))
    (hweakSlice : ∀ t : ℝ, 0 < t → ∀ w : Vec3 → Vec3,
      MemLp w 2 volume →
      Tendsto (fun n => ∫ x : Vec3, ∑ i : Fin 3, U n (x,t) i * w x i)
        atTop (nhds (∫ x : Vec3, ∑ i : Fin 3, u (x,t) i * w x i))) :
    AEStronglyMeasurable u
        (volume.restrict (spaceTimeSet Set.univ (Set.Ioo 0 T))) ∧
      AEStronglyMeasurable Du
        (volume.restrict (spaceTimeSet Set.univ (Set.Ioo 0 T))) ∧
      (∫⁻ z in spaceTimeSet Set.univ (Set.Ioo 0 T),
        ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤ ∧
      (∀ᵐ s ∂(volume.restrict (Set.Ioo 0 T)), ∀ i : Fin 3,
        HasWeakGradientOn Set.univ (fun x => u (x,s) i)
          (fun x => Du (x,s) i)) ∧
      (∀ᵐ s ∂(volume.restrict (Set.Ioo 0 T)),
        ∀ ψ : CKN.WeakTestFunction Set.univ,
          ∫ x : Vec3, ∑ i : Fin 3, u (x,s) i * ψ.partialDeriv i x = 0) := by
  refine ⟨humeas, hDmeas, lerayHopfLimit_joint_lintegral_finite _ _ _ hu hDu,
    hgradient, ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  have hspos : 0 < s := hs.1
  have hdiv := lerayHopfLimit_divergence_of_weakSlice
    (fun n x => U n (x,s)) (fun x => u (x,s))
    (fun n => hdivU n s (le_of_lt hspos)) (hweakSlice s hspos)
  exact hdiv

end CKN.Leray

end
